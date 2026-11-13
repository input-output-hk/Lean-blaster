import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Support
import Blaster.Reconstruct.SmtProof.Backend
import Blaster.Reconstruct.SmtProof.SymTable
import Blaster.Reconstruct.SmtProof.Tactics
import Blaster.Reconstruct.SmtProof.Replay
import Blaster.Reconstruct.SmtProof.Bridge
import Blaster.Reconstruct.SmtProof.RecFun
import Blaster.Reconstruct.SmtProof.Encoding

/-!
# Proof reconstruction from SMT proofs

Given a residual goal proved valid by the SMT solver, this module:
 1. translates the goal to SMT-LIB with Blaster's translation (top-level variables are introduced
    as Lean free variables such that the SMT constants can be mapped back to them);
 2. runs a proof producing backend (see `Backend`) on the query and parses its proof
    into the backend independent representation (`Proof`);
 3. builds the interpretation of the SMT symbols in Lean (`SymTable`) from the query and from
    Blaster's translation caches;
 4. replays the proof (see `Replay.lean`) to obtain a proof of `False` from the negation of the goal.
-/

open Lean Meta Elab Term Tactic Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.Reconstruct.SmtProof

/-! ## Main entry point -/

/-- Split the leading binders of `e` which are neither propositions nor sorts (i.e., data variables). -/
partial def dataBinders (e : Expr) (k : Array Expr → Expr → TermElabM α) (acc : Array Expr := #[]) : TermElabM α := do
  match e with
  | .forallE n t b bi =>
      -- NOTE: sort variables are introduced (see the interpretation of Blaster's polymorphic encoding)
      if (← isProp t) then k acc e
      else withLocalDecl n bi t fun x => dataBinders (b.instantiate1 x) k (acc.push x)
  | _ => k acc e

/-- The kernel checks of the auxiliary theorems of a proof, run in parallel (see `startKernelChecks`). -/
structure KernelChecks where
  tasks : Array (Task (Option String)) := #[]
  /-- set to interrupt the checks (e.g., once one of them failed, or when the proof is rejected otherwise) -/
  cancelTks : Array IO.CancelToken := #[]

instance : Append KernelChecks where
  append a b := { tasks := a.tasks ++ b.tasks, cancelTks := a.cancelTks ++ b.cancelTks }

/-- Interrupt the kernel checks `k` (e.g., when the proof is rejected otherwise). -/
def KernelChecks.cancel (k : KernelChecks) : BaseIO Unit := k.cancelTks.forM (·.set)

structure SmtProofResult where
  proof : Expr
  backend : String
  steps : Nat
  stats : ReplayStats
  /-- the kernel checks of the auxiliary theorems of the proof run in parallel (see `startKernelChecks`): the proof is
      only accepted once they all succeeded (see `awaitKernelChecks`) -/
  kernelChecks : KernelChecks := {}
  /-- the auxiliary theorems of the proof whose checks are started by `startKernelChecks`, with their values: known not
      to depend on `sorryAx` (see `dependsOnSorry`, such that their values are not traversed again) -/
  sorryFree : Array (Name × Expr) := #[]

/-- Start the kernel checks of `decls`, each against the kernel environment given with it (the environment before
    it, such that a declaration may only use the declarations before it), on `threads` dedicated threads. The checks
    stop at the first error. -/
def startKernelChecks (decls : Array (Kernel.Environment × Declaration)) (threads : Nat) (opts : Options) :
    BaseIO KernelChecks := do
  if decls.isEmpty then return {}
  let next ← IO.mkRef 0
  let tk ← IO.CancelToken.new
  -- the checks taking at least 200 ms (environment variable `BLASTER_SMTPROOF_TRACE`)
  let trace ← IO.getEnv "BLASTER_SMTPROOF_TRACE"
  let rec worker (fuel : Nat) : BaseIO (Option String) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      if ← tk.isSet then return none
      let i ← next.modifyGet fun i => (i, i + 1)
      let some (kenv, decl) := decls[i]? | return none
      let t0 ← IO.monoMsNow
      let r := kenv.addDeclCore 0 decl (some tk)
      if let some f := trace then
        let ms := (← IO.monoMsNow) - t0
        if ms ≥ 200 then
          let msg := s!"  kernel check of auxiliary theorem {i}/{decls.size}: {ms} ms"
          (do (← IO.FS.Handle.mk f .append).putStrLn msg).catchExceptions fun _ => pure ()
      match r with
      | .ok _ => worker fuel
      | .error ex =>
          -- NOTE: an interruption (see `KernelChecks.cancel`) is not reported as a failure of the check
          if ← tk.isSet then return none
          tk.set
          let msg ← (do return some (← (ex.toMessageData opts).toString)).catchExceptions fun _ => pure (some "?")
          return some s!"kernel check of {decl.getNames}: {msg.getD "?"}"
  let mut tasks := #[]
  for _ in [:max (min threads decls.size) 1] do
    tasks := tasks.push (← BaseIO.asTask (prio := .dedicated) (worker decls.size))
  return { tasks, cancelTks := #[tk] }

/-- Wait for the kernel checks `k` (see `startKernelChecks`): the first error, if any. -/
def awaitKernelChecks (k : KernelChecks) : BaseIO (Option String) := do
  let mut err := none
  for t in k.tasks do
    if let some msg ← IO.wait t then
      if err.isNone then err := some msg
  return err

/-- Given `e := ∀ b₁ ... bₙ, C` (leading binders), return `∀ xs, hs → C` where `xs` are the data binders and
    `hs` the propositions among the `bᵢ` (only when no data binder depends on a proposition), together with
    a function turning a proof of the latter into a proof of `e`. Blaster declares the data variables of
    the leading binders as SMT constants, including the ones following hypotheses. -/
def prenex (e : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  forallTelescope e fun bs c => do
    if bs.isEmpty then return none
    let mut data := #[]
    let mut hyps := #[]
    for b in bs do
      let t ← inferType b
      if (← isProp t) then hyps := hyps.push b
      else
        if hyps.any (fun h => t.containsFVar h.fvarId!) then return none
        data := data.push b
    if hyps.isEmpty || data.isEmpty then return none
    -- already in prenex form
    if bs == data ++ hyps then return none
    let e' ← mkForallFVars (data ++ hyps) c
    let back (p : Expr) : MetaM Expr :=
      forallTelescope e fun bs' _ => do
        -- bs' follow the order of `bs`
        let m := (bs.zip bs').toList
        let get (x : Expr) := (m.find? (·.1 == x)).map (·.2) |>.getD x
        mkLambdaFVars bs' (mkAppN p ((data ++ hyps).map get))
    return some (e', back)

/-- Quantifications over sorts `∀ (α : Sort u), b` and `∃ (α : Sort u), b` (`u ≠ 0`) in `e` (traversal with sharing), possibly with loose
    bound variables (e.g., `∀ (α : Type), (∀ (_x : α), n > 5) → n > 5` under `∃ n`). -/
partial def sortQuantifiers (e : Expr) : Array Expr := Id.run do
  let mut acc := #[]
  let mut stack := #[e]
  let mut seen : Std.HashSet Expr := {}
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if seen.contains s then continue
    seen := seen.insert s
    if let .forallE _ (.sort u) _ _ := s then
      if !u.isZero then acc := acc.push s
    -- `∃ (α : Sort u), b` (the lambda term over the sort)
    if let .app (.app (.const ``Exists _) (.sort u)) _ := s then
      if !u.isZero then acc := acc.push s
    match s with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return acc

/-- Sort variables of the goal `∀ xs, body` (Blaster's polymorphic encoding: sort variables are values of the sort
    `@Type`, and the values of the types they denote are values of the sort `@Instance`): the leading binders and the
    variables of the local context (e.g., auto-bound implicit arguments) whose type is a sort other than `Prop`, and
    whether `body` quantifies over sorts. -/
def sortVariables (xs : Array Expr) (body : Expr) : MetaM (Array Expr × Bool) := do
  let isSortVar (t : Expr) : MetaM Bool := do
    let t ← whnfR t
    return t.isSort && !t.isProp
  let mut sortVars ← xs.filterM fun x => do isSortVar (← inferType x)
  for d in ← getLCtx do
    if d.isImplementationDetail || sortVars.contains d.toExpr then continue
    if ← isSortVar d.type then
      if body.containsFVar d.fvarId || (← xs.anyM fun x => do return (← inferType x).containsFVar d.fvarId) then
        sortVars := sortVars.push d.toExpr
  -- propositions quantifying over sorts (below the leading binders)
  -- NOTE: a quantification with loose bound variables (e.g., under `∃`) is in a proposition of the goal: its sort
  -- variable is a value of the sort `@Type` as for a closed one
  let quantifiedSorts ← (sortQuantifiers body).anyM fun s => if s.hasLooseBVars then pure true else isProp s
  return (sortVars, quantifiedSorts)

/-- Interpretations of the polymorphic encoding tried in order (`true`: `Poly`, `false`: `@Instance` as the sort
    variable). With a single sort variable `α`, `@Instance` is first interpreted as `α` and `@Type` as `Unit`
    (membership predicates as `True`), which fails when `α` may be empty (e.g., skolem constants of sort
    `@Instance`). -/
def polyModes (sortVars : Array Expr) (quantifiedSorts : Bool) : Array Bool :=
  if quantifiedSorts then #[true]
  else if sortVars.isEmpty then #[false]
  else if sortVars.size == 1 then #[false, true]
  else #[true, false]

/-- The translation of the negation of the goal `body` over the data variables `xs` (with the sort variables
    `sortVars`): the goal translated (`body` or its optimized form, see below), the environment of the translation and
    the SMT commands. -/
def translateNegGoal (xs : Array Expr) (body : Expr) (sortVars : Array Expr) (sOpts : BlasterOptions) :
    TermElabM (Expr × TranslateEnv × Array SExpr) := do
  -- NOTE: commands are only recorded when `dumpSmtLib` is set (nothing is printed)
  let env := {(default : TranslateEnv) with
                optEnv.options.solverOptions := { sOpts with onlySmtLib := true, dumpSmtLib := true }}
  let (goalTerm, tenv) ← (do
      -- NOTE: the optimizer populates the caches used by the translation (e.g., the definitions of
      -- recursive functions); `body` being already optimized, `body'` is expected to be `body` (up to
      -- definitional equality, which the bridge requires).
      let body' ← Optimize.main body
      -- NOTE: when the optimizer is not idempotent on `body`, `body` itself is translated, such that the
      -- asserted formula is the translation of the negated goal (see the bridge)
      let reopt := body' == body
      setBlasterProcess
      -- sort variables introduced as free variables: declared as Blaster does for top-level quantifiers
      for α in sortVars do
        updateQuantifiedFVarsCache α.fvarId! true
        -- NOTE: the declarations of sorts are cached on (hash-consed) sort objects
        let decl ← generateSortInstDecl (← inferType α)
        declareConst (← typeParamNameToSmtSymbol α.fvarId!) decl.instSort
      -- the data variables are declared first: their datatypes are then declared before the body refers to
      -- their fields (e.g., the function fields of structures, applied in the body); with sort variables, they
      -- are declared with their membership predicates also when they don't occur in the goal (e.g., `a : α`
      -- witnessing that `α` is inhabited)
      -- NOTE: variables that can't be translated by themselves (e.g., instances of classes) are left to the
      -- translation of the body
      for x in xs do
        let t ← inferType x
        if sortVars.contains x || (← isProp t) || (← isClass? t).isSome then continue
        let saved ← get
        try discard <| translateExpr x catch _ => set saved
      -- NOTE: the unoptimized goal may not be translatable (e.g., terms that only the optimizer normalizes):
      -- its optimized form is then translated, when definitionally equal to it
      let saved ← get
      let (st, goalTerm) ← if reopt then pure (← translateExpr body', body') else
        try pure (← translateExpr body, body) catch ex => do
          set saved
          let defeq ← (·.getD false) <$> Local.withBudget? 20000 (withDefault <| isDefEq body body')
          if !defeq then throw ex
          pure (← translateExpr body', body')
      assertTerm (notSmt st)
      return goalTerm : TranslateEnvT Expr).run env
  let cmds ← tenv.smtEnv.smtCommands.mapM fun c => ofExcept (parseSExpr (toString c))
  return (goalTerm, tenv, cmds.map guardNatQuantifiers)

/-- The backend `n` of the proof replay on the commands `cmds` (see `proveBySmtProof`), if it applies: the backend, its
    query, the recursive functions of the query (`z3rec`), its number of random seeds and the delay between the starts
    of its runs. -/
def backendFor (n : String) (cmds : Array SExpr) (timeout : Nat) :
    TermElabM (Option (Backend × Array SExpr × Array RecFun.Pair × Nat × Nat)) := do
  let recQuery := if n == "z3rec" then (RecFun.rewriteQuery cmds).toOption else none
  if n == "z3rec" && recQuery.isNone then return none
  let backend ← match n with
    | "z3" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout)
    | "z3arith2" =>
        let b := z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout
        let drop := fun c => b.dropCommand c || (match c with
          | .list #[.atom "set-option", .atom ":smt.arith.solver", _] => true
          | _ => false)
        pure { b with
          name := "z3arith2"
          dropCommand := drop
          preamble := b.preamble.push "(set-option :smt.arith.solver 2)" }
    | "z3+" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout (simplifiers := true))
    | "z3rec" => pure { z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout with name := "z3rec" }
    | b => throwError "unknown proof backend {b}"
  let (query, pairs) := if n == "z3rec" then recQuery.getD (cmds, #[]) else (cmds, #[])
  -- Z3: portfolio of random seeds (environment variable `BLASTER_SMTPROOF_SEEDS`, default 3), started every
  -- `BLASTER_SMTPROOF_SEED_DELAY` ms (default: a quarter of the timeout, at most 10 s) while no proof is found
  -- NOTE: e.g., Z3 finds a proof of a CEK evaluation of a validator in 30 to 170 s depending on the seed
  let seedsEnv ← IO.getEnv "BLASTER_SMTPROOF_SEEDS"
  let seeds := (seedsEnv.bind String.toNat?).getD 3
  let delayMs := ((← IO.getEnv "BLASTER_SMTPROOF_SEED_DELAY").bind String.toNat?).getD (min 10000 (timeout * 250))
  return some (backend, query, pairs, seeds, delayMs)

/-- The backends of the proof replay, tried in order (environment variable `BLASTER_SMTPROOF_BACKENDS`, e.g.,
    `z3,z3rec`), and their timeout in seconds. -/
def proofBackends (sOpts : BlasterOptions) : IO (List String × Nat) := do
  let names := ((← IO.getEnv "BLASTER_SMTPROOF_BACKENDS").getD "z3,z3rec,z3+").splitOn ","
  let timeout := ((← IO.getEnv "BLASTER_SMTPROOF_TIMEOUT").bind String.toNat?).getD (sOpts.timeout.getD 20)
  return (names.map (·.trim), timeout)

/-- Try to prove `e` (a closed proposition proved valid by the SMT solver) by replaying a proof of the
    SMT backend. The polymorphic encoding is interpreted by `Poly` when `poly?` is `some true`, with `@Instance` as
    the sort variable when `some false`, and with the interpretations of `modes` tried in order otherwise. -/
partial def proveBySmtProof (e : Expr) (sOpts : BlasterOptions) (poly? : Option Bool := none) :
    TermElabM (Except String SmtProofResult) := do
  if let some (e', back) ← prenex e then
    match ← proveBySmtProof e' sOpts poly? with
    | .ok r => return .ok { r with proof := ← back r.proof }
    | .error msg => return .error msg
  if poly?.isNone then
    let modes ← dataBinders e fun xs body => do
      let (sortVars, quantifiedSorts) ← sortVariables xs body
      return polyModes sortVars quantifiedSorts
    if modes.size > 1 then
      let s ← saveState
      let ngen ← getNGen
      let mut msgs := #[]
      for poly in modes do
        s.restore
        -- NOTE: the name generator (not restored by `restore`) is reset too, such that the translations (whose
        -- SMT symbols have fresh names) coincide and the proofs of the backends are reused (see `runBackendCached`)
        setNGen ngen
        match ← proveBySmtProof e sOpts (some poly) with
        | .ok r => return .ok r
        | .error msg => msgs := msgs.push msg
      -- the error of the general interpretation first
      let errs := if modes[0]! then msgs else msgs.reverse
      return .error (String.intercalate "; with the other interpretation of the polymorphic encoding: " errs.toList)
  -- NOTE: each tactic attempt has its own heartbeat budget (see `proveWithTactic`)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
  dataBinders e fun xs body => do
  -- interrupts the proofs of the definitional equations started in parallel (see `RecFun.startEqTasks`) on return
  let eqStop ← IO.CancelToken.new
  try
    -- polymorphic encoding (see `sortVariables`), interpreted by `Poly` when `poly` is set
    let (sortVars, quantifiedSorts) ← sortVariables xs body
    let poly := poly?.getD (polyModes sortVars quantifiedSorts)[0]!
    -- 1. translation
    let (goalTerm, tenv, cmds) ← translateNegGoal xs body sortVars sOpts
    -- 3.-4. interpretation and replay of the proof `sproof` of `backend`
    -- 3. interpretation
    -- SMT constants of the free variables of the goal (the introduced variables, as well as the
    -- variables of the local context, e.g., section variables)
    let mut consts : Std.HashMap String Expr := {}
    let lctx ← getLCtx
    for (v, idx) in tenv.smtEnv.fvarsCache.toList do
      if lctx.contains v then consts := consts.insert s!"${idx}" (mkFVar v)
    let baseTbl ← if poly then polyBuildSymTable cmds tenv consts sortVars
      else buildSymTable cmds tenv consts sortVars[0]?
    let certificates := (← IO.getEnv "BLASTER_SMTPROOF_CERTIFICATES") == some "1"
    -- Both the pre-solver encoding contract and replay use this interpretation
    -- registry. Solver-local definitions are only added for replay afterwards.
    let bridgeConfig (tbl : SymTable) : TermElabM Bridge.Cfg := do
      let mut insts : Std.HashMap Name Expr := {}
      for (k, v) in tenv.optEnv.memCache.isMatcherCache.toList do insts := insts.insert k v.instApp
      let mut macros : Std.HashMap Name (Array (String × SExpr) × STerm) := {}
      for (k, v) in tenv.smtEnv.funInstCache.toList do
        let nm := match v with
          | .SimpleIdent s => toString s
          | .QualifiedIdent s _ => toString s
        if let .const n _ := k then
          if let some (.macro params body) := tbl.syms.get? nm then macros := macros.insert n (params, body)
      let macroOf (n : Name) : Option (Array Expr → MetaM Expr) := (macros.get? n).map fun (params, body) vals => do
        let locals := (params.zip vals).foldl (fun m ((x, _), v) => m.insert x v) {}
        (interp body).run { table := tbl, locals }
      let macroTacs ← macroTactics
      return {
        matchInst := insts.get?, macroOf, polyWorld := poly
        proveLemma := fun stmt => do return (← portfolio macroTacs stmt "macro").map (·.1) }
    let encoding? ← if certificates then
      prepareGoalEncoding? body goalTerm cmds baseTbl (← bridgeConfig baseTbl)
      else pure none
    -- NOTE: the parallel kernel checks of the auxiliary theorems of the proof (see `startKernelChecks`) are recorded in
    -- `kernelChecks`, such that the caller can interrupt them when the replay fails afterwards
    let replayWith (backend : Backend) (sproof : Proof) (recPairs : Array RecFun.Pair)
        (eqTasks : Array (Expr × Task (Except Exception (Option Expr)))) (kernelChecks : IO.Ref KernelChecks)
        (replayLimit : Option Nat := none) :
        TermElabM SmtProofResult := do
      clearLocalCache
      let sorryFree ← IO.mkRef (#[] : Array (Name × Expr))
      let tbl ← addSkolems sproof baseTbl
      -- auxiliary functions and case predicates of recursive functions (Z3)
      let (tbl, recAux) ← RecFun.addProofDefs sproof tbl
      -- 4. replay
      let bridge ← bridgeTactics
      -- axioms of the polymorphic encoding (see `Poly`)
      let polyTac := #[("poly", ← `(tactic| blaster_poly))]
      let bridge := if poly then polyTac ++ bridge else bridge
      let bcfg ← bridgeConfig tbl
      let tacCache : IO.Ref (Std.HashMap String (Array (String × TSyntax `tactic))) ← IO.mkRef {}
      -- the tactics on the statement `stmt` of a step of rule `rule`
      let tacticsFor (rule : String) (stmt : Expr) : TermElabM (Array (String × TSyntax `tactic)) := do
        -- NOTE: the tactic syntax of each rule is built once per replay
        let tacs ← match (← tacCache.get).get? rule with
          | some t => pure t
          | none => do let t ← stepTactics rule; tacCache.modify (·.insert rule t); pure t
        -- the axioms of the polymorphic encoding (e.g., Z3's `recfun` lemmas on the definitions of `@isList`)
        return if poly && (stmt.find? (·.isConstOf ``Poly.Img)).isSome then tacs ++ polyTac else tacs
      let proveStep (rule : String) (stmt : Expr) : TermElabM (Option (Expr × String)) := do
        portfolioPar (← tacticsFor rule stmt) stmt rule
      -- several goals attempted in parallel (see `proveClosedFirst`)
      let proveSteps? : Option (Array (String × Expr) → TermElabM (Option (Nat × Expr × String))) :=
        if (← IO.getEnv "BLASTER_SMTPROOF_PARPORTFOLIO") == some "0" then none else some fun gs => do
          portfolioParMulti (← gs.mapM fun (rule, stmt) => return (stmt, ← tacticsFor rule stmt, rule))
      -- recursive functions (`z3rec`): definitional equations, proved with the bridge tactics in the empty local
      -- context when closed (see `proveClosed`), and differences of normal forms in their unfoldings
      let recCtx ← RecFun.mkCtx tbl recAux recPairs sproof.defs
        (fun stmt => do
          let run : TermElabM (Option Expr) := do return (← portfolio bridge stmt "bridge").map (·.1)
          if stmt.hasFVar then run else withLCtx {} {} run)
        (fun stmt => do return (← proveClosed { proveDirect := fun _ => pure none, proveStep } "th-lemma" stmt).map (·.1))
        (fun a b => do
          let largeStep := !(Local.sizeLe a Local.largeTermSize && Local.sizeLe b Local.largeTermSize)
          let prove := localProof { proveDirect := fun _ => pure none, proveStep } "rewrite" largeStep
          Local.diffEq prove (← IO.mkRef 6) a b)
        eqTasks
      -- the definitional equations of the functions unfolded by the lemmas of the proof, proved in parallel
      let unfolded := sproof.steps.foldl (init := {}) fun acc s =>
        if s.rule == "th-lemma" && s.attrs[0]? == some (.atom "recfun") then RecFun.appliedSymbols s.concl acc else acc
      RecFun.startEqTasks recCtx unfolded (cancelTk? := some eqStop)
      let recCache : IO.Ref (Std.HashMap Expr (Option Expr)) ← IO.mkRef {}
      let pf ← withLocalDeclD `hneg (mkNot body) fun hneg => do
        let cfg : ReplayConfig := {
          certificates
          inputAssertions := encoding?.toArray.map fun e => (e.proposition, mkApp e.transport hneg)
          proveDirect := fun c => do
            -- Nat membership assertions are emitted separately from the
            -- negated goal. Use their structural nonnegativity proof before
            -- trying definition/bridge tactics on the entire goal context.
            if c.isAppOfArity ``LE.le 4 && (c.getArg! 0).isConstOf ``Int then
              if (← getIntValue? (c.getArg! 2)) == some 0 then
                if let some p ← NlArith.nonnegProof? (c.getArg! 3) then return some p
            if ← traceSlow "asserted: reducible defeq" (withReducible (isDefEq c (mkNot body))) then
              return some (← mkExpectedTypeHint hneg c)
            -- e.g., projections vs. case analyses, casts of literals (with a budget)
            let defeq (a b : Expr) : TermElabM Bool :=
              tryCatchRuntimeEx (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 50000 * 1000 }) <|
                  withCurrHeartbeats <| withDefault <| isDefEq a b)
                fun _ => return false
            if c.isAppOfArity ``Not 1 then
              if ← traceSlow "asserted: defeq" (defeq c (mkNot body)) then return some (← mkExpectedTypeHint hneg c)
            -- the interpretation of the translation of the negated goal: simultaneous traversal (see `Bridge`)
            -- NOTE: the translated goal is definitionally equal to the goal (see the translation above)
            let (r, fails) ← traceSlow "asserted: bridge" (Bridge.prove bcfg (mkNot goalTerm) c)
            if let some p := r then
              return some (← mkEqMP p (← mkExpectedTypeHint hneg (mkNot goalTerm)))
            if let some f ← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP" then
              let h ← IO.FS.Handle.mk f .append
              -- NOTE: only for the translation of the negated goal
              -- NOTE: the number of failed pairs is given by `BLASTER_SMTPROOF_BRIDGE_DUMP_N` (default 3)
              let n := ((← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP_N").bind String.toNat?).getD 3
              for (a, b) in if c.isAppOfArity ``Not 1 then fails.extract 0 n else #[] do
                h.putStrLn s!"=== bridge mismatch:\n{← ppExpr a}\n--- interpretation:\n{← ppExpr b}\n"
            -- definitions of Lean functions (e.g., by `match`): the traversal of their unfolding
            if !c.isAppOfArity ``Not 1 then
              if let some p ← (try Bridge.proveDefinition? bcfg c catch _ => pure none) then return some p
            -- definitional axioms of recursive functions (backends without `define-funs-rec`)
            if !c.isAppOfArity ``Not 1 then
              if let some p ← RecFun.proveDefAxiom? c then return some p
            let r ← portfolio bridge c "bridge"
            if r.isNone && (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then debugLog m!"bridge failed: {← dagString c 4000}"
            if r.isNone then
              if let some f ← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP" then
                let h ← IO.FS.Handle.mk f .append
                h.putStrLn s!"=== bridge failed:\n{← ppExpr c}\n--- negated goal:\n{← ppExpr (mkNot goalTerm)}\n"
            return r.map (·.1)
          proveStep, proveSteps?
          proveRecFun := fun c n => do
            -- NOTE: the lemmas have no premises (a failure is not retried)
            if let some r := (← recCache.get).get? c then return r
            let r ← try RecFun.proveLemma recCtx c n catch _ => pure none
            if r.isNone then debugLog m!"recfun lemma failed: {RecFun.brief c}"
            recCache.modify (·.insert c r)
            return r
          recFunOnly := !recPairs.isEmpty
          recHeads := recCtx.eqs.foldl (fun s eq => s.insert eq.head) {} }
        let cache ← IO.mkRef {}
        -- NOTE: the replay of the proofs of large goals takes minutes (e.g., about 5 minutes for the validators of
        -- CardanoLedgerApiBlaster's Governance); seconds (environment variable `BLASTER_SMTPROOF_DEADLINE`)
        let seconds := (← IO.getEnv "BLASTER_SMTPROOF_DEADLINE").bind String.toNat? |>.getD 1800
        let deadline := (← IO.monoMsNow) + 1000 * (replayLimit.map (min seconds)).getD seconds
        let global := (scopedSteps sproof).map (!·)
        -- the instances of the constructor applications that their arguments don't determine (see `SortInfer`)
        let t0 ← IO.monoMsNow
        let (sortHints, conflicts) := SortInfer.inferHints cmds sproof
        if (← IO.getEnv "BLASTER_SMTPROOF_TRACE").isSome then
          traceTimed s!"sort inference: {sortHints.size} hints, {conflicts} unification failures, \
            {(← IO.monoMsNow) - t0} ms" (pure ())
        let ctx : ReplayCtx := { proof := sproof, interp := { table := tbl, cache := some cache, sortHints }, cfg,
                                 deadline, global, openHyps := openHypotheses sproof,
                                 baseLCtx := ← getLCtx, baseInsts := ← getLocalInstances }
        let (p?, st) ← ((tryCatchRuntimeEx (do prepass; return Except.ok (← replay sproof.root))
                              fun ex => return Except.error ex) |>.run ctx).run {}
        let p ← match p? with
          | .ok p => pure p
          | .error ex =>
              -- report the first steps that could not be replayed (i.e., the deepest failures)
              let fs := st.stats.failures.extract 0 3
              let ms := (st.stats.msByRule.toArray.qsort (·.2 > ·.2)).extract 0 6
              let methods := st.stats.byRule.toList.map fun (r, m) => (r, m.toList)
              throwError "{ex.toMessageData}; first failures: {fs}; time per rule: {ms}; methods: {methods}"
        let pt ← traceTimed "root type" (inferType p)
        if !pt.isConstOf ``False then throwError "smt proof: root does not prove False: {pt}"
        -- NOTE: the proofs of the steps are instantiated once (see `replay`), the ones of the global steps as closed
        -- lambda terms over the variables of the goal and the negated goal (see `liftGlobalProofs`), the only free
        -- variables of their proofs as `e` is closed (not the variables of the context of the elaboration)
        -- NOTE: the proofs of many global steps (environment variable `BLASTER_SMTPROOF_SPLIT`, default 4096; 0:
        -- always) of large proofs (`BLASTER_SMTPROOF_SPLIT_DAG`, default 5M distinct subterms) are auxiliary theorems
        -- over the variables of the goal and the negated goal, checked by the kernel one at a time: the kernel's caches
        -- (e.g., the types inferred for the subterms) are kept for the check of a whole declaration, e.g., beyond 30 GB
        -- for the 10.1M distinct subterms of the proof of a CEK evaluation of a validator (19,369 global proofs),
        -- checked as auxiliary theorems in 6.5 minutes without memory increase. The smaller proofs are checked as a
        -- whole unless their auxiliary theorems are checked in parallel (see `startKernelChecks`): one at a time, the
        -- auxiliary theorems check the shared subterms of their statements again (e.g., 35 s instead of 25 s for the
        -- 2.6M distinct subterms of the proof of another validator, at 6.5 GB)
        let trace ← IO.getEnv "BLASTER_SMTPROOF_TRACE"
        let splitMin := ((← IO.getEnv "BLASTER_SMTPROOF_SPLIT").bind String.toNat?).getD 4096
        let splitDag := ((← IO.getEnv "BLASTER_SMTPROOF_SPLIT_DAG").bind String.toNat?).getD 5000000
        -- parallel kernel checks (environment variable `BLASTER_SMTPROOF_PARCHECK`: number of threads, default 8, 0:
        -- none) of the auxiliary theorems of the proofs with at least `BLASTER_SMTPROOF_PARCHECK_MIN` (default 1024)
        -- global proofs, e.g., 4 s instead of 26 s (as a whole) for the 6928 global proofs of the CEK evaluation of a
        -- minting policy, and a third of the memory
        let parThreads := ((← IO.getEnv "BLASTER_SMTPROOF_PARCHECK").bind String.toNat?).getD 8
        let parMin := ((← IO.getEnv "BLASTER_SMTPROOF_PARCHECK_MIN").bind String.toNat?).getD 1024
        let parallel := parThreads > 0 && st.globalProofs.size ≥ parMin
        let split := parallel || splitMin == 0 ||
          (st.globalProofs.size ≥ splitMin && !dagSizeLe (balancedBundle (st.globalProofs.map (·.2))) splitDag)
        let auxCount ← IO.mkRef 0
        let parDecls : IO.Ref (Array (Kernel.Environment × Declaration)) ← IO.mkRef #[]
        let aux? : Option (Nat → Expr → Expr → MetaM Expr) :=
          if !split then none else some fun i ty v => do
            -- NOTE: inlined when not closed, e.g., over variables of the polymorphic encoding (see `Poly`) bound by the
            -- enclosing context
            if ty.hasFVar || v.hasFVar || ty.hasMVar || v.hasMVar then return v
            let lvls := (collectLevelParams (collectLevelParams {} ty) v).params.toList
            let t0 ← IO.monoMsNow
            if parallel then
              -- NOTE: added without checking, and checked against the environment before it by `startKernelChecks`
              -- (such that it only uses the auxiliary theorems before it)
              -- NOTE: not traversed by `addDecl` either (`warn.sorry`), the whole proof being traversed by
              -- `dependsOnSorry`
              let kenv := (← getEnv).toKernelEnv
              let n ← mkAuxDeclName (kind := `_proof)
              let decl := Declaration.thmDecl { name := n, levelParams := lvls, type := ty, value := v }
              withOptions (fun o => warn.sorry.set (debug.skipKernelTC.set (maxHeartbeats.set o 0) true) false) <|
                addDecl decl
              parDecls.modify (·.push (kenv, decl))
              auxCount.modify (· + 1)
              return mkConst n (lvls.map mkLevelParam)
            let n ← withOptions (fun o => maxHeartbeats.set o 0) <| mkAuxLemma lvls ty v (cache := false)
            auxCount.modify (· + 1)
            -- the checks taking more than a second (environment variable `BLASTER_SMTPROOF_TRACE`)
            let ms := (← IO.monoMsNow) - t0
            if let some f := trace then
              if ms ≥ 1000 then
                let k := st.globalSteps.getD i 0
                let rule := (sproof.steps[k]?.map (·.rule)).getD "?"
                (← IO.FS.Handle.mk f .append).putStrLn
                  s!"  auxiliary theorem {← auxCount.get}/{st.globalProofs.size} (step {k} {rule}): {ms} ms, \
                    value {(dagStats v).1}, type {(dagStats ty).1}"
            return mkConst n (lvls.map mkLevelParam)
        if trace.isSome then
          traceTimed s!"{st.globalProofs.size} global proofs (auxiliary theorems: {aux?.isSome}), negated goal of \
            {(dagStats (← inferType hneg)).1} distinct subterms" (pure ())
        let p ← traceTimed "instantiation" (liftGlobalProofs p st.globalProofs (xs.push hneg) aux?)
        if parallel then
          let decls ← parDecls.get
          -- NOTE: the values of the auxiliary theorems share subterms (e.g., the interpreted terms of the goal),
          -- traversed once by a single traversal of all of them
          let thms := decls.filterMap fun (_, d) => match d with
            | .thmDecl t => some t
            | _ => none
          let entries := thms.map fun t => (t.name, t.value)
          let all := balancedBundle (thms.map fun t => mkApp2 (mkConst ``And) t.type t.value)
          if ← traceTimed "sorry check of the auxiliary theorems" (dependsOnSorry all entries) then
            throwError "smt proof: the proof depends on sorryAx"
          sorryFree.modify (· ++ entries)
          let checks ← traceTimed s!"parallel kernel checks of {decls.size} auxiliary theorems on {parThreads} threads"
            (startKernelChecks decls parThreads (← getOptions))
          kernelChecks.modify (· ++ checks)
        if trace.isSome then
          let (n, d) := dagStats p
          traceTimed s!"proof of {n} distinct subterms, binder depth {d}, metavariables {p.hasMVar}" (pure ())
          -- the cost of the instantiations of the binders by the kernel (environment variable
          -- `BLASTER_SMTPROOF_ISTATS`, the traversal being costly on large proofs)
          if (← IO.getEnv "BLASTER_SMTPROOF_ISTATS").isSome then
            let pf := mkLambda `hneg .default (← inferType hneg) (p.abstract #[hneg])
            let (m, total, hist) := instantiationStats (← mkLambdaFVars xs pf)
            traceTimed s!"instantiations: {m} subterms with loose bound variables, {total} copies, \
              histogram {hist}" (pure ())
        -- NOTE: the negated goal only occurs in the proofs of the asserted formulas (see `abstractFVar`)
        let pf ← traceTimed "abstraction of the negated goal" do
          if p.hasMVar then mkLambdaFVars #[hneg] p
          else return .lam `hneg (← inferType hneg) (abstractFVar p hneg.fvarId!) .default
        return (pf, st.stats)
      let (pf, stats) := pf
      let proofBody := mkApp2 (mkConst ``Classical.byContradiction) body pf
      let proof ← traceTimed "abstraction of the variables" (do instantiateMVars (← mkLambdaFVars xs proofBody))
      -- NOTE: e.g., type parameters that nothing determines (the other interpretation is then tried)
      if proof.hasMVar then throwError "smt proof: proof term contains metavariables"
      -- debugging: free variables escaping their scopes (environment variable `BLASTER_SMTPROOF_CHECKFINAL`)
      if (← IO.getEnv "BLASTER_SMTPROOF_CHECKFINAL").isSome then reportEscapedFVars proof
      return { proof, backend := backend.name, steps := sproof.steps.size, stats,
               kernelChecks := ← kernelChecks.get, sorryFree := ← sorryFree.get }
    -- 2. backend
    -- backends tried in order (environment variable `BLASTER_SMTPROOF_BACKENDS`, e.g., `z3,z3rec`)
    -- (`z3+`: Z3 with the simplifiers of the query; `z3rec`: Z3 on the query with its recursive functions defined by
    -- `define-funs-rec` (see `RecFun`), skipped when the query has no recursive function)
    -- NOTE: `z3rec` finds proofs when Z3 gets lost in the instantiations of the axioms of recursive functions (e.g., on
    -- the CEK evaluation of validators), but may time out where `z3` succeeds; the next backends are tried when the
    -- replay of a proof fails
    let (names, timeout) ← proofBackends sOpts
    -- A short attempt with the legacy arithmetic engine avoids the very coarse
    -- nonlinear certificates of the current engine on small arithmetic goals.
    -- Explicit backend selections keep their exact order and budgets.
    let autoArith := (← IO.getEnv "BLASTER_SMTPROOF_BACKENDS").isNone && preferArithmetic2 cmds
    let names := if autoArith then "z3arith2" :: names else names
    let mut errors := #[]
    for n in names do
      let budget := if autoArith && n == "z3arith2" then min timeout 2 else timeout
      let some (backend, query, pairs, seeds, delayMs) ← backendFor n cmds budget | continue
      -- the proofs of the definitional equations of the recursive functions, started before the search of the backend
      let eqTasks ← if pairs.isEmpty then pure #[] else
        traceTimed "definitional equations started"
          (try RecFun.preStartEqTasks baseTbl pairs (cancelTk? := some eqStop) catch _ => pure #[])
      match ← traceTimed s!"backend {backend.name}" (runBackendCached backend query seeds delayMs) with
      | .error msg => errors := errors.push msg
      | .ok out =>
          match backend.parseProof out with
          | .ok p =>
              -- NOTE: the next backends are tried when the replay fails (e.g., `z3rec` after `z3`)
              let s ← saveState
              let kernelChecks ← IO.mkRef ({} : KernelChecks)
              let replayLimit := if autoArith && n == "z3arith2" then some 10 else none
              let r ← tryCatchRuntimeEx (Except.ok <$> replayWith backend p pairs eqTasks kernelChecks replayLimit) fun ex => do
                (← kernelChecks.get).cancel
                s.restore
                return .error s!"{backend.name}: {← ex.toMessageData.toString}"
              match r with
              | .ok r => return .ok r
              | .error msg => errors := errors.push msg
          | .error msg => errors := errors.push s!"{backend.name}: {msg}"
    throwError "no proof: {errors}"
  catch ex =>
    return .error (← ex.toMessageData.toString)
  finally
    eqStop.set

end Blaster.Reconstruct.SmtProof
