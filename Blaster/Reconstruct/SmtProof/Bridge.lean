import Lean
import Blaster.Reconstruct.SmtProof.BridgeMatch

/-!
# Bridge between goals and the interpretation of their translation

The asserted formula of an SMT proof is Blaster's translation of the negated goal, which the replay
interprets back in Lean (see `Interp.lean`). The interpretation differs from the goal in the encodings
of the translation:
 - `match` expressions are translated to `ite` chains whose conditions are datatype testers and
   selectors (see `Blaster.Smt.Translate.Match`);
 - `Nat` terms are translated to `Int` terms, `Bool` terms to formulas;
 - `Blaster.dite'` (with non-dependent branches) and `ite` are translated to `ite`, etc.

This module proves the equality of a goal term `a` with the interpretation `b` of its translation by a
simultaneous traversal of both terms: congruence on their common structure, and lemmas for each
encoding at the points where they differ. The proven statement is `W(a) = b` where `W` is the
mapping to the SMT world: `(↑a : Int)` for `Nat` terms, `a = true` for `Bool` terms, the world of the
type of `a` for the terms of the polymorphic encoding (e.g., `Poly.inj α a` for `a : α`, see `Poly.lean`),
`a` otherwise.

`match` expressions are related to their `ite` encoding by auxiliary theorems stated for abstract
discriminants and alternatives (i.e., small statements, proved once per matcher instance by `proveMatchIte`,
which splits the matcher and evaluates the conditions of the encoding with case analyses). Functions
translated as SMT macros (e.g., `Nat.sub` as `@Nat.sub`, expanded by the backends) are related to the
interpretation of their macros by auxiliary theorems proved once per function (by the tactics given by the
caller).
-/

open Lean Meta Elab

namespace Blaster.Reconstruct.SmtProof.Bridge

/-! ## Traversal -/

structure Cfg where
  /-- Blaster's optimized instances of the matchers (whose alternative types are the patterns as
      translated) -/
  matchInst : Name → Option Expr := fun _ => none
  /-- maximal size of the terms compared by unification when they differ syntactically (e.g., literals) -/
  defeqSize : Nat := 64
  /-- SMT macros (`define-fun`) translating Lean functions (e.g., `Nat.sub`, `Int.toNat`): the
      interpretation of the body of the macro of a function for given arguments (in the SMT world) -/
  macroOf : Name → Option (Array Expr → MetaM Expr) := fun _ => none
  /-- prover of the auxiliary lemmas relating functions and their macros -/
  proveLemma : Expr → Term.TermElabM (Option Expr) := fun _ => pure none
  /-- hypotheses of the current branch (free variables), e.g., the conditions of the `ite` encoding of a
      `match` on `Nat`/`Int` patterns -/
  facts : Array Expr := #[]
  /-- maximal number of nested unfoldings of the functions inlined by Blaster's optimizer (see `walkUnfold`) -/
  unfoldDepth : Nat := 2
  /-- the polymorphic encoding is interpreted by `Poly` (see `walkPolyApp`, `walkPolyCasesOn` and `walkReduced`) -/
  polyWorld : Bool := false

structure State where
  cache : Std.HashMap (Expr × Expr) (Option Expr) := {}
  /-- matcher equations, per matcher instance (`M params motive`) -/
  lemmas : Std.HashMap Expr (Option Expr) := {}
  /-- macro equations, per function -/
  macroLemmas : Std.HashMap Name (Option Expr) := {}
  /-- naturality lemmas of the polymorphic functions, per statement (see `walkPolyApp`) -/
  natLemmas : Std.HashMap Expr (Option Expr) := {}
  /-- pairs of terms that could not be related (for diagnostics) -/
  failures : Array (Expr × Expr) := #[]
  /-- the hypotheses of the branches met so far (see `containsFact`) -/
  factIds : Std.HashSet FVarId := {}
  /-- whether a subterm contains a hypothesis of a branch (see `containsFact`) -/
  factMemo : Std.HashMap Expr Bool := {}

abbrev BridgeM := ReaderT Cfg (StateRefT State Term.TermElabM)

/-- Whether `p` contains one of the hypotheses of the branches met so far (`facts` being those of the current branch).
    Memoized across the walk (linear in total): a proof built in a branch only contains the hypotheses of that branch
    and of the enclosing ones (those of the other branches are abstracted), such that the hypotheses of all the branches
    met so far can be checked.
    NOTE: `Expr.hasAnyFVar` on the proof of each node re-traverses the proofs of the subterms (e.g., 40 s for the
    asserted formula of a CEK evaluation, under nested conditionals). -/
def containsFact (facts : Array Expr) (p : Expr) : BridgeM Bool := do
  if !p.hasFVar then return false
  modify fun s => { s with factIds := facts.foldl (fun acc h => acc.insert h.fvarId!) s.factIds }
  let ids := (← get).factIds
  -- NOTE: taken out of the state, such that it is updated in place
  let mut memo ← modifyGet fun s => (s.factMemo, { s with factMemo := {} })
  let mut stack : Array (Expr × Bool) := #[(p, false)]
  while !stack.isEmpty do
    let (e, expanded) := stack.back!
    stack := stack.pop
    if memo.contains e then continue
    let children : Array Expr := match e with
      | .app f a => #[f, a]
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ t v b _ => #[t, v, b]
      | .mdata _ b | .proj _ _ b => #[b]
      | _ => #[]
    let children := children.filter (·.hasFVar)
    if !expanded then
      if let .fvar x := e then memo := memo.insert e (ids.contains x); continue
      stack := stack.push (e, true)
      for c in children do if !memo.contains c then stack := stack.push (c, false)
    else
      memo := memo.insert e (children.any (memo.getD · false))
  modify fun s => { s with factMemo := memo }
  return memo.getD p false

/-- Naturality lemmas of the polymorphic functions (see `walkPolyApp`), per statement, across the calls of the bridge
    (reused while the environment contains them). -/
initialize natLemmaCache : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

/-- `(∀ xs alts, M params motive xs alts = ite ..., proof)` (see `iteOf` and `proveMatchIte`), where `inst?` is
    Blaster's optimized instance of the matcher. -/
def matcherEquation (m : Name) (lvls : List Level) (info : MatcherInfo) (inst? : Option Expr) (params : Array Expr)
    (motive resTy : Expr) : Term.TermElabM (Option (Expr × Expr)) := do
  let head := mkAppN (mkConst m lvls) (params.push motive)
  forallBoundedTelescope (← inferType head) (some (info.numDiscrs + info.numAlts)) fun xs _ => do
    let xd := xs.extract 0 info.numDiscrs
    let fs := xs.extract info.numDiscrs xs.size
    let some rhs ← withLocalDeclD `m (← inferType motive) fun mv => do
        let tys ← altTypes m lvls info inst? params mv xd
        iteOf resTy mv tys xd fs false
      | return none
    let stmt ← mkForallFVars xs (← mkEq (mkAppN head xs) rhs)
    let t0 ← IO.monoMsNow
    let pf? ← proveMatchIte stmt
    dbg m!"bridge: matcher equation of {m}: {(← IO.monoMsNow) - t0} ms"
    let some pf := pf? | dbg m!"bridge: matcher equation not proved: {stmt}"; return none
    return some (stmt, pf)

/-- An auxiliary theorem of the environment branch of a command (e.g., the `_proof_i` lemmas of tactics). -/
structure AuxThm where
  name : Name
  levelParams : List Name
  type : Expr
  value : Expr

/-- A closed matcher equation (statement and proof), with the auxiliary theorems of the environment branch it
    refers to (in dependency order). -/
structure SharedEquation where
  stmt : Expr
  proof : Expr
  aux : Array AuxThm

/-- The auxiliary theorems of the current module referenced by `es` (transitively), in dependency order. -/
partial def auxTheorems (es : Array Expr) : MetaM (Array AuxThm) := do
  let env ← getEnv
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array AuxThm)
  let rec visit (e : Expr) : MetaM Unit := do
    for n in e.getUsedConstants do
      if !n.isInternal || (env.getModuleIdxFor? n).isSome || (← visited.get).contains n then continue
      visited.modify (·.insert n)
      let some (.thmInfo info) := env.find? n | continue
      visit info.type
      visit info.value
      out.modify (·.push { name := n, levelParams := info.levelParams, type := info.type, value := info.value })
  for e in es do visit e
  out.get

/-- Add the auxiliary theorems `aux` of another environment branch to the environment (under new names, unless
    the current branch has a theorem of the same name and type), and rename the references to them in `es`. -/
def transplant (aux : Array AuxThm) (es : Array Expr) : MetaM (Array Expr) := do
  let mut ren : Std.HashMap Name Name := {}
  for a in aux do
    let rename (e : Expr) : Expr := if ren.isEmpty then e else
      e.replace fun e => match e with
        | .const n us => (ren.get? n).map (mkConst · us)
        | _ => none
    let ty := rename a.type
    if let some (.thmInfo info) := (← getEnv).find? a.name then
      if info.type == ty && info.levelParams == a.levelParams then continue
    let n ← mkAuxLemma a.levelParams ty (rename a.value)
    ren := ren.insert a.name n
  return es.map fun e => if ren.isEmpty then e else
    e.replace fun e => match e with
      | .const n us => (ren.get? n).map (mkConst · us)
      | _ => none

/-- Matcher equations shared by the commands (`#blaster` commands are elaborated concurrently, in their own
    environment branches): per matcher instance closed over its free variables (with Blaster's optimized
    instance), the task computing its equation (`none` when the computation was aborted). -/
initialize sharedEquations : IO.Ref (Std.HashMap (Expr × Option Expr) (Task (Option (Option SharedEquation)))) ←
  IO.mkRef {}

/-- `compute` once per `key` across the commands: the other commands wait for its result (and compute it
    themselves when the computation was aborted, e.g., by an exception). -/
def shareEquation (key : Expr × Option Expr) (compute : Term.TermElabM (Option SharedEquation)) :
    Term.TermElabM (Option SharedEquation) := do
  let p ← IO.Promise.new
  let existing? ← sharedEquations.modifyGet fun m => match m.get? key with
    | some t => (some t, m)
    | none => (none, m.insert key (p.resultD none))
  if let some t := existing? then
    if let some r ← IO.wait t then return r
    return ← compute
  try
    let r ← compute
    p.resolve (some r)
    return r
  finally
    if !(← p.isResolved) then
      p.resolve none
      sharedEquations.modify (·.erase key)

/-- `∀ xs alts, M params motive xs alts = ite ...`, proved once per matcher instance (as an auxiliary
    theorem). The equation is stated and proved in the local context of the free variables of the instance
    (e.g., in the parameters), and shared by the commands (see `shareEquation`). -/
def matcherLemma (m : Name) (lvls : List Level) (info : MatcherInfo) (params : Array Expr) (motive resTy : Expr) :
    BridgeM (Option Expr) := do
  let head := mkAppN (mkConst m lvls) (params.push motive)
  if let some l := (← get).lemmas.get? head then return l
  let inst? := (← read).matchInst m
  let l ← try
      let xs ← fvarClosure #[head]
      let compute : Term.TermElabM (Option SharedEquation) := withRestrictedLCtx xs do
        let some (stmt, pf) ← matcherEquation m lvls info inst? params motive resTy | return none
        let stmt ← mkForallFVars xs stmt
        let pf ← mkLambdaFVars xs pf
        if stmt.hasFVar || pf.hasFVar || stmt.hasMVar || pf.hasMVar then return none
        -- NOTE: the statement contains the proofs of the equations of named patterns
        return some { stmt, proof := pf, aux := ← auxTheorems #[stmt, pf] }
      let key := (← mkLambdaFVars xs head, inst?)
      let r ← if key.1.hasLevelParam || key.1.hasFVar then compute else shareEquation key compute
      let some eqn := r | pure none
      -- NOTE: the equation (computed by another command) is checked in the environment of this command, where
      -- the equations of the matcher (e.g., its splitter) are realized, and the auxiliary theorems are added
      let c ← try
          try discard <| Match.getEquationsFor m catch _ => pure ()
          let #[stmt, pf] ← transplant eqn.aux #[eqn.stmt, eqn.proof] | unreachable!
          mkAuxTheorem stmt pf
        catch ex => do
          dbg m!"bridge: shared equation of {m} rejected: {ex.toMessageData}"
          let some eqn ← compute | return none
          mkAuxTheorem eqn.stmt eqn.proof
      pure (some (mkAppN c xs))
    catch ex => dbg m!"bridge: matcher lemma {m}: {ex.toMessageData}"; pure none
  modify fun s => { s with lemmas := s.lemmas.insert head l }
  return l

/-- `(b, app = b)` where `b` is the right-hand side of the unfolding equation of the function `f` of `app`
    (`f.eq_def`, with the arguments of `app`). -/
def unfoldEqn? (app : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const f us := app.getAppFn | return none
  let some eqDef ← (try getUnfoldEqnFor? f (nonRec := true) catch _ => pure none) | return none
  let some (_, app', b) := (← instantiateForall (← inferType (mkConst eqDef us)) app.getAppArgs).eq? | return none
  if app' != app then return none
  return some (b.headBeta, mkAppN (mkConst eqDef us) app.getAppArgs)

/-- `W(a) = W(b)` from `a = b`. -/
def World.liftEq (w : World) (p : Expr) : MetaM Expr :=
  match w with
  | .same => pure p
  | .nat => mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) p
  | .bool => mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) p
  | .poly w _ => mkCongrArg w p

/-- Whether `f` is a function of the user, which Blaster's optimizer may inline (not a definition of the
    libraries, which are translated by dedicated rules). -/
def isUserFunction (f : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? f | return false
  if (← isMatcher f) || isInstanceCore env f || (env.getProjectionFnInfo? f).isSome then return false
  match env.getModuleIdxFor? f with
  | none => return true
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      return !(m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean || m.getRoot == `Blaster)

/-- `(i, a = i)` where `i` is the `ite` encoding of the matcher application `a` (with β-reduced alternatives). -/
def matcherIte? (a : Expr) : BridgeM (Option (Expr × Expr)) := do
  let .const m lvls := a.getAppFn | return none
  let some info ← getMatcherInfo? m | return none
  let args := a.getAppArgs
  if args.size != info.arity then dbg m!"bridge: over-applied matcher {m}"; return none
  if info.discrInfos.any (·.hName?.isSome) then dbg m!"bridge: matcher with discriminant equations {m}"; return none
  let np := info.numParams
  let params := args.extract 0 np
  let motive := args[np]!
  let discrs := args.extract (np + 1) (np + 1 + info.numDiscrs)
  let alts := args.extract (np + 1 + info.numDiscrs) args.size
  -- non-dependent motive
  let some resTy ← lambdaTelescope motive fun xs b => do
      if xs.any (fun x => b.containsFVar x.fvarId!) then return none else return some b
    | dbg m!"bridge: dependent motive {motive}"; return none
  let some lem ← matcherLemma m lvls info params motive resTy | return none
  -- the encoding of `a`: the right-hand side of the instance of the lemma (with β-reduced alternatives)
  let pf := mkAppN lem (discrs ++ alts)
  let some (_, _, rhs) := (← instantiateMVars (← inferType pf)).eq? | return none
  let i := betaChain rhs
  return some (i, ← mkExpectedTypeHint pf (← mkEq a i))

/-- `ite`-like terms of goals: `(α, c, inst, x, y, a = @ite α c inst x y)` for `ite`, `dite` and
    `Blaster.dite'` with non-dependent branches. -/
def iteView? (a : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  if a.isAppOfArity ``ite 5 then
    let args := a.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, ← mkEqRefl a)
  let branch (f : Expr) : Option Expr :=
    match f with
    | .lam _ _ b _ => if b.hasLooseBVars then none else some b
    | _ => none
  if a.isAppOfArity ``dite 5 then
    let args := a.getAppArgs
    let some x := branch args[3]! | return none
    let some y := branch args[4]! | return none
    let i := mkAppN a.getAppFn #[] |>.constLevels!
    let ite := mkApp5 (mkConst ``ite i) args[0]! args[1]! args[2]! x y
    -- `dite c (fun _ => x) (fun _ => y)` is `ite c x y` by definition
    return some (args[0]!, args[1]!, args[2]!, x, y, ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a ite))
  if a.isAppOfArity ``Blaster.dite' 4 then
    let args := a.getAppArgs
    let some x := branch args[2]! | return none
    let some y := branch args[3]! | return none
    let c := args[1]!
    let pf := mkApp4 (mkConst ``dite'_ite a.getAppFn.constLevels!) args[0]! c x y
    return some (args[0]!, c, mkApp (mkConst ``Classical.propDecidable) c, x, y,
      ← mkExpectedTypeHint pf (← mkEq a (mkApp5 (mkConst ``ite a.getAppFn.constLevels!) args[0]! c
          (mkApp (mkConst ``Classical.propDecidable) c) x y)))
  return none

/-- `@ite α' c' (Classical.propDecidable c') x' y'` -/
def classicalIte? (b : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if b.isAppOfArity ``ite 5 then
    let args := b.getAppArgs
    if args[2]!.isAppOfArity ``Classical.propDecidable 1 then some (args[1]!, args[3]!, args[4]!, args[0]!) else none
  else none

/-- Heads of the interpretation that are definitionally equal to Blaster's normal forms (same explicit
    arguments), e.g., `x + y` (on `Int`) for `Int.add x y`. -/
def normalizeHead (fa : Expr) (b : Expr) : Expr :=
  match fa with
  | .const n _ =>
    let args := b.getAppArgs
    let int := mkConst ``Int
    let ok (op : Name) (arity : Nat) : Bool := b.isAppOfArity op arity && args[0]! == int
    if n == ``Int.add && ok ``HAdd.hAdd 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.mul && ok ``HMul.hMul 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.sub && ok ``HSub.hSub 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.neg && ok ``Neg.neg 3 then mkApp fa args[2]!
    else if n == ``Int.ediv && ok ``HDiv.hDiv 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.emod && ok ``HMod.hMod 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.le && ok ``LE.le 4 then mkApp2 fa args[2]! args[3]!
    else if n == ``Int.lt && ok ``LT.lt 4 then mkApp2 fa args[2]! args[3]!
    else b
  | _ => b

/-- Whether `e` has at most `n` nodes (as a tree), without traversing more than `n` nodes. -/
def sizeLe (e : Expr) (n : Nat) : Bool :=
  (go e n).isSome
where
  go (e : Expr) (fuel : Nat) : Option Nat :=
    if fuel == 0 then none else
    match e with
    | .app f a => go f (fuel - 1) >>= go a
    | .lam _ t b _ | .forallE _ t b _ => go t (fuel - 1) >>= go b
    | .letE _ t v b _ => go t (fuel - 1) >>= go v >>= go b
    | .mdata _ b | .proj _ _ b => go b (fuel - 1)
    | _ => some (fuel - 1)

/-- Blaster's normal forms of the standard notations of the arithmetic operations on `Nat` and `Int`
    (definitionally equal, see `standardForm`). -/
def blasterForm (e : Expr) : Expr := Id.run do
  let ops := #[(``HAdd.hAdd, ``Nat.add, ``Int.add), (``HSub.hSub, ``Nat.sub, ``Int.sub),
    (``HMul.hMul, ``Nat.mul, ``Int.mul), (``HDiv.hDiv, ``Nat.div, ``Int.ediv), (``HMod.hMod, ``Nat.mod, ``Int.emod)]
  for (op, natOp, intOp) in ops do
    if e.isAppOfArity op 6 then
      let ty := e.getArg! 0
      if ty.isConstOf ``Nat && e.getArg! 1 == ty && e.getArg! 2 == ty then
        return mkApp2 (mkConst natOp) (e.getArg! 4) (e.getArg! 5)
      if ty.isConstOf ``Int && e.getArg! 1 == ty && e.getArg! 2 == ty then
        return mkApp2 (mkConst intOp) (e.getArg! 4) (e.getArg! 5)
  return e

/-- Standard notation of Blaster's normal forms (definitionally equal). -/
def standardForm (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if args.size != 2 then return e
  let .const f _ := e.getAppFn | return e
  let op? : Option Name :=
    if f == ``Nat.div || f == ``Int.ediv then some ``HDiv.hDiv
    else if f == ``Nat.mod || f == ``Int.emod then some ``HMod.hMod
    else if f == ``Nat.sub || f == ``Int.sub then some ``HSub.hSub
    else if f == ``Nat.add || f == ``Int.add then some ``HAdd.hAdd
    else if f == ``Nat.mul || f == ``Int.mul then some ``HMul.hMul
    else none
  let some op := op? | return e
  try mkAppM op args catch _ => return e

mutual

/-- Proof of `W(a) = b` where `W` is given by the types of `a` and `b` (see `World`). -/
partial def walk (a b : Expr) : BridgeM (Option Expr) := do
  if let some r := (← get).cache.get? (a, b) then return r
  -- β-redexes of the interpretation (e.g., applications of the interpretations of auxiliary functions)
  if b.isHeadBetaTarget then
    let b' := b.headBeta
    let some p ← walk a b' | return none
    return some (← mkExpectedTypeHint p (← mkEq (← inferType p >>= fun t => pure (t.getArg! 1)) b))
  let r ← try walkCore a b catch _ => pure none
  if r.isNone then modify fun s => { s with failures := s.failures.push (a, b) }
  -- NOTE: proofs using the hypotheses of a branch are not cached (they are only valid in the branch)
  let facts := (← read).facts
  let local? ← match r with
    | some p => if facts.isEmpty then pure false else containsFact facts p
    | none => pure !facts.isEmpty
  if !local? then modify fun s => { s with cache := s.cache.insert (a, b) r }
  return r

/-- Proof of the proposition `p` from the hypotheses of the branch (`omega`). -/
partial def byFacts (p : Expr) : BridgeM (Option Expr) := do
  let facts := (← read).facts
  if facts.isEmpty then return none
  withRestrictedLCtx (facts.push p) do
    if let some pf ← omegaProof? p then return some pf
    -- hypotheses on datatype testers (e.g., the negated conditions of the previous alternatives of a matcher, in
    -- the last alternative): case analyses on the variables of non-recursive datatypes
    Blaster.Reconstruct.proveWithTactic p (← `(tactic| (blaster_cases_nonrec <;>
      (try simp only [and_true, true_and, not_true, not_false_eq_true, and_false, false_and] at *) <;>
      $(← omegaTac):tactic)))

partial def walkCore (a b : Expr) : BridgeM (Option Expr) := do
  let ta ← inferType a
  let tb ← inferType b
  let some w ← worldOf ta tb | return none
  -- applications of functions of the polymorphic encoding (e.g., `f x` with `f : α → β`)
  if a.isApp && b.isApp && !a.getAppFn.isConst then
    if let some p ← walkLiftedApp a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
  -- polymorphic functions at sort variables, interpreted at the universe (e.g., `List.zipWith`), and case analyses
  if let .const f _ := a.getAppFn then
    if (← read).polyWorld && b.getAppFn.isConstOf f && a.getAppNumArgs == b.getAppNumArgs && a != b then
      if f == ``List.casesOn || f == ``Option.casesOn then
        if let some p ← walkPolyCasesOn a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
      else if isCasesOnRecursor (← getEnv) f then
        if let some p ← walkPolyIndCasesOn a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
      else if let some p ← walkPolyApp a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
  let r ← match w with
    | .same => walkSame a b
    | .nat => walkNat a b
    | .bool => walkBool a b
    | .poly w h => walkPoly w h a b
  if r.isSome || !(← read).polyWorld then return r
  if let some p ← walkPolySplit w a b then return some p
  let some p ← walkReduced a b | return none
  return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))

/-- Matchers on the datatypes over sort variables (e.g., lists, or datatypes of the user, see `Poly.mkIndWorld`),
    whose `ite` encoding would need default values of the selectors at the sort variables (see `matcherIte?`):
    `W(M d alts) = B[W' d]` by case analysis on the discriminant `d` (generalized in both terms), the equations of the
    constructors in the world `W'` of `d` (see `Poly.IndWorldLemmas`, by reduction for the functors, e.g.,
    `List.map`), and the testers and selectors of the interpretation reduced on constructor applications (see
    `reduceCases` and `walkReduced`). -/
partial def walkPolySplit (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let .const m _ := a.getAppFn | return none
  let some info ← getMatcherInfo? m | return none
  if info.numDiscrs != 1 || a.getAppNumArgs != info.arity then return none
  let i := info.numParams + 1
  let d := a.getArg! i
  if (a.getAppArgs.extract (i + 1) a.getAppNumArgs).any fun alt => (alt.find? (· == d)).isSome then return none
  -- the world of `d`: its application in the interpretation
  let cands ← IO.mkRef (#[] : Array Expr)
  b.forEach fun s => do if s.isApp && s.appArg! == d then cands.modify (·.push s)
  let mut wdd? := none
  for s in ← cands.get do
    if let some (w', _) ← Poly.mkWorld (← inferType d) (← inferType s) then
      if Poly.applyWorld w' d == s then wdd? := some (s, w'); break
  let some (wdd, wd) := wdd? | return none
  -- the equations of the constructors in the world (by reduction for the functors, e.g., `List.map`)
  let lemmas? ← Poly.indWorldLemmas? wd
  let tD ← inferType wdd
  let B ← kabstract b wdd
  if !B.hasLooseBVars || (B.find? (· == d)).isSome then return none
  let td ← whnfD (← inferType d)
  let .const T lvls := td.getAppFn | return none
  let some (.inductInfo tinfo) := (← getEnv).find? T | return none
  if tinfo.numIndices != 0 then return none
  let ps := td.getAppArgs
  let stmt (z : Expr) : MetaM Expr := do mkEq (w.lift (mkAppN a.getAppFn (a.getAppArgs.set! i z))) (B.instantiate1 (Poly.applyWorld wd z))
  let motive ← withLocalDeclD `z td fun z => do mkLambdaFVars #[z] (← stmt z)
  let mut minors := #[]
  for ctor in tinfo.ctors do
    let some eqn ← (match lemmas? with
        | some lemmas => pure ((lemmas.eqns.find? (·.1 == ctor)).map (·.2))
        | none => do
            let c := mkAppN (mkConst ctor lvls) ps
            forallTelescope (← inferType c) fun fs _ => do
              let l := Poly.applyWorld wd (mkAppN c fs)
              let r ← whnf l
              if !(← isConstructorApp r) then return none
              some <$> mkLambdaFVars fs (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r)))
      | return none
    let some minor ← forallTelescope (← inferType eqn) fun fs e => do
        let some (_, l, r) := e.eq? | return none
        let cfs := l.appArg!
        -- `M (C fs) alts` reduces to the alternative of `C`
        let .reduced ai ← reduceMatcher? (mkAppN a.getAppFn (a.getAppArgs.set! i cfs)) | return none
        let bi := B.instantiate1 r
        let bi' ← reduceCases bi
        let some p ← walk ai bi' | return none
        let p ← mkExpectedTypeHint p (← mkEq (w.lift ai) bi)
        let ctx ← withLocalDeclD `z tD fun z => do mkLambdaFVars #[z] (B.instantiate1 z)
        let p₁ ← mkCongrArg ctx (mkAppN eqn fs)
        let p ← mkEqTrans p (← mkEqSymm p₁)
        some <$> mkLambdaFVars fs (← mkExpectedTypeHint p (← stmt cfs))
      | return none
    minors := minors.push minor
  let casesOn := mkCasesOnName T
  let clvls := if (← getConstInfo casesOn).levelParams.length == lvls.length + 1 then levelZero :: lvls else lvls
  let pf := mkAppN (mkConst casesOn clvls) (ps.push motive |>.push d |>.append minors)
  return some (← mkExpectedTypeHint pf (← mkEq (w.lift a) b))

/-- Case analyses on constructor applications (fallback of the polymorphic encoding): `match` on the goal side (ι
    reduction) and `ite` of the interpretation whose condition is a tester of a constructor application (`if_pos`,
    `if_neg`), e.g., the encoding of `match x :: xs with ...` on a list of a sort variable (whose matcher lemma would
    need an inhabitant of the sort variable for the default values of its selectors). -/
partial def walkReduced (a b : Expr) : BridgeM (Option Expr) := do
  if let .reduced a' ← reduceMatcher? a then
    if a' != a then return ← walk a' b
  let some (c, x, y, _) := classicalIte? b | return none
  let c' ← whnfR c
  let (α, inst) := (b.getArg! 0, b.getArg! 2)
  if c'.isConstOf ``True then
    let some p ← walk a x | return none
    let pe ← mkAppOptM ``if_pos #[c, inst, ← mkExpectedTypeHint (mkConst ``True.intro) c, α, x, y]
    return some (← mkEqTrans p (← mkEqSymm pe))
  if c'.isConstOf ``False then
    let some p ← walk a y | return none
    let hn ← mkExpectedTypeHint (mkLambda `h .default c (.bvar 0)) (mkNot c)
    let pe ← mkAppOptM ``if_neg #[c, inst, hn, α, x, y]
    return some (← mkEqTrans p (← mkEqSymm pe))
  return none

/-- Small terms: definitional equality (e.g., literals in different forms). -/
partial def byDefEq (lhs b : Expr) : BridgeM (Option Expr) := do
  let n := (← read).defeqSize
  if lhs.approxDepth.toNat > n || b.approxDepth.toNat > n then return none
  if lhs.hasFVar && b.hasFVar && !(sizeLe lhs n) then return none
  let ok ← try withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 2000 * 1000 }) <|
      withCurrHeartbeats <| isDefEq lhs b
    catch _ => pure false
  if ok then return some (← mkExpectedTypeHint (← mkEqRefl b) (← mkEq lhs b)) else return none

/-- `ite` on the goal side: `W(ite c x y) = ite c' x' y'`. -/
partial def walkIte (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  -- NOTE: `ite` in the world of the polymorphic encoding is handled by `walkPoly`
  if let .poly .. := w then return none
  if a.isAppOfArity ``dite 5 then
    if let some p ← walkDite w a b then return some p
  let some (α, c, inst, x, y, pa) ← iteView? a | return none
  let some (c', x', y', _) := classicalIte? b | return none
  let some pc ← walk c c' | return none
  -- the branches are related under the condition (resp. its negation)
  let some px ← withLocalDeclD `hc c fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk x x' | return none
      some <$> mkLambdaFVars #[h] p
    | return none
  let some py ← withLocalDeclD `hc (mkNot c) fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk y y' | return none
      some <$> mkLambdaFVars #[h] p
    | return none
  -- `W(a) = W(ite c x y) = ite c W(x) W(y)`
  let pLift ← match w with
    | .same | .poly .. => mkEqRefl a
    | .nat =>
        mkEqTrans (← mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa)
          (mkApp4 (mkConst ``natCast_ite) c inst x y)
    | .bool =>
        mkEqTrans (← mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa)
          (mkApp4 (mkConst ``boolEq_ite) c inst x y)
  let (α', x₀, y₀) := match w with
    | .same | .poly .. => (α, x, y)
    | .nat => (mkConst ``Int, natCast x, natCast y)
    | .bool => (mkSort levelZero, boolTrue x, boolTrue y)
  let u ← getLevel α'
  let pIte := mkAppN (mkConst ``ite_congr_dep [u]) #[α', c, c', inst, x₀, x', y₀, y', pc, px, py]
  match w with
  | .same => return some (← mkEqTrans pa pIte)
  | _ => return some (← mkEqTrans pLift pIte)

/-- `dite c x y = ite c' x' y'` where the branches `x`, `y` depend on the condition (e.g., proofs of the equations
    of named patterns), related under the condition (resp. its negation). -/
partial def walkDite (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let args := a.getAppArgs
  let (α, c, inst, x, y) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let some (c', x', y', _) := classicalIte? b | return none
  let some pc ← walk c c' | return none
  let branch (cond f t : Expr) : BridgeM (Option Expr) :=
    withLocalDeclD `hc cond fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk (mkApp f h).headBeta t | return none
      some <$> mkLambdaFVars #[h] p
  let some px ← branch c x x' | return none
  let some py ← branch (mkNot c) y y' | return none
  match w with
  | .same =>
      let u ← getLevel α
      return some (mkAppN (mkConst ``dite_congr_dep [u]) #[α, c, c', inst, x, y, x', y', pc, px, py])
  | .nat => return some (mkAppN (mkConst ``natCast_dite_congr) #[c, c', inst, x, y, x', y', pc, px, py])
  | .bool => return some (mkAppN (mkConst ``boolEq_dite_congr) #[c, c', inst, x, y, x', y', pc, px, py])
  | .poly .. => return none

/-- Matchers on the goal side: `W(a) = W(i)` where `i` is the `ite` encoding of `a`, then `W(i) = b`. -/
partial def walkMatcher (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let some (i, pa) ← matcherIte? a | return none
  let some pi ← walk i b | return none
  let pa' ← match w with
    | .same => pure pa
    | .nat => mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa
    | .bool => mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa
    | .poly w _ => mkCongrArg w pa
  return some (← mkEqTrans pa' pi)

/-- Congruence: `f a₁ ... aₙ = f b₁ ... bₙ` from `aᵢ = bᵢ` (arguments without forward dependencies). -/
partial def walkApp (a b : Expr) : BridgeM (Option Expr) := do
  let fa := a.getAppFn
  let b := normalizeHead fa b
  let fb := b.getAppFn
  if fa != fb then return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if as.size != bs.size then return none
  let info ← getFunInfoNArgs fa as.size
  let mut pf ← mkEqRefl a
  let mut cur := as
  for i in [:as.size] do
    if as[i]! == bs[i]! then continue
    let mut resultDep := false
    if let some pi := info.paramInfo[i]? then
      if pi.hasFwdDeps then
        -- dependent argument: only definitionally equal arguments
        if ← isDefEq as[i]! bs[i]! then cur := cur.set! i bs[i]!; continue
        -- NOTE: an argument on which only the result type depends (e.g., the major premise of a `casesOn` with a
        -- constant motive) is related when the type of the application does not depend on it (see below)
        if (info.paramInfo.extract (i + 1) info.paramInfo.size).any (·.backDeps.contains i) then return none
        resultDep := true
    let ta ← inferType as[i]!
    let tb ← inferType bs[i]!
    if !(← isDefEq ta tb) then return none
    let some p ← walk as[i]! bs[i]! | return none
    -- `fun z => f cur[0..i) z as(i..n]`
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fa (cur.set! i z))
    if resultDep then
      let .forallE _ _ body _ ← whnfR (← inferType ctx) | return none
      if body.hasLooseBVars then return none
    pf ← mkEqTrans pf (← mkCongrArg ctx p)
    cur := cur.set! i bs[i]!
  return some (← mkExpectedTypeHint pf (← mkEq a b))

/-- Applications of functions translated as SMT macros: `W(f xs) = M(W(xs))` (an auxiliary lemma proved once
    per function) where `b` is an instance of the interpretation of the body `M` of the macro. -/
partial def walkMacro (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  -- NOTE: the standard notations (e.g., `x - y` on `Nat`) as Blaster's normal forms (`Nat.sub x y`)
  let a₀ := a
  let a := blasterForm a
  let .const f lvls := a.getAppFn | return none
  let some mk := (← read).macroOf f | return none
  let args := a.getAppArgs
  let fty ← inferType a.getAppFn
  -- non-dependent first-order functions only
  let (doms, _) ← forallTelescope fty fun xs body => do
    if (← xs.anyM fun x => do return !(← x.fvarId!.getBinderInfo).isExplicit) then return (#[], body)
    return (← xs.mapM fun x => inferType x, body)
  if doms.size != args.size || doms.any (·.hasLooseBVars) then return none
  let worldTy (t : Expr) : MetaM Expr := do
    let t' ← whnfR t
    if t'.isConstOf ``Nat then return mkConst ``Int
    if t'.isConstOf ``Bool then return mkSort levelZero
    return t
  let lift (t x : Expr) : MetaM Expr := do
    let t' ← whnfR t
    if t'.isConstOf ``Nat then return natCast x
    if t'.isConstOf ``Bool then return boolTrue x
    return x
  -- arguments of the macro in `b`, by matching
  let ms ← doms.mapM fun t => do mkFreshExprMVar (← worldTy t)
  let tmpl ← mk ms
  if !(← withReducible (isDefEq tmpl b)) then return none
  let bargs ← ms.mapM instantiateMVars
  if bargs.any (·.hasExprMVar) then return none
  -- lemma `∀ xs, W(f xs) = M(W(xs))` (stated with the standard notations of Blaster's normal forms, e.g.,
  -- `x / y` for `Nat.div x y`)
  let lem? ← match (← get).macroLemmas.get? f with
    | some l => pure l
    | none =>
        let l ← try
            let stmt ← forallTelescope fty fun xs _ => do
              let lhs := w.lift (← standardForm (mkAppN (mkConst f lvls) xs))
              let rhs ← mk (← (xs.zip doms).mapM fun (x, t) => lift t x)
              mkForallFVars xs (← mkEq lhs rhs)
            -- NOTE: proved in the empty local context, such that the proof does not refer to local hypotheses
            if stmt.hasFVar then pure none else
            let some pf ← withLCtx {} {} ((← read).proveLemma stmt) | pure none
            some <$> mkAuxTheorem stmt pf
          catch _ => pure none
        modify fun s => { s with macroLemmas := s.macroLemmas.insert f l }
        pure l
  let some lem := lem? | return none
  -- `W(f as) = M(W(as))`, then congruence with `W(aᵢ) = bᵢ`
  let mut pf := mkAppN lem args
  let liftedArgs ← (args.zip doms).mapM fun (x, t) => lift t x
  let mut cur := liftedArgs
  for i in [:args.size] do
    let some pi ← walk args[i]! bargs[i]! | return none
    if liftedArgs[i]! == bargs[i]! then continue
    let ctx ← withLocalDeclD `z (← worldTy doms[i]!) fun z => do mkLambdaFVars #[z] (← mk (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx pi)
    cur := cur.set! i bargs[i]!
  return some (← mkExpectedTypeHint pf (← mkEq (w.lift a₀) b))

partial def walkSame (a b : Expr) : BridgeM (Option Expr) := do
  if a == b then return some (← mkEqRefl a)
  -- `Bool` terms interpreted as formulas, converted back with `decide`
  if b.isAppOfArity ``Decidable.decide 2 && (b.getArg! 1).isAppOfArity ``Classical.propDecidable 1 then
    if (← whnfR (← inferType a)).isConstOf ``Bool then
      let p := b.getArg! 0
      if let some h ← walk a p then return some (mkApp3 (mkConst ``bool_decide) a p h)
  -- `Int.ofNat x` is `↑x`
  if a.isAppOfArity ``Int.ofNat 1 && !a.appArg!.isRawNatLit then
    if let some p ← walk a.appArg! b then return some (← mkExpectedTypeHint p (← mkEq a b))
  if let some p ← walkMatcher .same a b then return some p
  if let some p ← walkIte .same a b then return some p
  -- `true = e` (resp. `false = e`, `e = false`) where `e` is translated as a formula
  if a.isAppOfArity ``Eq 3 && (a.getArg! 0).isConstOf ``Bool then
    let (l, r) := (a.getArg! 1, a.getArg! 2)
    -- same orientation: congruence
    let swapped := b.isAppOfArity ``Eq 3 && (b.getArg! 0).isConstOf ``Bool && (b.getArg! 2).isConstOf ``Bool.true &&
      l.isConstOf ``Bool.true
    let same := b.isAppOfArity ``Eq 3 && !swapped
    if !same then
      if l.isConstOf ``Bool.true then
        let some p ← walk r b | return none
        return some (mkApp3 (mkConst ``true_eq) r b p)
      if r.isConstOf ``Bool.true then return ← walk l b
      if b.isAppOfArity ``Not 1 then
        if l.isConstOf ``Bool.false then
          let some p ← walk r b.appArg! | return none
          return some (mkApp3 (mkConst ``false_eq) r b.appArg! p)
        if r.isConstOf ``Bool.false then
          let some p ← walk l b.appArg! | return none
          return some (mkApp3 (mkConst ``eq_false') l b.appArg! p)
  -- relations whose arguments are in different worlds
  -- NOTE: the sides of equations may be swapped by Blaster's normalization (e.g., `0 = x` for `x = 0`)
  if a.isAppOfArity ``Eq 3 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if aa[0]! != ba[0]! then
      let some w ← worldOf aa[0]! ba[0]! | return none
      let eqOf (x y : Expr) : BridgeM (Option Expr) := do
        let some px ← walk aa[1]! x | return none
        let some py ← walk aa[2]! y | return none
        match w with
        | .nat => return some (mkApp6 (mkConst ``nat_eq) aa[1]! aa[2]! x y px py)
        | .bool => return some (mkApp6 (mkConst ``bool_eq) aa[1]! aa[2]! x y px py)
        | .poly _ h => return some (← mkAppM ``Poly.eq_world #[h, px, py])
        | .same => return none
      if let some p ← eqOf ba[1]! ba[2]! then return some p
      if let some p ← eqOf ba[2]! ba[1]! then
        return some (← mkEqTrans p (mkApp3 (mkConst ``Local.eq_comm_eq [← getLevel ba[0]!]) ba[0]! ba[2]! ba[1]!))
      if !(w matches .same) then return none
  for (op, lem) in [(``LE.le, ``nat_le), (``LT.lt, ``nat_lt)] do
    if a.isAppOfArity op 4 && b.isAppOfArity op 4 then
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if (← whnfD aa[0]!).isConstOf ``Nat && (← whnfD ba[0]!).isConstOf ``Int then
        let some px ← walk aa[2]! ba[2]! | return none
        let some py ← walk aa[3]! ba[3]! | return none
        return some (← mkExpectedTypeHint (mkApp6 (mkConst lem) aa[2]! aa[3]! ba[2]! ba[3]! px py) (← mkEq a b))
  if a.isAppOfArity ``Iff 2 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let some pp ← walk aa[0]! ba[1]! | return none
    let some pq ← walk aa[1]! ba[2]! | return none
    return some (mkApp6 (mkConst ``iff_eq) aa[0]! aa[1]! ba[1]! ba[2]! pp pq)
  -- type predicates of Blaster's encoding (interpreted as `True`) as hypotheses
  if let .forallE _ t' body' _ := b then
    if t'.isConstOf ``True && !body'.hasLooseBVars && !(a.isForall && a.bindingDomain!.isConstOf ``True) then
      let some p ← walk a body' | return none
      return some (mkApp3 (mkConst ``true_imp) a body' p)
  -- quantifiers over the types of the polymorphic encoding, guarded by membership predicates
  if let some (b', h) ← interleaveGuards b then
    let some p ← walk a b' | return none
    return some (← mkEqTrans p h)
  if let some p ← walkPolyBinder a b then return some p
  -- quantifiers over `Nat`, translated as quantifiers over `Int` guarded by `0 ≤ x`
  if let some p ← walkNatBinder a b then return some p
  -- binders
  match a, b with
  | .forallE n t body bi, .forallE _ t' body' _ =>
      if !body.hasLooseBVars && !body'.hasLooseBVars then
        let some pt ← walk t t' | return none
        let some pb ← walk body body' | return none
        return some (← mkAppM ``implies_congr #[pt, pb])
      if t != t' && !(← isDefEq t t') then return none
      return ← withLocalDecl n bi t fun x => do
        let some pb ← walk (body.instantiate1 x) (body'.instantiate1 x) | return none
        return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] pb])
  | .lam n t body bi, .lam _ t' body' _ =>
      if t != t' && !(← isDefEq t t') then return none
      return ← withLocalDecl n bi t fun x => do
        let some pb ← walk (body.instantiate1 x) (body'.instantiate1 x) | return none
        return some (← mkFunExt (← mkLambdaFVars #[x] pb))
  | .proj s i e, .proj s' i' e' =>
      if s != s' || i != i' then return none
      let some pe ← walk e e' | return none
      -- NOTE: the structure may be in the world of the polymorphic encoding (see `walkPoly`)
      let ctx ← withLocalDeclD `z (← inferType e') fun z => mkLambdaFVars #[z] (.proj s i z)
      return some (← mkExpectedTypeHint (← mkCongrArg ctx pe) (← mkEq a b))
  | .mdata _ a', _ => return ← walk a' b
  | _, .mdata _ b' => return ← walk a b'
  | _, _ => pure ()
  if a.isApp && b.isApp then
    if let some p ← walkApp a b then return some p
  -- equations of the same world with swapped sides
  if a.isAppOfArity ``Eq 3 && b.isAppOfArity ``Eq 3 && a.getArg! 0 == b.getArg! 0 then
    if let some px ← walk (a.getArg! 1) (b.getArg! 2) then
      if let some py ← walk (a.getArg! 2) (b.getArg! 1) then
        let u ← getLevel (a.getArg! 0)
        let p ← mkCongr (← mkCongrArg (mkApp (mkConst ``Eq [u]) (a.getArg! 0)) px) py
        return some (← mkEqTrans p (mkApp3 (mkConst ``Local.eq_comm_eq [u]) (b.getArg! 0) (b.getArg! 2) (b.getArg! 1)))
  -- `Int` terms in `Nat` positions (`Int.toNat`)
  if b.isAppOfArity ``Int.toNat 1 then
    if (← whnfR (← inferType a)).isConstOf ``Nat then
      if let some p ← walk a b.appArg! then
        if (← inferType p).isAppOfArity ``Eq 3 && ((← inferType p).getArg! 0).isConstOf ``Int then
          return some (mkApp3 (mkConst ``nat_toNat) a b.appArg! p)
  if let some p ← walkMacro .same a b then return some p
  if let some p ← walkUnfold .same a b then return some p
  if let some p ← walkArith .same a b then return some p
  byDefEq a b

/-- `∀ n : Nat, p n` (resp. `∃ n : Nat, p n`) and `∀ x : Int, 0 ≤ x → q x` (resp. `∃ x : Int, 0 ≤ x ∧ q x`). -/
partial def walkNatBinder (a b : Expr) : BridgeM (Option Expr) := do
  let isGuard (g : Expr) : Bool := g.isAppOfArity ``LE.le 4 && g.appArg! == .bvar 0 && (g.getArg! 0).isConstOf ``Int
  -- (name, Nat body (one loose bvar), Int body without the guard (one loose bvar), lemma)
  let view? : Option (Name × Expr × Expr × Name) :=
    match a, b with
    | .forallE n t p _, .forallE _ t' g _ =>
        if t.isConstOf ``Nat && t'.isConstOf ``Int then
          match g with
          | .forallE _ guard q _ =>
              if isGuard guard && !(q.hasLooseBVarInExplicitDomain 0 false) && !q.hasLooseBVar 0 then
                some (n, p, q.lowerLooseBVars 1 1, ``nat_forall)
              else none
          | _ => none
        else none
    | _, _ =>
        if a.isAppOfArity ``Exists 2 && b.isAppOfArity ``Exists 2 && (a.getArg! 0).isConstOf ``Nat && (b.getArg! 0).isConstOf ``Int then
          match a.getArg! 1, b.getArg! 1 with
          | .lam n _ p _, .lam _ _ g _ =>
              if g.isAppOfArity ``And 2 && isGuard (g.getArg! 0) then some (n, p, g.getArg! 1, ``nat_exists) else none
          | _, _ => none
        else none
  let some (n, p, q, lem) := view? | return none
  withLocalDeclD n (mkConst ``Nat) fun x => do
    let some h ← walk (p.instantiate1 x) (q.instantiate1 (natCast x)) | return none
    let pl := mkLambda n .default (mkConst ``Nat) p
    let ql := mkLambda n .default (mkConst ``Int) q
    let pf := mkApp3 (mkConst lem) pl ql (← mkLambdaFVars #[x] h)
    return some (← mkExpectedTypeHint pf (← mkEq a b))

/-- `∀ x : T, P x` (resp. `∃ x : T, P x`) and `∀ y : D, Img w y → Q y` (resp. `∃ y : D, Img w y ∧ Q y`) where
    `w : T → D` is the world of `T` in the polymorphic encoding (see `Poly`). -/
partial def walkPolyBinder (a b : Expr) : BridgeM (Option Expr) := do
  -- (binder name, `T`, body of `P`, `D`, guard, body of `Q` (with one loose bound variable each), `∃`)
  let view? : Option (Name × Expr × Expr × Expr × Expr × Expr × Bool) :=
    match a, b with
    | .forallE n t p _, .forallE _ d (.forallE _ guard q _) _ =>
        if q.hasLooseBVar 0 then none else some (n, t, p, d, guard, q.lowerLooseBVars 1 1, false)
    | _, _ =>
        if a.isAppOfArity ``Exists 2 && b.isAppOfArity ``Exists 2 then
          match a.getArg! 1, b.getArg! 1 with
          | .lam n t p _, .lam _ d g _ =>
              if g.isAppOfArity ``And 2 then some (n, t, p, d, g.getArg! 0, g.getArg! 1, true) else none
          | _, _ => none
        else none
  let some (n, t, p, d, guard, q, ex) := view? | return none
  if t.hasLooseBVars || d.hasLooseBVars || !Poly.hasUniv d then return none
  let some (w, _) ← Poly.mkWorld t d | return none
  -- the guard is the membership predicate of the world, or its definition expanded by the backend (e.g., for
  -- the datatypes of the user, see `polyGuardEq`)
  let ok ← withLocalDeclD `y d fun y => do
    withReducible (isDefEq (guard.instantiate1 y) (← mkAppM ``Poly.Img #[w, y]))
  let pg? ← if ok then pure none else
    match ← polyGuardEq w d guard with
    | some pg => pure (some pg)
    | none => return none
  withLocalDeclD n t fun x => do
    let some h ← walk (p.instantiate1 x) (q.instantiate1 (Poly.applyWorld w x)) | return none
    let pf ← mkAppOptM (if ex then ``Poly.exists_world else ``Poly.forall_world)
      (#[t, d, w, mkLambda n .default t p, mkLambda `y .default d q, ← mkLambdaFVars #[x] h].map some)
    let some pg := pg? | return some (← mkExpectedTypeHint pf (← mkEq a b))
    -- `(∀ y, Img w y → Q y) = (∀ y, G y → Q y)` (resp. `∃`)
    let pc ← withLocalDeclD `y d fun y => do
      let q := q.instantiate1 y
      let e := mkApp pg y
      if ex then
        mkLambdaFVars #[y] (← mkCongrFun (← mkCongrArg (mkConst ``And) e) q)
      else mkLambdaFVars #[y] (← mkAppM ``implies_congr #[e, ← mkEqRefl q])
    let pc ← if ex then mkCongrArg (mkApp (mkConst ``Exists [← getLevel d]) d) (← mkFunExt pc)
      else mkAppM ``forall_congr #[pc]
    return some (← mkExpectedTypeHint (← mkEqTrans pf pc) (← mkEq a b))

/-- `∀ y, Img w y = G y` where `G` is the definition of the membership predicate of a datatype (e.g., `@isEither` or
    `@isOption`, macros expanded by the backend in the asserted formulas), by case analysis on `y` and the images of
    the constructors (see `Poly.IndWorldLemmas`), once per statement (closed over its free variables). -/
partial def polyGuardEq (w d guard : Expr) : BridgeM (Option Expr) := do
  let stmt ← withLocalDeclD `y d fun y => do
    mkForallFVars #[y] (← mkEq (← mkAppM ``Poly.Img #[w, y]) (guard.instantiate1 y))
  let xs ← fvarClosure #[stmt]
  let closed ← mkForallFVars xs stmt
  if closed.hasFVar || closed.hasMVar then return none
  let lem? ← match (← get).natLemmas.get? closed with
    | some l => pure l
    | none =>
        let extra ← Poly.indWorldSimpTerms closed
        let l ← try
            let some pf ← withLCtx {} {} (Blaster.Reconstruct.proveWithTactic closed
                (← `(tactic| (intros; blaster_poly_cases <;> simp_all [Poly.img_list_nil, Poly.img_list_cons,
                  Poly.img_option_none, Poly.img_option_some, Poly.img_prod, $extra,*]))))
              | pure none
            pure (some (← mkAuxTheorem closed pf))
          catch _ => pure none
        if l.isNone then dbg m!"bridge: membership definition not proved: {closed}"
        modify fun s => { s with natLemmas := s.natLemmas.insert closed l }
        pure l
  return lem?.map (mkAppN · xs)

/-- `W(f x) = F X` where `f : A → B` is a function of the polymorphic encoding (e.g., `f : α → β` with `α`, `β` sort
    variables), whose world is `liftFun wa wb dflt`: from `liftFun wa wb dflt f = F` and `wa x = X`. The proof
    states `wb (f x) = F X`, i.e., `W(f x) = F X` up to definitional unfolding. -/
partial def walkLiftedApp (a b : Expr) : BridgeM (Option Expr) := do
  let .app fa xa := a | return none
  let .app fb xb := b | return none
  let tF ← inferType fb
  if !Poly.hasUniv tF then return none
  let some (wf, hf) ← Poly.mkWorld (← inferType fa) tF | return none
  if !(wf.isAppOfArity ``Poly.liftFun 7 && hf.isAppOfArity ``Poly.liftFun_injective 9) then return none
  let wa := wf.getArg! 4
  let some pf ← walk fa fb | return none
  let some px ← walk xa xb | return none
  let pf ← mkExpectedTypeHint pf (← mkEq (Poly.applyWorld wf fa) fb)
  let px ← mkExpectedTypeHint px (← mkEq (Poly.applyWorld wa xa) xb)
  return some (← mkAppM ``Poly.app_world #[hf.getArg! 5, pf, px])

/-- `W(f ts xs) = f ts' ys` where `f` is a polymorphic function at sort variables in the goal (type arguments `ts`)
    and at the universe in the interpretation (`ts'`, see `Poly.instantiateUniv`): from the naturality lemma
    `∀ αs xs, f ts' (W xs) = W (f ts xs)` (`αs` the sort variables of `ts`, proved once per statement by
    `blaster_poly_nat`) and `W(xᵢ) = yᵢ`. -/
partial def walkPolyApp (a b : Expr) : BridgeM (Option Expr) := do
  let fa := a.getAppFn
  let fb := b.getAppFn
  let .const f _ := fa | return none
  -- relations, `ite` and matchers have their own lemmas
  if [``Eq, ``Ne, ``HEq, ``ite, ``dite].contains f || (← isMatcher f) || isCasesOnRecursor (← getEnv) f then
    return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  let info ← getFunInfoNArgs fa as.size
  -- type and instance arguments
  let isType (i : Nat) : Bool := (info.paramInfo[i]?.map fun p => p.hasFwdDeps || p.isInstImplicit).getD false
  let tpos := (List.range as.size).filter isType
  if !(tpos.any fun i => Poly.hasUniv bs[i]!) || tpos.any (fun i => bs[i]!.hasFVar) then return none
  -- the sort variables of the instantiation in the goal
  let σ := (tpos.foldl (fun s i => collectFVars s as[i]!) {}).fvarIds.map mkFVar
  if ← σ.anyM fun α => do return !(← inferType α).isSort || (← isProp (← inferType α)) then return none
  -- domains of the value arguments (non-dependent)
  let mut tyA ← inferType fa
  let mut tyB ← inferType fb
  let mut doms : Array (Expr × Expr) := #[]
  for i in [:as.size] do
    let .forallE _ dA bA _ ← whnf tyA | return none
    let .forallE _ dB bB _ ← whnf tyB | return none
    if isType i then
      tyA := bA.instantiate1 as[i]!
      tyB := bB.instantiate1 bs[i]!
    else
      if bA.hasLooseBVars || bB.hasLooseBVars then return none
      doms := doms.push (dA, dB)
      tyA := bA
      tyB := bB
  let (rA, rB) := (tyA, tyB)
  let decls := doms.mapIdx fun k (dA, _) => (Name.mkSimple s!"x{k}", fun (_ : Array Expr) => pure dA)
  let stmt? ← withLocalDeclsD decls fun xs => do
    let mut argsA := #[]
    let mut argsB := #[]
    let mut k := 0
    for i in [:as.size] do
      if isType i then
        argsA := argsA.push as[i]!
        argsB := argsB.push bs[i]!
      else
        let (dA, dB) := doms[k]!
        let x := xs[k]!
        argsA := argsA.push x
        argsB := argsB.push (← match ← Poly.mkWorld dA dB with
          | some (w, _) => pure (Poly.applyWorld w x)
          | none => do if ← isDefEq dA dB then pure x else throwError "walkPolyApp: no world for {dA}")
        k := k + 1
    let rhs ← match ← Poly.mkWorld rA rB with
      | some (w, _) => pure (Poly.applyWorld w (mkAppN fa argsA))
      | none => do if ← isDefEq rA rB then pure (mkAppN fa argsA) else throwError "walkPolyApp: no world for {rA}"
    let stmt ← mkForallFVars (σ ++ xs) (← mkEq (mkAppN fb argsB) rhs)
    return if stmt.hasFVar then none else some stmt
  let some stmt := stmt? | return none
  let lem? ← match (← get).natLemmas.get? stmt with
    | some l => pure l
    | none =>
        let cached := (← natLemmaCache.get).get? stmt
        let env ← getEnv
        let valid (l : Expr) : Bool := match l.getAppFn with
          | .const n _ => env.contains n
          | _ => false
        let l ← if let some l := cached.filter valid then pure (some l) else
          try
            -- NOTE: proved in the empty local context (the statement is closed)
            let some pf ← withLCtx {} {} (Blaster.Reconstruct.proveWithTactic stmt (← `(tactic| blaster_poly_nat)))
              | pure none
            let l ← mkAuxTheorem stmt pf
            natLemmaCache.modify (·.insert stmt l)
            pure (some l)
          catch _ => pure none
        if l.isNone then dbg m!"bridge: naturality not proved: {stmt}"
        modify fun s => { s with natLemmas := s.natLemmas.insert stmt l }
        pure l
  let some lem := lem? | return none
  let vals := (List.range as.size).filter (!isType ·) |>.toArray.map (as[·]!)
  -- `W(f ts xs) = f ts' (W xs)`, then congruence with `W(xᵢ) = yᵢ`
  let mut pf ← mkEqSymm (mkAppN lem (σ ++ vals))
  let mut cur := (← inferType pf).appArg!.getAppArgs
  for i in [:as.size] do
    if isType i || cur[i]! == bs[i]! then continue
    let some p ← walk as[i]! bs[i]! | return none
    let ta ← inferType cur[i]!
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fb (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx (← mkExpectedTypeHint p (← mkEq cur[i]! bs[i]!)))
    cur := cur.set! i bs[i]!
  return some pf

/-- Proof of `False` from the hypotheses of the branch (e.g., `d = []` and `¬ (List.casesOn d True fun _ _ => False)`). -/
partial def absurdByFacts : BridgeM (Option Expr) := do
  let facts := (← read).facts
  if facts.isEmpty then return none
  withRestrictedLCtx facts do
    Blaster.Reconstruct.proveWithTactic (mkConst ``False) (← `(tactic| (subst_vars; simp_all)))

/-- Case analyses on lists and options of the polymorphic encoding (testers and selectors, e.g., in the `ite`
    encoding of a `match` on a list of a sort variable): `W(T.casesOn d ms) = T.casesOn D ms'` from `W d = D` and,
    for each constructor, `W(mᵢ fs) = mᵢ' (W fs)` under `d = cᵢ fs`, or a contradiction of `d = cᵢ fs` with the
    hypotheses of the branch (e.g., for the default values of selectors, see `Poly.list_casesOn_world`). -/
partial def walkPolyCasesOn (a b : Expr) : BridgeM (Option Expr) := do
  let .const f _ := a.getAppFn | return none
  let (lem, map, nargs) ← if f == ``List.casesOn then pure (``Poly.list_casesOn_world, ``List.map, 5)
    else if f == ``Option.casesOn then pure (``Poly.option_casesOn_world, ``Option.map, 4) else return none
  if !(a.isAppOfArity f nargs && b.isAppOfArity f nargs) then return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  let (d, dd) := (as[2]!, bs[2]!)
  let some (wd, _) ← Poly.mkWorld (← inferType d) (← inferType dd) | return none
  if !wd.isAppOfArity map 3 then return none
  let w := wd.appArg!
  -- non-dependent motives, and the world of the results
  let .lam _ _ c _ := as[1]! | return none
  let .lam _ _ c' _ := bs[1]! | return none
  if c.hasLooseBVars || c'.hasLooseBVars then return none
  let wr ← match ← Poly.mkWorld c c' with
    | some (wr, _) => pure wr
    | none => if ← isDefEq c c' then pure (mkLambda `x .default c (.bvar 0)) else return none
  let some hd ← walk d dd | return none
  -- `∀ fs, d = cᵢ fs → wr (mᵢ fs) = mᵢ' (W fs)`
  let minor (fields : Array (Name × Expr)) (ctor : Array Expr → MetaM Expr) (lifted : Array Expr → MetaM (Array Expr))
      (m m' : Expr) : BridgeM (Option Expr) :=
    withLocalDeclsD (fields.map fun (n, t) => (n, fun _ => pure t)) fun fs => do
    withLocalDeclD `e (← mkEq d (← ctor fs)) fun e => withReader (fun cfg => { cfg with facts := cfg.facts.push e }) do
      let l := (mkAppN m fs).headBeta
      let r := (mkAppN m' (← lifted fs)).headBeta
      let goal ← mkEq (Poly.applyWorld wr l) r
      let p ← match ← walk l r with
        | some p => pure (some (← mkExpectedTypeHint p goal))
        | none => do
            let some pf ← absurdByFacts | pure none
            pure (some (← mkFalseElim goal pf))
      let some p := p | return none
      some <$> mkLambdaFVars (fs.push e) p
  let ta := as[0]!
  if f == ``List.casesOn then
    let some hn ← minor #[] (fun _ => mkAppOptM ``List.nil #[ta]) (fun _ => pure #[]) as[3]! bs[3]! | return none
    let some hc ← minor #[(`h, ta), (`t, ← mkAppM ``List #[ta])] (fun fs => mkAppM ``List.cons #[fs[0]!, fs[1]!])
        (fun fs => do return #[Poly.applyWorld w fs[0]!, ← mkAppM ``List.map #[w, fs[1]!]]) as[4]! bs[4]! | return none
    return some (← mkAppM lem #[wr, hd, hn, hc])
  else
    let some hn ← minor #[] (fun _ => mkAppOptM ``Option.none #[ta]) (fun _ => pure #[]) as[3]! bs[3]! | return none
    let some hc ← minor #[(`v, ta)] (fun fs => mkAppM ``Option.some #[fs[0]!])
        (fun fs => do return #[Poly.applyWorld w fs[0]!]) as[4]! bs[4]! | return none
    return some (← mkAppM lem #[wr, hd, hn, hc])

/-- Constructors of the inductive types over sort variables (see `Poly.mkIndWorld`): `W (C xs) = C' ys` from the
    equation `W (C xs) = C' (Ŵ xs)` of the constructor in the world (see `Poly.IndWorldLemmas`) and `Ŵᵢ xᵢ = yᵢ`. -/
partial def walkPolyCtor (w a b : Expr) : BridgeM (Option Expr) := do
  let .const c _ := a.getAppFn | return none
  if !b.getAppFn.isConstOf c || a.getAppNumArgs != b.getAppNumArgs then return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  if a.getAppNumArgs != info.numParams + info.numFields then return none
  let some lemmas ← Poly.indWorldLemmas? w | return none
  let some (_, eqn) := lemmas.eqns.find? (·.1 == c) | return none
  let pe := mkAppN eqn (a.getAppArgs.extract info.numParams a.getAppNumArgs)
  let some (_, _, rhs) := (← inferType pe).eq? | return none
  let ra := rhs.getAppArgs
  let ba := b.getAppArgs
  for i in [:info.numParams] do
    if !(← isDefEq ra[i]! ba[i]!) then return none
  let mut pf ← mkEqRefl (mkAppN rhs.getAppFn (ra.extract 0 info.numParams))
  for i in [info.numParams:ra.size] do
    let p ← if ← isProof ra[i]! then mkEqRefl ra[i]! else
      let some p ← walk (a.getArg! i) ba[i]! | return none
      pure p
    pf ← mkCongr pf (← mkExpectedTypeHint p (← mkEq ra[i]! ba[i]!))
  return some (← mkEqTrans pe pf)

/-- Case analyses on the inductive types over sort variables (see `Poly.mkIndWorld`), e.g., the testers and selectors
    of the encoding of a `match`: `wr (T.casesOn d ms) = T.casesOn D ms'` from `W d = D` and, for each constructor
    `C`, `wr (m fs) = m' (Ŵ fs)` under `d = C fs` (see `walkPolyCasesOn`), by case analysis on `d` and the equations
    of the constructors in the world (see `Poly.IndWorldLemmas`). -/
partial def walkPolyIndCasesOn (a b : Expr) : BridgeM (Option Expr) := do
  let .const f lvls := a.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? f.getPrefix | return none
  if info.numIndices != 0 then return none
  let np := info.numParams
  if a.getAppNumArgs != np + 2 + info.numCtors || b.getAppNumArgs != a.getAppNumArgs then return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  let (d, dd) := (as[np + 1]!, bs[np + 1]!)
  let some (wd, _) ← Poly.mkWorld (← inferType d) (← inferType dd) | return none
  let some lemmas ← Poly.indWorldLemmas? wd | return none
  -- non-dependent motives, and the world of the results
  let .lam _ _ c _ := as[np]! | return none
  let .lam _ _ c' _ := bs[np]! | return none
  if c.hasLooseBVars || c'.hasLooseBVars then return none
  let wr ← match ← Poly.mkWorld c c' with
    | some (wr, _) => pure wr
    | none => if ← isDefEq c c' then pure (mkLambda `x .default c (.bvar 0)) else return none
  let some hd ← walk d dd | return none
  let ctors := info.ctors.toArray
  -- for each constructor `C`, with its equation `W (C fs) = C' (Ŵ fs)`: `∀ fs, d₀ = C fs → wr (m fs) = m' (Ŵ fs)`
  let some eqns := ctors.mapM fun ctor => (lemmas.eqns.find? (·.1 == ctor)).map (·.2) | return none
  let hyp (d₀ : Expr) (k : Nat) : MetaM Expr := do forallTelescope (← inferType eqns[k]!) fun fs e => do
    let some (_, l, r) := e.eq? | throwError "walkPolyIndCasesOn: equation expected"
    let ys := r.getAppArgs.extract np r.getAppNumArgs
    mkForallFVars fs (← mkArrow (← mkEq d₀ l.appArg!)
      (← mkEq (Poly.applyWorld wr (mkAppN as[np + 2 + k]! fs).headBeta) (mkAppN bs[np + 2 + k]! ys).headBeta))
  let mut hs := #[]
  for k in [:ctors.size] do
    let h ← forallTelescope (← inferType eqns[k]!) fun fs e => do
      let some (_, l, r) := e.eq? | return none
      let ys := r.getAppArgs.extract np r.getAppNumArgs
      withLocalDeclD `e (← mkEq d l.appArg!) fun e => withReader (fun cfg => { cfg with facts := cfg.facts.push e }) do
        let lhs := (mkAppN as[np + 2 + k]! fs).headBeta
        let rhs := (mkAppN bs[np + 2 + k]! ys).headBeta
        let goal ← mkEq (Poly.applyWorld wr lhs) rhs
        let p ← match ← walk lhs rhs with
          | some p => pure (some (← mkExpectedTypeHint p goal))
          | none => do
              let some pf ← absurdByFacts | pure none
              pure (some (← mkFalseElim goal pf))
        let some p := p | return none
        some <$> mkLambdaFVars (fs.push e) p
    let some h := h | return none
    hs := hs.push h
  -- `T.casesOn (motive := fun d₀ => ∀ D, W d₀ = D → hyps d₀ → wr (T.casesOn d₀ ms) = T.casesOn D ms') d …`
  let tD ← inferType dd
  let motive ← withLocalDeclD `d (← inferType d) fun d₀ => do
    let body ← withLocalDeclD `D tD fun D => do
      let mut concl ← mkEq (Poly.applyWorld wr (mkAppN a.getAppFn (as.set! (np + 1) d₀))) (mkAppN b.getAppFn (bs.set! (np + 1) D))
      for k in (List.range ctors.size).reverse do concl ← mkArrow (← hyp d₀ k) concl
      mkForallFVars #[D] (← mkArrow (← mkEq (Poly.applyWorld wd d₀) D) concl)
    mkLambdaFVars #[d₀] body
  let mut minors := #[]
  for k in [:ctors.size] do
    let m ← forallTelescope (← inferType eqns[k]!) fun fs e => do
      let some (_, l, _) := e.eq? | throwError "walkPolyIndCasesOn: equation expected"
      let cfs := l.appArg!
      let body ← instantiateForall (motive.beta #[cfs]) #[]
      let .forallE _ _ _ _ := body | throwError "walkPolyIndCasesOn: motive"
      withLocalDeclD `D tD fun D => do
      withLocalDeclD `hD (← mkEq (Poly.applyWorld wd cfs) D) fun hD => do
      let hTys ← (List.range ctors.size).toArray.mapM fun j => hyp cfs j
      withLocalDeclsD (hTys.mapIdx fun j t => (Name.mkSimple s!"h{j}", fun _ => pure t)) fun hs' => do
        -- `wr (m fs) = m' (Ŵ fs)` by the hypothesis, and `T.casesOn D ms' = m' (Ŵ fs)` by the equation of `C`
        let p₁ ← mkAppM' hs'[k]! (fs.push (← mkEqRefl cfs))
        let some (_, _, r₁) := (← inferType p₁).eq? | throwError "walkPolyIndCasesOn: equation expected"
        let eD ← mkEqTrans (← mkEqSymm hD) (mkAppN eqns[k]! fs)
        let ctx ← withLocalDeclD `z tD fun z => do mkLambdaFVars #[z] (mkAppN b.getAppFn (bs.set! (np + 1) z))
        let p₂ ← mkExpectedTypeHint (← mkCongrArg ctx eD)
          (← mkEq (mkAppN b.getAppFn (bs.set! (np + 1) D)) r₁)
        let p ← mkEqTrans p₁ (← mkEqSymm p₂)
        let goal ← mkEq (Poly.applyWorld wr (mkAppN a.getAppFn (as.set! (np + 1) cfs)))
          (mkAppN b.getAppFn (bs.set! (np + 1) D))
        mkLambdaFVars (fs ++ #[D, hD] ++ hs') (← mkExpectedTypeHint p goal)
    minors := minors.push m
  let casesOn := mkConst f (levelZero :: lvls.tail!)
  let pf := mkAppN casesOn ((as.extract 0 np).push motive |>.push d |>.append minors)
  return some (mkAppN pf (#[dd, hd] ++ hs))

/-- `w a = b` where `w` is the world of the type of `a` in the polymorphic encoding (see `Poly.mkWorld`), with
    `h` the proof of its injectivity. -/
partial def walkPoly (w h a b : Expr) : BridgeM (Option Expr) := do
  let la := Poly.applyWorld w a
  if la == b then return some (← mkEqRefl b)
  match a, b with
  | .mdata _ a', _ => return ← walk a' b
  | _, .mdata _ b' => return ← walk a b'
  -- projections of structures over sort variables (see `Poly.mkIndWorld`): `(W e).i` is `w (e.i)` (by η for
  -- structures and ι-reduction), from `W e = e'`
  | .proj s i e, .proj s' i' e' =>
      if s != s' || i != i' then return none
      let some pe ← walk e e' | return none
      let ctx ← withLocalDeclD `z (← inferType e') fun z => mkLambdaFVars #[z] (.proj s i z)
      return some (← mkExpectedTypeHint (← mkCongrArg ctx pe) (← mkEq la b))
  | _, _ => pure ()
  -- η-expansion of the goal side (e.g., `Prod.mk` for `fun x y => (x, y)`)
  if b.isLambda && !a.isLambda then
    let .forallE n t _ bi ← whnf (← inferType a) | return none
    let some p ← walk (mkLambda n bi t (mkApp a (.bvar 0))) b | return none
    return some (← mkExpectedTypeHint p (← mkEq la b))
  match a, b with
  | .lam n t body _, .lam _ d body' _ =>
      -- functions: `liftFun wa wb dflt (fun x => t) = fun y => t'` from `wb t = t'[y := wa x]` and `t'` being
      -- `dflt` outside of the domain (e.g., the identity)
      if !(w.isAppOfArity ``Poly.liftFun 7 && h.isAppOfArity ``Poly.liftFun_injective 9) then return none
      let (wa, wb, dflt) := (w.getArg! 4, w.getArg! 5, w.getArg! 6)
      let ts := #[w.getArg! 0, w.getArg! 1, w.getArg! 2, w.getArg! 3]
      -- lambda terms guarded by the membership predicates of their parameters (see `Driver.guardedLambda`):
      -- `liftFun wa wb dflt (fun x => t) = fun y => if Img wa y then t' else dflt y` from `wb t = t'[y := wa x]`
      if let some (c, x', y', _) := classicalIte? body' then
        if ← withLocalDeclD `y d fun y => do
            withReducible (isDefEq (c.instantiate1 y) (← mkAppM ``Poly.Img #[wa, y])) then
          let ok ← withLocalDeclD `y d fun y => do withReducible (isDefEq (y'.instantiate1 y) (Poly.applyWorld dflt y))
          if ok then
            let some hb ← withLocalDeclD n t fun x => do
                let some p ← walk (body.instantiate1 x) (x'.instantiate1 (Poly.applyWorld wa x)) | return none
                some <$> mkLambdaFVars #[x] p
              | return none
            let pf ← mkAppOptM ``Poly.lam_world_ite
              ((ts ++ #[wa, h.getArg! 5, wb, dflt, a, .lam `y d x' .default, hb]).map some)
            return some (← mkExpectedTypeHint pf (← mkEq la b))
      let some hb ← withLocalDeclD n t fun x => do
          let some p ← walk (body.instantiate1 x) (body'.instantiate1 (Poly.applyWorld wa x)) | return none
          some <$> mkLambdaFVars #[x] p
        | return none
      let some hout ← withLocalDeclD `y d fun y => do
          withLocalDeclD `hy (mkNot (← mkAppM ``Poly.Img #[wa, y])) fun hy => do
          let l := Poly.applyWorld dflt y
          let r := body'.instantiate1 y
          if !(← withReducible (isDefEq l r)) then return none
          some <$> mkLambdaFVars #[y, hy] (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r))
        | return none
      return some (← mkAppOptM ``Poly.lam_world ((ts ++ #[wa, h.getArg! 5, wb, dflt, a, b, hb, hout]).map some))
  | _, _ => pure ()
  -- `ite` on the goal side
  if let some (α, c, inst, x, y, pa) ← iteView? a then
    if let some (c', x', y', _) := classicalIte? b then
      let some pc ← walk c c' | return none
      let branch (cond v v' : Expr) : BridgeM (Option Expr) :=
        withLocalDeclD `hc cond fun hc => withReader (fun cfg => { cfg with facts := cfg.facts.push hc }) do
          let some p ← walk v v' | return none
          some <$> mkLambdaFVars #[hc] (← mkExpectedTypeHint p (← mkEq (Poly.applyWorld w v) v'))
      let some px ← branch c x x' | return none
      let some py ← branch (mkNot c) y y' | return none
      let pIte ← mkAppOptM ``Poly.ite_world (#[α, ← inferType b, w, c, c', inst, x, y, x', y', pc, px, py].map some)
      return some (← mkEqTrans (← mkCongrArg w pa) pIte)
  -- constructors of the functors (e.g., `List.map w (x :: xs)` is `w x :: List.map w xs`)
  let ctor (map ctor : Name) (mapArity ctorArity : Nat) (ws : Array Expr) : BridgeM (Option Expr) := do
    if !(w.isAppOfArity map mapArity && a.isAppOfArity ctor ctorArity && b.isAppOfArity ctor ctorArity) then
      return none
    let nps := ctorArity - ws.size
    let mut pf ← mkEqRefl (mkAppN b.getAppFn (b.getAppArgs.extract 0 nps))
    for i in [:ws.size] do
      let (x, x') := (a.getArg! (nps + i), b.getArg! (nps + i))
      let some p ← walk x x' | return none
      pf ← mkCongr pf (← mkExpectedTypeHint p (← mkEq (Poly.applyWorld ws[i]! x) x'))
    return some (← mkExpectedTypeHint pf (← mkEq la b))
  if w.isAppOfArity ``List.map 3 then
    if let some p ← ctor ``List.map ``List.cons 3 3 #[w.getArg! 2, w] then return some p
  if w.isAppOfArity ``Option.map 3 then
    if let some p ← ctor ``Option.map ``Option.some 3 2 #[w.getArg! 2] then return some p
  if w.isAppOfArity ``Prod.map 6 then
    if let some p ← ctor ``Prod.map ``Prod.mk 6 4 #[w.getArg! 4, w.getArg! 5] then return some p
  if let some p ← walkPolyCtor w a b then return some p
  if let some p ← walkMatcher (.poly w h) a b then return some p
  byDefEq la b

/-- Functions of the user inlined by Blaster's optimizer: `W(f xs) = W(b)` by the unfolding equation of `f`,
    then `W(b) = b'` (at most `Cfg.unfoldDepth` nested unfoldings). -/
partial def walkUnfold (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  if (← read).unfoldDepth == 0 then return none
  let .const f _ := a.getAppFn | return none
  if b.getAppFn.isConstOf f || !(← isUserFunction f) then return none
  let some (u, eqn) ← unfoldEqn? a | return none
  let some p ← withReader (fun c => { c with unfoldDepth := c.unfoldDepth - 1 }) (walk u b) | return none
  return some (← mkEqTrans (← w.liftEq eqn) p)

/-- Arithmetic terms equal modulo the normalizations of Blaster's optimizer (e.g., the reordering of the operands
    of `+` in the definitions of functions): the arithmetic atoms of `a` are related to atoms of `b` (`walk`),
    then `W(a) = b` is proved by `omega` from these equations (and the hypotheses of the branch). -/
partial def walkArith (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  if !(Local.isArithHead a && Local.isArithHead b) then return none
  if !(w == .nat || (w == .same && (← whnfR (← inferType a)).isConstOf ``Int)) then return none
  let as ← Local.arithAtoms a
  let bs ← Local.arithAtoms b
  if as.isEmpty || as.size > 8 || bs.size > 8 then return none
  let mut eqs : Array (Expr × Expr) := #[]
  for x in as do
    let mut found := false
    for y in bs do
      if let some p ← walk x y then
        eqs := eqs.push (← inferType p, p)
        found := true
        break
    if !found then return none
  let goal ← mkEq (w.lift a) b
  let decls := eqs.mapIdx fun i (t, _) => (Name.mkSimple s!"e{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun hs => do
    let some pf ← withRestrictedLCtx ((hs ++ (← read).facts).push goal) (omegaProof? goal) | return none
    return some (mkAppN (← mkLambdaFVars hs pf) (eqs.map (·.2)))

/-- `(↑a : Int) = b` -/
partial def walkNat (a b : Expr) : BridgeM (Option Expr) := do
  let la := natCast a
  if la == b then return some (← mkEqRefl b)
  if b.isAppOfArity ``Nat.cast 3 then
    let some p ← walk a b.appArg! | return none
    return some (← mkExpectedTypeHint (← mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) p) (← mkEq la b))
  if let some p ← walkMatcher .nat a b then return some p
  if let some p ← walkIte .nat a b then return some p
  let binop (lem : Name) : BridgeM (Option Expr) := do
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let (x, y) := (aa[aa.size - 2]!, aa[aa.size - 1]!)
    let some px ← walk x ba[4]! | return none
    let some py ← walk y ba[5]! | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst lem) x y ba[4]! ba[5]! px py) (← mkEq la b))
  if (a.isAppOfArity ``Nat.add 2 || a.isAppOfArity ``HAdd.hAdd 6) && b.isAppOfArity ``HAdd.hAdd 6 then
    if let some p ← binop ``nat_add then return some p
  if (a.isAppOfArity ``Nat.mul 2 || a.isAppOfArity ``HMul.hMul 6) && b.isAppOfArity ``HMul.hMul 6 then
    if let some p ← binop ``nat_mul then return some p
  if (a.isAppOfArity ``Nat.pow 2 || a.isAppOfArity ``HPow.hPow 6) && b.isAppOfArity ``HPow.hPow 6 then
    let aa := a.getAppArgs
    if (b.getArg! 5).isAppOfArity ``Int.toNat 1 then
      let (x, y) := (aa[aa.size - 2]!, aa[aa.size - 1]!)
      let (x', y') := (b.getArg! 4, (b.getArg! 5).appArg!)
      if let some px ← walk x x' then
        if let some py ← walk y y' then
          return some (← mkExpectedTypeHint (mkApp6 (mkConst ``nat_pow) x y x' y' px py) (← mkEq la b))
  -- subtraction (resp. `Int.toNat`) under the hypotheses of the branch (e.g., the variables of `n + 1` patterns)
  if (a.isAppOfArity ``Nat.sub 2 || a.isAppOfArity ``HSub.hSub 6) && b.isAppOfArity ``HSub.hSub 6 then
    let aa := a.getAppArgs
    let (x, y) := (aa[aa.size - 2]!, aa[aa.size - 1]!)
    if let some h ← byFacts (← mkAppM ``LE.le #[y, x]) then
      let ba := b.getAppArgs
      let some px ← walk x ba[4]! | return none
      let some py ← walk y ba[5]! | return none
      return some (← mkExpectedTypeHint (mkAppN (mkConst ``nat_sub_bridge) #[x, y, ba[4]!, ba[5]!, h, px, py]) (← mkEq la b))
  if a.isAppOfArity ``Int.toNat 1 && !(← read).facts.isEmpty then
    let x := a.appArg!
    if let some h ← byFacts (← mkAppM ``LE.le #[mkIntLit 0, x]) then
      if let some px ← walk x b then
        return some (← mkExpectedTypeHint (mkApp4 (mkConst ``toNat_bridge) x b h px) (← mkEq la b))
  if let some p ← walkMacro .nat a b then return some p
  if let some p ← walkUnfold .nat a b then return some p
  if let some p ← walkArith .nat a b then return some p
  byDefEq la b

/-- `(a = true) = b` -/
partial def walkBool (a b : Expr) : BridgeM (Option Expr) := do
  let la := boolTrue a
  if la == b then return some (← mkEqRefl b)
  if b.isAppOfArity ``Eq 3 && (b.getArg! 0).isConstOf ``Bool && (b.getArg! 2).isConstOf ``Bool.true then
    let some p ← walk a (b.getArg! 1) | return none
    return some (← mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) p)
  if a.isConstOf ``Bool.true && b.isConstOf ``True then return some (mkConst ``bool_true)
  if a.isConstOf ``Bool.false && b.isConstOf ``False then return some (mkConst ``bool_false)
  let bin (lem : Name) (op : Name) : BridgeM (Option Expr) := do
    if !b.isAppOfArity op 2 then return none
    let some px ← walk (a.getArg! 0) (b.getArg! 0) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 1) | return none
    return some (mkApp6 (mkConst lem) (a.getArg! 0) (a.getArg! 1) (b.getArg! 0) (b.getArg! 1) px py)
  if a.isAppOfArity ``and 2 then if let some p ← bin ``bool_and ``And then return some p
  if a.isAppOfArity ``or 2 then if let some p ← bin ``bool_or ``Or then return some p
  if a.isAppOfArity ``not 1 && b.isAppOfArity ``Not 1 then
    let some px ← walk a.appArg! b.appArg! | return none
    return some (mkApp3 (mkConst ``bool_not) a.appArg! b.appArg! px)
  if a.isAppOfArity ``Blaster.decide' 1 then
    let some p ← walk a.appArg! b | return none
    return some (mkApp3 (mkConst ``decide'_eq) a.appArg! b p)
  if a.isAppOfArity ``Decidable.decide 2 then
    let some p ← walk (a.getArg! 0) b | return none
    return some (mkApp4 (mkConst ``decide_eq) (a.getArg! 0) b (a.getArg! 1) p)
  if a.isAppOfArity ``BEq.beq 4 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let some px ← walk aa[2]! ba[1]! | return none
    let some py ← walk aa[3]! ba[2]! | return none
    let ty ← whnfD aa[0]!
    if ty.isConstOf ``Nat && (← whnfD ba[0]!).isConstOf ``Int then
      let some lawful ← (try some <$> synthInstance (mkApp2 (mkConst ``LawfulBEq [levelZero]) aa[0]! aa[1]!) catch _ => pure none) | return none
      return some (mkAppN (mkConst ``nat_beq) #[aa[1]!, lawful, aa[2]!, aa[3]!, ba[1]!, ba[2]!, px, py])
    if ← isDefEq aa[0]! ba[0]! then
      let u ← getLevel aa[0]!
      let some lawful ← (try some <$> synthInstance (mkApp2 (mkConst ``LawfulBEq [u.dec.getD levelZero]) aa[0]! aa[1]!) catch _ => pure none) | return none
      return some (mkAppN (mkConst ``beq_eq [u.dec.getD levelZero]) #[aa[0]!, aa[1]!, lawful, aa[2]!, aa[3]!, ba[1]!, ba[2]!, px, py])
  if a.isAppOfArity ``Nat.ble 2 && b.isAppOfArity ``LE.le 4 then
    let some px ← walk (a.getArg! 0) (b.getArg! 2) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 3) | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst ``nat_ble) (a.getArg! 0) (a.getArg! 1) (b.getArg! 2) (b.getArg! 3) px py) (← mkEq la b))
  if a.isAppOfArity ``Nat.beq 2 && b.isAppOfArity ``Eq 3 then
    let some px ← walk (a.getArg! 0) (b.getArg! 1) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 2) | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst ``nat_beq') (a.getArg! 0) (a.getArg! 1) (b.getArg! 1) (b.getArg! 2) px py) (← mkEq la b))
  if let some p ← walkMatcher .bool a b then return some p
  if let some p ← walkIte .bool a b then return some p
  if let some p ← walkMacro .bool a b then return some p
  if let some p ← walkUnfold .bool a b then return some p
  byDefEq la b

end

/-- Proof of the interpretation `c` of the definition of a Lean function `f` asserted by Blaster
    (`∀ xs, W(f xs) = b`, see `World`): the unfolding equation of `f` (`f.eq_def`), then the traversal of its
    right-hand side and `b` (e.g., the `ite` encoding of the `match` defining `f`). -/
def proveDefinition? (cfg : Cfg) (c : Expr) : Term.TermElabM (Option Expr) :=
  forallTelescope c fun xs body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let (w, app) :=
      if lhs.isAppOfArity ``Nat.cast 3 then (World.nat, lhs.appArg!)
      else if lhs.isAppOfArity ``Eq 3 && (lhs.getArg! 2).isConstOf ``Bool.true then (World.bool, lhs.getArg! 1)
      else (World.same, lhs)
    if w.lift app != lhs then return none
    let .const f _ := app.getAppFn | return none
    let some (unfolded, eqn) ← unfoldEqn? app | dbg m!"bridge: no unfolding equation for {f}"; return none
    -- NOTE: the hypotheses of the definition (e.g., `0 ≤ x` for the `Int` variables of `Nat` arguments) are facts
    let facts ← xs.filterM fun x => do isProp (← inferType x)
    let (r, st) ← (walk unfolded rhs |>.run { cfg with facts := cfg.facts ++ facts }).run {}
    let some p := r | do
      for (a, b) in st.failures.extract (st.failures.size - 4) st.failures.size do dbg m!"bridge: definition of {f} not proved: {← ppExpr a}\n  ≠ {← ppExpr b}"
      return none
    mkLambdaFVars xs (← mkExpectedTypeHint (← mkEqTrans (← w.liftEq eqn) p) body)

/-- Proof of `a = b` (resp. `a → b` when `imp`) for a goal term `a` and the interpretation `b` of its
    translation, with the failed pairs of subterms (deepest first) when it fails. -/
def prove (cfg : Cfg) (a b : Expr) : Term.TermElabM (Option Expr × Array (Expr × Expr)) := do
  let t0 ← IO.monoMsNow
  let (r, s) ← (walk a b |>.run cfg).run {}
  dbg m!"bridge: {(← IO.monoMsNow) - t0} ms ({r.isSome})"
  return (r, s.failures)

end Blaster.Reconstruct.SmtProof.Bridge
