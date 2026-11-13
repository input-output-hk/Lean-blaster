import Lean
import Blaster.Reconstruct.Support
import Blaster.Reconstruct.SmtProof.Z3
import Blaster.Reconstruct.SmtProof.Replay

/-!
# Recursive functions (Z3)

Blaster translates a recursive function `f` to a declaration `(declare-fun F (S⃗) T)`, the macro
`(define-fun F_LRec ((x S)⃗) T body[F])` and the axiom `(assert (forall ((x S)⃗) (= (F x⃗) (F_LRec x⃗))))`,
which Z3's `recfun-finder` simplifier turns into a recursive function definition. The simplifier does nothing
when proofs are produced: Z3 then reasons on the axioms by quantifier instantiation, which may not terminate
in practice (e.g., on the CEK evaluation of validators). This module (backend `z3rec`, see `proveBySmtProof`):
 1. rewrites such queries at the SMT-LIB level, as `recfun-finder` does (`rewriteQuery`): the functions are
    defined by a `define-funs-rec` block;
 2. extends the interpretation (`addProofDefs`) with the auxiliary functions defined in the header of Z3's
    proofs (`fold-rec-n`, which name subterms of the bodies, interpreted as auxiliary definitions), and with the
    case predicates `((_ case-def k f) a⃗)` of the recursive functions (see `interpCaseDef`);
 3. replays the lemmas of Z3's theory of recursive functions (`th-lemma recfun`) with exact proofs
    (`proveLemma`): unfoldings `¬ g₁ ∨ ... ∨ ¬ gₙ ∨ f a⃗ = r` of a function in the case of the guards `gᵢ` are
    proved by instantiating the definitional equation `∀ x⃗, f x⃗ = body` (proved once by case analysis, see
    `blaster_rec_eqn`, in the normal forms of Z3's rewriter) and reducing the conditionals of the body with the
    guards (`rewriteChain`); lemmas on case predicates are propositional.
-/

open Lean Meta Elab Term Tactic

namespace Blaster.Reconstruct.SmtProof.RecFun

/-! ## Query transformation -/

/-- Head symbol and arguments of a command or an application `(h args)`. -/
def headArgs? (e : SExpr) : Option (String × Array SExpr) :=
  match e with
  | SExpr.list xs => match xs[0]? with
    | some (SExpr.atom h) => some (h, xs.extract 1 xs.size)
    | _ => none
  | _ => none

/-- A function definition of the query. -/
structure Defn where
  params : Array (String × SExpr)
  sort : SExpr
  body : SExpr
  isRec : Bool
  deriving Inhabited

/-- A recursive function `fn` of the query, defined by the axiom `∀ x⃗, fn x⃗ = defn x⃗` (either orientation). -/
structure Pair where
  fn : String
  defn : String
  /-- index of the axiom in the query -/
  assertIdx : Nat
  /-- the formula of the axiom -/
  formula : SExpr
  /-- a type predicate of a recursive datatype (`@isT` defined by the recursive definition `@isT_LRec`) -/
  isPred : Bool := false
  deriving Inhabited

structure InlineCtx where
  /-- functions renamed in bodies (the definitions `F_LRec` of the recursive functions `F`) -/
  ren : Std.HashMap String String
  /-- macros (`define-fun`), inlined in bodies -/
  macros : Std.HashMap String Defn

/-- Inlining of macros, with the bodies of the macros memoized. -/
abbrev InlineM := ReaderT InlineCtx (StateT (Std.HashMap String SExpr) (Except String))

mutual
/-- Inline the macros of `e` (as `let` bindings of their parameters) and rename the functions of `ren`; `bound`
    are the variables in scope. -/
partial def inline (bound : Std.HashSet String) (e : SExpr) : InlineM SExpr := do
  let ctx ← read
  match e with
  | SExpr.atom a =>
      if bound.contains a then return e
      if let some f := ctx.ren.get? a then return SExpr.atom f
      if let some d := ctx.macros.get? a then
        if d.params.isEmpty then return ← macroBody a d
      return e
  | SExpr.str _ => return e
  | SExpr.list xs =>
      match xs[0]? with
      | some (SExpr.atom "let") =>
          let some binds := xs[1]? >>= SExpr.list? | throw s!"ill-formed let: {e}"
          let mut binds' := #[]
          let mut bound' := bound
          for b in binds do
            let some #[SExpr.atom x, t] := b.list? | throw s!"ill-formed binding: {b}"
            -- NOTE: `let` is parallel (bound terms are in the outer scope)
            binds' := binds'.push (SExpr.list #[SExpr.atom x, ← inline bound t])
            bound' := bound'.insert x
          return SExpr.list #[SExpr.atom "let", SExpr.list binds', ← inline bound' xs[2]!]
      | some (SExpr.atom "forall") | some (SExpr.atom "exists") | some (SExpr.atom "lambda") =>
          let some vs := xs[1]? >>= SExpr.list? | throw s!"ill-formed binder: {e}"
          let bound' := vs.foldl (fun acc v => match v with | SExpr.list #[SExpr.atom x, _] => acc.insert x | _ => acc) bound
          return SExpr.list #[xs[0]!, xs[1]!, ← inline bound' xs[2]!]
      | some (SExpr.atom "!") => return SExpr.list (#[xs[0]!, ← inline bound xs[1]!] ++ xs.extract 2 xs.size)
      | some (SExpr.atom "match") => throw "match is not supported"
      | some (SExpr.atom "as") | some (SExpr.atom "_") => return e
      | some (SExpr.atom h) =>
          let args ← (xs.extract 1 xs.size).mapM (inline bound)
          if !bound.contains h then
            if let some f := ctx.ren.get? h then return SExpr.list (#[SExpr.atom f] ++ args)
            if let some d := ctx.macros.get? h then
              if d.params.size != args.size then throw s!"wrong number of arguments for {h}"
              let body ← macroBody h d
              return SExpr.list #[SExpr.atom "let", SExpr.list ((d.params.zip args).map fun ((x, _), a) => SExpr.list #[SExpr.atom x, a]), body]
          return SExpr.list (#[SExpr.atom h] ++ args)
      | some hd => return SExpr.list (#[hd] ++ (← (xs.extract 1 xs.size).mapM (inline bound)))
      | none => return e

/-- Body of macro `n` with its macros inlined (memoized). -/
partial def macroBody (n : String) (d : Defn) : InlineM SExpr := do
  if let some b := (← get).get? n then return b
  let b ← inline (d.params.foldl (fun acc (x, _) => acc.insert x) {}) d.body
  modify (·.insert n b)
  return b
end

/-- Symbols of `e`. -/
partial def symbols (e : SExpr) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  match e with
  | SExpr.atom a => acc.insert a
  | SExpr.list xs => xs.foldl (fun acc x => symbols x acc) acc
  | _ => acc

/-- Maximal size (in characters) of the `define-funs-rec` block of the rewritten query. -/
def maxBlockSize : Nat := 16000000

/-- Rewrite Blaster's query `cmds` such that its recursive functions (see `Pair`) are defined by a
    `define-funs-rec` block, as Z3's `recfun-finder` simplifier does: each function `F` is defined by the body of
    its definition `F_LRec` (with `F_LRec` renamed to `F` and the macros inlined), and its declaration and axiom
    are removed. The recursive definitions (`define-fun-rec`) used by the bodies are moved to the block. The
    axioms of the type predicates of recursive datatypes (`@is…` functions, interpreted as `True` by the replay)
    are dropped, which only weakens the query. The other commands are kept in order, after the declarations
    and the block. Returns the rewritten query and the recursive functions. Functions with parameters of sort
    `Nat` are not rewritten (their axioms are guarded by `0 ≤ x`, see `guardNatQuantifiers`). -/
def rewriteQuery (cmds : Array SExpr) : Except String (Array SExpr × Array Pair) := do
  let mut declared : Std.HashMap String Nat := {}
  let mut defs : Std.HashMap String Defn := {}
  for c in cmds do
    match headArgs? c with
    | some ("declare-fun", #[SExpr.atom f, SExpr.list sorts, _]) => declared := declared.insert f sorts.size
    | some ("define-fun", #[SExpr.atom f, ps, s, b]) =>
        defs := defs.insert f { params := ← Z3.sortedVars ps, sort := s, body := b, isRec := false }
    | some ("define-fun-rec", #[SExpr.atom f, ps, s, b]) =>
        defs := defs.insert f { params := ← Z3.sortedVars ps, sort := s, body := b, isRec := true }
    | _ => pure ()
  -- axioms `∀ x⃗, F x⃗ = G x⃗`
  let mut found : Array Pair := #[]
  let mut paired : Std.HashSet String := {}
  for h : i in [:cmds.size] do
    let some ("assert", #[φ]) := headArgs? cmds[i] | continue
    let some ("forall", #[SExpr.list vs, body]) := headArgs? φ | continue
    let vars := vs.filterMap fun v => match v with
      | SExpr.list #[SExpr.atom x, s] => if s == SExpr.atom "Nat" then none else some (SExpr.atom x)
      | _ => none
    if vars.size != vs.size then continue
    let body := match headArgs? body with
      | some ("!", as) => as[0]?.getD body
      | _ => body
    let some ("=", #[l, r]) := headArgs? body | continue
    for (fa, ga) in [(l, r), (r, l)] do
      let some (f, fargs) := headArgs? fa | continue
      let some (g, gargs) := headArgs? ga | continue
      if fargs != vars || gargs != vars || paired.contains f then continue
      let some n := declared.get? f | continue
      let some d := defs.get? g | continue
      if n != vars.size || d.params.size != vars.size then continue
      found := found.push { fn := f, defn := g, assertIdx := i, formula := φ, isPred := d.isRec && f.startsWith "@is" }
      paired := paired.insert f
      break
  let dropped : Std.HashSet Nat := found.foldl (fun s p => s.insert p.assertIdx) {}
  let pairs := found.filter (!·.isPred)
  if pairs.isEmpty then throw "no recursive function"
  let fns : Std.HashSet String := pairs.foldl (fun s p => s.insert p.fn) {}
  let ictx : InlineCtx := {
    ren := pairs.foldl (fun m p => m.insert p.defn p.fn) {}
    macros := defs.filter fun _ d => !d.isRec }
  -- bodies of the block: the recursive functions, and the recursive definitions they use
  let block : InlineM (Array (String × Defn × SExpr)) := do
    let mut out := #[]
    let mut seen : Std.HashSet String := {}
    let mut todo : Array (String × Defn) := pairs.reverse.filterMap fun p => (defs.get? p.defn).map (p.fn, ·)
    while !todo.isEmpty do
      let (f, d) := todo.back!
      todo := todo.pop
      if seen.contains f then continue
      seen := seen.insert f
      let b ← inline (d.params.foldl (fun acc (x, _) => acc.insert x) {}) d.body
      out := out.push (f, d, b)
      for s in symbols b do
        if let some d' := defs.get? s then
          if d'.isRec && !seen.contains s && !ictx.ren.contains s then todo := todo.push (s, d')
    return out
  let (block, _) ← (block.run ictx).run {}
  let moved : Std.HashSet String := block.foldl (fun s (f, _) => if fns.contains f then s else s.insert f) {}
  let blockCmd := SExpr.list #[SExpr.atom "define-funs-rec",
    SExpr.list (block.map fun (f, d, _) =>
      SExpr.list #[SExpr.atom f, SExpr.list (d.params.map fun (x, s) => SExpr.list #[SExpr.atom x, s]), d.sort]),
    SExpr.list (block.map (·.2.2))]
  if (toString blockCmd).length > maxBlockSize then throw "definitions too large"
  let mut opts := #[]
  let mut sorts := #[]
  let mut decls := #[]
  let mut rest := #[]
  for h : i in [:cmds.size] do
    let c := cmds[i]
    let some (hd, args) := headArgs? c | rest := rest.push c; continue
    let name := (args[0]?.bind SExpr.atom?).getD ""
    if ["set-option", "set-simplifier", "set-logic", "set-info"].contains hd then opts := opts.push c
    else if ["declare-datatype", "declare-datatypes", "declare-sort", "define-sort"].contains hd then sorts := sorts.push c
    else if hd == "declare-fun" || hd == "declare-const" then
      if !fns.contains name then decls := decls.push c
    else if dropped.contains i || ["check-sat", "get-proof", "get-model", "exit"].contains hd then continue
    else if hd == "define-fun-rec" && moved.contains name then continue
    else rest := rest.push c
  return (opts ++ sorts ++ decls ++ #[blockCmd] ++ rest, pairs)

/-! ## Normal forms -/

theorem smt_int_lt (a b : Int) : (a < b) = ¬ (b ≤ a) := propext Int.not_le.symm

theorem smt_str_empty_lt (s : String) : ("" < s) = ¬ ("" = s) := by
  apply propext
  rw [String.lt_iff]
  cases s with
  | mk l =>
    cases l with
    | nil => simp
    | cons c cs =>
      constructor
      · intro _ h
        have := congrArg String.data h
        simp at this
      · intro _; exact List.Lex.nil

/-- The normal forms of Z3's rewriter in the cases of recursive functions: `a < b` as `¬ b ≤ a` (integers), `"" < s`
    as `¬ "" = s` (see `smt_int_lt`, `smt_str_empty_lt`). -/
def z3Normalize (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if t.isAppOfArity ``LT.lt 4 then
      let (ty, a, b) := (t.getArg! 0, t.getArg! 2, t.getArg! 3)
      if ty.isConstOf ``Int then return .done (mkNot (mkIntLe b a))
      -- NOTE: through the projections of constructor applications (e.g., `(ByteString.mk "").data`)
      if ty.isConstOf ``String && (← whnfCore a) == mkStrLit "" then
        return .done (mkNot (mkApp3 (mkConst ``Eq [1]) ty (mkStrLit "") b))
    return .done t)

/-! ## Interpretation -/

/-- Auxiliary definitions interpreting Z3's `fold-rec-n` functions (see `addProofDefs`), expanded by
    `blaster_rec_eqn`. -/
initialize auxDefs : IO.Ref NameSet ← IO.mkRef {}

/-- Function symbols applied in `t`. -/
partial def appliedSymbols (t : STerm) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  match t with
  | .sym f => acc.insert f
  | .app f args | .iapp f _ args | .qual f _ args => args.foldl (fun acc a => appliedSymbols a acc) (acc.insert f)
  | .quant _ _ b | .annot b _ => appliedSymbols b acc
  | _ => acc

/-- Extend the interpretation with the functions defined in the proof output that are not symbols of the query
    (Z3's auxiliary functions `fold-rec-n`, which name subterms of the bodies of recursive functions), and with the
    guards of the case predicates of recursive functions given by the lemmas `(or (not ((_ case-def k f) a⃗)) g)`
    (see `interpCaseDef`). The auxiliary functions are interpreted as auxiliary Lean definitions (in dependency
    order), which keeps the interpretation of their applications small (Z3 only unfolds them in its lemmas, see
    `rewriteChain`), or as macros when their body can't be interpreted. Returns the names of the auxiliary
    definitions. -/
def addProofDefs (proof : Proof) (tbl : SymTable) : TermElabM (SymTable × NameSet) := do
  let defs : Std.HashMap String FunDef := proof.defs.foldl (fun m d => if tbl.syms.contains d.name then m else m.insert d.name d) {}
  let mut tbl := tbl
  let mut aux : NameSet := {}
  -- dependency order (depth-first, a function after the auxiliary functions it uses)
  let mut order : Array FunDef := #[]
  let mut visited : Std.HashSet String := {}
  for d in proof.defs do
    if !defs.contains d.name || visited.contains d.name then continue
    let mut stack : Array (FunDef × Bool) := #[(d, false)]
    while !stack.isEmpty do
      let (e, expanded) := stack.back!
      stack := stack.pop
      if expanded then order := order.push e; continue
      if visited.contains e.name then continue
      visited := visited.insert e.name
      stack := stack.push (e, true)
      for s in appliedSymbols e.body do
        if let some e' := defs.get? s then
          if !visited.contains s then stack := stack.push (e', false)
  for d in order do
    let r ← try
        let lam ← instantiateMVars (← (interpQuant .lambda d.params d.body).run { table := tbl })
        if lam.hasMVar || lam.hasFVar then pure none else
        -- NOTE: in the normal forms of Z3's rewriter, as in Z3's lemmas (an equivalent interpretation)
        let lam ← z3Normalize lam
        let n ← Term.mkAuxName `smtFoldRec
        let e ← mkAuxDefinition n (← inferType lam) lam (compile := false)
        pure (some e)
      catch _ => pure none
    match r with
    | some e =>
        tbl := { tbl with syms := tbl.syms.insert d.name (.expr e) }
        if let some c := e.getAppFn.constName? then
          aux := aux.insert c
          auxDefs.modify (·.insert c)
    | none => tbl := { tbl with syms := tbl.syms.insert d.name (.macro d.params d.body) }
  for s in proof.steps do
    if s.rule != "th-lemma" || s.attrs[0]? != some (SExpr.atom "recfun") || !s.premises.isEmpty then continue
    let .app "or" #[l₁, l₂] := s.concl.stripAnnot | continue
    for (l, g) in [(l₁, l₂), (l₂, l₁)] do
      let some c := l.not? | continue
      let .iapp "case-def" idx args := c.stripAnnot | continue
      let some key := caseDefKey? idx | continue
      tbl := { tbl with caseGuards := tbl.caseGuards.insert key ((tbl.caseGuards.getD key #[]).push (args, g)) }
      break
  return (tbl, aux)

/-! ## Definitional equations -/

/-- `e` in Z3's normal forms (see `z3Normalize`) with a proof of `e = e'`, for the propositional structure of `e` (the
    normal forms of the instances of definitions, e.g., `"" < s` for the argument `s := ByteString.mk ""` of
    `x.data < y`); `none` when unchanged. -/
partial def z3NormalizeProp (e : Expr) (cache : IO.Ref (Std.HashMap Expr (Option (Expr × Expr)))) :
    MetaM (Option (Expr × Expr)) := do
  if let some r := (← cache.get).get? e then return r
  let r ← core
  cache.modify (·.insert e r)
  return r
where
  core : MetaM (Option (Expr × Expr)) := do
    if e.isAppOfArity ``LT.lt 4 then
      let (ty, a, b) := (e.getArg! 0, e.getArg! 2, e.getArg! 3)
      if ty.isConstOf ``Int then return some (mkNot (mkIntLe b a), mkApp2 (mkConst ``smt_int_lt) a b)
      if ty.isConstOf ``String && (← whnfCore a) == mkStrLit "" then
        return some (mkNot (mkApp3 (mkConst ``Eq [1]) ty (mkStrLit "") b), mkApp (mkConst ``smt_str_empty_lt) b)
      return none
    -- propositional structure
    if e.isAppOfArity ``Not 1 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 ||
        (e.isAppOfArity ``Eq 3 && (e.getArg! 0).isProp) then
      let f := e.getAppFn
      let args := e.getAppArgs
      let first := if e.isAppOfArity ``Eq 3 then 1 else 0
      let mut changed := false
      let mut cur := mkAppN f (args.extract 0 first)
      let mut pf ← mkEqRefl cur
      for i in [first:args.size] do
        match ← z3NormalizeProp args[i]! cache with
        | some (a', pa) =>
            pf ← if changed then mkCongr pf pa else mkCongrArg cur pa
            cur := mkApp cur a'
            changed := true
        | none =>
            if changed then pf ← mkCongrFun pf args[i]!
            cur := mkApp cur args[i]!
            if !changed then pf ← mkEqRefl cur
      return if changed then some (cur, pf) else none
    -- conditionals with the classical instance of the interpretation
    if e.isAppOfArity ``ite 5 && (e.getArg! 2).isAppOfArity ``Classical.propDecidable 1 then
      let args := e.getAppArgs
      let c' ← z3NormalizeProp args[1]! cache
      let a' ← z3NormalizeProp args[3]! cache
      let b' ← z3NormalizeProp args[4]! cache
      if c'.isNone && a'.isNone && b'.isNone then return none
      let (c₂, pc) ← match c' with | some r => pure r | none => do pure (args[1]!, ← mkEqRefl args[1]!)
      let (a₂, pa) ← match a' with | some r => pure r | none => do pure (args[3]!, ← mkEqRefl args[3]!)
      let (b₂, pb) ← match b' with | some r => pure r | none => do pure (args[4]!, ← mkEqRefl args[4]!)
      let u := e.getAppFn.constLevels!
      let e' ← mkClassicalIte c₂ a₂ b₂
      return some (e', mkAppN (mkConst ``Local.classical_ite_congr u) #[args[0]!, args[1]!, c₂, args[3]!, a₂, args[4]!, b₂, pc, pa, pb])
    return none

/-- The application `f a⃗` of the left-hand side of a definitional equation, through the conversions of the
    interpretation (`↑(f a⃗)` for functions returning `Nat`, `f a⃗ = true` for functions returning `Bool`). -/
def lhsApp (e : Expr) : Expr :=
  let e := if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Bool && (e.getArg! 2).isConstOf ``Bool.true then
    e.getArg! 1 else e
  if e.isAppOfArity ``Nat.cast 3 then e.appArg! else e

/-- Head constant of the application of the left-hand side of a definitional equation (see `lhsApp`). -/
def lhsHead? (e : Expr) : Option Name := (lhsApp e).getAppFn.constName?

/-- The variable whose case analysis unblocks the eliminator with major premise or discriminant `d`: `d` itself,
    or the structure whose projection is `d`. Variables of type `Int` and `Nat` are not case-analyzed. -/
partial def blockingVar? (d : Expr) : MetaM (Option FVarId) := do
  match d with
  | .fvar x =>
      let t ← whnfD (← inferType d)
      let .const n _ := t.getAppFn | return none
      if n == ``Int || n == ``Nat then return none
      let some (.inductInfo info) := (← getEnv).find? n | return none
      if info.numIndices != 0 || (← isProp t) then return none
      return some x
  | .proj _ _ s => blockingVar? s
  | .mdata _ e => blockingVar? e
  | _ =>
      if let .const f _ := d.getAppFn then
        if let some info ← getProjectionFnInfo? f then
          if d.getAppNumArgs == info.numParams + 1 then return ← blockingVar? d.appArg!
      return none

/-- Variables blocking the eliminators (`casesOn`, recursors, `match`) occurring in `e`. -/
partial def blockingVars (e : Expr) : MetaM (Array FVarId) := do
  let mut acc := #[]
  let mut stack := #[e]
  let mut seen : Std.HashSet Expr := {}
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if seen.contains s then continue
    seen := seen.insert s
    if s.isApp then
      let mut majors := #[]
      if let some m ← matchMatcherApp? s (alsoCasesOn := true) then majors := m.discrs
      else if let .const r _ := s.getAppFn then
        if let some (.recInfo info) := (← getEnv).find? r then
          if let some d := s.getAppArgs[info.getMajorIdx]? then majors := #[d]
      for d in majors do
        if let some x ← blockingVar? d then
          if !acc.contains x then acc := acc.push x
    match s with
    | .app f a => stack := stack.push f |>.push a
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return acc

/-- Variables of structure types (non-recursive inductive types with one constructor) of the local context, e.g.,
    whose fields are compared to the literals of patterns (their case analysis does not split the goal). -/
def structVars : MetaM (Array FVarId) := do
  let mut acc := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfD d.type
    let .const n _ := t.getAppFn | continue
    let some (.inductInfo info) := (← getEnv).find? n | continue
    if info.ctors.length != 1 || info.isRec || info.numIndices != 0 || isClass (← getEnv) n then continue
    -- NOTE: types with builtin representations (e.g., string literals) are kept
    if [``String, ``Char, ``Fin, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``BitVec, ``Float, ``Array,
        ``ByteArray, ``Subtype].contains n then continue
    if ← isProp d.type then continue
    acc := acc.push d.fvarId
  return acc

/-- Maximal number of goals of the case analyses of `blaster_rec_eqn`. -/
def maxEqnGoals : Nat := 512

syntax (name := blasterRecEqn) "blaster_rec_eqn" : tactic

/-- Proof of the definitional equation `∀ x⃗, f x⃗ = body` of a recursive function `f`, where `body` is the
    interpretation of its SMT definition (Blaster's translation of the optimized definition of `f`): `f x⃗` is
    unfolded once (equation `f.eq_def`), the user definitions are unfolded, and the variables blocking the
    eliminators (`match`, `casesOn`) of the goal are case-analyzed, until both sides are simplified to the same
    term. -/
@[tactic blasterRecEqn] def evalBlasterRecEqn : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  -- one unfolding of the head function of the left-hand side
  let g ← getMainGoal
  let g ← g.withContext do
    let some (_, lhs, _) := (← whnfR (← instantiateMVars (← g.getType))).eq?
      | throwError "blaster_rec_eqn: equality expected"
    let app := lhsApp lhs
    let .const f _ := app.getAppFn | throwError "blaster_rec_eqn: application of a constant expected"
    let some eqn ← getUnfoldEqnFor? f (nonRec := true) | throwError "blaster_rec_eqn: no equation for {f}"
    let eqc ← mkConstWithFreshMVarLevels eqn
    let (ms, _, eqTy) ← forallMetaTelescopeReducing (← inferType eqc)
    let some (_, l, _) := eqTy.eq? | throwError "blaster_rec_eqn: ill-formed equation {eqn}"
    if !(← isDefEq l app) then throwError "blaster_rec_eqn: equation {eqn} does not apply"
    let r ← g.rewrite (← g.getType) (← instantiateMVars (mkAppN eqc ms))
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    -- the auxiliary definitions of the body (Z3's `fold-rec-n` functions) are expanded
    let aux ← auxDefs.get
    g'.withContext do g'.replaceTargetDefEq (← deltaExpand (← instantiateMVars (← g'.getType)) aux.contains)
  replaceMainGoal [g]
  -- NOTE: the Boolean equalities of lawful instances as decided equalities (the user instances are unfolded by
  -- `blaster_unfold_user`, e.g., `x == y` into a recursive `eqData x y`, while Blaster translates them as equalities)
  try evalTactic (← `(tactic| simp only [Bool.beq_eq_decide_eq])) catch _ => pure ()
  try evalTactic (← `(tactic| blaster_unfold_user)) catch _ => pure ()
  -- case analyses: the goals are reduced (`dsimp`) and split, the eliminators of the left-hand side (the Lean
  -- definition) first, those of the right-hand side (the SMT definition, whose testers may examine more constructors
  -- than the patterns of the definition) when the left-hand side is reduced
  let mut todo := ← getGoals
  let mut count := todo.length
  let mut unfolded : Std.HashSet MVarId := {}
  let mut remaining := []
  -- debugging: the case analyses (environment variable `BLASTER_RECEQN_DEBUG`)
  let trace := (← IO.getEnv "BLASTER_RECEQN_DEBUG").isSome
  while !todo.isEmpty do
    let g := todo.head!
    todo := todo.tail!
    setGoals [g]
    try evalTactic (← `(tactic| dsimp only)) catch _ => pure ()
    let some g ← (do return (← getGoals).head?) | continue
    setGoals [g]
    -- NOTE: `simp_all` closes the contradictory cases (e.g., the patterns excluded by the hypotheses of `split`);
    -- `simp` closes other goals (e.g., a third of the nodes of the equations of the CEK evaluation of a validator),
    -- `simp only []` none (while costing a quarter of the time of these attempts)
    let hasHyps ← g.withContext do (← getLCtx).anyM fun d => do return !d.isImplementationDetail && (← isProp d.type)
    try evalTactic (← if hasHyps
                       then `(tactic| first | (simp [smt_str_empty_lt]; done) | (simp_all [smt_str_empty_lt]; done))
                       else `(tactic| (simp [smt_str_empty_lt]; done)))
    catch _ => pure ()
    if (← getGoals).isEmpty then continue
    let (lhs, all) ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      let mut e := t
      for d in ← getLCtx do
        if !d.isImplementationDetail then e := mkApp e (← instantiateMVars d.type)
      return ((t.eq?.map (·.2.1)).getD t, e)
    -- blocking variables of the left-hand side, conditions of its `match` and `if`, other blocking variables
    let mut subgoals? : Option (List MVarId) := none
    let env ← getEnv
    let lhsCond := lhs.find? fun e => e.isAppOf ``ite || e.isAppOf ``dite || isMatcherCore env e.getAppFn.constName
    if let some x := (← g.withContext (blockingVars lhs))[0]? then
      if trace then debugLog m!"blaster_rec_eqn: cases on {← g.withContext (ppExpr (mkFVar x))} (left-hand side)"
      subgoals? := some ((← g.cases x).toList.map (·.mvarId))
    else if lhsCond.isSome then
      subgoals? ← observing? (do evalTactic (← `(tactic| split)); getGoals)
      -- NOTE: `split` fails when the discriminants of a `match` can't be generalized in the goal (e.g., `x :: xs`
      -- matched against string literal patterns): the discriminants of the first `match` of the left-hand side are
      -- generalized first
      if subgoals?.isNone then
        let isMatch (e : Expr) : Bool := match e.getAppFn with
          | .const m _ => isMatcherCore env m && (getMatcherInfoCore? env m).any (·.arity == e.getAppNumArgs)
          | _ => false
        if let some m := lhs.find? isMatch then
          if let some app ← g.withContext (matchMatcherApp? m) then
            let ds := app.discrs.filter (!·.isFVar)
            if !ds.isEmpty then
              subgoals? ← observing? do
                let (_, g') ← g.generalize (ds.map fun d => { expr := d, hName? := some `hd })
                setGoals [g']
                evalTactic (← `(tactic| split))
                getGoals
      if trace then debugLog m!"blaster_rec_eqn: split (left-hand side): {subgoals?.map (·.length)}"
    if subgoals?.isNone then
      let vars ← g.withContext (blockingVars all)
      let vars ← if !vars.isEmpty then pure vars else g.withContext structVars
      if let some x := vars[0]? then
        if trace then debugLog m!"blaster_rec_eqn: cases on {← g.withContext (ppExpr (mkFVar x))}"
        subgoals? := some ((← g.cases x).toList.map (·.mvarId))
    if let some gs := subgoals? then
      count := count + gs.length
      if count > maxEqnGoals then
        debugLog m!"blaster_rec_eqn: too many cases\n{← Meta.ppGoal g}"
        throwError "blaster_rec_eqn: too many cases"
      todo := gs ++ todo
      continue
    setGoals [g]
    -- NOTE: e.g., `grind` for the orientations of equalities and the orders of conjunctions of Blaster's normal forms
    try evalTactic (← `(tactic| first | (simp_all [smt_str_empty_lt]; done) | rfl | (simp_all [smt_str_empty_lt] <;> grind) | grind))
    catch _ => pure ()
    if (← getGoals).isEmpty then continue
    if !unfolded.contains g then
      -- user definitions exposed by the case analyses
      try evalTactic (← `(tactic| simp only [Bool.beq_eq_decide_eq])) catch _ => pure ()
      try evalTactic (← `(tactic| blaster_unfold_user)) catch _ => pure ()
      for g' in ← getGoals do
        unfolded := unfolded.insert g'
        todo := g' :: todo
      continue
    -- case analyses on the conditions of the right-hand side
    if trace then debugLog m!"blaster_rec_eqn: split (right-hand side)\n{← Meta.ppGoal g}"
    let some gs ← observing? (do evalTactic (← `(tactic| split)); getGoals) | remaining := remaining ++ [g]; continue
    count := count + gs.length
    if count > maxEqnGoals then throwError "blaster_rec_eqn: too many cases"
    for g' in gs do unfolded := unfolded.insert g'
    todo := gs ++ todo
  if !remaining.isEmpty then
    for g in remaining.take 2 do debugLog m!"blaster_rec_eqn: unsolved case\n{← Meta.ppGoal g}"
    throwError "blaster_rec_eqn: unsolved cases"
  setGoals []

/-- Proof of the definitional axiom `∀ x⃗, f x⃗ = body` of a recursive function `f` asserted by Blaster's query (the
    backends without `define-funs-rec`, e.g., `z3`), by `blaster_rec_eqn`. -/
def proveDefAxiom? (c : Expr) : TermElabM (Option Expr) := do
  if c.hasFVar || c.hasMVar then return none
  let some head ← forallTelescope c fun _ b => do
      let some (_, l, _) := b.eq? | return none
      return lhsHead? l
    | return none
  if !(← isRecursiveDefinition head) then return none
  let t0 ← IO.monoMsNow
  let p ← withLCtx {} {} <| proveWithTactic c (← `(tactic| blaster_rec_eqn)) (budget := 2000000)
  debugLog m!"recfun: blaster_rec_eqn {if p.isSome then "proved" else "failed"} for the axiom of {head} ({(← IO.monoMsNow) - t0} ms)"
  return p

/-! ## Lemmas -/

/-- Short form of `e` for debugging messages (large terms are not printed). -/
def brief (e : Expr) : String :=
  if Local.sizeLe e 2000 then toString e else "<large term>"

/-- The error of the kernel on the closed theorem `type` with proof `value`, if any. -/
def kernelError? (type value : Expr) : MetaM (Option MessageData) := do
  if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then return some m!"open term"
  let lvls := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let decl := Declaration.thmDecl { name := ← mkFreshUserName `_blaster_check, levelParams := lvls, type, value }
  match Lean.Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return none
  | .error ex => return some (ex.toMessageData (← getOptions))

/-- Definitional equation `∀ x⃗, f x⃗ = body` of a recursive function, proved on first use. The candidate
    statements are tried in order: the body of the function in the header of Z3's proof (on which Z3's lemmas
    are expressed), then the body of the query (Blaster's normal form). -/
structure DefEq where
  stmts : Array Expr
  /-- head constant of the left-hand side (see `lhsHead?`) -/
  head : Name
  /-- the SMT symbols of the function (see `Pair`) -/
  fns : Array String := #[]
  /-- the proved statement and its proof (`none` when not attempted yet) -/
  proof : IO.Ref (Option (Option (Expr × Expr)))
  /-- the proofs of statements by `blaster_rec_eqn` started beforehand (see `startEqTasks`) -/
  tasks : IO.Ref (Array (Expr × Task (Except Exception (Option Expr))))

structure Ctx where
  eqs : Array DefEq := #[]
  /-- auxiliary definitions (Z3's `fold-rec-n` functions), unfolded by `rewriteChain` -/
  aux : NameSet := {}
  /-- proof of a definitional equation (e.g., with the bridge tactics) -/
  proveDef : Expr → TermElabM (Option Expr) := fun _ => pure none
  /-- proof of `g₁ → ... → gₙ → l = r` for the rewritten sides `l` and `r` of an unfolding under the guards `gᵢ`
      when they differ (e.g., in the normal forms of Blaster and Z3, like `0 < x` and `¬ x ≤ 0`) -/
  proveImp : Expr → TermElabM (Option Expr) := fun _ => pure none
  /-- proof of `l = r` for terms that differ in a few places (e.g., `0 < x` and `¬ x ≤ 0`, see `Local.diffEq`) -/
  proveDiff : Expr → Expr → TermElabM (Option Expr) := fun _ _ => pure none


/-- The interpretation of the definitional equation `φ` (`∀ x⃗, f x⃗ = body`) with the head of its left-hand side. -/
def interpEqStmt (tbl : SymTable) (φ : STerm) : TermElabM (Option (Expr × Name)) := do
  try
    let stmt ← instantiateMVars (← (interpProp φ).run { table := tbl })
    if stmt.hasMVar then return none
    let some head ← forallTelescope stmt fun _ b => do
        let some (_, l, _) := b.eq? | return none
        return lhsHead? l
      | return none
    return some (stmt, head)
  catch ex =>
    debugLog m!"recfun: no definitional equation for {φ}: {ex.toMessageData}"
    return none

/-- Definitional equations of the recursive functions `pairs`: the interpretation of `∀ x⃗, f x⃗ = body` for the
    body of `f` in the definitions `defs` of the proof output, and of the axiom of `f` in the query; `tasks`: the proofs
    of definitional equations started beforehand (see `preStartEqTasks`). -/
def mkCtx (tbl : SymTable) (aux : NameSet) (pairs : Array Pair) (defs : Array FunDef)
    (proveDef proveImp : Expr → TermElabM (Option Expr)) (proveDiff : Expr → Expr → TermElabM (Option Expr))
    (tasks : Array (Expr × Task (Except Exception (Option Expr))) := #[]) :
    TermElabM Ctx := do
  if !pairs.isEmpty then debugLog m!"recfun: {pairs.size} recursive functions, {defs.size} definitions in the proof"
  let interpStmt := interpEqStmt tbl
  let mut eqs := #[]
  for p in pairs do
    let mut cands := #[]
    if let some d := defs.find? (·.name == p.fn) then
      let lhs := STerm.app p.fn (d.params.map (STerm.sym ·.1))
      cands := cands.push (STerm.quant .forall d.params (.app "=" #[lhs, d.body]))
    if let .ok φ := STerm.ofSExpr {} p.formula then cands := cands.push φ
    let mut stmts := #[]
    let mut head := Name.anonymous
    for φ in cands do
      if let some (stmt, h) ← interpStmt φ then
        if head.isAnonymous then head := h
        if h == head then stmts := stmts.push stmt
    if !stmts.isEmpty then
      let started := tasks.filter fun (stmt, _) => stmts.contains stmt
      debugLog m!"recfun: {stmts.size} statements of the equation of {head}, {started.size} started beforehand"
      eqs := eqs.push { stmts, head, fns := #[p.fn, p.defn], proof := ← IO.mkRef none, tasks := ← IO.mkRef started }
  return { eqs, aux, proveDef, proveImp, proveDiff }

/-- The proof of a closed definitional equation `stmt` by `blaster_rec_eqn`. -/
def proveEqn (stmt : Expr) : TermElabM (Option Expr) := do
  if stmt.hasFVar then return none
  withLCtx {} {} <| proveWithTactic stmt (← `(tactic| blaster_rec_eqn)) (budget := 2000000)

/-- The proof of the closed definitional equation `stmt` by `blaster_rec_eqn` in a task (see `Local.runAsync`), usable
    in the current environment (see `Local.inlineNewConstants`), interrupted when `cancelTk?` is set. -/
def proveEqnAsync (stmt : Expr) (cancelTk? : Option IO.CancelToken := none) :
    TermElabM (Task (Except Exception (Option Expr))) := do
  let base ← getEnv
  Local.runAsync (cancelTk? := cancelTk?) do
    let some p ← proveEqn stmt | return none
    return some (← Local.inlineNewConstants base (← instantiateMVars p))

/-- Start the proofs of the definitional equations of the functions `fns` (SMT symbols, e.g., the ones of the recursive
    functions unfolded by the lemmas of the proof) in parallel (see `Local.runAsync`), their case analyses taking
    seconds each (e.g., 12 s in sequence for the 8 equations of the CEK evaluation of a validator). The proofs are used
    by `DefEq.get` when they are closed and only use constants of its environment. -/
def startEqTasks (ctx : Ctx) (fns : Std.HashSet String) (cancelTk? : Option IO.CancelToken := none) :
    TermElabM Unit := do
  for eq in ctx.eqs do
    if !eq.fns.any fns.contains then continue
    let some stmt := eq.stmts[0]? | continue
    if stmt.hasFVar || stmt.hasMVar then continue
    if (← eq.tasks.get).any (·.1 == stmt) then continue
    eq.tasks.modify (·.push (stmt, ← proveEqnAsync stmt cancelTk?))

/-- Start the proofs of the definitional equations of the recursive functions `pairs` from their axioms in the query
    (see `startEqTasks`), i.e., before the proof of the backend is available (e.g., during the 6 s of the search of Z3
    for a proof of the CEK evaluation of a validator): the started proofs, given to `mkCtx`. -/
def preStartEqTasks (tbl : SymTable) (pairs : Array Pair) (cancelTk? : Option IO.CancelToken := none) :
    TermElabM (Array (Expr × Task (Except Exception (Option Expr)))) := do
  let mut r := #[]
  for p in pairs do
    let .ok φ := STerm.ofSExpr {} p.formula | continue
    let some (stmt, _) ← interpEqStmt tbl φ | continue
    if stmt.hasFVar || stmt.hasMVar || r.any (·.1 == stmt) then continue
    r := r.push (stmt, ← proveEqnAsync stmt cancelTk?)
  return r

/-- Proof of the definitional equation `eq` (attempted once; the proof is shared by the lemmas using it). -/
def DefEq.get (eq : DefEq) (ctx : Ctx) : TermElabM (Option (Expr × Expr)) := do
  if let some r ← eq.proof.get then return r
  let mut r := none
  let tasks ← eq.tasks.get
  for stmt in eq.stmts do
    let prove : TermElabM (Option Expr) := do
      let t0 ← IO.monoMsNow
      -- the proof started beforehand (see `startEqTasks`), unless it uses declarations of its own environment (e.g.,
      -- equations realized on its branch only, `skipRealize`)
      let p ← match tasks.find? (·.1 == stmt) with
        | some (_, t) => match ← traceSlow s!"wait for the equation of {eq.head}" (IO.wait t) with
          | .ok (some p) =>
              traceSlow "realization of the reserved names of the equation" (Local.realizeReservedNames p)
              let env ← getEnv
              let usable (p : Expr) : Bool := !p.hasMVar && !p.hasFVar &&
                (p.find? fun e => e.isConst && !env.contains e.constName! (skipRealize := true)).isNone
              if usable p then pure (some p) else
                let missing := (p.getUsedConstants.filter (!env.contains · (skipRealize := true))).toList.take 5
                debugLog m!"recfun: the proof of the equation of {eq.head} started beforehand uses {missing}"
                traceSlow "blaster_rec_eqn" (proveEqn stmt)
          -- NOTE: the same tactic failed in the task, with the same budget (only an exception of the task is retried)
          | .ok none => pure none
          | .error _ => traceSlow "blaster_rec_eqn" (proveEqn stmt)
        | none => traceSlow "blaster_rec_eqn" (proveEqn stmt)
      debugLog m!"recfun: blaster_rec_eqn {if p.isSome then "proved" else "failed"} for {eq.head} ({(← IO.monoMsNow) - t0} ms)"
      if p.isSome then return p
      debugLog m!"recfun: bridge tactics on the definitional equation of {eq.head}"
      let r ← ctx.proveDef stmt
      debugLog m!"recfun: bridge tactics {if r.isSome then "proved" else "failed"} for {eq.head}"
      return r
    if let some p ← (try prove catch _ => pure none) then
      -- Z3's normal forms (as in Z3's lemmas)
      let stmt' ← traceSlow "z3 normal form of the equation" (z3Normalize stmt)
      let (stmt, p) ← if stmt' == stmt then pure (stmt, p) else do
        let imp ← withLCtx {} {} <| proveWithTactic (mkForall `h .default stmt stmt')
          (← `(tactic| (intro h; simp only [smt_int_lt, smt_str_empty_lt] at h ⊢; exact h)))
        match imp with
        | some q => pure (stmt', mkApp q p)
        | none => debugLog m!"recfun: no normal form for {eq.head}"; pure (stmt, p)
      -- NOTE: an auxiliary theorem, such that the instances of the equation (see `instantiateEq`) do not copy its
      -- proof (the instantiation of a metavariable assigned to the proof would beta-reduce its applications)
      let p ← instantiateMVars p
      -- the proof is checked by the kernel first: an ill-typed equation fails cleanly (the theorem would only be
      -- checked asynchronously, see `Elab.async`)
      if let some msg ← traceSlow "kernel check of the equation" (kernelError? stmt p) then
        debugLog m!"recfun: definitional equation of {eq.head} rejected by the kernel: {msg}"
        continue
      -- NOTE: added without checking it again, nor computing its closure (it is closed, see `kernelError?`), nor
      -- traversing it for `sorryAx` (the whole proof is, see `dependsOnSorry`)
      let lvls := (collectLevelParams (collectLevelParams {} stmt) p).params.toList
      let some c ← traceSlow "auxiliary theorem of the equation" (try
            let n ← withOptions (fun o => warn.sorry.set (debug.skipKernelTC.set o true) false) <|
              mkAuxLemma lvls stmt p (cache := false)
            pure (some (Lean.mkConst n (lvls.map mkLevelParam)))
          catch _ => pure none)
        | continue
      r := some (stmt, c)
      break
    debugLog m!"recfun: definitional equation not proved: {brief stmt}"
  eq.proof.set (some r)
  return r

/-- Instance of the equation `pf : stmt` (`∀ x⃗, l = r`) whose left-hand side is `t`: `r[a⃗]` and the proof of `t = r[a⃗]`. -/
def instantiateEq (stmt pf t : Expr) : MetaM (Option (Expr × Expr)) := do
  let (ms, _, body) ← forallMetaTelescopeReducing stmt
  let some (_, l, r) := body.eq? | return none
  if !(← withReducible (isDefEq l t)) then return none
  let r ← instantiateMVars r
  -- NOTE: the proof of the equation (an assigned metavariable) is not instantiated
  let as ← ms.mapM instantiateMVars
  if r.hasExprMVar || as.any (·.hasExprMVar) then return none
  return some (r, mkAppN pf as)

/-- Facts (propositions with their proofs), with the consequences of conjunctions, negated disjunctions and
    double negations. -/
partial def addFact (facts : Std.HashMap Expr Expr) (t p : Expr) : MetaM (Std.HashMap Expr Expr) := do
  if facts.contains t then return facts
  let facts := facts.insert t p
  if let some (a, b) := t.and? then
    return ← addFact (← addFact facts a (mkApp3 (mkConst ``And.left) a b p)) b (mkApp3 (mkConst ``And.right) a b p)
  if let some na := t.not? then
    if let some a := na.not? then
      return ← addFact facts a (mkApp2 (mkConst ``Classical.byContradiction) a p)
    if let some (a, b) := na.app2? ``Or then
      let pa ← withLam `h a fun h => return mkApp p (mkApp3 (mkConst ``Or.inl) a b h)
      let pb ← withLam `h b fun h => return mkApp p (mkApp3 (mkConst ``Or.inr) a b h)
      return ← addFact (← addFact facts (mkNot a) pa) (mkNot b) pb
  return facts

/-- Rewrite steps on `t`: unfolding of the recursive functions with their definitional equations, and reduction of
    the conditionals whose condition is decided by the facts. Returns the terms `t = t₀, t₁, ...` with the proofs
    of `t = tᵢ`. -/
partial def rewriteChain (ctx : Ctx) (facts : Std.HashMap Expr Expr) (t : Expr) (fuel := 64) : TermElabM (Array (Expr × Expr)) := do
  let mut cur := t
  let mut pf ← mkEqRefl t
  let mut out := #[(t, pf)]
  for _ in [0:fuel] do
    let some (next, p) ← step cur | break
    pf ← mkEqTrans pf p
    cur := next
    out := out.push (cur, pf)
  return out
where
  /-- The truth value of `c` given by the facts (with a proof of `c` or `¬ c`), also through the normal forms of
      Z3 (`a < b` as `¬ b ≤ a`, equalities up to symmetry). -/
  decide? (c : Expr) (normalized := false) : MetaM (Option (Bool × Expr)) := do
    if let some p := facts.get? c then return some (true, p)
    if let some p := facts.get? (mkNot c) then return some (false, p)
    if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Int then
      let (a, b) := (c.getArg! 2, c.getArg! 3)
      if let some p := facts.get? (mkNot (mkIntLe b a)) then return some (true, ← mkAppM ``Int.lt_of_not_ge #[p])
      if let some p := facts.get? (mkIntLe b a) then return some (false, ← mkAppM ``Int.not_lt_of_ge #[p])
    if let some (_, a, b) := c.eq? then
      let c' ← mkEq b a
      if let some p := facts.get? c' then return some (true, ← mkEqSymm p)
      if let some p := facts.get? (mkNot c') then
        return some (false, ← withLam `h c fun h => do return mkApp p (← mkEqSymm h))
    -- conjunctions of facts and of trivial conditions (e.g., the testers of single-constructor types, which Z3
    -- removes from the guards), by unit propagation
    if c.isAppOfArity ``And 2 then
      let mut hyps := facts.toArray
      for a in Local.opLeaves ``And c do
        if !facts.contains a then
          if ← defeqBudget a (mkConst ``True) 2000 true then hyps := hyps.push (a, ← mkExpectedTypeHint (mkConst ``True.intro) a)
      if let some p ← PropEngine.prove hyps c (splits := 0) then return some (true, p)
      if let some p ← PropEngine.prove hyps (mkNot c) (splits := 0) then return some (false, p)
    -- Z3's normal forms in the instances of the definitions (e.g., `"" < s` as `¬ "" = s`)
    if !normalized then
      if let some (c', pc) ← z3NormalizeProp c (← IO.mkRef {}) then
        match ← decide? c' (normalized := true) with
        | some (true, p) => return some (true, ← mkEqMPR pc p)
        | some (false, p) => return some (false, ← withLam `h c fun h => do return mkApp p (← mkEqMP pc h))
        | none => pure ()
    return none
  step (t : Expr) : TermElabM (Option (Expr × Expr)) := do
    if t.isAppOfArity ``ite 5 then
      let args := t.getAppArgs
      let (α, c, inst, a, b) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
      let us := t.getAppFn.constLevels!
      match ← decide? c with
      | some (true, hc) => return some (a, mkAppN (mkConst ``if_pos us) #[c, inst, hc, α, a, b])
      | some (false, hn) => return some (b, mkAppN (mkConst ``if_neg us) #[c, inst, hn, α, a, b])
      | none => return none
    -- auxiliary definitions: delta
    if let .const c _ := t.getAppFn then
      if ctx.aux.contains c then
        if let some t' ← unfoldDefinition? t then
          return some (t', ← mkExpectedTypeHint (← mkEqRefl t) (← mkEq t t'))
    let some h := lhsHead? t | return none
    for eq in ctx.eqs do
      if eq.head != h then continue
      let some (stmt, pf) ← traceSlow s!"definitional equation of {eq.head}" (eq.get ctx) | continue
      if let some r ← instantiateEq stmt pf t then return some r
    return none

/-- Proof of `goal` from the hypotheses `hyps` (propositions and proofs) with `ctx.proveImp`. -/
def proveUnder (ctx : Ctx) (hyps : Array (Expr × Expr)) (goal : Expr) : TermElabM (Option Expr) := do
  let stmt := hyps.foldr (fun (t, _) acc => mkForall `h .default t acc) goal
  return (← ctx.proveImp stmt).map (mkAppN · (hyps.map (·.2)))

/-- Proof of the literal `l` from the facts: the sides of an equality are rewritten to a common term (see
    `rewriteChain`), a proposition to `True`, a negated proposition to `False`. When the rewritten terms differ,
    their equality is proved under the guards `hyps`. -/
def proveLit (ctx : Ctx) (facts : Std.HashMap Expr Expr) (hyps : Array (Expr × Expr)) (l : Expr) :
    TermElabM (Option Expr) := do
  if let some (_, a, b) := l.eq? then
    let ca ← traceSlow "rewrite chain (left)" (rewriteChain ctx facts a)
    let cb ← traceSlow "rewrite chain (right)" (rewriteChain ctx facts b)
    if ca.size == 1 && cb.size == 1 then return none
    for (x, px) in ca do
      for (y, py) in cb do
        if x == y then return some (← mkEqTrans px (← mkEqSymm py))
    for (x, px) in ca do
      for (y, py) in cb do
        if x.getAppFn == y.getAppFn && (← propEq x y) then return some (← mkEqTrans px (← mkEqSymm py))
    -- differences of the rewritten sides
    let (x, px) := ca.back!
    let (y, py) := cb.back!
    -- Z3's normal forms in the instances of the definitions
    let (x, px) ← match ← traceSlow "z3 normal form" (z3NormalizeProp x (← IO.mkRef {})) with
      | some (x', p) => pure (x', ← mkEqTrans px p)
      | none => pure (x, px)
    if x == y then return some (← mkEqTrans px (← mkEqSymm py))
    if let some p ← traceSlow "difference" (ctx.proveDiff x y) then
      return some (← mkEqTrans (← mkEqTrans px p) (← mkEqSymm py))
    if let some p ← traceSlow "under guards" (proveUnder ctx hyps (← mkEq x y)) then
      return some (← mkEqTrans (← mkEqTrans px p) (← mkEqSymm py))
    if (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
      debugLog m!"recfun: no common rewrite ({ca.size}, {cb.size} rewrites) of\n{← dagString x 6000}\nand\n{← dagString y 6000}"
    return none
  if let some q := l.not? then
    let cq ← rewriteChain ctx facts q
    if cq.size == 1 then return none
    let pq ← match cq.find? (·.1.isConstOf ``False) with
      | some (_, pq) => pure pq
      | none =>
          let (x, px) := cq.back!
          let some p ← proveUnder ctx hyps (← mkEq x (mkConst ``False)) | return none
          mkEqTrans px p
    return some (← withLam `h q fun h => mkEqMP pq h)
  let cl ← rewriteChain ctx facts l
  if cl.size == 1 then return none
  let pl ← match cl.find? (·.1.isConstOf ``True) with
    | some (_, pl) => pure pl
    | none =>
        let (x, px) := cl.back!
        let some p ← proveUnder ctx hyps (← mkEq x (mkConst ``True)) | return none
        mkEqTrans px p
  return some (← mkEqMPR pl (mkConst ``True.intro))

/-- Proof of the clause `concl` (literals `lits`) from a proof of its `j`-th literal assuming the others false. -/
def proveByLit (ctx : Ctx) (lits : Array Expr) (concl : Expr) (j : Nat) : TermElabM (Option Expr) := do
  let r ← withLocalDeclD `hn (mkNot concl) fun hn => do
    let mut facts : Std.HashMap Expr Expr := {}
    let mut hyps := #[]
    let sfx := orSuffixes lits
    for i in [:lits.size] do
      if i == j then continue
      let l := lits[i]!
      let nl ← withLam `h l fun h => return mkApp hn (mkOrInjWith lits sfx i h)
      facts ← addFact facts (mkNot l) nl
      hyps := hyps.push (mkNot l, nl)
    let some p ← proveLit ctx facts hyps lits[j]! | return none
    return some (mkLambda `hn .default (mkNot concl) ((mkApp hn (mkOrInjWith lits sfx j p)).abstract #[hn]))
  return r.map (mkApp2 (mkConst ``Classical.byContradiction) concl ·)

/-- Proof of `goal` by case splits on `atoms` (in order), each case by unit propagation (see `PropEngine`), e.g.,
    the disjunction of the case predicates of a function (the conjunctions of the guards of its cases). -/
partial def splitProve (hyps : Array (Expr × Expr)) (goal : Expr) (atoms : List Expr) (budget : IO.Ref Nat) :
    MetaM (Option Expr) := do
  if let some p ← PropEngine.prove hyps goal (splits := 0) then return some p
  let n ← budget.get
  if n == 0 then return none
  budget.set (n - 1)
  match atoms with
  | [] => return none
  | c :: rest =>
      let some pos ← withLocalDeclD `hc c fun hc => do
          return (← splitProve (hyps.push (c, hc)) goal rest budget).map fun p => mkLambda `hc .default c (p.abstract #[hc])
        | return none
      let some neg ← withLocalDeclD `hc (mkNot c) fun hc => do
          return (← splitProve (hyps.push (mkNot c, hc)) goal rest budget).map fun p =>
            mkLambda `hc .default (mkNot c) (p.abstract #[hc])
        | return none
      return some (mkApp6 (mkConst ``Or.elim) c (mkNot c) goal (mkApp (mkConst ``Classical.em) c) pos neg)

/-- Atoms of the conjunctions of the literals `lits` (e.g., the guards of case predicates), by decreasing number of
    literals containing them. -/
def guardAtoms (lits : Array Expr) : Array Expr := Id.run do
  let rec conjuncts (e : Expr) (fuel : Nat) : List Expr :=
    match fuel, e.and? with
    | fuel + 1, some (a, b) => a :: conjuncts b fuel
    | _, _ => [e]
  let mut counts : Array (Expr × Nat) := #[]
  for l in lits do
    for g in conjuncts l 64 do
      let a := g.not?.getD g
      match counts.findIdx? (·.1 == a) with
      | some i => counts := counts.modify i fun (a, n) => (a, n + 1)
      | none => counts := counts.push (a, 1)
  return (counts.zipIdx.qsort fun ((_, n₁), i₁) ((_, n₂), i₂) => n₁ > n₂ || (n₁ == n₂ && i₁ < i₂)).map (·.1.1)

/-- Proof of a lemma of Z3's theory of recursive functions (`th-lemma recfun`), given the interpretation of its
    clause `concl` with `n` literals:
     - propositional lemmas on case predicates (e.g., `¬ case(a⃗) ∨ g`, `case(a⃗) ∨ ¬ g₁ ∨ ... ∨ ¬ gₙ`), by unit
       propagation;
     - unfoldings `¬ g₁ ∨ ... ∨ ¬ gₙ ∨ f a⃗ = r` (also of the auxiliary functions `fold-rec-n`, whose
       interpretation is their body), by rewriting (see `proveLit`);
     - disjunctions of the case predicates of a function at `a⃗`, by case splits on the guards. -/
def proveLemma (ctx : Ctx) (concl : Expr) (n : Nat) : TermElabM (Option Expr) := do
  if let some p ← PropEngine.prove #[] concl (splits := 0) then return some p
  let lits := disjuncts concl n
  if lits.size ≥ 1 then
    for j in (List.range lits.size).reverse do
      if let some p ← traceSlow s!"recfun literal {j}/{lits.size}" (proveByLit ctx lits concl j) then return some p
  -- disjunctions of case predicates (no equality between data)
  let isDataEq (l : Expr) : TermElabM Bool := do
    let some (ty, _, _) := l.eq? | return false
    return !ty.isProp
  if lits.size ≥ 2 && !(← lits.anyM isDataEq) then
    let atoms := guardAtoms lits
    if atoms.size ≤ 16 then
      return ← traceSlow "recfun case splits" (splitProve #[] concl atoms.toList (← IO.mkRef 512))
  return none

end Blaster.Reconstruct.SmtProof.RecFun
