import Lean
import Blaster.Optimize.Decidable
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.Support
import Blaster.Reconstruct.SmtProof.Poly
import Blaster.Reconstruct.SmtProof.Local
import Blaster.Reconstruct.SmtProof.BridgeLemmas

/-!
# Worlds and matchers of the bridge

The relations between the goal terms and the interpretation of their translation (`World`, see `Bridge.lean`), and
the auxiliary theorems relating the `match` expressions to their `ite` encoding (`proveMatchIte`), stated for abstract
discriminants and alternatives and proved once per matcher instance.
-/

open Lean Meta Elab

namespace Blaster.Reconstruct.SmtProof.Bridge

/-- Debugging output (environment variable `BLASTER_BRIDGE_DEBUG`). -/
def dbg (msg : MessageData) : MetaM Unit := do
  match ← IO.getEnv "BLASTER_BRIDGE_DEBUG" with
  | none => pure ()
  | some "1" => IO.eprintln (← msg.toString)
  | some f =>
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn (← msg.toString)

/-! ## Worlds -/

/-- Relation between a goal term and the interpretation of its translation. -/
inductive World where
  /-- same type: `a = b` -/
  | same
  /-- `Nat` term interpreted as an `Int` term: `(↑a : Int) = b` -/
  | nat
  /-- `Bool` term interpreted as a proposition: `(a = true) = b` -/
  | bool
  /-- term of the polymorphic encoding: `w a = b` where `w` is the world of its type (e.g., `inj α a = b` for
      `a : α` with `α` a sort variable, see `Poly.mkWorld`), with a proof `inj` of the injectivity of `w` -/
  | poly (w inj : Expr)
  deriving BEq, Inhabited

def natCast (a : Expr) : Expr :=
  mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) a

def boolTrue (a : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) a (mkConst ``Bool.true)

def World.lift : World → Expr → Expr
  | .same, a => a
  | .nat, a => natCast a
  | .bool, a => boolTrue a
  | .poly w _, a => Poly.applyWorld w a

def worldOf (ta tb : Expr) : MetaM (Option World) := do
  if ta == tb then return some .same
  -- NOTE: types may be given by aliases (e.g., `abbrev Integer := Int`)
  let ta' ← whnfD ta
  let tb' ← whnfD tb
  if ta'.isConstOf ``Nat && tb'.isConstOf ``Int then return some .nat
  if ta'.isConstOf ``Bool && tb'.isProp then return some .bool
  if ← isDefEq ta tb then return some .same
  if let some (w, h) ← Poly.mkWorld ta tb then return some (.poly w h)
  return none

/-- `omega` on goals and hypotheses with the literals of Blaster's normal forms (e.g., `Int.ofNat 0`,
    `Int.negSucc 2`, which `omega` does not interpret). -/
def omegaTac : MetaM (TSyntax `tactic) :=
  `(tactic| ((try simp only [Int.ofNat_eq_coe, Int.negSucc_eq] at *) <;> omega))

/-- `Int.ofNat n` (resp. `Int.negSucc n`) in the notation of `omega`: `↑n` (resp. `-(↑n + 1)`), and raw `Nat`
    literals as `OfNat` literals (definitionally equal). -/
partial def omegaNotation (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then some e
    else if let .lit (.natVal n) := e then some (mkNatLit n)
    else if e.isAppOfArity ``Int.ofNat 1 then
      match e.appArg! with
      | .lit (.natVal n) => some (mkIntLit n)
      | a => some (natCast (omegaNotation a))
    else if e.isAppOfArity ``Int.negSucc 1 then
      match e.appArg! with
      | .lit (.natVal n) => some (mkIntNeg (mkIntLit (n + 1)))
      | a => some (mkIntNeg (mkIntAdd (natCast (omegaNotation a)) (mkIntLit 1)))
    else none

/-- `e` with the case analyses on constructors reduced (e.g., the selectors of the interpretation applied to
    constructor applications in the cases of a matcher). -/
def reduceCases (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun e => do
    let .const n _ := e.getAppFn | return .done e
    if isCasesOnRecursor env n then return .done (← whnfCore e) else return .done e)

/-- Proof of `p` by `omega` from the hypotheses of the local context (in the notation of `omega`, see
    `omegaNotation`, with the case analyses on constructors reduced), without the tactic framework and the
    auxiliary theorems of the `omega` tactic. -/
def omegaProof? (p : Expr) : MetaM (Option Expr) :=
  Blaster.Reconstruct.attempt Blaster.Reconstruct.dischargeHeartbeats do
    let m ← mkFreshExprSyntheticOpaqueMVar (omegaNotation (← reduceCases p))
    let some g ← m.mvarId!.falseOrByContra | return none
    g.withContext do
      let hyps ← (← getLocalHyps).toList.mapM fun h => do
        let t ← inferType h
        let t' := omegaNotation (← reduceCases t)
        if t' == t then pure h else mkExpectedTypeHint h t'
      Lean.Elab.Tactic.Omega.omega hyps g
    let pf ← instantiateMVars m
    if pf.hasExprMVar then return none
    -- NOTE: as the `omega` tactic, the proof (typically large) is an auxiliary theorem
    return some (← mkAuxTheorem p (← mkExpectedTypeHint pf p) (zetaDelta := true))

/-- The free variables of `es` and, transitively, of their types and values, in the order of the local context. -/
def fvarClosure (es : Array Expr) : MetaM (Array Expr) := do
  let mut todo := es.foldl (fun acc e => (collectFVars {} e).fvarIds ++ acc) #[]
  let mut seen : FVarIdSet := {}
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if seen.contains f then continue
    seen := seen.insert f
    let some d := (← getLCtx).find? f | continue
    let s := collectFVars {} d.type
    let s := match d.value? with | some v => collectFVars s v | none => s
    todo := todo ++ s.fvarIds
  let lctx ← getLCtx
  return lctx.foldl (init := #[]) fun acc d => if seen.contains d.fvarId then acc.push d.toExpr else acc

/-- Run `k` in the local context restricted to the free variables of `es` (see `fvarClosure`): tactics are not
    slowed down by the other hypotheses of the context (e.g., the negated goal, which `simp at *` would rewrite
    and `omega` would analyze). -/
def withRestrictedLCtx [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n] (es : Array Expr) (k : n α) : n α := do
  let keep ← liftM (m := MetaM) <| fvarClosure es
  let full ← liftM (m := MetaM) getLCtx
  let restricted := keep.foldl (init := ({} : LocalContext)) fun l x =>
    match full.find? x.fvarId! with
    | some d => l.addDecl d
    | none => l
  let insts := (← liftM (m := MetaM) getLocalInstances).filter fun li => keep.contains li.fvar
  withLCtx restricted insts k

/-! ## Matchers -/

/-- Translation of a match alternative: the conditions on the discriminants (in the order of
    Blaster's translation) and the values of the pattern variables. -/
structure AltView where
  conds : Array Expr
  vals : Array Expr

def isLiteral (e : Expr) : Bool :=
  let natLit (n : Expr) : Bool := n.isRawNatLit || (n.isAppOfArity ``OfNat.ofNat 3 && (n.getArg! 1).isRawNatLit)
  e.isRawNatLit || e.isStringLit || e.isConstOf ``Bool.true || e.isConstOf ``Bool.false ||
  ((e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1) && natLit e.appArg!) ||
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit)

/-- `N + q` patterns on `Nat` (Blaster's `Nat.add N q`, `q + N`, `Nat.succ q`): `(N, q)`. -/
partial def natOffset? (p : Expr) : Option (Nat × Expr) :=
  let lit? (e : Expr) : Option Nat :=
    match e with
    | .lit (.natVal n) => some n
    | _ => if e.isAppOfArity ``OfNat.ofNat 3 then (match e.getArg! 1 with | .lit (.natVal n) => some n | _ => none) else none
  let rec go (p : Expr) (acc : Nat) : Option (Nat × Expr) :=
    if p.isAppOfArity ``Nat.succ 1 then go p.appArg! (acc + 1)
    else if p.isAppOfArity ``Nat.add 2 then
      match lit? (p.getArg! 0) with
      | some n => go (p.getArg! 1) (acc + n)
      | none => (match lit? (p.getArg! 1) with
          | some n => go (p.getArg! 0) (acc + n)
          | none => if acc == 0 then none else some (acc, p))
    else if p.isAppOfArity ``HAdd.hAdd 6 then
      match lit? (p.getArg! 5) with
      | some n => go (p.getArg! 4) (acc + n)
      | none => if acc == 0 then none else some (acc, p)
    else if acc == 0 then none else some (acc, p)
  go p 0

def mkNatLe (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [levelZero]) (mkConst ``Nat) (mkConst ``instLENat) a b

/-- Raw `Nat` literal. -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

/-- Blaster's normal form of the patterns in the conditions of the `ite` encoding (see
    `removeNamedPatternExpr` and `optimizePattern`): named patterns removed, and `Nat.add` (resp. `Int.neg`)
    applications on literals evaluated, e.g., `Int.neg (Int.ofNat (Nat.add 1 (p@(Nat.add 1 1))))` is `Int.negSucc 2`. -/
partial def normPattern (p : Expr) : Expr :=
  if p.isAppOfArity ``namedPattern 4 then normPattern p.getAppArgs[2]! else
  if !p.isApp then p else
  let f := p.getAppFn
  let args := p.getAppArgs.map normPattern
  if f.isConstOf ``Nat.add && args.size == 2 then
    match rawNatLit? args[0]!, rawNatLit? args[1]! with
    | some 0, _ => args[1]!
    | some a, some b => mkRawNatLit (a + b)
    | some a, none =>
        -- `N₁ + (N₂ + n)` is `(N₁ + N₂) + n`
        match (if args[1]!.isAppOfArity ``Nat.add 2 then rawNatLit? (args[1]!.getArg! 0) else none) with
        | some b => mkApp2 f (mkRawNatLit (a + b)) (args[1]!.getArg! 1)
        | none => mkAppN f args
    | _, _ => mkAppN f args
  else if f.isConstOf ``Int.neg && args.size == 1 then
    let a := args[0]!
    let lit? : Option Int :=
      if a.isAppOfArity ``Int.ofNat 1 then (rawNatLit? a.appArg!).map Int.ofNat
      else if a.isAppOfArity ``Int.negSucc 1 then (rawNatLit? a.appArg!).map Int.negSucc
      else none
    match lit? with
    | some i =>
        match -i with
        | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
        | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)
    | none => if a.isAppOfArity ``Int.neg 1 then a.appArg! else mkAppN f args
  else mkAppN f args

/-- Conditions and values of the `Nat`/`Int` patterns with variables (see `mkCond` and `mkLet` in
    `Blaster.Smt.Translate.Match`): `N + n` (`N ≤ x`, `n := x - N`), `Int.ofNat n` (`0 ≤ x`, `n := x.toNat`),
    `Int.ofNat (N + n)` (`N ≤ x`, `n := (x - N).toNat`), `Int.neg (Int.ofNat (N + n))` (`x ≤ -N`,
    `n := (-(x + N)).toNat`, Blaster's normal form of `Int.negSucc`), `Int.negSucc n` (`x ≤ -1`,
    `n := (-x - 1).toNat`). Returns the condition and the pattern of the variable with its value. -/
def numPattern? (x p : Expr) : Option (Expr × Expr × Expr) := Id.run do
  let natLit (n : Nat) : Expr := mkRawNatLit n
  if let some (n, q) := natOffset? p then
    return some (mkNatLe (natLit n) x, q,
      mkApp6 (mkConst ``HSub.hSub [levelZero, levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
        (mkApp2 (mkConst ``instHSub [levelZero]) (mkConst ``Nat) (mkConst ``instSubNat)) x (natLit n))
  if p.isAppOfArity ``Int.neg 1 && p.appArg!.isAppOfArity ``Int.ofNat 1 then
    if let some (n, q) := natOffset? p.appArg!.appArg! then
      return some (mkIntLe x (mkIntNeg (mkIntLit n)), q, mkApp (mkConst ``Int.toNat) (mkIntNeg (mkIntAdd x (mkIntLit n))))
  if p.isAppOfArity ``Int.ofNat 1 then
    let q := p.appArg!
    if let some (n, q') := natOffset? q then
      return some (mkIntLe (mkIntLit n) x, q', mkApp (mkConst ``Int.toNat) (mkIntSub x (mkIntLit n)))
    return some (mkIntLe (mkIntLit 0) x, q, mkApp (mkConst ``Int.toNat) x)
  if p.isAppOfArity ``Int.negSucc 1 then
    return some (mkIntLe x (mkIntNeg (mkIntLit 1)), p.appArg!, mkApp (mkConst ``Int.toNat) (mkIntSub (mkIntNeg x) (mkIntLit 1)))
  return none

/-- Literals of Blaster's normal forms in the notation of the interpretation (see `mkIntLit`). -/
def stdLit (e : Expr) : Expr :=
  match e with
  | .lit (.natVal n) => mkNatLit n
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => mkIntLit n
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => mkIntNeg (mkIntLit (n + 1))
  | e => e

/-- Conditions of pattern `p` on the discriminant `x` (see `mkCond` in `Blaster.Smt.Translate.Match`).
    Returns `none` for unsupported patterns. -/
partial def patCond (x p : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
  -- NOTE: the named patterns are removed and the literals evaluated (see `removeNamedPatternExpr`)
  let p := normPattern p
  -- literals (in the notation of the interpretation, e.g., `-3` for `Int.negSucc 2`)
  if isLiteral p then return some (acc.push (← mkEq (stdLit p) x))
  if p.isFVar then return some acc
  if let some (c, q, _) := numPattern? x p then
    -- NOTE: the variable of the pattern has no condition
    if q.isFVar then return some (acc.push c)
    return none
  let .const c _ := p.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  let args := p.getAppArgs
  if args.size != info.numParams + info.numFields then return none
  -- `Nat`/`Int` patterns (e.g., `n + 1`) are not supported (their translation needs the conditions
  -- of the branch)
  if info.induct == ``Nat || info.induct == ``Int then return none
  let mut acc := acc.push (← mkTester c x)
  for i in [:info.numFields] do
    let s ← mkSelector c i x
    let some acc' ← patCond s args[info.numParams + i]! acc | return none
    acc := acc'
  return some acc

/-- Values of the variables of pattern `p` matched against `x` (see `mkLet` in
    `Blaster.Smt.Translate.Match`), as a substitution of the variables. -/
partial def patVals (x p : Expr) (acc : Std.HashMap FVarId Expr) : MetaM (Option (Std.HashMap FVarId Expr)) := do
  if p.isAppOfArity ``namedPattern 4 then
    let args := p.getAppArgs
    let .fvar n := args[1]! | return none
    return ← patVals x args[2]! (acc.insert n x)
  if let .fvar v := p then return some (acc.insert v x)
  if isLiteral p then return some acc
  if let some (_, q, v) := numPattern? x p then
    if let .fvar n := q then return some (acc.insert n v)
    -- named pattern below the numeric pattern (e.g., `Int.ofNat (n@0)`): `n` and the variables of its pattern
    if q.isAppOfArity ``namedPattern 4 then return ← patVals v q acc
    return none
  -- named literal below `Int.ofNat` (e.g., `Int.ofNat (n@0)`): `n := x.toNat`
  if p.isAppOfArity ``Int.ofNat 1 && p.appArg!.isAppOfArity ``namedPattern 4 then
    return ← patVals (mkApp (mkConst ``Int.toNat) x) p.appArg! acc
  let .const c _ := p.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  if info.induct == ``Nat || info.induct == ``Int then return none
  let args := p.getAppArgs
  let mut acc := acc
  for i in [:info.numFields] do
    let some acc' ← patVals (← mkSelector c i x) args[info.numParams + i]! acc | return none
    acc := acc'
  return some acc

/-- Types of the alternatives of matcher `m` (with level parameters `lvls`) for the parameters `params`,
    a motive given as a free variable, and discriminants `discrs`: the patterns are the arguments of the
    motive. `inst` is Blaster's optimized instance of the matcher (when known), whose alternative types
    are the patterns as translated. -/
def altTypes (m : Name) (lvls : List Level) (info : MatcherInfo) (inst? : Option Expr)
    (params : Array Expr) (motive : Expr) (discrs : Array Expr) : MetaM (Array Expr) := do
  let args := params ++ #[motive] ++ discrs
  match inst? with
  | some inst =>
      -- `fun params motive discrs alts => ...`
      let mut e := inst
      for a in args do
        let .lam _ _ b _ := e | throwError "bridge: unexpected matcher instance"
        e := b.instantiate1 a
      let mut ts := #[]
      for _ in [:info.numAlts] do
        let .lam _ t b _ := e | throwError "bridge: unexpected matcher instance"
        ts := ts.push t
        e := b
      if ts.any (·.hasLooseBVars) then throwError "bridge: dependent alternatives"
      return ts
  | none =>
      let ty ← instantiateForall (← inferType (mkConst m lvls)) args
      let mut e := ty
      let mut ts := #[]
      for _ in [:info.numAlts] do
        let .forallE _ t b _ := e | throwError "bridge: unexpected matcher type"
        ts := ts.push t
        e := b
      if ts.any (·.hasLooseBVars) then throwError "bridge: dependent alternatives"
      return ts

/-- `ite` chain of Blaster's translation of `M params motive discrs alts`, given the types of the
    alternatives (with motive `mv`, a free variable): `if c₁ then alt₁ v⃗₁ else ... altₙ v⃗ₙ` where the
    last alternative has no condition, and an alternative without conditions ends the chain. The
    applications of the alternatives are β-reduced when `beta` is set. -/
partial def iteOf (ty : Expr) (mv : Expr) (altTys : Array Expr) (discrs alts : Array Expr) (beta : Bool) :
    Term.TermElabM (Option Expr) := do
  let u ← getLevel ty
  -- per alternative: the condition and the application of the alternative given a proof of the condition
  -- (for the proof parameters of named patterns `x@h:p`, whose equations hold under the condition)
  let mut branches : Array (Option Expr × (Option Expr → Term.TermElabM (Option Expr)) × Bool) := #[]
  for j in [:altTys.size] do
    let r ← forallTelescope altTys[j]! fun ys concl => do
      -- patterns: the arguments of the motive
      if !concl.isApp || concl.getAppFn != mv then dbg m!"bridge: unexpected alternative type {altTys[j]!}"; return none
      let pats := concl.getAppArgs
      if pats.size != discrs.size then dbg m!"bridge: unexpected patterns {pats}"; return none
      let mut conds := #[]
      let mut vals : Std.HashMap FVarId Expr := {}
      for (d, p) in discrs.zip pats do
        let some cs ← patCond d p conds | dbg m!"bridge: unsupported pattern {p} in {altTys[j]!}"; return none
        conds := cs
        let some vs ← patVals d p vals | dbg m!"bridge: unsupported pattern {p}"; return none
        vals := vs
      -- arguments of the alternative: the values of the pattern variables (`()` for `Unit`), proofs of the
      -- equations of named patterns (`none`)
      let mut args : Array (Option Expr) := #[]
      for y in ys do
        if let some v := vals.get? y.fvarId! then args := args.push (some v)
        else if (← inferType y).isConstOf ``Unit then args := args.push (some (mkConst ``Unit.unit))
        else if ← isProp (← inferType y) then args := args.push none
        else dbg m!"bridge: no value for the pattern variable {y} of {altTys[j]!}"; return none
      let dependent := args.any (·.isNone)
      let alt := alts[j]!
      let mk (hc? : Option Expr) : Term.TermElabM (Option Expr) := do
        let mut app := alt
        for a? in args do
          match a? with
          | some v => app := mkApp app v
          | none =>
              let some _ := hc? | return none
              let .forallE _ dom _ _ ← whnf (← inferType app) | return none
              let some pf ← proveEquation dom | dbg m!"bridge: equation of a named pattern not proved: {dom}"; return none
              app := mkApp app pf
        return some (if beta then app.headBeta else app)
      let cond ← if conds.isEmpty then pure none else some <$> foldAnd conds
      return some (cond, mk, dependent)
    let some b := r | return none
    branches := branches.push b
    if b.1.isNone then break
  let some (_, mkLast, depLast) := branches.back? | return none
  if depLast then return none
  let some last ← mkLast none | return none
  let mut acc := last
  for (c?, mk, dependent) in branches.pop.reverse do
    let some c := c? | return none
    let inst := mkApp (mkConst ``Classical.propDecidable) c
    if dependent then
      let some t ← withLocalDeclD `hc c fun hc => do
          let some app ← mk (some hc) | return none
          return some (← mkLambdaFVars #[hc] app)
        | return none
      acc := mkApp5 (mkConst ``dite [u]) ty c inst t (mkLambda `hc .default (mkNot c) acc)
    else
      let some app ← mk none | return none
      acc := mkApp5 (mkConst ``ite [u]) ty c inst app acc
  return some acc
where
  foldAnd (cs : Array Expr) : MetaM Expr := do
    let mut acc := cs.back!
    for c in cs.pop.reverse do acc := mkAnd c acc
    return acc
  /-- Proof of the equation of a named pattern under the condition of its alternative (in the local context). -/
  proveEquation (p : Expr) : Term.TermElabM (Option Expr) := do
    -- NOTE: the named patterns of the equations of the previous variables (reducible) are removed
    let some pf ← proveEquation' (stripNamed p) | return none
    return some (← mkExpectedTypeHint pf p)
  stripNamed (e : Expr) : Expr :=
    e.replace fun e => if e.isAppOfArity ``namedPattern 4 then some (stripNamed e.getAppArgs[2]!) else none
  proveEquation' (p : Expr) : Term.TermElabM (Option Expr) := do
    if let some pf ← omegaProof? p then return some pf
    for tac in [← `(tactic| (subst_vars; rfl)), ← `(tactic| (simp_all; done)),
                ← `(tactic| (rename_i h; cases h; subst_vars; simp_all))] do
      if let some pf ← Blaster.Reconstruct.proveWithTactic p tac then return some pf
    return none

/-- β-reduction of the alternatives of an `ite`/`dite` chain (see `iteOf`). -/
partial def betaChain (e : Expr) : Expr :=
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, args[3]!.headBeta, betaChain args[4]!]
  else if e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let t := match args[3]! with
      | .lam n ty b bi => Expr.lam n ty b.headBeta bi
      | t => t
    let f := match args[4]! with
      | .lam n ty b bi => Expr.lam n ty (betaChain b) bi
      | f => f
    mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t, f]
  else e.headBeta

/-! ## Proofs of the matcher equations -/

/-- Value of a condition of the `ite` encoding (a conjunction of testers and literal equalities), possibly
    after a case analysis. -/
inductive CondVal where
  | isTrue (pf : Expr)
  | isFalse (pf : Expr)
  /-- case analysis needed on a free variable -/
  | splitFVar (x : FVarId)
  /-- case analysis needed on a proposition (an equality between a variable and a literal) -/
  | splitProp (p : Expr)
  | unknown

/-- Free variable whose case analysis unblocks `e` (a stuck recursor application whose major premise is a
    free variable or a projection of a free variable). -/
def stuckMajor? (e : Expr) : MetaM (Option FVarId) := do
  let .const n _ := e.getAppFn | return none
  let env ← getEnv
  let idx? : Option Nat := match env.find? n with
    | some (.recInfo info) => some info.getMajorIdx
    | _ => none
  let some idx := idx? | return none
  let some m := e.getAppArgs[idx]? | return none
  match ← whnfD m with
  | .fvar f => return some f
  | .proj _ _ s =>
      let .fvar f ← whnfD s | return none
      return some f
  | _ => return none

/-- Value of a closed decidable condition (e.g., an equation between literals in different forms, such as
    `Int.ofNat 0 = Int.ofNat Nat.zero`), by evaluation of its decision procedure. -/
def evalClosed? (c : Expr) : MetaM (Option CondVal) := do
  if c.hasFVar || c.hasMVar then return none
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c) catch _ => pure none) | return none
  let r ← try withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 2000 * 1000 }) <|
      withCurrHeartbeats <| withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) c inst)
    catch _ => return none
  let refl (b : Name) := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst b)
  if r.isConstOf ``Bool.true then return some (.isTrue (mkApp3 (mkConst ``of_decide_eq_true) c inst (refl ``Bool.true)))
  if r.isConstOf ``Bool.false then return some (.isFalse (mkApp3 (mkConst ``of_decide_eq_false) c inst (refl ``Bool.false)))
  return none

partial def evalCond (c : Expr) : Term.TermElabM CondVal := do
  let c := c.consumeMData
  if c.isAppOfArity ``And 2 then
    let a := c.appFn!.appArg!
    let b := c.appArg!
    match ← evalCond a with
    | .isTrue pa =>
        match ← evalCond b with
        | .isTrue pb => return .isTrue (mkApp4 (mkConst ``And.intro) a b pa pb)
        | .isFalse nb => return .isFalse (mkLambda `h .default c (mkApp nb (mkApp3 (mkConst ``And.right) a b (.bvar 0))))
        | r => return r
    | .isFalse na => return .isFalse (mkLambda `h .default c (mkApp na (mkApp3 (mkConst ``And.left) a b (.bvar 0))))
    | r => return r
  let c' ← whnfD c
  if c'.isConstOf ``True then return .isTrue (← mkExpectedTypeHint (mkConst ``True.intro) c)
  if c'.isConstOf ``False then return .isFalse (mkLambda `h .default c (.bvar 0))
  if let some v ← evalClosed? c then return v
  if let some (_, l, r) := c'.eq? then
    let l ← whnfD l
    let r ← whnfD r
    if isLiteral l && isLiteral r then
      if ← isDefEq l r then return .isTrue (← mkEqRefl l)
      let pf ← mkDecideProof (mkNot (← mkEq l r))
      return .isFalse (← mkExpectedTypeHint pf (mkNot c))
    let (v, lit) := if isLiteral l then (r, l) else (l, r)
    if let some x ← stuckMajor? v then return .splitFVar x
    -- field of a structure variable
    if let .proj _ _ st := v then
      if let .fvar x ← whnfD st then return .splitFVar x
    if v.isFVar && isLiteral lit then
      -- hypothesis `¬ v = lit` (resp. `¬ lit = v`) of a previous case analysis
      for d in ← getLCtx do
        if let some p := d.type.not? then
          if let some (_, a, b) := p.eq? then
            -- NOTE: `c` is `l = r` up to reduction
            let ty ← inferType v
            let u ← getLevel ty
            if (a == l && b == r) then
              return .isFalse (mkLambda `h .default c (mkApp d.toExpr (.bvar 0)))
            if (a == r && b == l) then
              return .isFalse (mkLambda `h .default c (mkApp d.toExpr (mkApp4 (mkConst ``Eq.symm [u]) ty l r (.bvar 0))))
      return .splitProp (← mkEq v lit)
  if let some x ← stuckMajor? c' then return .splitFVar x
  -- arithmetic conditions (e.g., of `n + 1` patterns, or literal patterns of `Int` against the patterns of
  -- the matcher's case analysis): decided by `omega` in the context of the case analysis
  -- NOTE: on the condition before reduction (e.g., `Int.le` unfolds to `Int.NonNeg`)
  let numEq ← match c.eq? with
    | some (t, _, _) => do let t ← whnfR t; pure (t.isConstOf ``Int || t.isConstOf ``Nat)
    | none => pure false
  let arith := c.isAppOfArity ``LE.le 4 || c.isAppOfArity ``LT.lt 4 || numEq
  if arith then
    -- NOTE: the conditions of the alternatives preceding the alternative of a case are false
    if let some p ← omegaProof? (mkNot c) then return .isFalse p
    if let some p ← omegaProof? c then return .isTrue p
  dbg m!"bridge: unknown atom {c'}"
  return .unknown

/-- Close `g` with an overlap hypothesis of the splitter (`∀ ys, x = p → False`) whose equalities hold by
    unification. -/
def closeByOverlap (g : MVarId) (base : Nat) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    -- only the hypotheses of the proof (not the ones of the context)
    if d.index < base || d.isImplementationDetail || !d.type.isForall then continue
    let s ← saveState
    let ok ← try
        let (ms, _, body) ← forallMetaTelescopeReducing d.type
        if !body.isConstOf ``False then pure false
        else
          let mut ok := true
          for m in ms do
            let t ← instantiateMVars (← inferType m)
            if let some (_, a, b) := t.eq? then
              if ← isDefEq a b then m.mvarId!.assign (← mkEqRefl a) else ok := false; break
          if ok then
            let pf ← instantiateMVars (mkAppN d.toExpr ms)
            if pf.hasExprMVar then pure false
            else
              g.assign (← mkFalseElim (← g.getType) pf)
              pure true
          else pure false
      catch _ => pure false
    if ok then return true
    s.restore
  return false

/-- Variable of type `Nat` or `Int` of the condition `c` occurring in an overlap hypothesis of the splitter. -/
def overlapVar? (g : MVarId) (c : Expr) (base : Nat) : MetaM (Option FVarId) := g.withContext do
  let c ← instantiateMVars c
  let lctx ← getLCtx
  for d in lctx do
    if d.index < base || d.isImplementationDetail || !d.type.isForall then continue
    for x in (collectFVars {} c).fvarIds do
      if !d.type.containsFVar x then continue
      let some xd := lctx.find? x | continue
      let t ← whnfR xd.type
      if t.isConstOf ``Nat || t.isConstOf ``Int then return some x
  return none

/-- Prove `lhs = rhs`, where `rhs` is an `ite` chain over conditions decided by case analysis, by
    evaluating the conditions (with case analyses on the variables and literal equalities blocking them). -/
partial def solveIte (g : MVarId) (fuel : Nat) (base : Nat) : Term.TermElabM Bool := g.withContext do
  if fuel == 0 then dbg m!"bridge: no fuel left for {g}"; return false
  if ← closeByOverlap g base then return true
  let tgt ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := tgt.eq? | return false
  let dep := rhs.isAppOfArity ``dite 5
  if !dep && !rhs.isAppOfArity ``ite 5 then
    try g.refl; return true
    catch _ =>
      -- applications of the same alternative to arguments equal up to arithmetic (e.g., the values of the
      -- variables of `Int.ofNat (N + n)` patterns, `n` and `(Int.ofNat (n + N) - N).toNat`)
      if lhs.getAppFn.isFVar && lhs.getAppFn == rhs.getAppFn then
        let omega ← omegaTac
        let tac ← `(tactic| (congr 1 <;> first | rfl | $omega:tactic))
        if let some pf ← Blaster.Reconstruct.proveWithTactic tgt tac then
          g.assign pf; return true
      dbg m!"bridge: leaf {← ppGoal g}"
      return false
  let args := rhs.getAppArgs
  let (α, c, inst, t, e) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  -- `lhs = rhs` from `lhs = b` where `b` is the branch selected by `pc`
  let select (lem : Name) (b pc : Expr) : Term.TermElabM Bool := do
    let b := if dep then (mkApp b pc).headBeta else b
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs b)
    let h ← mkAppOptM lem #[c, inst, pc, α, t, e]
    g.assign (← mkEqTrans g' (← mkEqSymm h))
    solveIte g'.mvarId! (fuel - 1) base
  match ← evalCond c with
  | .isTrue pc => select (if dep then ``dif_pos else ``if_pos) t pc
  | .isFalse pnc => select (if dep then ``dif_neg else ``if_neg) e pnc
  | .splitFVar x =>
      let gs ← try g.cases x catch ex =>
        dbg m!"bridge: cases failed {ex.toMessageData} in {g}"
        return false
      gs.allM fun s => solveIte s.mvarId (fuel - 1) base
  | .splitProp p =>
      let (s₁, s₂) ← g.byCases p
      let g₁ : MVarId := (← subst? s₁.mvarId s₁.fvarId).getD s₁.mvarId
      if !(← solveIte g₁ (fuel - 1) base) then return false
      solveIte s₂.mvarId (fuel - 1) base
  | .unknown =>
      -- a variable constrained by an overlap hypothesis of the splitter (e.g., `∀ n, x = n + 2 → False` for an
      -- arithmetic condition on `x`): case analysis
      if let some x ← overlapVar? g c base then
        if let some gs ← try some <$> g.cases x catch _ => pure none then
          return ← gs.allM fun s => solveIte s.mvarId (fuel - 1) base
      dbg m!"bridge: unknown condition {c} ⟶ {← whnfD c} in {← ppGoal g}"
      return false

/-- Prove a matcher equation `∀ xs alts, M params motive xs alts = ite ...` (see `iteOf`). -/
def proveMatchIte (stmt : Expr) (fuel := 256) : Term.TermElabM (Option Expr) := do
  let m ← mkFreshExprMVar stmt
  let base := (← getLCtx).decls.size
  let s ← saveState
  try
    let (_, g) ← m.mvarId!.intros
    let ok ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let some (_, lhs, _) := tgt.eq? | return false
      let gs ← try Split.splitMatch g lhs catch _ => pure [g]
      gs.allM (solveIte · fuel base)
    if !ok then s.restore; return none
    let pf ← instantiateMVars m
    if pf.hasExprMVar then s.restore; return none
    return some pf
  catch ex =>
    dbg m!"bridge: {ex.toMessageData}"
    s.restore; return none

/-- `∀ ys, G₁ → … → Gₙ → Q` where the guards `Gᵢ` (membership predicates of the polymorphic encoding, see `Poly`)
    follow all the binders (e.g., Blaster's translation of `∀ (xs : List β) (f : List β → Nat), P`): the equivalent
    proposition where each guard follows the last binder it mentions (i.e., the order of the goal), with a proof
    of their equality. -/
partial def interleaveGuards (b : Expr) : MetaM (Option (Expr × Expr)) := do
  -- only for quantifiers over the types of the encoding
  let rec univBinder (e : Expr) (fuel : Nat) : Bool :=
    match fuel, e with
    | fuel + 1, .forallE _ t body _ => Poly.hasUniv t || univBinder body fuel
    | _, _ => false
  let .forallE _ _ (.forallE ..) _ := b | return none
  if !univBinder b 8 then return none
  go b #[] #[]
where
  -- NOTE: the definitions of the membership predicates of datatypes may be expanded by the backend (see
  -- `polyGuardEq`)
  isGuard (t : Expr) : Bool :=
    (t.isAppOfArity ``Poly.Img 4 && t.appArg!.isFVar) || (t.find? (·.isAppOfArity ``Poly.Img 4)).isSome
  go (e : Expr) (ys gs : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if let .forallE n t body bi := e then
      if gs.isEmpty && !(← isProp t) then
        return ← withLocalDecl n bi t fun y => go (body.instantiate1 y) (ys.push y) gs
      if isGuard t && !body.hasLooseBVars then
        return ← withLocalDecl n bi t fun g => go body ys (gs.push g)
    finish e ys gs
  finish (q : Expr) (ys gs : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if gs.isEmpty || ys.size < 2 then return none
    -- each guard after the last binder it mentions
    let mut order := #[]
    let mut placed := Array.replicate gs.size false
    for y in ys do
      order := order.push y
      for i in [:gs.size] do
        if placed[i]! then continue
        let gt ← inferType gs[i]!
        if ys.all fun y' => !gt.containsFVar y'.fvarId! || order.contains y' then
          order := order.push gs[i]!
          placed := placed.set! i true
    if placed.any (!·) || order == ys ++ gs then return none
    let b' ← mkForallFVars order q
    let b ← mkForallFVars (ys ++ gs) q
    let mp ← withLocalDeclD `h b' fun h => do mkLambdaFVars #[h] (← mkLambdaFVars (ys ++ gs) (mkAppN h order))
    let mpr ← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (← mkLambdaFVars order (mkAppN h (ys ++ gs)))
    return some (b', mkApp3 (mkConst ``propext) b' b (mkApp4 (mkConst ``Iff.intro) b' b mp mpr))

end Blaster.Reconstruct.SmtProof.Bridge
