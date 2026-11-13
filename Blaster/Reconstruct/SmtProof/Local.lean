import Lean

/-!
# Local proofs of equalities between large terms

Steps of SMT proofs (e.g., Z3's `rewrite`, `th-lemma`) often relate large terms that differ in a few
places only, and whose validity does not depend on the structure of their common subterms. Instead of
calling tactics on the whole statement:
 - `diffEq` relates the two sides by congruence on their common structure, and proves the remaining
   differences (the smallest subterms whose heads differ) separately;
 - `generalizeCommon` abstracts the maximal subterms common to both sides of a local statement as
   variables, such that the tactics only see the structure relevant to the rewrite.
-/

open Lean Meta Elab Term

namespace Blaster.Reconstruct.SmtProof.Local

theorem classical_ite_congr {α : Sort u} {c c' : Prop} {x x' y y' : α} (hc : c = c') (hx : x = x') (hy : y = y') :
    @ite α c (Classical.propDecidable c) x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc hx hy; rfl

theorem classical_decide_congr {p p' : Prop} (h : p = p') :
    @decide p (Classical.propDecidable p) = @decide p' (Classical.propDecidable p') := by
  subst h; rfl

theorem classical_ite_congr_ctx {α : Sort u} {c c' : Prop} {x x' y y' : α} (hc : c = c') (hx : c → x = x')
    (hy : ¬c → y = y') :
    @ite α c (Classical.propDecidable c) x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases h : c
  · rw [if_pos h, if_pos h]; exact hx h
  · rw [if_neg h, if_neg h]; exact hy h

theorem classical_ite_not {α : Sort u} (c : Prop) (x y : α) :
    @ite α (¬c) (Classical.propDecidable (¬c)) x y = @ite α c (Classical.propDecidable c) y x := by
  by_cases h : c
  · rw [if_neg (fun h' => h' h), if_pos h]
  · rw [if_pos h, if_neg h]

theorem ite_eq_or {α : Sort u} {c : Prop} {a b k : α} {e : Prop} (ha : c → a = k) (hb : ¬c → (b = k) = e) :
    (@ite α c (Classical.propDecidable c) a b = k) = (c ∨ e) := by
  by_cases h : c
  · rw [if_pos h]; exact propext ⟨fun _ => Or.inl h, fun _ => ha h⟩
  · rw [if_neg h, hb h]; exact propext ⟨Or.inr, fun h' => h'.resolve_left h⟩

theorem ite_eq_and {α : Sort u} {c : Prop} {a b k : α} {e : Prop} (ha : c → ¬a = k) (hb : ¬c → (b = k) = e) :
    (@ite α c (Classical.propDecidable c) a b = k) = (¬c ∧ e) := by
  by_cases h : c
  · rw [if_pos h]; exact propext ⟨fun h' => absurd h' (ha h), fun h' => absurd h h'.1⟩
  · rw [if_neg h, hb h]; exact propext ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩

theorem eq_comm_eq {α : Sort u} (a b : α) : (a = b) = (b = a) := propext eq_comm

theorem and_congr_ctx {a a' b b' : Prop} (ha : a = a') (hb : a → b = b') : (a ∧ b) = (a' ∧ b') := by
  subst ha; exact propext ⟨fun ⟨x, y⟩ => ⟨x, hb x ▸ y⟩, fun ⟨x, y⟩ => ⟨x, (hb x).symm ▸ y⟩⟩

theorem or_congr_ctx {a a' b b' : Prop} (ha : a = a') (hb : ¬a → b = b') : (a ∨ b) = (a' ∨ b') := by
  subst ha
  exact propext ⟨fun h => h.elim Or.inl (fun y => Classical.byCases (p := a) Or.inl (fun x => Or.inr (hb x ▸ y))),
    fun h => h.elim Or.inl (fun y => Classical.byCases (p := a) Or.inl (fun x => Or.inr ((hb x).symm ▸ y)))⟩


/-- The size (in distinct subterms, see `sizeLe`) beyond which a statement is large (e.g., the CEK evaluation of a
    validator): the tactics are only applied to its local differences (see `diffEq`), within time budgets. -/
def largeTermSize : Nat := 20000

/-- `x` with a budget of `budget` thousand heartbeats: `none` on any exception, including the runtime ones (e.g.,
    running out of the budget, which `try ... catch` does not catch); interruptions are propagated. -/
def withBudget? (budget : Nat) (x : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (some <$> withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 }) (withCurrHeartbeats x))
    fun _ => pure none

/-- `ite c x y = ite c' x' y'` (with the classical instances of the interpretation, whose argument depends on
    the condition), given the proofs of the equalities of the arguments (`sub`); similarly for `decide`. -/
def iteCongr? [Monad m] [MonadLiftT MetaM m] (l r : Expr) (sub : Expr → Expr → m (Option Expr)) : m (Option Expr) := do
  if l.isAppOfArity ``Decidable.decide 2 && r.isAppOfArity ``Decidable.decide 2 then
    if (l.getArg! 1).isAppOfArity ``Classical.propDecidable 1 && (r.getArg! 1).isAppOfArity ``Classical.propDecidable 1 then
      let some h ← sub (l.getArg! 0) (r.getArg! 0) | return none
      return some (mkApp3 (mkConst ``classical_decide_congr) (l.getArg! 0) (r.getArg! 0) h)
    return none
  if !(l.isAppOfArity ``ite 5 && r.isAppOfArity ``ite 5) then return none
  let la := l.getAppArgs
  let ra := r.getAppArgs
  if !(la[2]!.isAppOfArity ``Classical.propDecidable 1 && ra[2]!.isAppOfArity ``Classical.propDecidable 1) then return none
  if la[0]! != ra[0]! then return none
  let some pc ← (if la[1]! == ra[1]! then liftM (mkEqRefl la[1]!) >>= (pure ∘ some) else sub la[1]! ra[1]!) | return none
  let some px ← (if la[3]! == ra[3]! then liftM (mkEqRefl la[3]!) >>= (pure ∘ some) else sub la[3]! ra[3]!) | return none
  let some py ← (if la[4]! == ra[4]! then liftM (mkEqRefl la[4]!) >>= (pure ∘ some) else sub la[4]! ra[4]!) | return none
  let u ← liftM (getLevel la[0]!)
  return some (mkAppN (mkConst ``classical_ite_congr [u]) #[la[0]!, la[1]!, ra[1]!, la[3]!, ra[3]!, la[4]!, ra[4]!, pc, px, py])

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

/-- Subterms of `e` without loose bound variables (traversal of the DAG, with sharing). -/
partial def closedSubterms (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  if acc.contains e then acc else
  let acc := if e.hasLooseBVars then acc else acc.insert e
  match e with
  | .app f a => closedSubterms a (closedSubterms f acc)
  | .lam _ t b _ | .forallE _ t b _ => closedSubterms b (closedSubterms t acc)
  | .letE _ t v b _ => closedSubterms b (closedSubterms v (closedSubterms t acc))
  | .mdata _ b | .proj _ _ b => closedSubterms b acc
  | _ => acc

/-- Terms that are never abstracted: atoms, literals, types. -/
def isAtomic (e : Expr) : Bool :=
  match e with
  | .fvar .. | .const .. | .lit .. | .sort .. | .bvar .. | .mvar .. => true
  | _ =>
    e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``Nat.cast 3 && (e.getArg! 2).isRawNatLit ||
    e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1 || e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3

/-- Comparisons of integers and natural numbers, kept visible to the arithmetic tactics (e.g., the conditions
    of conditionals rewritten under these conditions, such as `if 0 = x then 2 + x else ...` into `2`). -/
def isArithComparison (e : Expr) : Bool :=
  let numeric (t : Expr) := t.isConstOf ``Int || t.isConstOf ``Nat
  (e.isAppOfArity ``Eq 3 && numeric (e.getArg! 0)) || (e.isAppOfArity ``LE.le 4 && numeric (e.getArg! 0)) ||
  (e.isAppOfArity ``LT.lt 4 && numeric (e.getArg! 0))

/-- Applications of the arithmetic operations of `Int` and `Nat` (not comparisons), and conditionals of numbers. -/
def isArithOperation (e : Expr) : Bool :=
  let ops := #[(``HAdd.hAdd, 6), (``HSub.hSub, 6), (``HMul.hMul, 6), (``HDiv.hDiv, 6), (``HMod.hMod, 6),
    (``Neg.neg, 3), (``Nat.cast, 3), (``Int.toNat, 1), (``Int.natAbs, 1), (``Int.add, 2), (``Int.mul, 2),
    (``Int.neg, 1), (``Int.sub, 2), (``Int.ediv, 2), (``Int.emod, 2), (``Int.tdiv, 2), (``Int.tmod, 2),
    (``Int.fdiv, 2), (``Int.fmod, 2), (``Nat.add, 2), (``Nat.mul, 2), (``Nat.sub, 2), (``Nat.div, 2), (``Nat.mod, 2),
    (``Nat.succ, 1)]
  ops.any fun (n, k) => e.isAppOfArity n k ||
    -- conditionals of numbers (e.g., the encodings of the divisions of Blaster's macros)
    (e.isAppOfArity ``ite 5 && ((e.getArg! 0).isConstOf ``Int || (e.getArg! 0).isConstOf ``Nat))

/-- Replace the subterms `ss` (by structural equality) by the free variables `zs` in `e`. -/
partial def replaceAll (m : Std.HashMap Expr Expr) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some z := m.get? e then return z
  if let some e' := (← get).get? e then return e'
  let e' ← match e with
    | .app f a => pure (e.updateApp! (← replaceAll m f) (← replaceAll m a))
    | .lam _ t b _ => pure (e.updateLambdaE! (← replaceAll m t) (← replaceAll m b))
    | .forallE _ t b _ => pure (e.updateForallE! (← replaceAll m t) (← replaceAll m b))
    | .mdata _ b => pure (e.updateMData! (← replaceAll m b))
    | .proj _ _ b => pure (e.updateProj! (← replaceAll m b))
    | _ => pure e
  modify (·.insert e e')
  return e'

/-- The maximal subterms of `e` that are not arithmetic operations, conditionals of numbers, arithmetic comparisons or
    connectives (e.g., the atoms of an arithmetic term). -/
partial def arithLeaves (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let args := e.getAppArgs
  let sub (k : Nat) : Array Expr := args.extract (args.size - k) args.size
  let children? : Option (Array Expr) :=
    if e.isAppOfArity ``ite 5 then some #[args[1]!, args[3]!, args[4]!]
    else if isArithOperation e || isArithComparison e then
      some (if e.isAppOfArity ``Neg.neg 3 || e.isAppOfArity ``Nat.cast 3 || e.getAppNumArgs == 1 then sub 1 else sub 2)
    else if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then some args
    else if e.isAppOfArity ``Not 1 then some args
    else none
  match children? with
  | some cs => cs.foldl (fun acc c => arithLeaves c acc) acc
  | none => if isAtomic e || acc.contains e then acc else acc.push e

/-- Maximal subterms of `l` that also occur in `r` (and are neither atomic, types nor arithmetic comparisons). Arithmetic
    operations and conditionals of numbers are generalized only when their atoms don't occur elsewhere (e.g., not
    `-1 * x` in `x / (-1 * x)`, whose relation with `x` would be lost): their atoms are generalized otherwise. With
    `lossless`, no subterm is generalized when its subterms occur elsewhere (e.g., not the selector `Data.I.0 (p.1)`
    when `p` occurs in other subterms). -/
partial def commonSubterms (l r : Expr) (lossless := false) : MetaM (Array Expr) := do
  let inR := closedSubterms r {}
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  -- whether the atoms of `e` (resp. its subterms, with `lossless`) occur only in the occurrences of `e`
  let isolated (e : Expr) : Bool :=
    let hole := Lean.mkConst `_blaster_hole
    let m : Std.HashMap Expr Expr := ({} : Std.HashMap Expr Expr).insert e hole
    let (l', _) := (replaceAll m l).run {}
    let (r', _) := (replaceAll m r).run {}
    let rest := closedSubterms r' (closedSubterms l' {})
    let parts := if lossless then (closedSubterms e {}).toArray.filter (fun s => s != e && !isAtomic s) else arithLeaves e
    !parts.any rest.contains
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if !e.hasLooseBVars && !isAtomic e && !isArithComparison e && inR.contains e &&
        (!(lossless || isArithOperation e) || isolated e) then
      -- values and propositions (not types, partial applications, nor instances, which tactics must see)
      let ty ← whnfR (← inferType e)
      if !(ty.isSort && !ty.isProp) && !ty.isForall && (← isClass? ty).isNone then
        found.modify (·.push e)
        return
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  go l
  found.get


/-- `(∀ zs, stmt[zs/ss], ss)` where `ss` are the maximal subterms common to `l` and `r` (the sides of
    `stmt`), or `none` when there is no common subterm or the generalization is not type correct. -/
def generalizeCommon (stmt l r : Expr) (lossless := false) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← commonSubterms l r lossless
  if ss.isEmpty then return none
  -- NOTE: the types are unfolded to their inductive types (e.g., `Value := List (Data × Data)`), such that tactics
  -- can perform case analyses on the variables
  let types ← ss.mapM fun s => do
    let t ← inferType s
    let t' ← whnfD t
    if let .const n _ := t'.getAppFn then
      if (← getEnv).find? n matches some (.inductInfo _) then return t'
    return t
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"z{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

/-- Leaves of the maximal tree of applications of the binary operation `op` (e.g., `And`) at the root of `e`. -/
partial def opLeaves (op : Name) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity op 2 then opLeaves op e.appArg! (opLeaves op e.appFn!.appArg! acc) else acc.push e

/-- Whether the trees of `op` applications at the roots of `l` and `r` have the same shape. -/
partial def sameOpShape (op : Name) (l r : Expr) : Bool :=
  match l.isAppOfArity op 2, r.isAppOfArity op 2 with
  | true, true => sameOpShape op l.appFn!.appArg! r.appFn!.appArg! && sameOpShape op l.appArg! r.appArg!
  | false, false => true
  | _, _ => false

/-- `e` with the leaves of its tree of `op` applications replaced by `f`. -/
partial def mapOpLeaves (op : Name) (f : Expr → Expr) (e : Expr) : Expr :=
  if e.isAppOfArity op 2 then mkApp2 e.appFn!.appFn! (mapOpLeaves op f e.appFn!.appArg!) (mapOpLeaves op f e.appArg!)
  else f e

/-- `e = e'` where `e'` is `e` with the leaves of its tree of `op` applications rewritten with `proofs`. -/
partial def congrLeaves (op : Name) (proofs : Std.HashMap Expr Expr) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity op 2 then
    let pa ← congrLeaves op proofs e.appFn!.appArg!
    let pb ← congrLeaves op proofs e.appArg!
    return ← mkCongr (← mkCongrArg e.appFn!.appFn! pa) pb
  match proofs.get? e with
  | some p => return p
  | none => mkEqRefl e

/-- Arithmetic operations, whose arguments are reordered and combined by the arithmetic normalizations
    of the solvers (e.g., Z3 sorting the summands and folding the constants). -/
def isArithOp (e : Expr) : Bool :=
  e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HMul.hMul 6 ||
  e.isAppOfArity ``Neg.neg 3

/-- Numeric literals of the interpretation and of Blaster's normal forms. -/
def isNumLit (e : Expr) : Bool :=
  e.isRawNatLit || e.isAppOfArity ``OfNat.ofNat 3 ||
  (e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3) ||
  ((e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1) && e.appArg!.isRawNatLit)

/-- `e` with the occurrences of `t` (structurally equal, i.e., pointer equal on the shared terms of the replay; `t`
    without loose bound variables) replaced by the loose bound variable 0, as `kabstract` without definitional
    unfolding: `kabstract` checks each subterm with the head of `t` for definitional equality (e.g., two minutes for a
    rewrite step over the CEK terms of a validator). -/
def abstractOccurrences (e t : Expr) : MetaM Expr := do
  if t.hasLooseBVars then return ← kabstract e t
  withLocalDeclD `z (← inferType t) fun z =>
    return (e.replace fun s => if s == t then some z else none).abstract #[z]

/-- Proof of `a = a'` under the hypothesis `h : k = t` (resp. `t = k`) where `k` is a literal, when `a` with `t`
    replaced by `k` is definitionally equal to `a'` (e.g., `3 + -2 * x` and `9` under `-3 = x`, Z3's
    simplification of the branches of conditionals under their conditions). -/
def substProof? (h a a' : Expr) : MetaM (Option Expr) := do
  let some (_, l, r) := (← inferType h).eq? | return none
  let (t, k, toK) ← if isNumLit l && !isNumLit r then pure (r, l, ← mkEqSymm h)
    else if isNumLit r && !isNumLit l then pure (l, r, h)
    else return none
  let abst ← abstractOccurrences a t
  if !abst.hasLooseBVars then return none
  let some true ← withBudget? 5000 (withDefault <| isDefEq (abst.instantiate1 k) a') | return none
  let f := mkLambda `z .default (← inferType t) abst
  return some (← mkExpectedTypeHint (← mkCongrArg f toK) (← mkEq a a'))

/-- Proof of the closed decidable proposition `p` by evaluation of its decision procedure, when it holds. -/
def decideTrue? (p : Expr) : MetaM (Option Expr) := do
  if p.hasFVar || p.hasMVar then return none
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) p) catch _ => pure none) | return none
  let some r ← withBudget? 5000 (withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)) | return none
  if !r.isConstOf ``Bool.true then return none
  return some (mkApp3 (mkConst ``of_decide_eq_true) p inst (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)))

/-- Hypotheses of the context passed to the tactics on the differences: arithmetic comparisons and their
    negations (e.g., the conditions of the conditionals enclosing a difference simplified under them). -/
def relevantHyps (hyps : Array Expr) (l r : Expr) : MetaM (Array Expr) := do
  let terms := closedSubterms r (closedSubterms l {})
  hyps.filterM fun h => do
    let t ← inferType h
    -- NOTE: also the conjunctions of comparisons (e.g., the contexts of conjuncts, see `diffEq`)
    let leaves := opLeaves ``And t
    if !leaves.all (fun c => isArithComparison (c.not?.getD c)) then return false
    -- small comparisons, or comparisons of the atoms of the difference (e.g., the condition `7 = x` of a conditional
    -- simplified under it, where `x` is a large term generalized with the difference)
    return sizeLe t (64 * leaves.size) || (arithLeaves t).all terms.contains

/-- Arithmetic and propositional structure, traversed by `arithAtoms`. -/
def isArithHead (e : Expr) : Bool :=
  let ops := #[(``HAdd.hAdd, 6), (``HSub.hSub, 6), (``HMul.hMul, 6), (``HDiv.hDiv, 6), (``HMod.hMod, 6),
    (``Neg.neg, 3), (``LE.le, 4), (``LT.lt, 4), (``GE.ge, 4), (``GT.gt, 4), (``Nat.cast, 3), (``Int.toNat, 1),
    (``Int.natAbs, 1), (``And, 2), (``Or, 2), (``Not, 1), (``Iff, 2), (``ite, 5), (``Int.add, 2), (``Int.mul, 2),
    (``Int.neg, 1), (``Int.sub, 2), (``Nat.add, 2), (``Nat.mul, 2), (``Nat.sub, 2), (``Int.ediv, 2), (``Int.emod, 2),
    (``Nat.div, 2), (``Nat.mod, 2), (``Nat.succ, 1)]
  ops.any (fun (n, k) => e.isAppOfArity n k) ||
  -- Preserve powers when generalizing arithmetic statements: abstract their
  -- bases, rather than replacing `x^2` and `x^3` by unrelated variables.
  (e.isAppOfArity ``HPow.hPow 6 && (e.getArg! 1).isConstOf ``Nat &&
    ((e.getArg! 0).isConstOf ``Int || (e.getArg! 0).isConstOf ``Nat))

/-- Maximal subterms of `e` that are not arithmetic or propositional structure (arithmetic atoms), i.e., the
    terms that linear arithmetic tactics treat as variables. -/
partial def arithAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if isAtomic e || e.hasLooseBVars then
      if let .forallE _ t b _ := e then go t; go b
      return
    if e.isAppOfArity ``Eq 3 then
      go (e.getArg! 1); go (e.getArg! 2); return
    if isArithHead e then
      -- instances and types are not traversed
      let args := e.getAppArgs
      let info ← getFunInfoNArgs e.getAppFn args.size
      for i in [:args.size] do
        if info.paramInfo[i]?.any (·.isExplicit) then go args[i]!
      return
    match e with
    | .forallE _ t b _ => go t; go b
    | .mdata _ b => go b
    | _ =>
      let ty ← whnfR (← inferType e)
      if !(ty.isSort && !ty.isProp) && !ty.isForall && !(← isProof e) && (← isClass? ty).isNone then
        found.modify (·.push e)
  go e
  found.get

/-- `e` with the classical instances of its conditionals (`ite`) replaced by decidable ones when they can be
    synthesized: the value of a conditional does not depend on its instance, and evaluation needs decidable ones. -/
def decidableItes (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun s => do
    if s.isAppOfArity ``ite 5 && (s.getArg! 2).isAppOfArity ``Classical.propDecidable 1 then
      let c := s.getArg! 1
      if let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c) catch _ => pure none) then
        return .done (mkAppN s.getAppFn #[s.getArg! 0, c, inst, s.getArg! 3, s.getArg! 4])
    return .continue)

/-- The proposition `p` with its equalities of propositions as equivalences (decidable). -/
def propEqAsIff (p : Expr) : Expr :=
  match p.eq? with
  | some (ty, a, b) => if ty.isProp then mkApp2 (mkConst ``Iff) a b else p
  | none => p

/-- Whether the closed decision `d` (`decide p`) evaluates to `false`. Inconclusive (e.g., stuck evaluation) is
    `false`.
    NOTE: runtime exceptions (e.g., the heartbeats of the evaluation exhausted) are inconclusive too. -/
def decidesFalse (d : Expr) : MetaM Bool := do
  let s ← saveState
  tryCatchRuntimeEx (do
      let r ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 200 * 1000 }) <| withCurrHeartbeats <|
        withDefault <| whnf d
      return r.isConstOf ``Bool.false)
    fun _ => do s.restore; return false

/-- The decision `decide p` of the proposition `p` (with its conditionals decidable, see `decidableItes`), if `p` has a
    decidable instance. -/
def decision? (p : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  tryCatchRuntimeEx (do
      let p ← decidableItes (propEqAsIff p)
      let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
      return some (mkApp2 (mkConst ``Decidable.decide) p inst))
    fun _ => do s.restore; return none

/-- Whether the closed proposition `p` evaluates to `false` (`decide` by evaluation; equalities of propositions as
    equivalences). Inconclusive (e.g., no decidable instance, stuck evaluation) is `false`. -/
def evalsFalse (p : Expr) : MetaM Bool := do
  let some d ← decision? p | return false
  decidesFalse d

/-- Whether the statement `g := ∀ zs, body` (e.g., a local difference with its common subterms generalized) is false:
    an instance of `body` at small values of its variables (of types `Int`, `Nat`, `Bool` and `Prop`) evaluates to
    `false`. A test (no proof): e.g., `∀ z, (¬0 ≤ z) = (0 ≤ z)`, whose proof attempts by tactics took seconds. -/
def refuted (g : Expr) (maxInstances := 64) : MetaM Bool := do
  if !sizeLe g 3000 || g.hasMVar then return false
  forallTelescope g fun zs body => do
    if zs.size > 4 || body.hasLooseBVars then return false
    let mut domains : Array (Array Expr) := #[]
    for z in zs do
      let t ← whnfR (← inferType z)
      let vals :=
        if t.isConstOf ``Int then #[0, 1, -1, 2, -2, 3].map (fun (i : Int) => toExpr i)
        else if t.isConstOf ``Nat then #[0, 1, 2, 3].map (fun (n : Nat) => toExpr n)
        else if t.isConstOf ``Bool then #[toExpr false, toExpr true]
        else if t.isProp then #[mkConst ``False, mkConst ``True]
        else #[]
      if vals.isEmpty then return false
      domains := domains.push vals
    -- the instances (at most `maxInstances`, the first values of each domain first)
    let mut combos : Array (Array Expr) := #[#[]]
    for d in domains do
      combos := (combos.flatMap fun c => d.map c.push).extract 0 maxInstances
    -- NOTE: the decision of the body is built once (its instances are synthesized with the variables, e.g.,
    -- `Int.decLt`), then instantiated at the values (the synthesis at each instance took a tenth of the replay of a CEK
    -- evaluation); per instance with variables of type `Prop` (e.g., the conditions of conditionals, decidable at
    -- `True` and `False`)
    let props ← zs.anyM fun z => return (← inferType z).isProp
    if let some d ← (if props then pure none else decision? body) then
      for c in combos do
        if ← decidesFalse (d.replaceFVars zs c) then return true
      return false
    for c in combos do
      if ← evalsFalse (body.replaceFVars zs c) then return true
    return false

/-- `x` run in a task (on a dedicated thread) in the empty local context with fresh elaboration and metavariable states
    (see `Core.wrapAsync`), whose final state is discarded: its messages, auxiliary declarations and metavariables are
    lost, i.e., its result is expected to be closed (e.g., the proof of a closed statement, checked by the caller).
    NOTE: the states are fresh such that the objects of the current ones (e.g., the large terms of a replay) are not
    shared with the task, i.e., marked as multi-threaded (their reference counts would be updated atomically, e.g.,
    five times slower replays when sharing the state of a replay with tasks).
    The task is interrupted when `cancelTk?` is set (see `Core.checkSystem`). -/
def runAsync (x : Elab.Term.TermElabM α) (cancelTk? : Option IO.CancelToken := none) :
    Elab.Term.TermElabM (Task (Except Exception α)) := do
  let tctx ← read
  let mctx := { (← readThe Meta.Context) with lctx := {}, localInstances := #[] }
  -- NOTE: the task gets the environment but not the caches, messages, info trees and traces of the Core state (taken by
  -- `Core.wrapAsync`), which would be shared with the task, i.e., copied by their next updates (e.g., after each of the
  -- parallel attempts of a portfolio, see `SmtProof.portfolioParMulti`)
  let saved ← getThe Core.State
  modifyThe Core.State fun s =>
    { s with cache := {}, messages := {}, infoState := {}, traceState := {}, snapshotTasks := #[] }
  let act ← try
      Core.wrapAsync (fun (_ : Unit) => do
        let ((a, _), _) ← (x.run tctx {}).run mctx {}
        return a) cancelTk?
    finally
      modifyThe Core.State fun s =>
        { s with cache := saved.cache, messages := saved.messages, infoState := saved.infoState,
                 traceState := saved.traceState, snapshotTasks := saved.snapshotTasks }
  EIO.asTask (act ()) (prio := .dedicated)

/-- `e` with the constants of the environment that are not in `base` replaced by their values, e.g., the auxiliary
    lemmas of the tactics in a task with its own environment (see `Local.runAsync`), such that the proof can be used in
    the environment `base`. The reserved names (e.g., the splitters and equations of matchers, realized on demand and
    shared between the environments, see `realizeReservedNames`) are kept. -/
partial def inlineNewConstants (base : Environment) (e : Expr) : CoreM Expr := do
  let env ← getEnv
  let rec go (e : Expr) : StateT (Std.HashMap Name (List Name × Expr)) CoreM Expr := do
    let cs := e.getUsedConstants.filter fun c => !base.contains c (skipRealize := true) && !isReservedName base c
    if cs.isEmpty then return e
    for c in cs do
      if (← get).contains c then continue
      let some info := env.find? c | throwError "inlineNewConstants: unknown constant {c}"
      let some v := info.value? (allowOpaque := true) | throwError "inlineNewConstants: {c} has no value"
      let v ← go v
      modify (·.insert c (info.levelParams, v))
    let m ← get
    return e.replace fun s => match s with
      | .const c us => (m.get? c).map fun (ps, v) => v.instantiateLevelParams ps us
      | _ => none
  (go e).run' {}

/-- Realize the reserved names among the constants of `e` that are not in the environment (e.g., the splitters and
    equations of matchers realized in the environment of a task, see `inlineNewConstants`); messages are discarded. -/
def realizeReservedNames (e : Expr) : CoreM Unit := do
  for c in e.getUsedConstants do
    let env ← getEnv
    if env.contains c (skipRealize := true) || !isReservedName env c then continue
    let msgs := (← getThe Core.State).messages
    tryCatchRuntimeEx (executeReservedNameAction c) fun _ => pure ()
    modifyThe Core.State fun s => { s with messages := msgs }

/-- Return `true` if the proof `p` found by a task with its own environment (see `runAsync` and `inlineNewConstants`) is
    usable in the current environment, after the realization of the reserved names it uses (e.g., the splitters of
    matchers, shared between the environments, see `realizeReservedNames`). -/
def usableProof (p : Expr) : CoreM Bool := do
  realizeReservedNames p
  let env ← getEnv
  return p.getUsedConstants.all (env.contains · (skipRealize := true))

/-- The time spent in the tactic portfolios (see `SmtProof.portfolioPar`) and their number of goals, e.g., per step of
    the replay (environment variable `BLASTER_SMTPROOF_TRACE`). -/
initialize portfolioTime : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- Option holding the deadline of the portfolio (monotonic time in ms plus one, `0`: none): no tactic is started after
    it, and a running one is interrupted at it (see `withPortfolioDeadline`, `SmtProof.portfolio` and
    `SmtProof.portfolioParMulti`, whose tasks capture it). An option of the context, i.e., local to the computation
    run by `withPortfolioDeadline`. -/
def portfolioDeadlineKey : Name := `blaster.smtproof.portfolioDeadline

/-- The deadline of the portfolio (see `portfolioDeadlineKey`). -/
def portfolioDeadline : CoreM (Option Nat) := do
  let d := (← getOptions).getNat portfolioDeadlineKey 0
  return if d == 0 then none else some (d - 1)

/-- Run `x` with the portfolio deadline in `ms` milliseconds (or the current one if earlier). -/
def withPortfolioDeadline (ms : Nat) (x : Elab.Term.TermElabM α) : Elab.Term.TermElabM α := do
  let d := (← IO.monoMsNow) + ms
  let d := match ← portfolioDeadline with
    | some s => min s d
    | none => d
  withOptions (fun o => o.setNat portfolioDeadlineKey (d + 1)) x

mutual
/-- Proof of `l = r` by congruence on the common structure of `l` and `r`, proving the remaining
    differences with `prove` (given the equality to prove, returns a proof). At most `budget` calls of
    `prove`. Conjunctions and disjunctions are compared modulo associativity and unit elements (e.g., the
    flattening of n-ary connectives by Z3's rewriter). -/
partial def diffEq (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (l r : Expr)
    (hyps : Array Expr := #[]) : TermElabM (Option Expr) := do
  if l == r then return some (← mkEqRefl l)
  for op in [``And, ``Or] do
    if (l.isAppOfArity op 2 || r.isAppOfArity op 2) && !sameOpShape op l r then
      if let some p ← acEq prove budget op l r hyps then return some p
  -- the difference as a whole, with the relevant hypotheses of the context (`∀ hs, l = r`)
  let whole : TermElabM (Option Expr) := do
    if (← budget.get) == 0 then return none
    budget.modify (· - 1)
    let hs ← relevantHyps hyps l r
    let some p ← prove (← mkForallFVars hs (← mkEq l r)) | return none
    return some (mkAppN p hs)
  -- Z3's rewrite of `ite c a b = k` into `c ∨ b' = k` (resp. `¬c ∧ b' = k`) when `a = k` (resp. `a ≠ k`) under `c`
  if let some p ← iteEq? prove budget l r hyps then return some p
  -- normalized arithmetic: the congruence on the arguments would mostly produce false differences
  if isArithOp l && isArithOp r && sizeLe l 400 && sizeLe r 400 then return ← whole
  -- divisions and modulos of large terms whose arithmetic atoms are common to both sides (generalized by the prover,
  -- e.g., Z3's rewrites of the modulos of CEK terms by their negations)
  let isDivMod (e : Expr) : Bool := e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``HMod.hMod 6
  if isDivMod l && isDivMod r then
    let al ← arithAtoms l
    let ar ← arithAtoms r
    if al.size ≤ 8 && al.all ar.contains && ar.all al.contains then return ← whole
  let fl := l.getAppFn
  let fr := r.getAppFn
  if !l.isApp || !r.isApp || fl != fr || l.getAppNumArgs != r.getAppNumArgs then
    match l, r with
    | .forallE n t b bi, .forallE _ t' b' _ =>
        if (t == t' || (← isDefEq t t')) && (b.hasLooseBVars || b'.hasLooseBVars) && (← isProp l) then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) hyps | return none
            return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] p])
          if r?.isSome then return r?
        else if !b.hasLooseBVars && !b'.hasLooseBVars then
          let some pt ← diffEq prove budget t t' hyps | return ← whole
          let some pb ← diffEq prove budget b b' hyps | return ← whole
          return some (← mkAppM ``implies_congr #[pt, pb])
      | .lam n t b bi, .lam _ t' b' _ =>
        if t == t' || (← isDefEq t t') then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) hyps | return none
            return some (← mkFunExt (← mkLambdaFVars #[x] p))
          if r?.isSome then return r?
      | _, _ => pure ()
    return ← whole
  -- arithmetic comparisons whose operands differ at their heads (e.g., Z3's normal form `x + y ≤ k` of `ite c a b ≤ k`,
  -- or of nested divisions): the comparisons as a whole first, the differences of their operands being often false or
  -- out of reach of the tactics (on CEK evaluations, failing after their time budget while the comparisons are proved)
  if isArithComparison l then
    if (l.getAppArgs.zip r.getAppArgs).any fun (a, b) => a != b && a.getAppFn != b.getAppFn then
      if let some p ← whole then return some p
  -- conditionals (the instance depends on the condition): the branches under the condition (resp. its negation)
  if let some p ← iteCongrCtx? prove budget l r hyps then return some p
  if l.isAppOfArity ``Decidable.decide 2 then
    if let some p ← iteCongr? l r (diffEq prove budget · · hyps) then return some p
  -- conjunctions (resp. disjunctions): the right operands under the left one (resp. its negation), e.g., Z3's
  -- simplifications of the conjuncts implied by the others
  if (l.isAppOfArity ``And 2 && r.isAppOfArity ``And 2) || (l.isAppOfArity ``Or 2 && r.isAppOfArity ``Or 2) then
    let isAnd := l.isAppOfArity ``And 2
    let (a, b, a', b') := (l.appFn!.appArg!, l.appArg!, r.appFn!.appArg!, r.appArg!)
    let some pa ← (if a == a' then some <$> mkEqRefl a else diffEq prove budget a a' hyps) | return ← whole
    let some pb ← withLocalDeclD `h (if isAnd then a else mkNot a) fun h => do
        let some p ← (if b == b' then some <$> mkEqRefl b else diffEq prove budget b b' (hyps.push h)) | return none
        some <$> mkLambdaFVars #[h] p
      | return ← whole
    return some (mkAppN (mkConst (if isAnd then ``and_congr_ctx else ``or_congr_ctx)) #[a, a', b, b', pa, pb])
  let as := l.getAppArgs
  let bs := r.getAppArgs
  let info ← getFunInfoNArgs fl as.size
  let mut pf ← mkEqRefl l
  let mut cur := as
  for i in [:as.size] do
    if as[i]! == bs[i]! then continue
    if let some pi := info.paramInfo[i]? then
      if pi.hasFwdDeps then return ← whole
    let ta ← inferType as[i]!
    if !(← isDefEq ta (← inferType bs[i]!)) then return ← whole
    let some p ← diffEq prove budget as[i]! bs[i]! hyps | return ← whole
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fl (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx p)
    cur := cur.set! i bs[i]!
  return some pf

/-- `ite c x y = ite c' x' y'` (classical instances) from `c = c'`, `c → x = x'` and `¬c → y = y'`: the
    differences of the branches are proved under the condition (resp. its negation), e.g., by substitution of
    the equation of the condition (see `substProof?`). -/
partial def iteCongrCtx? (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (l r : Expr)
    (hyps : Array Expr) : TermElabM (Option Expr) := do
  if !(l.isAppOfArity ``ite 5 && r.isAppOfArity ``ite 5) then return none
  let la := l.getAppArgs
  let ra := r.getAppArgs
  if !(la[2]!.isAppOfArity ``Classical.propDecidable 1 && ra[2]!.isAppOfArity ``Classical.propDecidable 1) then return none
  if la[0]! != ra[0]! then return none
  let (c, c') := (la[1]!, ra[1]!)
  -- negated conditions (e.g., Z3's normal form `ite c y x` of `ite (¬c) x y`): the branches swapped, the difference of
  -- the conditions being false (e.g., `(¬0 ≤ x) = (0 ≤ x)`)
  let u ← getLevel la[0]!
  let swapped (c x y : Expr) : Expr :=
    mkAppN (mkConst ``ite [u]) #[la[0]!, c, mkApp (mkConst ``Classical.propDecidable) c, y, x]
  if c.isAppOfArity ``Not 1 && c.appArg! == c' then
    let some p ← iteCongrCtx? prove budget (swapped c' la[3]! la[4]!) r hyps | return none
    return some (← mkEqTrans (mkAppN (mkConst ``classical_ite_not [u]) #[la[0]!, c', la[3]!, la[4]!]) p)
  if c'.isAppOfArity ``Not 1 && c'.appArg! == c then
    let some p ← iteCongrCtx? prove budget l (swapped c ra[3]! ra[4]!) hyps | return none
    return some (← mkEqTrans p (← mkEqSymm (mkAppN (mkConst ``classical_ite_not [u]) #[la[0]!, c, ra[3]!, ra[4]!])))
  let some pc ← (if c == c' then some <$> mkEqRefl c else diffEq prove budget c c' hyps) | return none
  let branch (cond x x' : Expr) (subst : Bool) : TermElabM (Option Expr) :=
    withLocalDeclD `h cond fun h => do
      let p? ← if x == x' then some <$> mkEqRefl x
        else if subst then do
          match ← substProof? h x x' with
          | some p => pure (some p)
          | none => diffEq prove budget x x' (hyps.push h)
        else diffEq prove budget x x' (hyps.push h)
      match p? with
      | some p => some <$> mkLambdaFVars #[h] p
      | none => pure none
  let some px ← branch c la[3]! ra[3]! true | return none
  let some py ← branch (mkNot c) la[4]! ra[4]! false | return none
  return some (mkAppN (mkConst ``classical_ite_congr_ctx [u]) #[la[0]!, c, c', la[3]!, ra[3]!, la[4]!, ra[4]!, pc, px, py])

/-- `(ite c a b = k) = (c ∨ e)` (resp. `(¬c ∧ e)`) from `c → a = k` (resp. `c → a ≠ k`) and `¬c → (b = k) = e`,
    also for `k = ite c a b` (Z3's rewrite of equalities with conditionals, simplifying the branches under the
    condition). -/
partial def iteEq? (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (l r : Expr)
    (hyps : Array Expr) : TermElabM (Option Expr) := do
  let some (α, x, y) := l.eq? | return none
  let isIte (e : Expr) := e.isAppOfArity ``ite 5 && (e.getArg! 2).isAppOfArity ``Classical.propDecidable 1
  -- `k = ite c a b`: symmetry
  if !isIte x && isIte y then
    let u ← getLevel α
    let some p ← iteEq? prove budget (← mkEq y x) r hyps | return none
    return some (← mkEqTrans (mkApp3 (mkConst ``eq_comm_eq [u]) α x y) p)
  if !isIte x then return none
  let args := x.getAppArgs
  let (c, a, b, k) := (args[1]!, args[3]!, args[4]!, y)
  let u ← getLevel α
  let disj := r.isAppOfArity ``Or 2 && r.appFn!.appArg! == c
  let conj := r.isAppOfArity ``And 2 && r.appFn!.appArg! == mkNot c
  if !disj && !conj then return none
  let e := r.appArg!
  let some ha ← iteHead? prove budget hyps disj c a k | return none
  let some hb ← withLocalDeclD `h (mkNot c) fun h => do
      let some p ← diffEq prove budget (← mkEq b k) e (hyps.push h) | return none
      some <$> mkLambdaFVars #[h] p
    | return none
  let lem := if disj then ``ite_eq_or else ``ite_eq_and
  return some (mkAppN (mkConst lem [u]) #[α, c, a, b, k, e, ha, hb])

/-- `c → a = k` (resp. `c → ¬a = k` when `!disj`): substitution of the equation of `c`, or the difference under
    `c` (resp. `a` evaluated by substitution, then decided, e.g., `2 + x ≠ 3` under `0 = x`). -/
partial def iteHead? (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (hyps : Array Expr)
    (disj : Bool) (c a k : Expr) : TermElabM (Option Expr) :=
  withLocalDeclD `h c fun h => do
    let goal ← if disj then mkEq a k else pure (mkNot (← mkEq a k))
    let p? ← if disj then do
        if let some p ← substProof? h a k then pure (some p) else diffEq prove budget a k (hyps.push h)
      else do
        let some (_, s, t) := (← inferType h).eq? | pure none
        let (tm, lit, toLit) ← if isNumLit s then pure (t, s, ← mkEqSymm h) else pure (s, t, h)
        let abst ← kabstract a tm
        if !abst.hasLooseBVars then pure none else
        let some d ← decideTrue? (mkNot (← mkEq (abst.instantiate1 lit) k)) | pure none
        -- `a = a[lit/tm]` by congruence, then `¬ a[lit/tm] = k`
        let pa ← mkCongrArg (mkLambda `z .default (← inferType tm) abst) toLit
        withLocalDeclD `h' (← mkEq a k) fun h' => do
          let p ← mkLambdaFVars #[h'] (mkApp d (← mkEqTrans (← mkEqSymm pa) h'))
          return some (← mkExpectedTypeHint p goal)
    match p? with
    | some p => some <$> mkLambdaFVars #[h] p
    | none => pure none

/-- A leaf `ite c a b = k` (or `k = ite c a b`) of a tree of `op` applications rewritten by Z3 into the leaves
    `¬c`, `b = k` of a conjunction (resp. `c`, `b = k` of a disjunction) flattened with the tree, where `rs` are
    the leaves of the rewritten tree: `(leaf = (¬c ∧ b = k), ¬c ∧ b = k)` (resp. with `c ∨ b = k`). -/
partial def expandIteEq? (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (hyps : Array Expr)
    (op : Name) (rs : Array Expr) (leaf : Expr) : TermElabM (Option (Expr × Expr)) := do
  let some (α, x, y) := leaf.eq? | return none
  let isIte (e : Expr) := e.isAppOfArity ``ite 5 && (e.getArg! 2).isAppOfArity ``Classical.propDecidable 1
  let u ← getLevel α
  let (i, k, sym?) ← if isIte x then pure (x, y, none)
    else if isIte y then pure (y, x, some (mkApp3 (mkConst ``eq_comm_eq [u]) α x y))
    else return none
  let args := i.getAppArgs
  let (c, a, b) := (args[1]!, args[3]!, args[4]!)
  let disj := op == ``Or
  if !(if disj then rs.contains c else rs.contains (mkNot c)) then return none
  let some ha ← iteHead? prove budget hyps disj c a k | return none
  let bk ← mkEq b k
  let tree := if disj then mkOr c bk else mkAnd (mkNot c) bk
  let hb ← withLocalDeclD `h (mkNot c) fun h => do mkLambdaFVars #[h] (← mkEqRefl bk)
  let p := mkAppN (mkConst (if disj then ``ite_eq_or else ``ite_eq_and) [u]) #[α, c, a, b, k, bk, ha, hb]
  let p ← match sym? with
    | some s => mkEqTrans s p
    | none => pure p
  return some (p, tree)

/-- `l = r` for trees of `op` applications of different shapes: the leaves of `l` (except the unit
    element, and the duplicates) are paired with the leaves of `r` in order and proved equal (`diffEq`),
    then `l` with the leaves of `r` is proved equal to `r` with the leaves generalized (`prove`). -/
partial def acEq (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (op : Name) (l r : Expr)
    (hyps : Array Expr) : TermElabM (Option Expr) := do
  let unit := if op == ``And then ``True else ``False
  let dedup (xs : Array Expr) : Array Expr := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
  let ls := dedup ((opLeaves op l).filter (!·.isConstOf unit))
  let rs := (opLeaves op r).filter (!·.isConstOf unit)
  if ls.size < rs.size then
    -- leaves of `l` rewritten by Z3 into several leaves (see `expandIteEq?`)
    let mut proofs : Std.HashMap Expr Expr := {}
    let mut trees : Std.HashMap Expr Expr := {}
    for x in ls do
      if let some (p, t) ← expandIteEq? prove budget hyps op rs x then
        proofs := proofs.insert x p
        trees := trees.insert x t
    if proofs.isEmpty then return none
    let l' := mapOpLeaves op (fun x => trees.getD x x) l
    let some p ← acEq prove budget op l' r hyps | return none
    return some (← mkEqTrans (← congrLeaves op proofs l) p)
  if ls.size != rs.size || ls.isEmpty then return none
  -- leaves of `l` rewritten into the leaves of `r`
  let mut m : Std.HashMap Expr Expr := {}
  let mut proofs : Std.HashMap Expr Expr := {}
  for (x, y) in ls.zip rs do
    m := m.insert x y
    if x != y then
      let some p ← diffEq prove budget x y hyps | return none
      proofs := proofs.insert x p
  let l' := mapOpLeaves op (fun x => m.getD x x) l
  -- `l = l'` by congruence (the differences are the leaves)
  let p₁ ← if proofs.isEmpty then mkEqRefl l else congrLeaves op proofs l
  -- `l' = r`: associativity, units and duplicates (the leaves are generalized)
  if l' == r then return some p₁
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let hs ← relevantHyps hyps l' r
  let some p₂ ← prove (← mkForallFVars hs (← mkEq l' r)) | return none
  return some (← mkEqTrans p₁ (mkAppN p₂ hs))
end

end Blaster.Reconstruct.SmtProof.Local

namespace Blaster.Reconstruct.SmtProof.Local

/-- Datatype terms of the propositional structure of `e` examined by a theory lemma: the sides of equalities and the
    arguments of testers (`casesOn` or recursors into propositions), through constructor applications, when they are
    not variables. -/
partial def datatypeAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let isInductive (t : Expr) : MetaM Bool := do
    let .const n _ := (← whnfD t).getAppFn | return false
    -- NOTE: arithmetic terms are left to the arithmetic tactics
    if n == ``Int || n == ``Nat then return false
    return (← getEnv).find? n matches some (.inductInfo _)
  let rec term (x : Expr) : MetaM Unit := do
    if (← visited.get).contains x || x.hasLooseBVars || isAtomic x then return
    visited.modify (·.insert x)
    if let .const c _ := x.getAppFn then
      if let some (.ctorInfo info) := (← getEnv).find? c then
        for a in x.getAppArgs.extract info.numParams x.getAppNumArgs do term a
        return
    if ← isInductive (← inferType x) then found.modify (·.push x)
  let rec prop (e : Expr) : MetaM Unit := do
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
      prop e.appFn!.appArg!; prop e.appArg!
    else if e.isAppOfArity ``Not 1 then prop e.appArg!
    else if let .forallE _ t b _ := e then
      if !b.hasLooseBVars then prop t; prop b
    else if e.isAppOfArity ``Eq 3 then
      if (e.getArg! 0).isProp then prop (e.getArg! 1); prop (e.getArg! 2)
      else if ← isInductive (e.getArg! 0) then term (e.getArg! 1); term (e.getArg! 2)
    else if let some m ← matchMatcherApp? e (alsoCasesOn := true) then
      for d in m.discrs do term d
    else if let .const r _ := e.getAppFn then
      if let some (.recInfo info) := (← getEnv).find? r then
        if let some d := e.getAppArgs[info.getMajorIdx]? then term d
  prop e
  found.get

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the datatype terms of `stmt` (see `datatypeAtoms`), e.g., for datatype lemmas
    whose premises relate different terms (`¬ is-nil a → ¬ is-cons b → a = b → False`). -/
def generalizeDatatypeAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← datatypeAtoms stmt
  if ss.isEmpty then return none
  let types ← ss.mapM fun s => do
    let t ← inferType s
    let t' ← whnfD t
    if let .const n _ := t'.getAppFn then
      if (← getEnv).find? n matches some (.inductInfo _) then return t'
    return t
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"d{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the arithmetic atoms of `stmt` (see `arithAtoms`). -/
def generalizeAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← arithAtoms stmt
  if ss.isEmpty then return none
  let types ← ss.mapM inferType
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"a{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

end Blaster.Reconstruct.SmtProof.Local

namespace Blaster.Reconstruct.SmtProof.Local

/-- Propositional structure, traversed by `propAtoms`. -/
def isPropHead (e : Expr) : Bool :=
  e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Not 1 || e.isAppOfArity ``Iff 2 ||
  e.isConstOf ``True || e.isConstOf ``False ||
  (e.isAppOfArity ``Eq 3 && (e.getArg! 0).isProp) || (e.isAppOfArity ``ite 5 && (e.getArg! 0).isProp)

/-- Maximal subterms of `e` that are not propositional structure (propositional atoms). -/
partial def propAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if e.hasLooseBVars then return
    if isPropHead e then
      if e.isAppOfArity ``ite 5 then go (e.getArg! 1); go (e.getArg! 3); go (e.getArg! 4)
      else if e.isAppOfArity ``Eq 3 then go (e.getArg! 1); go (e.getArg! 2)
      else for a in e.getAppArgs do go a
      return
    match e with
    | .forallE _ t b _ => if !b.hasLooseBVars then go t; go b else found.modify (·.push e)
    | .mdata _ b => go b
    | _ => if (← isProp e) then found.modify (·.push e)
  go e
  found.get

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the propositional atoms of `stmt` (see `propAtoms`). -/
def generalizePropAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← propAtoms stmt
  if ss.isEmpty then return none
  let decls := ss.mapIdx fun i _ => (Name.mkSimple s!"p{i}", fun (_ : Array Expr) => pure (mkSort levelZero))
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

end Blaster.Reconstruct.SmtProof.Local
