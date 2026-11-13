import Lean

/-!
# Nonlinear integer arithmetic

The tactic `blaster_nlarith` proves goals of nonlinear integer arithmetic (e.g., the theory lemmas and
rewrites of Z3's nonlinear arithmetic, see `Driver.stepTactics`), in the spirit of Mathlib's `nlinarith`
(Positivstellensatz certificates of degree 2), with `omega` as linear procedure:
 1. the negated goal and the hypotheses are split into cases (see `refute`), each a conjunction of literals over
    `Int` stated as `0 ≤ e`, `0 < e` or `e = 0` (disequalities are split into `<` and `>`); the `if-then-else`
    terms of the literals are split on their condition and replaced by their branches;
 2. facts on the atoms are added (see `closeOrSplit`): `0 ≤ t` for the nonnegative terms (e.g., casts of natural
    numbers and their divisions) and, for the divisions and modulos by non-numeral divisors `y` (whose sign is
    split), `y * (x / y) + x % y = x` and the bounds of `x % y`;
 3. the literals are normalized as polynomials over the atoms (proved by `Lean.Grind.CommRing` normalization,
    evaluated by the kernel), such that `omega` treats the nonlinear monomials as atoms, and each case is closed
    (see `closeLits`) by `omega` on the literals (e.g., Farkas lemmas over nonlinear monomials), then with the
    products of pairs of literals (e.g., `0 ≤ a → 0 ≤ b → 0 ≤ a * b`, and `a = 0 → a * x = 0` for the atoms `x`),
    then splitting on the signs of the atoms of nonlinear monomials.
-/

open Lean Meta Elab Tactic

namespace Blaster.Reconstruct.SmtProof.NlArith

initialize registerTraceClass `blaster.nlarith

theorem div_mod_eq (x y : Int) : y * (x / y) + x % y - x = 0 := Int.sub_eq_zero_of_eq (Int.mul_ediv_add_emod x y)
theorem emod_nonneg_of_pos (x : Int) {y : Int} (h : 0 < y) : 0 ≤ x % y := Int.emod_nonneg x (Int.ne_of_gt h)
theorem emod_nonneg_of_neg (x : Int) {y : Int} (h : y < 0) : 0 ≤ x % y := Int.emod_nonneg x (Int.ne_of_lt h)
theorem emod_lt_of_pos (x : Int) {y : Int} (h : 0 < y) : 0 < y - x % y :=
  Int.sub_pos_of_lt (Int.emod_lt_of_pos x h)
theorem emod_lt_of_neg (x : Int) {y : Int} (h : y < 0) : 0 < -y - x % y := by
  have := Int.emod_lt_of_pos x (Int.neg_pos.mpr h); rw [Int.emod_neg] at this; exact Int.sub_pos_of_lt this
theorem ediv_of_eq_zero (x : Int) {y : Int} (h : y = 0) : x / y = 0 := by subst h; exact Int.ediv_zero x
theorem emod_of_eq_zero (x : Int) {y : Int} (h : y = 0) : x % y - x = 0 := by subst h; simp
theorem eq_zero_or_pos_of_nonneg {a : Int} (h : 0 ≤ a) : a = 0 ∨ 0 < a := by omega
theorem pos_of_ne_zero_of_nonneg {a : Int} (h : 0 ≤ a) (hne : ¬a = 0) : 0 < a := by omega
theorem pos_of_zero_ne_of_nonneg {a : Int} (h : 0 ≤ a) (hne : ¬0 = a) : 0 < a := by omega
theorem emod_nonneg_of_nonneg {a : Int} (h : 0 ≤ a) (b : Int) : 0 ≤ a % b := by
  by_cases hb : b = 0
  · simp [hb, h]
  · exact Int.emod_nonneg a hb
theorem ite_nonneg {c : Prop} [Decidable c] {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite c a b := by
  split <;> assumption
theorem not_eq_zero_of_pos {t : Int} (h : 0 < t) : ¬t = 0 := by omega
theorem not_zero_eq_of_pos {t : Int} (h : 0 < t) : ¬0 = t := by omega
theorem not_eq_zero_of_neg {t : Int} (h : t < 0) : ¬t = 0 := by omega
theorem not_zero_eq_of_neg {t : Int} (h : t < 0) : ¬0 = t := by omega
theorem lt_of_not_le {a b : Int} (h : ¬a ≤ b) : b < a := Int.not_le.mp h
theorem le_of_not_lt {a b : Int} (h : ¬a < b) : b ≤ a := Int.not_lt.mp h
theorem not_iff_of_not_eq {a b : Prop} (h : ¬a = b) : ¬(a ↔ b) := fun h' => h (propext h')
theorem not_of_iff_not {a b : Prop} (h : a ↔ b) (hna : ¬a) : ¬b := fun hb => hna (h.mpr hb)
theorem sub_one_nonneg_of_pos {a : Int} (h : 0 < a) : 0 ≤ a - 1 := by omega
theorem nonneg_of_eq {e q : Int} (h : 0 ≤ e) (heq : e = q) : 0 ≤ q := heq ▸ h
theorem pos_of_eq {e q : Int} (h : 0 < e) (heq : e = q) : 0 < q := heq ▸ h
theorem zero_of_eq {e q : Int} (h : e = 0) (heq : e = q) : q = 0 := heq ▸ h
theorem mul_eq_zero_of_left {a : Int} (h : a = 0) (b : Int) : a * b = 0 := by rw [h, Int.zero_mul]
theorem square_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

open Lean.Grind.CommRing in
/-- Equality of polynomial expressions by normalization (evaluated by the kernel). -/
theorem eq_of_norm (ctx : Context Int) (a b : Lean.Grind.CommRing.Expr)
    (h : a.toPoly_k.beq' b.toPoly_k = true) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, Expr.toPoly_k_eq_toPoly] at h
  rw [← Expr.denote_toPoly, ← Expr.denote_toPoly, h]

theorem of_not_not {a : Prop} (h : ¬¬a) : a := Classical.not_not.mp h
theorem or_not_of_not_and {a b : Prop} (h : ¬(a ∧ b)) : ¬a ∨ ¬b := Classical.not_and_iff_not_or_not.mp h
theorem and_not_of_not_or {a b : Prop} (h : ¬(a ∨ b)) : ¬a ∧ ¬b := not_or.mp h
theorem not_iff_of_not_iff {a b : Prop} (h : ¬(a ↔ b)) : (¬a ↔ b) := Classical.not_iff.mp h
theorem and_not_of_not_imp {a b : Prop} (h : ¬(a → b)) : a ∧ ¬b := not_imp.mp h

/-- Literals: `0 ≤ e`, `0 < e`, `e = 0` (`e : Int`). -/
inductive Kind where
  | nonneg | pos | zero
  deriving BEq, Inhabited

/-- Signs of terms: `0 < t`, `t < 0`, `t = 0`. -/
inductive Sign where
  | pos | neg | zero

/-- A literal `0 ≤ e`, `0 < e` or `e = 0` (see `Kind`). -/
structure Lit where
  kind : Kind
  e : Expr
  /-- proof of the literal -/
  pf : Expr
  deriving Inhabited

/-- The term `e` of the literal `ty` (`0 ≤ e`, `0 < e` or `e = 0`). -/
def litTerm (kind : Kind) (ty : Expr) : Expr := if kind == .zero then ty.appFn!.appArg! else ty.appArg!

/-- State of a case (see `refute`). -/
structure State where
  lits : Array Lit := #[]
  /-- propositions of the processed facts, with their proofs (decided conditions of `if-then-else` terms) -/
  known : Std.HashMap Expr Expr := {}
  /-- signs of the terms (with their proof) given by the literals and the case splits -/
  signs : Std.HashMap Expr (Sign × Expr) := {}
  /-- `if-then-else` terms already split, divisions whose facts were added, terms whose sign was analyzed -/
  done : Std.HashSet Expr := {}

structure Config where
  /-- maximal number of cases (of the propositional structure, `if-then-else` terms and signs of divisors) -/
  maxCases : Nat := 32
  /-- maximal number of products of literals per `omega` call -/
  maxProducts : Nat := 400
  /-- maximal number of nested sign case splits on the atoms of nonlinear monomials -/
  signSplits : Nat := 2
  /-- heartbeats (in thousands) of each `omega` call -/
  heartbeats : Nat := 30000
  /-- maximal number of `omega` calls -/
  maxCalls : Nat := 48

/-- Configuration and counters of a run. -/
structure Ctx where
  cfg : Config := {}
  /-- number of cases -/
  cases : IO.Ref Nat
  /-- number of `omega` calls -/
  calls : IO.Ref Nat

/-- Numerals (e.g., `2`, `-1`, `↑2`). -/
partial def isNumeral (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 || e.isRawNatLit ||
  (e.isAppOfArity ``Neg.neg 3 && isNumeral e.appArg!) ||
  ((e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Nat.cast 3) && isNumeral e.appArg!)

/-- Whether `e` is the type `Int`. -/
def isInt (e : Expr) : Bool := e.isConstOf ``Int

/-- Whether `e` is the numeral `0`. -/
def isZero (e : Expr) : MetaM Bool := return (← getIntValue? e) == some 0

/-- Divisions and modulos (`x / y`, `x % y`). -/
def isDivOrMod (e : Expr) : Bool := e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``HMod.hMod 6

/-- Nonlinear terms: products of non-numerals, powers, divisions and modulos by non-numerals (over `Int`). -/
def isNonlinear (e : Expr) : Bool :=
  (e.isAppOfArity ``HMul.hMul 6 && isInt (e.getArg! 0) && !isNumeral (e.getArg! 4) && !isNumeral (e.getArg! 5)) ||
  (e.isAppOfArity ``HPow.hPow 6 && isInt (e.getArg! 0) && (e.getArg! 1).isConstOf ``Nat) ||
  (isDivOrMod e && isInt (e.getArg! 0) && !isNumeral (e.getArg! 5))

/-- Whether `e` contains a nonlinear term (see `isNonlinear`). -/
def hasNonlinear (e : Expr) : Bool := (e.find? fun s => isNonlinear s && !s.hasLooseBVars).isSome

/-- Subterms of `e` (without loose bound variables) satisfying `p`, outermost first. -/
def subterms (e : Expr) (p : Expr → Bool) : Array Expr := Id.run do
  let mut acc := #[]
  let mut stack := #[e]
  let mut seen : Std.HashSet Expr := {}
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if seen.contains s then continue
    seen := seen.insert s
    if !s.hasLooseBVars && p s then acc := acc.push s
    match s with
    | .app f a => stack := stack.push a |>.push f
    | .mdata _ b => stack := stack.push b
    | _ => pure ()
  return acc

/-- The free variables of `e` and of their types, in the order of the local context. -/
def closingFVars (e : Expr) : MetaM (Array Expr) := do
  let mut todo := (collectFVars {} e).fvarIds
  let mut seen : FVarIdSet := {}
  let mut decls := #[]
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if seen.contains f then continue
    seen := seen.insert f
    let d ← f.getDecl
    decls := decls.push d
    todo := todo ++ (collectFVars {} d.type).fvarIds
  return (decls.qsort (·.index < ·.index)).map (·.toExpr)

/-! ## Normalization of polynomials -/

/-- Polynomials over atoms (indices): monomials (sorted lists of atoms) with nonzero coefficients, sorted. -/
abbrev Poly := Array (List Nat × Int)

/-- Order of the monomials: by degree, then lexicographically. -/
def monLt (m₁ m₂ : List Nat) : Bool :=
  m₁.length < m₂.length || (m₁.length == m₂.length && compare m₁ m₂ == .lt)

/-- The polynomial of a sum of monomials (coefficients of equal monomials added, zero ones removed, sorted by
    `monLt`). -/
def Poly.ofArray (xs : Array (List Nat × Int)) : Poly :=
  let m : Std.HashMap (List Nat) Int := xs.foldl (fun m (k, c) => m.insert k (m.getD k 0 + c)) {}
  (m.toArray.filter (·.2 != 0)).qsort fun a b => monLt a.1 b.1

def Poly.const (k : Int) : Poly := Poly.ofArray #[([], k)]
def Poly.add (p q : Poly) : Poly := Poly.ofArray (p ++ q)
def Poly.scale (k : Int) (p : Poly) : Poly := Poly.ofArray (p.map fun (m, c) => (m, k * c))
def Poly.mul (p q : Poly) : Poly :=
  Poly.ofArray (p.flatMap fun (m, c) => q.map fun (m', c') => ((m ++ m').mergeSort, c * c'))

def Poly.pow (p : Poly) (n : Nat) : Poly :=
  (List.range n).foldl (fun acc _ => acc.mul p) (Poly.const 1)

abbrev RExpr := Lean.Grind.CommRing.Expr

/-- The term of a ring expression. -/
def rexprToExpr : RExpr → Expr
  | .num k => mkApp (mkConst ``Lean.Grind.CommRing.Expr.num) (ToExpr.toExpr k)
  | .var x => mkApp (mkConst ``Lean.Grind.CommRing.Expr.var) (mkNatLit x)
  | .add a b => mkApp2 (mkConst ``Lean.Grind.CommRing.Expr.add) (rexprToExpr a) (rexprToExpr b)
  | .sub a b => mkApp2 (mkConst ``Lean.Grind.CommRing.Expr.sub) (rexprToExpr a) (rexprToExpr b)
  | .mul a b => mkApp2 (mkConst ``Lean.Grind.CommRing.Expr.mul) (rexprToExpr a) (rexprToExpr b)
  | .neg a => mkApp (mkConst ``Lean.Grind.CommRing.Expr.neg) (rexprToExpr a)
  | .pow a n => mkApp2 (mkConst ``Lean.Grind.CommRing.Expr.pow) (rexprToExpr a) (mkNatLit n)
  | _ => mkApp (mkConst ``Lean.Grind.CommRing.Expr.num) (ToExpr.toExpr (0 : Int))

/-- Atoms of the polynomials of a case. -/
structure Atoms where
  atoms : Array Expr := #[]
  idx : Std.HashMap Expr Nat := {}

abbrev NormM := StateT Atoms MetaM

/-- The index of the atom `e` (added when new). -/
def atomIdx (e : Expr) : NormM Nat := do
  let s ← get
  if let some i := s.idx.get? e then return i
  set { atoms := s.atoms.push e, idx := s.idx.insert e s.atoms.size : Atoms }
  return s.atoms.size

/-- The polynomial of an `Int` term, and the term as a ring expression (whose denotation is the term). -/
partial def reify (e : Expr) : NormM (Poly × RExpr) := do
  if let some k ← getIntValue? e then return (Poly.const k, .num k)
  let bin (a b : Expr) (k : Poly → Poly → Poly) (r : RExpr → RExpr → RExpr) : NormM (Poly × RExpr) := do
    let (pa, ra) ← reify a
    let (pb, rb) ← reify b
    return (k pa pb, r ra rb)
  match_expr e with
  | HAdd.hAdd α β γ _ a b => if isInt α && isInt β && isInt γ then bin a b Poly.add .add else atom
  | HSub.hSub α β γ _ a b =>
      if isInt α && isInt β && isInt γ then bin a b (fun p q => p.add (q.scale (-1))) .sub else atom
  | HMul.hMul α β γ _ a b => if isInt α && isInt β && isInt γ then bin a b Poly.mul .mul else atom
  | Neg.neg α _ a =>
      if isInt α then do let (pa, ra) ← reify a; return (pa.scale (-1), .neg ra) else atom
  | HPow.hPow α β γ _ a n => do
      if !(isInt α && β.isConstOf ``Nat && isInt γ) then return ← atom
      let some k ← getNatValue? (← whnf n) | return ← atom
      -- Larger or symbolic powers stay atoms, avoiding unbounded polynomial
      -- expansion. The certificate retains the power and is checked by the kernel.
      if k > 8 then return ← atom
      let (pa, ra) ← reify a
      return (pa.pow k, .pow ra k)
  | _ => atom
where
  atom : NormM (Poly × RExpr) := do
    let i ← atomIdx e
    return (#[([i], 1)], .var i)

/-- The canonical term of a polynomial (`c₀ + c₁ * m₁ + ...`, monomials as left-nested products of atoms), and
    the term as a ring expression. -/
def Poly.toExpr (atoms : Array Expr) (p : Poly) : Expr × RExpr :=
  let mon (m : List Nat) : Expr × RExpr := match m with
    | [] => (mkIntLit 1, .num 1)
    | a :: rest => rest.foldl (fun (e, r) b => (mkIntMul e atoms[b]!, .mul r (.var b))) (atoms[a]!, .var a)
  let terms := p.map fun (m, c) =>
    if m.isEmpty then (mkIntLit c, (.num c : RExpr))
    else
      let (e, r) := mon m
      if c == 1 then (e, r) else (mkIntMul (mkIntLit c) e, .mul (.num c) r)
  if h : 0 < terms.size then
    (terms.extract 1 terms.size).foldl (fun (e, r) (e', r') => (mkIntAdd e e', .add r r')) terms[0]
  else (mkIntLit 0, .num 0)

/-- The context of the ring expressions over the atoms `atoms` (see `eq_of_norm`). -/
def ringContext (atoms : Array Expr) : MetaM Expr :=
  if h : 0 < atoms.size then (RArray.ofArray atoms h).toExpr (mkConst ``Int) id
  else pure (mkApp2 (mkConst ``RArray.leaf [levelZero]) (mkConst ``Int) (mkIntLit 0))

/-- A normalized literal: its polynomial, canonical term, and proof. -/
structure NLit where
  kind : Kind
  poly : Poly
  e : Expr
  r : RExpr
  pf : Expr
  deriving Inhabited

/-- Normalize the literal `0 ≤ e` / `0 < e` / `e = 0` (`r` is the ring expression of `e`). -/
def normalize (ctx : Expr) (atoms : Array Expr) (kind : Kind) (p : Poly) (e : Expr) (r : RExpr) (pf : Expr) :
    MetaM NLit := do
  let (q, rq) := p.toExpr atoms
  if q == e then return { kind, poly := p, e, r, pf }
  let refl := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
  let heq ← mkExpectedTypeHint (mkApp4 (mkConst ``eq_of_norm) ctx (rexprToExpr r) (rexprToExpr rq) refl) (← mkEq e q)
  let thm := match kind with | .nonneg => ``nonneg_of_eq | .pos => ``pos_of_eq | .zero => ``zero_of_eq
  return { kind, poly := p, e := q, r := rq, pf := mkApp4 (mkConst thm) e q pf heq }

/-- Products of the pairs of inequalities (including squares) and of the equalities with the atoms, with the
    number of their nonlinear monomials not occurring in the literals (which other products must cancel). The
    strict inequalities `0 < e` are multiplied as `0 ≤ e - 1` (e.g., `0 < a → 0 < b → 0 ≤ (a - 1) * (b - 1)`). -/
def products (ctx : Expr) (atoms : Array Expr) (lits : Array NLit) : Array (Nat × MetaM NLit) := Id.run do
  let ineqs := lits.filterMap fun l => match l.kind with
    | .zero => none
    | .nonneg => some (l.poly, l.e, l.r, l.pf)
    | .pos => some (l.poly.add (Poly.const (-1)), mkIntSub l.e (mkIntLit 1), .sub l.r (.num 1),
                    mkApp2 (mkConst ``sub_one_nonneg_of_pos) l.e l.pf)
  let mut target : Std.HashSet (List Nat) := {}
  for l in lits do
    for (m, _) in l.poly do
      if m.length ≥ 2 then target := target.insert m
  let new (p : Poly) : Array (List Nat) := (p.filter fun (m, _) => m.length ≥ 2 && !target.contains m).map (·.1)
  let mut acc : Array (Array (List Nat) × MetaM NLit) := #[]
  for i in [:ineqs.size] do
    for j in [i:ineqs.size] do
      let (pa, ea, ra, ha) := ineqs[i]!
      let (pb, eb, rb, hb) := ineqs[j]!
      let p := pa.mul pb
      acc := acc.push (new p, normalize ctx atoms .nonneg p (mkIntMul ea eb) (.mul ra rb)
        (mkApp4 (mkConst ``Int.mul_nonneg) ea eb ha hb))
  for a in lits do
    if a.kind != .zero then continue
    for h : i in [:atoms.size] do
      let x := atoms[i]
      let p := a.poly.mul #[([i], 1)]
      acc := acc.push (new p, normalize ctx atoms .zero p (mkIntMul a.e x) (.mul a.r (.var i))
        (mkApp3 (mkConst ``mul_eq_zero_of_left) a.e a.pf x))
  -- NOTE: the products with a new monomial occurring in no other product can't be part of a certificate (the
  -- monomial can't be canceled)
  let mut changed := true
  while changed do
    let mut count : Std.HashMap (List Nat) Nat := {}
    for (ms, _) in acc do
      for m in ms do count := count.insert m (count.getD m 0 + 1)
    let acc' := acc.filter fun (ms, _) => ms.all (count.getD · 0 ≥ 2)
    changed := acc'.size < acc.size
    acc := acc'
  return acc.map fun (ms, p) => (ms.size, p)

/-- The proofs of the literals `ls`, without duplicate facts (e.g., squares of opposite literals). -/
def dedupFacts (ls : Array NLit) : MetaM (Array Expr) := do
  let mut seen : Std.HashSet Expr := {}
  let mut hs := #[]
  for l in ls do
    let t ← inferType l.pf
    if seen.contains t then continue
    seen := seen.insert t
    hs := hs.push l.pf
  return hs

/-- `False` from the normalized facts `hs` of a case (over the atoms `atoms`), by `omega` on the statement
    closed over the atoms (as variables, such that `omega` doesn't compare the atoms up to definitional
    equality). The facts not used by the proof are dropped (e.g., unused products, whose normalization proofs are
    checked by the kernel). -/
def closeCase (ctx : Ctx) (atoms : Array Expr) (hs : Array Expr) : TacticM Expr := do
  if (← ctx.calls.modifyGet fun n => (n + 1, n + 1)) > ctx.cfg.maxCalls then
    throwError "blaster_nlarith: too many omega calls"
  let types ← hs.mapM fun h => do instantiateMVars (← inferType h)
  -- NOTE: the atoms interpreted by `omega` are kept (e.g., casts, divisions by numerals)
  let atoms := atoms.filter fun a => !(a.isAppOfArity ``Nat.cast 3 || a.isAppOfArity ``Int.toNat 1 ||
    a.isAppOfArity ``Int.natAbs 1 || a.isAppOfArity ``Min.min 4 || a.isAppOfArity ``Max.max 4 ||
    (isDivOrMod a && isNumeral (a.getArg! 5)))
  let idx : Std.HashMap Expr Nat := atoms.zipIdx.foldl (fun m (a, i) => m.insert a i) {}
  let decls := atoms.mapIdx fun i _ => (Name.mkSimple s!"a{i}", fun (_ : Array Expr) => pure (mkConst ``Int))
  let (fvs, g) ← withLocalDeclsD decls fun vs => do
    -- NOTE: the facts are canonical polynomials, whose atoms are replaced top-down
    let types := types.map fun t => t.replace fun s => (idx.get? s).map (vs[·]!)
    let body ← mkForallFVars vs (types.foldr (fun t acc => mkForall `h .default t acc) (mkConst ``False))
    let fvs ← closingFVars body
    return (fvs, ← mkForallFVars fvs body)
  if g.hasFVar then throwError "blaster_nlarith: case depends on local definitions"
  let atoms := fvs ++ atoms
  let mvar ← withLCtx {} {} (mkFreshExprMVar g)
  let t0 ← IO.monoMsNow
  let maxHeartbeats := ctx.cfg.heartbeats * 1000
  let gs ← tryCatchRuntimeEx
      (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats }) <|
        Tactic.run mvar.mvarId! (evalTactic (← `(tactic| (intros; omega)))))
      fun ex => do
        trace[blaster.nlarith] "omega failed on {hs.size} facts ({(← IO.monoMsNow) - t0} ms)"
        throw ex
  trace[blaster.nlarith] "omega succeeded on {hs.size} facts ({(← IO.monoMsNow) - t0} ms)"
  if !gs.isEmpty then throwError "blaster_nlarith: omega failed"
  let p ← instantiateMVars mvar
  withLCtx {} {} <| lambdaBoundedTelescope p (atoms.size + hs.size) fun xs b => do
    if xs.size != atoms.size + hs.size then return mkAppN p (atoms ++ hs)
    let used := (List.range hs.size).toArray.filter fun i => b.containsFVar xs[atoms.size + i]!.fvarId!
    let p' ← mkLambdaFVars (xs.extract 0 atoms.size ++ used.map (xs[atoms.size + ·]!)) b
    return mkAppN p' (atoms ++ used.map (hs[·]!))

/-- Proof of `0 ≤ e` for the terms built from casts of natural numbers, nonnegative numerals, sums, products,
    divisions, modulos and `if-then-else`. -/
partial def nonnegProof? (e : Expr) : MetaM (Option Expr) := do
  if let some k ← getIntValue? e then
    if k < 0 then return none
    return some (← mkDecideProof (mkIntLE (mkIntLit 0) e))
  let bin (thm : Name) (a b : Expr) : MetaM (Option Expr) := do
    let some ha ← nonnegProof? a | return none
    let some hb ← nonnegProof? b | return none
    return some (← mkAppM thm #[ha, hb])
  match_expr e with
  | Nat.cast α _ n =>
      if !isInt α then return none
      return some (← mkExpectedTypeHint (mkApp (mkConst ``Int.natCast_nonneg) n) (mkIntLE (mkIntLit 0) e))
  | HAdd.hAdd α _ _ _ a b => if isInt α then bin ``Int.add_nonneg a b else return none
  | HMul.hMul α _ _ _ a b => if isInt α then bin ``Int.mul_nonneg a b else return none
  | HDiv.hDiv α _ _ _ a b => if isInt α then bin ``Int.ediv_nonneg a b else return none
  | HMod.hMod α _ _ _ a b =>
      if !isInt α then return none
      let some ha ← nonnegProof? a | return none
      return some (← mkAppM ``emod_nonneg_of_nonneg #[ha, b])
  | ite α c inst a b =>
      if !isInt α then return none
      let some ha ← nonnegProof? a | return none
      let some hb ← nonnegProof? b | return none
      return some (mkAppN (mkConst ``ite_nonneg) #[c, inst, a, b, ha, hb])
  | _ => return none

/-- Literal of the comparison `a ≤ b` (`nonneg`), `a < b` (`pos`) or `a = b` (`zero`) proved by `h`, recording
    the signs of the terms compared with `0`. -/
def addLit (st : State) (kind : Kind) (a b h : Expr) : MetaM State := do
  -- the literal, and the sign of a term: `0 < y`, `y < 0` or `y = 0`
  let (pf, sign?) ← match kind with
    | .nonneg => if ← isZero a then pure (h, none) else pure (← mkAppM ``Int.sub_nonneg_of_le #[h], none)
    | .pos =>
        if ← isZero a then pure (h, some (b, Sign.pos, h))
        else if ← isZero b then pure (← mkAppM ``Int.sub_pos_of_lt #[h], some (a, .neg, h))
        else pure (← mkAppM ``Int.sub_pos_of_lt #[h], none)
    | .zero =>
        if ← isZero b then pure (h, some (a, .zero, h))
        else if ← isZero a then do let h' ← mkEqSymm h; pure (h', some (b, .zero, h'))
        else pure (← mkAppM ``Int.sub_eq_zero_of_eq #[h], none)
  let ty ← instantiateMVars (← inferType pf)
  let mut st := { st with lits := st.lits.push { kind, e := litTerm kind ty, pf } }
  if let some (y, sign, hs) := sign? then
    if !st.signs.contains y then st := { st with signs := st.signs.insert y (sign, hs) }
  return st

/-- Count a new case. -/
def newCase (ctx : Ctx) : MetaM Unit := do
  let n ← ctx.cases.modifyGet fun n => (n + 1, n + 1)
  if n > ctx.cfg.maxCases then throwError "blaster_nlarith: too many cases"

/-- Case analysis on `h : a ∨ b`. -/
def orElim (h : Expr) (ka kb : Expr → TacticM Expr) : TacticM Expr := do
  let t ← whnfR (← instantiateMVars (← inferType h))
  let some (a, b) := t.app2? ``Or | throwError "blaster_nlarith: not a disjunction {t}"
  let pa ← withLocalDeclD `h a fun x => do mkLambdaFVars #[x] (← ka x)
  let pb ← withLocalDeclD `h b fun x => do mkLambdaFVars #[x] (← kb x)
  return mkApp6 (mkConst ``Or.elim) a b (mkConst ``False) h pa pb

/-- Rewrite the literal `l` with `heq : t = v`. -/
def rewriteLit (t v heq : Expr) (l : Lit) : MetaM Lit := do
  let ty ← instantiateMVars (← inferType l.pf)
  let abst ← kabstract ty t
  if !abst.hasLooseBVars then return l
  let motive := mkLambda `t .default (mkConst ``Int) abst
  let pf := mkApp6 (mkConst ``Eq.ndrec [levelZero, levelOne]) (mkConst ``Int) t motive l.pf v heq
  return { l with e := litTerm l.kind (abst.instantiate1 v), pf }

/-- `False` from the literals of a case: the literals are normalized and the case is closed by `omega` (nonlinear
    monomials are atoms), first by linear reasoning (e.g., Farkas lemmas over nonlinear monomials, when `linear`),
    then with the products of pairs of literals, then splitting on the sign of an atom of the nonlinear monomials
    (at most `splits` nested splits, on atoms not in `split`). -/
partial def closeLits (ctx : Ctx) (lits : Array Lit) (splits : Nat)
    (split : Array Expr := #[]) (linear := true) : TacticM Expr := do
  let (rs, st) ← (lits.mapM fun l => reify l.e).run {}
  let atoms := st.atoms
  let rctx ← ringContext atoms
  let nlits ← (lits.zip rs).mapM fun (l, (p, r)) => normalize rctx atoms l.kind p l.e r l.pf
  -- NOTE: runtime exceptions (heartbeats of `omega`) are caught
  let attempt (x : TacticM Expr) (k : TacticM Expr) : TacticM Expr := tryCatchRuntimeEx x fun ex => do
    trace[blaster.nlarith] "failed: {ex.toMessageData}"
    k
  -- products by increasing number of new monomials (`omega` is slow on many facts): at most `maxProducts` products
  -- introducing no new monomial, then at most one, two, and four new monomials
  let withProducts : TacticM Expr := do
    -- Nonnegative pairs already occurring as factors of nonlinear monomials
    -- are useful multipliers: `(2-x)*x² ≥ 0` bounds a cube, and `(x-6)*y*z ≥ 0`
    -- bounds a product of three positive factors. This avoids generating an
    -- arbitrary second round of products of all inequalities.
    let mut seeds := nlits
    let mut pairs : Std.HashSet (Nat × Nat) := {}
    for l in nlits do
      for (m, _) in l.poly do
        let m := m.toArray
        for i in [:m.size] do
          for j in [i + 1:m.size] do
            if m[i]! == m[j]! || m.size ≥ 3 then pairs := pairs.insert (m[i]!, m[j]!)
    let nonnegAtom (a : Expr) : MetaM (Option Expr) := do
      if let some p ← nonnegProof? a then return some p
      for l in lits do
        if l.e != a then continue
        if l.kind == .nonneg then return some l.pf
        if l.kind == .pos then return some (← mkAppM ``Int.le_of_lt #[l.pf])
      return none
    -- Stable order, since candidate products are later truncated to a budget.
    for (i, j) in pairs.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) do
      let (a, b) := (atoms[i]!, atoms[j]!)
      let pf? ← if i == j then pure (some (mkApp (mkConst ``square_nonneg) a)) else do
        let some ha ← nonnegAtom a | pure none
        let some hb ← nonnegAtom b | pure none
        pure (some (mkApp4 (mkConst ``Int.mul_nonneg) a b ha hb))
      let some pf := pf? | continue
      seeds := seeds.push (← normalize rctx atoms .nonneg (Poly.ofArray #[([i, j], 1)]) (mkIntMul a b)
        (.mul (.var i) (.var j)) pf)
    let cands := (products rctx atoms seeds).toList.mergeSort (fun a b => a.1 ≤ b.1) |>.toArray
    let mut built : Array NLit := #[]
    let mut prev := 0
    let mut last : Option Exception := none
    for k in [0, 1, 2, 4] do
      let n := min ctx.cfg.maxProducts (cands.findIdx? (·.1 > k) |>.getD cands.size)
      if n ≤ prev then continue
      for c in cands.extract built.size n do built := built.push (← c.2)
      prev := n
      try return ← closeCase ctx atoms (← dedupFacts (seeds ++ built))
      catch ex => last := some ex
    throw (last.getD (.error .missing "blaster_nlarith: no products"))
  let withSigns : TacticM Expr := do
    -- atoms of nonlinear monomials not split yet, those whose sign is not bounded by a literal first (then the
    -- nonnegative ones, e.g., `↑x / ↑y`, then the casts of natural numbers)
    let bounded (i : Nat) : Bool := nlits.any fun l => l.poly.all (·.1.all (· == i)) && l.poly.any (·.1 == [i])
    let cands := (List.range atoms.size).filter fun i =>
      nlits.any (·.poly.any fun (m, _) => m.length ≥ 2 && m.contains i) && !split.contains atoms[i]!
    let rank (i : Nat) : Nat :=
      if atoms[i]!.isAppOfArity ``Nat.cast 3 then 2 else if bounded i then 1 else 0
    let some i := (cands.toArray.qsort fun i j => rank i < rank j)[0]? | throwError "blaster_nlarith: failed"
    let a := atoms[i]!
    let zero := mkIntLit 0
    let next (lits : Array Lit) : TacticM Expr := closeLits ctx lits (splits - 1) (split.push a) false
    newCase ctx
    -- `a < 0` (unless `0 ≤ a`), `a = 0` (`a` replaced by `0` in the literals), `0 < a`
    let zeroOrPos (h : Expr) : TacticM Expr :=
      orElim h (fun h => do next (← lits.mapM fun l => rewriteLit a zero h l))
        (fun h => do next (← addLit { lits } .pos zero a h).lits)
    if let some ha ← nonnegProof? a then return ← zeroOrPos (mkApp2 (mkConst ``eq_zero_or_pos_of_nonneg) a ha)
    orElim (← mkAppM ``Int.lt_trichotomy #[a, zero]) (fun h => do next (← addLit { lits } .pos a zero h).lits)
      zeroOrPos
  let nonlinear : TacticM Expr :=
    attempt withProducts (if splits > 0 then withSigns else throwError "blaster_nlarith: failed")
  if linear then attempt (closeCase ctx atoms (← dedupFacts nlits)) nonlinear else nonlinear

mutual

/-- Proof of `False` from the facts `todo` and the state `st` (see the module documentation). -/
partial def refute (ctx : Ctx) (todo : List Expr) (st : State) : TacticM Expr := do
  match todo with
  | [] => closeOrSplit ctx st
  | h :: rest =>
    let t₀ ← instantiateMVars (← inferType h)
    let t ← whnfR t₀
    let st := { st with known := st.known.insert t₀ h |>.insert t h }
    let next (todo : List Expr) (st := st) : TacticM Expr := refute ctx todo st
    let em (a : Expr) (ha hna : Expr → List Expr) : TacticM Expr := do
      newCase ctx
      orElim (mkApp (mkConst ``Classical.em) a) (fun x => next (ha x)) (fun x => next (hna x))
    -- other facts: propositional conflicts only
    let other : TacticM Expr := do
      if let some hn := st.known.get? (mkNot t₀) then return mkApp hn h
      if let some s := t₀.not? then
        if let some hs := st.known.get? s then return mkApp h hs
      next rest
    match_expr t with
    | False => return h
    | True => next rest
    | And a b => next (mkApp3 (mkConst ``And.left) a b h :: mkApp3 (mkConst ``And.right) a b h :: rest)
    | Or _ _ => newCase ctx; orElim h (fun x => next (x :: rest)) (fun x => next (x :: rest))
    | Iff a b => em a (fun x => x :: mkApp4 (mkConst ``Iff.mp) a b h x :: rest)
                      (fun x => x :: mkApp4 (mkConst ``not_of_iff_not) a b h x :: rest)
    | Eq α a b =>
        if α.isProp then next (mkApp3 (mkConst ``iff_of_eq) a b h :: rest)
        else if isInt α then next rest (← addLit st .zero a b h)
        else other
    | LE.le α _ a b => if isInt α then next rest (← addLit st .nonneg a b h) else other
    | LT.lt α _ a b => if isInt α then next rest (← addLit st .pos a b h) else other
    | Not p =>
        let p ← whnfR p
        let push (thm : Name) : TacticM Expr := do next ((← mkAppM thm #[h]) :: rest)
        match_expr p with
        | False => next rest
        | True => return mkApp h (mkConst ``True.intro)
        | Not _ => push ``of_not_not
        | And _ _ => push ``or_not_of_not_and
        | Or _ _ => push ``and_not_of_not_or
        | Iff _ _ => push ``not_iff_of_not_iff
        | Eq α _ _ =>
            if α.isProp then push ``not_iff_of_not_eq
            else if isInt α then
              -- `t ≠ 0` for a nonnegative term `t`: `0 < t`
              let a := p.appFn!.appArg!
              let b := p.appArg!
              if ← isZero b then
                if let some ha ← nonnegProof? a then
                  return ← next (mkApp3 (mkConst ``pos_of_ne_zero_of_nonneg) a ha h :: rest)
              if ← isZero a then
                if let some hb ← nonnegProof? b then
                  return ← next (mkApp3 (mkConst ``pos_of_zero_ne_of_nonneg) b hb h :: rest)
              push ``Int.lt_or_gt_of_ne
            else other
        | LE.le α _ _ _ => if isInt α then push ``lt_of_not_le else other
        | LT.lt α _ _ _ => if isInt α then push ``le_of_not_lt else other
        -- NOTE: by pattern matching (the nested action `← isProp p.bindingDomain!` would be evaluated before the guard)
        | _ => match p with
          | .forallE _ d b _ => if !b.hasLooseBVars && (← isProp d) then push ``and_not_of_not_imp else other
          | _ => other
    | _ =>
        match t with
        | .forallE _ d b _ =>
          if !b.hasLooseBVars && (← isProp d) then em d (fun x => mkApp h x :: rest) (· :: rest) else other
        | _ => other

/-- Case without pending facts: split the next `if-then-else` term or divisor sign, add the facts on the divisions,
    modulos and nonnegative terms, then close the case (see `closeLits`). -/
partial def closeOrSplit (ctx : Ctx) (st : State) : TacticM Expr := do
  let isDivMod (s : Expr) := isDivOrMod s && isNonlinear s
  let terms := st.lits.foldl (fun acc l => acc ++ subterms l.e fun s =>
    (s.isAppOfArity ``ite 5 && isInt (s.getArg! 0)) || isDivMod s ||
    (s.isAppOfArity ``Nat.cast 3 && isInt (s.getArg! 0))) #[]
  -- `if-then-else` terms: case analysis on the condition (unless it is decided)
  if let some s := terms.find? fun s => s.isAppOfArity ``ite 5 && !st.done.contains s then
    let #[α, c, inst, a, b] := s.getAppArgs | unreachable!
    let st := { st with done := st.done.insert s }
    -- the term is replaced by the branch in the literals (fewer atoms)
    let branch (hc : Expr) (thm : Name) (v : Expr) : TacticM Expr := do
      let heq := mkAppN (mkConst thm [levelOne]) #[c, inst, hc, α, a, b]
      refute ctx [hc] { st with lits := ← st.lits.mapM fun l => rewriteLit s v heq l }
    if let some hc := st.known.get? c then return ← branch hc ``if_pos a
    if let some hc := st.known.get? (mkNot c) then return ← branch hc ``if_neg b
    -- `t = 0` (or `0 = t`) for a term `t` of known sign
    if let some (t, zeroLeft) ← isZeroEq? c then
      if let some (sign, h) := st.signs.get? t then
        let ne (thm₁ thm₂ : Name) := mkApp2 (mkConst (if zeroLeft then thm₁ else thm₂)) t h
        match sign with
        | .zero => return ← branch (← if zeroLeft then mkEqSymm h else pure h) ``if_pos a
        | .pos => return ← branch (ne ``not_zero_eq_of_pos ``not_eq_zero_of_pos) ``if_neg b
        | .neg => return ← branch (ne ``not_zero_eq_of_neg ``not_eq_zero_of_neg) ``if_neg b
    newCase ctx
    return ← orElim (mkApp (mkConst ``Classical.em) c) (branch · ``if_pos a) (branch · ``if_neg b)
  -- divisions and modulos: case analysis on the sign of the divisor, then the facts of the division
  if let some s := terms.find? fun s => isDivMod s && !st.done.contains (divKey s) then
    let x := s.getArg! 4
    let y := s.getArg! 5
    match st.signs.get? y with
    | none =>
        -- NOTE: the sign is recorded for `y` itself (the literals of the cases may be stated for other forms of `y`)
        newCase ctx
        let withSign (sign : Sign) (h : Expr) : TacticM Expr :=
          refute ctx [h] { st with signs := st.signs.insert y (sign, h) }
        if let some hy ← nonnegProof? y then
          return ← orElim (mkApp2 (mkConst ``eq_zero_or_pos_of_nonneg) y hy) (withSign .zero) (withSign .pos)
        return ← orElim (← mkAppM ``Int.lt_trichotomy #[y, mkIntLit 0]) (withSign .neg) fun h =>
          orElim h (withSign .zero) (withSign .pos)
    | some (sign, hs) =>
        let st := { st with done := st.done.insert (divKey s) }
        let facts ← match sign with
          | .zero => pure [← mkAppM ``ediv_of_eq_zero #[x, hs], ← mkAppM ``emod_of_eq_zero #[x, hs]]
          | .pos => pure [← mkAppM ``emod_nonneg_of_pos #[x, hs], ← mkAppM ``emod_lt_of_pos #[x, hs]]
          | .neg => pure [← mkAppM ``emod_nonneg_of_neg #[x, hs], ← mkAppM ``emod_lt_of_neg #[x, hs]]
        return ← refute ctx (mkApp2 (mkConst ``div_mod_eq) x y :: facts) st
  -- nonnegative atoms (e.g., casts of natural numbers, their divisions)
  let mut st := st
  for s in terms do
    if !st.done.contains s then
      st := { st with done := st.done.insert s }
      if let some h ← nonnegProof? s then st ← addLit st .nonneg (mkIntLit 0) s h
  closeLits ctx st.lits ctx.cfg.signSplits
where
  /-- `(t, true)` for `0 = t`, `(t, false)` for `t = 0` (over `Int`) -/
  isZeroEq? (c : Expr) : MetaM (Option (Expr × Bool)) := do
    let some (α, a, b) := c.eq? | return none
    if !isInt α then return none
    if ← isZero a then return some (b, true)
    if ← isZero b then return some (a, false)
    return none
  /-- key of the facts of the division of `x` by `y` -/
  divKey (s : Expr) : Expr := mkApp2 (mkConst ``HDiv.hDiv) (s.getArg! 4) (s.getArg! 5)

end

syntax (name := blasterNlarith) "blaster_nlarith" : tactic

/-- Nonlinear integer arithmetic (see the module documentation). Fails quickly on goals without nonlinear terms. -/
@[tactic blasterNlarith] def evalBlasterNlarith : Tactic := fun _ => do
  let ctx : Ctx := { cases := ← IO.mkRef 0, calls := ← IO.mkRef 0 }
  liftMetaTactic fun g => do let (_, g) ← g.intros; return [g]
  withMainContext do
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
    let hasNl ← (hyps.map (·.type) |>.push tgt).anyM fun t => do return hasNonlinear (← instantiateMVars t)
    if !hasNl then throwError "blaster_nlarith: no nonlinear term"
    let facts := (← hyps.filterM fun d => isProp d.type).map (·.toExpr) |>.toList
    let pf ← if tgt.isConstOf ``False then refute ctx facts {}
      else
        if !(← isProp tgt) then throwError "blaster_nlarith: goal is not a proposition"
        let p ← withLocalDeclD `hneg (mkNot tgt) fun hneg => do
          mkLambdaFVars #[hneg] (← refute ctx (hneg :: facts) {})
        pure (mkApp2 (mkConst ``Classical.byContradiction) tgt p)
    g.assign pf
    replaceMainGoal []

end Blaster.Reconstruct.SmtProof.NlArith
