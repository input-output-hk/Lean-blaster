import Lean

/-! A standalone integer arithmetic certificate checker. No dependency on Blaster. -/

namespace Z3Certificate.IntFarkas

abbrev RExpr := Lean.Grind.CommRing.Expr

/-- An already weighted arithmetic constraint. -/
structure Term where
  expr : RExpr
  strict : Bool

def Valid (strict : Bool) (value : Int) : Prop :=
  if strict then 0 < value else 0 ≤ value

def sum : List Term → RExpr
  | [] => .num 0
  | t :: ts => .add t.expr (sum ts)

def hasStrict : List Term → Bool
  | [] => false
  | t :: ts => t.strict || hasStrict ts

def Holds (ctx : Lean.Grind.CommRing.Context Int) : List Term → Prop
  | [] => True
  | t :: ts => Valid t.strict (t.expr.denote ctx) ∧ Holds ctx ts

theorem add_valid {a b : Int} {sa sb : Bool}
    (ha : Valid sa a) (hb : Valid sb b) : Valid (sa || sb) (a + b) := by
  cases sa <;> cases sb <;> simp_all [Valid] <;> omega

theorem sum_valid (ctx : Lean.Grind.CommRing.Context Int) (ts : List Term)
    (h : Holds ctx ts) : Valid (hasStrict ts) ((sum ts).denote ctx) := by
  induction ts with
  | nil => change (0 : Int) ≤ 0; omega
  | cons t ts ih =>
    exact add_valid h.1 (ih h.2)

/-- The polynomial sum is the supplied constant, which contradicts its sign. -/
noncomputable def check (ts : List Term) (constant : Int) : Bool :=
  (sum ts).toPoly_k.beq' (Lean.Grind.CommRing.Expr.num constant).toPoly_k &&
    (if hasStrict ts then decide (constant ≤ 0) else decide (constant < 0))

open Lean.Grind.CommRing in
private theorem eq_of_norm (ctx : Context Int) (a b : Lean.Grind.CommRing.Expr)
    (h : a.toPoly_k.beq' b.toPoly_k = true) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, Expr.toPoly_k_eq_toPoly] at h
  rw [← Expr.denote_toPoly, ← Expr.denote_toPoly, h]

/-- An arithmetic identity checked by normalization, independent of hypotheses.
    This interface is also usable by the official Z3 Lean source exporter. -/
theorem constant_eq (ctx : Lean.Grind.CommRing.Context Int) (e : RExpr) (k : Int)
    (checked : e.toPoly_k.beq' (Lean.Grind.CommRing.Expr.num k).toPoly_k = true) :
    e.denote ctx = k := by
  have number : (Lean.Grind.CommRing.Expr.num k).denote ctx = k := by
    simp [Lean.Grind.CommRing.Expr.denote, Lean.Grind.CommRing.denoteInt_eq]
  exact (eq_of_norm ctx e (.num k) checked).trans number

/-- Soundness of the data checker. Its Boolean premise is evaluated by the kernel. -/
theorem check_sound (ctx : Lean.Grind.CommRing.Context Int) (ts : List Term)
    (constant : Int) (h : Holds ctx ts) (checked : check ts constant = true) : False := by
  have parts := checked
  unfold check at parts
  simp only [Bool.and_eq_true] at parts
  have eq := constant_eq ctx (sum ts) constant parts.1
  have valid := sum_valid ctx ts h
  rw [eq] at valid
  cases hs : hasStrict ts <;> simp_all [Valid] <;> omega

theorem scale_nonneg {a : Int} (k : Int) (hk : 0 ≤ k) (h : 0 ≤ a) : Valid false (k * a) :=
  Int.mul_nonneg hk h

theorem scale_pos {a : Int} (k : Int) (hk : 0 < k) (h : 0 < a) : Valid true (k * a) :=
  Int.mul_pos hk h

theorem scale_zero {a : Int} (k : Int) (h : a = 0) : Valid false (k * a) := by
  simp [Valid, h]

end Z3Certificate.IntFarkas
