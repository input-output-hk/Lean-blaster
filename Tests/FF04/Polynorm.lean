/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Lean

/-!
Core-only adaptation of the reflective list/sorted-monomial algorithm in
lean-smt 9b314968f6405395ecbc030c4d3f9b35e4974aa1,
Smt/Reconstruct/ZMod/Polynorm.lean. The upstream authors and license are above.

This retains its insertion/merge, fold-based multiplication and repeated-power
algorithm and semantic proof structure. Only the coefficient algebra and Lean
4.24 core lemma compatibility are adapted. No Qq reifier or native proof path
is imported. Equality certificates use `decide` followed by the semantic theorem.
This is a bounded FF-04 experiment, not a complete canonical-form decision
procedure: the upstream zero-monomial behavior is deliberately preserved.
-/
namespace Blaster.FF04.Polynorm

open Lean.Grind
open Semiring CommSemiring Ring AddCommGroup

variable {R : Type u} [CommRing R]

attribute [local simp] Semiring.add_zero Semiring.one_mul Semiring.mul_one
  Semiring.zero_mul Semiring.mul_zero Semiring.pow_zero Semiring.pow_one
  AddCommMonoid.zero_add AddCommGroup.neg_zero

abbrev Var := Nat

def Context (R : Type u) := Var → R

structure Monomial (R : Type u) where
  coeff : R
  vars : List (Var × Nat) -- variable index and multiplicity
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial R) : Monomial R :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial R) (_ : m₁.vars = m₂.vars) : Monomial R :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial R) : Monomial R :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert : Var × Nat → List (Var × Nat) → List (Var × Nat) := fun (x, xn) ys =>
    match ys with
    | [] => [(x, xn)]
    | (y, yn) :: ys =>
      if x < y then (x, xn) :: (y, yn) :: ys
      else if y = x then (x, xn + yn) :: ys
      else (y, yn) :: insert (x, xn) ys

def denote (ctx : Context R) (m : Monomial R) : R :=
  m.coeff * m.vars.foldl (fun acc (v, vn) => acc * (ctx v) ^ vn) 1

theorem denote_neg {m : Monomial R} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Ring.neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end

theorem foldl_mul_factor {ctx : Context R} (l : List (Var × Nat)) (z : R) :
  List.foldl (fun acc (v, k) => acc * (ctx v) ^ k) z l =
  z * List.foldl (fun acc (v, k) => acc * (ctx v) ^ k) 1 l := by
  conv => lhs; rw [show z = z * 1 from (mul_one z).symm]
  exact foldl_assoc mul_assoc z 1

-- Can be generalized.
theorem foldl_mul_insert {ctx : Context R} :
  List.foldl (fun z (a, k) => z * (ctx a) ^ k) 1 (mul.insert (y, yn) ys) =
  (ctx y) ^ yn * List.foldl (fun z (a, k) => z * (ctx a) ^ k) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    obtain ⟨x, xn⟩ := x
    by_cases h : y < x
    · simp [mul.insert, h, foldl_assoc mul_assoc ((ctx y) ^ yn) ((ctx x) ^ xn)]
    · simp only [mul.insert, h, if_false]
      by_cases heq : x = y
      · rw [if_pos heq, heq]
        simp only [List.foldl_cons, one_mul, pow_add]
        rw [foldl_assoc mul_assoc ((ctx y) ^ yn) ((ctx y) ^ xn)]
      · rw [if_neg heq]
        simp only [List.foldl_cons, one_mul]
        rw [foldl_mul_factor _ ((ctx x) ^ xn), ih,
            foldl_mul_factor ys ((ctx x) ^ xn),
            ← mul_assoc, mul_comm ((ctx x) ^ xn) ((ctx y) ^ yn), mul_assoc]

theorem denote_add {ctx: Context R} {m n : Monomial R} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, right_distrib, h]

theorem denote_mul{ctx: Context R}  {m₁ m₂ : Monomial R} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, mul_assoc]; congr 1
  rw [← mul_assoc, mul_comm _ m₂.coeff, mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨y, yn⟩ := y
    rw [List.foldr_cons, foldl_mul_insert, ih, List.foldl_cons, one_mul,
        foldl_mul_factor ys ((ctx y) ^ yn), mul_assoc]

end Monomial

abbrev Polynomial (R : Type u) := List (Monomial R)

variable [DecidableEq R]

namespace Polynomial

def neg (p : Polynomial R) : Polynomial R :=
  p.map Monomial.neg

scoped instance [LT α] [LT β] : LT (α × β) where
  lt := fun (x₁, y₁) (x₂, y₂) => x₁ < x₂ ∨ (x₁ = x₂ ∧ y₁ < y₂)

scoped instance [LT α] [LT β] [DecidableLT α] [DecidableEq α] [DecidableLT β]
  : DecidableLT (α × β) := fun (x₁, y₁) (x₂, y₂) =>
  show Decidable (x₁ < x₂ ∨ x₁ = x₂ ∧ y₁ < y₂) from
  inferInstance

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial R) : Polynomial R :=
  p.foldr insert q
where
  insert (m : Monomial R) : Polynomial R → Polynomial R
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial R) : Polynomial R :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial R) (p : Polynomial R) : Polynomial R :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial R) : Polynomial R :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def pow (p : Polynomial R) (k : Nat) : Polynomial R :=
  k.repeat p.mul [{ coeff := 1, vars := [] }]

def denote (ctx : Context R) (p : Polynomial R) : R :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

-- ⊢ List.foldl (fun z a => z + Monomial.denote ctx a) 0
--     (if h : m.vars = n.vars then if (m.add n ⋯).coeff = 0 then p else m.add n ⋯ :: p else n :: add.insert m p) =
--   Monomial.denote ctx m + (Monomial.denote ctx n + List.foldl (fun z a => z + Monomial.denote ctx a) 0 p)

theorem foldl_add_insert (ctx : Context R) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, add_comm (0 : R), Monomial.foldl_assoc add_assoc ]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←add_assoc, add_comm, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq]
        · simp [-add_zero, add_comm (0:R), Monomial.foldl_assoc add_assoc, Monomial.denote_add, add_assoc]
      · simp only [List.foldl_cons, add_comm (0: R), ih, Monomial.foldl_assoc add_assoc]
        rw [←add_assoc, add_comm (Monomial.denote ctx n), add_assoc]

omit [DecidableEq R] in
theorem denote_neg {p : Polynomial R} :
 p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, add_comm (0:R),
     Monomial.foldl_assoc add_assoc,neg_add,
     ←ih,
     List.map,
     Monomial.denote_neg]

theorem denote_add {p q : Polynomial R} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, add_comm (0:R), Monomial.foldl_assoc add_assoc, add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial R} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, Ring.sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial R} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, add_comm (0 :R), Monomial.foldl_assoc add_assoc, left_distrib, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

omit [DecidableEq R] in
theorem denote_cons {p : List (Monomial R)} {ctx : Context R} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  simp only [denote, List.foldl_cons, add_comm (0 :R), Monomial.foldl_assoc add_assoc]

theorem denote_nil_add {p : Polynomial R} {ctx : Context R} :
    denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, denote_cons, show denote ctx [] = 0 by rfl]

theorem denote_add_insert {g : Monomial R → Polynomial R} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih, @ih ((g k).add []), ← add_assoc, denote_nil_add, denote_add, add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial R → Polynomial R} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) (0 :R) p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, add_comm] at *
    rw [add_comm (0:R), Monomial.foldl_assoc add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial R} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx := by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, right_distrib, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

theorem denote_pow {p : Polynomial R} {k : Nat} : (p.pow k).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero =>
    simp [pow, Nat.repeat, denote, Monomial.denote]
  | succ k ih =>
    show (p.mul (p.pow k)).denote ctx = p.denote ctx ^ (k + 1)
    rw [denote_mul, ih, pow_succ, mul_comm]

end Polynomial

inductive Expr (R : Type u) where
  | val (v : R)
  | var (v : Nat)
  | neg (a : Expr R)
  | add (a b : Expr R)
  | sub (a b : Expr R)
  | mul (a b : Expr R)
  | pow (a : Expr R) (n : Nat)
deriving DecidableEq, Inhabited, Repr

namespace Expr

/-- Normalize using the pinned insertion/fold algorithm. Equality of results is
a sufficient certificate, not a complete decision procedure for ring equality. -/
def toPolynomial : Expr R → Polynomial R
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := (1 : R), vars := [(v, 1)] }]
  | .neg a => Polynomial.neg (toPolynomial a)
  | .add a b => Polynomial.add (toPolynomial a) (toPolynomial b)
  | .sub a b => Polynomial.sub (toPolynomial a) (toPolynomial b)
  | .mul a b => Polynomial.mul (toPolynomial a) (toPolynomial b)
  | .pow a n => Polynomial.pow (toPolynomial a) n

def eval (ctx : Context R) : Expr R → R
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.eval ctx
  | .add a b => a.eval ctx + b.eval ctx
  | .sub a b => a.eval ctx - b.eval ctx
  | .mul a b => a.eval ctx * b.eval ctx
  | .pow a n => a.eval ctx ^ n

/-- Every normalization operation preserves evaluation in the coefficient ring. -/
theorem eval_toPolynomial {e : Expr R} : eval ctx e  = (toPolynomial e).denote ctx := by
  induction e with
  | val v =>
    simp only [eval, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv];  rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [eval, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [eval, toPolynomial, Polynomial.denote_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPolynomial, Polynomial.denote_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPolynomial, Polynomial.denote_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPolynomial, Polynomial.denote_mul, ih₁, ih₂]
  | pow a n ih =>
    simp only [eval, toPolynomial, Polynomial.denote_pow, ih]

/-- Transport a kernel-checked normal-form equality to the original expressions.
No solver result or native-decision axiom is used by this soundness bridge. -/
theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr R} (h : e₁.toPolynomial = e₂.toPolynomial)
  : e₁.eval ctx = e₂.eval ctx := by
  rw [eval_toPolynomial, eval_toPolynomial, h]

end Expr

end Blaster.FF04.Polynorm
