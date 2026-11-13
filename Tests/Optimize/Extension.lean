import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.Extension

/-! ## Hand-written optimization function -/

@[blaster String.contains]
def optimizeStrContains (_f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 2 then return none
  -- args[0] string argument
  -- args[1] char argument
  let op1 := args[0]!
  let op2 := args[1]!
  if let Expr.lit (Literal.strVal s) := op1 then
    if let some c := isCharValue? op2 then
      return ← mkBoolLit (String.contains s c)
    else return none
  else return none

#blaster [String.contains "aabbcccdddefffg" 'e' = true]

/-! ## Optimization functions generated from theorems/axioms -/

/-! Equality with a premise (checked in the hypothesis map) and restart flag. -/
@[blaster (restart := true)]
theorem tdiv_eq_ediv_of_gt_zero (a b : Int) (h : 0 < a) : Int.tdiv a b = Int.ediv a b := by
 cases a with
  | ofNat m =>
    cases b with
    | ofNat n => first | rfl | simp [Int.tdiv, Int.ediv]
    | negSucc n => first | rfl | simp [Int.tdiv, Int.ediv]
  | negSucc m =>
    exfalso
    first
      | exact absurd h (Int.negSucc_not_pos m)
      | exact absurd h (by omega)
      | simp at h

-- ∀ (a b c : Int), 0 < a → Int.tdiv a b = c ===> ∀ (a b c : Int), 0 < a → c = Int.ediv a b
#testOptimize [ "ExtTdivEdiv_1" ] (norm-result: 1)
  ∀ (a b c : Int), 0 < a → Int.tdiv a b = c ===>
  ∀ (a b c : Int), 0 < a → c = Int.ediv a b

-- premise not available: no rewriting
#testOptimize [ "ExtTdivEdiv_2" ] ∀ (a b c : Int), Int.tdiv a b = c ===> ∀ (a b c : Int), c = Int.tdiv a b

/-! Structural matching on constructor-like (axiom) applications. -/

structure MyPt where
  x : Nat
  y : Nat

axiom mkMyPt : Nat → Nat → MyPt
axiom firstPt (p : MyPt) : Nat

@[blaster]
axiom first_pt_of_mk : ∀ (x y : Nat), firstPt (mkMyPt x y) = x

-- NOTE: the unused binder `y` is removed by the optimizer
#testOptimize [ "ExtFirstPt_1" ] ∀ (x y z : Nat), firstPt (mkMyPt x y) = z ===> ∀ (x z : Nat), x = z
#testOptimize [ "ExtFirstPt_2" ] ∀ (x y : Nat), firstPt (mkMyPt x y) = x ===> True
#testOptimize [ "ExtFirstPt_3" ] ∀ (p : MyPt) (z : Nat), firstPt p = z ===> ∀ (p : MyPt) (z : Nat), z = firstPt p

/-! Nat literals in the lhs/rhs and nested patterns. -/

axiom g : Nat → Nat

@[blaster]
axiom g_succ : ∀ (n : Nat), g (Nat.add 1 n) = Nat.add 1 (g n)

#testOptimize [ "ExtGSucc_1" ] (norm-result: 1) ∀ (n m : Nat), g (1 + n) = m ===> ∀ (n m : Nat), m = Nat.add 1 (g n)
#testOptimize [ "ExtGSucc_2" ] (norm-result: 1) ∀ (n m : Nat), g (2 + n) = m ===> ∀ (n m : Nat), m = g (Nat.add 2 n)

/-! Predicates: `p x` handled as `p x = True`, `¬ q x` handled as `q x = False`. -/

axiom p : Nat → Prop
axiom q : Nat → Prop

@[blaster]
axiom p_g : ∀ (n : Nat), p (g n)

@[blaster]
axiom not_q_g : ∀ (n : Nat), ¬ q (g n)

#testOptimize [ "ExtPredTrue_1" ] ∀ (n : Nat), p (g n) ===> True
#testOptimize [ "ExtPredTrue_2" ] ∀ (n : Nat), p n → p (g n) ===> True
#testOptimize [ "ExtPredFalse_1" ] ∀ (n : Nat), q (g n) → p n ===> True
#testOptimize [ "ExtPredFalse_2" ] ∀ (n : Nat), ¬ q (g n) ===> True

/-! `≠` conclusion: `gn n ≠ 0` is unfolded to `¬ (gn n = 0)` and normalized (`0 < gn n` for `Nat`,
`¬ (0 = gz n)` for `Int`), then handled as a predicate.
The `ExtPredNeSwap_*` cases write the goal as `gn n = N`: the operands of commutative operators are
reordered before the registered rules are looked up, so the rule fires on `N = gn n` as well. -/

axiom gn : Nat → Nat
axiom gz : Int → Int
axiom pz : Int → Prop

@[blaster]
axiom gn_ne_zero : ∀ (n : Nat), gn n ≠ 0

@[blaster]
axiom gn_ne_five : ∀ (n : Nat), gn n ≠ 5

@[blaster]
axiom gz_ne_zero : ∀ (n : Int), gz n ≠ 0

@[blaster]
axiom gz_ne_five : ∀ (n : Int), gz n ≠ 5

#testOptimize [ "ExtPredNe_1" ] ∀ (n : Nat), gn n ≠ 0 ===> True
#testOptimize [ "ExtPredNe_2" ] ∀ (n : Nat), ¬ (gn n = 0) ===> True
#testOptimize [ "ExtPredNe_3" ] ∀ (n : Nat), 0 < gn n ===> True
#testOptimize [ "ExtPredNe_4" ] ∀ (n : Nat), 0 < gn n → p n ===> ∀ (n : Nat), p n
#testOptimize [ "ExtPredNe_5" ] ∀ (n : Nat), ¬ (5 = gn n) ===> True
#testOptimize [ "ExtPredNe_6" ] ∀ (n : Nat), 5 = gn n → p n ===> True
#testOptimize [ "ExtPredNe_7" ] ∀ (n : Int), ¬ (0 = gz n) ===> True
#testOptimize [ "ExtPredNe_8" ] ∀ (n : Int), 0 = gz n → pz n ===> True
#testOptimize [ "ExtPredNe_9" ] ∀ (n : Int), ¬ (5 = gz n) ===> True
#testOptimize [ "ExtPredNe_10" ] ∀ (n : Int), 5 = gz n → pz n ===> True
-- goal written with the operands in the non-normalized order (reordered before the lookup)
#testOptimize [ "ExtPredNeSwap_1" ] ∀ (n : Nat), gn n ≠ 5 ===> True
#testOptimize [ "ExtPredNeSwap_2" ] ∀ (n : Nat), ¬ (gn n = 5) ===> True
#testOptimize [ "ExtPredNeSwap_3" ] ∀ (n : Nat), gn n = 5 → p n ===> True
#testOptimize [ "ExtPredNeSwap_4" ] ∀ (n : Int), gz n ≠ 0 ===> True
#testOptimize [ "ExtPredNeSwap_5" ] ∀ (n : Int), ¬ (gz n = 0) ===> True
#testOptimize [ "ExtPredNeSwap_6" ] ∀ (n : Int), gz n = 0 → pz n ===> True
#testOptimize [ "ExtPredNeSwap_7" ] ∀ (n : Int), gz n ≠ 5 ===> True
#testOptimize [ "ExtPredNeSwap_8" ] ∀ (n : Int), ¬ (gz n = 5) ===> True
#testOptimize [ "ExtPredNeSwap_9" ] ∀ (n : Int), gz n = 5 → pz n ===> True

/-! Iff conclusion. -/

axiom r : Nat → Prop

@[blaster]
axiom r_g_iff : ∀ (n : Nat), r (g n) ↔ p n

#testOptimize [ "ExtIff_1" ] ∀ (n : Nat), r (g n) ===> ∀ (n : Nat), p n

/-! Non-linear patterns. -/

axiom h2 : Nat → Nat → Nat

@[blaster]
axiom h2_same : ∀ (n : Nat), h2 n n = n

#testOptimize [ "ExtNonLinear_1" ] ∀ (n m : Nat), h2 n n = m ===> ∀ (n m : Nat), n = m
#testOptimize [ "ExtNonLinear_2" ] ∀ (n m : Nat), h2 n m = m ===> ∀ (n m : Nat), m = h2 n m

/-! Universe polymorphic theorem: levels are recovered from the lhs. -/

universe u

axiom pl : {α : Type u} → List α → Nat

@[blaster]
axiom pl_cons : ∀ {α : Type u} (a : α) (xs : List α), pl (a :: xs) = Nat.add 1 (pl xs)

@[blaster]
axiom pl_nil : ∀ {α : Type u}, pl (@List.nil α) = 0

-- NOTE: the unused binder `a` is removed by the optimizer
#testOptimize [ "ExtPoly_1" ] (norm-result: 1) ∀ (a : Nat) (xs : List Nat) (m : Nat), pl (a :: xs) = m ===> ∀ (xs : List Nat) (m : Nat), m = Nat.add 1 (pl xs)
#testOptimize [ "ExtPoly_2" ] (norm-result: 1) ∀ (m : Nat), pl ([] : List Nat) = m ===> ∀ (m : Nat), 0 = m

/-! Target head specified explicitly: must be the head of the lhs. -/

@[blaster g]
axiom g_zero : g 0 = 0

#testOptimize [ "ExtHead_1" ] (norm-result: 1) ∀ (m : Nat), g 0 = m ===> ∀ (m : Nat), 0 = m


/-! Target head is a Ctor -/

@[blaster (restart := true)]
theorem dite_pull_on_cons (m n : Nat) (b : Bool) :
  Blaster.dite' b (fun _ => m) (fun _ => n) :: [] =
  Blaster.dite' b (fun _ => [m]) (fun _ => [n]) :=
  by dsimp [Blaster.dite']; cases h : Blaster.decide' b
     case false => simp
     case true => simp

@[blaster (restart := true)]
-- handling optimization not applied on arguments
theorem ite_pull_on_cons (m n : Nat) (b : Bool) :
  (if b then m else n) :: [] = if b then [m] else [n] := by split <;> simp

@[blaster (restart := true)]
theorem ite_pull_on_some (m n : Nat) (b : Bool) :
  some (if b then m else n) = Blaster.dite' b (fun _ => some m) (fun _ => some n) :=
  by dsimp [Blaster.dite']; cases h : Blaster.decide' b
     case false => simp; intro h1; have h2 := (Blaster.decide'_false _).mp h; contradiction
     case true =>
       simp; intro h1
       have h2 := (Blaster.decide'_true _).mp h;
       have h3 := ne_true_of_eq_false h1
       contradiction

#testOptimize [ "ExtCtor_1"]
  ∀ (m n : Nat) (b : Bool) (ys : List Nat), Blaster.dite' b (fun _ => m) (fun _ => n) :: [] = ys ===>
  ∀ (m n : Nat) (b : Bool) (ys : List Nat), ys = Blaster.dite' (true = b) (fun _ => [m]) (fun _ => [n])

#testOptimize [ "ExtCtor_2"]
  ∀ (m n : Nat) (b : Bool) (ys : List Nat), (if b then m else n) :: [] = ys ===>
  ∀ (m n : Nat) (b : Bool) (ys : List Nat), ys = Blaster.dite' (true = b) (fun _ => [m]) (fun _ => [n])

#testOptimize [ "ExtCtor_3"]
  ∀ (m n : Nat) (b : Bool) (y : Option Nat), some (if b then m else n) = y ===>
  ∀ (m n : Nat) (b : Bool) (y : Option Nat), y = Blaster.dite' (true = b) (fun _ => some m) (fun _ => some n)

/-! ## Normalization of the theorem statement

The statement is normalized (see `normalizeExpr`) before the optimization function is generated:
`OfNat` literals, `let`, beta-redexes, `True`/`False` in premises and conclusions, double negation,
operand ordering of commutative operators, ... are all taken care of. Function unfolding is not
applied, so operators must be written in their normalized form (`Nat.add`, not `+`).
-/

axiom c1 : Nat → Prop
axiom c2 : Nat → Prop
axiom c3 : Nat → Prop
axiom c4 : Nat → Prop

/-! `Nat.add 0 n` and `Nat.add n 0` are simplified on both sides. -/
axiom nz : Nat → Nat

@[blaster]
axiom nz_zero_add : ∀ (n : Nat), nz (Nat.add 0 n) = Nat.add n 0

#testOptimize [ "ExtNormZeroAdd_1" ] ∀ (n m : Nat), nz n = m ===> ∀ (n m : Nat), n = m

/-! Beta-redex in the lhs. -/
axiom nb : Nat → Nat

@[blaster]
axiom nb_beta : ∀ (n : Nat), (fun x => nb x) (Nat.add 1 n) = n

#testOptimize [ "ExtNormBeta_1" ] ∀ (n m : Nat), nb (1 + n) = m ===> ∀ (n m : Nat), n = m
#testOptimize [ "ExtNormBeta_2" ] (norm-result: 1) ∀ (n m : Nat), nb (2 + n) = m ===> ∀ (n m : Nat), m = nb (Nat.add 2 n)

/-! `let` in the lhs. -/
axiom nl : Nat → Nat

@[blaster]
axiom nl_let : ∀ (n : Nat), (let k := Nat.add 2 n; nl k) = n

#testOptimize [ "ExtNormLet_1" ] ∀ (n m : Nat), nl (2 + n) = m ===> ∀ (n m : Nat), n = m

/-! `True` premises and `True` conjuncts are removed; `Nat.mul 1 n` is simplified. -/
axiom nt : Nat → Nat

@[blaster]
axiom nt_true : ∀ (n : Nat), True → (True ∧ c1 n) → nt (Nat.mul 1 n) = n

#testOptimize [ "ExtNormTrue_1" ] ∀ (n m : Nat), c1 n → nt n = m ===> ∀ (n m : Nat), c1 n → n = m
#testOptimize [ "ExtNormTrue_2" ] ∀ (n m : Nat), nt n = m ===> ∀ (n m : Nat), m = nt n

/-! `False` disjuncts are removed; `if` on a constant condition is reduced on both sides. -/
axiom nf : Nat → Nat

@[blaster]
axiom nf_false : ∀ (n : Nat), c2 n ∨ False → nf (if true then n else 0) = (if 1 = 1 then n else 0)

#testOptimize [ "ExtNormFalse_1" ] ∀ (n m : Nat), c2 n → nf n = m ===> ∀ (n m : Nat), c2 n → n = m
#testOptimize [ "ExtNormFalse_2" ] ∀ (n m : Nat), nf n = m ===> ∀ (n m : Nat), m = nf n

/-! Double negation in a premise; operands of `Nat.add` are reordered (`Nat.add n 1` ↦ `Nat.add 1 n`). -/
axiom nn : Nat → Nat

@[blaster]
axiom nn_notnot : ∀ (n : Nat), ¬ ¬ c2 n → nn (Nat.add n 1) = n

#testOptimize [ "ExtNormNotNot_1" ] ∀ (n m : Nat), c2 n → nn (n + 1) = m ===> ∀ (n m : Nat), c2 n → n = m
#testOptimize [ "ExtNormNotNot_2" ] (norm-result: 1) ∀ (n m : Nat), nn (n + 1) = m ===> ∀ (n m : Nat), m = nn (Nat.add 1 n)

/-! A statement that normalizes to `True` is handled natively: no optimization function is generated
    and an info message is logged by the attribute. -/
axiom ntriv : Nat → Nat

/-! `Eq`: the lhs and rhs are equal after normalization. -/
/--
info: @[blaster]: `Test.Extension.ntriv_triv` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_triv : ∀ (n : Nat), ntriv (Nat.add 0 n) = ntriv n

#testOptimize [ "ExtNormTriv_1" ] ∀ (n m : Nat), ntriv (0 + n) = m ===> ∀ (n m : Nat), m = ntriv n

/-! `Eq`: reflexivity. -/
/--
info: @[blaster]: `Test.Extension.ntriv_eq_refl` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_eq_refl : ∀ (n : Nat), ntriv n = ntriv n

/-! `Iff`: both sides are equal after normalization. -/
/--
info: @[blaster]: `Test.Extension.ntriv_iff` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_iff : ∀ (n : Nat), c1 (Nat.add 0 n) ↔ c1 n

/-! Predicate: `c1 n ∨ True` normalizes to `True`. -/
/--
info: @[blaster]: `Test.Extension.ntriv_or_true` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_or_true : ∀ (n : Nat), c1 n ∨ True

/-! Predicate: `0 < Nat.add 1 n` is decided natively. -/
/--
info: @[blaster]: `Test.Extension.ntriv_zero_lt` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_zero_lt : ∀ (n : Nat), 0 < Nat.add 1 n

/-! Predicate: `n ≤ n` is decided natively. -/
/--
info: @[blaster]: `Test.Extension.ntriv_le_refl` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_le_refl : ∀ (n : Nat), n ≤ n

/-! Negation: `¬ (Nat.add 1 n = 0)` is decided natively. -/
/--
info: @[blaster]: `Test.Extension.ntriv_not_eq` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_not_eq : ∀ (n : Nat), ¬ (Nat.add 1 n = 0)

/-! Negation: `≠` is unfolded, `Nat.add 1 n ≠ 0` is decided natively as well. -/
/--
info: @[blaster]: `Test.Extension.ntriv_ne` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_ne : ∀ (n : Nat), Nat.add 1 n ≠ 0

/-! Negation: `¬ False` normalizes to `True` (the premise is dropped as well). -/
/--
info: @[blaster]: `Test.Extension.ntriv_not_false` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_not_false : ∀ (n : Nat), c1 n → ¬ False

/-! Implication: the premise entails the conclusion. -/
/--
info: @[blaster]: `Test.Extension.ntriv_imp_self` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_imp_self : ∀ (n : Nat), c1 n → c1 n

/-! A statement that normalizes to `False` is rejected.
    NOTE: the axiom is nevertheless added to the environment; it is not used by any other test. -/
/-- error: blaster: theorem Test.Extension.ntriv_unsound is unsound -/
#guard_msgs in
@[blaster]
axiom ntriv_unsound : ∀ (n : Nat), ¬ (ntriv n = ntriv n)

/-! ## Conjunction and disjunction premises

Each premise is compiled to a `TranslateEnvT Bool` check: atoms are looked up in the hypothesis
map, `∧` becomes `<&&>` and `∨` becomes `<||>`. Note that a disjunction is not looked up as a whole
in the hypothesis map: each disjunct is checked separately.
-/

/-! Conjunction. -/
axiom k1 : Nat → Nat → Nat

@[blaster]
axiom k1_conj : ∀ (n m : Nat), c1 n ∧ c2 m → k1 n m = n

#testOptimize [ "ExtConj_1" ] ∀ (n m z : Nat), c1 n → c2 m → k1 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → n = z
-- a conjunction hypothesis is split in the hypothesis map
#testOptimize [ "ExtConj_2" ] ∀ (n m z : Nat), c1 n ∧ c2 m → k1 n m = z ===> ∀ (n m z : Nat), c1 n ∧ c2 m → n = z
#testOptimize [ "ExtConj_3" ] ∀ (n m z : Nat), c1 n → k1 n m = z ===> ∀ (n m z : Nat), c1 n → z = k1 n m
#testOptimize [ "ExtConj_4" ] ∀ (n m z : Nat), c2 m → k1 n m = z ===> ∀ (n m z : Nat), c2 m → z = k1 n m

/-! Disjunction. -/
axiom k2 : Nat → Nat → Nat

@[blaster]
axiom k2_disj : ∀ (n m : Nat), c1 n ∨ c2 m → k2 n m = m

#testOptimize [ "ExtDisj_1" ] ∀ (n m z : Nat), c1 n → k2 n m = z ===> ∀ (n m z : Nat), c1 n → m = z
-- NOTE: the unused binder `n` is removed by the optimizer
#testOptimize [ "ExtDisj_2" ] ∀ (n m z : Nat), c2 m → k2 n m = z ===> ∀ (m z : Nat), c2 m → m = z
#testOptimize [ "ExtDisj_3" ] ∀ (n m z : Nat), c1 n → c2 m → k2 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → m = z
#testOptimize [ "ExtDisj_4" ] ∀ (n m z : Nat), c3 n → k2 n m = z ===> ∀ (n m z : Nat), c3 n → z = k2 n m
-- the disjunction as a whole is not looked up in the hypothesis map
#testOptimize [ "ExtDisj_5" ] ∀ (n m z : Nat), c1 n ∨ c2 m → k2 n m = z ===> ∀ (n m z : Nat), c1 n ∨ c2 m → z = k2 n m

/-! Disjunction of conjunctions. -/
axiom k3 : Nat → Nat → Nat

@[blaster]
axiom k3_disj_conj : ∀ (n m : Nat), (c1 n ∧ c2 m) ∨ (c3 n ∧ c4 m) → k3 n m = n

#testOptimize [ "ExtDisjConj_1" ] ∀ (n m z : Nat), c1 n → c2 m → k3 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → n = z
#testOptimize [ "ExtDisjConj_2" ] ∀ (n m z : Nat), c3 n → c4 m → k3 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → n = z
#testOptimize [ "ExtDisjConj_3" ] ∀ (n m z : Nat), c1 n → c3 n → k3 n m = z ===> ∀ (n m z : Nat), c1 n → c3 n → z = k3 n m
#testOptimize [ "ExtDisjConj_4" ] ∀ (n m z : Nat), c2 m → c4 m → k3 n m = z ===> ∀ (n m z : Nat), c2 m → c4 m → z = k3 n m

/-! Conjunction of disjunctions. -/
axiom k4 : Nat → Nat → Nat

@[blaster]
axiom k4_conj_disj : ∀ (n m : Nat), (c1 n ∨ c2 m) ∧ (c3 n ∨ c4 m) → k4 n m = m

#testOptimize [ "ExtConjDisj_1" ] ∀ (n m z : Nat), c1 n → c3 n → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c3 n → m = z
#testOptimize [ "ExtConjDisj_2" ] ∀ (n m z : Nat), c2 m → c3 n → k4 n m = z ===> ∀ (n m z : Nat), c2 m → c3 n → m = z
#testOptimize [ "ExtConjDisj_3" ] ∀ (n m z : Nat), c1 n → c4 m → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c4 m → m = z
#testOptimize [ "ExtConjDisj_4" ] ∀ (n m z : Nat), c1 n → c2 m → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → z = k4 n m
#testOptimize [ "ExtConjDisj_5" ] ∀ (n m z : Nat), c3 n → c4 m → k4 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → z = k4 n m

/-! Deeper nesting. -/
axiom k5 : Nat → Nat → Nat

@[blaster]
axiom k5_nested : ∀ (n m : Nat), c1 n ∨ (c2 m ∧ (c3 n ∨ c4 m)) → k5 n m = n

-- NOTE: the unused binder `m` is removed by the optimizer
#testOptimize [ "ExtNested_1" ] ∀ (n m z : Nat), c1 n → k5 n m = z ===> ∀ (n z : Nat), c1 n → n = z
#testOptimize [ "ExtNested_2" ] ∀ (n m z : Nat), c2 m → c4 m → k5 n m = z ===> ∀ (n m z : Nat), c2 m → c4 m → n = z
#testOptimize [ "ExtNested_3" ] ∀ (n m z : Nat), c2 m → c3 n → k5 n m = z ===> ∀ (n m z : Nat), c2 m → c3 n → n = z
#testOptimize [ "ExtNested_4" ] ∀ (n m z : Nat), c2 m → k5 n m = z ===> ∀ (n m z : Nat), c2 m → z = k5 n m
#testOptimize [ "ExtNested_5" ] ∀ (n m z : Nat), c3 n → c4 m → k5 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → z = k5 n m

/-! Specialized atomic checks (`0 < n`, `¬ 0 = m`) inside a disjunction. -/
axiom k6 : Nat → Nat → Nat

@[blaster]
axiom k6_lit : ∀ (n m : Nat), 0 < n ∨ ¬ m = 0 → k6 n m = Nat.add n m

#testOptimize [ "ExtDisjLit_1" ] (norm-result: 1) ∀ (n m z : Nat), 0 < n → k6 n m = z ===> ∀ (n m z : Nat), 0 < n → z = Nat.add n m
#testOptimize [ "ExtDisjLit_2" ] (norm-result: 1) ∀ (n m z : Nat), ¬ m = 0 → k6 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
-- `¬ 0 = m` is derived from `0 < m` by `nonZeroNatInHyps`
#testOptimize [ "ExtDisjLit_3" ] (norm-result: 1) ∀ (n m z : Nat), 0 < m → k6 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjLit_4" ] ∀ (n m z : Nat), k6 n m = z ===> ∀ (n m z : Nat), z = k6 n m

/-! `≠` atoms inside a disjunction / conjunction (`m ≠ 0` is unfolded then normalized to `0 < m`). -/
axiom k14 : Nat → Nat → Nat

@[blaster]
axiom k14_disj_ne : ∀ (n m : Nat), 0 < n ∨ m ≠ 0 → k14 n m = Nat.add n m

#testOptimize [ "ExtDisjNe_1" ] (norm-result: 1) ∀ (n m z : Nat), m ≠ 0 → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjNe_2" ] (norm-result: 1) ∀ (n m z : Nat), ¬ (m = 0) → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjNe_3" ] (norm-result: 1) ∀ (n m z : Nat), 0 < m → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
-- `<missing> ∨ True`
#testOptimize [ "ExtDisjNe_4" ] (norm-result: 1) ∀ (n z : Nat), k14 n 5 = z ===> ∀ (n z : Nat), z = Nat.add 5 n
-- `False ∨ False`: no rewriting
#testOptimize [ "ExtDisjNe_5" ] (norm-result: 1) ∀ (z : Nat), k14 0 0 = z ===> ∀ (z : Nat), z = k14 0 0
#testOptimize [ "ExtDisjNe_6" ] ∀ (n m z : Nat), k14 n m = z ===> ∀ (n m z : Nat), z = k14 n m

axiom k15 : Nat → Nat → Nat

@[blaster]
axiom k15_conj_ne : ∀ (n m : Nat), c1 n ∧ m ≠ 0 → k15 n m = n

#testOptimize [ "ExtConjNe_1" ] (norm-result: 1) ∀ (n m z : Nat), c1 n → m ≠ 0 → k15 n m = z ===> ∀ (n m z : Nat), c1 n → 0 < m → n = z
#testOptimize [ "ExtConjNe_2" ] (norm-result: 1) ∀ (n m z : Nat), c1 n → 0 < m → k15 n m = z ===> ∀ (n m z : Nat), c1 n → 0 < m → n = z
-- `<hypothesis> ∧ True`
#testOptimize [ "ExtConjNe_3" ] (norm-result: 1) ∀ (n z : Nat), c1 n → k15 n 5 = z ===> ∀ (n z : Nat), c1 n → n = z
-- `<hypothesis> ∧ False`: no rewriting
#testOptimize [ "ExtConjNe_4" ] (norm-result: 1) ∀ (n z : Nat), c1 n → k15 n 0 = z ===> ∀ (n z : Nat), c1 n → z = k15 n 0
-- `<missing> ∧ True`: no rewriting
#testOptimize [ "ExtConjNe_5" ] (norm-result: 1) ∀ (n z : Nat), k15 n 5 = z ===> ∀ (n z : Nat), z = k15 n 5

/-! ## Premises evaluated at application time

A premise is rebuilt (`optimizeAppExt`, i.e. `optimizeAppAux` iterated until no restart is pending)
with the matched arguments before being checked with `isTruePremise`: when the instantiated premise is reduced to `True` the rule applies without any
hypothesis, when it is reduced to `False` the rule must not be triggered, otherwise the premise is
looked up in the hypothesis map. The cases below cover literals, structurally decided premises
(`n ≤ n`, `n < Nat.add 1 n`, `n = n`, `Nat.add 1 n ≠ n`), premises reduced to a literal
(`Nat.mul n 0`), and premises established by (derived) hypotheses, for both `Nat` and `Int`.
`≠` premises are unfolded to `¬ (_ = _)` by `normalizeTheorem` and behave like them.
NOTE: unused binders are removed by the optimizer when the rule applies.
-/

axiom d1 : Int → Prop

/-! `Nat`: `0 < a`. -/
axiom k7 : Nat → Nat → Nat

@[blaster]
axiom k7_pos : ∀ (a z : Nat), 0 < a → k7 a z = z

#testOptimize [ "ExtPosNat_1" ] (norm-result: 1) ∀ (z w : Nat), k7 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtPosNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k7 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtPosNat_3" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k7 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
#testOptimize [ "ExtPosNat_4" ] (norm-result: 1) ∀ (n z w : Nat), 5 ≤ n → k7 n z = w ===> ∀ (n z w : Nat), ¬ (n < 5) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtPosNat_5" ] (norm-result: 1) ∀ (z w : Nat), k7 0 z = w ===> ∀ (z w : Nat), w = k7 0 z
#testOptimize [ "ExtPosNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k7 (n * 0) z = w ===> ∀ (z w : Nat), w = k7 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtPosNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k7 n z = w ===> ∀ (n z w : Nat), w = k7 n z

/-! `Nat`: `¬ (a = 0)` (normalized to `0 < a`). -/
axiom k8 : Nat → Nat → Nat

@[blaster]
axiom k8_nz : ∀ (a z : Nat), ¬ (a = 0) → k8 a z = z

#testOptimize [ "ExtNzNat_1" ] (norm-result: 1) ∀ (z w : Nat), k8 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNzNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k8 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNzNat_3" ] (norm-result: 1) ∀ (n z w : Nat), n ≠ 0 → k8 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNzNat_4" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k8 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNzNat_5" ] (norm-result: 1) ∀ (z w : Nat), k8 0 z = w ===> ∀ (z w : Nat), w = k8 0 z
#testOptimize [ "ExtNzNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k8 (n * 0) z = w ===> ∀ (z w : Nat), w = k8 0 z

/-! `Nat`: `a ≠ 0` (unfolded to `¬ (a = 0)`, then normalized to `0 < a`). -/
axiom k16 : Nat → Nat → Nat

@[blaster]
axiom k16_ne : ∀ (a z : Nat), a ≠ 0 → k16 a z = z

#testOptimize [ "ExtNeNat_1" ] (norm-result: 1) ∀ (z w : Nat), k16 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k16 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat_3" ] (norm-result: 1) ∀ (n z w : Nat), n ≠ 0 → k16 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNeNat_4" ] (norm-result: 1) ∀ (n z w : Nat), ¬ (n = 0) → k16 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNeNat_5" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k16 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeNat_6" ] (norm-result: 1) ∀ (z w : Nat), k16 0 z = w ===> ∀ (z w : Nat), w = k16 0 z
#testOptimize [ "ExtNeNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k16 (n * 0) z = w ===> ∀ (z w : Nat), w = k16 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNeNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k16 n z = w ===> ∀ (n z w : Nat), w = k16 n z

/-! `Nat`: `a ≤ b` (normalized to `¬ (b < a)`). -/
axiom k9 : Nat → Nat → Nat → Nat

@[blaster]
axiom k9_le : ∀ (a b z : Nat), a ≤ b → k9 a b z = z

#testOptimize [ "ExtLeNat_1" ] (norm-result: 1) ∀ (z w : Nat), k9 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_2" ] (norm-result: 1) ∀ (z w : Nat), k9 5 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k9 n n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_4" ] (norm-result: 1) ∀ (n z w : Nat), k9 0 n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_5" ] (norm-result: 1) ∀ (n z w : Nat), k9 n (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_6" ] (norm-result: 1) ∀ (n m z w : Nat), n ≤ m → k9 n m z = w ===> ∀ (n m z w : Nat), ¬ (m < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLeNat_7" ] (norm-result: 1) ∀ (z w : Nat), k9 5 3 z = w ===> ∀ (z w : Nat), w = k9 5 3 z
#testOptimize [ "ExtLeNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k9 (n + 1) n z = w ===> ∀ (n z w : Nat), w = k9 (Nat.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLeNat_9" ] (norm-result: 1) ∀ (n m z w : Nat), k9 n m z = w ===> ∀ (n m z w : Nat), w = k9 n m z

/-! `Nat`: `a < b`. -/
axiom k10 : Nat → Nat → Nat → Nat

@[blaster]
axiom k10_lt : ∀ (a b z : Nat), a < b → k10 a b z = z

#testOptimize [ "ExtLtNat_1" ] (norm-result: 1) ∀ (z w : Nat), k10 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k10 n (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k10 0 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_4" ] (norm-result: 1) ∀ (n m z w : Nat), n < m → k10 n m z = w ===> ∀ (n m z w : Nat), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLtNat_5" ] (norm-result: 1) ∀ (z w : Nat), k10 5 5 z = w ===> ∀ (z w : Nat), w = k10 5 5 z
#testOptimize [ "ExtLtNat_6" ] (norm-result: 1) ∀ (z w : Nat), k10 5 3 z = w ===> ∀ (z w : Nat), w = k10 5 3 z
#testOptimize [ "ExtLtNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k10 n n z = w ===> ∀ (n z w : Nat), w = k10 n n z
#testOptimize [ "ExtLtNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k10 n 0 z = w ===> ∀ (n z w : Nat), w = k10 n 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtLtNat_9" ] (norm-result: 1) ∀ (n m z w : Nat), k10 n m z = w ===> ∀ (n m z w : Nat), w = k10 n m z

/-! `Nat`: `a = b`. -/
axiom k11 : Nat → Nat → Nat → Nat

@[blaster]
axiom k11_eq : ∀ (a b z : Nat), a = b → k11 a b z = z

#testOptimize [ "ExtEqNat_1" ] (norm-result: 1) ∀ (z w : Nat), k11 5 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k11 n n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k11 (n + 1) (1 + n) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_4" ] (norm-result: 1) ∀ (n m z w : Nat), n = m → k11 n m z = w ===> ∀ (n m z w : Nat), n = m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtEqNat_5" ] (norm-result: 1) ∀ (z w : Nat), k11 5 6 z = w ===> ∀ (z w : Nat), w = k11 5 6 z
#testOptimize [ "ExtEqNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k11 (n + 1) 0 z = w ===> ∀ (n z w : Nat), w = k11 (Nat.add 1 n) 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtEqNat_7" ] (norm-result: 1) ∀ (n m z w : Nat), k11 n m z = w ===> ∀ (n m z w : Nat), w = k11 n m z

/-! `Nat`: `a ≠ b` (unfolded to `¬ (a = b)`). -/
axiom k17 : Nat → Nat → Nat → Nat

@[blaster]
axiom k17_ne : ∀ (a b z : Nat), a ≠ b → k17 a b z = z

#testOptimize [ "ExtNeNat2_1" ] (norm-result: 1) ∀ (z w : Nat), k17 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_2" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) 0 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_3" ] (norm-result: 1) ∀ (n z w : Nat), k17 0 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_4" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_5" ] (norm-result: 1) ∀ (n m z w : Nat), n ≠ m → k17 n m z = w ===> ∀ (n m z w : Nat), ¬ (n = m) → z = w
-- `¬ (n = m)` is derived from `n < m`
#testOptimize [ "ExtNeNat2_6" ] (norm-result: 1) ∀ (n m z w : Nat), n < m → k17 n m z = w ===> ∀ (n m z w : Nat), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeNat2_7" ] (norm-result: 1) ∀ (z w : Nat), k17 5 5 z = w ===> ∀ (z w : Nat), w = k17 5 5 z
#testOptimize [ "ExtNeNat2_8" ] (norm-result: 1) ∀ (n z w : Nat), k17 n n z = w ===> ∀ (n z w : Nat), w = k17 n n z
#testOptimize [ "ExtNeNat2_9" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) (1 + n) z = w ===> ∀ (n z w : Nat), w = k17 (Nat.add 1 n) (Nat.add 1 n) z
-- premise not established: no rewriting
#testOptimize [ "ExtNeNat2_10" ] (norm-result: 1) ∀ (n m z w : Nat), k17 n m z = w ===> ∀ (n m z w : Nat), w = k17 n m z

/-! `Nat`: conjunction / disjunction with an evaluated conjunct / disjunct. -/
axiom k12 : Nat → Nat → Nat → Nat

@[blaster]
axiom k12_conj : ∀ (a n z : Nat), 0 < a ∧ c1 n → k12 a n z = z

#testOptimize [ "ExtConjNat_1" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k12 5 n z = w ===> ∀ (n z w : Nat), c1 n → z = w
-- `True ∧ <missing>`: no rewriting
#testOptimize [ "ExtConjNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k12 5 n z = w ===> ∀ (n z w : Nat), w = k12 5 n z
-- `False ∧ <hypothesis>`: no rewriting
#testOptimize [ "ExtConjNat_3" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k12 0 n z = w ===> ∀ (n z w : Nat), c1 n → w = k12 0 n z

axiom k13 : Nat → Nat → Nat → Nat

@[blaster]
axiom k13_disj : ∀ (a n z : Nat), 0 < a ∨ c1 n → k13 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjNat_1" ] (norm-result: 1) ∀ (n z w : Nat), k13 5 n z = w ===> ∀ (z w : Nat), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjNat_2" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k13 0 n z = w ===> ∀ (n z w : Nat), c1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k13 0 n z = w ===> ∀ (n z w : Nat), w = k13 0 n z

/-! `Int`: `0 < a`. -/
axiom j7 : Int → Int → Int

@[blaster]
axiom j7_pos : ∀ (a z : Int), 0 < a → j7 a z = z

#testOptimize [ "ExtPosInt_1" ] (norm-result: 1) ∀ (z w : Int), j7 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtPosInt_2" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j7 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtPosInt_3" ] (norm-result: 1) ∀ (n z w : Int), 5 ≤ n → j7 n z = w ===> ∀ (n z w : Int), ¬ (n < 5) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtPosInt_4" ] (norm-result: 1) ∀ (z w : Int), j7 0 z = w ===> ∀ (z w : Int), w = j7 0 z
#testOptimize [ "ExtPosInt_5" ] (norm-result: 1) ∀ (z w : Int), j7 (-5) z = w ===> ∀ (z w : Int), w = j7 (Int.negSucc 4) z
#testOptimize [ "ExtPosInt_6" ] (norm-result: 1) ∀ (n z w : Int), j7 (n * 0) z = w ===> ∀ (z w : Int), w = j7 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtPosInt_7" ] (norm-result: 1) ∀ (n z w : Int), j7 n z = w ===> ∀ (n z w : Int), w = j7 n z
-- premise on an `Int.ofNat` argument: deciding it needs a restart pass, the generated check
-- re-optimizes the premise until no restart is pending
#testOptimize [ "ExtPosIntLift_1" ] ∀ (n : Nat), 0 < Int.ofNat (n + 1) ===> True
#testOptimize [ "ExtPosIntLift_2" ] (norm-result: 1) ∀ (n : Nat) (z w : Int), j7 (Int.ofNat (n + 1)) z = w ===> ∀ (z w : Int), z = w

/-! `Int`: `a < 0`. -/
axiom j14 : Int → Int → Int

@[blaster]
axiom j14_neg : ∀ (a z : Int), a < 0 → j14 a z = z

#testOptimize [ "ExtNegInt_1" ] (norm-result: 1) ∀ (z w : Int), j14 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNegInt_2" ] (norm-result: 1) ∀ (n z w : Int), n < -5 → j14 n z = w ===> ∀ (n z w : Int), n < Int.negSucc 4 → z = w
#testOptimize [ "ExtNegInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j14 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNegInt_4" ] (norm-result: 1) ∀ (z w : Int), j14 0 z = w ===> ∀ (z w : Int), w = j14 0 z
#testOptimize [ "ExtNegInt_5" ] (norm-result: 1) ∀ (z w : Int), j14 5 z = w ===> ∀ (z w : Int), w = j14 5 z
-- premise not established: no rewriting
#testOptimize [ "ExtNegInt_6" ] (norm-result: 1) ∀ (n z w : Int), j14 n z = w ===> ∀ (n z w : Int), w = j14 n z

/-! `Int`: `¬ (a = 0)` (normalized to `¬ (0 = a)`). -/
axiom j8 : Int → Int → Int

@[blaster]
axiom j8_nz : ∀ (a z : Int), ¬ (a = 0) → j8 a z = z

#testOptimize [ "ExtNzInt_1" ] (norm-result: 1) ∀ (z w : Int), j8 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNzInt_2" ] (norm-result: 1) ∀ (z w : Int), j8 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNzInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≠ 0 → j8 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNzInt_4" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j8 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtNzInt_5" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j8 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNzInt_6" ] (norm-result: 1) ∀ (z w : Int), j8 0 z = w ===> ∀ (z w : Int), w = j8 0 z
#testOptimize [ "ExtNzInt_7" ] (norm-result: 1) ∀ (n z w : Int), j8 (n * 0) z = w ===> ∀ (z w : Int), w = j8 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNzInt_8" ] (norm-result: 1) ∀ (n z w : Int), j8 n z = w ===> ∀ (n z w : Int), w = j8 n z

/-! `Int`: `a ≠ 0` (unfolded to `¬ (a = 0)`, then normalized to `¬ (0 = a)`). -/
axiom j15 : Int → Int → Int

@[blaster]
axiom j15_ne : ∀ (a z : Int), a ≠ 0 → j15 a z = z

#testOptimize [ "ExtNeInt_1" ] (norm-result: 1) ∀ (z w : Int), j15 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt_2" ] (norm-result: 1) ∀ (z w : Int), j15 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≠ 0 → j15 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNeInt_4" ] (norm-result: 1) ∀ (n z w : Int), ¬ (n = 0) → j15 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNeInt_5" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j15 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtNeInt_6" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j15 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeInt_7" ] (norm-result: 1) ∀ (z w : Int), j15 0 z = w ===> ∀ (z w : Int), w = j15 0 z
#testOptimize [ "ExtNeInt_8" ] (norm-result: 1) ∀ (n z w : Int), j15 (n * 0) z = w ===> ∀ (z w : Int), w = j15 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNeInt_9" ] (norm-result: 1) ∀ (n z w : Int), j15 n z = w ===> ∀ (n z w : Int), w = j15 n z

/-! `Int`: `a ≤ b` (normalized to `¬ (b < a)`). -/
axiom j9 : Int → Int → Int → Int

@[blaster]
axiom j9_le : ∀ (a b z : Int), a ≤ b → j9 a b z = z

#testOptimize [ "ExtLeInt_1" ] (norm-result: 1) ∀ (z w : Int), j9 3 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_2" ] (norm-result: 1) ∀ (z w : Int), j9 (-5) 3 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_3" ] (norm-result: 1) ∀ (z w : Int), j9 (-5) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_4" ] (norm-result: 1) ∀ (n z w : Int), j9 n n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_5" ] (norm-result: 1) ∀ (n z w : Int), j9 n (n + 1) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_6" ] (norm-result: 1) ∀ (n m z w : Int), n ≤ m → j9 n m z = w ===> ∀ (n m z w : Int), ¬ (m < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLeInt_7" ] (norm-result: 1) ∀ (z w : Int), j9 3 (-5) z = w ===> ∀ (z w : Int), w = j9 3 (Int.negSucc 4) z
#testOptimize [ "ExtLeInt_8" ] (norm-result: 1) ∀ (z w : Int), j9 5 3 z = w ===> ∀ (z w : Int), w = j9 5 3 z
#testOptimize [ "ExtLeInt_9" ] (norm-result: 1) ∀ (n z w : Int), j9 (n + 1) n z = w ===> ∀ (n z w : Int), w = j9 (Int.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLeInt_10" ] (norm-result: 1) ∀ (n m z w : Int), j9 n m z = w ===> ∀ (n m z w : Int), w = j9 n m z

/-! `Int`: `a < b`. -/
axiom j10 : Int → Int → Int → Int

@[blaster]
axiom j10_lt : ∀ (a b z : Int), a < b → j10 a b z = z

#testOptimize [ "ExtLtInt_1" ] (norm-result: 1) ∀ (z w : Int), j10 (-3) 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_2" ] (norm-result: 1) ∀ (n z w : Int), j10 n (n + 1) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_3" ] (norm-result: 1) ∀ (n z w : Int), j10 (n - 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_4" ] (norm-result: 1) ∀ (n m z w : Int), n < m → j10 n m z = w ===> ∀ (n m z w : Int), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLtInt_5" ] (norm-result: 1) ∀ (z w : Int), j10 5 5 z = w ===> ∀ (z w : Int), w = j10 5 5 z
#testOptimize [ "ExtLtInt_6" ] (norm-result: 1) ∀ (z w : Int), j10 5 (-3) z = w ===> ∀ (z w : Int), w = j10 5 (Int.negSucc 2) z
#testOptimize [ "ExtLtInt_7" ] (norm-result: 1) ∀ (n z w : Int), j10 n n z = w ===> ∀ (n z w : Int), w = j10 n n z
#testOptimize [ "ExtLtInt_8" ] (norm-result: 1) ∀ (n z w : Int), j10 (n + 1) n z = w ===> ∀ (n z w : Int), w = j10 (Int.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLtInt_9" ] (norm-result: 1) ∀ (n m z w : Int), j10 n m z = w ===> ∀ (n m z w : Int), w = j10 n m z

/-! `Int`: `a = b`. -/
axiom j11 : Int → Int → Int → Int

@[blaster]
axiom j11_eq : ∀ (a b z : Int), a = b → j11 a b z = z

#testOptimize [ "ExtEqInt_1" ] (norm-result: 1) ∀ (z w : Int), j11 (-5) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_2" ] (norm-result: 1) ∀ (n z w : Int), j11 n n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_3" ] (norm-result: 1) ∀ (n z w : Int), j11 (n + 1) (1 + n) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_4" ] (norm-result: 1) ∀ (n m z w : Int), n = m → j11 n m z = w ===> ∀ (n m z w : Int), n = m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtEqInt_5" ] (norm-result: 1) ∀ (z w : Int), j11 5 (-5) z = w ===> ∀ (z w : Int), w = j11 5 (Int.negSucc 4) z
#testOptimize [ "ExtEqInt_6" ] (norm-result: 1) ∀ (z w : Int), j11 5 6 z = w ===> ∀ (z w : Int), w = j11 5 6 z
-- premise not established: no rewriting
#testOptimize [ "ExtEqInt_7" ] (norm-result: 1) ∀ (n m z w : Int), j11 n m z = w ===> ∀ (n m z w : Int), w = j11 n m z

/-! `Int`: `a ≠ b` (unfolded to `¬ (a = b)`). -/
axiom j16 : Int → Int → Int → Int

@[blaster]
axiom j16_ne : ∀ (a b z : Int), a ≠ b → j16 a b z = z

#testOptimize [ "ExtNeInt2_1" ] (norm-result: 1) ∀ (z w : Int), j16 (-3) 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_2" ] (norm-result: 1) ∀ (z w : Int), j16 (-3) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_3" ] (norm-result: 1) ∀ (n z w : Int), j16 (n + 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_4" ] (norm-result: 1) ∀ (n z w : Int), j16 (n - 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_5" ] (norm-result: 1) ∀ (n m z w : Int), n ≠ m → j16 n m z = w ===> ∀ (n m z w : Int), ¬ (n = m) → z = w
-- `¬ (n = m)` is derived from `n < m`
#testOptimize [ "ExtNeInt2_6" ] (norm-result: 1) ∀ (n m z w : Int), n < m → j16 n m z = w ===> ∀ (n m z w : Int), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeInt2_7" ] (norm-result: 1) ∀ (z w : Int), j16 5 5 z = w ===> ∀ (z w : Int), w = j16 5 5 z
#testOptimize [ "ExtNeInt2_8" ] (norm-result: 1) ∀ (z w : Int), j16 (-5) (-5) z = w ===> ∀ (z w : Int), w = j16 (Int.negSucc 4) (Int.negSucc 4) z
#testOptimize [ "ExtNeInt2_9" ] (norm-result: 1) ∀ (n z w : Int), j16 n n z = w ===> ∀ (n z w : Int), w = j16 n n z
-- premise not established: no rewriting
#testOptimize [ "ExtNeInt2_10" ] (norm-result: 1) ∀ (n m z w : Int), j16 n m z = w ===> ∀ (n m z w : Int), w = j16 n m z

/-! `Int`: conjunction / disjunction with an evaluated conjunct / disjunct. -/
axiom j12 : Int → Int → Int → Int

@[blaster]
axiom j12_conj : ∀ (a n z : Int), 0 < a ∧ d1 n → j12 a n z = z

#testOptimize [ "ExtConjInt_1" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j12 5 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `True ∧ <missing>`: no rewriting
#testOptimize [ "ExtConjInt_2" ] (norm-result: 1) ∀ (n z w : Int), j12 5 n z = w ===> ∀ (n z w : Int), w = j12 5 n z
-- `False ∧ <hypothesis>`: no rewriting
#testOptimize [ "ExtConjInt_3" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j12 (-5) n z = w ===> ∀ (n z w : Int), d1 n → w = j12 (Int.negSucc 4) n z

axiom j13 : Int → Int → Int → Int

@[blaster]
axiom j13_disj : ∀ (a n z : Int), 0 < a ∨ d1 n → j13 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjInt_1" ] (norm-result: 1) ∀ (n z w : Int), j13 5 n z = w ===> ∀ (z w : Int), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjInt_2" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j13 0 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjInt_3" ] (norm-result: 1) ∀ (n z w : Int), j13 (-5) n z = w ===> ∀ (n z w : Int), w = j13 (Int.negSucc 4) n z

/-! `Int`: `≠` disjunct evaluated at application time. -/
axiom j17 : Int → Int → Int → Int

@[blaster]
axiom j17_disj_ne : ∀ (a n z : Int), a ≠ 0 ∨ d1 n → j17 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjNeInt_1" ] (norm-result: 1) ∀ (n z w : Int), j17 (-5) n z = w ===> ∀ (z w : Int), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjNeInt_2" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j17 0 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjNeInt_3" ] (norm-result: 1) ∀ (n z w : Int), j17 0 n z = w ===> ∀ (n z w : Int), w = j17 0 n z

/-! `tdiv_eq_ediv_of_gt_zero` (see above) applied with a literal dividend. -/
#testOptimize [ "ExtTdivEdiv_3" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv 5 b = c ===> ∀ (b c : Int), c = Int.ediv 5 b
#testOptimize [ "ExtTdivEdiv_4" ] (norm-result: 1) ∀ (a b c : Int), 5 ≤ a → Int.tdiv a b = c ===> ∀ (a b c : Int), ¬ (a < 5) → c = Int.ediv a b
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtTdivEdiv_5" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv (-5) b = c ===> ∀ (b c : Int), c = Int.tdiv (Int.negSucc 4) b
-- `Int.tdiv 0 b` is reduced to `0` natively (the rule is not involved)
#testOptimize [ "ExtTdivEdiv_6" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv 0 b = c ===> ∀ (c : Int), (0 : Int) = c

/-! ## `OfNat.ofNat` with a non-standard instance in a rule
     The optimizer only reduces `OfNat.ofNat T n inst` natively when `inst` is the standard instance of `T`;
     any other instance has to be unfolded (its value is unrelated to `n`). Theorems are normalized in
     normalize-only mode, in which functions are not unfolded: the rules are declared with `restart := true`
     so that the rewritten term goes through optimization again. These cases check that a non-standard
     instance in the lhs, the rhs or a premise of a rule is handled consistently with the normal form of
     the goal. -/

/-! Standard instance (control). -/
axiom on0 : Nat → Nat

@[blaster]
axiom on0_rhs : ∀ (n : Nat), on0 n = 7

#testOptimize [ "ExtOfNatStd_1" ] ∀ (n : Nat), on0 n = 7 ===> True
#testOptimize [ "ExtOfNatStd_2" ] (norm-result: 1) ∀ (n m : Nat), on0 n = m ===> ∀ (m : Nat), 7 = m

/-! Non-standard instance in the rhs (`Nat`). -/
axiom on1 : Nat → Nat

@[blaster (restart := true)]
axiom on1_rhs : ∀ (n : Nat), on1 n = @OfNat.ofNat Nat 7 ⟨99⟩

#testOptimize [ "ExtOfNatRhs_1" ] ∀ (n : Nat), on1 n = 99 ===> True
#testOptimize [ "ExtOfNatRhs_2" ] ∀ (n : Nat), on1 n = 7 ===> False
#testOptimize [ "ExtOfNatRhs_3" ] (norm-result: 1) ∀ (n m : Nat), on1 n = m ===> ∀ (m : Nat), 99 = m

/-! Non-standard instance in the rhs (`Int`). -/
axiom on2 : Int → Int

@[blaster (restart := true)]
axiom on2_rhs : ∀ (x : Int), on2 x = @OfNat.ofNat Int 7 ⟨99⟩

#testOptimize [ "ExtOfNatRhsInt_1" ] ∀ (x : Int), on2 x = 99 ===> True
#testOptimize [ "ExtOfNatRhsInt_2" ] ∀ (x : Int), on2 x = 7 ===> False

/-! Symbolic instance in the rhs: the payload is a pattern variable. -/
axiom on3 : Nat → Nat

@[blaster (restart := true)]
axiom on3_rhs : ∀ (i : Nat), on3 i = @OfNat.ofNat Nat 7 ⟨i + 1⟩

#testOptimize [ "ExtOfNatRhsSym_1" ] ∀ (i : Nat), on3 i = i + 1 ===> True
#testOptimize [ "ExtOfNatRhsSym_2" ] on3 4 = 5 ===> True

/-! Non-standard instance in the lhs: the goal is unfolded before the rule is tried. -/
axiom on4 : Nat → Nat

@[blaster (restart := true)]
axiom on4_lhs : ∀ (i : Nat), on4 (@OfNat.ofNat Nat 7 ⟨i⟩) = i

#testOptimize [ "ExtOfNatLhs_1" ] ∀ (i : Nat), on4 (@OfNat.ofNat Nat 7 ⟨i⟩) = i ===> True
#testOptimize [ "ExtOfNatLhs_2" ] ∀ (i : Nat), on4 i = i ===> True
#testOptimize [ "ExtOfNatLhs_3" ] on4 5 = 5 ===> True

/-! Non-standard instance in a premise (a relational premise, as an equality premise `n = c`
    substitutes `n` in the conclusion and the rule is rejected). -/
axiom on5 : Nat → Nat

@[blaster (restart := true)]
axiom on5_prem : ∀ (n : Nat), @OfNat.ofNat Nat 7 ⟨99⟩ < n → on5 n = 0

#testOptimize [ "ExtOfNatPrem_1" ] ∀ (n : Nat), 99 < n → on5 n = 0 ===> True
#testOptimize [ "ExtOfNatPrem_2" ] on5 100 = 0 ===> True
-- premise not available: no rewriting
#testOptimize [ "ExtOfNatPrem_3" ] (norm-result: 1) ∀ (n : Nat), 7 < n → on5 n = 0 ===> ∀ (n : Nat), 7 < n → 0 = on5 n

/-! Local instance in a rule: the instance is a pattern variable, the application must stay symbolic. -/
axiom on6 : Nat → Nat → Nat

@[blaster (restart := true)]
axiom on6_inst : ∀ [inst : OfNat Nat (nat_lit 7)] (n : Nat), on6 (@OfNat.ofNat Nat (nat_lit 7) inst) n = n

#testOptimize [ "ExtOfNatLocalInst_1" ] ∀ [inst : OfNat Nat (nat_lit 7)] (n : Nat), on6 (@OfNat.ofNat Nat (nat_lit 7) inst) n = n ===> True
#testOptimize [ "ExtOfNatLocalInst_2" ] ∀ (n : Nat), on6 7 n = n ===> True
-- the goal's instance `⟨99⟩` is projected before the rule is tried: the pattern variable `inst`
-- cannot match a bare literal, no rewriting
#testOptimize [ "ExtOfNatLocalInst_3" ] (norm-result: 1) ∀ (n : Nat), on6 (@OfNat.ofNat Nat 7 ⟨99⟩) n = n ===> ∀ (n : Nat), n = on6 99 n
-- no rewriting
#testOptimize [ "ExtOfNatLocalInst_4" ] (norm-result: 1) ∀ (n : Nat), on6 8 n = n ===> ∀ (n : Nat), n = on6 8 n

/-! `BitVec` literals in rules. In normalize-only mode a literal stops at `BitVec.ofNat w n` (the dedicated
    `ofNat` functions are not opaque yet), whereas the goal unfolds it down to `BitVec.ofFin w ⟨n, _⟩`:
    a rhs is recovered through `restart := true`, but a literal in the lhs does not match the goal.
    TODO: the commented test cases `ExtOfNatBitVecLhs_1` and `ExtOfNatBitVecLhs_2` will be handled
    (and must be re-enabled) once `BitVec.ofNat` is opacified: both modes will then stop at
    `BitVec.ofNat w n` and the lhs literal will match the goal. -/
axiom onb1 : BitVec 8 → BitVec 8

@[blaster (restart := true)]
axiom onb1_rhs : ∀ (x : BitVec 8), onb1 x = 99

#testOptimize [ "ExtOfNatBitVecRhs_1" ] ∀ (x : BitVec 8), onb1 x = 99 ===> True

axiom onb2 : BitVec 8 → BitVec 8

@[blaster (restart := true)]
axiom onb2_rhs : ∀ (x : BitVec 8), onb2 x = @OfNat.ofNat (BitVec 8) 7 ⟨99⟩

#testOptimize [ "ExtOfNatBitVecRhs_2" ] ∀ (x : BitVec 8), onb2 x = 99 ===> True

axiom onb3 : BitVec 8 → BitVec 8 → BitVec 8

@[blaster (restart := true)]
axiom onb3_lhs : ∀ (x : BitVec 8), onb3 99 x = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtOfNatBitVecLhs_1" ] ∀ (x : BitVec 8), onb3 99 x = x ===> True

axiom onb4 : BitVec 8 → BitVec 8 → BitVec 8

@[blaster (restart := true)]
axiom onb4_lhs : ∀ (x : BitVec 8), onb4 (@OfNat.ofNat (BitVec 8) 7 ⟨99⟩) x = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtOfNatBitVecLhs_2" ] ∀ (x : BitVec 8), onb4 99 x = x ===> True

/-! `Int` literals in rules: a non-negative literal normalizes to `Int.ofNat n` in both modes, but a
    negative literal stops at `Int.neg (Int.ofNat n)` in normalize-only mode whereas the goal reduces it
    to `Int.negSucc (n - 1)`: a negative literal in the lhs does not match the goal.
    TODO: the commented test case `ExtOfNatIntLhs_3` will be handled (and must be re-enabled) together
    with the opacification of `BitVec.ofNat`, when the literal normal forms of both modes are aligned. -/
axiom oni1 : Int → Int → Int

@[blaster]
axiom oni1_lhs : ∀ (x : Int), oni1 99 x = x

#testOptimize [ "ExtOfNatIntLhs_1" ] ∀ (x : Int), oni1 99 x = x ===> True

axiom oni2 : Int → Int → Int

@[blaster]
axiom oni2_lhs : ∀ (x : Int), oni2 (@OfNat.ofNat Int 7 ⟨99⟩) x = x

#testOptimize [ "ExtOfNatIntLhs_2" ] ∀ (x : Int), oni2 99 x = x ===> True

axiom oni3 : Int → Int → Int

@[blaster]
axiom oni3_lhs : ∀ (x : Int), oni3 (-5) x = x

#testOptimize [ "ExtOfNatIntLhs_3" ] ∀ (x : Int), oni3 (-5) x = x ===> True

axiom oni4 : Int → Int

@[blaster]
axiom oni4_rhs : ∀ (x : Int), oni4 x = -5

#testOptimize [ "ExtOfNatIntRhs_1" ] ∀ (x : Int), oni4 x = -5 ===> True

/-! ## Class functions folded in normalize-only mode (`foldableFuns`)
     Theorems are normalized in normalize-only mode, in which no function is unfolded except the class
     functions listed in `foldableFuns` (`Opaque.lean`): `Ne`, `OfNat.ofNat`, `HAdd.hAdd`, `HSub.hSub`,
     `HMul.hMul`, `HDiv.hDiv`, `HMod.hMod`, `HPow.hPow`, `Add.add`, `Sub.sub`, `Div.div`, `Mod.mod`,
     `Neg.neg`, `NatPow.pow`, `Append.append`, `HAppend.hAppend`, `GetElem?.getElem?`. An operator written
     with its class function in a rule (`n + 1`, `x / 2`, `-x`, `l ++ m`, `l[i]?`, `n ≠ 0`, ...) must reach the
     same normal form as in the goal (`Nat.add 1 n`, `Int.neg x`, `List.append l m`, `¬ (n = 0)`, ...), otherwise
     the lhs does not match and the rhs / premises are not comparable with the goal. Each operator is checked
     in the lhs, the rhs and a premise of a rule, through the heterogeneous class function (`HAdd.hAdd`, ...)
     and the homogeneous one (`Add.add`, ...). `OfNat.ofNat` is covered by the previous section.
     Rules are tried before the arguments of the application are optimized: an argument reused in the rhs
     may still be un-normalized (e.g., `OfNat.ofNat Nat 5 _`, `HAdd.hAdd … n 1`), hence rules whose rhs
     reuses an argument are declared with `restart := true` so that the rewritten term is optimized again
     (see the `ExtFoldRestart` cases). -/

/-! `HAdd.hAdd` / `Add.add` on `Nat`. -/
axiom foa1 : Nat → Nat
@[blaster]
axiom foa1_lhs : ∀ (n : Nat), foa1 (n + 1) = n

#testOptimize [ "ExtFoldNatAdd_1" ] ∀ (n : Nat), foa1 (n + 1) = n ===> True
#testOptimize [ "ExtFoldNatAdd_2" ] ∀ (n : Nat), foa1 (1 + n) = n ===> True
#testOptimize [ "ExtFoldNatAdd_3" ] ∀ (n : Nat), foa1 (Nat.add n 1) = n ===> True
-- no rewriting: the literal `5` does not match the pattern `Nat.add 1 n`
#testOptimize [ "ExtFoldNatAdd_4" ] (norm-result: 1) foa1 5 = 4 ===> 4 = foa1 5

axiom foa2 : Nat → Nat
@[blaster (restart := true)]
axiom foa2_rhs : ∀ (n : Nat), foa2 n = n + 1

#testOptimize [ "ExtFoldNatAdd_5" ] ∀ (n : Nat), foa2 n = n + 1 ===> True
#testOptimize [ "ExtFoldNatAdd_6" ] ∀ (n : Nat), foa2 n = Nat.add 1 n ===> True
#testOptimize [ "ExtFoldNatAdd_7" ] foa2 5 = 6 ===> True

axiom foa3 : Nat → Nat → Nat
@[blaster]
axiom foa3_prem : ∀ (n m : Nat), n + 1 < m → foa3 n m = n

#testOptimize [ "ExtFoldNatAdd_8" ] ∀ (n m : Nat), n + 1 < m → foa3 n m = n ===> True
#testOptimize [ "ExtFoldNatAdd_9" ] ∀ (n m : Nat), Nat.add 1 n < m → foa3 n m = n ===> True
-- premise not available: no rewriting
#testOptimize [ "ExtFoldNatAdd_10" ] (norm-result: 1) ∀ (n m : Nat), n < m → foa3 n m = n ===> ∀ (n m : Nat), n < m → n = foa3 n m

axiom foa4 : Nat → Nat
@[blaster]
axiom foa4_add : ∀ (n : Nat), foa4 (Add.add n 1) = n

#testOptimize [ "ExtFoldNatAdd_11" ] ∀ (n : Nat), foa4 (n + 1) = n ===> True

-- literals are folded on both sides: `n + 1 + 1` and `n + 2` have the same normal form
axiom foa5 : Nat → Nat
@[blaster]
axiom foa5_fold : ∀ (n : Nat), foa5 (n + 1 + 1) = n

#testOptimize [ "ExtFoldNatAdd_12" ] ∀ (n : Nat), foa5 (n + 2) = n ===> True

/-! `HSub.hSub` / `Sub.sub` on `Nat`. -/
axiom fos1 : Nat → Nat
@[blaster]
axiom fos1_lhs : ∀ (n : Nat), fos1 (n - 1) = n

#testOptimize [ "ExtFoldNatSub_1" ] ∀ (n : Nat), fos1 (n - 1) = n ===> True
#testOptimize [ "ExtFoldNatSub_2" ] ∀ (n : Nat), fos1 (Nat.sub n 1) = n ===> True

axiom fos2 : Nat → Nat
@[blaster (restart := true)]
axiom fos2_rhs : ∀ (n : Nat), fos2 n = n - 1

#testOptimize [ "ExtFoldNatSub_3" ] ∀ (n : Nat), fos2 n = n - 1 ===> True
#testOptimize [ "ExtFoldNatSub_4" ] fos2 5 = 4 ===> True

axiom fos3 : Nat → Nat → Nat
@[blaster]
axiom fos3_prem : ∀ (n m : Nat), n - 1 < m → fos3 n m = n

#testOptimize [ "ExtFoldNatSub_5" ] ∀ (n m : Nat), n - 1 < m → fos3 n m = n ===> True

axiom fos4 : Nat → Nat
@[blaster]
axiom fos4_sub : ∀ (n : Nat), fos4 (Sub.sub n 1) = n

#testOptimize [ "ExtFoldNatSub_6" ] ∀ (n : Nat), fos4 (n - 1) = n ===> True

/-! `HMul.hMul` / `Mul.mul` on `Nat`. -/
axiom fom1 : Nat → Nat
@[blaster]
axiom fom1_lhs : ∀ (n : Nat), fom1 (2 * n) = n

#testOptimize [ "ExtFoldNatMul_1" ] ∀ (n : Nat), fom1 (2 * n) = n ===> True
#testOptimize [ "ExtFoldNatMul_2" ] ∀ (n : Nat), fom1 (Nat.mul 2 n) = n ===> True

axiom fom2 : Nat → Nat
@[blaster (restart := true)]
axiom fom2_rhs : ∀ (n : Nat), fom2 n = 2 * n

#testOptimize [ "ExtFoldNatMul_3" ] ∀ (n : Nat), fom2 n = 2 * n ===> True
#testOptimize [ "ExtFoldNatMul_4" ] fom2 5 = 10 ===> True

axiom fom3 : Nat → Nat → Nat
@[blaster]
axiom fom3_prem : ∀ (n m : Nat), 2 * n < m → fom3 n m = n

#testOptimize [ "ExtFoldNatMul_5" ] ∀ (n m : Nat), 2 * n < m → fom3 n m = n ===> True

axiom fom4 : Nat → Nat
@[blaster]
axiom fom4_mul : ∀ (n : Nat), fom4 (Mul.mul 2 n) = n

#testOptimize [ "ExtFoldNatMul_6" ] ∀ (n : Nat), fom4 (2 * n) = n ===> True

/-! `HDiv.hDiv` / `Div.div` on `Nat`. -/
axiom fod1 : Nat → Nat
@[blaster]
axiom fod1_lhs : ∀ (n : Nat), fod1 (n / 2) = n

#testOptimize [ "ExtFoldNatDiv_1" ] ∀ (n : Nat), fod1 (n / 2) = n ===> True
#testOptimize [ "ExtFoldNatDiv_2" ] ∀ (n : Nat), fod1 (Nat.div n 2) = n ===> True

axiom fod2 : Nat → Nat
@[blaster (restart := true)]
axiom fod2_rhs : ∀ (n : Nat), fod2 n = n / 2

#testOptimize [ "ExtFoldNatDiv_3" ] ∀ (n : Nat), fod2 n = n / 2 ===> True
#testOptimize [ "ExtFoldNatDiv_4" ] fod2 9 = 4 ===> True

axiom fod3 : Nat → Nat → Nat
@[blaster]
axiom fod3_prem : ∀ (n m : Nat), n / 2 < m → fod3 n m = n

#testOptimize [ "ExtFoldNatDiv_5" ] ∀ (n m : Nat), n / 2 < m → fod3 n m = n ===> True

axiom fod4 : Nat → Nat
@[blaster]
axiom fod4_div : ∀ (n : Nat), fod4 (Div.div n 2) = n

#testOptimize [ "ExtFoldNatDiv_6" ] ∀ (n : Nat), fod4 (n / 2) = n ===> True

/-! `HMod.hMod` / `Mod.mod` on `Nat`. -/
axiom foo1 : Nat → Nat
@[blaster]
axiom foo1_lhs : ∀ (n : Nat), foo1 (n % 2) = n

#testOptimize [ "ExtFoldNatMod_1" ] ∀ (n : Nat), foo1 (n % 2) = n ===> True
#testOptimize [ "ExtFoldNatMod_2" ] ∀ (n : Nat), foo1 (Nat.mod n 2) = n ===> True

axiom foo2 : Nat → Nat
@[blaster (restart := true)]
axiom foo2_rhs : ∀ (n : Nat), foo2 n = n % 2

#testOptimize [ "ExtFoldNatMod_3" ] ∀ (n : Nat), foo2 n = n % 2 ===> True
#testOptimize [ "ExtFoldNatMod_4" ] foo2 9 = 1 ===> True

axiom foo3 : Nat → Nat → Nat
@[blaster]
axiom foo3_prem : ∀ (n m : Nat), 0 < n % 2 → foo3 n m = n

#testOptimize [ "ExtFoldNatMod_5" ] ∀ (n m : Nat), 0 < n % 2 → foo3 n m = n ===> True

axiom foo4 : Nat → Nat
@[blaster]
axiom foo4_mod : ∀ (n : Nat), foo4 (Mod.mod n 2) = n

#testOptimize [ "ExtFoldNatMod_6" ] ∀ (n : Nat), foo4 (n % 2) = n ===> True

/-! `HPow.hPow` / `Pow.pow` / `NatPow.pow` on `Nat` (`n ^ 2` unfolds through `instHPow`, `instPowNat` and
    `instNatPowNat`, i.e. `HPow.hPow` ↦ `Pow.pow` ↦ `NatPow.pow` ↦ `Nat.pow`). -/
axiom fop1 : Nat → Nat
@[blaster]
axiom fop1_lhs : ∀ (n : Nat), fop1 (n ^ 2) = n

#testOptimize [ "ExtFoldNatPow_1" ] ∀ (n : Nat), fop1 (n ^ 2) = n ===> True
#testOptimize [ "ExtFoldNatPow_2" ] ∀ (n : Nat), fop1 (Nat.pow n 2) = n ===> True

axiom fop2 : Nat → Nat
@[blaster (restart := true)]
axiom fop2_rhs : ∀ (n : Nat), fop2 n = n ^ 2

#testOptimize [ "ExtFoldNatPow_3" ] ∀ (n : Nat), fop2 n = n ^ 2 ===> True
#testOptimize [ "ExtFoldNatPow_4" ] fop2 3 = 9 ===> True

axiom fop3 : Nat → Nat
@[blaster]
axiom fop3_pow : ∀ (n : Nat), fop3 (Pow.pow n 2) = n

#testOptimize [ "ExtFoldNatPow_5" ] ∀ (n : Nat), fop3 (n ^ 2) = n ===> True

axiom fop4 : Nat → Nat
@[blaster]
axiom fop4_natpow : ∀ (n : Nat), fop4 (NatPow.pow n 2) = n

#testOptimize [ "ExtFoldNatPow_6" ] ∀ (n : Nat), fop4 (n ^ 2) = n ===> True

/-! Several operators in a single rule. -/
axiom fox1 : Nat → Nat → Nat
@[blaster]
axiom fox1_mixed : ∀ (n m : Nat), fox1 (n + m) (n - m) = (n + m) / 2 % 7

#testOptimize [ "ExtFoldNatMixed_1" ] ∀ (n m : Nat), fox1 (n + m) (n - m) = (n + m) / 2 % 7 ===> True
#testOptimize [ "ExtFoldNatMixed_2" ] ∀ (n m : Nat), fox1 (m + n) (n - m) = Nat.mod (Nat.div (Nat.add n m) 2) 7 ===> True

/-! `HAdd.hAdd` on `Int`. -/
axiom fia1 : Int → Int
@[blaster]
axiom fia1_lhs : ∀ (x : Int), fia1 (x + 1) = x

#testOptimize [ "ExtFoldIntAdd_1" ] ∀ (x : Int), fia1 (x + 1) = x ===> True
#testOptimize [ "ExtFoldIntAdd_2" ] ∀ (x : Int), fia1 (Int.add x 1) = x ===> True

axiom fia2 : Int → Int
@[blaster (restart := true)]
axiom fia2_rhs : ∀ (x : Int), fia2 x = x + 1

#testOptimize [ "ExtFoldIntAdd_3" ] ∀ (x : Int), fia2 x = x + 1 ===> True
#testOptimize [ "ExtFoldIntAdd_4" ] fia2 5 = 6 ===> True

axiom fia3 : Int → Int → Int
@[blaster]
axiom fia3_prem : ∀ (x y : Int), x + 1 < y → fia3 x y = x

#testOptimize [ "ExtFoldIntAdd_5" ] ∀ (x y : Int), x + 1 < y → fia3 x y = x ===> True

/-! `HSub.hSub` on `Int`: `Int.sub` is unfolded to `Int.add x (Int.neg y)` in the goal. -/
axiom fis1 : Int → Int
@[blaster]
axiom fis1_lhs : ∀ (x : Int), fis1 (x - 1) = x

#testOptimize [ "ExtFoldIntSub_1" ] ∀ (x : Int), fis1 (x - 1) = x ===> True

axiom fis2 : Int → Int
@[blaster (restart := true)]
axiom fis2_rhs : ∀ (x : Int), fis2 x = x - 1

#testOptimize [ "ExtFoldIntSub_2" ] ∀ (x : Int), fis2 x = x - 1 ===> True
#testOptimize [ "ExtFoldIntSub_3" ] fis2 5 = 4 ===> True

axiom fis3 : Int → Int → Int
@[blaster]
axiom fis3_prem : ∀ (x y : Int), x - 1 < y → fis3 x y = x

#testOptimize [ "ExtFoldIntSub_4" ] ∀ (x y : Int), x - 1 < y → fis3 x y = x ===> True

/-! `HMul.hMul` on `Int`. -/
axiom fim1 : Int → Int
@[blaster]
axiom fim1_lhs : ∀ (x : Int), fim1 (2 * x) = x

#testOptimize [ "ExtFoldIntMul_1" ] ∀ (x : Int), fim1 (2 * x) = x ===> True

axiom fim2 : Int → Int
@[blaster (restart := true)]
axiom fim2_rhs : ∀ (x : Int), fim2 x = 2 * x

#testOptimize [ "ExtFoldIntMul_2" ] ∀ (x : Int), fim2 x = 2 * x ===> True
#testOptimize [ "ExtFoldIntMul_3" ] fim2 5 = 10 ===> True

/-! `HDiv.hDiv` / `HMod.hMod` on `Int`. -/
axiom fid1 : Int → Int
@[blaster]
axiom fid1_lhs : ∀ (x : Int), fid1 (x / 2) = x

#testOptimize [ "ExtFoldIntDiv_1" ] ∀ (x : Int), fid1 (x / 2) = x ===> True

axiom fid2 : Int → Int
@[blaster (restart := true)]
axiom fid2_rhs : ∀ (x : Int), fid2 x = x / 2

#testOptimize [ "ExtFoldIntDiv_2" ] ∀ (x : Int), fid2 x = x / 2 ===> True
#testOptimize [ "ExtFoldIntDiv_3" ] fid2 9 = 4 ===> True

axiom fid3 : Int → Int → Int
@[blaster]
axiom fid3_prem : ∀ (x y : Int), x / 2 < y → fid3 x y = x

#testOptimize [ "ExtFoldIntDiv_4" ] ∀ (x y : Int), x / 2 < y → fid3 x y = x ===> True

axiom fio1 : Int → Int
@[blaster]
axiom fio1_lhs : ∀ (x : Int), fio1 (x % 2) = x

#testOptimize [ "ExtFoldIntMod_1" ] ∀ (x : Int), fio1 (x % 2) = x ===> True

axiom fio2 : Int → Int
@[blaster (restart := true)]
axiom fio2_rhs : ∀ (x : Int), fio2 x = x % 2

#testOptimize [ "ExtFoldIntMod_2" ] ∀ (x : Int), fio2 x = x % 2 ===> True
#testOptimize [ "ExtFoldIntMod_3" ] fio2 9 = 1 ===> True

axiom fio3 : Int → Int → Int
@[blaster]
axiom fio3_prem : ∀ (x y : Int), x % 2 < y → fio3 x y = x

#testOptimize [ "ExtFoldIntMod_4" ] ∀ (x y : Int), x % 2 < y → fio3 x y = x ===> True

/-! `HPow.hPow` on `Int` (`Int.pow`). -/
axiom fip1 : Int → Int
@[blaster]
axiom fip1_lhs : ∀ (x : Int), fip1 (x ^ 2) = x

#testOptimize [ "ExtFoldIntPow_1" ] ∀ (x : Int), fip1 (x ^ 2) = x ===> True

axiom fip2 : Int → Int
@[blaster (restart := true)]
axiom fip2_rhs : ∀ (x : Int), fip2 x = x ^ 2

#testOptimize [ "ExtFoldIntPow_2" ] ∀ (x : Int), fip2 x = x ^ 2 ===> True

/-! `Neg.neg` on `Int`. -/
axiom fin1 : Int → Int
@[blaster]
axiom fin1_lhs : ∀ (x : Int), fin1 (-x) = x

#testOptimize [ "ExtFoldIntNeg_1" ] ∀ (x : Int), fin1 (-x) = x ===> True
#testOptimize [ "ExtFoldIntNeg_2" ] ∀ (x : Int), fin1 (Int.neg x) = x ===> True

axiom fin2 : Int → Int
@[blaster (restart := true)]
axiom fin2_rhs : ∀ (x : Int), fin2 x = -x

#testOptimize [ "ExtFoldIntNeg_3" ] ∀ (x : Int), fin2 x = -x ===> True
#testOptimize [ "ExtFoldIntNeg_4" ] fin2 5 = -5 ===> True

axiom fin3 : Int → Int → Int
@[blaster]
axiom fin3_prem : ∀ (x y : Int), -x < y → fin3 x y = x

#testOptimize [ "ExtFoldIntNeg_5" ] ∀ (x y : Int), -x < y → fin3 x y = x ===> True

axiom fin4 : Int → Int
@[blaster]
axiom fin4_neg : ∀ (x : Int), fin4 (Neg.neg x) = x

#testOptimize [ "ExtFoldIntNeg_6" ] ∀ (x : Int), fin4 (-x) = x ===> True

/-! `HAppend.hAppend` / `Append.append` on `List` and `String`. -/
axiom fol1 : List Nat → Nat
@[blaster]
axiom fol1_lhs : ∀ (l : List Nat) (a : Nat), fol1 (l ++ [a]) = a

#testOptimize [ "ExtFoldListApp_1" ] ∀ (l : List Nat) (a : Nat), fol1 (l ++ [a]) = a ===> True
#testOptimize [ "ExtFoldListApp_2" ] ∀ (l : List Nat) (a : Nat), fol1 (List.append l [a]) = a ===> True

axiom fol2 : List Nat → List Nat
@[blaster (restart := true)]
axiom fol2_rhs : ∀ (l : List Nat), fol2 l = l ++ [0]

#testOptimize [ "ExtFoldListApp_3" ] ∀ (l : List Nat), fol2 l = l ++ [0] ===> True
#testOptimize [ "ExtFoldListApp_4" ] fol2 [1] = [1, 0] ===> True

axiom fol3 : List Nat → List Nat → Nat
@[blaster]
axiom fol3_prem : ∀ (l m : List Nat), l ++ m = [] → fol3 l m = 0

#testOptimize [ "ExtFoldListApp_5" ] ∀ (l m : List Nat), l ++ m = [] → fol3 l m = 0 ===> True

axiom fol4 : List Nat → Nat
@[blaster]
axiom fol4_app : ∀ (l : List Nat) (a : Nat), fol4 (Append.append l [a]) = a

#testOptimize [ "ExtFoldListApp_6" ] ∀ (l : List Nat) (a : Nat), fol4 (l ++ [a]) = a ===> True

axiom fost1 : String → Nat
@[blaster]
axiom fost1_lhs : ∀ (s : String), fost1 (s ++ "a") = 0

#testOptimize [ "ExtFoldStrApp_1" ] ∀ (s : String), fost1 (s ++ "a") = 0 ===> True

axiom fost2 : String → String
@[blaster (restart := true)]
axiom fost2_rhs : ∀ (s : String), fost2 s = s ++ "a"

#testOptimize [ "ExtFoldStrApp_2" ] ∀ (s : String), fost2 s = s ++ "a" ===> True
#testOptimize [ "ExtFoldStrApp_3" ] fost2 "b" = "ba" ===> True

/-! `GetElem?.getElem?` on `List`. -/
axiom fog1 : Option Nat → Nat
@[blaster]
axiom fog1_lhs : ∀ (l : List Nat) (i : Nat), fog1 l[i]? = i

#testOptimize [ "ExtFoldGetElem_1" ] ∀ (l : List Nat) (i : Nat), fog1 l[i]? = i ===> True

axiom fog2 : List Nat → Nat → Option Nat
@[blaster (restart := true)]
axiom fog2_rhs : ∀ (l : List Nat) (i : Nat), fog2 l i = l[i]?

#testOptimize [ "ExtFoldGetElem_2" ] ∀ (l : List Nat) (i : Nat), fog2 l i = l[i]? ===> True
#testOptimize [ "ExtFoldGetElem_3" ] ∀ (a : Nat) (l : List Nat), fog2 (a :: l) 0 = some a ===> True
#testOptimize [ "ExtFoldGetElem_4" ] ∀ (i : Nat), fog2 [] i = none ===> True

axiom fog3 : List Nat → Nat → Nat
@[blaster]
axiom fog3_prem : ∀ (l : List Nat) (i : Nat), l[i]? = none → fog3 l i = 0

#testOptimize [ "ExtFoldGetElem_5" ] ∀ (l : List Nat) (i : Nat), l[i]? = none → fog3 l i = 0 ===> True

/-! `Ne` as an argument and in an `Iff` rhs (premises and conclusions with `≠` are covered above). -/
axiom fone1 : Prop → Nat
@[blaster]
axiom fone1_lhs : ∀ (n : Nat), fone1 (n ≠ 0) = n

#testOptimize [ "ExtFoldNe_1" ] ∀ (n : Nat), fone1 (n ≠ 0) = n ===> True
#testOptimize [ "ExtFoldNe_2" ] ∀ (n : Nat), fone1 (¬ (n = 0)) = n ===> True
#testOptimize [ "ExtFoldNe_3" ] ∀ (n : Nat), fone1 (0 < n) = n ===> True

axiom fone2 : Nat → Prop
@[blaster (restart := true)]
axiom fone2_iff : ∀ (n : Nat), fone2 n ↔ n ≠ 0

#testOptimize [ "ExtFoldNe_4" ] ∀ (n : Nat), fone2 n ↔ 0 < n ===> True
#testOptimize [ "ExtFoldNe_5" ] ∀ (n : Nat), fone2 (n + 1) ===> True

axiom fone3 : Int → Prop
@[blaster]
axiom fone3_iff : ∀ (x : Int), fone3 x ↔ x ≠ 0

#testOptimize [ "ExtFoldNe_6" ] ∀ (x : Int), fone3 x ↔ ¬ (0 = x) ===> True

/-! Rules are tried before the arguments of the application are optimized and, without `restart`, the
    rewritten term is not optimized again: a literal argument reused in the rhs would stay un-normalized
    (`Nat.sub (OfNat.ofNat Nat 5 _) 1`, `0 < HAdd.hAdd … n 1`). With `restart := true` the rewritten term
    is normalized (`fonr1 5 = 4` and `fonr2 (n + 1)` reduce to `True`). -/
axiom fonr1 : Nat → Nat
@[blaster (restart := true)]
axiom fonr1_rhs : ∀ (n : Nat), fonr1 n = n - 1

#testOptimize [ "ExtFoldRestart_1" ] ∀ (n : Nat), fonr1 n = n - 1 ===> True
#testOptimize [ "ExtFoldRestart_2" ] fonr1 5 = 4 ===> True

axiom fonr2 : Nat → Prop
@[blaster (restart := true)]
axiom fonr2_iff : ∀ (n : Nat), fonr2 n ↔ n ≠ 0

#testOptimize [ "ExtFoldRestart_3" ] ∀ (n : Nat), fonr2 n ↔ 0 < n ===> True
#testOptimize [ "ExtFoldRestart_4" ] ∀ (n : Nat), fonr2 (n + 1) ===> True

/-! `HAdd.hAdd` on `UInt8`: the goal unfolds `UInt8.add` down to `UInt8.ofBitVec (BitVec.ofFin 8 ⟨_, _⟩)`
    whereas the rule stops at `UInt8.add x (UInt8.ofNat 1)` in normalize-only mode.
    TODO: to be handled (and re-enabled) together with the opacification of `BitVec.ofNat`. -/
axiom fou1 : UInt8 → UInt8
@[blaster]
axiom fou1_lhs : ∀ (x : UInt8), fou1 (x + 1) = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtFoldUInt8Add_1" ] ∀ (x : UInt8), fou1 (x + 1) = x ===> True

axiom fou2 : UInt8 → UInt8
@[blaster (restart := true)]
axiom fou2_rhs : ∀ (x : UInt8), fou2 x = x + 1

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtFoldUInt8Add_2" ] ∀ (x : UInt8), fou2 x = x + 1 ===> True

end Test.Extension
