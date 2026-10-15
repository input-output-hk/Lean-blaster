import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.DerivedFacts
/-! ## Test objectives to validate the facts derived from hypotheses (see `addHypotheses`)

When a hypothesis `h : e` is added to the hypothesis map, additional facts entailed by `e` are
added as well (forward derivation). A fact is observable when a conclusion stating it is reduced
to `True`. Each section also contains cases where a fact that is *not* entailed is left untouched
(a conclusion `c` that is not entailed is kept, or the statement is reduced to `… → ¬c` when the
conclusion is contradicted by the hypothesis).
-/

/-! ### Conjunction `a ∧ b`: both `a` and `b` are added (recursively). -/

-- (a ∧ b) → c → a ===> True
#testOptimize [ "DerivedAnd_1" ] ∀ (a b c : Prop), (a ∧ b) → c → a ===> True

-- (a ∧ b) → c → b ===> True
#testOptimize [ "DerivedAnd_2" ] ∀ (a b c : Prop), (a ∧ b) → c → b ===> True

-- (a ∧ (b ∧ c)) → c ===> True
#testOptimize [ "DerivedAnd_3" ] ∀ (a b c : Prop), (a ∧ (b ∧ c)) → c ===> True

-- ((a ∧ b) ∧ c) → b ===> True
#testOptimize [ "DerivedAnd_4" ] ∀ (a b c : Prop), ((a ∧ b) ∧ c) → b ===> True

-- (a ∧ b) → c ===> (a ∧ b) → c
#testOptimize [ "DerivedAnd_5" ] ∀ (a b c : Prop), (a ∧ b) → c ===> ∀ (a b c : Prop), (a ∧ b) → c


/-! ### Negated disjunction `¬ (a ∨ b)`: both `¬ a` and `¬ b` are added (recursively). -/

-- ¬ (a ∨ b) → c → ¬ a ===> True
#testOptimize [ "DerivedNotOr_1" ] ∀ (a b c : Prop), ¬ (a ∨ b) → c → ¬ a ===> True

-- ¬ (a ∨ b) → ¬ b ===> True
#testOptimize [ "DerivedNotOr_2" ] ∀ (a b : Prop), ¬ (a ∨ b) → ¬ b ===> True

-- ¬ (a ∨ (b ∨ c)) → ¬ c ===> True
#testOptimize [ "DerivedNotOr_3" ] ∀ (a b c : Prop), ¬ (a ∨ (b ∨ c)) → ¬ c ===> True

-- ¬ ((a ∧ b) ∨ c) → ¬ (a ∧ b) ===> True
#testOptimize [ "DerivedNotOr_4" ] ∀ (a b c : Prop), ¬ ((a ∧ b) ∨ c) → ¬ (a ∧ b) ===> True

-- (¬ (a ∨ b) ∧ c) → ¬ a ===> True
#testOptimize [ "DerivedNotOr_5" ] ∀ (a b c : Prop), (¬ (a ∨ b) ∧ c) → ¬ a ===> True

-- ¬ (a ∨ b) → a ===> a ∨ b
-- NOTE: `¬ a` is in the hypothesis map, hence `a` is reduced to `False` and `¬ (a ∨ b) → False` to `a ∨ b`
#testOptimize [ "DerivedNotOr_6" ] ∀ (a b : Prop), ¬ (a ∨ b) → a ===> ∀ (a b : Prop), a ∨ b

-- ¬ (a ∨ b) → c ===> ¬ (a ∨ b) → c
#testOptimize [ "DerivedNotOr_7" ] ∀ (a b c : Prop), ¬ (a ∨ b) → c ===> ∀ (a b c : Prop), ¬ (a ∨ b) → c


/-! ### Negation facts (`addNotPropFacts`):
     - `¬ (false = e)` adds `true = e`;  `¬ (true = e)` adds `false = e` (with Type(e) = Bool)
     - `true = e` adds `¬ (false = e)`;  `false = e` adds `¬ (true = e)` (with Type(e) = Bool)
     - `¬ (¬ a)` adds `a`
     - `¬ (0 < n)` adds `0 = n`;  `¬ (0 = n)` adds `0 < n` (with Type(n) = Nat)
     - `¬ (n < N)` with `N ≠ 0` adds `0 < n` and `¬ (0 = n)` (with Type(n) = Nat)
     - `¬ (a < N)` with `N > 0` adds `0 < a`, `¬ (0 = a)` and `¬ (a < 0)` (with Type(a) = Int)
     - `¬ (N < a)` with `N < 0` adds `a < 0`, `¬ (0 = a)` and `¬ (0 < a)` (with Type(a) = Int)
     Note that `a ≤ b` is normalized to `¬ (b < a)` and `a ≥ b` to `¬ (a < b)`, so the last three
     cases cover the sign information given by non-strict bounds (`5 ≤ a`, `a ≤ -5`, `a ≥ 5`).
-/

-- ¬ (false = a) → c → true = a ===> True
#testOptimize [ "DerivedNot_1" ] ∀ (a : Bool) (c : Prop), ¬ (false = a) → c → true = a ===> True

-- ¬ (true = a) → c → false = a ===> True
#testOptimize [ "DerivedNot_2" ] ∀ (a : Bool) (c : Prop), ¬ (true = a) → c → false = a ===> True

-- ¬ (a = false) → c → a = true ===> True
#testOptimize [ "DerivedNot_3" ] ∀ (a : Bool) (c : Prop), ¬ (a = false) → c → a = true ===> True

-- true = a → c → ¬ (false = a) ===> True
#testOptimize [ "DerivedNot_4" ] ∀ (a : Bool) (c : Prop), true = a → c → ¬ (false = a) ===> True

-- false = a → c → ¬ (true = a) ===> True
#testOptimize [ "DerivedNot_5" ] ∀ (a : Bool) (c : Prop), false = a → c → ¬ (true = a) ===> True

-- a → c → ¬ (a = false) ===> True (with Type(a) = Bool)
#testOptimize [ "DerivedNot_6" ] ∀ (a : Bool) (c : Prop), a → c → ¬ (a = false) ===> True

-- (!a) → c → ¬ (a = true) ===> True (with Type(a) = Bool)
#testOptimize [ "DerivedNot_7" ] ∀ (a : Bool) (c : Prop), (!a) → c → ¬ (a = true) ===> True

-- ¬ (¬ a) → b → a ===> True
#testOptimize [ "DerivedNot_8" ] ∀ (a b : Prop), ¬ (¬ a) → b → a ===> True

-- ¬ (¬ (a ∧ b)) → a ===> True
#testOptimize [ "DerivedNot_9" ] ∀ (a b : Prop), ¬ (¬ (a ∧ b)) → a ===> True

-- ¬ (0 < n) → c → 0 = n ===> True
#testOptimize [ "DerivedNot_10" ] ∀ (n : Nat) (c : Prop), ¬ (0 < n) → c → 0 = n ===> True

-- ¬ (0 < n) → n + m = m ===> True
#testOptimize [ "DerivedNot_11" ] ∀ (n m : Nat), ¬ (0 < n) → n + m = m ===> True

-- ¬ (0 = n) → c → 0 < n ===> True
#testOptimize [ "DerivedNot_12" ] ∀ (n : Nat) (c : Prop), ¬ (0 = n) → c → 0 < n ===> True

-- n ≠ 0 → c → 0 < n ===> True
#testOptimize [ "DerivedNot_13" ] ∀ (n : Nat) (c : Prop), n ≠ 0 → c → 0 < n ===> True

-- ¬ (0 = n) → c → n = 0 ===> 0 < n → ¬ c
#testOptimize [ "DerivedNot_14" ] (norm-result: 1)
  ∀ (n : Nat) (c : Prop), ¬ (0 = n) → c → n = 0 ===> ∀ (n : Nat) (c : Prop), 0 < n → ¬ c

-- ¬ (n < 5) → c → 0 < n ===> True  (Nat, N ≠ 0)
#testOptimize [ "DerivedNot_15" ] ∀ (n : Nat) (c : Prop), ¬ (n < 5) → c → 0 < n ===> True

-- ¬ (n < 5) → c → ¬ (0 = n) ===> True
#testOptimize [ "DerivedNot_16" ] ∀ (n : Nat) (c : Prop), ¬ (n < 5) → c → ¬ (0 = n) ===> True

-- 5 ≤ n → c → 0 < n ===> True  (`5 ≤ n` is normalized to `¬ (n < 5)`)
#testOptimize [ "DerivedNot_17" ] ∀ (n : Nat) (c : Prop), 5 ≤ n → c → 0 < n ===> True

-- n ≥ 5 → c → n ≠ 0 ===> True
#testOptimize [ "DerivedNot_18" ] ∀ (n : Nat) (c : Prop), n ≥ 5 → c → n ≠ 0 ===> True

-- 1 ≤ n → c → 0 < n ===> True
#testOptimize [ "DerivedNot_19" ] ∀ (n : Nat) (c : Prop), 1 ≤ n → c → 0 < n ===> True

-- ¬ (n < 5) → n / n = 1 ===> True
-- NOTE: `n / n = 1` requires `¬ (0 = n)`, derived from `¬ (n < 5)`
#testOptimize [ "DerivedNot_20" ] ∀ (n : Nat), ¬ (n < 5) → n / n = 1 ===> True

-- 5 ≤ n → m < m + n ===> True
#testOptimize [ "DerivedNot_21" ] ∀ (n m : Nat), 5 ≤ n → m < m + n ===> True

-- ¬ (c ∨ n < 5) → 0 < n ===> True
#testOptimize [ "DerivedNot_22" ] ∀ (n : Nat) (c : Prop), ¬ (c ∨ n < 5) → 0 < n ===> True

-- ¬ (n < 5) → c → n = 0 ===> ¬ (n < 5) → ¬ c
#testOptimize [ "DerivedNot_23" ] (norm-result: 1)
  ∀ (n : Nat) (c : Prop), ¬ (n < 5) → c → n = 0 ===> ∀ (n : Nat) (c : Prop), ¬ (n < 5) → ¬ c

-- ¬ (n < 0) → c → 0 < n ===> c → 0 < n  (no derivation when N = 0: `¬ (n < 0)` is simply `True`)
#testOptimize [ "DerivedNot_24" ] (norm-result: 1)
  ∀ (n : Nat) (c : Prop), ¬ (n < 0) → c → 0 < n ===> ∀ (n : Nat) (c : Prop), c → 0 < n

-- ¬ (5 < n) → c → 0 < n ===> ¬ (5 < n) → c → 0 < n  (no derivation from an upper bound)
#testOptimize [ "DerivedNot_25" ] (norm-result: 1)
  ∀ (n : Nat) (c : Prop), ¬ (5 < n) → c → 0 < n ===> ∀ (n : Nat) (c : Prop), ¬ (5 < n) → c → 0 < n

-- ¬ (c ∨ n < 0) → 0 < n ===> ¬ c → 0 < n  (no derivation when N = 0)
#testOptimize [ "DerivedNot_26" ] (norm-result: 1)
  ∀ (n : Nat) (c : Prop), ¬ (c ∨ n < 0) → 0 < n ===> ∀ (n : Nat) (c : Prop), ¬ c → 0 < n

-- ¬ (a < 5) → c → 0 < a ===> True  (Int, N > 0)
#testOptimize [ "DerivedNot_27" ] ∀ (a : Int) (c : Prop), ¬ (a < 5) → c → 0 < a ===> True

-- ¬ (a < 5) → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedNot_28" ] ∀ (a : Int) (c : Prop), ¬ (a < 5) → c → ¬ (0 = a) ===> True

-- ¬ (a < 5) → c → ¬ (a < 0) ===> True
#testOptimize [ "DerivedNot_29" ] ∀ (a : Int) (c : Prop), ¬ (a < 5) → c → ¬ (a < 0) ===> True

-- 5 ≤ a → c → 0 ≤ a ===> True
#testOptimize [ "DerivedNot_30" ] ∀ (a : Int) (c : Prop), 5 ≤ a → c → 0 ≤ a ===> True

-- a ≥ 5 → c → a ≠ 0 ===> True
#testOptimize [ "DerivedNot_31" ] ∀ (a : Int) (c : Prop), a ≥ 5 → c → a ≠ 0 ===> True

-- 1 ≤ a → c → 0 < a ===> True
#testOptimize [ "DerivedNot_32" ] ∀ (a : Int) (c : Prop), 1 ≤ a → c → 0 < a ===> True

-- ¬ (-5 < a) → c → a < 0 ===> True  (Int, N < 0)
#testOptimize [ "DerivedNot_33" ] ∀ (a : Int) (c : Prop), ¬ (-5 < a) → c → a < 0 ===> True

-- ¬ (-5 < a) → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedNot_34" ] ∀ (a : Int) (c : Prop), ¬ (-5 < a) → c → ¬ (0 = a) ===> True

-- ¬ (-5 < a) → c → ¬ (0 < a) ===> True
#testOptimize [ "DerivedNot_35" ] ∀ (a : Int) (c : Prop), ¬ (-5 < a) → c → ¬ (0 < a) ===> True

-- a ≤ -5 → c → a ≤ 0 ===> True
#testOptimize [ "DerivedNot_36" ] ∀ (a : Int) (c : Prop), a ≤ -5 → c → a ≤ 0 ===> True

-- a ≤ -1 → c → a ≠ 0 ===> True
#testOptimize [ "DerivedNot_37" ] ∀ (a : Int) (c : Prop), a ≤ -1 → c → a ≠ 0 ===> True

-- ¬ (a < 5) → a / a = 1 ===> True
#testOptimize [ "DerivedNot_38" ] ∀ (a : Int), ¬ (a < 5) → a / a = 1 ===> True

-- a ≤ -5 → a / a = 1 ===> True
#testOptimize [ "DerivedNot_39" ] ∀ (a : Int), a ≤ -5 → a / a = 1 ===> True

-- 5 ≤ a → 6 ≤ b → 0 < a + b ===> True
#testOptimize [ "DerivedNot_40" ] ∀ (a b : Int), 5 ≤ a → 6 ≤ b → 0 < a + b ===> True

-- a ≤ -5 → b ≤ -6 → a + b ≤ 0 ===> True
#testOptimize [ "DerivedNot_41" ] ∀ (a b : Int), a ≤ -5 → b ≤ -6 → a + b ≤ 0 ===> True

-- ¬ (c ∨ a < 5) → 0 < a ===> True
#testOptimize [ "DerivedNot_42" ] ∀ (a : Int) (c : Prop), ¬ (c ∨ a < 5) → 0 < a ===> True

-- ¬ (c ∨ -5 < a) → a < 0 ===> True
#testOptimize [ "DerivedNot_43" ] ∀ (a : Int) (c : Prop), ¬ (c ∨ -5 < a) → a < 0 ===> True

-- ¬ (a < 5) → c → a = 0 ===> ¬ (a < 5) → ¬ c
#testOptimize [ "DerivedNot_44" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (a < 5) → c → a = 0 ===> ∀ (a : Int) (c : Prop), ¬ (a < 5) → ¬ c

-- a ≤ -5 → c → 0 ≤ a ===> ¬ (-5 < a) → ¬ c
#testOptimize [ "DerivedNot_45" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), a ≤ -5 → c → 0 ≤ a ===> ∀ (a : Int) (c : Prop), ¬ (Int.negSucc 4 < a) → ¬ c

-- ¬ (a < 5) → c → a < 0 ===> ¬ (a < 5) → ¬ c
#testOptimize [ "DerivedNot_46" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (a < 5) → c → a < 0 ===> ∀ (a : Int) (c : Prop), ¬ (a < 5) → ¬ c

-- ¬ (a < 0) → c → 0 < a ===> ¬ (a < 0) → c → 0 < a  (no derivation when N ≤ 0)
#testOptimize [ "DerivedNot_47" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (a < 0) → c → 0 < a ===> ∀ (a : Int) (c : Prop), ¬ (a < 0) → c → 0 < a

-- ¬ (a < -5) → c → 0 < a ===> ¬ (a < -5) → c → 0 < a  (no derivation when N ≤ 0)
#testOptimize [ "DerivedNot_48" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (a < -5) → c → 0 < a ===> ∀ (a : Int) (c : Prop), ¬ (a < Int.negSucc 4) → c → 0 < a

-- ¬ (0 < a) → c → a < 0 ===> ¬ (0 < a) → c → a < 0  (no derivation when N ≥ 0)
#testOptimize [ "DerivedNot_49" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (0 < a) → c → a < 0 ===> ∀ (a : Int) (c : Prop), ¬ (0 < a) → c → a < 0

-- ¬ (5 < a) → c → a < 0 ===> ¬ (5 < a) → c → a < 0  (no derivation when N ≥ 0)
#testOptimize [ "DerivedNot_50" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), ¬ (5 < a) → c → a < 0 ===> ∀ (a : Int) (c : Prop), ¬ (5 < a) → c → a < 0


/-! ### Int relational facts (`addRelIntFacts`): when `a < b` (with Type(a) = Int)
     - `¬ (b < a)` and `¬ (a = b)` (or `¬ (b = a)`) are added
     - when `N < a` with `N > 0`: `¬ (0 = a)`, `0 < a` and `¬ (a < 0)` are added
     - when `a < N` with `N < 0`: `¬ (0 = a)`, `a < 0` and `¬ (0 < a)` are added
-/

-- a < b → c → ¬ (b < a) ===> True
#testOptimize [ "DerivedRelInt_1" ] ∀ (a b : Int) (c : Prop), a < b → c → ¬ (b < a) ===> True

-- a < b → c → a ≤ b ===> True
#testOptimize [ "DerivedRelInt_2" ] ∀ (a b : Int) (c : Prop), a < b → c → a ≤ b ===> True

-- a < b → c → ¬ (a = b) ===> True
#testOptimize [ "DerivedRelInt_3" ] ∀ (a b : Int) (c : Prop), a < b → c → ¬ (a = b) ===> True

-- a < b → c → ¬ (b = a) ===> True
#testOptimize [ "DerivedRelInt_4" ] ∀ (a b : Int) (c : Prop), a < b → c → ¬ (b = a) ===> True

-- a < b → c → a ≠ b ===> True
#testOptimize [ "DerivedRelInt_5" ] ∀ (a b : Int) (c : Prop), a < b → c → a ≠ b ===> True

-- 5 < a → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedRelInt_6" ] ∀ (a : Int) (c : Prop), 5 < a → c → ¬ (0 = a) ===> True

-- 5 < a → c → 0 < a ===> True
#testOptimize [ "DerivedRelInt_7" ] ∀ (a : Int) (c : Prop), 5 < a → c → 0 < a ===> True

-- a < -5 → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedRelInt_8" ] ∀ (a : Int) (c : Prop), a < -5 → c → ¬ (0 = a) ===> True

-- a < -5 → c → a < 0 ===> True
#testOptimize [ "DerivedRelInt_9" ] ∀ (a : Int) (c : Prop), a < -5 → c → a < 0 ===> True

-- 5 < a → c → ¬ (a < 0) ===> True
#testOptimize [ "DerivedRelInt_9a" ] ∀ (a : Int) (c : Prop), 5 < a → c → ¬ (a < 0) ===> True

-- 5 < a → c → 0 ≤ a ===> True
#testOptimize [ "DerivedRelInt_9b" ] ∀ (a : Int) (c : Prop), 5 < a → c → 0 ≤ a ===> True

-- a < -5 → c → ¬ (0 < a) ===> True
#testOptimize [ "DerivedRelInt_9c" ] ∀ (a : Int) (c : Prop), a < -5 → c → ¬ (0 < a) ===> True

-- a < -5 → c → a ≤ 0 ===> True
#testOptimize [ "DerivedRelInt_9d" ] ∀ (a : Int) (c : Prop), a < -5 → c → a ≤ 0 ===> True

-- 5 < a → 6 < b → c → 0 < a + b ===> True
#testOptimize [ "DerivedRelInt_9e" ] ∀ (a b : Int) (c : Prop), 5 < a → 6 < b → c → 0 < a + b ===> True

-- a < -5 → b < -6 → c → a + b ≤ 0 ===> True
#testOptimize [ "DerivedRelInt_9f" ] ∀ (a b : Int) (c : Prop), a < -5 → b < -6 → c → a + b ≤ 0 ===> True

-- 0 < a → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedRelInt_10" ] ∀ (a : Int) (c : Prop), 0 < a → c → ¬ (0 = a) ===> True

-- a < 0 → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedRelInt_11" ] ∀ (a : Int) (c : Prop), a < 0 → c → ¬ (0 = a) ===> True

-- (a < b ∧ c) → ¬ (b < a) ===> True
#testOptimize [ "DerivedRelInt_12" ] ∀ (a b : Int) (c : Prop), (a < b ∧ c) → ¬ (b < a) ===> True

-- 3 < a → a / a = 1 ===> True
-- NOTE: `a / a = 1` requires `¬ (0 = a)`, derived from `3 < a`
#testOptimize [ "DerivedRelInt_13" ] ∀ (a : Int), 3 < a → a / a = 1 ===> True

-- a < -3 → a / a = 1 ===> True
#testOptimize [ "DerivedRelInt_14" ] ∀ (a : Int), a < -3 → a / a = 1 ===> True

-- a < b → c → b ≤ a ===> a < b → ¬ c
#testOptimize [ "DerivedRelInt_15" ] ∀ (a b : Int) (c : Prop), a < b → c → b ≤ a ===> ∀ (a b : Int) (c : Prop), a < b → ¬ c

-- a < b → c → b = a ===> a < b → ¬ c
#testOptimize [ "DerivedRelInt_16" ] ∀ (a b : Int) (c : Prop), a < b → c → b = a ===> ∀ (a b : Int) (c : Prop), a < b → ¬ c

-- a < b → c → b < a ===> a < b → ¬ c
#testOptimize [ "DerivedRelInt_17" ] ∀ (a b : Int) (c : Prop), a < b → c → b < a ===> ∀ (a b : Int) (c : Prop), a < b → ¬ c

-- 5 < a → c → a = 0 ===> 5 < a → ¬ c
#testOptimize [ "DerivedRelInt_18" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), 5 < a → c → a = 0 ===> ∀ (a : Int) (c : Prop), 5 < a → ¬ c

-- a < -5 → c → 0 ≤ a ===> a < -5 → ¬ c
#testOptimize [ "DerivedRelInt_19" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), a < -5 → c → 0 ≤ a ===> ∀ (a : Int) (c : Prop), a < Int.negSucc 4 → ¬ c

-- a < 0 → c → a = 0 ===> a < 0 → ¬ c
#testOptimize [ "DerivedRelInt_20" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), a < 0 → c → a = 0 ===> ∀ (a : Int) (c : Prop), a < 0 → ¬ c

-- -5 < a → c → ¬ (0 = a) ===> -5 < a → c → ¬ (0 = a)  (no derivation when N ≤ 0)
#testOptimize [ "DerivedRelInt_21" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), -5 < a → c → ¬ (0 = a) ===> ∀ (a : Int) (c : Prop), Int.negSucc 4 < a → c → ¬ (0 = a)

-- -5 < a → c → 0 < a ===> -5 < a → c → 0 < a  (no derivation when N ≤ 0)
#testOptimize [ "DerivedRelInt_22" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), -5 < a → c → 0 < a ===> ∀ (a : Int) (c : Prop), Int.negSucc 4 < a → c → 0 < a

-- a < 5 → c → a < 0 ===> a < 5 → c → a < 0  (no derivation when N ≥ 0)
#testOptimize [ "DerivedRelInt_23" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), a < 5 → c → a < 0 ===> ∀ (a : Int) (c : Prop), a < 5 → c → a < 0

-- -5 < a → c → ¬ (a < 0) ===> -5 < a → c → ¬ (a < 0)  (no derivation when N ≤ 0)
#testOptimize [ "DerivedRelInt_24" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), -5 < a → c → ¬ (a < 0) ===> ∀ (a : Int) (c : Prop), Int.negSucc 4 < a → c → ¬ (a < 0)

-- a < 5 → c → ¬ (0 < a) ===> a < 5 → c → ¬ (0 < a)  (no derivation when N ≥ 0)
#testOptimize [ "DerivedRelInt_25" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), a < 5 → c → ¬ (0 < a) ===> ∀ (a : Int) (c : Prop), a < 5 → c → ¬ (0 < a)


/-! ### Int equality facts (`addEqIntFacts`): when `a = b` (with Type(a) = Int)
     - `¬ (a < b)` and `¬ (b < a)` are added
     - when `N = a` with `N ≠ 0`: `¬ (0 = a)` is added, as well as `0 < a` (`N > 0`) or `a < 0` (`N < 0`)
-/

-- a = b → c → ¬ (a < b) ===> True
#testOptimize [ "DerivedEqInt_1" ] ∀ (a b : Int) (c : Prop), a = b → c → ¬ (a < b) ===> True

-- a = b → c → ¬ (b < a) ===> True
#testOptimize [ "DerivedEqInt_2" ] ∀ (a b : Int) (c : Prop), a = b → c → ¬ (b < a) ===> True

-- a = b → c → a ≤ b ===> True
#testOptimize [ "DerivedEqInt_3" ] ∀ (a b : Int) (c : Prop), a = b → c → a ≤ b ===> True

-- a = b → c → b ≤ a ===> True
#testOptimize [ "DerivedEqInt_4" ] ∀ (a b : Int) (c : Prop), a = b → c → b ≤ a ===> True

-- 5 = a → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedEqInt_5" ] ∀ (a : Int) (c : Prop), 5 = a → c → ¬ (0 = a) ===> True

-- a = 5 → c → 0 < a ===> True
#testOptimize [ "DerivedEqInt_6" ] ∀ (a : Int) (c : Prop), a = 5 → c → 0 < a ===> True

-- -5 = a → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedEqInt_7" ] ∀ (a : Int) (c : Prop), -5 = a → c → ¬ (0 = a) ===> True

-- -5 = a → c → a < 0 ===> True
#testOptimize [ "DerivedEqInt_8" ] ∀ (a : Int) (c : Prop), -5 = a → c → a < 0 ===> True

-- 3 = a → a / a = 1 ===> True
#testOptimize [ "DerivedEqInt_9" ] ∀ (a : Int), 3 = a → a / a = 1 ===> True

-- a = b → c → a < b ===> a = b → ¬ c
#testOptimize [ "DerivedEqInt_10" ] ∀ (a b : Int) (c : Prop), a = b → c → a < b ===> ∀ (a b : Int) (c : Prop), a = b → ¬ c

-- 0 = a → c → ¬ (0 = a) ===> 0 = a → ¬ c
#testOptimize [ "DerivedEqInt_11" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), 0 = a → c → ¬ (0 = a) ===> ∀ (a : Int) (c : Prop), 0 = a → ¬ c

-- 0 = a → c → 0 < a ===> 0 = a → ¬ c
#testOptimize [ "DerivedEqInt_12" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop), 0 = a → c → 0 < a ===> ∀ (a : Int) (c : Prop), 0 = a → ¬ c


/-! ### Nat relational facts (`addRelNatFacts`): when `a < b` (with Type(a) = Nat)
     - `¬ (b < a)`, `¬ (0 = b)`, `0 < b` and `¬ (a = b)` (or `¬ (b = a)`) are added
-/

-- a < b → c → ¬ (b < a) ===> True
#testOptimize [ "DerivedRelNat_1" ] ∀ (a b : Nat) (c : Prop), a < b → c → ¬ (b < a) ===> True

-- a < b → c → a ≤ b ===> True
#testOptimize [ "DerivedRelNat_2" ] ∀ (a b : Nat) (c : Prop), a < b → c → a ≤ b ===> True

-- a < b → c → ¬ (0 = b) ===> True
#testOptimize [ "DerivedRelNat_3" ] ∀ (a b : Nat) (c : Prop), a < b → c → ¬ (0 = b) ===> True

-- a < b → c → 0 < b ===> True
#testOptimize [ "DerivedRelNat_4" ] ∀ (a b : Nat) (c : Prop), a < b → c → 0 < b ===> True

-- a < b → c → b ≠ 0 ===> True
#testOptimize [ "DerivedRelNat_5" ] ∀ (a b : Nat) (c : Prop), a < b → c → b ≠ 0 ===> True

-- a < b → c → ¬ (a = b) ===> True
#testOptimize [ "DerivedRelNat_6" ] ∀ (a b : Nat) (c : Prop), a < b → c → ¬ (a = b) ===> True

-- a < b → c → ¬ (b = a) ===> True
#testOptimize [ "DerivedRelNat_7" ] ∀ (a b : Nat) (c : Prop), a < b → c → ¬ (b = a) ===> True

-- 5 < a → c → 0 < a ===> True
#testOptimize [ "DerivedRelNat_8" ] ∀ (a : Nat) (c : Prop), 5 < a → c → 0 < a ===> True

-- ¬ (c ∨ 0 = n) → 0 < n ===> True
#testOptimize [ "DerivedRelNat_9" ] ∀ (n : Nat) (c : Prop), ¬ (c ∨ 0 = n) → 0 < n ===> True

-- b < a → b % b = 0 ===> True
#testOptimize [ "DerivedRelNat_10" ] ∀ (a b : Nat), b < a → Nat.mod b b = 0 ===> True

-- 3 < a → a / a = 1 ===> True
#testOptimize [ "DerivedRelNat_11" ] ∀ (a : Nat), 3 < a → a / a = 1 ===> True

-- a < b → c → b = a ===> a < b → ¬ c
#testOptimize [ "DerivedRelNat_12" ] ∀ (a b : Nat) (c : Prop), a < b → c → b = a ===> ∀ (a b : Nat) (c : Prop), a < b → ¬ c

-- a < b → c → b < a ===> a < b → ¬ c
#testOptimize [ "DerivedRelNat_13" ] ∀ (a b : Nat) (c : Prop), a < b → c → b < a ===> ∀ (a b : Nat) (c : Prop), a < b → ¬ c

-- a < b → c → 0 < a ===> a < b → c → 0 < a  (nothing is known about `a`)
#testOptimize [ "DerivedRelNat_14" ] (norm-result: 1)
  ∀ (a b : Nat) (c : Prop), a < b → c → 0 < a ===> ∀ (a b : Nat) (c : Prop), a < b → c → 0 < a

-- a < 5 → c → ¬ (0 = a) ===> a < 5 → c → 0 < a  (nothing is known about `a`)
#testOptimize [ "DerivedRelNat_15" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop), a < 5 → c → ¬ (0 = a) ===> ∀ (a : Nat) (c : Prop), a < 5 → c → 0 < a


/-! ### Nat equality facts (`addEqNatFacts`): when `a = b` (with Type(a) = Nat)
     - `¬ (a < b)` and `¬ (b < a)` are added
     - when `N = a` with `N ≠ 0`: `¬ (0 = a)` and `0 < a` are added
-/

-- a = b → c → ¬ (a < b) ===> True
#testOptimize [ "DerivedEqNat_1" ] ∀ (a b : Nat) (c : Prop), a = b → c → ¬ (a < b) ===> True

-- a = b → c → ¬ (b < a) ===> True
#testOptimize [ "DerivedEqNat_2" ] ∀ (a b : Nat) (c : Prop), a = b → c → ¬ (b < a) ===> True

-- a = b → c → a ≤ b ===> True
#testOptimize [ "DerivedEqNat_3" ] ∀ (a b : Nat) (c : Prop), a = b → c → a ≤ b ===> True

-- 5 = a → c → ¬ (0 = a) ===> True
#testOptimize [ "DerivedEqNat_4" ] ∀ (a : Nat) (c : Prop), 5 = a → c → ¬ (0 = a) ===> True

-- a = 5 → c → 0 < a ===> True
#testOptimize [ "DerivedEqNat_5" ] ∀ (a : Nat) (c : Prop), a = 5 → c → 0 < a ===> True

-- ¬ (c ∨ a = b) → ¬ (a = b) ===> True
#testOptimize [ "DerivedEqNat_6" ] ∀ (a b : Nat) (c : Prop), ¬ (c ∨ a = b) → ¬ (a = b) ===> True

-- a = b → c → a < b ===> a = b → ¬ c
#testOptimize [ "DerivedEqNat_7" ] ∀ (a b : Nat) (c : Prop), a = b → c → a < b ===> ∀ (a b : Nat) (c : Prop), a = b → ¬ c

-- 0 = a → c → 0 < a ===> 0 = a → ¬ c
#testOptimize [ "DerivedEqNat_8" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop), 0 = a → c → 0 < a ===> ∀ (a : Nat) (c : Prop), 0 = a → ¬ c

-- 0 = a → c → ¬ (0 = a) ===> 0 = a → ¬ c
#testOptimize [ "DerivedEqNat_9" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop), 0 = a → c → ¬ (0 = a) ===> ∀ (a : Nat) (c : Prop), 0 = a → ¬ c


/-! ### Dependent if-then-else facts (`addDitePropFacts`): when `if c then a else b`
     - `c → a` and `¬ c → b` are added (and `false = x → b` when `c := true = x`)
-/

-- (if x then a else b) → x → a ===> True
#testOptimize [ "DerivedDite_1" ] ∀ (a b : Prop) (x : Bool), (if x then a else b) → x → a ===> True

-- (if x then a else b) → ¬ x → b ===> True
#testOptimize [ "DerivedDite_2" ] ∀ (a b : Prop) (x : Bool), (if x then a else b) → ¬ x → b ===> True

-- (if x then a else b) → false = x → b ===> True
#testOptimize [ "DerivedDite_3" ] ∀ (a b : Prop) (x : Bool), (if x then a else b) → false = x → b ===> True

-- (if c then a else b) → c → a ===> True
#testOptimize [ "DerivedDite_4" ] ∀ (a b c : Prop) [Decidable c], (if c then a else b) → c → a ===> True

-- (if c then a else b) → ¬ c → b ===> True
#testOptimize [ "DerivedDite_5" ] ∀ (a b c : Prop) [Decidable c], (if c then a else b) → ¬ c → b ===> True


/-! ### Derived proofs

When a derived fact is used to reduce a dependent `if`, the proof of the derived fact is
substituted for the bound hypothesis in the selected branch. The expected terms below spell out the
proof terms built by `addHypotheses`, so that both the derivation and the shape of the proof are
validated (an ill-typed proof would not match the type-checked expected term).
-/

/-! Conjunction / negated disjunction. -/

-- p ∧ q → (if h : p then f h else g) = g ===> g = f (And.left p q h)
#testOptimize [ "DerivedProofAnd_1" ]
  ∀ (p q : Prop) [Decidable p] (f : p → Nat) (g : Nat), p ∧ q → (if h : p then f h else g) = g ===>
  ∀ (p q : Prop) (f : p → Nat) (g : Nat) (h : p ∧ q), g = f (@And.left p q h)

-- p ∧ q → (if h : q then f h else g) = g ===> g = f (And.right p q h)
#testOptimize [ "DerivedProofAnd_2" ]
  ∀ (p q : Prop) [Decidable q] (f : q → Nat) (g : Nat), p ∧ q → (if h : q then f h else g) = g ===>
  ∀ (p q : Prop) (f : q → Nat) (g : Nat) (h : p ∧ q), g = f (@And.right p q h)

-- ¬ (p ∨ q) → (if h : ¬ p then f h else g) = g ===> g = f (And.left (¬ p) (¬ q) (and_not_from_not_or p q h))
#testOptimize [ "DerivedProofNotOr_1" ]
  ∀ (p q : Prop) [Decidable p] (f : ¬ p → Nat) (g : Nat), ¬ (p ∨ q) → (if h : ¬ p then f h else g) = g ===>
  ∀ (p q : Prop) (f : ¬ p → Nat) (g : Nat) (h : ¬ (p ∨ q)),
    g = f (@And.left (¬ p) (¬ q) (@Blaster.and_not_from_not_or p q h))

-- ¬ (p ∨ q) → (if h : ¬ q then f h else g) = g ===> g = f (And.right (¬ p) (¬ q) (and_not_from_not_or p q h))
#testOptimize [ "DerivedProofNotOr_2" ]
  ∀ (p q : Prop) [Decidable q] (f : ¬ q → Nat) (g : Nat), ¬ (p ∨ q) → (if h : ¬ q then f h else g) = g ===>
  ∀ (p q : Prop) (f : ¬ q → Nat) (g : Nat) (h : ¬ (p ∨ q)),
    g = f (@And.right (¬ p) (¬ q) (@Blaster.and_not_from_not_or p q h))

/-! Negation facts (the negated hypothesis is obtained from a negated disjunction, so that it is not
    normalized before being added to the hypothesis map). -/

-- ¬ (q ∨ ¬ p) → (if h : p then f h else g) = g ===> g = f (not_not_cancel p _)
#testOptimize [ "DerivedProofNot_1" ]
  ∀ (p q : Prop) [Decidable p] (f : p → Nat) (g : Nat), ¬ (q ∨ ¬ p) → (if h : p then f h else g) = g ===>
  ∀ (p q : Prop) (f : p → Nat) (g : Nat) (h : ¬ (q ∨ ¬ p)),
    g = f (@Blaster.not_not_cancel p (@And.right (¬ q) (¬ ¬ p) (@Blaster.and_not_from_not_or q (¬ p) h)))

-- ¬ (c ∨ false = x) → (if h : true = x then f h else g) = g ===> g = f (true_eq_of_not_false_eq x _)
#testOptimize [ "DerivedProofNot_2" ]
  ∀ (x : Bool) (c : Prop) (f : true = x → Nat) (g : Nat), ¬ (c ∨ false = x) → (if h : true = x then f h else g) = g ===>
  ∀ (x : Bool) (c : Prop) (f : true = x → Nat) (g : Nat) (h : ¬ (c ∨ false = x)),
    g = f (@Blaster.true_eq_of_not_false_eq x
            (@And.right (¬ c) (¬ (false = x)) (@Blaster.and_not_from_not_or c (false = x) h)))

-- ¬ (c ∨ true = x) → (if h : false = x then f h else g) = g ===> g = f (false_eq_of_not_true_eq x _)
#testOptimize [ "DerivedProofNot_3" ]
  ∀ (x : Bool) (c : Prop) (f : false = x → Nat) (g : Nat), ¬ (c ∨ true = x) → (if h : false = x then f h else g) = g ===>
  ∀ (x : Bool) (c : Prop) (f : false = x → Nat) (g : Nat) (h : ¬ (c ∨ true = x)),
    g = f (@Blaster.false_eq_of_not_true_eq x
            (@And.right (¬ c) (¬ (true = x)) (@Blaster.and_not_from_not_or c (true = x) h)))

-- ¬ (c ∨ 0 = a) → (if h : 0 < a then f h else g) = g ===> g = f (nat_zero_lt_of_not_zero_eq a _)
#testOptimize [ "DerivedProofNot_4" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop) (f : 0 < a → Nat) (g : Nat), ¬ (c ∨ 0 = a) → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Nat) (c : Prop) (f : 0 < a → Nat) (g : Nat) (h : ¬ (c ∨ 0 = a)),
    g = f (@Blaster.nat_zero_lt_of_not_zero_eq a
            (@And.right (¬ c) (¬ (0 = a)) (@Blaster.and_not_from_not_or c (0 = a) h)))

-- ¬ (c ∨ 0 < a) → (if h : 0 = a then f h else g) = g ===> g = f (nat_zero_eq_of_not_zero_lt a _)
#testOptimize [ "DerivedProofNot_5" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop) (f : 0 = a → Nat) (g : Nat), ¬ (c ∨ 0 < a) → (if h : 0 = a then f h else g) = g ===>
  ∀ (a : Nat) (c : Prop) (f : 0 = a → Nat) (g : Nat) (h : ¬ (c ∨ 0 < a)),
    g = f (@Blaster.nat_zero_eq_of_not_zero_lt a
            (@And.right (¬ c) (¬ (0 < a)) (@Blaster.and_not_from_not_or c (0 < a) h)))

-- ¬ (a < 5) → (if h : 0 < a then f h else g) = g ===> g = f (nat_zero_lt_of_not_lt_neq a 5 h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofNot_6" ] (norm-result: 1)
  ∀ (a : Nat) (f : 0 < a → Nat) (g : Nat), ¬ (a < 5) → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Nat) (f : 0 < a → Nat) (g : Nat) (h : ¬ (a < 5)),
    g = f (@Blaster.nat_zero_lt_of_not_lt_neq a 5 h
            (@of_decide_eq_true (¬ ((0 : Nat) = 5))
              (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))
              (@rfl Bool (@decide (¬ ((0 : Nat) = 5)) (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))))))

-- 5 ≤ a → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (nat_zero_lt_of_not_lt_neq a 5 h (of_decide_eq_true ..))
-- NOTE: on Nat, `¬ (0 = a)` is normalized to `0 < a` (also in the type of `f`), so the derived
--       fact `¬ (0 = a)` is not observable on its own: the `0 < a` proof is used.
#testOptimize [ "DerivedProofNot_7" ] (norm-result: 1)
  ∀ (a : Nat) (f : ¬ (0 = a) → Nat) (g : Nat), 5 ≤ a → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Nat) (f : 0 < a → Nat) (g : Nat) (h : ¬ (a < 5)),
    g = f (@Blaster.nat_zero_lt_of_not_lt_neq a 5 h
            (@of_decide_eq_true (¬ ((0 : Nat) = 5))
              (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))
              (@rfl Bool (@decide (¬ ((0 : Nat) = 5)) (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))))))

-- ¬ (c ∨ a < 5) → (if h : 0 < a then f h else g) = g ===> g = f (nat_zero_lt_of_not_lt_neq a 5 _ (of_decide_eq_true ..))
#testOptimize [ "DerivedProofNot_8" ] (norm-result: 1)
  ∀ (a : Nat) (c : Prop) (f : 0 < a → Nat) (g : Nat), ¬ (c ∨ a < 5) → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Nat) (c : Prop) (f : 0 < a → Nat) (g : Nat) (h : ¬ (c ∨ a < 5)),
    g = f (@Blaster.nat_zero_lt_of_not_lt_neq a 5
            (@And.right (¬ c) (¬ (a < 5)) (@Blaster.and_not_from_not_or c (a < 5) h))
            (@of_decide_eq_true (¬ ((0 : Nat) = 5))
              (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))
              (@rfl Bool (@decide (¬ ((0 : Nat) = 5)) (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))))))

-- ¬ (a < 5) → (if h : 0 < a then f h else g) = g ===> g = f (int_zero_lt_of_nlt_zero_lt a 5 h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofNot_9" ] (norm-result: 1)
  ∀ (a : Int) (f : 0 < a → Int) (g : Int), ¬ (a < 5) → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Int) (f : 0 < a → Int) (g : Int) (h : ¬ (a < 5)),
    g = f (@Blaster.int_zero_lt_of_nlt_zero_lt a 5 h
            (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
              (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5)))))

-- 5 ≤ a → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (int_not_zero_eq_of_zero_lt a (int_zero_lt_of_nlt_zero_lt a 5 h ..))
#testOptimize [ "DerivedProofNot_10" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int), 5 ≤ a → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int) (h : ¬ (a < 5)),
    g = f (@Blaster.int_not_zero_eq_of_zero_lt a
            (@Blaster.int_zero_lt_of_nlt_zero_lt a 5 h
              (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
                (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5))))))

-- ¬ (a < 5) → (if h : ¬ (a < 0) then f h else g) = g ===> g = f (int_not_lt_of_lt 0 a (int_zero_lt_of_nlt_zero_lt a 5 h ..))
#testOptimize [ "DerivedProofNot_11" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (a < 0) → Int) (g : Int), ¬ (a < 5) → (if h : ¬ (a < 0) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (a < 0) → Int) (g : Int) (h : ¬ (a < 5)),
    g = f (@Blaster.int_not_lt_of_lt 0 a
            (@Blaster.int_zero_lt_of_nlt_zero_lt a 5 h
              (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
                (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5))))))

-- ¬ (-5 < a) → (if h : a < 0 then f h else g) = g ===> g = f (int_lt_zero_of_nlt_lt_zero a (-5) h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofNot_12" ] (norm-result: 1)
  ∀ (a : Int) (f : a < 0 → Int) (g : Int), ¬ (-5 < a) → (if h : a < 0 then f h else g) = g ===>
  ∀ (a : Int) (f : a < 0 → Int) (g : Int) (h : ¬ (Int.negSucc 4 < a)),
    g = f (@Blaster.int_lt_zero_of_nlt_lt_zero a (Int.negSucc 4) h
            (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
              (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)))))

-- a ≤ -5 → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (int_not_zero_eq_of_lt_zero a (int_lt_zero_of_nlt_lt_zero a (-5) h ..))
#testOptimize [ "DerivedProofNot_13" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int), a ≤ -5 → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int) (h : ¬ (Int.negSucc 4 < a)),
    g = f (@Blaster.int_not_zero_eq_of_lt_zero a
            (@Blaster.int_lt_zero_of_nlt_lt_zero a (Int.negSucc 4) h
              (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
                (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0))))))

-- ¬ (-5 < a) → (if h : ¬ (0 < a) then f h else g) = g ===> g = f (int_not_lt_of_lt a 0 (int_lt_zero_of_nlt_lt_zero a (-5) h ..))
#testOptimize [ "DerivedProofNot_14" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 < a) → Int) (g : Int), ¬ (-5 < a) → (if h : ¬ (0 < a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 < a) → Int) (g : Int) (h : ¬ (Int.negSucc 4 < a)),
    g = f (@Blaster.int_not_lt_of_lt a 0
            (@Blaster.int_lt_zero_of_nlt_lt_zero a (Int.negSucc 4) h
              (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
                (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0))))))

-- ¬ (c ∨ a < 5) → (if h : 0 < a then f h else g) = g ===> g = f (int_zero_lt_of_nlt_zero_lt a 5 _ (of_decide_eq_true ..))
#testOptimize [ "DerivedProofNot_15" ] (norm-result: 1)
  ∀ (a : Int) (c : Prop) (f : 0 < a → Int) (g : Int), ¬ (c ∨ a < 5) → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Int) (c : Prop) (f : 0 < a → Int) (g : Int) (h : ¬ (c ∨ a < 5)),
    g = f (@Blaster.int_zero_lt_of_nlt_zero_lt a 5
            (@And.right (¬ c) (¬ (a < 5)) (@Blaster.and_not_from_not_or c (a < 5) h))
            (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
              (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5)))))

/-! Nat relational / equality facts. -/

-- a < b → (if h : 0 < b then f h else g) = g ===> g = f (nat_zero_lt_of_lt a b h)
#testOptimize [ "DerivedProofRelNat_1" ] (norm-result: 1)
  ∀ (a b : Nat) (f : 0 < b → Nat) (g : Nat), a < b → (if h : 0 < b then f h else g) = g ===>
  ∀ (a b : Nat) (f : 0 < b → Nat) (g : Nat) (h : a < b), g = f (@Blaster.nat_zero_lt_of_lt a b h)

-- a < b → (if h : ¬ (0 = b) then f h else g) = g ===> g = f (nat_zero_lt_of_lt a b h)
-- NOTE: the condition `¬ (0 = b)` is normalized to `0 < b`
#testOptimize [ "DerivedProofRelNat_2" ] (norm-result: 1)
  ∀ (a b : Nat) (f : ¬ (0 = b) → Nat) (g : Nat), a < b → (if h : ¬ (0 = b) then f h else g) = g ===>
  ∀ (a b : Nat) (f : 0 < b → Nat) (g : Nat) (h : a < b), g = f (@Blaster.nat_zero_lt_of_lt a b h)

-- a < b → (if h : ¬ (b < a) then f h else g) = g ===> g = f (nat_not_lt_of_lt a b h)
#testOptimize [ "DerivedProofRelNat_3" ]
  ∀ (a b : Nat) (f : ¬ (b < a) → Nat) (g : Nat), a < b → (if h : ¬ (b < a) then f h else g) = g ===>
  ∀ (a b : Nat) (f : ¬ (b < a) → Nat) (g : Nat) (h : a < b), g = f (@Blaster.nat_not_lt_of_lt a b h)

-- a < b → (if h : ¬ (a = b) then f h else g) = g ===> g = f (nat_not_eq_of_lt_left a b h)
#testOptimize [ "DerivedProofRelNat_4" ]
  ∀ (a b : Nat) (f : ¬ (a = b) → Nat) (g : Nat), a < b → (if h : ¬ (a = b) then f h else g) = g ===>
  ∀ (a b : Nat) (f : ¬ (a = b) → Nat) (g : Nat) (h : a < b), g = f (@Blaster.nat_not_eq_of_lt_left a b h)

-- b < a → (if h : ¬ (a = b) then f h else g) = g ===> g = f (nat_not_eq_of_lt_left_sym b a h)
#testOptimize [ "DerivedProofRelNat_5" ]
  ∀ (a b : Nat) (f : ¬ (a = b) → Nat) (g : Nat), b < a → (if h : ¬ (a = b) then f h else g) = g ===>
  ∀ (a b : Nat) (f : ¬ (a = b) → Nat) (g : Nat) (h : b < a), g = f (@Blaster.nat_not_eq_of_lt_left_sym b a h)

-- a = b → (if h : ¬ (a < b) then f h else g) = g ===> g = f (nat_not_lt_left_of_eq a b h)
#testOptimize [ "DerivedProofEqNat_1" ]
  ∀ (a b : Nat) (f : ¬ (a < b) → Nat) (g : Nat), a = b → (if h : ¬ (a < b) then f h else g) = g ===>
  ∀ (a b : Nat) (f : ¬ (a < b) → Nat) (g : Nat) (h : a = b), g = f (@Blaster.nat_not_lt_left_of_eq a b h)

-- a = b → (if h : ¬ (b < a) then f h else g) = g ===> g = f (nat_not_lt_right_of_eq a b h)
#testOptimize [ "DerivedProofEqNat_2" ]
  ∀ (a b : Nat) (f : ¬ (b < a) → Nat) (g : Nat), a = b → (if h : ¬ (b < a) then f h else g) = g ===>
  ∀ (a b : Nat) (f : ¬ (b < a) → Nat) (g : Nat) (h : a = b), g = f (@Blaster.nat_not_lt_right_of_eq a b h)

-- 5 = a → (if h : 0 < a then f h else g) = g ===> g = f (nat_zero_lt_of_eq_neq 5 a h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofEqNat_3" ] (norm-result: 1)
  ∀ (a : Nat) (f : 0 < a → Nat) (g : Nat), 5 = a → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Nat) (f : 0 < a → Nat) (g : Nat) (h : 5 = a),
    g = f (@Blaster.nat_zero_lt_of_eq_neq 5 a h
            (@of_decide_eq_true (¬ ((0 : Nat) = 5))
              (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))
              (@rfl Bool (@decide (¬ ((0 : Nat) = 5)) (@instDecidableNot ((0 : Nat) = 5) (instDecidableEqNat 0 5))))))

/-! Int relational / equality facts. -/

-- a < b → (if h : ¬ (b < a) then f h else g) = g ===> g = f (int_not_lt_of_lt a b h)
#testOptimize [ "DerivedProofRelInt_1" ]
  ∀ (a b : Int) (f : ¬ (b < a) → Int) (g : Int), a < b → (if h : ¬ (b < a) then f h else g) = g ===>
  ∀ (a b : Int) (f : ¬ (b < a) → Int) (g : Int) (h : a < b), g = f (@Blaster.int_not_lt_of_lt a b h)

-- a < b → (if h : ¬ (a = b) then f h else g) = g ===> g = f (int_not_eq_of_lt_left a b h)
#testOptimize [ "DerivedProofRelInt_2" ]
  ∀ (a b : Int) (f : ¬ (a = b) → Int) (g : Int), a < b → (if h : ¬ (a = b) then f h else g) = g ===>
  ∀ (a b : Int) (f : ¬ (a = b) → Int) (g : Int) (h : a < b), g = f (@Blaster.int_not_eq_of_lt_left a b h)

-- b < a → (if h : ¬ (a = b) then f h else g) = g ===> g = f (int_not_eq_of_lt_left_sym b a h)
#testOptimize [ "DerivedProofRelInt_3" ]
  ∀ (a b : Int) (f : ¬ (a = b) → Int) (g : Int), b < a → (if h : ¬ (a = b) then f h else g) = g ===>
  ∀ (a b : Int) (f : ¬ (a = b) → Int) (g : Int) (h : b < a), g = f (@Blaster.int_not_eq_of_lt_left_sym b a h)

-- 5 < a → (if h : 0 < a then f h else g) = g ===> g = f (Int.lt_trans (of_decide_eq_true ..) h)
#testOptimize [ "DerivedProofRelInt_4" ] (norm-result: 1)
  ∀ (a : Int) (f : 0 < a → Int) (g : Int), 5 < a → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Int) (f : 0 < a → Int) (g : Int) (h : 5 < a),
    g = f (@Int.lt_trans 0 5 a
            (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
              (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5))))
            h)

-- 5 < a → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (int_not_zero_eq_of_lt_zero_lt 5 a h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofRelInt_5" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int), 5 < a → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int) (h : 5 < a),
    g = f (@Blaster.int_not_zero_eq_of_lt_zero_lt 5 a h
            (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
              (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5)))))

-- a < -5 → (if h : a < 0 then f h else g) = g ===> g = f (Int.lt_trans h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofRelInt_6" ] (norm-result: 1)
  ∀ (a : Int) (f : a < 0 → Int) (g : Int), a < -5 → (if h : a < 0 then f h else g) = g ===>
  ∀ (a : Int) (f : a < 0 → Int) (g : Int) (h : a < Int.negSucc 4),
    g = f (@Int.lt_trans a (Int.negSucc 4) 0 h
            (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
              (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)))))

-- a < -5 → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (int_not_zero_eq_of_lt_lt_zero a (-5) h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofRelInt_7" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int), a < -5 → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int) (h : a < Int.negSucc 4),
    g = f (@Blaster.int_not_zero_eq_of_lt_lt_zero a (Int.negSucc 4) h
            (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
              (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)))))

-- 5 < a → (if h : ¬ (a < 0) then f h else g) = g ===> g = f (int_not_lt_of_lt 0 a (Int.lt_trans (of_decide_eq_true ..) h))
#testOptimize [ "DerivedProofRelInt_8" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (a < 0) → Int) (g : Int), 5 < a → (if h : ¬ (a < 0) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (a < 0) → Int) (g : Int) (h : 5 < a),
    g = f (@Blaster.int_not_lt_of_lt 0 a
            (@Int.lt_trans 0 5 a
              (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
                (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5))))
              h))

-- 5 < a → (if h : 0 ≤ a then f h else g) = g ===> g = f (int_not_lt_of_lt 0 a (Int.lt_trans (of_decide_eq_true ..) h))
-- NOTE: the condition `0 ≤ a` is normalized to `¬ (a < 0)`
#testOptimize [ "DerivedProofRelInt_9" ] (norm-result: 1)
  ∀ (a : Int) (f : 0 ≤ a → Int) (g : Int), 5 < a → (if h : 0 ≤ a then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (a < 0) → Int) (g : Int) (h : 5 < a),
    g = f (@Blaster.int_not_lt_of_lt 0 a
            (@Int.lt_trans 0 5 a
              (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
                (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5))))
              h))

-- a < -5 → (if h : ¬ (0 < a) then f h else g) = g ===> g = f (int_not_lt_of_lt a 0 (Int.lt_trans h (of_decide_eq_true ..)))
#testOptimize [ "DerivedProofRelInt_10" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 < a) → Int) (g : Int), a < -5 → (if h : ¬ (0 < a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 < a) → Int) (g : Int) (h : a < Int.negSucc 4),
    g = f (@Blaster.int_not_lt_of_lt a 0
            (@Int.lt_trans a (Int.negSucc 4) 0 h
              (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
                (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0))))))

-- a < -5 → (if h : a ≤ 0 then f h else g) = g ===> g = f (int_not_lt_of_lt a 0 (Int.lt_trans h (of_decide_eq_true ..)))
-- NOTE: the condition `a ≤ 0` is normalized to `¬ (0 < a)`
#testOptimize [ "DerivedProofRelInt_11" ] (norm-result: 1)
  ∀ (a : Int) (f : a ≤ 0 → Int) (g : Int), a < -5 → (if h : a ≤ 0 then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 < a) → Int) (g : Int) (h : a < Int.negSucc 4),
    g = f (@Blaster.int_not_lt_of_lt a 0
            (@Int.lt_trans a (Int.negSucc 4) 0 h
              (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
                (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0))))))

-- a = b → (if h : ¬ (a < b) then f h else g) = g ===> g = f (int_not_lt_left_of_eq a b h)
#testOptimize [ "DerivedProofEqInt_1" ]
  ∀ (a b : Int) (f : ¬ (a < b) → Int) (g : Int), a = b → (if h : ¬ (a < b) then f h else g) = g ===>
  ∀ (a b : Int) (f : ¬ (a < b) → Int) (g : Int) (h : a = b), g = f (@Blaster.int_not_lt_left_of_eq a b h)

-- a = b → (if h : ¬ (b < a) then f h else g) = g ===> g = f (int_not_lt_right_of_eq a b h)
#testOptimize [ "DerivedProofEqInt_2" ]
  ∀ (a b : Int) (f : ¬ (b < a) → Int) (g : Int), a = b → (if h : ¬ (b < a) then f h else g) = g ===>
  ∀ (a b : Int) (f : ¬ (b < a) → Int) (g : Int) (h : a = b), g = f (@Blaster.int_not_lt_right_of_eq a b h)

-- 5 = a → (if h : ¬ (0 = a) then f h else g) = g ===> g = f (int_not_zero_eq_of_eq_neq 5 a h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofEqInt_3" ] (norm-result: 1)
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int), 5 = a → (if h : ¬ (0 = a) then f h else g) = g ===>
  ∀ (a : Int) (f : ¬ (0 = a) → Int) (g : Int) (h : 5 = a),
    g = f (@Blaster.int_not_zero_eq_of_eq_neq 5 a h
            (@of_decide_eq_true (¬ ((0 : Int) = 5))
              (@instDecidableNot ((0 : Int) = 5) (Int.instDecidableEq 0 5))
              (@rfl Bool (@decide (¬ ((0 : Int) = 5)) (@instDecidableNot ((0 : Int) = 5) (Int.instDecidableEq 0 5))))))

-- 5 = a → (if h : 0 < a then f h else g) = g ===> g = f (int_zero_lt_of_eq_zero_lt 5 a h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofEqInt_4" ] (norm-result: 1)
  ∀ (a : Int) (f : 0 < a → Int) (g : Int), 5 = a → (if h : 0 < a then f h else g) = g ===>
  ∀ (a : Int) (f : 0 < a → Int) (g : Int) (h : 5 = a),
    g = f (@Blaster.int_zero_lt_of_eq_zero_lt 5 a h
            (@of_decide_eq_true ((0 : Int) < 5) (Int.decLt 0 5)
              (@rfl Bool (@decide ((0 : Int) < 5) (Int.decLt 0 5)))))

-- -5 = a → (if h : a < 0 then f h else g) = g ===> g = f (int_lt_zero_of_eq_lt_zero (-5) a h (of_decide_eq_true ..))
#testOptimize [ "DerivedProofEqInt_5" ] (norm-result: 1)
  ∀ (a : Int) (f : a < 0 → Int) (g : Int), -5 = a → (if h : a < 0 then f h else g) = g ===>
  ∀ (a : Int) (f : a < 0 → Int) (g : Int) (h : Int.negSucc 4 = a),
    g = f (@Blaster.int_lt_zero_of_eq_lt_zero (Int.negSucc 4) a h
            (@of_decide_eq_true (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)
              (@rfl Bool (@decide (Int.negSucc 4 < (0 : Int)) (Int.decLt (Int.negSucc 4) 0)))))

end Tests.DerivedFacts
