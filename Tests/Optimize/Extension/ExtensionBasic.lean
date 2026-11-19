import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionBasic

/-! ## Hand-written optimization function -/

@[blaster String.contains (noRestart := true)]
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
@[blaster]
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

@[blaster (noRestart := true)]
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

/-! Non-linear patterns. -/

axiom h2 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom h2_same : ∀ (n : Nat), h2 n n = n

#testOptimize [ "ExtNonLinear_1" ] ∀ (n m : Nat), h2 n n = m ===> ∀ (n m : Nat), n = m
#testOptimize [ "ExtNonLinear_2" ] ∀ (n m : Nat), h2 n m = m ===> ∀ (n m : Nat), m = h2 n m

/-! Target head specified explicitly: must be the head of the lhs. -/

@[blaster g (noRestart := true)]
axiom g_zero : g 0 = 0

#testOptimize [ "ExtHead_1" ] (norm-result: 1) ∀ (m : Nat), g 0 = m ===> ∀ (m : Nat), 0 = m

/-! Target head is a Ctor -/

@[blaster]
theorem dite_pull_on_cons (m n : Nat) (b : Bool) :
  Blaster.dite' b (fun _ => m) (fun _ => n) :: [] =
  Blaster.dite' b (fun _ => [m]) (fun _ => [n]) :=
  by dsimp [Blaster.dite']; cases h : Blaster.decide' b
     case false => simp
     case true => simp

@[blaster]
-- handling optimization not applied on arguments
theorem ite_pull_on_cons (m n : Nat) (b : Bool) :
  (if b then m else n) :: [] = if b then [m] else [n] := by split <;> simp

@[blaster]
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

end Test.ExtensionBasic
