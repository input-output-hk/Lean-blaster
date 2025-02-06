import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.RecFun

/-! ## Test objectives to validate the normalization of recursive functions. -/


/-! Test cases to validate recursive function normalization. -/

def powerN (a : Int) (n : Nat) : Int :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => a * powerN a n'

-- ∀ (x : Int) (n : Nat), powerN x n = Int.pow x n ===> True
-- NOTE: Equivalence detection with opaque function
#testOptimize ["NormRecFun_1"] ∀ (x : Int) (n : Nat), powerN x n = Int.pow x n ===> True


-- ∀ (x : Int) (n : Nat), x ^ n = powerN x n ===> True
-- NOTE: Equivalence detection with opaque function
#testOptimize ["NormRecFun_2"] ∀ (x : Int) (n : Nat), x ^ n = powerN x n ===> True


def addNat (a : Nat) (b : Nat) : Nat :=
 match a, b with
 | _, Nat.zero => a
 | _, Nat.succ b => Nat.succ (addNat a b)

-- ∀ (x y : Nat), addNat x y = x + y ===> True
-- NOTE: Equivalence detection with opaque function
#testOptimize ["NormRecFun_3"] ∀ (x y : Nat), addNat x y = x + y ===> True

-- ∀ (x y : Nat), x + y = addNat x y = ===> True
-- NOTE: Equivalence detection with opaque function
#testOptimize ["NormRecFun_4"] ∀ (x y : Nat), x + y = addNat x y ===> True


def listNatBeq (xs : List Nat) (ys : List Nat) : Bool :=
 match xs, ys with
 | [], [] => true
 | x :: xs, y :: ys => listNatBeq xs ys && y == x
 | _, _ => false

-- ∀ (xs ys : List Nat), (List.beq xs ys) = listNatBeq xs ys ===> True
-- NOTE: Equivalence detection between polymorphic and non-polymorphic function
-- NOTE: Also validates structrual equivalence on match expresssions.
#testOptimize ["NormRecFun_5"] ∀ (xs ys : List Nat), (List.beq xs ys) = listNatBeq xs ys ===> True


-- ∀ (xs ys : List Nat), listNatBeq xs ys = (xs == ys) ===> True
-- NOTE: Equivalence detection between polymorphic and non-polymorphic function.
-- NOTE: Also validates structrual equivalence on match expresssions.
#testOptimize ["NormRecFun_6"] ∀ (xs ys : List Nat), listNatBeq xs ys = (xs == ys) ===> True


def listPolyBeq [BEq α] (xs : List α) (ys : List α) : Bool :=
 match xs, ys with
 | [], [] => true
 | x :: xs, y :: ys => listPolyBeq xs ys && x == y
 | _, _ => false


-- ∀ (α : Type) (xs ys : List α), [BEq α] → (List.beq xs ys) = listPolyBeq xs ys ===> True
-- NOTE: Equivalence detection between two polymorphic functions
#testOptimize ["NormRecFun_7"] ∀ (α : Type) (xs ys : List α), [BEq α] → (List.beq xs ys) = listPolyBeq xs ys ===> True

-- ∀ (α : Type) (xs ys : List α), [BEq α] → listPolyBeq xs ys = (xs == ys) ===> True
-- NOTE: Equivalence detection between two polymorphic functions
#testOptimize ["NormRecFun_8"] ∀ (α : Type) (xs ys : List α), [BEq α] → listPolyBeq xs ys = (xs == ys) ===> True

-- ∀ (xs ys : List Nat), listPolyBeq xs ys = (xs == ys) ===> True
-- NOTE: Equivalence between two instantiated polymorphic functions
#testOptimize ["NormRecFun_9"] ∀ (xs ys : List Nat), listPolyBeq xs ys = (xs == ys) ===> True


-- ∀ (a b : List Int) (c d : List Nat), (listPolyBeq a b) = (listPolyBeq c d) → (a == b) = (c == d) ===> True
-- NOTE: Equivalence between two instantiated polymorphic functions resulting to same expression.
#testOptimize ["NormRecFun_10"]  ∀ (a b : List Int) (c d : List Nat),
                                    (listPolyBeq a b) = (listPolyBeq c d) → (a == b) = (c == d) ===> True


def addAlias (x : Nat) (y : Nat) : Nat := addNat x y

def mulNat (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | _, Nat.zero => 0
 | _, Nat.succ b => addAlias x (mulNat x b) -- commutativity detected when addNat is replaced with Nat.add

def mulAlias := mulNat

def powerNat (a : Nat) (n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => mulAlias a (powerNat a n') -- commutativity detected when mulNat is replaced with Nat.mul


-- ∀ (x y : Nat), powerNat x y = Nat.pow x y ===> True
-- NOTE: Equivalence detection between nested opaque functions (i.e., here 3 nested level)
-- NOTE: Also ensures that non-recursive function are inlined.
#testOptimize ["NormRecFun_11"] ∀ (x y : Nat), powerNat x y = Nat.pow x y ===> True

-- ∀ (x y : Nat), x ^ y = powerNat x y ===> True
-- NOTE: Equivalence detection between nested opaque function (i.e., here 3 nested level)
-- NOTE: Also ensures that non-recursive function are inlined.
#testOptimize ["NormRecFun_12"] ∀ (x y : Nat), x ^ y = powerNat x y ===> True


-- ∀ (x y : Nat), powerNat y x + Nat.pow x y = Nat.pow y x + powerNat x y ===> True
-- NOTE: Equivalence detection between nested opaque function (i.e., here 3 nested level)
-- NOTE: Also ensures that structural equivalence is properly performed when
-- a recursive function is referenced more than once (i.e., proper use of instance cache)
#testOptimize ["NormRecFun_13"] ∀ (x y : Nat), powerNat y x + Nat.pow x y = Nat.pow y x + powerNat x y ===> True

-- ∀ (x y : Nat), if x < y then powerNat y x else powerNat x y < Nat.pow x y ===>
-- ∀ (x y : Nat), if x < y then Nat.pow y x else Nat.pow x y < Nat.pow x y
-- NOTE: Equivalence detection between nested opaque function (i.e., here 3 nested level)
-- NOTE: Also ensures that structural equivalence is properly performed when
-- a recursive function is referenced more than once (i.e., proper use of instance cache)
#testOptimize ["NormRecFun_14"] ∀ (x y : Nat), (if x < y then powerNat y x else powerNat x y) < Nat.pow x y ===>
                                ∀ (x y : Nat), (if x < y then Nat.pow y x else Nat.pow x y) < Nat.pow x y

def eqNat (a : Nat) (b : Nat) : Bool :=
  match a, b with
  | Nat.zero, Nat.zero   => true
  | Nat.zero, Nat.succ _ => false
  | Nat.succ _, Nat.zero   => false
  | Nat.succ n, Nat.succ m => eqNat n m

-- ∀ (x y : Nat), Nat.beq x y = eqNat x y ===> True
-- NOTE: Equivalence detection with opaque function
-- NOTE: Also verify effect of normalization performed on Nat.beq in recursive definition,
-- i.e., `Nat.beq x y ===> x == y`
#testOptimize ["NormRecFun_15"] ∀ (x y : Nat), Nat.beq x y = eqNat x y ===> True


-- ∀ (c : Bool) (x y : Nat), if c then Nat.beq x y else eqNat y x ===>
-- ∀ (x y : Nat), x = y
-- NOTE: Equivalence detection with opaque function
-- NOTE: Also verify effect of normalization performed on Nat.beq in recursive definition,
-- i.e., `Nat.beq x y ===> x == y`
-- NOTE: `true = (x == y) ===> x = y`
#testOptimize ["NormRecFun_16"] ∀ (c : Bool) (x y : Nat), if c then Nat.beq x y else eqNat y x ===>
                                ∀ (x y : Nat), x = y


/-! Test cases to validate when match expressions and recursive functions are NOT wrongly
    declared as equivalent.
-/

def powerNAddOne (a : Int) (n : Nat) : Int :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => (a + 1) * powerNAddOne a n'

-- ∀ (x : Int) (n : Nat), powerNAddOne x n = x ^ n ===>
-- ∀ (x : Int) (n : Nat), Int.pow x n = powerNAddOne x n
#testOptimize ["NormRecUnchanged_1"] ∀ (x : Int) (n : Nat), powerNAddOne x n = x ^ n ===>
                                     ∀ (x : Int) (n : Nat), Int.pow x n = powerNAddOne x n

def addNatBug (a : Nat) (b : Nat) : Nat :=
 match a, b with
 | _, Nat.zero => 0
 | _, Nat.succ b => Nat.succ (addNatBug a b)

-- ∀ (x y : Nat), addNatBug x y = x + y ===>
-- ∀ (x y : Nat), Nat.add x y = addNatBug x y
#testOptimize ["NormRecUnchanged_2"] ∀ (x y : Nat), addNatBug x y = x + y ===>
                                     ∀ (x y : Nat), Nat.add x y = addNatBug x y


def listNatBeqInverse (xs : List Nat) (ys : List Nat) : Bool :=
 match xs, ys with
 | x :: xs, y :: ys => listNatBeqInverse xs ys && y == x
 | [], [] => true
 | _, _ => false

-- ∀ (xs ys : List Nat), xs == ys = listNatRevertBeq xs ys ===>
-- ∀ (xs ys : List Nat), listNatBeqInverse xs ys = List.beq xs ys
-- NOTE: Test cases to ensure that structrual equivalence no match are not wrongly applied
#testOptimize ["NormRecUnchanged_3"] ∀ (xs ys : List Nat), (xs == ys) = listNatBeqInverse xs ys ===>
                                     ∀ (xs ys : List Nat), listNatBeqInverse xs ys = List.beq xs ys


def listPolyBeqInverse [BEq α] (xs : List α) (ys : List α) : Bool :=
 match xs, ys with
 | x :: xs, y :: ys => listPolyBeqInverse xs ys && x == y
 | [], [] => true
 | _, _ => false


-- ∀ (α : Type) (xs ys : List α), [BEq α] → listPolyBeq xs ys = (xs == ys) ===>
-- ∀ (α : Type) (xs ys : List α), [BEq α] → List.beq xs ys = listPolyBeqInverse xs ys
-- NOTE: Test cases to ensure that structrual equivalence no match are not wrongly applied
#testOptimize ["NormRecUnchanged_4"] ∀ (α : Type) (xs ys : List α), [BEq α] → listPolyBeqInverse xs ys = (xs == ys) ===>
                                     ∀ (α : Type) (xs ys : List α), [BEq α] → List.beq xs ys = listPolyBeqInverse xs ys


-- ∀ (xs ys : List Nat), listPolyBeq xs ys = listPolyBeqInverse xs ys ===>
-- ∀ (xs ys : List Nat), listPolyBeq xs ys = listPolyBeqInverse xs ys
-- NOTE: Test cases to ensure that structrual equivalence no match are not wrongly applied
#testOptimize ["NormRecUnchanged_5"] ∀ (xs ys : List Nat), listPolyBeq xs ys = listPolyBeqInverse xs ys ===>
                                     ∀ (xs ys : List Nat), listPolyBeq xs ys = listPolyBeqInverse xs ys


def mulNatBug (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | _, Nat.zero => 0
 | _, Nat.succ b => addNatBug x (mulNatBug x b)


def powerNatBug (a : Nat) (n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => mulNatBug a (powerNatBug a n')


-- ∀ (x y : Nat), powerNatBug x y = x ^ y ===>
-- ∀ (x y : Nat), Nat.pow x y = powerNatBug x y
#testOptimize ["NormRecUnchanged_6"] ∀ (x y : Nat), powerNatBug x y = x ^ y ===>
                                     ∀ (x y : Nat), Nat.pow x y = powerNatBug x y


def polyMul [Mul α] (x : α) (y : α) : α := x * y

-- ∀ (x y z : Int), polyMul x y > z → polyMul x.toNat y.toNat > z.toNat ===>
-- ∀ (x y z : Int), z < Int.mul x y → z.toNat < Nat.mul x.toNat y.toNat
#testOptimize ["NormRecUnchanged_7"] ∀ (x y z : Int), polyMul x y > z → polyMul x.toNat y.toNat > z.toNat ===>
                                     ∀ (x y z : Int), z < Int.mul x y → z.toNat < Nat.mul x.toNat y.toNat


-- ∀ (a b : List Int) (c d : List Nat), (listPolyBeq a b) = (listPolyBeq c d) ===>
-- ∀ (a b : List Int) (c d : List Nat), (listPolyBeq a b) = (listPolyBeq c d)
-- NOTE: test case to ensure that structural equivalence is not performed
-- on polymorphic function instantiated with different types.
#testOptimize ["NormRecUnchanged_8"]  ∀ (a b : List Int) (c d : List Nat), (listPolyBeq a b) = (listPolyBeq c d) ===>
                                      ∀ (a b : List Int) (c d : List Nat), (listPolyBeq a b) = (listPolyBeq c d)


end Tests.RecFun
