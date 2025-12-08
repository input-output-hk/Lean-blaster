import Lean
import Tests.Utils


namespace Test.NormChoiceApp
/-! ## Test objectives to validate normalization rules on choice application.
    This covers mainly normalization rules pushing function application
    over ite, dite and match.
-/

/-! Test cases to validate when normalization of function application on ite. -/


-- ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c then Nat.add x else Nat.sub x) y > 0 ===>
-- ∀ (c : Prop) (x y : Nat), y < x →
--   0 < Blaster.dite' c (fun _ : c =>  Nat.add x y) (fun _ : ¬ c => Nat.sub x y)
#testOptimize [ "NormChoiceAppIte_1" ] (norm-result: 1)
  ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c then Nat.add x else Nat.sub x) y > 0 ===>
  ∀ (c : Prop) (x y : Nat), y < x →
    0 < Blaster.dite' c (fun _ => Nat.add x y) (fun _ => Nat.sub x y)


-- ∀ (α : Type) (c : Prop) (x y : α) (f : α → α → Nat) (g : α → α → Nat), [Decidable c] →
--   (if c then f x else g x) y > 0 ===>
-- ∀ (α : Type) (c : Prop) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
--   0 < Blaster.dite' c (fun _ : c => f x y) (fun _ : ¬ c => g x y)
#testOptimize [ "NormChoiceAppIte_2" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (x y : α) (f : α → α → Nat) (g : α → α → Nat), [Decidable c] →
    (if c then f x else g x) y > 0 ===>
  ∀ (α : Type) (c : Prop) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
    0 < Blaster.dite' c (fun _ => f x y) (fun _ => g x y)


-- ∀ (α : Type) (c : Prop) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
--   [Decidable c] → (if c then f w else g w) x y z > 0 ===>
-- ∀ (α : Type) (c : Prop) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
--   0 < Blaster.dite' c (fun _ : c => f w x y z) (fun _ : ¬ c => g w x y z)
#testOptimize [ "NormChoiceAppIte_3" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
    [Decidable c] → (if c then f w else g w) x y z > 0 ===>
  ∀ (α : Type) (c : Prop) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
    0 < Blaster.dite' c (fun _ => f w x y z) (fun _ => g w x y z)

-- ∀ (α : Type) (c : Prop) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
--   [Decidable c] → (if c then f w else g w) y z = h ===>
-- ∀ (α : Type) (c : Prop) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
--   h = Blaster.dite' c (fun _ : c => λ k => f w y z k) (fun _ : ¬ c => λ k => g w y z k)
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppIte_4" ]
  ∀ (α : Type) (c : Prop) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
    [Decidable c] → (if c then f w else g w) y z = h ===>
  ∀ (α : Type) (c : Prop) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
    h = Blaster.dite' c (fun _ => λ k => f w y z k) (fun _ => λ k => g w y z k)


def getValue (xs : Array Nat) (i : USize) (h : i.toNat < xs.size) (y : Nat) : Nat :=
  let v := xs.uget i h
  if v < y then v else y

-- ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c ∨ ¬ c then Nat.add x else Nat.sub x) y > 0 ===>
-- ∀ (x y : Nat), y < x → 0 < Nat.add x y
-- NOTE: Test case to validate that the extra arguments are considered properly when
-- condition is reduced to True/False.
#testOptimize [ "NormChoiceAppIte_5" ] (norm-result: 1)
  ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c ∨ ¬ c then Nat.add x else Nat.sub x) y > 0 ===>
  ∀ (x y : Nat), y < x → 0 < Nat.add x y

-- ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c ∧ ¬ c then Nat.add x else Nat.sub x) y > 0 ===>
-- ∀ (x y : Nat), y < x → 0 < Nat.sub x y
-- NOTE: Test case to validate that the extra arguments are considered properly when
-- condition is reduced to True/False.
#testOptimize [ "NormChoiceAppIte_6" ] (norm-result: 1)
  ∀ (c : Prop) (x y : Nat), [Decidable c] → x > y → (if c ∧ ¬ c then Nat.add x else Nat.sub x) y > 0 ===>
  ∀ (x y : Nat), y < x → 0 < Nat.sub x y


/-! Test cases to validate when normalization of function application on dite. -/

-- ∀ (x : USize) (xs : Array Nat) (y : Nat) (f : Nat → Nat),
--   (if h : x.toNat < xs.size then getValue xs x h else f) y > 0 →
--   (0 < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else y else f y) ===> True
-- NOTE: We prefer to check for equivalence here, as opposed to verify the resulting optimized expression,
-- mainly to avoid having to provide the unfolded definition for xs.uget.
#testOptimize [ "NormChoiceAppDite_1" ] (norm-result: 1)
  ∀ (x : USize) (xs : Array Nat) (y : Nat) (f : Nat → Nat),
    (if h : x.toNat < xs.size then getValue xs x h else f) y > 0 →
    (0 < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else y else f y) ===> True


def getValuePolyOne [LT α] [DecidableLT α] (xs : Array α) (i : USize) (h : i.toNat < xs.size) (y : α) : α :=
  let v := xs.uget i h
  if v < y then v else y

-- ∀ (α : Type) (x : USize) (xs : Array α) (y : α) (f : α → α), [LT α] → [DecidableLT α] →
--   (if h : x.toNat < xs.size then getValuePolyOne xs x h else f) y > y →
--   (y < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else y else f y) ===> True
-- NOTE: We prefer to check for equivalence here, as opposed to verify the resulting optimized expression,
-- mainly to avoid having to provide the unfolded definition for xs.uget.
#testOptimize [ "NormChoiceAppDite_2" ] (norm-result: 1)
  ∀ (α : Type) (x : USize) (xs : Array α) (y : α) (f : α → α), [LT α] → [DecidableLT α] →
    (if h : x.toNat < xs.size then getValuePolyOne xs x h else f) y > y →
    (y < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else y else f y) ===> True


def getValuePolyTwo
  [LT α] [DecidableLT α]
  (xs : Array α) (i : USize) (h : i.toNat < xs.size) (f : α → α → α → α) (w y z : α) : α :=
  let v := xs.uget i h
  if v < y then v else f w y z

-- ∀ (α : Type) (x : USize) (xs : Array α) (w y z : α) (f : α → α → α → α), [LT α] → [DecidableLT α] →
--    (if h : x.toNat < xs.size then getValuePolyTwo xs x h f else f) w y z > y →
--    (y < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else f w y z else f w y z) ===> True
-- NOTE: We prefer to check for equivalence here, as opposed to verify the resulting optimized expression,
-- mainly to avoid having to provide the unfolded definition for xs.uget.
#testOptimize [ "NormChoiceAppDite_3" ] (norm-result: 1)
  ∀ (α : Type) (x : USize) (xs : Array α) (w y z : α) (f : α → α → α → α), [LT α] → [DecidableLT α] →
    (if h : x.toNat < xs.size then getValuePolyTwo xs x h f else f) w y z > y →
    (y < if h : x.toNat < xs.size then if xs.uget x h < y then xs.uget x h else f w y z else f w y z) ===> True

-- ∀ (α : Type) (x : USize) (xs : Array α) (w y : α) (f : α → α → α → α) (h : α → α), [LT α] → [DecidableLT α] →
--   (if h : x.toNat < xs.size then getValuePolyTwo xs x h f else f) w y = h →
--   h = if h : x.toNat < xs.size
--        then ( λ z => if xs.uget x h < y then xs.uget x h else f w y z)
--        else (λ z => f w y z) ===> True
-- NOTE: We prefer to check for equivalence here, as opposed to verify the resulting optimized expression,
-- mainly to avoid having to provide the unfolded definition for xs.uget.
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppDite_4" ] (norm-result: 1)
  ∀ (α : Type) (x : USize) (xs : Array α) (w y : α) (f : α → α → α → α) (h : α → α), [LT α] → [DecidableLT α] →
    (if hs : x.toNat < xs.size then getValuePolyTwo xs x hs f else f) w y = h →
    h = if hs : x.toNat < xs.size
         then ( λ z => if xs.uget x hs < y then xs.uget x hs else f w y z)
         else (λ z => f w y z) ===> True

-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) x > 0 ===>
-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat),
--   0 < Blaster.dite' c (fun h : c => f h x) (fun h : ¬ c => g h x)
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_5" ] (norm-result: 1)
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) x > 0 ===>
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat),
    0 < Blaster.dite' c (fun h : c => f h x) (fun h : ¬ c => g h x)

-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : c then f h x else g h) x > 0 ===>
-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat → Nat) (g : ¬ c → Nat → Nat),
--   0 < Blaster.dite' c (fun h : c => f h x x) (fun h : ¬ c => g h x)
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_6" ] (norm-result: 1)
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    (if h : c then f h x else g h) x > 0 ===>
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat → Nat) (g : ¬ c → Nat → Nat),
    0 < Blaster.dite' c (fun h : c => f h x x) (fun h : ¬ c => g h x)

-- ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) w x > 0 ===>
-- ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat),
--   0 < Blaster.dite' c (fun h : c => f h w x) (fun h : ¬ c => g h w x)
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_7" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) w x > 0 ===>
  ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat),
    0 < Blaster.dite' c (fun h : c => f h w x) (fun h : ¬ c => g h w x)

-- ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
--   (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) w = h ===>
-- ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
--   (g : ¬ c → α → Nat → Nat) (h : Nat → Nat),
--   h = Blaster.dite' c (fun h : c => λ x => f h w x) (fun h : ¬ c => λ x => g h w x)
-- NOTE: Test case to validate quantified function in dite.
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppDite_8" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
    (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) w = h ===>
  ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
    (g : ¬ c → α → Nat → Nat) (h : Nat → Nat),
    h = Blaster.dite' c (fun h : c => λ x => f h w x) (fun h : ¬ c => λ x => g h w x)

-- ∀ (x : Nat) (f : True → Nat → Nat) (g : ¬ True → Nat → Nat),
--   (if h : True then f h else g h) x > 0 ===>
-- ∀ (x : Nat) (f : True → Nat → Nat), 0 < f True.intro x
-- NOTE: Test case to validate that the extra arguments are considered properly when
-- condition is reduced to True/False.
#testOptimize [ "NormChoiceAppDite_9" ] (norm-result: 1)
  ∀ (x : Nat) (f : True → Nat → Nat) (g : ¬ True → Nat → Nat),
    (if h : True then f h else g h) x > 0 ===>
  ∀ (x : Nat) (f : True → Nat → Nat), 0 < f True.intro x

-- ∀ (x : Nat) (f : False → Nat → Nat) (g : ¬ False → Nat → Nat),
--   (if h : False then f h else g h) x > 0 ===>
-- ∀ (x : Nat) (g : True → Nat → Nat), 0 < g not_false x
-- NOTE: Test case to validate that the extra arguments are considered properly when
-- condition is reduced to True/False.
def normChoiceAddDite_10 : Lean.Expr :=
Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `g
    (Lean.Expr.forallE `h1
      (Lean.Expr.const `True [])
      (Lean.Expr.forallE `h2
        (Lean.Expr.const `Nat [])
        (Lean.Expr.const `Nat [])
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.lit (Lean.Literal.natVal 0)))
      (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `not_false [])) (Lean.Expr.bvar 1)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "normChoiceAddDite_10" : term => return normChoiceAddDite_10

#testOptimize [ "NormChoiceAppDite_10" ]
  ∀ (x : Nat) (f : False → Nat → Nat) (g : ¬ False → Nat → Nat),
    (if h : False then f h else g h) x > 0 ===> normChoiceAddDite_10

/-! Test cases to validate when normalization of function application on match. -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def toWeight (x : Color) (y : Nat) : Nat :=
  match x with
  | .red _ => 10 * y
  | .transparent => 1
  | .blue _ => 12 * y
  | .black => 0

def toNat (x : Color) : Nat → Nat :=
 match x with
 | .red c => toWeight c
 | .transparent => λ x => 5 * x
 | .blue c => toWeight c
 | .black => λ x => x + 1

-- ∀ (c : Color) (factor : Nat), factor > 0 → toNat c factor > factor ===>
-- ∀ (c : Color) (factor : Nat), 0 < factor  →
--   factor < toWeight.match_1 (fun ( _ : Color) => Nat) c
--            (fun (x : Color) =>
--               toWeight.match_1 (fun ( _ : Color) => Nat) x
--               (fun (_ : Color) => Nat.mul 10 factor)
--               (fun (_ : Unit) => 1)
--               (fun (_ : Color) => Nat.mul 12 factor)
--               (fun (_ : Unit) => 0))
--            (fun (_ : Unit) => Nat.mul 5 factor)
--            (fun (x : Color) =>
--               toWeight.match_1 (fun ( _ : Color) => Nat) x
--               (fun (_ : Color) => Nat.mul 10 factor)
--               (fun (_ : Unit) => 1)
--               (fun (_ : Color) => Nat.mul 12 factor)
--               (fun (_ : Unit) => 0))
--            (fun (_ : Unit) => Nat.add 1 factor)
#testOptimize [ "NormChoiceAppMatch_1" ] (norm-result: 1)
  ∀ (c : Color) (factor : Nat), factor > 0 → toNat c factor > factor ===>
  ∀ (c : Color) (factor : Nat), 0 < factor  →
    factor < toWeight.match_1 (fun ( _ : Color) => Nat) c
             (fun (x : Color) =>
                toWeight.match_1 (fun ( _ : Color) => Nat) x
                (fun (_ : Color) => Nat.mul 10 factor)
                (fun (_ : Unit) => 1)
                (fun (_ : Color) => Nat.mul 12 factor)
                (fun (_ : Unit) => 0))
             (fun (_ : Unit) => Nat.mul 5 factor)
             (fun (x : Color) =>
                toWeight.match_1 (fun ( _ : Color) => Nat) x
                (fun (_ : Color) => Nat.mul 10 factor)
                (fun (_ : Unit) => 1)
                (fun (_ : Color) => Nat.mul 12 factor)
                (fun (_ : Unit) => 0))
             (fun (_ : Unit) => Nat.add 1 factor)

def listToNatOne (x : List α) : Nat → Nat :=
 match x with
 | [] => λ _x => 0
 | _ :: [] => λ x => 2 * x
 | _ :: _ :: [] => λ x => 3 * x
 | _ :: _ :: _ :: [] => λ x => 4 * x
 | _ => λ x => x * x

-- ∀ (α : Type) (xs : List α) (factor : Nat), xs.length > 0 → listToNat xs factor ≥ factor ===>
-- ∀ (α : Type) (xs : List α) (factor : Nat),
--   0 < xs.length →
--    ¬ ( listToNat.match_1 (fun ( _ : List α) => Nat) xs
--        (fun (_ : Unit) => 0)
--        (fun (_ : α) => Nat.mul 2 factor)
--        (fun (_ : α) (_ : α) => Nat.mul 3 factor)
--        (fun (_ : α) (_ : α) (_ : α) => Nat.mul 4 factor)
--        (fun (_ : List α) => Nat.mul factor factor) < factor )
#testOptimize [ "NormChoiceAppMatch_2" ] (norm-result: 1)
  ∀ (α : Type) (xs : List α) (factor : Nat), xs.length > 0 → listToNatOne xs factor ≥ factor ===>
  ∀ (α : Type) (xs : List α) (factor : Nat),
    0 < xs.length →
     ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
         (fun (_ : Unit) => 0)
         (fun (_ : α) => Nat.mul 2 factor)
         (fun (_ : α) (_ : α) => Nat.mul 3 factor)
         (fun (_ : α) (_ : α) (_ : α) => Nat.mul 4 factor)
         (fun (_ : List α) => Nat.mul factor factor) < factor )

def listToNatTwo (x : List α) : Nat → Nat → Nat → Nat :=
 match x with
 | [] => λ _x _y _z => 0
 | _ :: [] => λ x y z => (2 * x) + z - y
 | _ :: _ :: [] => λ x y z  => ((3 * x) + z) * y
 | _ :: _ :: _ :: [] => λ x y z => 4 * x * y * z
 | _ => λ x y z => x * x * y * z


-- ∀ (α : Type) (xs : List α) (x y z : Nat), xs.length > 0 → listToNatTwo xs x y z ≥ 2 * x ===>
-- ∀ (α : Type) (xs : List α) (x y z : Nat),
--   0 < xs.length →
--    ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
--        (fun (_ : Unit) => 0)
--        (fun (_ : α) => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
--        (fun (_ : α) (_ : α) => Nat.mul y (Nat.add z (Nat.mul 3 x)))
--        (fun (_ : α) (_ : α) (_ : α) => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
--        (fun (_ : List α) => Nat.mul z (Nat.mul y (Nat.mul x x))) < Nat.mul 2 x)
-- NOTE: listToNatTwo.match_1 is equivalent to listToNatOne.match_1 and therefore
-- has been replaced by Lean at compilation time
#testOptimize [ "NormChoiceAppMatch_3" ] (norm-result: 1)
  ∀ (α : Type) (xs : List α) (x y z : Nat), xs.length > 0 → listToNatTwo xs x y z ≥ 2 * x ===>
  ∀ (α : Type) (xs : List α) (x y z : Nat),
    0 < xs.length →
     ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
         (fun (_ : Unit) => 0)
         (fun (_ : α) => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
         (fun (_ : α) (_ : α) => Nat.mul y (Nat.add z (Nat.mul 3 x)))
         (fun (_ : α) (_ : α) (_ : α) => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
         (fun (_ : List α) => Nat.mul z (Nat.mul y (Nat.mul x x))) < Nat.mul 2 x)


-- ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat), listToNatTwo xs x y = f ===>
-- ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat),
--   f = listToNatOne.match_1 (fun ( _ : List α) => Nat → Nat) xs
--       (fun (_ : Unit) => λ _ => 0)
--       (fun (_ : α) => λ z => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
--       (fun (_ : α) (_ : α) => λ z => Nat.mul y (Nat.add z (Nat.mul 3 x)))
--       (fun (_ : α) (_ : α) (_ : α) => λ z => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
--       (fun (_ : List α) => λ z => Nat.mul z (Nat.mul y (Nat.mul x x)))
-- NOTE: listToNatTwo.match_1 is equivalent to listToNatOne.match_1 and therefore
-- has been replaced by Lean at compilation time
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppMatch_4" ] (norm-result: 1)
  ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat), listToNatTwo xs x y = f ===>
  ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat),
    f = listToNatOne.match_1 (fun ( _ : List α) => Nat → Nat) xs
        (fun (_ : Unit) => λ _ => 0)
        (fun (_ : α) => λ z => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
        (fun (_ : α) (_ : α) => λ z => Nat.mul y (Nat.add z (Nat.mul 3 x)))
        (fun (_ : α) (_ : α) (_ : α) => λ z => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
        (fun (_ : List α) => λ z => Nat.mul z (Nat.mul y (Nat.mul x x)))


def listMap (x : List α) (a : β) (b : β) : Nat → Nat → β :=
 match x with
 | [] => λ x y => if x < y then a else b
 | _ :: [] => λ x y => if 2 * x < y then a else b
 | _ :: _ :: [] => λ x y  => if 3 * x < y then a else b
 | _ :: _ :: _ :: [] => λ x y => if 4 * x < y then a else b
 | _ => λ x y => if x * x < y then a else b


-- ∀ (α : Type) (xs : List α) (x y z : Nat), xs.length > 0 → listToNatTwo xs x y z ≥ 2 * x ===>
-- ∀ (α : Type) (xs : List α) (x y z : Nat),
--   0 < xs.length →
--    ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
--        (fun (_ : Unit) => 0)
--        (fun (_ : α) => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
--        (fun (_ : α) (_ : α) => Nat.mul y (Nat.add z (Nat.mul 3 x)))
--        (fun (_ : α) (_ : α) (_ : α) => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
--        (fun (_ : List α) => Nat.mul z (Nat.mul y (Nat.mul x x))) < Nat.mul 2 x)
-- NOTE: listMap.match_1 is equivalent to listToNatOne.match_1 and therefore
-- has been replaced by Lean at compilation time
-- NOTE: Test case to validate polymorphic return type
#testOptimize [ "NormChoiceAppMatch_5" ] (norm-result: 1)
  ∀ (α : Type) (β : Type) (xs : List α) (a b : β) (x y : Nat),
     x > y → listMap xs a b x y = b ===>
  ∀ (α : Type) (β : Type) (xs : List α) (a b : β) (x y : Nat),
     y < x →
       b = listToNatOne.match_1 (fun (_ : List α) => β) xs
           (fun (_ : Unit) => b) -- simplified due to hypothesis simp rule as we have y < x in hyp
           (fun (_ : α) =>
             Blaster.dite' (Nat.mul 2 x < y) (fun _ => a) (fun _ => b))
           (fun (_ : α) (_ : α) =>
             Blaster.dite' (Nat.mul 3 x < y) (fun _ => a) (fun _ => b))
           (fun (_ : α) (_ : α) (_ : α) =>
             Blaster.dite' (Nat.mul 4 x < y) (fun _ => a) (fun _ => b))
           (fun (_ : List α) =>
             Blaster.dite' (Nat.mul x x < y) (fun _ => a) (fun _ => b))

end Test.NormChoiceApp
