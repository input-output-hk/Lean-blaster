import Lean
import Tests.Utils


namespace Test.NormChoiceApp
/-! ## Test objectives to validate normalization rules on choice application.
    This covers mainly normalization rules pushing function application
    over ite, dite and match.
-/

/-! Test cases to validate when normalization of function application on ite. -/

-- ∀ (c : Bool) (x y : Nat), x > y → (if c then Nat.add x else Nat.sub x) y > 0 ===>
-- ∀ (c : Bool) (x y : Nat), y < x → 0 < if true = c then Nat.add x y else Nat.sub x y
#testOptimize [ "NormChoiceAppIte_1" ] (norm-result: 1)
  ∀ (c : Bool) (x y : Nat), x > y → (if c then Nat.add x else Nat.sub x) y > 0 ===>
  ∀ (c : Bool) (x y : Nat), y < x → 0 < if true = c then Nat.add x y else Nat.sub x y

-- ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
--   (if c then f x else g x) y > 0 ===>
-- ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
--   0 < if true = c then f x y else g x y
#testOptimize [ "NormChoiceAppIte_2" ] (norm-result: 1)
  ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
    (if c then f x else g x) y > 0 ===>
  ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
    0 < if true = c then f x y else g x y


-- ∀ (α : Type) (c : Bool) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
--   (if c then f w else g w) x y z > 0 ===>
-- ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
--   0 < if true = c then f x y else g x y
#testOptimize [ "NormChoiceAppIte_3" ] (norm-result: 1)
  ∀ (α : Type) (c : Bool) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
    (if c then f w else g w) x y z > 0 ===>
  ∀ (α : Type) (c : Bool) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
    0 < if true = c then f w x y z else g w x y z

-- ∀ (α : Type) (c : Bool) (w x y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat),
--   (if c then f w else g w) x y z > 0 ===>
-- ∀ (α : Type) (c : Bool) (x y : α) (f : α → α → Nat) (g : α → α → Nat),
--   0 < if true = c then f x y else g x y
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppIte_4" ]
  ∀ (α : Type) (c : Bool) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
    (if c then f w else g w) y z = h ===>
  ∀ (α : Type) (c : Bool) (w y z : α) (f : α → α → α → α → Nat) (g : α → α → α → α → Nat) (h : α → Nat),
    h = (if true = c then λ k => f w y z k else λ k => g w y z k)


def getValue (xs : Array Nat) (i : USize) (h : i.toNat < xs.size) (y : Nat) : Nat :=
  let v := xs.uget i h
  if v < y then v else y


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
--   (if h : x.toNat < xs.size then getValuePoly xs x h else f) y > y →
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
    (if h : x.toNat < xs.size then getValuePolyTwo xs x h f else f) w y = h →
    h = if h : x.toNat < xs.size
         then ( λ z => if xs.uget x h < y then xs.uget x h else f w y z)
         else (λ z => f w y z) ===> True


-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) x > 0 ===>
-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   0 < if h : c then f h x else g h x
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_5" ] (norm-result: 1)
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) x > 0 ===>
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    0 < if h : c then f h x else g h x


-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) x > 0 ===>
-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   0 < if h : c then f h x else g h x
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_6" ] (norm-result: 1)
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) x > 0 ===>
  ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
    0 < if h : c then f h x else g h x


-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) x > 0 ===>
-- ∀ (c : Prop) (x : Nat) (f : c → Nat → Nat) (g : ¬ c → Nat → Nat), [Decidable c] →
--   0 < if h : c then f h x else g h x
-- NOTE: Test case to validate quantified function in dite.
#testOptimize [ "NormChoiceAppDite_7" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) w x > 0 ===>
  ∀ (α : Type) (c : Prop) (x : Nat) (w : α) (f : c → α → Nat → Nat) (g : ¬ c → α → Nat → Nat), [Decidable c] →
    0 < if h : c then f h w x else g h w x


-- ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
--   (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
--   (if h : c then f h else g h) w = h ===>
-- ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
--   (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
--   h = if h : c then λ x => f h w x else λ x => g h w x
-- NOTE: Test case to validate quantified function in dite.
-- NOTE: Test case to validate partially applied function
#testOptimize [ "NormChoiceAppDite_8" ] (norm-result: 1)
  ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
    (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
    (if h : c then f h else g h) w = h ===>
  ∀ (α : Type) (c : Prop) (w : α) (f : c → α → Nat → Nat)
    (g : ¬ c → α → Nat → Nat) (h : Nat → Nat), [Decidable c] →
    h = if h : c then λ x => f h w x else λ x => g h w x


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
--               (fun (_ : PUnit) => 1)
--               (fun (_ : Color) => Nat.mul 12 factor)
--               (fun (_ : PUnit) => 0))
--            (fun (_ : PUnit) => Nat.mul 5 factor)
--            (fun (x : Color) =>
--               toWeight.match_1 (fun ( _ : Color) => Nat) x
--               (fun (_ : Color) => Nat.mul 10 factor)
--               (fun (_ : PUnit) => 1)
--               (fun (_ : Color) => Nat.mul 12 factor)
--               (fun (_ : PUnit) => 0))
--            (fun (_ : PUnit) => Nat.add 1 factor)
#testOptimize [ "NormChoiceAppMatch_1" ] (norm-result: 1)
  ∀ (c : Color) (factor : Nat), factor > 0 → toNat c factor > factor ===>
  ∀ (c : Color) (factor : Nat), 0 < factor  →
    factor < toWeight.match_1 (fun ( _ : Color) => Nat) c
             (fun (x : Color) =>
                toWeight.match_1 (fun ( _ : Color) => Nat) x
                (fun (_ : Color) => Nat.mul 10 factor)
                (fun (_ : PUnit) => 1)
                (fun (_ : Color) => Nat.mul 12 factor)
                (fun (_ : PUnit) => 0))
             (fun (_ : PUnit) => Nat.mul 5 factor)
             (fun (x : Color) =>
                toWeight.match_1 (fun ( _ : Color) => Nat) x
                (fun (_ : Color) => Nat.mul 10 factor)
                (fun (_ : PUnit) => 1)
                (fun (_ : Color) => Nat.mul 12 factor)
                (fun (_ : PUnit) => 0))
             (fun (_ : PUnit) => Nat.add 1 factor)

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
--        (fun (_ : PUnit) => 0)
--        (fun (_ : α) => Nat.mul 2 factor)
--        (fun (_ : α) (_ : α) => Nat.mul 3 factor)
--        (fun (_ : α) (_ : α) (_ : α) => Nat.mul 4 factor)
--        (fun (_ : List α) => Nat.mul factor factor) < factor )
#testOptimize [ "NormChoiceAppMatch_2" ] (norm-result: 1)
  ∀ (α : Type) (xs : List α) (factor : Nat), xs.length > 0 → listToNatOne xs factor ≥ factor ===>
  ∀ (α : Type) (xs : List α) (factor : Nat),
    0 < xs.length →
     ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
         (fun (_ : PUnit) => 0)
         (fun (_ : α) => Nat.mul 2 factor)
         (fun (_ : α) (_ : α) => Nat.mul 3 factor)
         (fun (_ : α) (_ : α) (_ : α) => Nat.mul 4 factor)
         (fun (_ : List α) => Nat.mul factor factor) < factor )

def listToNatTwo (x : List α) : Nat → Nat → Nat → Nat :=
 match x with
 | [] => λ _x _y _z => 0
 | _ :: [] => λ x y z=> (2 * x) + z - y
 | _ :: _ :: [] => λ x y z  => ((3 * x) + z) * y
 | _ :: _ :: _ :: [] => λ x y z => 4 * x * y * z
 | _ => λ x y z => x * x * y * z


-- ∀ (α : Type) (xs : List α) (x y z : Nat), xs.length > 0 → listToNatTwo xs x y z ≥ 2 * x ===>
-- ∀ (α : Type) (xs : List α) (x y z : Nat),
--   0 < xs.length →
--    ¬ ( listToNatOne.match_1 (fun ( _ : List α) => Nat) xs
--        (fun (_ : PUnit) => 0)
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
         (fun (_ : PUnit) => 0)
         (fun (_ : α) => Nat.sub (Nat.add z (Nat.mul 2 x)) y)
         (fun (_ : α) (_ : α) => Nat.mul y (Nat.add z (Nat.mul 3 x)))
         (fun (_ : α) (_ : α) (_ : α) => Nat.mul z (Nat.mul y (Nat.mul 4 x)))
         (fun (_ : List α) => Nat.mul z (Nat.mul y (Nat.mul x x))) < Nat.mul 2 x)


-- ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat), listToNatTwo xs x y = f ===>
-- ∀ (α : Type) (xs : List α) (x y : Nat) (f : Nat → Nat),
--   f = listToNatOne.match_1 (fun ( _ : List α) => Nat → Nat) xs
--       (fun (_ : PUnit) => λ _ => 0)
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
        (fun (_ : PUnit) => λ _ => 0)
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
--        (fun (_ : PUnit) => 0)
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
           (fun (_ : PUnit) => b) -- simplified due to hypothesis simp rule as we have y < x in hyp
           (fun (_ : α) => if Nat.mul 2 x < y then a else b)
           (fun (_ : α) (_ : α) => if Nat.mul 3 x < y then a else b)
           (fun (_ : α) (_ : α) (_ : α) => if Nat.mul 4 x < y then a else b)
           (fun (_ : List α) => if Nat.mul x x < y then a else b)


end Test.NormChoiceApp
