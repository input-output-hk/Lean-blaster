import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstCtorProp

/-! ## Choices inside constructor fields

Constructors keep their field-level conditionals and matches. Hoisting a choice
out of each field duplicates entire values and can grow exponentially. These
cases retain the original inputs while checking the new constructor-preserving
normal forms, including shared matches and branch-local context reuse.
-/

/-! Nondependent field choices. -/

#testOptimize [ "IteOverCtor_1" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int), [Decidable c] →
    (if c then some x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_2" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then (if b then some x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ =>
            @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
          fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_3" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then some x else (if b then some x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun _ => @Option.some Int x) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_4" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ =>
            @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => @Option.some Int y)
          fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs


#testOptimize [ "IteOverCtor_5" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else some y
    else if b then some x else none;
  let op2 := if b then [] else some y :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ =>
            @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => @Option.some Int y)
          fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b (fun _ => @List.nil (Option Int)) fun _ =>
          @List.cons (Option Int) (@Option.some Int y) (@List.nil (Option Int))))
      xs

#testOptimize [ "IteOverCtor_6" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int), [Decidable c] →
    (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int),
    @Eq (List (Int → Option Int))
      (@List.cons (Int → Option Int)
        (@Blaster.dite' (Int → Option Int) c (fun _ n => @Option.some Int (x.add n)) fun _ n =>
          @Option.some Int (x.add n.neg))
        (@List.nil (Int → Option Int)))
      xs


#testOptimize [ "IteOverCtor_7" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int), [Decidable c] →
    (if c then x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun _ => x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_8" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    [Decidable b] → [Decidable c] →
    (if c then (if b then x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) b (fun _ => x) fun _ => @Option.none Int) fun _ =>
          @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_9" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    [Decidable b] → [Decidable c] →
      (if c then some x else (if b then p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun _ => @Option.some Int x) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => p) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "IteOverCtor_10" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else p
    else if b then some x else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => p) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs


#testOptimize [ "IteOverCtor_11" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => p) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b (fun _ => @List.nil (Option Int)) fun _ =>
          @List.cons (Option Int) p (@List.nil (Option Int))))
      xs

#testOptimize [ "IteOverCtor_FunctionField" ] (norm-result: 1)
  ∀ (c : Bool) (x y z : Int),
    some ((if c then λ n => x + n else λ n => x - n) z) = some y ===>
  ∀ (c : Bool) (x y z : Int),
    @Eq (Option Int) (@Option.some Int y)
      (@Option.some Int
        (@Blaster.dite' Int (@Eq Bool Bool.true c) (fun _ => x.add z) fun _ => x.add z.neg))

#testOptimize [ "IteOverCtor_NestedTail" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then if c then [] else p :: [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => p) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b
          (fun _ =>
            @Blaster.dite' (List (Option Int)) c (fun _ => @List.nil (Option Int)) fun _ =>
              @List.cons (Option Int) p (@List.nil (Option Int)))
          fun _ => @List.cons (Option Int) p (@List.nil (Option Int))))
      xs

#testOptimize [ "IteOverCtor_13" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then if c ∨ d then [] else p :: [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) d (fun _ => @Option.some Int x) fun _ => p) fun _ =>
          @Blaster.dite' (Option Int) b (fun _ => @Option.some Int x) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b
          (fun _ =>
            @Blaster.dite' (List (Option Int)) (Or c d) (fun _ => @List.nil (Option Int)) fun _ =>
              @List.cons (Option Int) p (@List.nil (Option Int)))
          fun _ => @List.cons (Option Int) p (@List.nil (Option Int))))
      xs

/-! Test cases to validate when dite over constructor constant propagation must be applied. -/

#testOptimize [ "DIteOverCtor_1" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
    (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun h => t h x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_2" ] (norm-result: 1)
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
   [Decidable b] → [Decidable c] →
     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (t : b → Int → Option Int)
    (f : Not c → Option Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ => @Blaster.dite' (Option Int) b (fun h2 => t h2 x) fun _ => @Option.none Int) fun h1 =>
          f h1 (@Option.none Int))
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_3" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int) (f : b → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun h1 => t h1 x) fun _ =>
          @Blaster.dite' (Option Int) b (fun h2 => f h2 x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_4" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
   (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
   (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c
    then if h2 : d then t h1 x else f h2 y
    else if h3 : b then g h3 x else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int) (t : c → Int → Option Int)
    (f : Not d → Int → Option Int) (g : b → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun h1 => @Blaster.dite' (Option Int) d (fun _ => t h1 x) fun h2 => f h2 y) fun _ =>
          @Blaster.dite' (Option Int) b (fun h3 => g h3 x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_5" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
  (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
  (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c then if h2 : d then t h1 x else f h2 y
    else if h3 : b then g h3 x else none;
  let op2 := if h4 : b then g h4 y :: [] else []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int) (t : c → Int → Option Int)
    (f : Not d → Int → Option Int) (g : b → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun h1 => @Blaster.dite' (Option Int) d (fun _ => t h1 x) fun h2 => f h2 y) fun _ =>
          @Blaster.dite' (Option Int) b (fun h3 => g h3 x) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b
          (fun h4 => @List.cons (Option Int) (g h4 y) (@List.nil (Option Int))) fun _ =>
          @List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_6" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
      (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int) (t : c → Int → Option Int)
    (e : Not c → Int → Option Int),
    @Eq (List (Int → Option Int))
      (@List.cons (Int → Option Int)
        (@Blaster.dite' (Int → Option Int) c (fun h n => t h (x.add n)) fun h n => e h (x.add n.neg))
        (@List.nil (Int → Option Int)))
      xs

#testOptimize [ "DIteOverCtor_7" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
     (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun h => t h x) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_8" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (t : b → Int → Int) (f : Not c → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun _ =>
            @Blaster.dite' (Option Int) b (fun h2 => @Option.some Int (t h2 x)) fun _ =>
              @Option.none Int)
          fun h1 => f h1 x)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_9" ] (norm-result: 1)
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x p : Int) (t : c → Int → Option Int)
    (f : b → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c (fun h1 => t h1 x) fun _ =>
          @Blaster.dite' (Option Int) b (fun h2 => f h2 p) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_10" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : b → Int → Int) (g : c → Int → Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c
    then if h2 : d then some (t h2 x) else g h1 p
    else if h3 : b then some (f h3 x) else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x p : Int) (t : d → Int → Int) (f : b → Int → Int)
    (g : c → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun h1 => @Blaster.dite' (Option Int) d (fun h2 => @Option.some Int (t h2 x)) fun _ => g h1 p)
          fun _ =>
          @Blaster.dite' (Option Int) b (fun h3 => @Option.some Int (f h3 x)) fun _ => @Option.none Int)
        (@List.nil (Option Int)))
      xs

#testOptimize [ "DIteOverCtor_11" ] (norm-result: 1)
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : c → Int → Option Int) (g : b → Int → Int)
  (j : ¬ b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c then if h2 : d then some (t h2 x) else f h1 p
    else if h3 : b then some (g h3 x) else none;
  let op2 := if h4 : b then [] else j h4 p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x p : Int) (t : d → Int → Int) (f : c → Int → Option Int)
    (g : b → Int → Int) (j : Not b → Int → Option Int),
    @Eq (List (Option Int))
      (@List.cons (Option Int)
        (@Blaster.dite' (Option Int) c
          (fun h1 => @Blaster.dite' (Option Int) d (fun h2 => @Option.some Int (t h2 x)) fun _ => f h1 p)
          fun _ =>
          @Blaster.dite' (Option Int) b (fun h3 => @Option.some Int (g h3 x)) fun _ => @Option.none Int)
        (@Blaster.dite' (List (Option Int)) b (fun _ => @List.nil (Option Int)) fun h4 =>
          @List.cons (Option Int) (j h4 p) (@List.nil (Option Int))))
      xs

#testOptimize [ "DIteOverCtor_13" ] (norm-result: 1)
  ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : ¬ true = c → Int → Int),
    some ((if h : true = c then λ n => t h (x + n) else λ n => f h (x - n)) z) = some y ===>
  ∀ (c : Bool) (x y z : Int) (t : @Eq Bool Bool.true c → Int → Int) (f : @Eq Bool Bool.false c → Int → Int),
    @Eq (Option Int) (@Option.some Int y)
      (@Option.some Int
        (@Blaster.dite' Int (@Eq Bool Bool.true c) (fun h => t h (x.add z)) fun h => f (@Blaster.false_eq_of_not_true_eq c h) (x.add z.neg)))

#testOptimize [ "DIteOverCtor_14" ] (norm-result: 1)
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
    r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : Not c → Bool),
    @Eq (Option Bool) (@Option.some Bool (@Blaster.dite' Bool c t e)) r

#testOptimize [ "DIteOverCtor_15" ] (norm-result: 1)
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : Not c → Int → Bool),
    @Eq (Option (Int → Bool)) (@Option.some (Int → Bool) (@Blaster.dite' (Int → Bool) c t e)) r

/-! Matches inside constructor fields. -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def toColorOne (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some _ => .blue .transparent

#testOptimize [ "MatchOverCtor_1" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorOne n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    @Eq (List Color)
      (@List.cons Color
        (toColorOne.match_1 (fun _ => Color) n
          (fun _ => Color.black) (fun _ => Color.transparent)
          (fun _ => Color.transparent.red) (fun _ => Color.black.blue) fun _ =>
          Color.transparent.blue)
        (@List.nil Color))
      xs

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

#testOptimize [ "MatchOverCtor_2" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color),
    @Eq (List Color)
      (@List.cons Color
        (@toColorTwo.match_1 α (fun _ => Color) n
          (fun _ => Color.black) fun _ => Color.transparent.blue)
        (@List.nil Color))
      xs

def toColorThree (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some n => if n < 10 then .blue .transparent
             else if n < 100 then .red .black
             else .red .transparent

#testOptimize [ "MatchOverCtor_3" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    @Eq (List Color)
      (@List.cons Color
        (toColorOne.match_1 (fun _ => Color) n
          (fun _ => Color.black) (fun _ => Color.transparent)
          (fun _ => Color.transparent.red) (fun _ => Color.black.blue) fun val =>
          @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 10))
            (fun _ => Color.transparent.blue) fun _ =>
            @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 100))
              (fun _ => Color.black.red) fun _ => Color.transparent.red)
        (@List.nil Color))
      xs

def beqColor : Color → Color → Bool
| .red x, .red y
| .blue x, .blue y => beqColor x y
| .transparent, .transparent
| .black, .black => true
| _, _ => false

def beqColorDegree : Color → Color → (Nat → Bool)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then true else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => true
| _, _ => λ _n => false

#testOptimize [ "MatchOverCtor_4" ] (norm-result: 1)
  ∀ (x y : Color) (xs : List (Nat → Bool)), beqColorDegree x y :: [] = xs ===>
  ∀ (x y : Color) (xs : List (Nat → Bool)),
    @Eq (List (Nat → Bool))
      (@List.cons (Nat → Bool)
        (beqColor.match_1 (fun _ _ => Nat → Bool) x y
          (fun x y n =>
            @Blaster.dite' Bool (@Eq Nat (nat_lit 0) n) (fun _ => Bool.true) fun _ =>
              beqColor x y)
          (fun x y n =>
            @Blaster.dite' Bool (@Eq Nat (nat_lit 0) n) (fun _ => Bool.true) fun _ =>
              beqColor x y)
          (fun _ _ => Bool.true) (fun _ _ => Bool.true) fun _ _ _ => Bool.false)
        (@List.nil (Nat → Bool)))
      xs

#testOptimize [ "MatchOverCtor_5" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop), [Decidable c] →
    let op := if c then [] else .transparent :: [];
    toColorTwo n :: op = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop),
    @Eq (List Color)
      (@List.cons Color
        (@toColorTwo.match_1 α (fun _ => Color) n
          (fun _ => Color.black) fun _ => Color.transparent.blue)
        (@Blaster.dite' (List Color) c (fun _ => @List.nil Color)
          fun _ =>
          @List.cons Color Color.transparent
            (@List.nil Color)))
      xs

#testOptimize [ "MatchOverCtor_6" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    @Eq (List Color)
      (@List.cons Color
        (toColorOne.match_1 (fun _ => Color) n
          (fun _ => Color.black) (fun _ => Color.transparent)
          (fun _ => Color.transparent.red) (fun _ => Color.black.blue) fun val =>
          @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 10))
            (fun _ => Color.transparent.blue) fun _ =>
            @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 100))
              (fun _ => Color.black.red) fun _ => Color.transparent.red)
        (@List.cons Color
          (toColorOne.match_1 (fun _ => Color) n
            (fun _ => Color.black) (fun _ => Color.transparent)
            (fun _ => Color.transparent.red) (fun _ => Color.black.blue)
            fun val =>
            @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 10))
              (fun _ => Color.transparent.blue) fun _ =>
              @Blaster.dite' Color (@LT.lt Nat instLTNat val (nat_lit 100))
                (fun _ => Color.black.red) fun _ => Color.transparent.red)
          (@List.nil Color)))
      xs

end Tests.ConstCtorProp
