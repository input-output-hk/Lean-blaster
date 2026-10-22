import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.UnifyPattern

/-! ## Test objectives to validate pattern/discriminator unification on match alternatives
     (i.e., `unifyAndUpdateEqMap`): when a match expression is neither reduced nor normalized
     to `ite`, each discriminator is unified with the pattern of the alternative being optimized
     and the resulting equalities are propagated in the rhs of the alternative through the
     equality map.

     NOTE: In every test case below, the first alternative cannot be decided (its pattern contains
     a literal/constructor compared with a free variable) so that choice reduction does not apply,
     and at least one pattern is a constructor application with free variables of a user-defined
     inductive type so that the match is not normalized to `ite`.

     NOTE: The named pattern hypothesis sections cover the hypothesis of a named pattern (`p@hp:pat`),
     which is instantiated with `Eq.refl` both when the match is reduced and when it is not.

     NOTE: The last sections cover constructors with inductive parameters and proof fields, cascades
     of named patterns, discriminators containing a `forallE` or a lambda, string and character
     literal patterns vs the different string/character representations, and `Int.ofNat` patterns
     vs negated `Int.ofNat` discriminators.

-/

inductive Value where
  | nat : Nat → Value
  | int : Int → Value
  | str : String → Value
  | pair : Nat → Nat → Value
  | wrap : Value → Nat → Value
  | unit : Value
  | none : Value
  deriving Inhabited

opaque v0 : Value

variable (m n : Nat) (w : Int) (s : String) (c1 c2 : Char) (cs : List Char) (ms : List Nat) (v u : Value)
variable (h : Nat → Nat) (hi : Int → Int) (f : Nat → Value) (g : Value → Nat) (gi : Int → Nat)

/-! ### Variable patterns and Nat literal patterns -/

def natArg (x : Value) (z : Nat) : Nat :=
  match x with
  | .nat 5 => z + 100
  | .nat k => k + z
  | _ => 0

-- natArg (.nat m) m ===>
--   match Value.nat m with
--   | .nat 5 => 105
--   | .nat k => Nat.add m m
--   | _ => 0
-- NOTE: literal pattern vs free variable discriminator binds `m := 5`,
--       variable pattern vs free variable discriminator binds `k := m`
#testOptimize [ "UnifyPattern_1" ] (norm-result: 1)
  natArg (.nat m) m ===>
    match Value.nat m with
    | .nat 5 => 105
    | .nat _k => Nat.add m m
    | _ => 0

-- natArg (.nat (m + 2)) m ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 103
--   | .nat k => Nat.add m (Nat.add 2 m)
--   | _ => 0
-- NOTE: literal pattern vs offset discriminator `2 + m` binds `m := 3` (5 ≥ 2),
--       variable pattern vs expression discriminator binds `k := 2 + m`
#testOptimize [ "UnifyPattern_2" ] (norm-result: 1)
  natArg (.nat (m + 2)) m ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 103
    | .nat _k => Nat.add m (Nat.add 2 m)
    | _ => 0

def pairArg (x : Value) (z : Nat) : Nat :=
  match x with
  | .pair _ 3 => z + 100
  | .pair 5 k => k + z
  | .pair 7 k => k * z
  | .pair j k => j + k + z
  | _ => 0

-- pairArg (.pair 5 m) m ===>
--   match Value.pair 5 m with
--   | .pair _ 3 => 103
--   | .pair 5 k => Nat.add m m
--   | .pair 7 k => Nat.mul m k
--   | .pair j k => Nat.add m (Nat.add 5 m)
--   | _ => 0
-- NOTE: equal literals (`5` vs `5`) continue the unification with the pending arguments (`k := m`),
--       distinct literals (`7` vs `5`) stop the unification (`k` is left unbound)
#testOptimize [ "UnifyPattern_3" ] (norm-result: 1)
  pairArg (.pair 5 m) m ===>
    match Value.pair 5 m with
    | .pair _ 3 => 103
    | .pair 5 _k => Nat.add m m
    | .pair 7 k => Nat.mul m k
    | .pair _j _k => Nat.add m (Nat.add 5 m)
    | _ => 0

-- pairArg (.pair (h m + 2) m) (h m) ===>
--   match Value.pair (Nat.add 2 (h m)) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add 3 m
--   | .pair 7 k => Nat.mul 5 m
--   | .pair j k => Nat.add (h m) (Nat.add m (Nat.add 2 (h m)))
--   | _ => 0
-- NOTE: literal pattern vs offset discriminator `2 + h m` binds the expression `h m := 3` and `h m := 5`
#testOptimize [ "UnifyPattern_4" ] (norm-result: 1)
  pairArg (.pair (h m + 2) m) (h m) ===>
    match Value.pair (Nat.add 2 (h m)) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 _k => Nat.add 3 m
    | .pair 7 _k => Nat.mul 5 m
    | .pair _j _k => Nat.add (h m) (Nat.add m (Nat.add 2 (h m)))
    | _ => 0

-- pairArg (.pair (h m + 7) m) (h m) ===>
--   match Value.pair (Nat.add 7 (h m)) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add k (h m)
--   | .pair 7 k => 0
--   | .pair j k => Nat.add (h m) (Nat.add m (Nat.add 7 (h m)))
--   | _ => 0
-- NOTE: literal `5` smaller than offset `7` stops the unification (`k` is left unbound),
--       literal `7` vs offset `7 + h m` binds `h m := 0`
#testOptimize [ "UnifyPattern_5" ] (norm-result: 1)
  pairArg (.pair (h m + 7) m) (h m) ===>
    match Value.pair (Nat.add 7 (h m)) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 k => Nat.add k (h m)
    | .pair 7 _k => 0
    | .pair _j _k => Nat.add (h m) (Nat.add m (Nat.add 7 (h m)))
    | _ => 0

-- pairArg (.pair (h m) m) (h m) ===>
--   match Value.pair (h m) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add 5 m
--   | .pair 7 k => Nat.mul 7 m
--   | .pair j k => Nat.add (h m) (Nat.add m (h m))
--   | _ => 0
-- NOTE: literal pattern vs non constructor application discriminator binds `h m := 5` and `h m := 7`
#testOptimize [ "UnifyPattern_6" ] (norm-result: 1)
  pairArg (.pair (h m) m) (h m) ===>
    match Value.pair (h m) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 _k => Nat.add 5 m
    | .pair 7 _k => Nat.mul 7 m
    | .pair _j _k => Nat.add (h m) (Nat.add m (h m))
    | _ => 0

/-! ### Nat offset patterns (`k + c`) -/

def natOffset (x : Value) (z : Nat) : Nat :=
  match x with
  | .nat 5 => z + 100
  | .nat (k + 2) => k + z
  | .nat k => k * z
  | _ => 0

-- natOffset (.nat (m + 5)) m ===>
--   match Value.nat (Nat.add 5 m) with
--   | .nat 5 => 100
--   | .nat (k + 2) => Nat.add m (Nat.add 3 m)
--   | .nat k => Nat.mul m (Nat.add 5 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `5 + m` binds `k := 3 + m` (2 < 5)
#testOptimize [ "UnifyPattern_7" ] (norm-result: 1)
  natOffset (.nat (m + 5)) m ===>
    match Value.nat (Nat.add 5 m) with
    | .nat 5 => 100
    | .nat (_k + 2) => Nat.add m (Nat.add 3 m)
    | .nat _k => Nat.mul m (Nat.add 5 m)
    | _ => 0

-- natOffset (.nat (m + 2)) m ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 103
--   | .nat (k + 2) => Nat.add m m
--   | .nat k => Nat.mul m (Nat.add 2 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `2 + m` binds `k := m` (2 = 2)
#testOptimize [ "UnifyPattern_8" ] (norm-result: 1)
  natOffset (.nat (m + 2)) m ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 103
    | .nat (_k + 2) => Nat.add m m
    | .nat _k => Nat.mul m (Nat.add 2 m)
    | _ => 0

-- natOffset (.nat (m + 1)) m ===>
--   match Value.nat (Nat.add 1 m) with
--   | .nat 5 => 104
--   | .nat (k + 2) => Nat.add k (Nat.add 1 k)
--   | .nat k => Nat.mul m (Nat.add 1 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `1 + m` binds `m := 1 + k` (2 > 1)
#testOptimize [ "UnifyPattern_9" ] (norm-result: 1)
  natOffset (.nat (m + 1)) m ===>
    match Value.nat (Nat.add 1 m) with
    | .nat 5 => 104
    | .nat (k + 2) => Nat.add k (Nat.add 1 k)
    | .nat _k => Nat.mul m (Nat.add 1 m)
    | _ => 0

-- natOffset (.nat m) m ===>
--   match Value.nat m with
--   | .nat 5 => 105
--   | .nat (k + 2) => Nat.add k (Nat.add 2 k)
--   | .nat k => Nat.mul m m
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs free variable discriminator binds `m := 2 + k`
#testOptimize [ "UnifyPattern_10" ] (norm-result: 1)
  natOffset (.nat m) m ===>
    match Value.nat m with
    | .nat 5 => 105
    | .nat (k + 2) => Nat.add k (Nat.add 2 k)
    | .nat _k => Nat.mul m m
    | _ => 0

-- natOffset (.nat (h m)) (h m) ===>
--   match Value.nat (h m) with
--   | .nat 5 => 105
--   | .nat (k + 2) => Nat.add k (Nat.add 2 k)
--   | .nat k => Nat.mul (h m) (h m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs non constructor application discriminator binds `h m := 2 + k`
#testOptimize [ "UnifyPattern_11" ] (norm-result: 1)
  natOffset (.nat (h m)) (h m) ===>
    match Value.nat (h m) with
    | .nat 5 => 105
    | .nat (k + 2) => Nat.add k (Nat.add 2 k)
    | .nat _k => Nat.mul (h m) (h m)
    | _ => 0

def wrapNat (x : Value) (z : Nat) : Nat :=
  match x with
  | .wrap _ 5 => z + 100
  | .wrap (.nat 5) j => z + j
  | .wrap (.nat (k + 2)) j => k + j + z
  | .wrap (.nat k) j => k * j * z
  | _ => 0

-- wrapNat (.wrap (.nat 7) m) m ===>
--   match Value.wrap (Value.nat 7) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m j
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add 5 m)
--   | .wrap (.nat k) j => Nat.mul m (Nat.mul 7 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs literal discriminator `7` binds `k := 5` (7 ≥ 2),
--       distinct literals (`5` vs `7`) stop the unification (`j` is left unbound)
#testOptimize [ "UnifyPattern_12" ] (norm-result: 1)
  wrapNat (.wrap (.nat 7) m) m ===>
    match Value.wrap (Value.nat 7) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) j => Nat.add m j
    | .wrap (.nat (_k + 2)) _j => Nat.add m (Nat.add 5 m)
    | .wrap (.nat _k) _j => Nat.mul m (Nat.mul 7 m)
    | _ => 0

-- wrapNat (.wrap (.nat 1) m) m ===>
--   match Value.wrap (Value.nat 1) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m j
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add k j)
--   | .wrap (.nat k) j => Nat.mul m m
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs literal discriminator `1` stops the unification (1 < 2)
#testOptimize [ "UnifyPattern_13" ] (norm-result: 1)
  wrapNat (.wrap (.nat 1) m) m ===>
    match Value.wrap (Value.nat 1) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) j => Nat.add m j
    | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add k j)
    | .wrap (.nat _k) _j => Nat.mul m m
    | _ => 0

-- wrapNat (.wrap (.nat 5) m) m ===>
--   match Value.wrap (Value.nat 5) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m m
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add 3 m)
--   | .wrap (.nat k) j => Nat.mul m (Nat.mul 5 m)
--   | _ => 0
-- NOTE: equal literals (`5` vs `5`) continue the unification with the pending arguments (`j := m`)
#testOptimize [ "UnifyPattern_14" ] (norm-result: 1)
  wrapNat (.wrap (.nat 5) m) m ===>
    match Value.wrap (Value.nat 5) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) _j => Nat.add m m
    | .wrap (.nat (_k + 2)) _j => Nat.add m (Nat.add 3 m)
    | .wrap (.nat _k) _j => Nat.mul m (Nat.mul 5 m)
    | _ => 0

/-! ### Int patterns (`Int.ofNat`, `Int.negSucc`, literals and offsets) -/

def intArg (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .int 3 => gi z + 100
  | .int (.ofNat 7) => gi z + 107
  | .int (.negSucc 2) => gi z + 300
  | .int (.ofNat (k + 1)) => gi z + k
  | .int (.negSucc (k + 1)) => gi z + 2 * k
  | .int (.ofNat k) => gi z + 3 * k
  | .int (.negSucc k) => gi z + 4 * k
  | _ => 0

-- intArg gi (.int (Int.ofNat m)) (Int.ofNat m) ===>
--   match Value.int (Int.ofNat m) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat m))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 m)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat` patterns unify with the `Int.ofNat m` discriminator (`m := 3`, `m := 7`, `m := 1 + k`, `k := m`),
--       `Int.negSucc` patterns (normalized to `Int.neg (Int.ofNat _)` or kept as literals) do not unify
#testOptimize [ "UnifyPattern_15" ] (norm-result: 1)
  intArg gi (.int (Int.ofNat m)) (Int.ofNat m) ===>
    match Value.int (Int.ofNat m) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat m))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 k)
    | .int (.ofNat _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 m)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (Int.ofNat (m + 2))) (Int.ofNat (m + 2)) ===>
--   match Value.int (Int.ofNat (Nat.add 2 m)) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat (Nat.add 2 m)))
--   | .int (.ofNat (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.add 1 m)
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 3 (Nat.add 2 m))
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat` literal patterns vs offset discriminator `2 + m` bind `m := 1` and `m := 5`,
--       offset pattern `1 + k` vs offset discriminator `2 + m` binds `k := 1 + m`
#testOptimize [ "UnifyPattern_16" ] (norm-result: 1)
  intArg gi (.int (Int.ofNat (m + 2))) (Int.ofNat (m + 2)) ===>
    match Value.int (Int.ofNat (Nat.add 2 m)) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat (Nat.add 2 m)))
    | .int (.ofNat (_k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.add 1 m)
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 2 k)
    | .int (.ofNat _k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 3 (Nat.add 2 m))
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int w) w ===>
--   match Value.int w with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: every Int pattern binds the free variable discriminator `w` to its (normalized) pattern
#testOptimize [ "UnifyPattern_17" ] (norm-result: 1)
  intArg gi (.int w) w ===>
    match Value.int w with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-w)) (-w) ===>
--   match Value.int (Int.neg w) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat _` and `Int.negSucc _` patterns vs `Int.neg w` discriminator (`w` not an `Int.ofNat`
--       expression) bind the expression `Int.neg w` to the pattern
#testOptimize [ "UnifyPattern_18" ] (norm-result: 1)
  intArg gi (.int (-w)) (-w) ===>
    match Value.int (Int.neg w) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (hi w)) (hi w) ===>
--   match Value.int (hi w) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: every Int pattern binds the non constructor application discriminator `hi w` to its pattern
#testOptimize [ "UnifyPattern_19" ] (norm-result: 1)
  intArg gi (.int (hi w)) (hi w) ===>
    match Value.int (hi w) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

def intNegDiscr (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .int (.ofNat 7) => gi z + 107
  | .int (.negSucc 2) => gi z + 300
  | .int (.ofNat (k + 1)) => gi z + k
  | .int (.ofNat k) => gi z + 3 * k
  | _ => 0

-- intNegDiscr gi (.int (Int.negSucc m)) (Int.negSucc m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
--   | .int (.ofNat k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 m)))) (Nat.mul 3 k)
--   | _ => 0
-- NOTE: `Int.negSucc m` discriminator is normalized to `Int.neg (Int.ofNat (1 + m))`:
--       `Int.ofNat` patterns do not unify, the `Int.negSucc 2` literal pattern binds `m := 2`
--       (`3` vs `1 + m`), and `Int.neg (Int.ofNat 3)` is folded back to `Int.negSucc 2`
#testOptimize [ "UnifyPattern_20" ] (norm-result: 1)
  intNegDiscr gi (.int (Int.negSucc m)) (Int.negSucc m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
    | .int (.ofNat k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 m)))) (Nat.mul 3 k)
    | _ => 0

def intLit (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .wrap (.int 3) j => gi z + j + 100
  | .wrap (.int (.negSucc 2)) j => gi z + j + 300
  | .wrap (.int (.ofNat (k + 1))) j => gi z + k + j
  | .wrap (.int (.negSucc (k + 1))) j => gi z + 2 * k + j
  | .wrap (.int (.ofNat k)) j => gi z + 3 * k + j
  | .wrap (.int (.negSucc k)) j => gi z + 4 * k + j
  | _ => 0

-- intLit gi (.wrap (.int 3) m) 3 ===>
--   match Value.wrap (Value.int (Int.ofNat 3)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add m (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 3)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add m (Nat.add 2 (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add m (Nat.add 9 (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 4 k))
--   | _ => 0
-- NOTE: positive literal discriminator: `Int.ofNat` patterns unify (`j := m`, `k := 2`, `k := 3`),
--       `Int.negSucc` patterns stop the unification (`j` is left unbound)
#testOptimize [ "UnifyPattern_21" ] (norm-result: 1)
  intLit gi (.wrap (.int 3) m) 3 ===>
    match Value.wrap (Value.int (Int.ofNat 3)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) _j => Nat.add 100 (Nat.add m (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 3)))
    | .wrap (.int (.ofNat (_k + 1))) _j => Nat.add m (Nat.add 2 (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat _k)) _j => Nat.add m (Nat.add 9 (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 4 k))
    | _ => 0

-- intLit gi (.wrap (.int (-3)) m) (-3) ===>
--   match Value.wrap (Value.int (Int.negSucc 2)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 2)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add m (gi (Int.negSucc 2)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 2)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add m (Nat.add 2 (gi (Int.negSucc 2)))
--   | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 2)) (Nat.mul 3 k))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (Nat.add 8 (gi (Int.negSucc 2)))
--   | _ => 0
-- NOTE: negative literal discriminator `Int.negSucc 2`: the `Int.negSucc 2` literal pattern continues
--       the unification (`j := m`), `Int.negSucc (k + 1)` (normalized to `Int.neg (Int.ofNat (2 + k))`)
--       binds `k := 1` (`2 + k` vs `3`), `Int.negSucc k` binds `k := 2`, `Int.ofNat` patterns stop the unification
#testOptimize [ "UnifyPattern_22" ] (norm-result: 1)
  intLit gi (.wrap (.int (-3)) m) (-3) ===>
    match Value.wrap (Value.int (Int.negSucc 2)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 2)))
    | .wrap (.int (.negSucc 2)) _j => Nat.add 300 (Nat.add m (gi (Int.negSucc 2)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 2)))
    | .wrap (.int (.negSucc (_k + 1))) _j => Nat.add m (Nat.add 2 (gi (Int.negSucc 2)))
    | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 2)) (Nat.mul 3 k))
    | .wrap (.int (.negSucc _k)) _j => Nat.add m (Nat.add 8 (gi (Int.negSucc 2)))
    | _ => 0

-- intLit gi (.wrap (.int 0) m) 0 ===>
--   match Value.wrap (Value.int (Int.ofNat 0)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.ofNat 0)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 0)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.ofNat 0)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add m (gi (Int.ofNat 0))
--   | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 4 k))
--   | _ => 0
-- NOTE: offset pattern `Int.ofNat (1 + k)` vs literal `Int.ofNat 0` stops the unification (0 < 1),
--       `Int.ofNat k` binds `k := 0` and `j := m`
#testOptimize [ "UnifyPattern_23" ] (norm-result: 1)
  intLit gi (.wrap (.int 0) m) 0 ===>
    match Value.wrap (Value.int (Int.ofNat 0)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.ofNat 0)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 0)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.ofNat 0)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat _k)) _j => Nat.add m (gi (Int.ofNat 0))
    | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 4 k))
    | _ => 0

-- intLit gi (.wrap (.int (-1)) m) (-1) ===>
--   match Value.wrap (Value.int (Int.negSucc 0)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 0)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.negSucc 0)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 0)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 3 k))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (gi (Int.negSucc 0))
--   | _ => 0
-- NOTE: `Int.negSucc (k + 1)` (normalized to `Int.neg (Int.ofNat (2 + k))`) vs literal `Int.negSucc 0`
--       stops the unification (1 < 2), `Int.negSucc 2` vs `Int.negSucc 0` stops the unification,
--       `Int.negSucc k` binds `k := 0` and `j := m`
#testOptimize [ "UnifyPattern_24" ] (norm-result: 1)
  intLit gi (.wrap (.int (-1)) m) (-1) ===>
    match Value.wrap (Value.int (Int.negSucc 0)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 0)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.negSucc 0)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 0)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 3 k))
    | .wrap (.int (.negSucc _k)) _j => Nat.add m (gi (Int.negSucc 0))
    | _ => 0

/-! ### String patterns (literals and `String.mk`) -/

def strLit (x : Value) (z : String) : Nat :=
  match x with
  | .str "ab" => z.length + 100
  | .str _ => z.length
  | _ => 0

-- strLit (.str s) s ===>
--   match Value.str s with
--   | .str "ab" => 102
--   | .str _ => String.length s
--   | _ => 0
-- NOTE: string literal pattern vs free variable discriminator binds `s := "ab"`
#testOptimize [ "UnifyPattern_25" ] (norm-result: 1)
  strLit (.str s) s ===>
    match Value.str s with
    | .str "ab" => 102
    | .str _ => String.length s
    | _ => 0

-- strLit (.str (String.mk [c1, c2])) (String.mk [c1, c2]) ===>
--   match Value.str (String.mk [c1, c2]) with
--   | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
--   | .str _ => String.length (String.mk [c1, c2])
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk` discriminator is unified as a list of characters
--       (`c1 := 'a'`, `c2 := 'b'`)
#testOptimize [ "UnifyPattern_26" ] (norm-result: 1)
  strLit (.str (String.mk [c1, c2])) (String.mk [c1, c2]) ===>
    match Value.str (String.mk [c1, c2]) with
    | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
    | .str _ => String.length (String.mk [c1, c2])
    | _ => 0

-- strLit (.str (String.mk cs)) (String.mk cs) ===>
--   match Value.str (String.mk cs) with
--   | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
--   | .str _ => String.length (String.mk cs)
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk cs` discriminator binds `cs := ['a', 'b']`
#testOptimize [ "UnifyPattern_27" ] (norm-result: 1)
  strLit (.str (String.mk cs)) (String.mk cs) ===>
    match Value.str (String.mk cs) with
    | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
    | .str _ => String.length (String.mk cs)
    | _ => 0

def strCtor (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str ⟨cs⟩) j => cs.length + z.length + j
  | _ => 0

-- strCtor (.wrap (.str s) m) s ===>
--   match Value.wrap (Value.str s) m with
--   | .wrap _ 5 => Nat.add 100 (String.length s)
--   | .wrap (.str ⟨cs⟩) j => Nat.add m (Nat.add (String.length (String.mk cs)) (List.length cs))
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs free variable discriminator binds `s := String.mk cs`
#testOptimize [ "UnifyPattern_28" ] (norm-result: 1)
  strCtor (.wrap (.str s) m) s ===>
    match Value.wrap (Value.str s) m with
    | .wrap _ 5 => Nat.add 100 (String.length s)
    | .wrap (.str ⟨cs⟩) _j => Nat.add m (Nat.add (String.length (String.mk cs)) (List.length cs))
    | _ => 0

-- strCtor (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
--   match Value.wrap (Value.str (String.mk [c1, c2])) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
--   | .wrap (.str ⟨cs⟩) j => Nat.add m (Nat.add 2 (String.length (String.mk [c1, c2])))
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs `String.mk [c1, c2]` discriminator binds `cs := [c1, c2]`
#testOptimize [ "UnifyPattern_29" ] (norm-result: 1)
  strCtor (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
    match Value.wrap (Value.str (String.mk [c1, c2])) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
    | .wrap (.str ⟨_cs⟩) _j => Nat.add m (Nat.add 2 (String.length (String.mk [c1, c2])))
    | _ => 0

-- strCtor (.wrap (.str "ab") m) "ab" ===>
--   match Value.wrap (Value.str "ab") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨cs⟩) j => Nat.add 4 m
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs string literal discriminator binds `cs := ['a', 'b']`
#testOptimize [ "UnifyPattern_30" ] (norm-result: 1)
  strCtor (.wrap (.str "ab") m) "ab" ===>
    match Value.wrap (Value.str "ab") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨_cs⟩) _j => Nat.add 4 m
    | _ => 0

/-! ### Constructor constants, opaque constants and function applications as discriminators -/

def wrapCtor (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .wrap .unit 5 => 100
  | .wrap .unit k => g x + k
  | .wrap (.nat 5) k => g x + k
  | .wrap (.nat n) k => g x + n + k
  | .wrap .none k => g x + k
  | .wrap w k => g w + k
  | _ => 0

-- wrapCtor g (.wrap .unit m) ===>
--   match Value.wrap Value.unit m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add k (g (Value.wrap Value.unit m))
--   | .wrap (.nat n) k => Nat.add k (Nat.add n (g (Value.wrap Value.unit m)))
--   | .wrap .none k => Nat.add k (g (Value.wrap Value.unit m))
--   | .wrap w k => Nat.add m (g Value.unit)
--   | _ => 0
-- NOTE: equal constructor constants (`.unit` vs `.unit`) continue the unification (`k := m`), a constructor
--       application or a distinct constructor constant vs `.unit` stops the unification (`k` is left unbound),
--       variable pattern `w` binds `w := .unit`
#testOptimize [ "UnifyPattern_31" ] (norm-result: 1)
  wrapCtor g (.wrap .unit m) ===>
    match Value.wrap Value.unit m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) k => Nat.add k (g (Value.wrap Value.unit m))
    | .wrap (.nat n) k => Nat.add k (Nat.add n (g (Value.wrap Value.unit m)))
    | .wrap .none k => Nat.add k (g (Value.wrap Value.unit m))
    | .wrap _w _k => Nat.add m (g Value.unit)
    | _ => 0

-- wrapCtor g (.wrap (.nat n) m) ===>
--   match Value.wrap (Value.nat n) m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add k (g (Value.wrap (Value.nat n) m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n_1) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add k (g (Value.wrap (Value.nat n) m))
--   | .wrap w k => Nat.add m (g (Value.nat n))
--   | _ => 0
-- NOTE: constructor constant vs constructor application discriminator stops the unification,
--       `.nat 5` binds `n := 5` which is also propagated in the discriminator occurrence `g x`
#testOptimize [ "UnifyPattern_32" ] (norm-result: 1)
  wrapCtor g (.wrap (.nat n) m) ===>
    match Value.wrap (Value.nat n) m with
    | .wrap .unit 5 => 100
    | .wrap .unit k => Nat.add k (g (Value.wrap (Value.nat n) m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat _n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none k => Nat.add k (g (Value.wrap (Value.nat n) m))
    | .wrap _w _k => Nat.add m (g (Value.nat n))
    | _ => 0

-- wrapCtor g (.wrap (f n) m) ===>
--   match Value.wrap (f n) m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g (f n))
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs non constructor application
--       discriminator bind `f n` to the pattern
#testOptimize [ "UnifyPattern_33" ] (norm-result: 1)
  wrapCtor g (.wrap (f n) m) ===>
    match Value.wrap (f n) m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g (f n))
    | _ => 0

-- wrapCtor g (.wrap v0 m) ===>
--   match Value.wrap v0 m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g v0)
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs opaque constant
--       discriminator bind `v0` to the pattern
#testOptimize [ "UnifyPattern_34" ] (norm-result: 1)
  wrapCtor g (.wrap v0 m) ===>
    match Value.wrap v0 m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g v0)
    | _ => 0

-- wrapCtor g (.wrap v m) ===>
--   match Value.wrap v m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g v)
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs free variable
--       discriminator bind `v` to the pattern
#testOptimize [ "UnifyPattern_35" ] (norm-result: 1)
  wrapCtor g (.wrap v m) ===>
    match Value.wrap v m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g v)
    | _ => 0

/-! ### Named patterns -/

def namedArg (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, p@(.nat 5) => g p + 100
  | p@(.nat k), _ => g p + k
  | p@(.pair a b), _ => g p + a + b
  | p@.unit, _ => g p
  | p@(.wrap q@(.nat k) j), _ => g p + g q + k + j
  | _, _ => 0

-- namedArg g v u ===>
--   match v, u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
-- NOTE: each named pattern alias (incl. nested ones) is bound to its pattern (without named patterns)
#testOptimize [ "UnifyPattern_36" ] (norm-result: 1)
  namedArg g v u ===>
    match v, u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.nat (m + 2)) u ===>
--   match Value.nat (Nat.add 2 m), u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_37" ] (norm-result: 1)
  namedArg g (.nat (m + 2)) u ===>
    match Value.nat (Nat.add 2 m), u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat _k), _ => Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.pair m (m + 1)) u ===>
--   match Value.pair m (Nat.add 1 m), u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add (Nat.add m (g (Value.pair m (Nat.add 1 m)))) (Nat.add 1 m)
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_38" ] (norm-result: 1)
  namedArg g (.pair m (m + 1)) u ===>
    match Value.pair m (Nat.add 1 m), u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair _a _b), _ => Nat.add (Nat.add m (g (Value.pair m (Nat.add 1 m)))) (Nat.add 1 m)
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.wrap (.nat (m + 2)) m) u ===>
--   match Value.wrap (Value.nat (Nat.add 2 m)) m, u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ =>
--       Nat.add m (Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.wrap (Value.nat (Nat.add 2 m)) m))) (Nat.add 2 m))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_39" ] (norm-result: 1)
  namedArg g (.wrap (.nat (m + 2)) m) u ===>
    match Value.wrap (Value.nat (Nat.add 2 m)) m, u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat _k) _j), _ =>
        Nat.add m (Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.wrap (Value.nat (Nat.add 2 m)) m))) (Nat.add 2 m))
    | _, _ => 0

/-! ### Polymorphic constructors (type arguments) -/

def optPoly {α : Type} (g : Option α → Nat) (x : Option α) (y : Value) : Nat :=
  match x, y with
  | some v, .nat 5 => g (some v)
  | some _, .nat k => g x + k
  | _, _ => 0

-- ∀ (α : Type) (a : α) (g : Option α → Nat), optPoly g (some a) (.nat m) = n ===>
-- ∀ (α : Type) (a : α) (g : Option α → Nat),
--   n = match some a, Value.nat m with
--       | some v, .nat 5 => g (some a)
--       | some _, .nat k => Nat.add m (g (some a))
--       | _, _ => 0
-- NOTE: the type argument `α` of `some` is the same free variable in the pattern and in the discriminator
--       (no binding), the value argument binds `v := a`
#testOptimize [ "UnifyPattern_40" ] (norm-result: 1)
  ∀ (α : Type) (a : α) (g : Option α → Nat), optPoly g (some a) (.nat m) = n ===>
  ∀ (α : Type) (a : α) (g : Option α → Nat),
    n = match some a, Value.nat m with
        | some _v, .nat 5 => g (some a)
        | some _, .nat _k => Nat.add m (g (some a))
        | _, _ => 0

def optList (x : Option (List Nat)) (z : List Nat) : Nat :=
  match x with
  | some [5] => 100
  | some (k :: ks) => k + ks.length + z.length
  | _ => 0

-- optList (some (m :: ms)) (m :: ms) ===>
--   match some (m :: ms) with
--   | some [5] => 100
--   | some (k :: ks) => Nat.add (Nat.add m (List.length ms)) (Nat.add 1 (List.length ms))
--   | _ => 0
-- NOTE: the type argument `List Nat` of `some` (an inductive type application) is skipped,
--       the nested constructor `List.cons` binds `k := m` and `ks := ms`
#testOptimize [ "UnifyPattern_41" ] (norm-result: 1)
  optList (some (m :: ms)) (m :: ms) ===>
    match some (m :: ms) with
    | some [5] => 100
    | some (_k :: _ks) => Nat.add (Nat.add m (List.length ms)) (Nat.add 1 (List.length ms))
    | _ => 0

/-! ### Opaque constant discriminator -/

def opaqueDiscr (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .nat k => g x + k
  | y => g x + g y

-- opaqueDiscr g v0 ===>
--   match v0 with
--   | .nat k => Nat.add k (g (Value.nat k))
--   | y => Nat.add (g v0) (g v0)
-- NOTE: constructor application pattern vs opaque constant discriminator binds `v0 := Value.nat k`
--       and the match alternative is optimized in a new context (the binding must not leak into
--       the following alternatives: `g v0` is left unchanged in the variable pattern alternative)
#testOptimize [ "UnifyPattern_42" ] (norm-result: 1)
  opaqueDiscr g v0 ===>
    match v0 with
    | .nat k => Nat.add k (g (Value.nat k))
    | _y => Nat.add (g v0) (g v0)

-- intArg gi (.int (Int.negSucc m)) (Int.ofNat m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat m))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 m)
--   | _ => 0
-- NOTE: `Int.negSucc m` discriminator is normalized to `Int.neg (Int.ofNat (1 + m))`: the `Int.negSucc`
--       variable patterns (normalized to `Int.neg (Int.ofNat _)`) unify through `Int.neg` and `Int.ofNat`
--       (`m := 1 + k` and `k := m`), the `Int.negSucc 2` literal pattern binds `m := 2`
#testOptimize [ "UnifyPattern_43" ] (norm-result: 1)
  intArg gi (.int (Int.negSucc m)) (Int.ofNat m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat m))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
    | .int (.negSucc _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 m)
    | _ => 0

-- intArg gi (.int (-w)) w ===>
--   match Value.int (Int.neg w) with
--   | .int 3 => Nat.add 100 (gi w)
--   | .int (.ofNat 7) => Nat.add 107 (gi w)
--   | .int (.negSucc 2) => Nat.add 300 (gi w)
--   | .int (.ofNat (k + 1)) => Nat.add k (gi w)
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi w) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg w` discriminator (`w` free variable): the `Int.negSucc` variable patterns unify through
--       `Int.neg` and bind `w := Int.ofNat (2 + k)` and `w := Int.ofNat (1 + k)`, the other patterns
--       bind the expression `Int.neg w` to the pattern (not visible in the rhs)
#testOptimize [ "UnifyPattern_44" ] (norm-result: 1)
  intArg gi (.int (-w)) w ===>
    match Value.int (Int.neg w) with
    | .int 3 => Nat.add 100 (gi w)
    | .int (.ofNat 7) => Nat.add 107 (gi w)
    | .int (.negSucc 2) => Nat.add 300 (gi w)
    | .int (.ofNat (k + 1)) => Nat.add k (gi w)
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi w) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(hi w))) (hi w) ===>
--   match Value.int (Int.neg (hi w)) with
--   | .int 3 => Nat.add 100 (gi (hi w))
--   | .int (.ofNat 7) => Nat.add 107 (gi (hi w))
--   | .int (.negSucc 2) => Nat.add 300 (gi (hi w))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (hi w))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (hi w)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg (hi w)` discriminator (non constructor application under `Int.neg`): the `Int.negSucc`
--       variable patterns unify through `Int.neg` and bind `hi w := Int.ofNat (2 + k)` and `hi w := Int.ofNat (1 + k)`
#testOptimize [ "UnifyPattern_45" ] (norm-result: 1)
  intArg gi (.int (-(hi w))) (hi w) ===>
    match Value.int (Int.neg (hi w)) with
    | .int 3 => Nat.add 100 (gi (hi w))
    | .int (.ofNat 7) => Nat.add 107 (gi (hi w))
    | .int (.negSucc 2) => Nat.add 300 (gi (hi w))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (hi w))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (hi w)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(Int.ofNat (h n)))) (Int.ofNat (h n)) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat (h n)))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat (h n)))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 3))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (h n)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat _k) => gi (Int.ofNat 0)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg (Int.ofNat (h n))` discriminator: the `Int.negSucc` patterns unify through `Int.neg` and
--       `Int.ofNat` down to the Nat argument and bind `h n := 3`, `h n := 2 + k` and `h n := 1 + k`
#testOptimize [ "UnifyPattern_46" ] (norm-result: 1)
  intArg gi (.int (-(Int.ofNat (h n)))) (Int.ofNat (h n)) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat (h n)))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat (h n)))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 3))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (h n)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat _k) => gi (Int.ofNat 0)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(Int.ofNat (m + 2)))) (Int.ofNat m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 2 m))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat m))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 1))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 m)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 (Nat.add 1 m))
--   | _ => 0
-- NOTE: `Int.neg (Int.ofNat (2 + m))` discriminator: the `Int.negSucc` patterns unify through `Int.neg` and
--       `Int.ofNat` down to the Nat offsets and bind `m := 1` (3 ≥ 2), `k := m` (2 = 2) and `k := 1 + m` (1 < 2)
#testOptimize [ "UnifyPattern_47" ] (norm-result: 1)
  intArg gi (.int (-(Int.ofNat (m + 2)))) (Int.ofNat m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 2 m))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat m))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 1))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
    | .int (.negSucc (_k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 m)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
    | .int (.negSucc _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 (Nat.add 1 m))
    | _ => 0

/-! ### Named patterns: alias re-optimized w.r.t. the unification of its pattern -/

def namedOffset (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => g y + 100
  | p@(.nat (k + 2)), _ => g p + k
  | p@(.nat k), _ => g p + k
  | _, _ => 0

-- namedOffset g (.nat (m + 5)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 5 m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 3 m)
--   | p@(.nat k), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 5 m)
--   | _, _ => 0
-- NOTE: the alias `p` is bound to its pattern `Value.nat (2 + k)` and re-optimized once replaced:
--       with `k := 3 + m`, `g p` becomes `g (Value.nat (5 + m))` (offsets are folded)
#testOptimize [ "UnifyPattern_48" ] (norm-result: 1)
  namedOffset g (.nat (m + 5)) (.nat (h n)) ===>
    match Value.nat (Nat.add 5 m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (_k + 2)), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 3 m)
    | _p@(.nat _k), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 5 m)
    | _, _ => 0

-- namedOffset g (.nat 7) (.nat (h n)) ===>
--   match Value.nat 7, Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add 5 (g (Value.nat 7))
--   | p@(.nat k), _ => Nat.add 7 (g (Value.nat 7))
--   | _, _ => 0
-- NOTE: with `k := 5`, the alias `p` (bound to `Value.nat (2 + k)`) is re-optimized to `Value.nat 7`
#testOptimize [ "UnifyPattern_49" ] (norm-result: 1)
  namedOffset g (.nat 7) (.nat (h n)) ===>
    match Value.nat 7, Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (_k + 2)), _ => Nat.add 5 (g (Value.nat 7))
    | _p@(.nat _k), _ => Nat.add 7 (g (Value.nat 7))
    | _, _ => 0

-- namedOffset g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add k (g (Value.nat (Nat.add 2 k)))
--   | p@(.nat k), _ => Nat.add (h m) (g (Value.nat (h m)))
--   | _, _ => 0
-- NOTE: offset pattern vs non constructor application discriminator binds `h m := 2 + k`, the alias `p`
--       is left bound to its pattern `Value.nat (2 + k)`; variable pattern binds `k := h m` and the alias
--       `p` is re-optimized to `Value.nat (h m)`
#testOptimize [ "UnifyPattern_50" ] (norm-result: 1)
  namedOffset g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (k + 2)), _ => Nat.add k (g (Value.nat (Nat.add 2 k)))
    | _p@(.nat _k), _ => Nat.add (h m) (g (Value.nat (h m)))
    | _, _ => 0

def varAlias (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => g y + 100
  | p@k, .wrap q _ => g p + g k + g q
  | _, _ => 0

-- varAlias g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@k, .wrap q _ => Nat.add (g q) (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.nat (Nat.add 2 m))))
--   | _, _ => 0
-- NOTE: named variable pattern `p@k`: `k` is bound to the discriminator and the alias `p` (bound to `k`)
--       is re-optimized to the discriminator as well
#testOptimize [ "UnifyPattern_51" ] (norm-result: 1)
  varAlias g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@_k, .wrap q _ => Nat.add (g q) (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.nat (Nat.add 2 m))))
    | _, _ => 0

-- varAlias g v (.nat (h n)) ===>
--   match v, Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@k, .wrap q _ => Nat.add (g q) (Nat.add (g v) (g v))
--   | _, _ => 0
-- NOTE: named variable pattern `p@k` vs free variable discriminator: `k := v` and the alias `p` is
--       re-optimized to `v`
#testOptimize [ "UnifyPattern_52" ] (norm-result: 1)
  varAlias g v (.nat (h n)) ===>
    match v, Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@_k, .wrap q _ => Nat.add (g q) (Nat.add (g v) (g v))
    | _, _ => 0

-- NOTE: `generalizing := false` so that the named pattern hypothesis `h : p = Value.nat k` is not added
--       as an extra discriminator of the inner match
def nestedAlias (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x with
  | .nat 5 => 100
  | p@(.nat k) =>
      match (generalizing := false) y, p with
      | .nat 5, _ => 50
      | _, .nat j => g p + j + k
      | _, _ => 0
  | _ => 0

-- nestedAlias g v (.nat (h n)) ===>
--   match v with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat k with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add k (Nat.add k (g (Value.nat k)))
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: `p` is replaced by its pattern `Value.nat k`
--       and the nested variable pattern then binds `j := k`
#testOptimize [ "UnifyPattern_53" ] (norm-result: 1)
  nestedAlias g v (.nat (h n)) ===>
    match v with
    | .nat 5 => 100
    | _p@(.nat k) =>
      match Value.nat (h n), Value.nat k with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add k (Nat.add k (g (Value.nat k)))
      | _, _ => 0
    | _ => 0

-- nestedAlias g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat (Nat.add 2 m) with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: with `k := 2 + m`, `p` is re-optimized to
--       `Value.nat (2 + m)` (also as discriminator) and the nested variable pattern binds `j := 2 + m`
#testOptimize [ "UnifyPattern_54" ] (norm-result: 1)
  nestedAlias g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 100
    | _p@(.nat _k) =>
      match Value.nat (h n), Value.nat (Nat.add 2 m) with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
      | _, _ => 0
    | _ => 0

-- nestedAlias g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m) with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat (h m) with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add (h m) (Nat.add (h m) (g (Value.nat (h m))))
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: with `k := h m`, `p` is re-optimized to
--       `Value.nat (h m)` (also as discriminator) and the nested variable pattern binds `j := h m`
#testOptimize [ "UnifyPattern_55" ] (norm-result: 1)
  nestedAlias g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m) with
    | .nat 5 => 100
    | _p@(.nat _k) =>
      match Value.nat (h n), Value.nat (h m) with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add (h m) (Nat.add (h m) (g (Value.nat (h m))))
      | _, _ => 0
    | _ => 0

/-! ### Named pattern hypothesis -/

variable (q : ∀ {a b : Value}, a = b → Nat)

def hypUse (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | _p@hp:(.nat k) => q hp + k
  | _ => 0

-- hypUse q v ===>
--   match v with
--   | .pair _ 3 => 100
--   | p@hp:(.nat k) => Nat.add k (q (Eq.refl (Value.nat k)))
--   | _ => 0
-- NOTE: match not reduced (free variable discriminator): the named pattern hypothesis `hp : p = Value.nat k`
--       is replaced by `Eq.refl (Value.nat k)` since the alias `p` is bound to its pattern
#testOptimize [ "UnifyPattern_56" ] (norm-result: 1)
  hypUse q v ===>
    match v with
    | .pair _ 3 => 100
    | _p@_hp:(.nat k) => Nat.add k (q (Eq.refl (Value.nat k)))
    | _ => 0

-- hypUse q (.nat (m + 2)) ===> Nat.add (Nat.add 2 m) (q (Eq.refl (Value.nat (Nat.add 2 m))))
-- NOTE: the match is reduced to the named pattern alternative (`k := 2 + m`) and, as in the definition
--       of the matcher `hypUse.match_1`, the hypothesis `hp` is instantiated with `Eq.refl`.
#testOptimize [ "UnifyPattern_57" ] (norm-result: 1)
  hypUse q (.nat (m + 2)) ===> Nat.add (Nat.add 2 m) (q (Eq.refl (Value.nat (Nat.add 2 m))))

-- NOTE: the nested match on the alias `p` implicitly uses the named pattern hypothesis
--       (added as an extra discriminator by Lean, see `nestedAlias` above)
def nestedAliasHyp (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | p@(.nat k) =>
      match p with
      | .nat j => g p + j + k
      | _ => 0
  | _ => 0

-- nestedAliasHyp g (.nat (m + 2)) ===>
--   Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
-- NOTE: the outer match is reduced to the named pattern alternative (`k := 2 + m`, `p := Value.nat (2 + m)`)
--       and the nested match is then reduced as well (`j := 2 + m`).
#testOptimize [ "UnifyPattern_58" ] (norm-result: 1)
  nestedAliasHyp g (.nat (m + 2)) ===>
    Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)

def hypTwo (q : ∀ {a b : Value}, a = b → Nat) (x y : Value) : Nat :=
  match x, y with
  | .pair _ 3, _ => 100
  | _p@hp:(.nat k), _r@hr:(.nat j) => q hp + q hr + k + j
  | _, _ => 0

-- hypTwo q (.nat (m + 2)) v ===>
--   match Value.nat (Nat.add 2 m), v with
--   | .pair _ 3, _ => 100
--   | p@hp:(.nat k), r@hr:(.nat j) =>
--       Nat.add j (Nat.add (Nat.add (q (Eq.refl (Value.nat j))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
--   | _, _ => 0
-- NOTE: match not reduced (second discriminator is a free variable): both named pattern hypotheses are
--       replaced by `Eq.refl` of their (unified) pattern, `k := 2 + m` and `v := Value.nat j`
#testOptimize [ "UnifyPattern_59" ] (norm-result: 1)
  hypTwo q (.nat (m + 2)) v ===>
    match Value.nat (Nat.add 2 m), v with
    | .pair _ 3, _ => 100
    | _p@_hp:(.nat _k), _r@_hr:(.nat j) =>
        Nat.add j (Nat.add (Nat.add (q (Eq.refl (Value.nat j))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
    | _, _ => 0

-- hypTwo q (.nat (m + 2)) (.nat (h m)) ===>
--   Nat.add (h m) (Nat.add (Nat.add (q (Eq.refl (Value.nat (h m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
-- NOTE: match reduced on two discriminators with named patterns: both hypotheses are instantiated with `Eq.refl`
#testOptimize [ "UnifyPattern_60" ] (norm-result: 1)
  hypTwo q (.nat (m + 2)) (.nat (h m)) ===>
    Nat.add (h m) (Nat.add (Nat.add (q (Eq.refl (Value.nat (h m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))

def hypMatchH (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match hx : x with
  | .pair _ 3 => 100
  | _p@hp:(.nat k) => q hp + q hx + k
  | _ => 0

-- hypMatchH q v ===>
--   match hx : v with
--   | .pair _ 3 => 100
--   | p@hp:(.nat k) => Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.nat k))))
--   | _ => 0
-- NOTE: `match hx : x with` hypothesis and named pattern hypothesis are both replaced by `Eq.refl` of the pattern.
--       The expected term is written as an explicit matcher application: the binder type of `hx` in the
--       named pattern alternative is `v = namedPattern p (Value.nat k) hp` (as elaborated by Lean in the
--       definition), which cannot be obtained with the `match` syntax.
#testOptimize [ "UnifyPattern_61" ] (norm-result: 1)
  hypMatchH q v ===>
    hypMatchH.match_1 (fun _ => Nat) v
      (fun (a : Nat) (_hx : v = Value.pair a 3) => 100)
      (fun (_p : Value) (k : Nat) (hp : _p = Value.nat k) (_hx : v = namedPattern _p (Value.nat k) hp) =>
         Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.nat k)))))
      (fun (x : Value) (_hx : v = x) => 0)

-- hypMatchH q (.nat (m + 2)) ===>
--   Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m)
-- NOTE: match reduced: `match hx : x with` hypothesis and named pattern hypothesis are both instantiated with `Eq.refl`
#testOptimize [ "UnifyPattern_62" ] (norm-result: 1)
  hypMatchH q (.nat (m + 2)) ===>
    Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m)


def hypNested (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | _p@hp:(.wrap _r@hr:(.nat k) j) => q hp + q hr + k + j
  | _ => 0

-- hypNested q v ===>
--   match v with
--   | .pair _ 3 => 100
--   | p@hp:(.wrap r@hr:(.nat k) j) =>
--       Nat.add j (Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.wrap (Value.nat k) j)))))
--   | _ => 0
-- NOTE: the hypothesis `hp : p = Value.wrap (namedPattern r (Value.nat k) hr) j` of the outer named pattern
--       must be replaced by `Eq.refl` of its pattern without named patterns.
#testOptimize [ "UnifyPattern_63" ] (norm-result: 1)
  hypNested q v ===>
    match v with
    | .pair _ 3 => 100
    | _p@_hp:(.wrap _r@_hr:(.nat k) j) =>
        Nat.add j (Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.wrap (Value.nat k) j)))))
    | _ => 0

-- hypNested q (.wrap (.nat (m + 2)) m) ===>
--   Nat.add m (Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.wrap (Value.nat (Nat.add 2 m)) m)))) (Nat.add 2 m))
-- NOTE: match reduced: the hypothesis `hp` of the outer named pattern must be instantiated with `Eq.refl`
--       of the discriminator.
#testOptimize [ "UnifyPattern_64" ] (norm-result: 1)
  hypNested q (.wrap (.nat (m + 2)) m) ===>
    Nat.add m (Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.wrap (Value.nat (Nat.add 2 m)) m)))) (Nat.add 2 m))

/-! ### Named pattern hypothesis: alias re-optimized w.r.t. the unification of its pattern -/

def hypVar (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:k, .wrap _ _ => q hp + g p + g k
  | _, _ => 0

-- hypVar q g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:k, .wrap _ _ =>
--       Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add (g (Value.nat (Nat.add 2 m))) (q (Eq.refl (Value.nat (Nat.add 2 m)))))
--   | _, _ => 0
-- NOTE: named variable pattern `p@hp:k`: `k` is bound to the discriminator, the alias `p` and the hypothesis
--       `hp` (bound to `k` and `Eq.refl k`) are re-optimized to the discriminator
#testOptimize [ "UnifyPattern_65" ] (norm-result: 1)
  hypVar q g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:_k, .wrap _ _ =>
        Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add (g (Value.nat (Nat.add 2 m))) (q (Eq.refl (Value.nat (Nat.add 2 m)))))
    | _, _ => 0

def hypOffset (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:(.nat (k + 2)), _ => q hp + g p + k
  | _p@hp:(.nat k), _ => q hp + k
  | _, _ => 0

-- hypOffset q g (.nat (m + 5)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 5 m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.nat (k + 2)), _ =>
--       Nat.add (Nat.add (g (Value.nat (Nat.add 5 m))) (q (Eq.refl (Value.nat (Nat.add 5 m))))) (Nat.add 3 m)
--   | p@hp:(.nat k), _ => Nat.add (Nat.add 5 m) (q (Eq.refl (Value.nat (Nat.add 5 m))))
--   | _, _ => 0
-- NOTE: with `k := 3 + m`, the alias `p` and the hypothesis `hp` (bound to `Value.nat (2 + k)` and
--       `Eq.refl (Value.nat (2 + k))`) are re-optimized with the offsets folded
#testOptimize [ "UnifyPattern_66" ] (norm-result: 1)
  hypOffset q g (.nat (m + 5)) (.nat (h n)) ===>
    match Value.nat (Nat.add 5 m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.nat (_k + 2)), _ =>
        Nat.add (Nat.add (g (Value.nat (Nat.add 5 m))) (q (Eq.refl (Value.nat (Nat.add 5 m))))) (Nat.add 3 m)
    | _p@_hp:(.nat _k), _ => Nat.add (Nat.add 5 m) (q (Eq.refl (Value.nat (Nat.add 5 m))))
    | _, _ => 0

-- hypOffset q g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.nat (k + 2)), _ => Nat.add k (Nat.add (g (Value.nat (Nat.add 2 k))) (q (Eq.refl (Value.nat (Nat.add 2 k)))))
--   | p@hp:(.nat k), _ => Nat.add (h m) (q (Eq.refl (Value.nat (h m))))
--   | _, _ => 0
-- NOTE: offset pattern vs non constructor application discriminator binds `h m := 2 + k`, the hypothesis `hp`
--       is `Eq.refl` of the pattern; variable pattern binds `k := h m` and `hp` is re-optimized to
--       `Eq.refl (Value.nat (h m))`
#testOptimize [ "UnifyPattern_67" ] (norm-result: 1)
  hypOffset q g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.nat (k + 2)), _ => Nat.add k (Nat.add (g (Value.nat (Nat.add 2 k))) (q (Eq.refl (Value.nat (Nat.add 2 k)))))
    | _p@_hp:(.nat _k), _ => Nat.add (h m) (q (Eq.refl (Value.nat (h m))))
    | _, _ => 0

def hypInt (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:(.int (.negSucc (k + 1))), _ => q hp + g p + k
  | _, _ => 0

-- hypInt q g (.int (-w)) (.nat (h n)) ===>
--   match Value.int (Int.neg w), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.int (.negSucc (k + 1))), _ =>
--       Nat.add k (Nat.add (g (Value.int (Int.neg (Int.ofNat (Nat.add 2 k))))) (q (Eq.refl (Value.int (Int.neg (Int.ofNat (Nat.add 2 k)))))))
--   | _, _ => 0
-- NOTE: the alias `p` and the hypothesis `hp` are bound to the normalized pattern
--       `Value.int (Int.neg (Int.ofNat (2 + k)))` (`w := Int.ofNat (2 + k)` is not visible in the rhs)
#testOptimize [ "UnifyPattern_68" ] (norm-result: 1)
  hypInt q g (.int (-w)) (.nat (h n)) ===>
    match Value.int (Int.neg w), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.int (.negSucc (k + 1))), _ =>
        Nat.add k (Nat.add (g (Value.int (Int.neg (Int.ofNat (Nat.add 2 k))))) (q (Eq.refl (Value.int (Int.neg (Int.ofNat (Nat.add 2 k)))))))
    | _, _ => 0

/-! ### Named pattern hypothesis: generalized by a nested match on the alias -/

-- NOTE: the nested match generalizes the hypothesis `h : p = Value.nat k` of the named pattern
--       (added as an extra discriminator by Lean, cf. `nestedAlias` with `generalizing := false`)
def nestedAliasGen (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x with
  | .nat 5 => 100
  | p@(.nat k) =>
      match y, p with
      | .nat 5, _ => 50
      | _, .nat j => g p + j + k
      | _, _ => 0
  | _ => 0

-- nestedAliasGen g v (.nat (h n)) ===>
--   match v with
--   | .nat 5 => 100
--   | p@h_1:(.nat k) =>
--     nestedAliasGen.match_1 k (fun (y p : Value) (h : p = Value.nat k) => Nat) (Value.nat (h n)) (Value.nat k)
--       (Eq.refl (Value.nat k))
--       (fun (x : Value) (h : x = Value.nat k) => 50)
--       (fun (x : Value) (j : Nat) (h : Value.nat j = Value.nat k) => Nat.add k (Nat.add k (g (Value.nat k))))
--       (fun (x p : Value) (h : p = Value.nat k) => 0)
--   | _ => 0
-- NOTE: the alias `p` and the hypothesis `h_1` are replaced by `Value.nat k` and `Eq.refl (Value.nat k)` as
--       discriminators of the nested match (which is not reduced), the nested variable pattern binds `j := k`.
--       The nested match is written as an explicit matcher application because of its dependent motive.
#testOptimize [ "UnifyPattern_69" ] (norm-result: 1)
  nestedAliasGen g v (.nat (h n)) ===>
    match v with
    | .nat 5 => 100
    | _p@(.nat k) =>
      nestedAliasGen.match_1 k (fun (_y _p : Value) (_h : _p = Value.nat k) => Nat) (Value.nat (h n)) (Value.nat k)
        (Eq.refl (Value.nat k))
        (fun (_x : Value) (_h : _x = Value.nat k) => 50)
        (fun (_x : Value) (_j : Nat) (_h : Value.nat _j = Value.nat k) => Nat.add k (Nat.add k (g (Value.nat k))))
        (fun (_x _p : Value) (_h : _p = Value.nat k) => 0)
    | _ => 0

/-! ### Constructors with a proof field and inductive parameters -/

variable (P : Nat → Prop) (PV : Value → Prop)
variable (qP : ∀ {x : Nat}, P x → Nat) (pn : P (h n)) (qV : ∀ {x : Value}, PV x → Nat) (pv : PV (Value.nat (h m)))

structure Tagged (R : Nat → Prop) (b : Nat) where
  val : Nat
  ok : R val

def tagged (P : Nat → Prop) (b : Nat) (q : ∀ {x : Nat}, P x → Nat) (y : Nat) (s : Tagged P (b + 0)) : Nat :=
  match y, s with
  | 5, _ => 100
  | _, ⟨x, hx⟩ => q hx + x

-- tagged P n qP m ⟨h n, pn⟩ ===>
--   tagged.match_1 P n (fun y (s : Tagged P n) => Nat) m (Tagged.mk (h n) pn)
--     (fun (x : Tagged P (n + 0)) => 100)
--     (fun x x (hx : P x) => Nat.add (h n) (qP pn))
-- NOTE: the inductive parameters of the constructor are skipped by the unification: the parameter
--       `b + 0` of the pattern (taken from the type of the matcher) differs from the normalized
--       parameter `n` of the discriminator, the value field binds `x := h n` and the proof field
--       binds `hx := pn`. The expected result is written as an explicit matcher application because
--       the motive of the optimized match mentions the normalized parameter `Tagged P n`.
#testOptimize [ "UnifyPattern_70" ] (norm-result: 1)
  tagged P n qP m ⟨h n, pn⟩ ===>
    tagged.match_1 P n (fun (_y : Nat) (_s : Tagged P n) => Nat) m (@Tagged.mk P n (h n) pn)
      (fun (_x : Tagged P (n + 0)) => 100)
      (fun (_y _x : Nat) (_hx : P _x) => Nat.add (h n) (qP pn))

structure TaggedV (R : Value → Prop) where
  val : Value
  ok : R val

def taggedNested (PV : Value → Prop) (q : ∀ {x : Value}, PV x → Nat) (y : Nat) (s : TaggedV PV) : Nat :=
  match y, s with
  | 5, _ => 100
  | _, ⟨.nat k, hx⟩ => q hx + k
  | _, _ => 0

-- taggedNested PV qV n ⟨.nat (h m), pv⟩ ===>
--   match n, TaggedV.mk (Value.nat (h m)) pv with
--   | 5, _ => 100
--   | _, ⟨.nat k, hx⟩ => Nat.add (h m) (qV pv)
--   | _, _ => 0
-- NOTE: nested constructor pattern inside a constructor with a proof field: the parameter `PV` is
--       the same in the pattern and in the discriminator, the nested pattern binds `k := h m` and
--       the proof field binds `hx := pv`
#testOptimize [ "UnifyPattern_71" ] (norm-result: 1)
  taggedNested PV qV n ⟨.nat (h m), pv⟩ ===>
    match n, (⟨.nat (h m), pv⟩ : TaggedV PV) with
    | 5, _ => 100
    | _, ⟨.nat _k, _hx⟩ => Nat.add (h m) (qV pv)
    | _, _ => 0

/-! ### Cascade of named patterns -/

variable (qn : ∀ {a b : Nat}, a = b → Nat)

def cascade (x : Nat) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@(.succ (q@(.succ (r@(.succ n))))), .wrap _ j => (p + 3) + q + r + n + j
  | _, _ => 0

-- cascade (h m) v ===>
--   match h m, v with
--   | _, .nat 5 => 100
--   | p@(.succ (q@(.succ (r@(.succ n))))), .wrap _ j =>
--       Nat.add j (Nat.add n (Nat.add (Nat.add (Nat.add 2 n) (Nat.add 6 n)) (Nat.add 1 n)))
--   | _, _ => 0
-- NOTE: cascade of named patterns vs function application discriminator: `h m := 3 + n` and the
--       aliases are bound to their (normalized) pattern, `p := 3 + n`, `q := 2 + n`, `r := 1 + n`
--       (`p + 3` is folded to `6 + n`)
#testOptimize [ "UnifyPattern_72" ] (norm-result: 1)
  cascade (h m) v ===>
    match h m, v with
    | _, .nat 5 => 100
    | _p@(.succ (_q@(.succ (_r@(.succ n))))), .wrap _ j =>
        Nat.add j (Nat.add n (Nat.add (Nat.add (Nat.add 2 n) (Nat.add 6 n)) (Nat.add 1 n)))
    | _, _ => 0

-- cascade (m + 7) v ===>
--   match Nat.add 7 m, v with
--   | _, .nat 5 => 100
--   | p@(.succ (q@(.succ (r@(.succ n))))), .wrap _ j =>
--       Nat.add j (Nat.add (Nat.add (Nat.add (Nat.add 6 m) (Nat.add 10 m)) (Nat.add 5 m)) (Nat.add 4 m))
--   | _, _ => 0
-- NOTE: cascade of named patterns vs offset discriminator: `n := 4 + m` and every alias is
--       re-optimized w.r.t. this binding, `r := 5 + m`, `q := 6 + m`, `p := 7 + m` (`p + 3 := 10 + m`)
#testOptimize [ "UnifyPattern_73" ] (norm-result: 1)
  cascade (m + 7) v ===>
    match Nat.add 7 m, v with
    | _, .nat 5 => 100
    | _p@(.succ (_q@(.succ (_r@(.succ _n))))), .wrap _ j =>
        Nat.add j (Nat.add (Nat.add (Nat.add (Nat.add 6 m) (Nat.add 10 m)) (Nat.add 5 m)) (Nat.add 4 m))
    | _, _ => 0

-- cascade 7 v ===>
--   match 7, v with
--   | _, .nat 5 => 100
--   | p@(.succ (q@(.succ (r@(.succ n))))), .wrap _ j => Nat.add 25 j
--   | _, _ => 0
-- NOTE: cascade of named patterns vs literal discriminator: `n := 4`, `r := 5`, `q := 6`, `p := 7`
#testOptimize [ "UnifyPattern_74" ] (norm-result: 1)
  cascade 7 v ===>
    match 7, v with
    | _, .nat 5 => 100
    | _p@(.succ (_q@(.succ (_r@(.succ _n))))), .wrap _ j => Nat.add 25 j
    | _, _ => 0

def cascadeHyp (q : ∀ {a b : Nat}, a = b → Nat) (x : Nat) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:(.succ (q'@hq:(.succ n))), .wrap _ j => q hp + q hq + p + q' + n + j
  | _, _ => 0

-- cascadeHyp qn (m + 7) v ===>
--   match Nat.add 7 m, v with
--   | _, .nat 5 => 100
--   | p@hp:(.succ (q'@hq:(.succ n))), .wrap _ j =>
--       Nat.add j (Nat.add (Nat.add (Nat.add (Nat.add (qn (Eq.refl (Nat.add 6 m))) (qn (Eq.refl (Nat.add 7 m))))
--                                   (Nat.add 7 m)) (Nat.add 6 m)) (Nat.add 5 m))
--   | _, _ => 0
-- NOTE: cascade of named patterns with hypotheses vs offset discriminator: the hypotheses follow
--       the re-optimization of their alias, `hp := Eq.refl (7 + m)` and `hq := Eq.refl (6 + m)`
#testOptimize [ "UnifyPattern_75" ] (norm-result: 1)
  cascadeHyp qn (m + 7) v ===>
    match Nat.add 7 m, v with
    | _, .nat 5 => 100
    | _p@_hp:(.succ (_q@_hq:(.succ _n))), .wrap _ j =>
        Nat.add j (Nat.add (Nat.add (Nat.add (Nat.add (qn (Eq.refl (Nat.add 6 m))) (qn (Eq.refl (Nat.add 7 m))))
                                    (Nat.add 7 m)) (Nat.add 6 m)) (Nat.add 5 m))
    | _, _ => 0

-- cascadeHyp qn (h m) v ===>
--   match h m, v with
--   | _, .nat 5 => 100
--   | p@hp:(.succ (q'@hq:(.succ n))), .wrap _ j =>
--       Nat.add j (Nat.add n (Nat.add (Nat.add (Nat.add (qn (Eq.refl (Nat.add 1 n))) (qn (Eq.refl (Nat.add 2 n))))
--                                     (Nat.add 2 n)) (Nat.add 1 n)))
--   | _, _ => 0
-- NOTE: cascade of named patterns with hypotheses vs function application discriminator:
--       `hp := Eq.refl (2 + n)` and `hq := Eq.refl (1 + n)`
#testOptimize [ "UnifyPattern_76" ] (norm-result: 1)
  cascadeHyp qn (h m) v ===>
    match h m, v with
    | _, .nat 5 => 100
    | _p@_hp:(.succ (_q@_hq:(.succ n))), .wrap _ j =>
        Nat.add j (Nat.add n (Nat.add (Nat.add (Nat.add (qn (Eq.refl (Nat.add 1 n))) (qn (Eq.refl (Nat.add 2 n))))
                                      (Nat.add 2 n)) (Nat.add 1 n)))
    | _, _ => 0

/-! ### Discriminators containing a `forallE` (Prop field) -/

structure Pk where
  p : Prop
  n : Nat

def propField (s : Pk) : Prop :=
  match s with
  | ⟨_, 5⟩ => True
  | ⟨p, k⟩ => p ∧ k = 2

-- propField ⟨∀ x, P x, h m⟩ ===>
--   match Pk.mk (∀ x, P x) (h m) with
--   | ⟨_, 5⟩ => True
--   | ⟨p, k⟩ => 2 = h m ∧ ∀ x, P x
-- NOTE: variable pattern vs `forallE` discriminator binds `p := ∀ x, P x`, which is propagated in
--       the rhs (`k := h m`)
#testOptimize [ "UnifyPattern_77" ] (norm-result: 1)
  propField ⟨∀ x, P x, h m⟩ ===>
    match Pk.mk (∀ x, P x) (h m) with
    | ⟨_, 5⟩ => True
    | ⟨_p, _k⟩ => 2 = h m ∧ ∀ x, P x

-- propField ⟨P m → P n, h m⟩ ===>
--   match Pk.mk (P m → P n) (h m) with
--   | ⟨_, 5⟩ => True
--   | ⟨p, k⟩ => 2 = h m ∧ (P m → P n)
-- NOTE: variable pattern vs implication (non-dependent `forallE`) discriminator binds `p := P m → P n`
#testOptimize [ "UnifyPattern_78" ] (norm-result: 1)
  propField ⟨P m → P n, h m⟩ ===>
    match Pk.mk (P m → P n) (h m) with
    | ⟨_, 5⟩ => True
    | ⟨_p, _k⟩ => 2 = h m ∧ (P m → P n)

/-! ### Lambda discriminators -/

inductive Fn where
  | mk : (Nat → Nat) → Fn
  | none : Fn

def lamField (x : Fn) (z : Nat) : Nat :=
  match x, z with
  | _, 5 => 100
  | .mk f, k => f k + f 1
  | _, _ => 0

-- lamField (.mk (fun x => x + m)) (h n) ===>
--   match Fn.mk (fun x => Nat.add m x), h n with
--   | _, 5 => 100
--   | .mk f, k => Nat.add (Nat.add m (h n)) (Nat.add 1 m)
--   | _, _ => 0
-- NOTE: variable pattern vs lambda discriminator binds `f := fun x => m + x`, the applications of
--       `f` in the rhs are beta-reduced (`f k := m + h n` with `k := h n`, `f 1 := 1 + m`)
#testOptimize [ "UnifyPattern_79" ] (norm-result: 1)
  lamField (.mk (fun x => x + m)) (h n) ===>
    match Fn.mk (fun x => Nat.add m x), h n with
    | _, 5 => 100
    | .mk _f, _k => Nat.add (Nat.add m (h n)) (Nat.add 1 m)
    | _, _ => 0

-- lamField (.mk (fun _ => 7)) (h n) ===>
--   match Fn.mk (fun x => 7), h n with
--   | _, 5 => 100
--   | .mk f, k => 14
--   | _, _ => 0
-- NOTE: constant lambda discriminator, `f k + f 1 := 7 + 7`
#testOptimize [ "UnifyPattern_80" ] (norm-result: 1)
  lamField (.mk (fun _ => 7)) (h n) ===>
    match Fn.mk (fun _ => 7), h n with
    | _, 5 => 100
    | .mk _f, _k => 14
    | _, _ => 0

-- lamField (.mk h) (h n) ===>
--   match Fn.mk h, h n with
--   | _, 5 => 100
--   | .mk f, k => Nat.add (h (h n)) (h 1)
--   | _, _ => 0
-- NOTE: variable pattern vs free function variable discriminator binds `f := h`
#testOptimize [ "UnifyPattern_81" ] (norm-result: 1)
  lamField (.mk h) (h n) ===>
    match Fn.mk h, h n with
    | _, 5 => 100
    | .mk _f, _k => Nat.add (h (h n)) (h 1)
    | _, _ => 0

def lamNamed (x : Fn) (z : Nat) : Nat :=
  match x, z with
  | _, 5 => 100
  | p@(.mk f), k => f k + (match p with | .mk g => g 2 | _ => 0)
  | _, _ => 0

-- lamNamed (.mk (fun x => x + m)) (h n) ===>
--   match Fn.mk (fun x => Nat.add m x), h n with
--   | _, 5 => 100
--   | p@(.mk f), k => Nat.add (Nat.add m (h n)) (Nat.add 2 m)
--   | _, _ => 0
-- NOTE: named pattern on a constructor with a lambda argument: the alias `p := Fn.mk (fun x => m + x)`
--       reduces the nested match on `p` (`g 2 := 2 + m`)
#testOptimize [ "UnifyPattern_82" ] (norm-result: 1)
  lamNamed (.mk (fun x => x + m)) (h n) ===>
    match Fn.mk (fun x => Nat.add m x), h n with
    | _, 5 => 100
    | _p@(.mk _f), _k => Nat.add (Nat.add m (h n)) (Nat.add 2 m)
    | _, _ => 0

/-! ### String patterns: list of characters vs string literal and `String.mk` discriminators -/

variable (gc : Char → Nat) (gl : List Char → Nat)

def strCons (gc : Char → Nat) (gl : List Char → Nat) (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str ⟨c :: xs⟩) j => gc c + gl xs + z.length + j
  | _ => 0

-- strCons gc gl (.wrap (.str "ab") m) "ab" ===>
--   match Value.wrap (Value.str "ab") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨c :: xs⟩) j => Nat.add m (Nat.add 2 (Nat.add (gc 'a') (gl ['b'])))
--   | _ => 0
-- NOTE: `String.mk` pattern with a `List.cons` argument vs string literal discriminator: the literal
--       is converted to a list of characters and unified with the pattern (`c := 'a'`, `xs := ['b']`)
#testOptimize [ "UnifyPattern_83" ] (norm-result: 1)
  strCons gc gl (.wrap (.str "ab") m) "ab" ===>
    match Value.wrap (Value.str "ab") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨_c :: _xs⟩) _j => Nat.add m (Nat.add 2 (Nat.add (gc 'a') (gl ['b'])))
    | _ => 0

-- strCons gc gl (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
--   match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
--   | .wrap (.str ⟨c :: xs⟩) j =>
--       Nat.add m (Nat.add (String.length (String.mk (c1 :: cs))) (Nat.add (gc c1) (gl cs)))
--   | _ => 0
-- NOTE: `String.mk` pattern vs `String.mk` discriminator with a `List.cons` argument (`c := c1`, `xs := cs`)
#testOptimize [ "UnifyPattern_84" ] (norm-result: 1)
  strCons gc gl (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
    match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
    | .wrap (.str ⟨_c :: _xs⟩) _j =>
        Nat.add m (Nat.add (String.length (String.mk (c1 :: cs))) (Nat.add (gc c1) (gl cs)))
    | _ => 0

-- strCons gc gl (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
--   match Value.wrap (Value.str (String.mk [c1, c2])) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
--   | .wrap (.str ⟨c :: xs⟩) j =>
--       Nat.add m (Nat.add (String.length (String.mk [c1, c2])) (Nat.add (gc c1) (gl [c2])))
--   | _ => 0
-- NOTE: `String.mk` pattern vs `String.mk` discriminator with an explicit list (`c := c1`, `xs := [c2]`)
#testOptimize [ "UnifyPattern_85" ] (norm-result: 1)
  strCons gc gl (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
    match Value.wrap (Value.str (String.mk [c1, c2])) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
    | .wrap (.str ⟨_c :: _xs⟩) _j =>
        Nat.add m (Nat.add (String.length (String.mk [c1, c2])) (Nat.add (gc c1) (gl [c2])))
    | _ => 0

-- strCons gc gl (.wrap (.str s) m) s ===>
--   match Value.wrap (Value.str s) m with
--   | .wrap _ 5 => Nat.add 100 (String.length s)
--   | .wrap (.str ⟨c :: xs⟩) j =>
--       Nat.add m (Nat.add (String.length (String.mk (c :: xs))) (Nat.add (gc c) (gl xs)))
--   | _ => 0
-- NOTE: `String.mk` pattern vs free variable discriminator binds `s := String.mk (c :: xs)`
#testOptimize [ "UnifyPattern_86" ] (norm-result: 1)
  strCons gc gl (.wrap (.str s) m) s ===>
    match Value.wrap (Value.str s) m with
    | .wrap _ 5 => Nat.add 100 (String.length s)
    | .wrap (.str ⟨c :: xs⟩) _j =>
        Nat.add m (Nat.add (String.length (String.mk (c :: xs))) (Nat.add (gc c) (gl xs)))
    | _ => 0

def strCharCons (gl : List Char → Nat) (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str ⟨'a' :: xs⟩) j => gl xs + z.length + j
  | _ => 0

-- strCharCons gl (.wrap (.str "ab") m) "ab" ===>
--   match Value.wrap (Value.str "ab") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨'a' :: xs⟩) j => Nat.add m (Nat.add 2 (gl ['b']))
--   | _ => 0
-- NOTE: `String.mk` pattern with a character literal vs string literal discriminator (`xs := ['b']`)
#testOptimize [ "UnifyPattern_87" ] (norm-result: 1)
  strCharCons gl (.wrap (.str "ab") m) "ab" ===>
    match Value.wrap (Value.str "ab") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨'a' :: _xs⟩) _j => Nat.add m (Nat.add 2 (gl ['b']))
    | _ => 0

def strTwo (gc : Char → Nat) (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str ⟨[c, d]⟩) j => gc c + gc d + z.length + j
  | _ => 0

-- strTwo gc (.wrap (.str "ab") m) "ab" ===>
--   match Value.wrap (Value.str "ab") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨[c, d]⟩) j => Nat.add m (Nat.add 2 (Nat.add (gc 'a') (gc 'b')))
--   | _ => 0
-- NOTE: `String.mk` pattern with an explicit list vs string literal discriminator (`c := 'a'`, `d := 'b'`)
#testOptimize [ "UnifyPattern_88" ] (norm-result: 1)
  strTwo gc (.wrap (.str "ab") m) "ab" ===>
    match Value.wrap (Value.str "ab") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨[_c, _d]⟩) _j => Nat.add m (Nat.add 2 (Nat.add (gc 'a') (gc 'b')))
    | _ => 0

-- strTwo gc (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
--   match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
--   | .wrap (.str ⟨[c, d]⟩) j =>
--       Nat.add m (Nat.add (String.length (String.mk [c1, d])) (Nat.add (gc c1) (gc d)))
--   | _ => 0
-- NOTE: explicit list pattern vs `List.cons` discriminator: `c := c1` and the tail binds the other way,
--       `cs := [d]`
#testOptimize [ "UnifyPattern_89" ] (norm-result: 1)
  strTwo gc (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
    match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
    | .wrap (.str ⟨[_c, d]⟩) _j =>
        Nat.add m (Nat.add (String.length (String.mk [c1, d])) (Nat.add (gc c1) (gc d)))
    | _ => 0

def strLitP (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str "ab") j => z.length + j
  | _ => 0

-- strLitP (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
--   match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
--   | .wrap (.str "ab") j => Nat.add m (String.length (String.mk ['a', 'b']))
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk` discriminator with a `List.cons` argument
--       (`c1 := 'a'`, `cs := ['b']`)
#testOptimize [ "UnifyPattern_90" ] (norm-result: 1)
  strLitP (.wrap (.str (String.mk (c1 :: cs))) m) (String.mk (c1 :: cs)) ===>
    match Value.wrap (Value.str (String.mk (c1 :: cs))) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk (c1 :: cs)))
    | .wrap (.str "ab") _j => Nat.add m (String.length (String.mk ['a', 'b']))
    | _ => 0

-- strLitP (.wrap (.str (String.mk [c1, c2, c1])) m) (String.mk [c1, c2, c1]) ===>
--   match Value.wrap (Value.str (String.mk [c1, c2, c1])) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2, c1]))
--   | .wrap (.str "ab") j => Nat.add j (String.length (String.mk ['a', 'b', 'a']))
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk` discriminator with a longer list: the characters are
--       unified up to the end of the literal (`c1 := 'a'`, `c2 := 'b'`), then `List.nil` vs `List.cons`
--       stops the unification (`j` is left unbound)
#testOptimize [ "UnifyPattern_91" ] (norm-result: 1)
  strLitP (.wrap (.str (String.mk [c1, c2, c1])) m) (String.mk [c1, c2, c1]) ===>
    match Value.wrap (Value.str (String.mk [c1, c2, c1])) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2, c1]))
    | .wrap (.str "ab") j => Nat.add j (String.length (String.mk ['a', 'b', 'a']))
    | _ => 0

-- strCons gc gl (.wrap (.str "") m) "" ===>
--   match Value.wrap (Value.str "") m with
--   | .wrap _ 5 => 100
--   | .wrap (.str ⟨c :: xs⟩) j => Nat.add j (Nat.add (gc c) (gl xs))
--   | _ => 0
-- NOTE: `List.cons` pattern vs empty string literal (`List.nil`): the alternative cannot match and no
--       unification is performed (`j` is left unbound)
#testOptimize [ "UnifyPattern_92" ] (norm-result: 1)
  strCons gc gl (.wrap (.str "") m) "" ===>
    match Value.wrap (Value.str "") m with
    | .wrap _ 5 => 100
    | .wrap (.str ⟨c :: xs⟩) j => Nat.add j (Nat.add (gc c) (gl xs))
    | _ => 0

/-! ### Nat offset patterns vs non-literal sums -/

-- natOffset (.nat (h n + m)) m ===>
--   match Value.nat (Nat.add m (h n)) with
--   | .nat 5 => Nat.add 100 m
--   | .nat (k + 2) => Nat.add m k
--   | .nat k => Nat.mul m (Nat.add m (h n))
--   | _ => 0
-- NOTE: offset pattern vs a sum whose first argument is not a literal: the discriminator is an
--       expression, the whole sum is bound to the pattern (`h n + m := 2 + k`) and `k` is left unbound
--       (the sum must not be decomposed argument-wise, `m := 2` and `k := h n` would be wrong, e.g.,
--       `h n = 0` and `m = 5` match with `k = 3`)
#testOptimize [ "UnifyPattern_93" ] (norm-result: 1)
  natOffset (.nat (h n + m)) m ===>
    match Value.nat (Nat.add m (h n)) with
    | .nat 5 => Nat.add 100 m
    | .nat (k + 2) => Nat.add m k
    | .nat _k => Nat.mul m (Nat.add m (h n))
    | _ => 0

-- natOffset (.nat (h n + (m + 3))) m ===>
--   match Value.nat (Nat.add (h n) (Nat.add 3 m)) with
--   | .nat 5 => Nat.add 100 m
--   | .nat (k + 2) => Nat.add m k
--   | .nat k => Nat.mul m (Nat.add (h n) (Nat.add 3 m))
--   | _ => 0
-- NOTE: same as above with a nested offset in the sum: the whole sum is bound to the pattern and `k`
--       is left unbound (`h n := 2` and `k := 3 + m` would be wrong)
#testOptimize [ "UnifyPattern_94" ] (norm-result: 1)
  natOffset (.nat (h n + (m + 3))) m ===>
    match Value.nat (Nat.add (h n) (Nat.add 3 m)) with
    | .nat 5 => Nat.add 100 m
    | .nat (k + 2) => Nat.add m k
    | .nat _k => Nat.mul m (Nat.add (h n) (Nat.add 3 m))
    | _ => 0

/-! ### Character literal patterns vs string literal discriminators

     The characters of a string literal discriminator are built by `stringToCtor` as `Char.ofNat n`,
     whereas a character literal in a pattern is elaborated in constructor form (`Char.mk ..`).
     When the discriminator is not a `Char.mk` application, `isPatternMatch` and `unifyAndUpdateEqMap`
     convert the pattern to `Char.ofNat n` (through `isUInt32Value?`) so that both representations
     unify: a mismatch is decided and a match is reduced. -/

def strCharRed (x : Value) (z : String) : Nat :=
  match x with
  | .nat 5 => z.length + 100
  | .wrap (.str ⟨'a' :: xs⟩) j => xs.length + z.length + j
  | _ => 0

-- strCharRed (.wrap (.str "bc") m) "bc" ===> 0
-- NOTE: `'a'` vs `'b'` cannot match, the match is reduced to the last alternative
#testOptimize [ "UnifyPattern_95" ] (norm-result: 1)
  strCharRed (.wrap (.str "bc") m) "bc" ===> 0

-- strCharRed (.wrap (.str "ab") m) "ab" ===> Nat.add 3 m
-- NOTE: `'a'` vs `'a'` matches, the match is reduced to the second alternative with `xs := ['b']`
--       and `j := m`
#testOptimize [ "UnifyPattern_96" ] (norm-result: 1)
  strCharRed (.wrap (.str "ab") m) "ab" ===> Nat.add 3 m

-- strCharCons gl (.wrap (.str "bc") m) "bc" ===>
--   match Value.wrap (Value.str "bc") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨'a' :: xs⟩) j => Nat.add j (Nat.add 2 (gl xs))
--   | _ => 0
-- NOTE: non reduced match (`.wrap _ 5` vs `m`): `'a'` vs `'b'` cannot match, so no unification is
--       performed on the second alternative (`xs` and `j` left unbound, as in `UnifyPattern_92`)
#testOptimize [ "UnifyPattern_97" ] (norm-result: 1)
  strCharCons gl (.wrap (.str "bc") m) "bc" ===>
    match Value.wrap (Value.str "bc") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨'a' :: xs⟩) j => Nat.add j (Nat.add 2 (gl xs))
    | _ => 0

/-! ### Proof field of a `Subtype` constructor

     For `{x : Nat // P x}` the type expected for the proof argument of `Subtype.mk` is the beta-redex
     `(fun x => P x) (h m)`, which is not structurally equal to the type `P (h m)` of the proof `pm`:
     `backwardProof` beta-reduces the expected type before comparing it with the type of the proof,
     so the proof is preserved (compare with `UnifyPattern_70` where the proof field of a structure
     with a non-lambda predicate is preserved by structural equality). -/

variable (pm : P (h m))

def subProof (P : Nat → Prop) (q : ∀ {x : Nat}, P x → Nat) (y : Nat) (s : {x : Nat // P x}) : Nat :=
  match y, s with
  | 5, _ => 100
  | _, ⟨x, hx⟩ => q hx + x

-- subProof P qP n ⟨h m, pm⟩ ===>
--   match n, Subtype.mk (h m) pm with
--   | 5, _ => 100
--   | _, ⟨x, hx⟩ => Nat.add (h m) (qP pm)
-- NOTE: the value field binds `x := h m` and the proof field binds `hx := pm`, the proof is
--       preserved in the discriminator and in the rhs
#testOptimize [ "UnifyPattern_98" ] (norm-result: 1)
  subProof P qP n ⟨h m, pm⟩ ===>
    match n, (⟨h m, pm⟩ : {x : Nat // P x}) with
    | 5, _ => 100
    | _, ⟨_x, _hx⟩ => Nat.add (h m) (qP pm)

-- subProof P qP 7 ⟨h m, pm⟩ ===> Nat.add (h m) (qP pm)
-- NOTE: reduced match, the proof `pm` is preserved in the rhs
#testOptimize [ "UnifyPattern_118" ] (norm-result: 1)
  subProof P qP 7 ⟨h m, pm⟩ ===> Nat.add (h m) (qP pm)

def subNested (PV : Value → Prop) (q : ∀ {x : Value}, PV x → Nat) (y : Nat) (s : {x : Value // PV x}) : Nat :=
  match y, s with
  | 5, _ => 100
  | _, ⟨.nat k, hx⟩ => q hx + k
  | _, _ => 0

-- subNested PV qV n ⟨.nat (h m), pv⟩ ===>
--   match n, Subtype.mk (Value.nat (h m)) pv with
--   | 5, _ => 100
--   | _, ⟨.nat k, hx⟩ => Nat.add (h m) (qV pv)
--   | _, _ => 0
-- NOTE: nested constructor pattern in the value field of a `Subtype`: `k := h m` and `hx := pv`,
--       the proof is preserved (compare with `UnifyPattern_71`)
#testOptimize [ "UnifyPattern_119" ] (norm-result: 1)
  subNested PV qV n ⟨.nat (h m), pv⟩ ===>
    match n, (⟨.nat (h m), pv⟩ : {x : Value // PV x}) with
    | 5, _ => 100
    | _, ⟨.nat _k, _hx⟩ => Nat.add (h m) (qV pv)
    | _, _ => 0

/-! ### `Int.ofNat` patterns vs negated `Int.ofNat` discriminators

     An `Int.ofNat` pattern vs an `Int.neg (Int.ofNat e)` discriminator is a mismatch only when the
     pattern is a positive literal or an offset `k + c` (`c ≥ 1`), or when `e` is an offset `c + x`
     (`c ≥ 1`): for the literal `0` and for a variable `k`, `-(Int.ofNat e) = Int.ofNat 0` when
     `e = 0`, so the alternative is a potential match and the unification records `e := 0` (and
     `k := 0`). `UnifyPattern_102` and `UnifyPattern_103` cover the offset boundary where the
     mismatch is decided. -/

def intZeroRed (x : Value) : Nat :=
  match x with
  | .int 0 => 1
  | .wrap _ j => j
  | _ => 0

-- intZeroRed (.int (-(Int.ofNat (h n)))) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int 0 => 1
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: literal `0` vs `-(Int.ofNat (h n))` is a potential match (`h n = 0`), the match is kept
#testOptimize [ "UnifyPattern_99" ] (norm-result: 1)
  intZeroRed (.int (-(Int.ofNat (h n)))) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int 0 => 1
    | .wrap _ j => j
    | _ => 0

def intOfNatRed (x : Value) : Nat :=
  match x with
  | .int (.ofNat k) => k + 1
  | .wrap _ j => j
  | _ => 0

-- intOfNatRed (.int (-(Int.ofNat (h n)))) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int (.ofNat k) => 1
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: `Int.ofNat k` vs `-(Int.ofNat (h n))` is a potential match with `k := 0` (and `h n := 0`),
--       the match is kept and the rhs optimized to `1`
#testOptimize [ "UnifyPattern_100" ] (norm-result: 1)
  intOfNatRed (.int (-(Int.ofNat (h n)))) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int (.ofNat _k) => 1
    | .wrap _ j => j
    | _ => 0

def intNegZero (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .wrap (.int 0) j => gi z + j + 100
  | .wrap (.int (.ofNat k)) j => gi z + 3 * k + j
  | .wrap (.int (.negSucc k)) j => gi z + 4 * k + j
  | _ => 0

-- intNegZero gi (.wrap (.int (-(Int.ofNat (h n)))) m) (Int.ofNat (h n)) ===>
--   match Value.wrap (Value.int (Int.neg (Int.ofNat (h n)))) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 0) j => Nat.add 100 (Nat.add m (gi (Int.ofNat 0)))
--   | .wrap (.int (.ofNat k)) j => Nat.add m (gi (Int.ofNat 0))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k))
--   | _ => 0
-- NOTE: non reduced match: the `0` and `Int.ofNat k` alternatives bind `h n := 0` (and `k := 0`)
--       so that `gi z` becomes `gi (Int.ofNat 0)`, and `j := m`. The `Int.negSucc k` alternative
--       binds `h n := 1 + k` as before.
#testOptimize [ "UnifyPattern_101" ] (norm-result: 1)
  intNegZero gi (.wrap (.int (-(Int.ofNat (h n)))) m) (Int.ofNat (h n)) ===>
    match Value.wrap (Value.int (Int.neg (Int.ofNat (h n)))) m with
    | .wrap _ 5 => 100
    | .wrap (.int 0) _j => Nat.add 100 (Nat.add m (gi (Int.ofNat 0)))
    | .wrap (.int (.ofNat _k)) _j => Nat.add m (gi (Int.ofNat 0))
    | .wrap (.int (.negSucc k)) _j => Nat.add m (Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k))
    | _ => 0

-- intOfNatRed (.int (-(Int.ofNat (h n + 1)))) ===> 0
-- NOTE: `Int.ofNat k` vs `-(Int.ofNat (1 + h n))` cannot match (the discriminator is strictly negative),
--       the match is reduced to the last alternative
#testOptimize [ "UnifyPattern_102" ] (norm-result: 1)
  intOfNatRed (.int (-(Int.ofNat (h n + 1)))) ===> 0

-- intNegZero gi (.wrap (.int (-(Int.ofNat (h n + 1)))) m) (Int.ofNat (h n + 1)) ===>
--   match Value.wrap (Value.int (Int.neg (Int.ofNat (Nat.add 1 (h n))))) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 0) j => Nat.add 100 (Nat.add j (gi (Int.ofNat (Nat.add 1 (h n)))))
--   | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.ofNat (Nat.add 1 (h n)))) (Nat.mul 3 k))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (Nat.add (gi (Int.ofNat (Nat.add 1 (h n)))) (Nat.mul 4 (h n)))
--   | _ => 0
-- NOTE: with a strictly negative discriminator the `0` and `Int.ofNat k` alternatives cannot match
--       (no unification, `j` and `k` left unbound), the `Int.negSucc k` alternative binds `k := h n`
#testOptimize [ "UnifyPattern_103" ] (norm-result: 1)
  intNegZero gi (.wrap (.int (-(Int.ofNat (h n + 1)))) m) (Int.ofNat (h n + 1)) ===>
    match Value.wrap (Value.int (Int.neg (Int.ofNat (Nat.add 1 (h n))))) m with
    | .wrap _ 5 => 100
    | .wrap (.int 0) j => Nat.add 100 (Nat.add j (gi (Int.ofNat (Nat.add 1 (h n)))))
    | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.ofNat (Nat.add 1 (h n)))) (Nat.mul 3 k))
    | .wrap (.int (.negSucc _k)) _j => Nat.add m (Nat.add (gi (Int.ofNat (Nat.add 1 (h n)))) (Nat.mul 4 (h n)))
    | _ => 0

/-! ### Named patterns, variables and sums under a negated `Int.ofNat` discriminator

     For an `Int.ofNat` pattern vs an `Int.neg (Int.ofNat e)` discriminator, `e := 0` is recorded and
     the Nat argument of the pattern is then unified with `0`, so a named pattern under (or around)
     the `Int.ofNat` pattern is bound as well. `e` may be a variable or a sum whose first argument is
     not a literal, in which case the whole sum is bound to `0`. -/

def intNamedIn (x : Value) (z : Nat) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .int (.ofNat (p@k)) => p + k + z + 1
  | .wrap _ j => j
  | _ => 0

-- intNamedIn (.int (-(Int.ofNat (h n)))) (h n) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .wrap _ 5 => 100
--   | .int (.ofNat (p@k)) => 1
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: non reduced match: the named pattern under `Int.ofNat` binds `p := 0` and `k := 0`, and
--       `h n := 0` is recorded, so `p + k + z + 1` becomes `1`
#testOptimize [ "UnifyPattern_104" ] (norm-result: 1)
  intNamedIn (.int (-(Int.ofNat (h n)))) (h n) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .wrap _ 5 => 100
    | .int (.ofNat (_p@_k)) => 1
    | .wrap _ j => j
    | _ => 0

def intNamedOut (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .int (p@(.ofNat k)) => gi p + gi z + k + 1
  | .wrap _ j => j
  | _ => 0

-- intNamedOut gi (.int (-(Int.ofNat (h n)))) (-(Int.ofNat (h n))) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .wrap _ 5 => 100
--   | .int (p@(.ofNat k)) => Nat.add 1 (Nat.add (gi (Int.ofNat 0)) (gi (Int.ofNat 0)))
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: non reduced match: the named pattern around `Int.ofNat` binds `p := -(Int.ofNat (h n))`,
--       `k := 0` and `h n := 0`, so both `gi p` and `gi z` become `gi (Int.ofNat 0)`
#testOptimize [ "UnifyPattern_105" ] (norm-result: 1)
  intNamedOut gi (.int (-(Int.ofNat (h n)))) (-(Int.ofNat (h n))) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .wrap _ 5 => 100
    | .int (_p@(.ofNat _k)) => Nat.add 1 (Nat.add (gi (Int.ofNat 0)) (gi (Int.ofNat 0)))
    | .wrap _ j => j
    | _ => 0

-- intNamedOut gi (.int (-(Int.ofNat (h n + 1)))) (-(Int.ofNat (h n + 1))) ===> 0
-- NOTE: `-(Int.ofNat (1 + h n))` is never `Int.ofNat k`, the named alternative is discarded
#testOptimize [ "UnifyPattern_106" ] (norm-result: 1)
  intNamedOut gi (.int (-(Int.ofNat (h n + 1)))) (-(Int.ofNat (h n + 1))) ===> 0

def intZeroZ (x : Value) (z : Nat) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .int 0 => z + 1
  | .wrap _ j => j
  | _ => 0

-- intZeroZ (.int (-(Int.ofNat m))) m ===>
--   match Value.int (Int.neg (Int.ofNat m)) with
--   | .wrap _ 5 => 100
--   | .int 0 => 1
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: non reduced match: `0` vs `-(Int.ofNat m)` with a variable `m` records `m := 0`
#testOptimize [ "UnifyPattern_107" ] (norm-result: 1)
  intZeroZ (.int (-(Int.ofNat m))) m ===>
    match Value.int (Int.neg (Int.ofNat m)) with
    | .wrap _ 5 => 100
    | .int 0 => 1
    | .wrap _ j => j
    | _ => 0

-- intZeroZ (.int (-(Int.ofNat (h n + m)))) (h n + m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add m (h n)))) with
--   | .wrap _ 5 => 100
--   | .int 0 => 1
--   | .wrap _ j => j
--   | _ => 0
-- NOTE: non reduced match: `0` vs `-(Int.ofNat (h n + m))` where the sum is not an offset records
--       `h n + m := 0` (the sum is not decomposed argument-wise)
#testOptimize [ "UnifyPattern_108" ] (norm-result: 1)
  intZeroZ (.int (-(Int.ofNat (h n + m)))) (h n + m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add m (h n)))) with
    | .wrap _ 5 => 100
    | .int 0 => 1
    | .wrap _ j => j
    | _ => 0

/-! ### Literal `0` pattern as first alternative vs a negated `Int.ofNat` discriminator

     For the literal pattern `0` vs `Int.neg (Int.ofNat e)`, `unifyAndUpdateEqMap` records `e := 0`
     and must report that the context was updated even though the recursive unification of `0`
     with `0` binds nothing: when no previous alternative has added a disequality (first
     alternative), the new context is only created from this flag. Otherwise the binding is not
     applied to the rhs of the alternative and the entry recorded under the pending context
     identifier leaks into the context created for the next alternative. -/

def intZeroFirst (x : Value) (z : Nat) : Nat :=
  match x with
  | .int 0 => z + 1
  | .int _ => z + 7
  | _ => 0

-- intZeroFirst (.int (-(Int.ofNat (h n)))) (h n) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int 0 => 1
--   | .int _ => Nat.add 7 (h n)
--   | _ => 0
-- NOTE: the first alternative records `h n := 0`, so its rhs becomes `1`; the second alternative
--       must not use this binding (`Nat.add 7 (h n)`, e.g., for `h n = 3` it yields `10`)
#testOptimize [ "UnifyPattern_109" ] (norm-result: 1)
  intZeroFirst (.int (-(Int.ofNat (h n)))) (h n) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int 0 => 1
    | .int _ => Nat.add 7 (h n)
    | _ => 0

def intZeroFirstWrap (x : Value) (z : Nat) : Nat :=
  match x with
  | .int 0 => z + 1
  | .wrap _ j => z + j
  | _ => 0

-- intZeroFirstWrap (.int (-(Int.ofNat (h n)))) (h n) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int 0 => 1
--   | .wrap _ j => Nat.add j (h n)
--   | _ => 0
-- NOTE: same as above with a `.wrap` second alternative (`j` is bound, `h n` is not)
#testOptimize [ "UnifyPattern_110" ] (norm-result: 1)
  intZeroFirstWrap (.int (-(Int.ofNat (h n)))) (h n) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int 0 => 1
    | .wrap _ j => Nat.add j (h n)
    | _ => 0

/-! ### Character literal patterns vs character discriminators

     A character literal pattern (`Char.mk ..`) is unified value-wise with a `Char.mk` discriminator
     (the validity proof is skipped), so a mismatch is decided and a match is reduced. A character
     variable discriminator is bound to the pattern in constructor form. -/

variable (c : Char)

def charRed (x : Value) (c : Char) : Nat :=
  match x, c with
  | .nat 5, _ => 100
  | .wrap _ j, 'a' => j + 1
  | _, _ => 0

-- charRed (.wrap v m) 'a' ===> Nat.add 1 m
-- NOTE: `'a'` vs `'a'` matches, the match is reduced to the second alternative with `j := m`
#testOptimize [ "UnifyPattern_111" ] (norm-result: 1)
  charRed (.wrap v m) 'a' ===> Nat.add 1 m

-- charRed (.wrap v m) 'b' ===> 0
-- NOTE: `'a'` vs `'b'` cannot match, the match is reduced to the last alternative
#testOptimize [ "UnifyPattern_112" ] (norm-result: 1)
  charRed (.wrap v m) 'b' ===> 0

-- charRed (.wrap v m) c ===>
--   match Value.wrap v m, c with
--   | .nat 5, _ => 100
--   | .wrap _ j, 'a' => Nat.add 1 m
--   | _, _ => 0
-- NOTE: non reduced match (`'a'` vs the variable `c`): `j := m` and `c := 'a'` (in constructor form,
--       which cannot be written in an expected term, so the rhs does not use `c`)
#testOptimize [ "UnifyPattern_113" ] (norm-result: 1)
  charRed (.wrap v m) c ===>
    match Value.wrap v m, c with
    | .nat 5, _ => 100
    | .wrap _ _j, 'a' => Nat.add 1 m
    | _, _ => 0

def charCons (gl : List Char → Nat) (x : Value) (z : List Char) : Nat :=
  match x, z with
  | .wrap _ 5, _ => 100
  | .wrap _ j, 'a' :: xs => gl xs + j
  | _, _ => 0

-- charCons gl (.wrap v m) (c1 :: cs) ===>
--   match Value.wrap v m, c1 :: cs with
--   | .wrap _ 5, _ => 100
--   | .wrap _ j, 'a' :: xs => Nat.add m (gl cs)
--   | _, _ => 0
-- NOTE: non reduced match (`.wrap _ 5` vs `m`): `c1 := 'a'` (in constructor form), `xs := cs` and
--       `j := m`. A character literal discriminator (e.g., `['a', c1]`) is normalized to the same
--       constructor form as the pattern, which cannot be written in an expected term.
#testOptimize [ "UnifyPattern_114" ] (norm-result: 1)
  charCons gl (.wrap v m) (c1 :: cs) ===>
    match Value.wrap v m, c1 :: cs with
    | .wrap _ 5, _ => 100
    | .wrap _ _j, 'a' :: _xs => Nat.add m (gl cs)
    | _, _ => 0

/-! ### `Char.mk` pattern with a variable value

     A `Char.mk v _` pattern whose value is not a literal (`isUInt32Value?` answers `none`) is
     converted to `Char.ofNat (UInt32.toNat v)` when the discriminator is not a `Char.mk`
     application: for the `Char.ofNat n` built by `stringToCtor`, `UInt32.toNat v` is unified with
     the literal `n` and `v.toNat := n` is recorded (in projection form). Against a `Char.mk`
     discriminator (character literal), the values are unified directly. -/

def charMkVar (x : Value) (z : String) : Nat :=
  match x, z with
  | .wrap _ 5, _ => 100
  | .wrap _ j, ⟨[⟨vv, _⟩]⟩ => vv.toNat + j
  | _, _ => 0

-- charMkVar (.wrap v m) "a" ===>
--   match Value.wrap v m, "a" with
--   | .wrap _ 5, _ => 100
--   | .wrap _ j, ⟨[⟨vv, _⟩]⟩ => Nat.add 97 m
--   | _, _ => 0
-- NOTE: non reduced match (`.wrap _ 5` vs `m`): `vv.toNat := 97` and `j := m`, so `vv.toNat + j`
--       becomes `97 + m`
#testOptimize [ "UnifyPattern_115" ] (norm-result: 1)
  charMkVar (.wrap v m) "a" ===>
    match Value.wrap v m, "a" with
    | .wrap _ 5, _ => 100
    | .wrap _ _j, ⟨[⟨_vv, _⟩]⟩ => Nat.add 97 m
    | _, _ => 0

-- charMkVar (.wrap v m) "ab" ===>
--   match Value.wrap v m, "ab" with
--   | .wrap _ 5, _ => 100
--   | .wrap _ j, ⟨[⟨vv, _⟩]⟩ => Nat.add 97 m
--   | _, _ => 0
-- NOTE: non reduced match: `vv.toNat := 97` and `j := m` are recorded before the unification stops
--       at `[]` vs `['b']` (as in `UnifyPattern_91`, the alternative is unreachable)
#testOptimize [ "UnifyPattern_116" ] (norm-result: 1)
  charMkVar (.wrap v m) "ab" ===>
    match Value.wrap v m, "ab" with
    | .wrap _ 5, _ => 100
    | .wrap _ _j, ⟨[⟨_vv, _⟩]⟩ => Nat.add 97 m
    | _, _ => 0

def charMkRed (x : Value) (c : Char) : Nat :=
  match x, c with
  | .nat 5, _ => 100
  | .wrap _ j, ⟨vv, _⟩ => vv.toNat + j
  | _, _ => 0

-- charMkRed (.wrap v m) 'a' ===> Nat.add 97 m
-- NOTE: `Char.mk vv _` vs the character literal `'a'` (in constructor form) unifies value-wise with
--       `vv := 97`, the match is reduced to the second alternative and `vv.toNat` folds to `97`
#testOptimize [ "UnifyPattern_117" ] (norm-result: 1)
  charMkRed (.wrap v m) 'a' ===> Nat.add 97 m

end Tests.UnifyPattern
