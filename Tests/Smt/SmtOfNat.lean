import Lean
import Blaster

namespace Test.SmtOfNat

/-! # Test cases on `OfNat.ofNat` applications whose instance is not the standard one.
     The normalization rules `OfNat.ofNat Nat n ==> n`, `OfNat.ofNat Int n ==> Int.ofNat n`, ... only apply
     to the standard instances. With a non-standard instance (`⟨99⟩`, `⟨i⟩`, or a local instance variable)
     the value of `OfNat.ofNat T 7 inst` is unrelated to `7`.
     NOTE: fixed-width integers (`UInt8`, ...) are not covered here as `BitVec` is not supported by the
     SMT translation; see `Tests/Optimize/OptimizeOfNat.lean` for the corresponding normalization tests.
-/

structure Wrap where
  val : Nat

/-! ## Valid statements (hold for any instance) -/

-- literal non-standard instance: the value is 99
#blaster [∀ (x : Nat), x < @OfNat.ofNat Nat 7 ⟨99⟩ → x < 100]
#blaster [∀ (x : Nat), @OfNat.ofNat Nat 7 ⟨99⟩ + x = 99 + x]
#blaster [∀ (x : Int), x < @OfNat.ofNat Int 7 ⟨99⟩ → x < 100]

-- symbolic instance: the value is the payload
#blaster [∀ (i x : Nat), x < @OfNat.ofNat Nat 7 ⟨i⟩ → x < i + 1]
#blaster [∀ (i x : Nat), @OfNat.ofNat Nat 7 ⟨i⟩ + x = i + x]
#blaster [∀ (i x : Int), x < @OfNat.ofNat Int 7 ⟨i⟩ → x < i + 1]

-- local instance variable: the application is left as an uninterpreted term
#blaster [∀ [inst : OfNat Nat (nat_lit 7)] (x : Nat), x < @OfNat.ofNat Nat (nat_lit 7) inst → x + 1 ≤ @OfNat.ofNat Nat (nat_lit 7) inst]
#blaster [∀ [inst : OfNat Int (nat_lit 7)] (x : Int), x < @OfNat.ofNat Int (nat_lit 7) inst → x + 1 ≤ @OfNat.ofNat Int (nat_lit 7) inst]
#blaster [∀ [inst : OfNat Wrap 5] (f : Wrap → Nat), f (@OfNat.ofNat Wrap 5 inst) < 1 → f (@OfNat.ofNat Wrap 5 inst) = 0]
#blaster [∀ [inst : OfNat Wrap 5], (@OfNat.ofNat Wrap 5 inst).val < 1 → (@OfNat.ofNat Wrap 5 inst).val = 0]
#blaster [∀ [inst : OfNat Wrap 5] (f : Wrap → Nat), f (@OfNat.ofNat Wrap 5 inst) = f 5]

/-! ## Test cases to ensure that counterexample are properly detected
      (each statement is falsified by taking the value of the instance to be `99`) -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x < @OfNat.ofNat Nat 7 ⟨99⟩ → x < 10]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), @OfNat.ofNat Nat 7 ⟨99⟩ = 7]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (i x : Nat), x < @OfNat.ofNat Nat 7 ⟨i⟩ → x < 10]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (i : Nat), @OfNat.ofNat Nat 7 ⟨i⟩ = 7]
#blaster (gen-cex: 0) (solve-result: 1) [∀ [inst : OfNat Nat (nat_lit 7)] (x : Nat), x < @OfNat.ofNat Nat (nat_lit 7) inst → x < 10]
-- NOTE: a literal `7` elaborated under `[inst : OfNat Nat 7]` resolves to `inst` itself, hence `nat_lit`
#blaster (gen-cex: 0) (solve-result: 1) [∀ [inst : OfNat Nat (nat_lit 7)], @OfNat.ofNat Nat (nat_lit 7) inst = nat_lit 7]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x < @OfNat.ofNat Int 7 ⟨99⟩ → x < 10]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), @OfNat.ofNat Int 7 ⟨99⟩ = 7]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (i x : Int), x < @OfNat.ofNat Int 7 ⟨i⟩ → x < 10]
#blaster (gen-cex: 0) (solve-result: 1) [∀ [inst : OfNat Int (nat_lit 7)] (x : Int), x < @OfNat.ofNat Int (nat_lit 7) inst → x < 10]


end Test.SmtOfNat
