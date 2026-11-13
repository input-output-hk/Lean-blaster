import Blaster

set_option warningAsError true

namespace Tests.Reconstruct.Z3

open Lean Elab Command in
elab "#standard_axioms " n:ident : command => do
  let axioms ← liftCoreM (collectAxioms n.getId)
  let forbidden := axioms.filter fun a => ![``propext, ``Classical.choice, ``Quot.sound].contains a
  unless forbidden.isEmpty do throwError "unexpected axioms: {forbidden.toList}"

-- Actual TxPipe optimization, certificate replay, then Z3 reconstruction.
theorem square (x : Int) : 0 ≤ -(-x) * -(-x) := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms square

theorem local_let (x : Int) : 0 ≤ (x + 1) * (x + 1) := by
  let y := x + 1
  change 0 ≤ y * y
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms local_let

theorem hypothesis_transport (x y : Int) (h : -(-x) ≤ y) : x + 1 ≤ y + 1 := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms hypothesis_transport

theorem quantified_transport : ∀ (x y : Int), -(-x) ≤ y → x + 1 ≤ y + 1 := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms quantified_transport

theorem optimizer_only (x : Int) : -(-x) = x := by
  blaster (gen-proof: 1) (only-optimize: 1)
#standard_axioms optimizer_only

theorem string_assoc (s t u : String) : (s ++ t) ++ u = s ++ (t ++ u) := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms string_assoc

theorem nat_power (x : Nat) : x ^ 2 = x * x := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_power

theorem nat_div (x y : Nat) : x / (y + 1) ≤ x := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_div

theorem poly_option (α : Type) (x : Option α) : x.isSome = true → x ≠ none := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms poly_option

-- Checked command path and option order must both enforce reconstruction.
#blaster (gen-proof: 1) (timeout: 5) [∀ x : Int, 0 ≤ x * x]
#blaster (gen-proof: 1) (reconstruct: 0) (timeout: 5) [∀ x : Int, 0 ≤ x * x]

-- False claims and an optimizer-only run that leaves a residual are rejected.
example : True := by
  fail_if_success
    have impossible : (1 : Int) = 0 := by blaster (gen-proof: 1) (timeout: 5)
  fail_if_success
    have unfinished (x : Int) : 0 ≤ x * x := by
      blaster (gen-proof: 1) (only-optimize: 1)
  trivial

end Tests.Reconstruct.Z3
