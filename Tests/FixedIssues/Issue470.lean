import Blaster

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/470
--        `Blaster.Tactic.blasterProven : ∀ {α : Sort u}, α` is the axiom used by the `blaster`
--        tactic to close SMT-verified goals. Since it was public, any user code (e.g., an LLM
--        generated proof) could reference it directly and "prove" anything, including `False`,
--        without invoking the solver.
--
-- Modifications: `blasterProven` is now a `private` axiom. It can only be referenced from
--                `Blaster/Command/Tactic.lean`, where the `blaster` tactic builds its proof term.
--
-- NOTE: `example`s are used for the rejected cases so that no declaration is
--       added to the environment (in particular in the `Blaster.Tactic` namespace).

/-! ## Original example -/

namespace Tests.Issue470

/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
theorem contradiction : False :=
  Blaster.Tactic.blasterProven

theorem two_eq_one : (2 : Nat) = 1 :=
  False.elim contradiction

-- `contradiction` is admitted by error recovery: the "proof" now only relies on `sorryAx`.
/-- info: 'Tests.Issue470.two_eq_one' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms two_eq_one

end Tests.Issue470

/-! ## Term-mode references -/

-- explicit universe-polymorphic application
/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := @Blaster.Tactic.blasterProven False

-- named implicit argument
/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := Blaster.Tactic.blasterProven (α := False)

-- `_root_` qualified name
/-- error: Unknown identifier `_root_.Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := _root_.Blaster.Tactic.blasterProven

-- `show ... from` with a non `False` goal
/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : (2 : Nat) = 1 := show (2 : Nat) = 1 from Blaster.Tactic.blasterProven

-- the axiom is universe polymorphic: an uninhabited type (`Sort 1`) must not be inhabited either
/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : Empty := Blaster.Tactic.blasterProven

-- inside a structure instance
/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : Inhabited Empty := ⟨Blaster.Tactic.blasterProven⟩

/-! ## Tactic-mode references -/

/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := by exact Blaster.Tactic.blasterProven

/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := by apply Blaster.Tactic.blasterProven

/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
example : False := by
  have h : False := Blaster.Tactic.blasterProven
  exact h

/-! ## Namespace manipulation -/

-- `open` does not expose private declarations of another module
section
open Blaster.Tactic

/-- error: Unknown identifier `blasterProven` -/
#guard_msgs in
example : False := blasterProven
end

-- partially qualified name after opening the parent namespace
section
open Blaster

/-- error: Unknown identifier `Tactic.blasterProven` -/
#guard_msgs in
example : False := Tactic.blasterProven
end

-- re-entering the `Blaster.Tactic` namespace in another module
namespace Blaster.Tactic

/-- error: Unknown identifier `blasterProven` -/
#guard_msgs in
example : False := blasterProven

end Blaster.Tactic

/-- error: Unknown constant `Blaster.Tactic.blasterProven` -/
#guard_msgs in
open Blaster.Tactic (blasterProven)

/-- error: Unknown constant `Blaster.Tactic.blasterProven` -/
#guard_msgs in
open Blaster.Tactic renaming blasterProven → bp

/-- error: Unknown constant `Blaster.Tactic.blasterProven` -/
#guard_msgs in
export Blaster.Tactic (blasterProven)

/-! ## Name resolution in commands and metaprograms -/

/-- error: Unknown identifier `Blaster.Tactic.blasterProven` -/
#guard_msgs in
#check Blaster.Tactic.blasterProven

/-- error: Unknown constant `Blaster.Tactic.blasterProven` -/
#guard_msgs in
#print Blaster.Tactic.blasterProven

-- the double backtick name literal is resolved at elaboration time
/-- error: Unknown constant `Blaster.Tactic.blasterProven` -/
#guard_msgs in
open Lean in
example : Name := ``Blaster.Tactic.blasterProven

/-! ## The `blaster` tactic is unaffected -/

namespace Tests.Issue470

/--
info: ✅ Valid
---
warning: declaration uses 'blasterProven' (SMT-verified, no proof term)
-/
#guard_msgs in
theorem add_zero_blaster (x : Nat) : x + 0 = x := by blaster

-- SMT-verified theorems are still distinguishable from kernel-checked proofs
/--
info: 'Tests.Issue470.add_zero_blaster' depends on axioms: [_private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms add_zero_blaster

-- including transitively, through a theorem relying on an SMT-verified one
theorem uses_add_zero_blaster : (3 : Nat) + 0 = 3 := add_zero_blaster 3

/--
info: 'Tests.Issue470.uses_add_zero_blaster' depends on axioms: [_private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms uses_add_zero_blaster

-- `blaster` still closes goals under hypotheses (and `warn.sorry` still silences its warning)
/-- info: ✅ Valid -/
#guard_msgs in
set_option warn.sorry false in
theorem eq_symm_blaster (a b : Nat) (h : a = b) : b = a := by blaster

/--
info: 'Tests.Issue470.eq_symm_blaster' depends on axioms: [_private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms eq_symm_blaster

end Tests.Issue470
