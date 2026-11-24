import Blaster

-- Problem: a goal the optimizer closes by rewriting is proved by replaying its proof stack, and
--          the replay embeds in its proof the optimizer's terms and the definitions it unfolds.
--          When one of them depends on `sorryAx`, the `blaster` proof depended on `sorryAx` too,
--          with only Lean's generic "declaration uses 'sorry'" warning: `#print axioms` showed
--          `sorryAx` where the theorem should be admitted via `blasterProven`, as any other
--          reconstruction gap.
--
-- Diagnosis: nothing on the path of `blaster` rejected a reconstructed proof depending on
--            `sorryAx`; only the `#testOptimize` gate checked it, with its own walk.
-- Modifications: `proveGoalByProofStack`, the single exit of the replay, rejects a proof that
--                depends on `sorryAx` (`containsSorry`): the goal is a reconstruction gap,
--                admitted via `blasterProven` with the gap warning, and an error in the gate
--                (`admit := false`), which relies on this check instead of its own walk.

namespace Tests.ReplaySorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def g (n : Nat) : Nat := if n = 0 then 0 else sorry

/-! ## A `sorry` in a definition the optimizer unfolds -/

-- the replay on the whole goal
/--
info: ✅ Valid
---
warning: blaster: reconstruction gap, admitted via `blasterProven`
the proof depends on `sorryAx`
-/
#guard_msgs in
theorem unfold_sorry : g 0 = 0 := by blaster

-- `sorryAx` is still listed, as the statement uses `g`
/--
info: 'Tests.ReplaySorry.unfold_sorry' depends on axioms: [sorryAx,
 _private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms unfold_sorry

-- `P = True`, proved from a proof of `P` by `eq_true`
/--
info: ✅ Valid
---
warning: blaster: reconstruction gap, admitted via `blasterProven`
the proof depends on `sorryAx`
-/
#guard_msgs in
theorem unfold_sorry_eq_true : (g 0 = 0) = True := by blaster

/--
info: 'Tests.ReplaySorry.unfold_sorry_eq_true' depends on axioms: [sorryAx,
 _private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms unfold_sorry_eq_true

-- an equation of foralls whose binders match, proved by `propext` from the replay of the
-- equation of their bodies (`proveForallEq`)
/--
info: ✅ Valid
---
warning: blaster: reconstruction gap, admitted via `blasterProven`
the proof depends on `sorryAx`
-/
#guard_msgs in
theorem unfold_sorry_forall_eq :
    (∀ (x y : Nat), x < y ∧ g 0 = 0) = (∀ (x y : Nat), x < y) := by blaster

/--
info: 'Tests.ReplaySorry.unfold_sorry_forall_eq' depends on axioms: [sorryAx,
 _private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms unfold_sorry_forall_eq

/-! ## A `sorry` in a term of the optimizer -/

-- NOTE: this depends on the `sorry` that the optimizer puts in the term of a `Char` literal
--       (`valid := sorry`, `backwardProof` in `Blaster/Optimize/Hypotheses.lean`). When that
--       is fixed, the warning and the axioms below change.
/--
info: ✅ Valid
---
warning: blaster: reconstruction gap, admitted via `blasterProven`
the proof depends on `sorryAx`
-/
#guard_msgs in
theorem char_ne : ¬ ('a' = 'b') := by blaster

/--
info: 'Tests.ReplaySorry.char_ne' depends on axioms: [_private.Blaster.Command.Tactic.0.Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms char_ne

end Tests.ReplaySorry
