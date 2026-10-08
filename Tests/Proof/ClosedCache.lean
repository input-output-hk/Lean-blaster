import Blaster
import Tests.Proof.Support

/-! A false statement that Blaster must refute. The optimizer rewrites the
closed term `f ∧ g` to `g` under the hypothesis `f`; before the fix it cached
that rewrite globally and reused it outside the hypothesis, proving the
statement. -/

opaque auditF : Nat → Bool
opaque auditG : Nat → Bool

#reject "Goal was falsified" in
theorem closed_cache_false :
    (auditF 0 = true → ((auditF 0 = true ∧ auditG 0 = true) ↔ auditG 0 = true)) ∧
    ((auditF 0 = true ∧ auditG 0 = true) ↔ auditG 0 = true) := by
  blaster (timeout: 10)
