import Blaster.FiniteField.Basic
import Lean

/-!
# Source rules for bounded power translation

These identities expose square-and-multiply on `Residue p` using only its
`Lean.Grind.CommRing` instance. A translator recursively translates the half
exponent once, reuses that result for the square, and adds one multiplication
by the base for odd exponents. The arithmetic identities are independent of
any translation budget and require neither primality nor field operations.
-/

namespace Blaster.FiniteField.Residue

variable {p : Nat} [NeZero p]

/-- The zero-exponent leaf is one, including when the base is zero. -/
theorem pow_zero (a : Residue p) : a ^ (0 : Nat) = 1 :=
  Lean.Grind.Semiring.pow_zero a

/-- The exponent-one leaf can reuse the translated base without multiplication. -/
theorem pow_one (a : Residue p) : a ^ (1 : Nat) = a :=
  Lean.Grind.Semiring.pow_one a

/-- An even binary step squares the result for its half exponent. -/
theorem pow_bit0 (a : Residue p) (k : Nat) :
    a ^ (k + k) = a ^ k * a ^ k :=
  Lean.Grind.Semiring.pow_add a k k

/-- An odd binary step squares the half-power, then multiplies by the base. -/
theorem pow_bit1 (a : Residue p) (k : Nat) :
    a ^ (k + k + 1) = (a ^ k * a ^ k) * a := by
  rw [Lean.Grind.Semiring.pow_succ, pow_bit0]

/-- The even half-exponent rule uses the single recursive exponent `n / 2`. -/
theorem pow_even (a : Residue p) (n : Nat) (h : n % 2 = 0) :
    a ^ n = a ^ (n / 2) * a ^ (n / 2) := by
  have hn : n = n / 2 + n / 2 := by omega
  calc
    a ^ n = a ^ (n / 2 + n / 2) := congrArg (fun k : Nat => a ^ k) hn
    _ = a ^ (n / 2) * a ^ (n / 2) := pow_bit0 a (n / 2)

/-- The odd half-exponent rule matches the nonzero-remainder branch directly. -/
theorem pow_odd (a : Residue p) (n : Nat) (h : n % 2 ≠ 0) :
    a ^ n = (a ^ (n / 2) * a ^ (n / 2)) * a := by
  have hn : n = n / 2 + n / 2 + 1 := by omega
  calc
    a ^ n = a ^ (n / 2 + n / 2 + 1) := congrArg (fun k : Nat => a ^ k) hn
    _ = (a ^ (n / 2) * a ^ (n / 2)) * a := pow_bit1 a (n / 2)

/-- In particular, source `0 ^ 0` is one, not a positive zero power. -/
theorem zero_pow_zero : (0 : Residue p) ^ (0 : Nat) = 1 :=
  pow_zero 0

/-- A successor power of the source zero is zero. -/
theorem zero_pow_succ (n : Nat) : (0 : Residue p) ^ (n + 1) = 0 := by
  rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.mul_zero]

/-- A positive source zero power is zero; positivity excludes `0 ^ 0`. -/
theorem zero_pow_pos (n : Nat) (h : 0 < n) : (0 : Residue p) ^ n = 0 := by
  cases n with
  | zero => omega
  | succ n => exact zero_pow_succ n

-- Reject any unexpected axiom in the transitive dependencies of every rule.
run_cmd do
  for declaration in #[
      ``pow_zero, ``pow_one, ``pow_bit0, ``pow_bit1, ``pow_even, ``pow_odd,
      ``zero_pow_zero, ``zero_pow_succ, ``zero_pow_pos] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected residue power axiom in {declaration}: {axiomName}"

end Blaster.FiniteField.Residue
