import Blaster
import Tests.Proof.Support

/-!
# A statement machine (not the CEK machine)

A small-step machine for an accumulator language, in the style of a CEK
machine: the statement being executed, a continuation of statements, the
accumulator and the remaining inputs. Two programs are proved through the
explorer from their runs: a loop (`bounded`, for a threshold of a finite sum
type, which the solver reasons about by cases) and a recursive procedure whose
continuation grows with the input (`counted`). The rejected claims check that
neither a claim false for one threshold nor a false invariant model
establishes a theorem.
-/

namespace Tests.Machine

/-- Statements of a small accumulator language over a list of integer inputs. -/
inductive Stmt where
  | skip
  | seq (first second : Stmt)
  | setAcc (value : Int)
  | addConst (value : Int)
  /-- Add the next input to the accumulator, consuming it (nothing when none is left). -/
  | addInput
  /-- Add every remaining input, consuming them. -/
  | sumInputs
  /-- Run procedure `index` when inputs remain. -/
  | callIfInputs (index : Nat)
  /-- Fail unless the accumulator is at least `bound`. -/
  | assertGe (bound : Int)
  /-- Fail unless the accumulator is at most `bound`. -/
  | assertLe (bound : Int)

structure Program where
  main : Stmt
  procedures : List Stmt

/-- A small-step machine in the style of a CEK machine: the statement being
executed, the continuation of statements still to run (innermost first), the
accumulator and the remaining inputs. `true` when everything has run. -/
def run (procedures : List Stmt) : Stmt → List Stmt → Int → List Int → Nat → Bool
  | _, _, _, _, 0 => false
  | .skip, [], _, _, _ + 1 => true
  | .skip, s :: k, acc, xs, n + 1 => run procedures s k acc xs n
  | .seq a b, k, acc, xs, n + 1 => run procedures a (b :: k) acc xs n
  | .setAcc v, k, _, xs, n + 1 => run procedures .skip k v xs n
  | .addConst v, k, acc, xs, n + 1 => run procedures .skip k (acc + v) xs n
  | .addInput, k, acc, [], n + 1 => run procedures .skip k acc [] n
  | .addInput, k, acc, x :: xs, n + 1 => run procedures .skip k (acc + x) xs n
  | .sumInputs, k, acc, [], n + 1 => run procedures .skip k acc [] n
  | .sumInputs, k, acc, x :: xs, n + 1 => run procedures .sumInputs k (acc + x) xs n
  | .callIfInputs _, k, acc, [], n + 1 => run procedures .skip k acc [] n
  | .callIfInputs i, k, acc, x :: xs, n + 1 =>
    match procedures[i]? with
    | some body => run procedures body k acc (x :: xs) n
    | none => false
  | .assertGe t, k, acc, xs, n + 1 => if t ≤ acc then run procedures .skip k acc xs n else false
  | .assertLe t, k, acc, xs, n + 1 => if acc ≤ t then run procedures .skip k acc xs n else false

def execute (p : Program) (xs : List Int) (fuel : Nat) : Bool :=
  match p with
  | ⟨main, procedures⟩ => run procedures main [] 0 xs fuel

def total : List Int → Int
  | [] => 0
  | x :: xs => x + total xs

/-- A threshold chosen by the caller. -/
inductive Mode where
  | low
  | high

def threshold : Mode → Int
  | .low => 0
  | .high => 10

/-- A loop: accept inputs whose sum lies in [10, 100]. -/
def bounded : Program := ⟨
  .seq (.setAcc 0)
  (.seq .sumInputs
  (.seq (.addConst (-10))
  (.seq (.assertGe 0)
  (.seq (.addConst (-90))
  (.seq (.assertLe 0)
  .skip))))), []⟩

/-- A recursive procedure: procedure 0 adds the next input, recurses while
inputs remain and adds one on return (as `+2`, `-1`), so the accumulator ends
at the sum plus the number of inputs; accept when that is at least 10. -/
def counted : Program := ⟨
  .seq (.setAcc 0)
  (.seq (.callIfInputs 0)
  (.seq (.addConst (-4))
  (.seq (.addConst (-6))
  (.seq (.assertGe 0)
  .skip)))),
  [.seq .addInput (.seq (.callIfInputs 0) (.seq (.addConst 2) (.addConst (-1))))]⟩

end Tests.Machine

set_option maxHeartbeats 0
set_option stderrAsMessages false

-- (the mode stays one variable: the solver reasons by cases)
theorem Tests.Machine.bounded_accepts (mode : Tests.Machine.Mode) (xs : List Int) :
    Tests.Machine.execute Tests.Machine.bounded xs 1000 = true →
      Tests.Machine.threshold mode ≤ Tests.Machine.total xs ∧ Tests.Machine.total xs ≤ 100 := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

theorem Tests.Machine.counted_accepts (xs : List Int) :
    Tests.Machine.execute Tests.Machine.counted xs 1000 = true →
      10 ≤ Tests.Machine.total xs + xs.length := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

-- False for `high` only: the inputs `[10]` are accepted.
#reject "invariant search failed" in
theorem Tests.Machine.bounded_above (mode : Tests.Machine.Mode) (xs : List Int) :
    Tests.Machine.execute Tests.Machine.bounded xs 1000 = true →
      Tests.Machine.threshold mode < Tests.Machine.total xs := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

-- A model is only a proposal: a false entry invariant must not establish even
-- a true statement.
#reject "verification conditions remain unproved" in
set_option blaster.explore.modelFile "Tests/Proof/Fixtures/false-invariant.model" in
theorem Tests.Machine.bounded_from_false_model (xs : List Int) :
    Tests.Machine.execute Tests.Machine.bounded xs 1000 = true → 10 ≤ Tests.Machine.total xs := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

#print axioms Tests.Machine.bounded_accepts
#print axioms Tests.Machine.counted_accepts
