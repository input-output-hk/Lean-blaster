import Lean
/-! Stable logical recursion models for native operations whose implementation
    changed in Lean 4.35. The theorems below justify using these models during
    preprocessing; their constants are replaced with the original operation when
    constructing its recursive optimizer body. -/
namespace Blaster.Optimize.Canonical

def intPow (a : Int) : Nat → Int
  | 0 => 1
  | n+1 => a * intPow a n

theorem intPow_eq (a : Int) (n : Nat) : intPow a n = Int.pow a n := by
  change intPow a n = a ^ n
  induction n with
  | zero => simp [intPow]
  | succ n ih => simp [intPow, Int.pow_succ, ih, Int.mul_comm]

def natBle : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _+1 => true
  | _+1, 0 => false
  | n+1, m+1 => natBle n m

theorem natBle_eq (n m : Nat) : natBle n m = Nat.ble n m := by
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n ih => cases m <;> simp [natBle, Nat.ble, ih]

def listBeq {α : Type u} [BEq α] : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => listBeq xs ys && x == y
  | _, _ => false

theorem listBeq_eq {α : Type u} [BEq α] (xs ys : List α) : listBeq xs ys = List.beq xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp [listBeq, List.beq, ih, Bool.and_comm]
/-- The equivalence theorem is the registration: the model is read from its left
    side, and both sides must apply their function to every quantified parameter
    in order. This prevents the selected body and its correctness theorem from
    drifting apart. -/
def modelName? (native : Lean.Name) : Lean.MetaM (Option Lean.Name) := do
  let some theoremName := equivalenceTheorem? native | return none
  Lean.Meta.forallTelescope (← Lean.getConstInfo theoremName).type fun params proposition => do
    let some (_, modelApp, nativeApp) := proposition.eq?
      | throwError "Canonical model: equality theorem expected for {native}"
    let .const model _ := modelApp.getAppFn
      | throwError "Canonical model: a defined function expected for {native}"
    unless nativeApp.isAppOf native && nativeApp.getAppArgs == params &&
        modelApp.getAppArgs == params do
      throwError "Canonical model: {theoremName} must relate both functions at every parameter"
    return some model
where
  equivalenceTheorem? : Lean.Name → Option Lean.Name
  | ``Int.pow => some ``intPow_eq
  | ``Nat.ble => some ``natBle_eq
  | ``List.beq => some ``listBeq_eq
  | _ => none

end Blaster.Optimize.Canonical
