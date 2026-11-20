import Tests.Utils

open Lean Elab Command Term Meta Blaster.Optimize
namespace Tests.EarlyListSelector

#testOptimize ["LookupSelectedComputation"] (norm-result: 1)
  List.get?Internal [1 + 2, 4 + 5] 0 ===> some 3

#testOptimize ["LookupSecondComputation"] (norm-result: 1)
  List.get?Internal [1 + 2, 4 + 5] 1 ===> some 9

#testOptimize ["LookupBeyondEnd"] (norm-result: 1)
  List.get?Internal [1, 2] 4 ===> (none : Option Nat)

#testOptimize ["LookupComputedIndex"] (norm-result: 1)
  List.get?Internal [1, 2, 3] (1 + 1) ===> some 3

-- Concrete prefix lookup does not depend on the unknown tail.
example (a b : Nat) (xs : List Nat) :
    List.get?Internal (a :: b :: xs) 1 = some b := by blaster (only-optimize: 1)

-- Consuming a prefix must retain the right index on the residual lookup.
example (a b : Nat) (xs : List Nat) :
    List.get?Internal (a :: b :: xs) 3 = List.get?Internal xs 1 := by blaster (only-optimize: 1)

example (n : Nat) : List.get?Internal ([] : List Nat) n = none := by blaster (only-optimize: 1)

-- The selected element still receives contextual rewriting.
example (a b : Nat) : a = b → List.get?Internal [a, 10] 0 = some b := by blaster
example (a b : Nat) :
    (a = b → List.get?Internal [a, 10] 0 = some b) ∧
    (a = 7 → List.get?Internal [a, 10] 0 = some 7) := by blaster


-- Exercise the early rule itself: a frontend numeral must select the element
-- without normalizing or assigning the skipped head or the unknown list tail.
elab "#check_early_frontend_lookup" : command => runTermElabM fun _ => do
  let nat := Lean.mkConst ``Nat
  let skipped ← mkFreshExprMVar (some nat)
  let tail ← mkFreshExprMVar (some (mkApp (Lean.mkConst ``List [levelZero]) nat))
  let selected := mkApp2 (Lean.mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)
  let cons := mkApp (Lean.mkConst ``List.cons [levelZero]) nat
  let list := mkApp2 cons skipped (mkApp2 cons selected tail)
  let expected := mkApp2 (Lean.mkConst ``Option.some [levelZero]) nat selected
  let work : TranslateEnvT Unit := do
    let result ← reduceListLookupBeforeArgs? (Lean.mkConst ``List.get?Internal [levelZero]) #[nat, list, mkNatLit 1]
    let some result := result | throwError "Frontend lookup did not reduce early"
    unless Expr.eqv result expected do throwError "Wrong early lookup result"
  discard <| work.run default
  unless (← getExprMVarAssignment? skipped.mvarId!).isNone &&
      (← getExprMVarAssignment? tail.mvarId!).isNone do
    throwError "Early lookup assigned an unused list component"

#check_early_frontend_lookup

-- A symbolic index over a known spine keeps the selected value concrete.
example (a b n : Nat) : List.get?Internal [a, b] n =
    Nat.casesOn (motive := fun _ => Option Nat) n (some a)
      (fun k => Nat.casesOn (motive := fun _ => Option Nat) k (some b) (fun _ => none)) := by
  blaster

-- An unknown tail stays a recursive lookup rather than an arbitrary element.
example (α : Type) (a : α) (xs : List α) (n : Nat) : List.get?Internal (a :: xs) n =
    Nat.casesOn (motive := fun _ => Option α) n (some a) (fun k => List.get?Internal xs k) := by
  blaster

-- Contextual index information must discard the skipped computation first.
private def slow : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => slow n (acc + 1)

example (n : Nat) : n = 1 → List.get?Internal [slow 1000000 0, 42] n = some 42 := by
  blaster (only-optimize: 1)

-- Independent kernel checks of both symbolic cases and out-of-range behavior.
example (α : Type) (a b : α) (n : Nat) : List.get?Internal [a, b] n =
    Nat.casesOn (motive := fun _ => Option α) n (some a)
      (fun k => Nat.casesOn (motive := fun _ => Option α) k (some b) (fun _ => none)) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

end Tests.EarlyListSelector
