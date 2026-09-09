import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

namespace Tests.Specialize

def lookup (xs : List (String × Nat)) (key : String) : Option Nat :=
  match xs with
  | [] => none
  | (name, value) :: rest =>
      if key = name then some value else lookup rest key

-- Compare with the ordinary optimizer; closed-control cases also check
-- definitional equality with the original input. This includes shadowing, missing names, symbolic names,
-- sibling branches, and values captured under different lambdas.
run_cmd liftTermElabM do
  let inputs := #[
    (← `(fun x y : Nat => lookup [("x", x), ("x", y)] "x")),
    (← `(fun x y : Nat => lookup [("other", x), ("x", y)] "x")),
    (← `(fun x : Nat => lookup [("other", x)] "missing")),
    (← `(fun b : Bool => lookup [(if b then "x" else "y", 3), ("x", 5)] "x")),
    (← `(fun b : Bool => (lookup [("x", if b then 1 else 2)] "x",
                         lookup [("x", if b then 2 else 1)] "x"))),
    (← `(fun x : Nat => (fun y : Nat => lookup [("x", x), ("y", y)] "y"))),
    (← `(fun xs : List (String × Nat) => lookup xs "x")),
    (← `(lookup []))
  ]
  for i in [:inputs.size] do
    let stx := inputs[i]!
    let input ← Tests.parseTerm stx
    let expected ← (Optimize.main input).run' (default : TranslateEnv)
    let env := specializeExt.modifyState (← getEnv) (·.insert ``lookup 0)
    let actual ← withEnv env <| (Optimize.main input).run' (default : TranslateEnv)
    unless ← isDefEq actual expected do
      throwError "specialization changed normalization: {input}\nactual: {actual}\nexpected: {expected}"
    unless i >= 3 || (← isDefEq actual input) do
      throwError "specialization is not definitionally equal to the lookup: {input}"

-- This case intentionally specializes farther than the ordinary optimizer.
-- Check the explicit residual against Lean's kernel, then against Blaster.
theorem symbolic_key_correct (key : String) :
    lookup [("x", 3), ("y", 5)] key =
      (Blaster.dite' ("x" = key) (fun _ => some 3)
        (fun _ => Blaster.dite' ("y" = key) (fun _ => some 5) (fun _ => none))) := by
  have h : lookup [("x", 3), ("y", 5)] key =
      (if "x" = key then some 3 else if "y" = key then some 5 else none) := by
    simp [lookup, eq_comm]
  simpa only [Blaster.ite_to_dite'_equiv] using h

section
attribute [local blaster_specialize 1] lookup

#testOptimize ["SpecializedSymbolicKey"] (norm-result: 1)
  (fun key : String => lookup [("x", 3), ("y", 5)] key) ===>
  (fun key : String => Blaster.dite' ("x" = key) (fun _ => some 3)
    (fun _ => Blaster.dite' ("y" = key) (fun _ => some 5) (fun _ => none)))


#testOptimize ["SpecializedLookupShadowing"]
  (fun x y : Nat => lookup [("x", x), ("x", y)] "x") ===>
  (fun x _ : Nat => some x)

#testOptimize ["SpecializedLookupSkipsUnusedBranches"] (norm-result: 1)
  (fun a b : Bool => lookup [("unused", if a then 1 else 2),
                            ("unused", if b then 3 else 4), ("x", 7)] "x") ===>
  (fun _ _ : Bool => some 7)

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ x y : Nat, lookup [("x", x), ("x", y)] "x" = some y]
end

-- The selected fuel may be known while the payload remains symbolic. Repeated
-- swaps exercise assignment restoration and simultaneous substitution.
def swapFuel (fuel : Nat) (x y : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (x, y)
  | n + 1 => swapFuel n y x

section
attribute [local blaster_specialize 1] swapFuel
#testOptimize ["SpecializedFuelSymbolicPayload"]
  (fun x y : Nat => swapFuel 12 x y) ===> (fun x y : Nat => (x, y))
#testOptimize ["SpecializedFuelOddSwaps"]
  (fun x y : Nat => swapFuel 13 x y) ===> (fun x y : Nat => (y, x))
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ x y : Nat, swapFuel 13 x y = (x, y)]
end

-- A local annotation must not escape its section.
run_cmd do
  if (specializeExt.getState (← getEnv)).contains ``lookup then
    throwError "local specialization attribute escaped its scope"

end Tests.Specialize
