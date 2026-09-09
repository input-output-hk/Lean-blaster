import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

namespace Tests.Specialize

def lookup (xs : List (String × Nat)) (key : String) : Option Nat :=
  match xs with
  | [] => none
  | (name, value) :: rest =>
      if key = name then some value else lookup rest key

-- Every input is checked against the original definition as well as the
-- ordinary optimizer. This includes shadowing, missing names, symbolic names,
-- sibling branches, and values captured under different lambdas.
run_cmd liftTermElabM do
  let inputs := #[
    (← `(fun x y : Nat => lookup [("x", x), ("x", y)] "x")),
    (← `(fun x y : Nat => lookup [("other", x), ("x", y)] "x")),
    (← `(fun x : Nat => lookup [("other", x)] "missing")),
    (← `(fun key : String => lookup [("x", 3), ("y", 5)] key)),
    (← `(fun b : Bool => lookup [(if b then "x" else "y", 3), ("x", 5)] "x")),
    (← `(fun b : Bool => (lookup [("x", if b then 1 else 2)] "x",
                         lookup [("x", if b then 2 else 1)] "x"))),
    (← `(fun x : Nat => (fun y : Nat => lookup [("x", x), ("y", y)] "y"))),
    (← `(fun xs : List (String × Nat) => lookup xs "x")),
    (← `(lookup []))
  ]
  for stx in inputs do
    let input ← Tests.parseTerm stx
    let expected ← (Optimize.main input).run' (default : TranslateEnv)
    let env := specializeExt.modifyState (← getEnv) (·.push ``lookup)
    let actual ← withEnv env <| (Optimize.main input).run' (default : TranslateEnv)
    unless ← isDefEq actual expected do
      throwError "specialization changed normalization: {input}"
    unless ← isDefEq actual input do
      throwError "specialization is not definitionally equal to the lookup: {input}"

section
attribute [local blaster_specialize] lookup

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

-- A local annotation must not escape its section.
run_cmd do
  if (specializeExt.getState (← getEnv)).contains ``lookup then
    throwError "local specialization attribute escaped its scope"

end Tests.Specialize
