import Tests.Utils
import Blaster.Optimize.Env.GroundValue

open Lean Elab Command Term Meta Blaster.Optimize

namespace Tests.GroundValue

axiom customNumeral : OfNat Nat 1

inductive Tree where
  | leaf (n : Nat)
  | branch (left right : Tree)
  | text (value : String)

-- Recognition must not suppress computations or canonical literal conversion.
#testOptimize ["GroundFieldComputation"] (norm-result: 1)
  Tree.branch (Tree.leaf (1 + 2)) (Tree.leaf (Nat.succ Nat.zero)) ===>
  Tree.branch (Tree.leaf 3) (Tree.leaf 1)

#testOptimize ["GroundStringConversion"] (norm-result: 1)
  Tree.text (String.mk []) ===> Tree.text ""

elab "#check_ground_contexts" : command => runTermElabM fun _ => do
  let leaf := fun n => mkApp (mkConst ``Tree.leaf) (mkRawNatLit n)
  let a := leaf 1
  let b := leaf 2
  let c := leaf 3
  let computation := mkApp (mkConst ``Tree.leaf)
    (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 1) (mkRawNatLit 2))
  let work : TranslateEnvT Unit := do
    unless ← isGroundConstructorValue a do throwError "Literal tree not recognized"
    let frontend := mkApp (mkConst ``Tree.leaf) (mkNatLit 1)
    let some canonical ← groundConstructorValue? frontend | throwError "Frontend literal not recognized"
    unless Expr.eqv canonical a do throwError "Wrong numeral conversion"
    let custom := mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Nat)
      (mkRawNatLit 1) (mkConst ``customNumeral)
    if ← isGroundConstructorValue custom then throwError "Custom numeral instance was folded"
    let some negative ← groundConstructorValue? (toExpr (-7 : Int)) | throwError "Negative literal not recognized"
    let expected ← mkIntLitExpr (-7)
    unless Expr.eqv negative expected do throwError "Wrong negative literal conversion"
    if ← isGroundConstructorValue computation then throwError "Computation recognized as a value"
    if ← isGroundConstructorValue (mkApp (mkConst ``Tree.branch) a) then
      throwError "Partial constructor recognized as a value"
    let a ← hashcons a
    let b ← hashcons b
    let c ← hashcons c
    let checkTerm := fun term expected => do
      let actual ← optimizeExpr term
      unless Expr.eqv actual expected do throwError "Wrong contextual constructor rewrite"
    let check := checkTerm a
    -- Warm the shared classification and global normalization cache.
    discard <| Optimize.main a
    let parent ← newCtx
    updateEqualityMap a b parent.current
    check b
    checkTerm frontend b
    let child ← newCtx
    updateEqualityMap a c child.current
    check c
    endCtx child
    check b
    endCtx parent
    check a
    checkTerm frontend a
    let sibling ← newCtx
    updateEqualityMap a c sibling.current
    check c
    checkTerm frontend c
    endCtx sibling
    check a
  discard <| work.run default

#check_ground_contexts

end Tests.GroundValue
