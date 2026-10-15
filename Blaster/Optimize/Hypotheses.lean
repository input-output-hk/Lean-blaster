import Lean
import Blaster.Optimize.Lemmas
import Blaster.Optimize.Rewriting.OptimizePropNot

open Lean Meta Elab Blaster.Data.HashMap

namespace Blaster.Optimize


/-- Check the veracity of a premise by performing the following:
     When `e := True`
       - return `true`
     When `e := False`
       - return `false`
     Otherwise:
        - return `
    NOTE: This function is to be used only by Blaster extension.
-/
@[always_inline, inline]
def isTruePremise (e : Expr) : TranslateEnvT Bool :=
 match e with
 | Expr.const ``True _ => return true
 | Expr.const ``False _ => return false
 | _ => hypMapContains e

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≠ 0
      - 0 < e := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def gtZeroNatInHyps (e : Expr) : TranslateEnvT Bool := do
 match isNatValue? e with
 | .some 0 => return false
 | .some _ => return true
 | .none   =>
     let zero_nat ← mkNatLitExpr 0
     let zero_lt ← mkNatLtExpr zero_nat e
     hypMapContains zero_lt

/-- Return `true` only when one of the following conditions is satisfied:
      - e := 0
      - 0 = e := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def eqZeroNatInHyps (e : Expr) : TranslateEnvT Bool := do
 match isNatValue? e with
 | .some 0 => return true
 | .some _ => return false
 | .none   =>
     let zero_nat ← mkNatLitExpr 0
     let zero_eq ← mkNatEqExpr zero_nat e
     hypMapContains zero_eq

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≠ 0
      - ¬ (0 = e) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def nonZeroNatInHyps (e : Expr) : TranslateEnvT Bool := do
 match isNatValue? e with
 | .some 0 => return false
 | .some _ => return true
 | .none   =>
     let zero_nat ← mkNatLitExpr 0
     let zero_eq ← mkNatEqExpr zero_nat e
     let not_eq_zero ← mkAppExpr (← mkPropNotOp) zero_eq
     hypMapContains not_eq_zero

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N < 0
      - e < 0 := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def ltZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.negSucc _) => return true
 | .some _            => return false
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let lt_zero ← mkIntLtExpr e zero_int
     hypMapContains lt_zero

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N > 0
      - 0 < e := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def gtZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat 0) => return false
 | .some (.ofNat _) => return true
 | .some _          => return false
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     hypMapContains zero_lt

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≠ 0
      - ¬ (0 = e) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def nonZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat 0) => return false
 | .some _          => return true
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_eq ← mkIntEqExpr zero_int e
     hypMapContains (← mkAppExpr (← mkPropNotOp) zero_eq)

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≥ 0
      - ¬ (e < 0) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def geqZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat _) => return true
 | .some _          => return false
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let lt_zero ← mkIntLtExpr e zero_int
     hypMapContains (← mkAppExpr (← mkPropNotOp) lt_zero)

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≤ 0
      - ¬ (0 < e) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def leqZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat 0) => return true
 | .some (.ofNat _) => return false
 | .some _          => return true
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     hypMapContains (← mkAppExpr (← mkPropNotOp) zero_lt)

@[always_inline, inline]
def updateHypMap (e : Expr) (fv : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
 match (← get).optEnv.hypothesisContext.hypothesisMap.get? e with
 | none =>
    let refEntry ← IO.mkRef [(nextCtxId, fv)]
    modifyOptEnv
      fun ⟨o1, o2, o3, o4, o5, o6, o7, ⟨hypothesisMap, equalityMap⟩, o9, o10, o11, o12, o13, o14⟩ =>
          ⟨o1, o2, o3, o4, o5, o6, o7, ⟨hypothesisMap.insert e refEntry, equalityMap⟩, o9, o10, o11, o12, o13, o14⟩
 | some refEntry => refEntry.modify (λ l => (nextCtxId, fv) :: l)

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := ¬ false = e`
        - add `true = c := Blaster.true_eq_of_not_false_eq e h` to hypothesisMap
     - When `e := ¬ true = e`
        - add `false = e := Blaster.false_eq_of_not_true_eq e h` to hypothesisMap

     - When `e := ¬ (0 < a) ∧ Type(a) = Nat`
         - add `0 = a := Blaster.nat_zero_eq_of_not_zero_lt a h` to hypothesisMap

     - When `e := ¬ (a < N) ∧ Type(a) = Nat ∧ N ≠ 0`
         - add `0 < a := Blaster.nat_zero_lt_of_not_lt_neq a N h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
         - add `¬ (0 = a) := Blaster.nat_not_zero_eq_of_zero_lt a
                             (Blaster.nat_zero_lt_of_not_lt_neq a N h (← mkOfDecideEqProof (¬ (0 = N)) true))` to hypothesisMap

     - When `e := ¬ (0 = a) ∧ Type(a) = Nat`
         - add `0 < a := Blaster.nat_zero_lt_of_not_zero_e a h` to hypothesisMap

     - When `e := ¬ (a < N) ∧ Type(a) = Int ∧ N > 0`
          - add `0 < a := Blaster.int_zero_lt_of_nlt_zero_lt a N h (← mkOfDecideEqProof (0 < N)) true)` to hypothesisMap
          - add `¬ (0 = a) := Blaster.int_not_zero_eq_of_zero_lt a
                              (Blaster.int_zero_lt_of_nlt_zero_lt a N h (← mkOfDecideEqProof (0 < N)) true))` to hypothesisMap
          - add `¬ (a < 0) := Blaster.int_not_lt_of_lt 0 a
                              (Blaster.int_zero_lt_of_nlt_zero_lt a N h (← mkOfDecideEqProof (0 < N)) true))` to hypothesisMap

     - When `e := ¬ (N < a) ∧ Type(a) = Int ∧ N < 0`
          - add `a < 0 := Blaster.int_lt_zero_of_nlt_lt_zero a N h (← mkOfDecideEqProof (N < 0)) true)` to hypothesisMap
          - add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_zero a
                              (Blaster.int_lt_zero_of_nlt_lt_zero a N h (← mkOfDecideEqProof (N < 0)) true))` to hypothesisMap
          - add `¬ (0 < a) := Blaster.int_not_lt_of_lt a 0
                              (Blaster.int_lt_zero_of_nlt_lt_zero a N h (← mkOfDecideEqProof (N < 0)) true))` to hypothesisMap

     - When `e := ¬ (¬ a)`
         - add `a := Blaster.not_not_cancel a h` to hypothesisMap

     - When `e := true = e`
         - add `¬ (false = e) := Blaster.not_false_eq_of_true_eq e h` to hypothesisMap

     - When `e := false = e`
         - add `¬ (true = e) := Blaster.not_true_eq_of_false_eq e h` to hypothesisMap

     NOTE: This function need to be in sync with optimizeAdvancedNot
-/
@[always_inline, inline]
def addNotPropFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some ne := propNot? e then
    if let some (r, op2, boolLit) ← notEqSimp? ne then
      let proofOp ← if boolLit then mkBlaster_false_eq_of_not_true_eq else mkBlaster_true_eq_of_not_false_eq
      let proof ← mkApp2Expr proofOp op2 h
      updateHypMap r proof nextCtxId

    if let some (Expr.const ``Nat _, _inst, op1, op2) := lt? ne then
      if let some 0 := isNatValue? op1 then
        -- case : e := ¬ (0 < a) ∧ Type(a) = Nat
        let eqFact ← mkNatEqExpr op1 op2
        let eq_proof ← mkApp2Expr (← mkNat_zero_eq_of_not_zero_lt) op2 h
        updateHypMap eqFact eq_proof nextCtxId
      if let some n := isNatValue? op2 then
        unless n == 0 do
          -- case : e := ¬ (a < N) ∧ Type(a) = Nat ∧ N ≠ 0
          let zeroNat ← mkNatLitExpr 0
          let ltFact ← mkNatLtExpr zeroNat op1
          let notOp ← mkPropNotOp
          let neqHyp ← mkAppExpr notOp (← mkNatEqExpr zeroNat op2)
          let neqHyp_proof ← mkOfDecideEqProof neqHyp true
          let lt_proof ← mkApp4Expr (← mkNat_zero_lt_of_not_lt_neq) op1 op2 h neqHyp_proof
          -- add `0 < a := Blaster.nat_zero_lt_of_not_lt_neq a N h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
          updateHypMap ltFact lt_proof nextCtxId
          let neqFact ← mkAppExpr notOp (← mkNatEqExpr zeroNat op1)
          let neq_proof ← mkApp2Expr (← mkNat_not_zero_eq_of_zero_lt) op1 lt_proof
          -- add `¬ (0 = a) := Blaster.nat_not_zero_eq_of_zero_lt a ...` to hypothesisMap
          updateHypMap neqFact neq_proof nextCtxId

    if let some (Expr.const ``Nat _, op1, op2) := eq? ne then
      if let some 0 := isNatValue? op1 then
        -- case : e := ¬ (0 = a) ∧ Type(a) = Nat
        let ltFact ← mkNatLtExpr op1 op2
        let lt_proof ← mkApp2Expr (← mkNat_zero_lt_of_not_zero_eq) op2 h
        updateHypMap ltFact lt_proof nextCtxId

    if let some (Expr.const ``Int _, _inst, op1, op2) := lt? ne then
      if let some n := isIntValue? op2 then
        unless n ≤ 0 do
          -- case : e := ¬ (a < N) ∧ Type(a) = Int ∧ N > 0
          let zeroInt ← mkIntLitExpr 0
          let ltFact ← mkIntLtExpr zeroInt op1
          let ltHyp ← mkIntLtExpr zeroInt op2
          let ltHyp_proof ← mkOfDecideEqProof ltHyp true
          let lt_proof ← mkApp4Expr (← mkInt_zero_lt_of_nlt_zero_lt) op1 op2 h ltHyp_proof
          -- add `0 < a := Blaster.int_zero_lt_of_nlt_zero_lt a N h (← mkOfDecideEqProof (0 < N)) true)` to hypothesisMap
          updateHypMap ltFact lt_proof nextCtxId
          let notOp ← mkPropNotOp
          let neqFact ← mkAppExpr notOp (← mkIntEqExpr zeroInt op1)
          let neq_proof ← mkApp2Expr (← mkInt_not_zero_eq_of_zero_lt) op1 lt_proof
          -- add `¬ (0 = a) := Blaster.int_not_zero_eq_of_zero_lt a ...` to hypothesisMap
          updateHypMap neqFact neq_proof nextCtxId
          let nltFact ← mkAppExpr notOp (← mkIntLtExpr op1 zeroInt)
          let nlt_proof ← mkApp3Expr (← mkInt_not_lt_of_lt) zeroInt op1 lt_proof
          -- add `¬ (a < 0) := Blaster.int_not_lt_of_lt 0 a ...` to hypothesisMap
          updateHypMap nltFact nlt_proof nextCtxId
      if let some n := isIntValue? op1 then
        unless n ≥ 0 do
          -- case : e := ¬ (N < a) ∧ Type(a) = Int ∧ N < 0
          let zeroInt ← mkIntLitExpr 0
          let ltFact ← mkIntLtExpr op2 zeroInt
          let ltHyp ← mkIntLtExpr op1 zeroInt
          let ltHyp_proof ← mkOfDecideEqProof ltHyp true
          let lt_proof ← mkApp4Expr (← mkInt_lt_zero_of_nlt_lt_zero) op2 op1 h ltHyp_proof
          -- add `a < 0 := Blaster.int_lt_zero_of_nlt_lt_zero a N h (← mkOfDecideEqProof (N < 0)) true)` to hypothesisMap
          updateHypMap ltFact lt_proof nextCtxId
          let notOp ← mkPropNotOp
          let neqFact ← mkAppExpr notOp (← mkIntEqExpr zeroInt op2)
          let neq_proof ← mkApp2Expr (← mkInt_not_zero_eq_of_lt_zero) op2 lt_proof
          -- add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_zero a ...` to hypothesisMap
          updateHypMap neqFact neq_proof nextCtxId
          let nltFact ← mkAppExpr notOp (← mkIntLtExpr zeroInt op2)
          let nlt_proof ← mkApp3Expr (← mkInt_not_lt_of_lt) op2 zeroInt lt_proof
          -- add `¬ (0 < a) := Blaster.int_not_lt_of_lt a 0 ...` to hypothesisMap
          updateHypMap nltFact nlt_proof nextCtxId

    if let some ne' := propNot? ne then
       -- case : e := ¬ (¬ e)
       let not_proof ← mkApp2Expr (← mkBlaster_not_not_cancel) ne' h
       updateHypMap ne' not_proof nextCtxId

  if let some (Expr.const ``Bool _, op1, op2) := eq? e then
    if let some b := isBoolValue? op1 then
      let notOp ← mkPropNotOp
      if b then
        -- case : e := true = e
        let notFact ← mkAppExpr notOp (← mkEqBool op2 false)
        let not_proof ← mkApp2Expr (← mkBlaster_not_false_eq_of_true_eq) e h
        -- add `¬ (false = e) := Blaster_not_false_eq_of_true_eq e h` to hypothesisMap
        updateHypMap notFact not_proof nextCtxId
      else
        -- case : e := false = e
        let notFact ← mkAppExpr notOp (← mkEqBool op2 true)
        let not_proof ← mkApp2Expr (← mkBlaster_not_true_eq_of_false_eq) e h
        -- add `¬ (true = e) := Blaster.not_true_eq_of_false_eq e h` to hypothesisMap
        updateHypMap notFact not_proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := a < b ∧ Type(a) = Int`

        - add `¬ (b < a) := Blaster.int_not_lt_of_lt a b h` to hypothesisMap

        - When `a <ₒ b`
            - add `¬ (a = b) := Blaster.int_not_eq_of_lt_left a b h` to hypothesisMap

        - Otherwise
            - add `¬ (b = a) := Blaster.int_not_eq_of_lt_left_sym a b h` to hypothesisMap

     - When `e := N < a ∧ Type(a) = Int ∧ N > 0`
          - add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_zero_lt N a h (← mkOfDecideEqProof (0 < N) true)` to hypothesisMap
          - add `0 < a := Int.lt_trans 0 N a (← mkOfDecideEqProof (0 < N) true) h` to hypothesisMap
          - add `¬ (a < 0) := Blaster.int_not_lt_of_lt 0 a (Int.lt_trans 0 N a (← mkOfDecideEqProof (0 < N) true) h)` to hypothesisMap

     - When `e := a < N ∧ Type(a) = Int ∧ N < 0`
          - add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_lt_zero a N h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
          - add `a < 0 := Int.lt_trans a N 0 h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
          - add `¬ (0 < a) := Blaster.int_not_lt_of_lt a 0 (Int.lt_trans a N 0 h (← mkOfDecideEqProof (N < 0) true))` to hypothesisMap

-/
@[always_inline, inline]
def addRelIntFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (Expr.const ``Int _, _inst, op1, op2) := lt? e then
    -- case : e := a < b ∧ Type(a) = Int
    let lt_proof ← mkApp3Expr (← mkInt_not_lt_of_lt) op1 op2 h
    let ltExpr ← mkIntLtExpr op2 op1
    let notOp ← mkPropNotOp
    -- add `¬ (b < a) := Blaster.int_not_lt_of_lt a b h` to hypothesisMap
    updateHypMap (← mkAppExpr notOp ltExpr) lt_proof nextCtxId
    let (op1', _) ← reorderEq #[op1, op2]
    if exprEq op1' op1 then
      let neq_proof ← mkApp3Expr (← mkInt_not_eq_of_lt_left) op1 op2 h
      let eqExpr ← mkIntEqExpr op1 op2
      -- add `¬ (a = b) := Blaster.int_not_eq_of_lt_left a b h` to hypothesisMap
      updateHypMap (← mkAppExpr notOp eqExpr) neq_proof nextCtxId
    else
      let neq_proof ← mkApp3Expr (← mkInt_not_eq_of_lt_left_sym) op1 op2 h
      let eqExpr ← mkIntEqExpr op2 op1
      -- add `¬ (b = a) := Blaster.int_not_eq_of_lt_left_sym a b h` to hypothesisMap
      updateHypMap (← mkAppExpr notOp eqExpr) neq_proof nextCtxId
    if let some n1 := isIntValue? op1 then
      unless n1 ≤ 0 do
       -- case : e := N < a ∧ Type(a) = Int ∧ N > 0
       let zeroInt ← mkIntLitExpr 0
       let ltHyp ← mkIntLtExpr zeroInt op1
       let neqFact ← mkAppExpr notOp (← mkIntEqExpr zeroInt op2)
       let ltHyp_proof ← mkOfDecideEqProof ltHyp true
       let neq_proof ← mkApp4Expr (← mkInt_not_zero_eq_of_lt_zero_lt) op1 op2 h ltHyp_proof
       -- add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_zero_lt N a h (← mkOfDecideEqProof (0 < N) true)` to hypothesisMap
       updateHypMap neqFact neq_proof nextCtxId
       let ltFact ← mkIntLtExpr zeroInt op2
       let lt_proof ← mkApp5Expr (← mkInt_lt_trans) zeroInt op1 op2 ltHyp_proof h
       -- add `0 < a := Int.lt_trans 0 N a (← mkOfDecideEqProof (0 < N) true) h` to hypothesisMap
       updateHypMap ltFact lt_proof nextCtxId
       let nlt_proof ← mkApp3Expr (← mkInt_not_lt_of_lt) zeroInt op2 lt_proof
       let nltFact ← mkAppExpr notOp (← mkIntLtExpr op2 zeroInt)
       -- add `¬ (a < 0) := Blaster.int_not_lt_of_lt 0 a (Int.lt_trans 0 N a (← mkOfDecideEqProof (0 < N) true) h)` to hypothesisMap
       updateHypMap nltFact nlt_proof nextCtxId
    if let some n2 := isIntValue? op2 then
      unless n2 ≥ 0 do
        -- case : e := a < N ∧ Type(a) = Int ∧ N < 0
        let zeroInt ← mkIntLitExpr 0
        let ltHyp ← mkIntLtExpr op2 zeroInt
        let ltHyp_proof ← mkOfDecideEqProof ltHyp true
        let neqFact ← mkAppExpr notOp (← mkIntEqExpr zeroInt op1)
        let neq_proof ← mkApp4Expr (← mkInt_not_zero_eq_of_lt_lt_zero) op1 op2 h ltHyp_proof
        -- add `¬ (0 = a) := Blaster.int_not_zero_eq_of_lt_lt_zero a N h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
        updateHypMap neqFact neq_proof nextCtxId
        let ltFact ← mkIntLtExpr op1 zeroInt
        let lt_proof ← mkApp5Expr (← mkInt_lt_trans) op1 op2 zeroInt h ltHyp_proof
        -- add `a < 0 := Int.lt_trans a N 0 h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
        updateHypMap ltFact lt_proof nextCtxId
        let nlt_proof ← mkApp3Expr (← mkInt_not_lt_of_lt) op1 zeroInt lt_proof
        let nltFact ← mkAppExpr notOp (← mkIntLtExpr zeroInt op1)
        -- add `¬ (0 < a) := Blaster.int_not_lt_of_lt a 0 (Int.lt_trans a N 0 h (← mkOfDecideEqProof (N < 0) true))` to hypothesisMap
        updateHypMap nltFact nlt_proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := a = b ∧ Type(a) = Int`
            - add `¬ (a < b) := Blaster.int_not_lt_left_of_eq a b h` to hypothesisMap
            - add `¬ (b < a) := Blaster.int_not_lt_right_of_eq a b h` to hypothesisMap

     - When `e := N = a ∧ Type(a) = Int ∧ N ≠ 0`
         - add `¬ (0 = a) := Blaster.int_not_zero_eq_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap

         - When `N > 0`
             - add `0 < a := Blaster.int_zero_lt_of_eq_zero_lt N a h (← mkOfDecideEqProof (0 < N) true)` to hypothesisMap

         - Otherwise
             - add `a < 0 := Blaster.int_lt_zero_of_eq_lt_zero N a h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
-/
@[always_inline, inline]
def addEqIntFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (Expr.const ``Int _, op1, op2) := eq? e then
    -- case : e := a = b ∧ Type(a) = Int
    let ltExpr1 ← mkIntLtExpr op1 op2
    let ltExpr2 ← mkIntLtExpr op2 op1
    let notOp ← mkPropNotOp
    let neq_proof1 ← mkApp3Expr (← mkInt_not_lt_left_of_eq) op1 op2 h
    let neq_proof2 ← mkApp3Expr (← mkInt_not_lt_right_of_eq) op1 op2 h
    -- add `¬ (a < b) := Blaster.int_not_lt_left_of_eq a b h` to hypothesisMap
    -- add `¬ (b < a) := Blaster.int_not_lt_right_of_eq a b h` to hypothesisMap
    updateHypMap (← mkAppExpr notOp ltExpr1) neq_proof1 nextCtxId
    updateHypMap (← mkAppExpr notOp ltExpr2) neq_proof2 nextCtxId
    if let some n := isIntValue? op1 then
     -- case : e := N = a ∧ Type(a) = Int ∧ N ≠ 0`
     unless n == 0 do
      let zeroInt ← mkIntLitExpr 0
      let neqZero ← mkAppExpr notOp (← mkIntEqExpr zeroInt op1)
      let neq_proof ← mkApp4Expr (← mkInt_not_zero_eq_of_eq_neq) op1 op2 h (← mkOfDecideEqProof neqZero true)
      let eqExpr ← mkIntEqExpr zeroInt op2
      -- add `¬ (0 = a) := Blaster.int_not_zero_eq_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
      updateHypMap (← mkAppExpr notOp eqExpr) neq_proof nextCtxId
      if n > 0 then
        let ltHyp ← mkIntLtExpr zeroInt op1
        let ltFact ← mkIntLtExpr zeroInt op2
        let lt_proof ← mkApp4Expr (← mkInt_zero_lt_of_eq_zero_lt) op1 op2 h (← mkOfDecideEqProof ltHyp true)
        -- add `0 < a := Blaster.int_zero_lt_of_eq_zero_lt N a h (← mkOfDecideEqProof (0 < N) true)` to hypothesisMap
        updateHypMap ltFact lt_proof nextCtxId
      else
        let ltHyp ← mkIntLtExpr op1 zeroInt
        let ltFact ← mkIntLtExpr op2 zeroInt
        let lt_proof ← mkApp4Expr (← mkInt_lt_zero_of_eq_lt_zero) op1 op2 h (← mkOfDecideEqProof ltHyp true)
        -- add `a < 0 := Blaster.int_lt_zero_of_eq_lt_zero N a h (← mkOfDecideEqProof (N < 0) true)` to hypothesisMap
        updateHypMap ltFact lt_proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := a < b ∧ Type(a) = Nat`
        - add `¬ (b < a) := Blaster.nat_not_lt_of_lt a b h` to hypothesisMap
        - add `¬ (0 = b) := Blaster.nat_not_zero_eq_of_lt a b h` to hypothesisMap
        - add `0 < b := Blaster.nat_zero_lt_of_lt a b h` to hypothesisMap

        - When `a <ₒ b`
            - add `¬ (a = b) := Blaster.nat_not_eq_of_lt_left a b h` to hypothesisMap
        - Otherwise
            - add `¬ (b = a) := Blaster.nat_not_eq_of_lt_left_sym a b h` to hypothesisMap
-/
@[always_inline, inline]
def addRelNatFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (Expr.const ``Nat _, _inst, op1, op2) := lt? e then
    -- case : e := a < b ∧ Type(a) = Nat
    let nlt_proof ← mkApp3Expr (← mkNat_not_lt_of_lt) op1 op2 h
    let notOp ← mkPropNotOp
    let nltFact ← mkAppExpr notOp (← mkNatLtExpr op2 op1)
    -- add `¬ (b < a) := Blaster.nat_not_lt_of_lt a b h` to hypothesisMap
    updateHypMap nltFact nlt_proof nextCtxId
    let zeroNat ← mkNatLitExpr 0
    let neqFact ← mkAppExpr notOp (← mkNatEqExpr zeroNat op2)
    let neq_proof ← mkApp3Expr (← mkNat_not_zero_eq_of_lt) op1 op2 h
    -- add `¬ (0 = b) := Blaster.nat_not_zero_eq_of_lt a b h` to hypothesisMap
    updateHypMap neqFact neq_proof nextCtxId
    let ltFact ← mkNatLtExpr zeroNat op2
    let lt_proof ← mkApp3Expr (← mkNat_zero_lt_of_lt) op1 op2 h
    -- add `0 < b := Blaster.nat_zero_lt_of_lt a b h` to hypothesisMap
    updateHypMap ltFact lt_proof nextCtxId
    let (op1', _) ← reorderEq #[op1, op2]
    if exprEq op1' op1 then
      let neqFact ← mkAppExpr notOp (← mkNatEqExpr op1 op2)
      let neq_proof ← mkApp3Expr (← mkNat_not_eq_of_lt_left) op1 op2 h
      -- add `¬ (a = b) := Blaster.nat_not_eq_of_lt_left a b h` to hypothesisMap
      updateHypMap neqFact neq_proof nextCtxId
    else
      let neqFact ← mkAppExpr notOp (← mkNatEqExpr op2 op1)
      let neq_proof ← mkApp3Expr (← mkNat_not_eq_of_lt_left_sym) op1 op2 h
      -- add `¬ (b = a) := Blaster.nat_not_eq_of_lt_left_sym a b h` to hypothesisMap
      updateHypMap neqFact neq_proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := a = b ∧ Type(a) = Nat`
            - add `¬ (a < b) := Blaster.nat_not_lt_left_of_eq a b h` to hypothesisMap
            - add `¬ (b < a) := Blaster.nat_not_lt_right_of_eq a b h` to hypothesisMap

     - When `e := N = a ∧ Type(a) = Nat ∧ N ≠ 0`
         - add `¬ (0 = a) := Blaster.nat_not_zero_eq_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
         - add `0 < a := Blaster.nat_zero_lt_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
-/
@[always_inline, inline]
def addEqNatFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (Expr.const ``Nat _, op1, op2) := eq? e then
    -- case : e := a = b ∧ Type(a) = Nat
    let notOp ← mkPropNotOp
    let nltFact1 ← mkAppExpr notOp (← mkNatLtExpr op1 op2)
    let nltFact2 ← mkAppExpr notOp (← mkNatLtExpr op2 op1)
    let nlt_proof1 ← mkApp3Expr (← mkNat_not_lt_left_of_eq) op1 op2 h
    let nlt_proof2 ← mkApp3Expr (← mkNat_not_lt_right_of_eq) op1 op2 h
    -- add `¬ (a < b) := Blaster.nat_not_lt_left_of_eq a b h` to hypothesisMap
    -- add `¬ (b < a) := Blaster.nat_not_lt_right_of_eq a b h` to hypothesisMap
    updateHypMap nltFact1 nlt_proof1 nextCtxId
    updateHypMap nltFact2 nlt_proof2 nextCtxId
    if let some n := isNatValue? op1 then
      unless n == 0 do
        -- case : e := N = a ∧ Type(a) = Nat ∧ N ≠ 0
        let zeroNat ← mkNatLitExpr 0
        let neqHyp ← mkAppExpr notOp (← mkNatEqExpr zeroNat op1)
        let neqHyp_proof ← mkOfDecideEqProof neqHyp true
        let neq_proof ← mkApp4Expr (← mkNat_not_zero_eq_of_eq_neq) op1 op2 h neqHyp_proof
        let neqFact ← mkAppExpr notOp (← mkNatEqExpr zeroNat op2)
        -- add `¬ (0 = a) := Blaster.nat_not_zero_eq_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
        updateHypMap neqFact neq_proof nextCtxId
        let ltFact ← mkNatLtExpr zeroNat op2
        let lt_proof ← mkApp4Expr (← mkNat_zero_lt_of_eq_neq) op1 op2 h neqHyp_proof
        -- add `0 < a := Blaster.nat_zero_lt_of_eq_neq N a h (← mkOfDecideEqProof (¬ (0 = N)) true)` to hypothesisMap
        updateHypMap ltFact lt_proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := sif h : c then e1 else e2`
        - add `c → e1 := And.left (c → e1) (¬ c → e2) (Blaster.and_implies_from_dite e1 e2 c h)` to hypothesisMap
        - add `¬ c → e1 := And.right (c → e1) (¬ c → e2) (Blaster.and_implies_from_dite e1 e2 c h)` to hypothesisMap
     Assume that dite has already been normalized.
-/
@[always_inline, inline]
def addDitePropFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (_u, _sort, cond, e1, e2) := dite'? e then
    let e1' ← toImplies e1 cond
    let e2' ← toImplies e2 cond (isThen := false)
    let impProof ← mkApp4Expr (← mkBlaster_and_implies_from_dite) cond e1 e2 h
    let proof1 ← mkApp3Expr (← mkAndLeft) e1' e2' impProof
    let proof2 ← mkApp3Expr (← mkAndRight) e1' e2' impProof
    updateHypMap e1' proof1 nextCtxId
    updateHypMap e2' proof2 nextCtxId
    negFacts cond e2' proof2
  else return ()

  where
    negFacts (c imp proof : Expr) : TranslateEnvT Unit := do
      match eq? c with
      | some (_psort, Expr.const ``true _, e) =>
          -- case : c := ¬ (true = e) → b
          match imp with
          | Expr.forallE n _t b bi =>
               if b.hasLooseBVars then return ()
               else
                 let impNeg ← mkForallExpr n bi (← mkEqBool e false) b
                 -- add false = e → b := (Blaster.false_eq_imp_of_not_true_imp e b proof) to hypothesisMap
                 updateHypMap impNeg (← mkApp3Expr (← mkBlaster_false_eq_imp_of_not_true_imp) e b proof) nextCtxId
          | _ => return ()
      | _ => return ()

    toImplies (e : Expr) (c : Expr) (isThen := true) : TranslateEnvT Expr := do
       match e with
       | Expr.lam n t b bi => mkForallExpr n bi t b
       | _ =>
          let c ← if isThen then pure c else mkAppExpr (← mkPropNotOp) c
          let body ← mkAppExpr e (← mkBVarExpr 0)
          mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default c body

@[always_inline, inline]
def addEqRewriteInMap (e : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
 if let some (_psort, a, b) := eq? e then
    if !(isBoolCtor a) then
      match a, b with
      | Expr.fvar _, Expr.fvar _ => pure ()
      | Expr.lit _, _ => updateEqualityMap b a nextCtxId
      | _, Expr.lit _ => updateEqualityMap a b nextCtxId
      | Expr.fvar _, _ => updateEqualityMap a b nextCtxId
      | _, Expr.fvar _ => updateEqualityMap b a nextCtxId
      | _, _ =>
        if (← isCtorExpr a.getAppFn) then updateEqualityMap b a nextCtxId
        else if (← isCtorExpr b.getAppFn) then updateEqualityMap a b nextCtxId
        else pure ()

/-- Perform the following actions:
     Let hyps := (← get).optEnv.options.hypothesisContext
     Let hMap := hyps.hypothesisMap
      - When Type(e) = Prop:
         - let hMap' := hMap ∪ [ e := h | ¬ ∃ e := h' ∈ hMap ] ∪
                               [ e₁ := And.left e₁ e₂ h | e := e₁ ∧ e₂, ¬ ∃ e₁ := h' ∈ hMap ] ∪
                               [ e₂ := And.right e₁ e₂ h | e := e₁ ∧ e₂, ¬ ∃ e₂ := h' ∈ hMap ]

         - return (hMap' ≠ hMap, {hypothesisMap := hMap', equalityMap := default})
     Otherwise:
       - return (false, hyps)
    Note: flag isPropBody is used only for forall case
    TODO: UPDATE SPEC
-/
partial def addHypotheses
  (e : Expr) (h : Expr) (isPropBody := true) : TranslateEnvT (Option CtxScope) := do
  if (← isPropEnv e) && isPropBody then
    let s ← newCtx
    updateHypMap e h s.current
    visit [(e, h)] s.current
    return s
  else return none

  where

    @[always_inline, inline]
    addFacts (e : Expr) (fv : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
      addNotPropFacts e fv nextCtxId
      addDitePropFacts e fv nextCtxId
      addEqRewriteInMap e nextCtxId
      addRelIntFacts e fv nextCtxId
      addEqIntFacts e fv nextCtxId
      addRelNatFacts e fv nextCtxId
      addEqNatFacts e fv nextCtxId

    visit (es : List (Expr × Expr)) (nextCtxId : CtxId) : TranslateEnvT Unit := do
      match es with
      | [] => return ()
      | (e, fv) :: xs =>
        if let some (a, b) := propAnd? e then
            let proof1 ← mkApp3Expr (← mkAndLeft) a b fv
            let proof2 ← mkApp3Expr (← mkAndRight) a b fv
            -- add `a := And.left a b fv` to hypothesisMap
            -- add `b := And.right a b fv` to hypothesisMap
            updateHypMap a proof1 nextCtxId
            updateHypMap b proof2 nextCtxId
            visit ((a, proof1) :: (b, proof2) :: xs) nextCtxId
        if let some (a, b) := notPropOr? e then
          let notOp ← mkPropNotOp
          let notA ← mkAppExpr notOp a
          let notB ← mkAppExpr notOp b
          let not_proof ← mkApp3Expr (← mkBlaster_and_not_from_not_or) a b fv
          -- add : ¬ a := And.left (¬ a) (¬ b) (Blaster.and_not_from_not_or a b fv)` to hypothesisMap
          -- add : ¬ b := And.right (¬ a) (¬ b) (Blaster.and_not_from_not_or a b fv)` to hypothesisMap
          let left_proof ← mkApp3Expr (← mkAndLeft) notA notB not_proof
          let right_proof ← mkApp3Expr (← mkAndRight) notA notB not_proof
          updateHypMap notA left_proof nextCtxId
          updateHypMap notB right_proof nextCtxId
          visit ((notA, left_proof) :: (notB, right_proof) :: xs) nextCtxId
        else
          addFacts e fv nextCtxId
          visit xs nextCtxId

    @[always_inline, inline]
    notPropOr? (e : Expr) : Option (Expr × Expr) :=
      if let some ne := propNot? e then
         propOr? ne
      else none

/-- Given `e` and hypothesis map `h` perform the following:
      - When `e := p ∈ h`:
          - return `some p`
-/
@[always_inline, inline]
def inHypMap (e : Expr) : TranslateEnvT (Option Expr) := do
  if e.hasMVar then return none
  hypMapFind? e

/-- Given `e` and hypothesis map `h` perform the following:
     - When `e := ¬ a`
        - return `hypMapFind? a`
     - Otherwise:
       - return `hypMapFind? (¬ e)`
-/
@[always_inline, inline]
def notInHypMap (e : Expr) : TranslateEnvT (Option Expr) := do
  if e.hasMVar then return none
  if let some ne := propNot? e
  then hypMapFind? ne
  else hypMapFind? (← mkAppExpr (← mkPropNotOp) e)


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
      - return `some (S1 "<" S2)` when `op1 := S1 ∧ op2 := S2 ∧ Type(op1) = String`
    NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
    Otheriwse `none`.
-/
def cstLT? (op1 : Expr) (op2 : Expr) : Option Bool :=
 match op1 with
 | Expr.lit (Literal.natVal n1) =>
    if let Expr.lit (Literal.natVal n2) := op2
    then some $ Nat.blt n1 n2
    else none
 | Expr.lit (Literal.strVal s1) =>
    if let Expr.lit (Literal.strVal s2) := op2
    then some $ s1 < s2
    else none
 | _ =>
   if let some n1 := isIntValue? op1 then
     if let some n2 := isIntValue? op2
     then some $ n1 < n2
     else none
   else none


/-- Given `op1` and `op2` corresponding to the operands for `LT.le`:
      - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
      - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
      - return `some (S1 "≤" S2)` when `op1 := S1 ∧ op2 := S2 ∧ Type(op1) = String`
    NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
    Otheriwse `none`.
-/
def cstLE? (op1 : Expr) (op2 : Expr) : Option Bool :=
 match op1 with
 | Expr.lit (Literal.natVal n1) =>
    if let Expr.lit (Literal.natVal n2) := op2
    then some $ Nat.ble n1 n2
    else none
 | Expr.lit (Literal.strVal s1) =>
    if let Expr.lit (Literal.strVal s2) := op2
    then some $ s1 ≤ s2
    else none
 | _ =>
   if let some n1 := isIntValue? op1 then
     if let some n2 := isIntValue? op2
     then some $ n1 ≤ n2
     else none
   else none

inductive BackProofStack where
  | WaitAndLeft (e a b : Expr)
  | WaitAndRight (e a b p : Expr)
  | WaitOrLeft (e a b : Expr)
  | WaitOrRight (e a b : Expr)
deriving Repr

abbrev BackProofCache := HashMap PtrExpr (Option Expr)

private unsafe def backwardProofAux (expectedProof : Expr) : TranslateEnvT (Option Expr) :=
  let rec go (res : Sum Expr (Option Expr)) (stk : Array BackProofStack) (cache : BackProofCache) : TranslateEnvT (Option Expr) := do
    match res with
    | Sum.inr none =>
        if stk.usize > 0 then
          let topIdx := stk.usize - 1
          let next := stk.uget topIdx lcProof
          match next with
          | .WaitOrLeft e a b =>
               -- left not in hyp try right
               let stk := stk.uset topIdx (.WaitOrRight e a b) lcProof
               go (Sum.inl b) stk cache
          | _ => return none -- no proof found
        else return none -- no proof found
    | Sum.inr res@(some p) =>
        if stk.usize > 0 then
          let topIdx := stk.usize - 1
          let next := stk.uget topIdx lcProof
          match next with
          | .WaitAndLeft e a b =>
               let stk := stk.uset topIdx (.WaitAndRight e a b p) lcProof
               go (Sum.inl b) stk cache
          | .WaitAndRight e a b pa =>
               let andProof ← mkApp4Expr (← mkAndIntro) a b pa p
               go (Sum.inr (some andProof)) stk.pop (cache.insert e andProof)
          | .WaitOrLeft e a b =>
               let orProof ← mkApp3Expr (← mkOrInl) a b p
               go (Sum.inr (some orProof)) stk.pop (cache.insert e orProof)
          | .WaitOrRight e a b =>
               let orProof ← mkApp3Expr (← mkOrInr) a b p
               go (Sum.inr (some orProof)) stk.pop (cache.insert e orProof)
        else return res
    | Sum.inl cur =>
       if let some p := cache.get? cur then
         go (Sum.inr p) stk cache
       else if let p@(some r) ← atomicProof? cur then
         go (Sum.inr p) stk (cache.insert cur r)
       else if let p@(some h) ← inHypMap cur then
         go (Sum.inr p) stk (cache.insert cur h)
       else if let some (a, b) := propAnd? cur then
         let stk := stk.push (.WaitAndLeft cur a b)
         go (Sum.inl a) stk cache
       else if let some (a, b) := propOr? cur then
         let stk := stk.push (.WaitOrLeft cur a b)
         go (Sum.inl a) stk cache
       else go (Sum.inr none) stk (cache.insert cur none)
  go (Sum.inl expectedProof) (Array.emptyWithCapacity (expectedProof.approxDepth.toNat + 16)) (HashMap.emptyWithCapacity 64)

 where
   atomicProof? (p : Expr) : TranslateEnvT (Option Expr) := do
     if isTrueExpr p then return ← mkTrueIntro
     else if isFalseExpr p then return ← mkNotFalse
     else if let some r ← isReflEq? p then return r
     else if let some r ← isDecidableLt? p then return r
     else isDecidableLe? p

   /-- Perform the following:
        - return some `Eq.refl a` when `p := a = a`.
        - return some `Eq.refl Decidable.decide True` when `p := Decidable.decide True = true`
        - return some `Eq.refl Decidable.decide True` when `p := true = Decidable.decide True`
   -/
   @[always_inline, inline]
   isReflEq? (p : Expr) : TranslateEnvT (Option Expr) := do
     match eq? p with
     | some (psort, e1, e2) =>
         let lvl ← getLevelEnv psort
          if exprEq e1 e2 then mkApp2Expr (← mkEqRefl [lvl]) psort e1
          else if isBoolTrue e1 && isDecideTrue e2 then mkApp2Expr (← mkEqRefl [lvl]) psort e2
          else if isBoolTrue e2 && isDecideTrue e1 then mkApp2Expr (← mkEqRefl [lvl]) psort e1
          else return none
     | _ => return none

   /-- Generate decidable proof only when one of the following conditions is satisfied:
         - p := N1 < N2 ∧ Type(N1) ∈ [Int, Nat]
         - p := S1 < S2 ∧ Type(S1) = String
   -/
   @[always_inline, inline]
   isDecidableLt? (p : Expr) : TranslateEnvT (Option Expr) := do
    if let some (_psort, _pinst, e1, e2) := lt? p then
      if let some true := cstLT? e1 e2
      then mkOfDecideEqProof? p true
      else return none
    else return none

   /-- Generate decidable proof only when one of the following conditions is satisfied:
         - p := N1 ≤ N2 ∧ Type(N1) ∈ [Int, Nat]
         - p := S1 ≤ S2 ∧ Type(S1) = String
   -/
   @[always_inline, inline]
   isDecidableLe? (p : Expr) : TranslateEnvT (Option Expr) := do
    if let some (_psort, _pinst, e1, e2) := le? p then
      if let some true := cstLE? e1 e2
      then mkOfDecideEqProof? p true
      else return none
    else return none

/-- Given expected proof `p` and actual proof `a` perform backward proof reconstruction w.r.t. hypothesis map -/
def backwardProof (p a : Expr) : TranslateEnvT Expr := do
  if exprEq p a -- case for trivial proof (e.g., Eq.refl)
  then return a
  else
   let a' ← inferTypeEnv a
   if exprEq a' p then return a
   else if ← isLambdaEq p a' then return a
   else if let some r ← unsafe backwardProofAux p then return r
   else if let some r ← isDecidable p then return r
   else
     -- Add sorry proof for now when we can't perform proof reconstruction
     hashcons (← mkSorry p false)

 where

   isDecidable (p : Expr) : TranslateEnvT (Option Expr) := do
     if p.hasFVar then return none
     else mkOfDecideEqProof? p true

   /-- Return `true` only when the following conditions are satisfied
        - p := (fun x₁ ... xₙ => P x₁ ... xₙ) a₁ ... aₙ
        - a := P a₁ ... aₙ
   -/
   isLambdaEq (p a : Expr) : TranslateEnvT Bool := do
     let f := p.getAppFn'
     match f with
     | Expr.lam .. => return exprEq (← betaLambdaShared f p.getAppArgs) a
     | _ => return false

end Blaster.Optimize
