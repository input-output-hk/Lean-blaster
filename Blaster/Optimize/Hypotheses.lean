import Lean
import Blaster.Optimize.Lemmas
import Blaster.Optimize.Rewriting.OptimizePropNot

open Lean Meta Elab Blaster.Data.HashMap

namespace Blaster.Optimize

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
      - 0 < e := _ ∈ hypothesisContext.hypothesisMap; or
      - ¬ (0 = e) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def nonZeroNatInHyps (e : Expr) : TranslateEnvT Bool := do
 match isNatValue? e with
 | .some 0 => return false
 | .some _ => return true
 | .none   =>
     let zero_nat ← mkNatLitExpr 0
     let zero_lt ← mkNatLtExpr zero_nat e
     if ← hypMapContains zero_lt then return true
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
      - 0 < e := _ ∈ hypothesisContext.hypothesisMap; or
      - e < 0 := _ ∈ hypothesisContext.hypothesisMap; or
      - ¬ (0 = e) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def nonZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat 0) => return false
 | .some _          => return true
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     if ← hypMapContains zero_lt then return true
     let lt_zero ← mkIntLtExpr e zero_int
     if ← hypMapContains lt_zero then return true
     let zero_eq ← mkIntEqExpr zero_int e
     hypMapContains (← mkAppExpr (← mkPropNotOp) zero_eq)

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≥ 0
      - 0 < e := _ ∈ hypothesisContext.hypothesisMap; or
      - 0 = e := _ ∈ hypothesisContext.hypothesisMap; or
      - ¬ (e < 0) := _ ∈ hypothesisContext.hypothesisMap
-/
@[always_inline, inline]
def geqZeroIntInHyps (e : Expr) : TranslateEnvT Bool := do
 match isIntValue? e with
 | .some (.ofNat _) => return true
 | .some _          => return false
 | .none =>
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     if ← hypMapContains zero_lt then return true
     let zero_eq ← mkIntEqExpr zero_int e
     if ← hypMapContains zero_eq then return true
     let lt_zero ← mkIntLtExpr e zero_int
     hypMapContains (← mkAppExpr (← mkPropNotOp) lt_zero)

/-- Return `true` only when one of the following conditions is satisfied:
      - e := N ∧ N ≤ 0
      - e < 0 := _ ∈ hypothesisContext.hypothesisMap; or
      - 0 = e := _ ∈ hypothesisContext.hypothesisMap; or
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
     let lt_zero ← mkIntLtExpr e zero_int
     if ← hypMapContains lt_zero then return true
     let zero_eq ← mkIntEqExpr zero_int e
     if ← hypMapContains zero_eq then return true
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
-/
@[always_inline, inline]
def addNotPropFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some ne := propNot? e then
    if let some (r, op2, boolLit) ← notEqSimp? ne then
      let proofOp ← if boolLit then mkBlasterFalseEqNotTrueEq else mkBlasterTrueEqNotFalseEq
      let proof ← mkApp2Expr proofOp op2 h
      updateHypMap r proof nextCtxId

/-- Given proposition `e` referenced by hypothesis `h`, perform the following:
     - When `e := sif h : c then e1 else e2`
        - add `c → e1 := And.left (c → e1) (¬ c → e2) (Blaster.and_implies_from_dite_prop_cond e1 e2 c h)` to hypothesisMap
        - add `¬ c → e1 := And.right (c → e1) (¬ c → e2) (Blaster.and_implies_from_dite_prop_cond e1 e2 c h)` to hypothesisMap
     Assume that dite has already been normalized.
-/
@[always_inline, inline]
def addDitePropFacts (e : Expr) (h : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  if let some (_sort, cond, e1, e2) := dite'? e then
    let e1' ← toImplies e1 cond
    let e2' ← toImplies e2 cond (isThen := false)
    let impProof ← mkApp4Expr (← mkBlasterAndImpliesOfDite) cond e1 e2 h
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
          match imp with
          | Expr.forallE n _t b bi =>
               if b.hasLooseBVars then return ()
               else
                 let impNeg ← mkForallExpr n bi (← mkEqBool e false) b
                 updateHypMap impNeg (← mkApp3Expr (← mkBlasterFalseEqImpOfNotTrueImp) e b proof) nextCtxId
          | _ => return ()
      | _ => return ()

    negateExpr (c : Expr) : TranslateEnvT Expr := do
      optimizeAdvancedNot (← mkPropNotOp) (restart := false) #[c]

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

    visit (es : List (Expr × Expr)) (nextCtxId : CtxId) : TranslateEnvT Unit := do
      match es with
      | [] => return ()
      | (e, fv) :: xs =>
        if let some (a, b) := propAnd? e then
            let proof1 ← mkApp3Expr (← mkAndLeft) a b fv
            let proof2 ← mkApp3Expr (← mkAndRight) a b fv
            updateHypMap a proof1 nextCtxId
            updateHypMap b proof2 nextCtxId
            visit ((a, proof1) :: (b, proof2) :: xs) nextCtxId
        else
          addFacts e fv nextCtxId
          visit xs nextCtxId


/-- Given `e` and hypothesis map `h` perform the following:
      - When `e := p ∈ h`:
          - return `some p`

      - When `e := ¬ (a = b) ∧ Type(a) = Int ∧ a < b := p ∈ h
          - return `some Blaster.int_not_eq_of_lt_left a b p`

      - When `e := ¬ (a = b) ∧ Type(a) = Int ∧ b < a := p ∈ h
          - return `some Blaster.int_not_eq_of_lt_right a b p`

      - When `e := ¬ (0 = a) ∧ Type(a) = Int ∧ a < 0 := p ∈ h
          - return `some Blaster.int_not_zero_eq_of_lt_zero a p`

      - When `e := ¬ (0 = a) ∧ Type(a) = Int ∧ 0 < a := p ∈ h
          - return `some Blaster.int_not_zero_eq_of_zero_lt a p`

      - When `e := ¬ (a = b) ∧ Type(a) = Nat ∧ a < b := p ∈ h
          - return `some Blaster.nat_not_eq_of_lt_left a b p`

      - When `e := ¬ (a = b) ∧ Type(a) = Nat ∧ b < a := p ∈ h
          - return `some Blaster.nat_not_eq_of_lt_right a b p`

      - When `e := ¬ (0 = a) ∧ Type(a) = Nat ∧ 0 < a := p ∈ h
          - return `some Blaster.nat_not_zero_eq_of_zero_lt a p`

      - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ a = b := p ∈ h
          - return `some Blaster.int_not_lt_left_of_eq a b p`

      - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ b = a := p ∈ h
          - return `some Blaster.int_not_lt_right_of_eq b a p`

      - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ b < a := p ∈ h
          - return `some Blaster.int_not_lt_of_lt b a p`

      - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ a = b := p ∈ h
          - return `some Blaster.nat_not_lt_left_of_eq a b p`

      - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ b = a := p ∈ h
          - return `some Blaster.nat_not_lt_right_of_eq b a p`

      - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ b < a := p ∈ h
          - return `some Blaster.nat_not_lt_of_lt b a p`

     - When `e := 0 < a ∧ Type(a) = Nat ∧ ¬ 0 = a := p ∈ h
          - return `some Blaster.nat_zero_lt_of_not_zero_eq a p`

      - Otherwise:
          - return `none`

    Note that:
     - `a ≤ b` is normalized to `¬ (b < a)` when `Type(a) ∈ [Int, Nat]`
     - `0 = -a` is normalized to `0 = a when `Type(a) = Int`
-/
@[always_inline, inline]
def inHypMap (e : Expr) : TranslateEnvT (Option Expr) := do
  if e.hasMVar then return none
  if let some m ← hypMapFind? e then return some m
  if let some m ← notEqInHyp? e then return some m
  if let some m ← zeroNatLtInHyp? e then return some m
  notLtInHyp? e

  where

   /-- Perform the following:
         - When `e := 0 < a ∧ Type(a) = Nat ∧ ¬ 0 = a := p ∈ h
             - return `some Blaster.nat_zero_lt_of_not_zero_eq a p`
         - Otherwise:
             - return `none`
   -/
   @[always_inline, inline]
   zeroNatLtInHyp? (e : Expr) : TranslateEnvT (Option Expr) := do
     let some (Expr.const ``Nat _, _inst, op1, op2) := lt? e | return none
     match isNatValue? op1 with
     | some 0 =>
          if let some p ← hypMapFind? (← mkAppExpr (← mkPropNotOp) (← mkNatEqExpr op1 op2))
          then mkApp2Expr (← mkNat_zero_lt_of_not_zero_eq) op2 p
          else return none
     | _ => return none

   /-- Perform the following:
        - When `e := ¬ (a = b) ∧ Type(a) = Int ∧ a < b := p ∈ h
           - return `some Blaster.int_not_eq_of_lt_left a b p`

        - When `e := ¬ (a = b) ∧ Type(a) = Int ∧ b < a := p ∈ h
            - return `some Blaster.int_not_eq_of_lt_right a b p`

       - When `e := ¬ (0 = a) ∧ Type(a) = Int ∧ a < 0 := p ∈ h
           - return `some Blaster.int_not_zero_eq_of_lt_zero a p`

       - When `e := ¬ (0 = a) ∧ Type(a) = Int ∧ 0 < a := p ∈ h
           - return `some Blaster.int_not_zero_eq_of_zero_lt a p`

        - When `e := ¬ (a = b) ∧ Type(a) = Nat ∧ a < b := p ∈ h
           - return `some Blaster.nat_not_eq_of_lt_left a b p`

        - When `e := ¬ (a = b) ∧ Type(a) = Nat ∧ b < a := p ∈ h
           - return `some Blaster.nat_not_eq_of_lt_right a b p`

        - When `e := ¬ (0 = a) ∧ Type(a) = Nat ∧ 0 < a := p ∈ h
           - return `some Blaster.nat_not_zero_eq_of_zero_lt a p`


        - Otherwise:
            - return `none`
   -/
   @[always_inline, inline]
   notEqInHyp? (e : Expr) : TranslateEnvT (Option Expr) := do
    let some ne := propNot? e | return none
    let some (sort, op1, op2) := eq? ne | return none
    match sort with
    | Expr.const ``Nat _ =>
        if let some p ← hypMapFind? (← mkNatLtExpr op1 op2)
        then mkApp3Expr (← mkNat_not_eq_of_lt_left) op1 op2 p
        else if let some p ← hypMapFind? (← mkNatLtExpr op2 op1)
        then mkApp3Expr (← mkNat_not_eq_of_lt_right) op1 op2 p
        else match isNatValue? op1 with
             | some 0 =>
                if let some p ← hypMapFind? (← mkNatLtExpr op1 op2)
                then mkApp2Expr (← mkNat_not_zero_eq_of_zero_lt) op2 p
                else return none
             | _ => return none

    | Expr.const ``Int _ =>
        if let some p ← hypMapFind? (← mkIntLtExpr op1 op2)
        then mkApp3Expr (← mkInt_not_eq_of_lt_left) op1 op2 p
        else if let some p ← hypMapFind? (← mkIntLtExpr op2 op1)
        then mkApp3Expr (← mkInt_not_eq_of_lt_right) op1 op2 p
        else match isIntValue? op1 with
             | some 0 =>
                if let some p ← hypMapFind? (← mkIntLtExpr op2 op1)
                then mkApp2Expr (← mkInt_not_zero_eq_of_lt_zero) op2 p
                else if let some p ← hypMapFind? (← mkIntLtExpr op1 op2)
                then mkApp2Expr (← mkInt_not_zero_eq_of_zero_lt) op2 p
                else return none
             | _ => return none
    | _ => return none

   /-- Perform the following:
        - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ a = b := p ∈ h
            - return `some Blaster.int_not_lt_left_of_eq a b p`

        - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ b = a := p ∈ h
            - return `some Blaster.int_not_lt_right_of_eq b a p`

        - When `e := ¬ (a < b) ∧ Type(a) = Int ∧ b < a := p ∈ h
            - return `some Blaster.int_not_lt_of_lt b a p`

        - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ a = b := p ∈ h
            - return `some Blaster.nat_not_lt_left_of_eq a b p`

        - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ b = a := p ∈ h
            - return `some Blaster.nat_not_lt_right_of_eq b a p`

        - When `e := ¬ (a < b) ∧ Type(a) = Nat ∧ b < a := p ∈ h
            - return `some Blaster.nat_not_lt_of_lt b a p`

        - Otherwise:
            - return `none`
   -/
   notLtInHyp? (e : Expr) : TranslateEnvT (Option Expr) := do
     let some ne := propNot? e | return none
     let some (sort, _inst, op1, op2) := lt? ne | return none
     match sort with
     | Expr.const ``Nat _ =>
          let (op1', op2') ← reorderEq #[op1, op2]
          if let some p ← hypMapFind? (← mkNatEqExpr op1' op2') then
            if exprEq op1 op1'
            then mkApp3Expr (← mkNat_not_lt_left_of_eq) op1 op2 p
            else mkApp3Expr (← mkNat_not_lt_right_of_eq) op2 op1 p
          else if let some p ← hypMapFind? (← mkNatLtExpr op2 op1)
          then mkApp3Expr (← mkNat_not_lt_of_lt) op2 op1 p
          else return none

     | Expr.const ``Int _ =>
          let (op1', op2') ← reorderEq #[op1, op2]
          if let some p ← hypMapFind? (← mkIntEqExpr op1' op2') then
            if exprEq op1 op1'
            then mkApp3Expr (← mkInt_not_lt_left_of_eq) op1 op2 p
            else mkApp3Expr (← mkInt_not_lt_right_of_eq) op2 op1 p
          else if let some p ← hypMapFind? (← mkIntLtExpr op2 op1)
          then mkApp3Expr (← mkInt_not_lt_of_lt) op2 op1 p
          else return none
     | _ => return none

/-- Given `e` and hypothesis map `h` perform the following:
     - When `some p := inHypMap (← optimizeAdvancedNot (¬ e)) h`
       - return `some p`
-/
@[always_inline, inline]
def notInHypMap (e : Expr) : TranslateEnvT (Option Expr) := do
  if e.hasMVar then return none
  let not_e ← optimizeAdvancedNot (← mkPropNotOp) (restart := false) #[e]
  inHypMap not_e


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

   /-- Return some `Eq.refl a` only when p := a = a. -/
   @[always_inline, inline]
   isReflEq? (p : Expr) : TranslateEnvT (Option Expr) := do
     match eq? p with
     | some (psort, e1, e2) =>
          if exprEq e1 e2 then
            let lvl ← getLevelEnv psort
            mkApp2Expr (← mkEqRefl [lvl]) psort e1
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



/-- Given expected proof `p` perform backward proof reconstruction w.r.t. hypothesis map -/
def backwardProof (p : Expr) : TranslateEnvT Expr := do
  if let some r ← unsafe backwardProofAux p then return r
  -- Add sorry proof for now when we can't perform proof reconstruction
  hashcons (← mkSorry p false)


end Blaster.Optimize
