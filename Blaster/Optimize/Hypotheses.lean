import Lean
import Blaster.Optimize.Lemmas
import Blaster.Optimize.Rewriting.OptimizePropNot

open Lean Meta

namespace Blaster.Optimize

abbrev UpdatedHypContext := Bool × HypothesisContext
-- flag Bool is set to true only when the context has been updated.

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_nat ← mkNatLitExpr 0
     let zero_lt ← mkNatLtExpr zero_nat e
     return hyps.contains zero_lt

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_nat ← mkNatLitExpr 0
     let zero_eq ← mkNatEqExpr zero_nat e
     return hyps.contains zero_eq

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_nat ← mkNatLitExpr 0
     let zero_lt ← mkNatLtExpr zero_nat e
     if hyps.contains zero_lt then return true
     let zero_eq ← mkNatEqExpr zero_nat e
     return hyps.contains (mkApp (← mkPropNotOp) zero_eq)

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let lt_zero ← mkIntLtExpr e zero_int
     return hyps.contains lt_zero

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     return hyps.contains zero_lt

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     if hyps.contains zero_lt then return true
     let lt_zero ← mkIntLtExpr e zero_int
     if hyps.contains lt_zero then return true
     let zero_eq ← mkIntEqExpr zero_int e
     return hyps.contains (mkApp (← mkPropNotOp) zero_eq)

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let zero_lt ← mkIntLtExpr zero_int e
     if hyps.contains zero_lt then return true
     let zero_eq ← mkIntEqExpr zero_int e
     if hyps.contains zero_eq then return true
     let lt_zero ← mkIntLtExpr e zero_int
     return hyps.contains (mkApp (← mkPropNotOp) lt_zero)

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
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     let zero_int ← mkIntLitExpr (Int.ofNat 0)
     let lt_zero ← mkIntLtExpr e zero_int
     if hyps.contains lt_zero then return true
     let zero_eq ← mkIntEqExpr zero_int e
     if hyps.contains zero_eq then return true
     let zero_lt ← mkIntLtExpr zero_int e
     return hyps.contains (mkApp (← mkPropNotOp) zero_lt)


/-- Perform the following actions:
     Let hyps := (← get).optEnv.options.hypothesisContext
     Let hMap := hyps.hypothesisMap
      - When Type(e) = Prop:
         - let hMap' := hMap ∪ [ e := h | ¬ ∃ e := h' ∈ hMap ] ∪
                               [ e₁ := Blaster.and_left e₁ e₂ h | e := e₁ ∧ e₂, ¬ ∃ e₁ := h' ∈ hMap ] ∪
                               [ e₂ := Blaster.and_right e₁ e₂ h | e := e₁ ∧ e₂, ¬ ∃ e₂ := h' ∈ hMap ]

         - return (hMap' ≠ hMap, {hypothesisMap := hMap', equalityMap := default})
     Otherwise:
       - return (false, hyps)
    Note: flag isNotPropBody is set only when a forall body is not of type Prop.
-/
@[inline] partial def addHypotheses
  (e : Expr) (h : Expr) (isNotPropBody := false) : TranslateEnvT UpdatedHypContext := do
  let hyps := (← get).optEnv.hypothesisContext
  if (← isPropEnv e) && !isNotPropBody then
    visit [(e, h)] (updateHypContext (false, hyps) e h)
  else return (false, hyps)

  where
    @[always_inline, inline]
    updateHypMap
      (h : Bool × HypothesisMap) (e : Expr) (fv : Expr) : Bool × HypothesisMap :=
        match h.2.get? e with
        | none => (true, h.2.insert e fv)
        | _ => h

    @[always_inline, inline]
    updateHypContext (h : UpdatedHypContext) (e : Expr) (fv : Expr) : UpdatedHypContext :=
      let (b, hyps) := updateHypMap (h.1, h.2.1) e fv
      (b, {h.2 with hypothesisMap := hyps})

    visit (es : List (Expr × Expr)) (h : UpdatedHypContext) : TranslateEnvT UpdatedHypContext := do
      match es with
      | [] => return h
      | (e, fv) :: xs =>
        match (e.and?) with
        | some (a, b) =>
            let proof1 := mkApp3 (← mkBlasterAndLeft) a b fv
            let proof2 := mkApp3 (← mkBlasterAndRight) a b fv
            visit ((a, proof1) :: (b, proof2) :: xs) ((updateHypContext (updateHypContext h a proof1) b proof2))
        | none => visit xs h


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
def inHypMap (e : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  if let some m := h.get? e then return some m
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
          if let some p := h.get? (mkApp (← mkPropNotOp) (← mkNatEqExpr op1 op2)) then
            return mkApp2 (← mkNat_zero_lt_of_not_zero_eq) op2 p
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
        if let some p := h.get? (← mkNatLtExpr op1 op2) then
           return mkApp3 (← mkNat_not_eq_of_lt_left) op1 op2 p
        else if let some p := h.get? (← mkNatLtExpr op2 op1) then
           return mkApp3 (← mkNat_not_eq_of_lt_right) op1 op2 p
        else match isNatValue? op1 with
             | some 0 =>
                if let some p := h.get? (← mkNatLtExpr op1 op2) then
                  return mkApp2 (← mkNat_not_zero_eq_of_zero_lt) op2 p
                else return none
             | _ => return none

    | Expr.const ``Int _ =>
        if let some p := h.get? (← mkIntLtExpr op1 op2) then
           return mkApp3 (← mkInt_not_eq_of_lt_left) op1 op2 p
        else if let some p := h.get? (← mkIntLtExpr op2 op1) then
           return mkApp3 (← mkInt_not_eq_of_lt_right) op1 op2 p
        else match isIntValue? op1 with
             | some 0 =>
                if let some p := h.get? (← mkIntLtExpr op2 op1) then
                  return mkApp2 (← mkInt_not_zero_eq_of_lt_zero) op2 p
                if let some p := h.get? (← mkIntLtExpr op1 op2) then
                  return mkApp2 (← mkInt_not_zero_eq_of_zero_lt) op2 p
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
          if let some p := h.get? (← mkNatEqExpr op1' op2') then
            if exprEq op1 op1'
            then return mkApp3 (← mkNat_not_lt_left_of_eq) op1 op2 p
            else return mkApp3 (← mkNat_not_lt_right_of_eq) op2 op1 p
          else if let some p := h.get? (← mkNatLtExpr op2 op1) then
            return mkApp3 (← mkNat_not_lt_of_lt) op2 op1 p
          else return none

     | Expr.const ``Int _ =>
          let (op1', op2') ← reorderEq #[op1, op2]
          if let some p := h.get? (← mkIntEqExpr op1' op2') then
            if exprEq op1 op1'
            then return mkApp3 (← mkInt_not_lt_left_of_eq) op1 op2 p
            else return mkApp3 (← mkInt_not_lt_right_of_eq) op2 op1 p
          else if let some p := h.get? (← mkIntLtExpr op2 op1) then
            return mkApp3 (← mkInt_not_lt_of_lt) op2 op1 p
          else return none
     | _ => return none

/-- Given `e` and hypothesis map `h` perform the following:
     - When `some p := inHypMap (← optimizeNot (¬ e)) h`
       - return `some p`
-/
@[always_inline, inline]
def notInHypMap (e : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  let not_e ← optimizeNot (← mkPropNotOp) (cacheResult := false) #[e]
  inHypMap not_e h

end Blaster.Optimize
