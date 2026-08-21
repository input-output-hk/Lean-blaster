import Lean
import Blaster.Optimize.Hypotheses

open Lean Meta
namespace Blaster.Optimize

/-- `@Eq.refl Bool true`, used as a defeq proof of a decidable condition `b = true`
    (e.g. `Nat.ble n1 n2 = true` or `decide (0 < n) = true`) when `b` reduces to `true`. -/
private def boolTrueRefl : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- `@Eq.refl Bool false`, the `false` counterpart of `boolTrueRefl`. -/
private def boolFalseRefl : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.false)

/-- Return `true` when `e` corresponds to the one nat literal. -/
def isOneNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 1 => true
  | _ => false

/-- Proof-returning companion to `geqZeroIntInHyps` for a non-literal `e`: when a hypothesis
    entailing `0 ≤ e` is in context (stored as `0 < e`, `0 = e`, or `¬ (e < 0)`), return a proof
    of the canonical `0 ≤ e`; otherwise `none`. -/
def geqZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkIntLitExpr (Int.ofNat 0)
 if let some p := hyps.get? (← mkIntLtExpr zero e) then
   return mkApp2 (mkConst ``Blaster.int_le_of_zero_lt) e p
 if let some p := hyps.get? (← mkIntEqExpr zero e) then
   return mkApp2 (mkConst ``Blaster.int_le_of_zero_eq) e p
 if let some p := hyps.get? (mkApp (← mkPropNotOp) (← mkIntLtExpr e zero)) then
   return mkApp2 (mkConst ``Blaster.int_le_of_not_lt_zero) e p
 return none

/-- Proof-returning companion to `ltZeroIntInHyps` for a non-literal `e`: when `e < 0` is a
    hypothesis in context, return its proof; otherwise `none`. -/
def ltZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkIntLitExpr (Int.ofNat 0)
 return hyps.get? (← mkIntLtExpr e zero)

/-- Proof-returning companion to `gtZeroIntInHyps` for a non-literal `e`: when `0 < e` is a
    hypothesis in context, return its proof; otherwise `none`. -/
def gtZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkIntLitExpr (Int.ofNat 0)
 return hyps.get? (← mkIntLtExpr zero e)

/-- Proof-returning companion to `leqZeroIntInHyps` for a non-literal `e`: when a hypothesis
    entailing `e ≤ 0` is in context (stored as `e < 0`, `0 = e`, or `¬ (0 < e)`), return a proof
    of the canonical `e ≤ 0`; otherwise `none`. -/
def leqZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkIntLitExpr (Int.ofNat 0)
 if let some p := hyps.get? (← mkIntLtExpr e zero) then
   return mkApp2 (mkConst ``Blaster.int_le_zero_of_lt_zero) e p
 if let some p := hyps.get? (← mkIntEqExpr zero e) then
   return mkApp2 (mkConst ``Blaster.int_le_zero_of_zero_eq) e p
 if let some p := hyps.get? (mkApp (← mkPropNotOp) (← mkIntLtExpr zero e)) then
   return mkApp2 (mkConst ``Blaster.int_le_zero_of_not_zero_lt) e p
 return none

/-- Proof-returning companion to `eqZeroNatInHyps` for a non-literal `e`: when `0 = e` is a
    hypothesis in context, return its proof; otherwise `none`. -/
def eqZeroNatProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkNatLitExpr 0
 return hyps.get? (← mkNatEqExpr zero e)

/-- Proof-returning companion to `gtZeroNatInHyps` for a non-literal `e`: when `0 < e` is a
    hypothesis in context, return its proof; otherwise `none`. -/
def gtZeroNatProof? (e : Expr) : TranslateEnvT (Option Expr) := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 let zero ← mkNatLitExpr 0
 return hyps.get? (← mkNatLtExpr zero e)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N > 0 ∧ Type(N) = Int`
      - return `some True` when `op1 := N + e ∧ op2 := e ∧ N < 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(N) = Int ∧ geqZeroIntInHyps b`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(N) = Int ∧ geqZeroIntInHyps b`
      - return `some True` when `op1 := a + b ∧ op2 := a ∧ Type(N) = Int ∧ ltZeroIntInHyps b`
      - return `some True` when `op1 := b + a ∧ op2 := a ∧ Type(N) = Int ∧ ltZeroIntInHyps b`
    Otherwise `none`.
-/
def intRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 match isIntValue? e1 with
 | some n =>
    if !(exprEq e2 op2) then return none
    if n > 0
    then
      pushProofStep
        (.rewrite (mkApp3 (mkConst ``Blaster.int_add_pos_lt_self_eq_false) op2 e1 boolTrueRefl))
      return ← mkPropFalse
    else
      pushProofStep
        (.rewrite (mkApp3 (mkConst ``Blaster.int_add_neg_lt_self_eq_true) op2 e1 boolTrueRefl))
      return ← mkPropTrue
 | none =>
     if exprEq e1 op2 then
       if let some p ← geqZeroIntProof? e2 then
         pushProofStep
           (.rewrite (mkApp3 (mkConst ``Blaster.int_add_lt_self_eq_false_of_nonneg) op2 e2 p))
         return ← mkPropFalse
       if let some p ← ltZeroIntProof? e2 then
         pushProofStep
           (.rewrite (mkApp3 (mkConst ``Blaster.int_add_lt_self_eq_true_of_neg) op2 e2 p))
         return ← mkPropTrue
     if exprEq e2 op2 then
       if let some p ← geqZeroIntProof? e1 then
         pushProofStep
           (.rewrite (mkApp3 (mkConst ``Blaster.int_add_lt_self_right_eq_false_of_nonneg) op2 e1 p))
         return ← mkPropFalse
       if let some p ← ltZeroIntProof? e1 then
         pushProofStep
           (.rewrite (mkApp3 (mkConst ``Blaster.int_add_lt_self_right_eq_true_of_neg) op2 e1 p))
         return ← mkPropTrue
     return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := e ∧ op2 := N + e ∧ N < 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Int ∧ leqZeroIntInHyps b`
      - return `some False` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Int ∧ leqZeroIntInHyps b`
      - return `some True` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Int ∧ gtZeroIntInHyps b`
      - return `some True` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Int ∧ gtZeroIntInHyps b`
    Otherwise `none`.
-/
def intRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 match (isIntValue? e1) with
 | some n =>
      if !(exprEq e2 op1) then return none
      if n > 0
      then
        pushProofStep
          (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_pos_eq_true) op1 e1 boolTrueRefl))
        return ← mkPropTrue
      else
        pushProofStep
          (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_neg_eq_false) op1 e1 boolTrueRefl))
        return ← mkPropFalse
 | none =>
      if exprEq e1 op1 then
        if let some p ← leqZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_self_eq_false_of_nonpos) op1 e2 p))
          return ← mkPropFalse
        if let some p ← gtZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_self_eq_true_of_pos) op1 e2 p))
          return ← mkPropTrue
      if exprEq e2 op1 then
        if let some p ← leqZeroIntProof? e1 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_self_right_eq_false_of_nonpos) op1 e1 p))
          return ← mkPropFalse
        if let some p ← gtZeroIntProof? e1 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_add_self_right_eq_true_of_pos) op1 e1 p))
          return ← mkPropTrue
      return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(a) = Nat`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(a) = Nat`
    Otherwise `none`.
-/
def natRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 if (exprEq e1 op2) then
   pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_add_lt_self_eq_false) op2 e2))
   return ← mkPropFalse
 if (exprEq e2 op2) then
   pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_add_lt_self_right_eq_false) op2 e1))
   return ← mkPropFalse
 return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Nat`
      - return `some False` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Nat ∧ eqZeroNatInHyps b`
      - return `some False` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Nat ∧ eqZeroNatInHyps b`
      - return `some True` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Nat ∧ gtZeroNatInHyps b`
      - return `some True` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Nat ∧ gtZeroNatInHyps b`
    Otherwise `none`.
-/
def natRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 match isNatValue? e1 with
 | some n =>
      if (exprEq e2 op1) then
        if n > 0 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_add_left_eq_true) op1 e1 boolTrueRefl))
          return ← mkPropTrue
      return none
 | none =>
      if (exprEq e1 op1) then
        if let some p ← eqZeroNatProof? e2 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_add_self_eq_false_of_zero_eq) op1 e2 p))
          return ← mkPropFalse
        if let some p ← gtZeroNatProof? e2 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_add_self_eq_true_of_zero_lt) op1 e2 p))
          return ← mkPropTrue
      if (exprEq e2 op1) then
        if let some p ← eqZeroNatProof? e1 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_add_self_right_eq_false_of_zero_eq) op1 e1 p))
          return ← mkPropFalse
        if let some p ← gtZeroNatProof? e1 then
          pushProofStep
            (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_add_self_right_eq_true_of_zero_lt) op1 e1 p))
          return ← mkPropTrue
      return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
      - return `some (S1 "<" S2)` when `op1 := S1 ∧ op2 := S2 ∧ Type(op1) = String`
    NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
    Otheriwse `none`.
-/
def cstLTProp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 match op1, op2 with
 | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) =>
   if Nat.blt n1 n2
   then pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_eq_true) op1 op2 boolTrueRefl))
   else pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_eq_false) op1 op2 boolFalseRefl))
   mkPropLit (Nat.blt n1 n2)
 | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => mkPropLit (s1 < s2)
 | _, _ =>
   match isIntValue? op1, isIntValue? op2 with
   | some n1, some n2 =>
     if n1 < n2
     then pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_eq_true) op1 op2 boolTrueRefl))
     else pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_eq_false) op1 op2 boolFalseRefl))
     mkPropLit (n1 < n2)
   | _, _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some ¬ (b < op1)` when `op2 := 1 + b ∧ Type(op1) = Int`
    Otherwise `none`.
-/
def intLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some 1 := isIntValue? e1 | return none
 pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.int_lt_one_add_eq_not_lt) op1 e2))
 setRestart
 return mkApp (← mkPropNotOp) (← mkIntLtExpr e2 op1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some b < 0` when `op1 := 0` ∧ op2 := -b ∧ Type(op1) = Int`
    Otherwise `none`.
-/
def intZeroLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some 0 := isIntValue? op1 | return none
 let some op2' := intNeg? op2 | return none
 pushProofStep (.rewrite (mkApp (mkConst ``Blaster.int_zero_lt_neg_eq_lt_zero) op2'))
 setRestart
 mkIntLtExpr op2' op1

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some True` when `op1 := 0` and `op2 := x + y` and `geqZeroIntInHyps x` and `gtZeroIntInHyps y`
      - return `some True` when `op1 := 0` and `op2 := x + y` and `gtZeroIntInHyps x` and `geqZeroIntInHyps y`
      - return `some False` when `op1 := 0` and `op2 := x + y` and `leqZeroIntInHyps x` and `ltZeroIntInHyps y`
      - return `some False` when `op1 := 0` and `op2 := x + y` and `ltZeroIntInHyps x` and `leqZeroIntInHyps y`

      - return `some False` when `op1 := x + y` and `op2 := 0` and `geqZeroIntInHyps x` and `gtZeroIntInHyps y`
      - return `some False` when `op1 := x + y` and `op2 := 0` and `gtZeroIntInHyps x` and `geqZeroIntInHyps y`
      - return `some True` when `op1 := x + y` and `op2 := 0` and `leqZeroIntInHyps x` and `ltZeroIntInHyps y`
      - return `some True` when `op1 := x + y` and `op2 := 0` and `ltZeroIntInHyps x` and `leqZeroIntInHyps y`

    Otherwise `none`
-/
def intZeroLtSum? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? op1, isIntValue? op2, intAdd? op1, intAdd? op2 with
  | some 0, _, _, some (e1, e2) =>
      if let some p1 ← geqZeroIntProof? e1 then
        if let some p2 ← gtZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_zero_lt_add_eq_true_of_nonneg_pos) e1 e2 p1 p2))
          return (← mkPropTrue)
      if let some p1 ← gtZeroIntProof? e1 then
        if let some p2 ← geqZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_zero_lt_add_eq_true_of_pos_nonneg) e1 e2 p1 p2))
          return (← mkPropTrue)
      if let some p1 ← leqZeroIntProof? e1 then
        if let some p2 ← ltZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_zero_lt_add_eq_false_of_nonpos_neg) e1 e2 p1 p2))
          return (← mkPropFalse)
      if let some p1 ← ltZeroIntProof? e1 then
        if let some p2 ← leqZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_zero_lt_add_eq_false_of_neg_nonpos) e1 e2 p1 p2))
          return (← mkPropFalse)
      return none
  | _, some 0, some (e1, e2), _ =>
      if let some p1 ← geqZeroIntProof? e1 then
        if let some p2 ← gtZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_add_lt_zero_eq_false_of_nonneg_pos) e1 e2 p1 p2))
          return (← mkPropFalse)
      if let some p1 ← gtZeroIntProof? e1 then
        if let some p2 ← geqZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_add_lt_zero_eq_false_of_pos_nonneg) e1 e2 p1 p2))
          return (← mkPropFalse)
      if let some p1 ← leqZeroIntProof? e1 then
        if let some p2 ← ltZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_add_lt_zero_eq_true_of_nonpos_neg) e1 e2 p1 p2))
          return (← mkPropTrue)
      if let some p1 ← ltZeroIntProof? e1 then
        if let some p2 ← leqZeroIntProof? e2 then
          pushProofStep
            (.rewrite (mkApp4 (mkConst ``Blaster.int_add_lt_zero_eq_true_of_neg_nonpos) e1 e2 p1 p2))
          return (← mkPropTrue)
      return none
  | _, _, _, _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some ¬ (b < op1)` when `op2 := 1 + b ∧ Type(a) = Nat`
    Otherwise `none`.
-/
def natLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some 1 := isNatValue? e1 | return none
 pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_lt_one_add_eq_not_lt) op1 e2))
 setRestart
 return (mkApp (← mkPropNotOp) (← mkNatLtExpr e2 op1))


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Nat`:
       - return `some False` when `N2 ≤ N1`
       - return `some a < N2 "-" N1` when `N2 > N1`
    Otherwise `none`.
-/
def addNatLeftLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 let some n2 := isNatValue? op2 | return none
 let some n1 := isNatValue? e1 | return none
 if n2 ≤ n1 then
   pushProofStep
    (.rewrite (mkApp4 (mkConst ``Blaster.nat_add_const_lt_eq_false) e2 e1 op2 boolTrueRefl))
   mkPropFalse
 else
   pushProofStep
    (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_const_lt_eq_lt_sub) e2 e1 op2))
   setRestart -- restart necessary to cache new expression
   mkNatLtExpr e2 (← evalBinNatOp Nat.sub n2 n1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Nat`:
       - return `some True` when `N1 < N2`
       - return `some N1 "-" N2 < a` when `N1 ≥ N2`
    Otherwise `none`.
-/
def addNatRightLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some n1 := isNatValue? op1 | return none
 let some n2 := isNatValue? e1 | return none
 if n1 < n2 then
   pushProofStep
    (.rewrite (mkApp4 (mkConst ``Blaster.nat_const_lt_add_eq_true) e2 op1 e1 boolTrueRefl))
   mkPropTrue
 else
   pushProofStep
    (.rewrite (mkApp4 (mkConst ``Blaster.nat_const_lt_add_eq_sub_lt) e2 op1 e1 boolTrueRefl))
   setRestart -- restart necessary to cache new expression
   mkNatLtExpr (← evalBinNatOp Nat.sub n1 n2) e2


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Int`:
       - return `some a < N2 "-" N1`
    Otherwise `none`.
-/
def addIntLeftLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 let some n2 := isIntValue? op2 | return none
 let some n1 := isIntValue? e1 | return none
 pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_add_const_lt_eq_lt_sub) e2 e1 op2))
 setRestart -- restart necessary to cache new expression
 mkIntLtExpr e2 (← evalBinIntOp Int.sub n2 n1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Int`:
       - return `some N1 "-" N2 < a`
    Otherwise `none`.
-/
def addIntRightLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some n1 := isIntValue? op1 | return none
 let some n2 := isIntValue? e1 | return none
 pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_const_lt_add_eq_sub_lt) e2 op1 e1))
 setRestart -- restart necessary to cache new expression
 mkIntLtExpr (← evalBinIntOp Int.sub n1 n2) e2

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`,
    return `true` only when the following conditions are satisfied
      - `op1 := N` ∧
      - ¬ (N - 1 < op2) _ ∈ hypothesisContext.hypothesisMap ∧
      - Type(op2) ∈ [Nat, Int]
-/
def predCstLTInHyp (op1 : Expr) (op2 : Expr) : TranslateEnvT Bool := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 match isNatValue? op1 with
 | some n =>
      let pred_n ← evalBinNatOp Nat.sub n 1
      if let some p := hyps.get? (mkApp (← mkPropNotOp) (← mkNatLtExpr pred_n op2)) then
        pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_lt_false_of_not_pred_lt) op1 op2 p))
        return true
      return false
 | none =>
    let some n := isIntValue? op1 | return false
    let pred_n ← evalBinIntOp Int.sub n 1
    if let some p := hyps.get? (mkApp (← mkPropNotOp) (← mkIntLtExpr pred_n op2)) then
      pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_lt_false_of_not_pred_lt) op1 op2 p))
      return true
    return false

/-- Apply the following simplification/normalization rules on `LT.lt` :
     - e1 < e2 ==> False (if e1 =ₚₜᵣ e2)    [proof: Blaster.{nat,int}_lt_self_eq_false]
     - e < 0 ==> False (if Type(e) = Nat)   [proof: Blaster.nat_lt_zero_eq_false]
     - 0 < -e ==> e < 0 (if Type(e) = Int   [proof: Blaster.int_zero_lt_neg_eq_lt_zero]
     - N1 < N2 ==> N1 "<" N2    [proof: Blaster.{nat,int}_lt_eq_{true,false}]
     - N < e ==> False (if ¬ (N - 1 < e) := _ ∈ hypothesisContext.hypothesisMap ∧ Type(e) ∈ [Nat, Int])    [proof: Blaster.{nat,int}_lt_false_of_not_pred_lt]
     - e < 1 ==> 0 = e (if Type(e) = Nat)    [proof: Blaster.nat_lt_one_eq_zero_eq]
     - a + b < a | b + a < a ==> False (if Type(a) = Nat)    [proof: Blaster.nat_add_lt_self{,_right}_eq_false]
     - N + e < e ==> False (if N > 0 ∧ Type(e) = Int)        [proof: Blaster.int_add_pos_lt_self_eq_false]
     - N + e < e ==> True (if N < 0 ∧ Type(e) = Int)         [proof: Blaster.int_add_neg_lt_self_eq_true]
     - a + b < a | b + a < a ==> False (if Type(a) = Int ∧ geqZeroIntInHyps b)    [proof: Blaster.int_add_lt_self{,_right}_eq_false_of_nonneg]
     - a + b < a | b + a < a ==> True (if Type(a) = Int ∧ ltZeroIntInHyps b)    [proof: Blaster.int_add_lt_self{,_right}_eq_true_of_neg]
     - e < N + e ==> True (if N > 0 ∧ Type(N) ∈ [Nat, Int])  [proof: Blaster.nat_lt_add_left_eq_true, Blaster.int_lt_add_pos_eq_true]
     - e < N + e ==> False (if N < 0 ∧ Type(N) = Int)        [proof: Blaster.int_lt_add_neg_eq_false]
     - a < a + b | a < b + a ==> False (if Type(a) = Nat ∧ eqZeroNatInHyps b)    [proof: Blaster.nat_lt_add_self{,_right}_eq_false_of_zero_eq]
     - a < a + b | a < b + a ==> True (if Type(a) = Nat ∧ gtZeroNatInHyps b)    [proof: Blaster.nat_lt_add_self{,_right}_eq_true_of_zero_lt]
     - a < a + b | a < b + a ==> False (if Type(a) = Int ∧ leqZeroIntInHyps b)    [proof: Blaster.int_lt_add_self{,_right}_eq_false_of_nonpos]
     - a < a + b | a < b + a ==> True (if Type(a) = Int ∧ gtZeroIntInHyps b)    [proof: Blaster.int_lt_add_self{,_right}_eq_true_of_pos]
     - N1 + a < N2 ==> False (if Type(a) = Nat ∧ N2 ≤ N1)    [proof: Blaster.nat_add_const_lt_eq_false]
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Nat ∧ N2 > N1)    [proof: Blaster.nat_add_const_lt_eq_lt_sub]
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Int)    [proof: Blaster.int_add_const_lt_eq_lt_sub]
     - N1 < N2 + a ==> True (if Type(a) = Nat ∧ N1 < N2)    [proof: Blaster.nat_const_lt_add_eq_true]
     - N1 < N2 + a ==> N1 "-" N2 < a (if Type(a) = Nat ∧ N1 ≥ N2)    [proof: Blaster.nat_const_lt_add_eq_sub_lt]
     - N1 < N2 + a ==> N1 "-" N2 < a  (if Type(a) = Int)    [proof: Blaster.int_const_lt_add_eq_sub_lt]
     - N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])    [proof: Blaster.{nat,int}_add_both_lt]
     - a < 1 + b ==> ¬ (b < a) (if Type(a) ∈ [Nat, Int])    [proof: Blaster.{nat,int}_lt_one_add_eq_not_lt]
     - 0 < x + y ==> True (if Type (x) ∈ Int ∧ geqZeroIntInHyps x ∧ gtZeroIntInHyps y)    [proof: Blaster.int_zero_lt_add_eq_true_of_nonneg_pos]
     - 0 < x + y ==> True (if Type (x) ∈ Int ∧ gtZeroIntInHyps x ∧ geqZeroIntInHyps y)    [proof: Blaster.int_zero_lt_add_eq_true_of_pos_nonneg]
     - 0 < x + y ==> False (if Type (x) = Int ∧ ltZeroIntInHyps x ∧ leqZeroIntInHyps y)    [proof: Blaster.int_zero_lt_add_eq_false_of_neg_nonpos]
     - 0 < x + y ==> False (if Type (x) = Int ∧ leqZeroIntInHyps x ∧ ltZeroIntInHyps y)    [proof: Blaster.int_zero_lt_add_eq_false_of_nonpos_neg]
     - x + y < 0 ==> False (if Type (x) = Int ∧ geqZeroIntInHyps x ∧ gtZeroIntInHyps y)    [proof: Blaster.int_add_lt_zero_eq_false_of_nonneg_pos]
     - x + y < 0 ==> False (if Type (x) = Int ∧ gtZeroIntInHyps x ∧ geqZeroIntInHyps y)    [proof: Blaster.int_add_lt_zero_eq_false_of_pos_nonneg]
     - x + y < 0 ==> True (if Type (x) = Int ∧ leqZeroIntInHyps x ∧ ltZeroIntInHyps y)    [proof: Blaster.int_add_lt_zero_eq_true_of_nonpos_neg]
     - x + y < 0 ==> True (if Type (x) = Int ∧ ltZeroIntInHyps x ∧ leqZeroIntInHyps y)    [proof: Blaster.int_add_lt_zero_eq_true_of_neg_nonpos]
   The simplifications are only applied when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LT.lt.
   Do nothing if operator is partially applied (i.e., args.size < 4)
-/
def optimizeLT (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (mkAppN f args)
 if args.size != 4 then return (mkAppN f args)
 -- args[0] is sort parameter
 -- args[1] LT instance
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if (exprEq op1 op2) then
   let lt_type := args[0]!
   if lt_type.isConstOf ``Nat then
     pushProofStep (.rewrite (mkApp (mkConst ``Blaster.nat_lt_self_eq_false) op1))
   else if lt_type.isConstOf ``Int then
     pushProofStep (.rewrite (mkApp (mkConst ``Blaster.int_lt_self_eq_false) op1))
   return (← mkPropFalse)
 if (isZeroNat op2) then
   pushProofStep (.rewrite (mkConst ``Blaster.nat_lt_zero_eq_false))
   return (← mkPropFalse)
 if let some r ← intZeroLtNorm? op1 op2 then return r
 if let some r ← cstLTProp? op1 op2 then return r
 if ← predCstLTInHyp op1 op2 then return (← mkPropFalse)
 if (isOneNat op2) then
   pushProofStep (.rewrite (mkApp (mkConst ``Blaster.nat_lt_one_eq_zero_eq) op1))
   return (← mkNatEqExpr (← mkNatLitExpr 0) op1)
 if let some r ← intRelLeftReduce? op1 op2 then return r
 if let some r ← intRelRightReduce? op1 op2 then return r
 if let some r ← natRelLeftReduce? op1 op2 then return r
 if let some r ← natRelRightReduce? op1 op2 then return r
 if let some r ← addNatLeftLtReduce? op1 op2 then return r
 if let some r ← addNatRightLtReduce? op1 op2 then return r
 if let some r ← addIntLeftLtReduce? op1 op2 then return r
 if let some r ← addIntRightLtReduce? op1 op2 then return r
 if let some r ← addNatBothReduce? op1 op2 then return r
 if let some r ← addIntBothReduce? op1 op2 then return r
 if let some r ← intLtNorm? op1 op2 then return r
 if let some r ← natLtNorm? op1 op2 then return r
 if let some r ← intZeroLtSum? op1 op2 then return r
 return mkAppN f args

 where
   /-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Nat`:
       - return `some N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addNatBothReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := natAdd? op1 | return none
     let some (e3, e4) := natAdd? op2 | return none
     let some n1 := isNatValue? e1 | return none
     let some n2 := isNatValue? e3 | return none
     setRestart
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let leftLit ← mkNatLitExpr leftValue
     let rightLit ← mkNatLitExpr rightValue
     let op1' := mkApp2 (← mkNatAddOp) leftLit e2
     let op2' := mkApp2 (← mkNatAddOp) rightLit e4
     let hLeft := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) leftLit
     let hRight := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) rightLit
     pushProofStep
       (.rewrite (mkAppN (mkConst ``Blaster.nat_add_both_lt) #[e2, e4, e1, e3, leftLit, rightLit, hLeft, hRight]))
     return mkApp4 f args[0]! args[1]! op1' op2'

   /-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Int`:
       - return `some N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addIntBothReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := intAdd? op1 | return none
     let some (e3, e4) := intAdd? op2 | return none
     let some n1 := isIntValue? e1 | return none
     let some n2 := isIntValue? e3 | return none
     setRestart
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let leftLit ← mkIntLitExpr leftValue
     let rightLit ← mkIntLitExpr rightValue
     let op1' := mkApp2 (← mkIntAddOp) leftLit e2
     let op2' := mkApp2 (← mkIntAddOp) rightLit e4
     let hLeft := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Int) leftLit
     let hRight := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Int) rightLit
     pushProofStep
       (.rewrite (mkAppN (mkConst ``Blaster.int_add_both_lt) #[e2, e4, e1, e3, leftLit, rightLit, hLeft, hRight]))
     return mkApp4 f args[0]! args[1]! op1' op2'


/-- Apply the following normalization rule on `LE.le` :
     - e1 ≤ e2 ==> ¬ (e2 < e1) (if Type(e1) = Nat)   [proof: Blaster.nat_le_eq_not_lt]
     - e1 ≤ e2 ==> ¬ (e2 < e1) (if Type(e1) = Int)   [proof: Blaster.int_le_eq_not_lt]

   This normalization rule is applied only when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LE.le.
-/
def optimizeLE (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (mkAppN f args)
 if args.size == 4 then
   -- args[0] is sort parameter
   -- args[1] Le instance
   -- args[2] left operand
   -- args[3] right operand
   let le_type := args[0]!
   let op1 := args[2]!
   let op2 := args[3]!
   if le_type.isConstOf ``Nat then
     pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_le_eq_not_lt) op1 op2))
   else if le_type.isConstOf ``Int then
     pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.int_le_eq_not_lt) op1 op2))
   setRestart
   mkNotLtExpr le_type op2 op1
 else if args.size == 2 then
   setRestart
   -- we need to return a lambda term here, i.e.,
   -- λ e1 e2 => ¬ (e2 < e1)
   let le_type := args[0]!
   let body ← mkNotLtExpr le_type (mkBVar 0) (mkBVar 1)
   let lam1 := mkLambda `y BinderInfo.default le_type body
   return mkLambda `x BinderInfo.default le_type lam1
 else throwEnvError "optimizeLE: at least 2 arguments expected but got {reprStr args}"

 where
   mkNotLtExpr (t : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT Expr := do
     let ltInst ← findLtInstance t
     let ltExpr := mkApp4 (← mkLtOp) t ltInst op1 op2
     return mkApp (← mkPropNotOp) ltExpr

   findLtInstance (t : Expr) : TranslateEnvT Expr := do
     let some ltInst ← trySynthConstraintInstance? (mkApp (← mkLTConst) t)
       | throwEnvError "optimizeLE: synthesize instance for [LT {reprStr t} cannot be found"
     return ltInst

/-- Apply simplification and normalization rules on `LE.le` and `LT.lt` :
-/
def optimizeRelational? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
  | ``LE.le => optimizeLE f args
  | ``LT.lt => optimizeLT f args
  | _ => return none


end Blaster.Optimize
