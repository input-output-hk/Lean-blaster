import Lean
import Solver.Optimize.Rewriting.OptimizePropNot

open Lean Meta Elab
namespace Solver.Optimize

/-- `mkImpliesExpr a b` return expression `a → b` without applying any normalization. -/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  return mkForall (← Term.mkFreshBinderName) BinderInfo.default a b

/-- Given `h : a → b`, apply the simplification rules:
      - When `a := True ∧ Type(b) = Prop`:
         - When ¬ fVarInExpr h.fvarId! b:
            - return `some b`
         - When fVarInExpr h.fvarId! b:
            - return `some b[h/True.intro]`
      - When `a := False ∧ Type(b) = Prop`:
          - return `some True`
      - Otherwise
          - return `none`

    TODO: We need to find a way to replace h in body with the proper h in hypothesis.
-/
def isCstImplies? (h : Expr) (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if !(← isPropEnv b) then return none
 match a with
 | Expr.const ``True _ =>
     if fVarInExpr h.fvarId! b
     then return (← mkExpr $ Expr.replaceFVar b h (← mkTrueIntro))
     else return b
 | Expr.const ``False _ => return (← mkPropTrue)
 | _ => return none

 /-- Given `a → b`, apply the following normalization rule:
      - When `b := False ∧ Type(a) = Prop`
         - return `some ¬ a`
      - Otherwise
         - return `none`
 -/
 def isNotDef? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  if !(← isPropEnv a) then return none
  match b with
  | Expr.const ``False _ =>
      setRestart
      return mkApp (← mkPropNotOp) a
  | _ => return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = ¬ b
        - return `some ¬ a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some ¬ a`
     - Otherwise:
        - return `none`
 -/
 def impliesToNeg? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  let notOp ← mkPropNotOp
  if (← notInHypMap b h) then
    setRestart
    return mkApp notOp a
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if (← notInHypMap b hyps) then
    setRestart
    return mkApp notOp a
  return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some True`
     - Otherwise:
        - return `none`
 -/
 def impliesToTrue? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  if (← inHypMap b h).isSome then return ← mkPropTrue
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if (← inHypMap b hyps).isSome then return ← mkPropTrue
  if !(← isPropEnv b) then return none
  if (← notInHypMap a hyps) then return ← mkPropTrue
  return none

/-- Given `h : a → b`, apply the simplification rules:
    - When a := m ∈ hypothesisContext.hypothesisMap ∧ Type(b) = Prop
       - When ¬ fVarInExpr h.fvarId! b
          - return `some b`
       - When fVarInExpr h.fvarId! b
           - When m := some h'
              - return `some b[h/h']
           - Otherwise
              - return `none`
    - Otherwise:
       - return `none`
-/
def hypReduction? (h : Expr) (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if !(← isPropEnv b) then return none
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 match (← inHypMap a hyps) with
 | none => return none
 | some m =>
    if !fVarInExpr h.fvarId! b
    then return b
    else match m with
         | some h' => return (← mkExpr $ Expr.replaceFVar b h h')
         | none => return none

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - False → e ==> True (if Type(e) = Prop)
      - h : True → e ==> e (if Type(e) = Prop ∧ ¬ fVarInExpr h.fvarId! e)
      - h : True → e ==> e[h/True.intro] (if Type(e) = Prop ∧ fVarInExpr h.fvarId! e)
            TODO: replace True.intro with proper proof
      - e → False ==> ¬ e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ h, e = e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2[h/h'] (if e1 := some h' ∈ hypothesisContext.hypothesisMap ∧ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop )
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  Assume that `h` corresponds to the hypothesis map updated with hypotheses in `t`.
-/
def optimizeForall (n : Expr) (t : Expr) (h : HypothesisMap) (b : Expr) : TranslateEnvT Expr := do
  if let Expr.const ``True _ := b then return b
  if let some r ← isCstImplies? n t b then return r
  if let some r ← isNotDef? t b then return r
  if (← (exprEq t b) <&&> (isPropEnv t)) then return (← mkPropTrue)
  if let some r ← impliesToNeg? t b h then return r
  if let some r ← impliesToTrue? t b h then return r
  if let some r ← hypReduction? n t b then return r
  if (← (isSortOrInhabited t) <&&> (isPropEnv b) <&&> (pure !fVarInExpr n.fvarId! b)) then return b
  mkForallExpr n b

end Solver.Optimize
