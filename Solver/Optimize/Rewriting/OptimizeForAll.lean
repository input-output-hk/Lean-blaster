import Lean
import Solver.Optimize.Rewriting.OptimizePropNot

open Lean Meta Elab
namespace Solver.Optimize


/-- Given `a → b`, apply the simplification rules:
      - When `a := True ∧ Type(b) = Prop`:
         - return `some b`
      - When `a := False ∧ Type(b) = Prop`:
          - return `some True`
      - Otherwise
          - return `none`
-/
def isCstImplies? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if !(← isProp b) then return none
 match a with
 | Expr.const ``True _ => return b
 | Expr.const ``False _ => return (← mkPropTrue)
 | _ => return none

 /-- Given `a → b`, apply the following normalization rule:
      - When `b := False ∧ Type(a) = Prop`
         - return `some ¬ a`
      - Otherwise
         - return `none`
 -/
 def isNotDef? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  if !(← isProp a) then return none
  match b with
  | Expr.const ``False _ => optimizeNot (← mkPropNotOp) #[a]
  | _ => return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = ¬ b
        - return `some ¬ a`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ b
        - return `some ¬ a`
     - Otherwise:
        - return `none`
 -/
 def impliesToNeg? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  let notOp ← mkPropNotOp
  if (← notInHypMap b h) then return (← optimizeNot notOp #[a])
  let hyps := (← get).optEnv.hypsInContext
  if (← notInHypMap b hyps) then return (← optimizeNot notOp #[a])
  return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypsInContext, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ a
        - return `some True`
     - Otherwise:
        - return `none`
 -/
 def impliesToTrue? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  if (← inHypMap b h).isSome then return ← mkPropTrue
  let hyps := (← get).optEnv.hypsInContext
  if (← inHypMap b hyps).isSome then return ← mkPropTrue
  if !(← isProp b) then return none
  if (← notInHypMap a hyps) then return ← mkPropTrue
  return none

/-- Given `h : a → b`, apply the simplification rules:
    - When a := m ∈ hypsInContext
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
 if !(← isProp b) then return none
 let hyps := (← get).optEnv.hypsInContext
 match (← inHypMap a hyps) with
 | none => return none
 | some m =>
    if !fVarInExpr h.fvarId! b
    then return b
    else match m with
         | some h' => return (Expr.replaceFVar b h h')
         | none => return none

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - False → e ==> True (if Type(e) = Prop)
      - True → e ==> e (if Type(e) = Prop)
      - e → False ==> ¬ e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypsInContext, e = ¬ e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ h, e = e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypsInContext, e = e2)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypsInContext, e = ¬ e1 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypsInContext ∧ ¬ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2[h/h'] (if e1 := some h' ∈ hypsInContext ∧ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop )
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  Assume that `h` corresponds to the hypothesis map updated with hypotheses in `t`.
-/
def optimizeForall (n : Expr) (t : Expr) (h : HypothesisMap) (b : Expr) : TranslateEnvT Expr := do
  if let Expr.const ``True _ := b then return b
  if let some r ← isCstImplies? t b then return r
  if let some r ← isNotDef? t b then return r
  if (← (exprEq t b) <&&> (isProp t)) then return (← mkPropTrue)
  if let some r ← impliesToNeg? t b h then return r
  if let some r ← impliesToTrue? t b h then return r
  if let some r ← hypReduction? n t b then return r
  if (← (isSortOrInhabited t) <&&> (isProp b) <&&> (pure !(fVarInExpr n.fvarId! b))) then return b
  mkForallExpr n b

/-- `mkImpliesExpr a b` perform the following:
      - construct expression `a → b`
      - apply normalization/simplification rules on `a → b`
      - cache result
-/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default a fun x => do
    optimizeForall x a (← addHypotheses a (some x)).2 b


end Solver.Optimize
