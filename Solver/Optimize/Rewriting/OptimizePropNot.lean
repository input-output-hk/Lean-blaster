import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta
namespace Solver.Optimize

/-- Return `true` when `e` corresponds to the zero nat literal. -/
def isZeroNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 0 => true
  | _ => false

/-- Return `some (true = e)` when `ne := false = e` or `some (false = e)` when `ne := true = e`.
    Otherwise `none`.
-/
def notEqSimp? (ne : Expr) : TranslateEnvT (Option Expr) := do
  match ne.eq? with
  | some (eq_sort, op1, op2) =>
     match op1 with
     | Expr.const ``false _ =>
         mkExpr (mkApp3 ne.getAppFn eq_sort (← mkBoolTrue) op2)
     | Expr.const ``true _ =>
         mkExpr (mkApp3 ne.getAppFn eq_sort (← mkBoolFalse) op2)
     | _ => return none
  | none => return none

/-- Given `ne` the operand for `Not`, try to apply the following normalization rules:
    - When `ne := 0 < e` ∧ Type(a) = Nat:
       - return `some (0 = e)`
    - Otherwise:
       - return `none`
-/
def notLTNumNorm? (ne : Expr) : TranslateEnvT (Option Expr) := do
  let some (_t, _i, e1, e2) := lt? ne | return none
  if isZeroNat e1
  then mkNatEqExpr e1 e2
  else return none

/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True
     - ¬ True ==> False
     - ¬ (¬ e) ==> e (classical)
     - ¬ (false = e) ==> true = e
     - ¬ (true = e) ==> false = e
     - ¬ (0 < e) ==> (0 = e) (if Type(e) = Nat)
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Not` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeNot: exactly one argument expected"
 let e := args[0]!
 if let Expr.const ``False _ := e then return (← mkPropTrue)
 if let Expr.const ``True _ := e then return (← mkPropFalse)
 if let some op := propNot? e then return op
 if let some r ← notEqSimp? e then return r
 if let some r ← notLTNumNorm? e then return r
 mkExpr (mkApp f e)

/-- Apply simplification and normalization rules on proposition `Not` formulae. -/
def optimizePropNot? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Not _ => optimizeNot f args
  | _ => pure none

/-- Given `e` and hypothesis map `h` returns `true` when one of the following conditions
    is satisfied:
      - ¬ e := fv ∈ h;
      - e := a = b ∧ Type(a) ∈ [Int, Nat] ∧ (a < b := fv ∈ h ∨ b < a := fv ∈ h)
      - e := a < b ∧ Type(a) ∈ [Int, Nat] ∧ (a = b := fv ∈ h ∨ b < a := fv ∈ h)

    Note that:
     - a ≤ b is normalized to `¬ (b < a)` when `Type(a) ∈ [Int, Nat]`
-/
def notInHypMap (e : Expr) (h : HypothesisMap) : TranslateEnvT Bool := do
  let not_e ← optimizeNot (← mkPropNotOp) #[e]
  if h.contains not_e then return true
  if (← notEqInHyp e) then return true
  notLtInHyp e

 where
   /-- Return `true` when the following condition is satisfied:
         - e := a = b ∧ Type(a) ∈ [Int, Nat] ∧ (a < b := fv ∈ h ∨ b < a := fv ∈ h)
       Otherwise `none`
   -/
   notEqInHyp (e : Expr) : TranslateEnvT Bool := do
    let some (sort, op1, op2) := e.eq? | return false
    match sort with
    | Expr.const ``Nat _ =>
        if h.contains (← mkNatLtExpr op1 op2) then return true
        return h.contains (← mkNatLtExpr op2 op1)
    | Expr.const ``Int _ =>
        if h.contains (← mkIntLtExpr op1 op2) then return true
        return h.contains (← mkIntLtExpr op2 op1)
    | _ => return false

   /-- Return `true` when the following condition is satisfied:
       - e := a < b ∧ Type(a) ∈ [Int, Nat] ∧ (a = b := fv ∈ h ∨ b < a := fv ∈ h)
   -/
   notLtInHyp (e : Expr) : TranslateEnvT Bool := do
     let some (sort, _inst, op1, op2) := lt? e | return false
     match sort with
     | Expr.const ``Nat _ =>
          let args ← reorderPropOp #[op1, op2]
          if h.contains (← mkNatEqExpr args[0]! args[1]! ) then return true
          return h.contains (← mkNatLtExpr op2 op1)
     | Expr.const ``Int _ =>
          let args ← reorderPropOp #[op1, op2]
          if h.contains (← mkIntEqExpr args[0]! args[1]! ) then return true
          return h.contains (← mkIntLtExpr op2 op1)
     | _ => return false


/-- Given `e` and hypothesis map `h` returns `some fv` when one of the following conditions
    is satisfied:
      - e := fv ∈ h;
      - e := ¬ (a = b) ∧ Type(a) ∈ [Int, Nat] ∧ (a < b := fv ∈ h ∨ b < a := fv ∈ h)
-/
@[always_inline, inline]
def inHypMap (e : Expr) (h : HypothesisMap) : TranslateEnvT (Option (Option Expr)) := do
  if let some m := h.get? e then return some m
  let some ne := propNot? e | return none
  let some (sort, op1, op2) := ne.eq? | return none
  match sort with
  | Expr.const ``Nat _ =>
      if let some m := h.get? (← mkNatLtExpr op1 op2) then return some m
      return h.get? (← mkNatLtExpr op2 op1)
  | Expr.const ``Int _ =>
      if let some m := h.get? (← mkIntLtExpr op1 op2) then return some m
      return h.get? (← mkIntLtExpr op2 op1)
  | _ => return none

end Solver.Optimize
