import Lean
import Solver.Optimize.Rewriting.OptimizeBoolBinary
import Solver.Optimize.Rewriting.OptimizeEq
import Solver.Optimize.Rewriting.OptimizePropBinary

open Lean Meta
namespace Solver.Optimize

/- Given `op1` and `op2` corresponding to the operands for a propositional binary operator:
    - return `some (true = (boolOp1 NOP(B1, e1) NOP(B2, e2)))` when `op1 := B1 = e1 ∧ op2 := B2 = e2 ∧ (B1 ∨ B2)`
    - return `some (false = (boolOp2 e1 e2)` when `op1 := B1 = e1 ∧ op2 := B2 = e2 ∧ ¬ B1 ∧ ¬ B2`
   with
     - NOP(B, e) := e if B
                 := !e  otherwise
     - boolOp1 := ``and if isBoolAnd?
               := ``or otherwise
     - boolOp2 := ``or if isBoolAnd?
               := ``and otherwise
   Otherwise `none`
-/
def propExprToBoolExpr?
  (op1 : Expr) (op2 : Expr) (isBoolAnd? := true) : TranslateEnvT (Option Expr) := do
  match op1.eq?, op2.eq? with
  | some (_, a_op1, a_op2), some (_, b_op1, b_op2) =>
     match isBoolValue? a_op1, isBoolValue? b_op1 with
     | some bv1, some bv2 =>
         if bv1 || bv2
         then
           let e1 ← toBoolNotExpr? bv1 a_op2
           let e2 ← toBoolNotExpr? bv2 b_op2
           let binExpr ← if isBoolAnd?
                         then optimizeBoolAnd (← mkBoolAndOp) #[e1, e2]
                         else optimizeBoolOr (← mkBoolOrOp) #[e1, e2]
           mkEqBool binExpr true
         else
           let binExpr ← if isBoolAnd?
                         then optimizeBoolOr (← mkBoolOrOp) #[a_op2, b_op2]
                         else optimizeBoolAnd (← mkBoolAndOp) #[a_op2, b_op2]
           mkEqBool binExpr false
     | _, _ => return none
  | _, _ => return none

/-- Call `optimizeAnd f args` and apply the following simplification/normalization
    rules on the resulting `And` expression (if any):
      - B1 = e1 ∧ B2 = e2 ==> true = (NOP(B1, e1) && NOP(B2, e2)) (if B1 ∨ B2)
      - B1 = e1 ∧ B2 = e2 ==> false = (e1 || e2) (if ¬ B1 ∧ ¬ B2)
    with
     NOP(B, e) := e if B
               := !e  otherwise

   Assume that f = Expr.const ``And.

   TODO: consider simplification rule:
     - `B = e ∧ (a = b) | (a = b) ∧ B = e ===> true = (NOP(B, e) && a == b) if isCompatibleBeqType Type(a)`
     - `(a = b) ∧ (c = d) ===> true = (a == b && c == d) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
     - `¬ (a = b) ∧ (c = d) | (c = d) ∧ ¬ (a = b) ===> true = (c == d && !(a == b)) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
     - `¬ (a = b) ∧ ¬ (c = d) ===> true = (!(a == b) && !(c == d)) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
    We need extra simplification rules on boolean operators to avoid hanlding the last case, i.e.,
    either normalize to CNF or push negation outside, i.e., ¬ ((a = b) ∨ (c = d)).

   TODO: reordering on list of `∧` must be performed to regroup all `B = e`
   together and all prop expression together. The reordering must be
   deterministic to produce the same sequence.

-/
def optimizeBoolPropAnd (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeAnd f args (cacheResult := false)
 let some (op1, op2) := propAnd? e | return e
 if let some r ← propExprToBoolExpr? op1 op2 then return r
 mkExpr e


/-- Call `optimizeOr f args` and apply the following simplification/normalization
    rules on the resulting `Or` expression (if any):
     - B1 = e1 ∨ B2 = e2 ==> true = (NOP(B1, e1) || NOP(B2, e2)) (if B1 ∨ B2)
     - B1 = e1 ∨ B2 = e2 ==> false = (e1 && e2) (if ¬ B1 ∧ ¬ B2)
    with
     NOP(B, e) := e if B
               := !e  otherwise

   Assume that f = Expr.const ``Or.

   TODO: consider simplification rule:
     - `B = e ∨ (a = b) | (a = b) ∨ B = e ===> true = (NOP(B, e) || a == b) if isCompatibleBeqType Type(a)`
     - `(a = b) ∨ (c = d) ===> true = (a == b || c == d) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
     - `¬ (a = b) ∨ (c = d) | (c = d) ∨ ¬ (a = b) ===> true = (c == d || !(a == b)) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
     - `¬ (a = b) ∨ ¬ (c = d) ===> true = (!(a == b) | !(c == d)) if isCompatibleBeqType Type(a)` ∧ isCompatibleBeqType Type(c)`
     We need extra simplification rules on boolean operators to avoid hanlding the last case, i.e.,
     either normalize to CNF or push negation outside, i.e., ¬ ((a = b) ∧ (c = d)).

   TODO: reordering on list of `∨` must be performed to regroup all `B = e`
   together and all prop expression together. The reordering must be
   deterministic to produce the same sequence.
-/
def optimizeBoolPropOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeOr f args (cacheResult := false)
 let some (op1, op2) := propOr? e | return e
 if let some r ← propExprToBoolExpr? op1 op2 (isBoolAnd? := false) then return r
 mkExpr e


/-- Apply simplification and normalization rules on proposition binary formulae.
-/
def optimizePropBinary? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``And => optimizeBoolPropAnd f args
  | ``Or => optimizeBoolPropOr f args
  | `Iff => optimizeIff args
  | _ => return none

end Solver.Optimize
