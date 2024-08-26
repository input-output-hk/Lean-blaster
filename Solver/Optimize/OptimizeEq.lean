import Lean
import Solver.Optimize.OptimizeBool
import Solver.Optimize.OptimizeProp

open Lean Meta
namespace Solver.Optimize


/-- Return `some true` if op1 and op2 are constructors that are structurally equivalent modulo variable name/function equivalence
    Return `some false` if op1 and op2 are constructors that are NOT structurally equivalent.
    Return `none` otherwise.
-/
partial def structEq? (op1 : Expr) (op2: Expr) : MetaM (Option Bool) := do
 match op1, op2 with
 | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) => pure (some (n1 == n2))
 | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => pure (some (s1 == s2))
 | Expr.fvar v1, Expr.fvar v2 => pure (if v1 == v2 then some true else none)
 | _, _ =>
   match op1, op2 with
   | Expr.const n1 _, Expr.const n2 _ =>
       if (← (isCtorName n1) <&&> (isCtorName n2))
       then pure (some (n1 == n2))
       else if n1 == n2 -- functional case
            then pure (some true)
            else pure none
   | Expr.app .., Expr.app .. =>
      Expr.withApp op1 fun f1 as1 =>
       Expr.withApp op2 fun f2 as2 => do
        if as1.size == as2.size
        then
         match (← structEq? f1 f2) with
         | feq@(some b) =>
            -- lattice to handle arguments
            -- some false -> some none -> some true
            let mut lat := some true
            if b
            then
              for i in [:as1.size] do
               lat := updateLattice lat (← structEq? as1[i]! as2[i]!)
               unless (!isTop lat) do return lat -- break if false
              pure lat
            else pure feq
         | none => pure none
        else
          if (← (isCtorExpr f1) <&&> (isCtorExpr f2))
          then pure (some false)
          else pure none -- return non when f1 and f2 are functions
   | _, _ =>
     -- for all other cases we return `some true` only when op1 and op2
     -- are physically equivalent, e.g., same function call,
     -- same lambda expression, etc.
     if (← exprEq op1 op2)
     then pure (some true)
     else pure none

 where
   /-- update the lattice for application arguments such that:
        - some true corresponds to the bottom element
        - some false corresponds to the top element (the identity element)
        - some none the middle element
       The join rules applied on update are the following:
        - some true, some false ===> some false
        - none, some false ===> some false
        - some false, some false ==> some false
        - some true, none ===> none
        - none, none ===> none
        - some true, some true ===> some true

   -/
   updateLattice : Option Bool -> Option Bool -> Option Bool
     | some false, _ | _, some false => some false
     | none, _ | _, none => none
     | some true, some true => some true

   isTop : Option Bool -> Bool
    | some false => true
    | _ => false


/-- Apply the following simplification/normalization rules on `Eq` :
     - False = e ==> ¬ e
     - True = e ==> e
     - e = ¬ e ==> False
     - ¬ e = e ==> False
     - e = not e ==> False
     - not e = e ==> False
     - e1 = e2 ==> True (if e1 =ₚₜᵣ e2)
     - e1 = e2 ==> False (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜₜ)
     - true = not e ==> false = e
     - false = not e ==> true = e
     - ¬ e1 = ¬ e2 ==> e1 = e2 (require classical)
     - not e1 = not e2 ==> e1 = e2
     - e1 = e2 ==> e2 = e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Eq.
   An error is triggered when:
    - args.size ≠ 4; or
    - structEq? e1 e2 = some true
   TODO: consider additional simplification rules
   TODO: seperate rewriting that require classical reasoning from others.
   TODO: add an option to activate/deactivate classical simplification (same for optimizeProp).
-/
partial def optimizeEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size == 3 then
   -- args[0] is sort parameter
   -- args[1] left operand
   -- args[2] right operand
   let opArgs ← reorderArgs #[args[1]!, args[2]!]
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``False _, _ => optimizeNot (← mkPropNotOp) #[op2]
   | Expr.const ``True _, _ => pure op2
   | _, _ =>
     if (← (isNotExprOf op1 op2) <||> (isNotExprOf op2 op1) <||> (isBoolNotExprOf op1 op2) <||> (isBoolNotExprOf op2 op1))
     then mkPropFalse
     else if (← exprEq op1 op2) then mkPropTrue
     else
       match (← structEq? op1 op2) with
       | some b =>
          if !b
          then mkPropFalse
          else throwError f!"optimizeEq: pointer equality expected for {op1} {op2}" -- should be unreachable if memoization properly done
       | none =>
         match (← notNegEqSimp op1 op2) with
         | some (e1, e2) => optimizeEq f #[args[0]!, e1, e2]
         | none => mkAppExpr f #[args[0]!, op1, op2]
 else throwError f!"optimizeEq: three arguments for Eq but got {args}"

 where
   notNegEqSimp (op1: Expr) (op2: Expr) : TranslateEnvT (Option (Expr × Expr)) := do
    match op1, toBoolNotExpr op2, toBoolNotExpr op1 with
    | Expr.const ``true _, some e, _ => pure (some (← mkBoolFalse, e))
    | Expr.const ``false _, some e, _ => pure (some (← mkBoolTrue, e))
    | _, some e2, some e1 => pure (some (e1, e2))
    | _, _, _ =>
      match toNotExpr op1, toNotExpr op2 with
      | some e1, some e2 => pure (some (e1, e2))
      | _, _ => pure none


/-- Apply the following simplification/normalization rules on `BEq.beq` :
     - false == e ==> not e
     - true == e ==> e
     - e == not e ==> false
     - not e == e ==> false
     - e1 == e2 ==> true (if e1 =ₚₜᵣ e2)
     - not e1 == not e2 ==> e1 == e2
     - e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)

   Assume that f = Expr.const ``BEq.beq.
   An error is triggered when
     - args.size ≠ 4; or
     - isOpaqueBeq f.constName args is not satisfied.

   NOTE: The above simmplification rules are applied only on BEq.beq satisfiying the isOpaqueBeq predicate.
   In fact, we can't assume that BEq.beq will properly be defined for user-defined types or parametric inductive types.

   NOTE: Unlike `Eq there is no need to add an explicity rule for constructor operands as these
   are implicilty resolved via reduceApp.
   TODO: consider additional simplification rules
-/
partial def optimizeBEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size == 4 && isOpaqueBeq f.constName args
 then
   -- args[0] is sort parameter
   -- args[1] decidable instance parameter
   -- args[2] left operand
   -- args[3] right operand
   let opArgs ← reorderArgs #[args[2]!, args[3]!]
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``false _, _ => optimizeBoolNot (← mkBoolNotOp) #[op2]
   | Expr.const ``true _, _ => pure op2
   | _, _ =>
     if (← (isBoolNotExprOf op1 op2) <||> (isBoolNotExprOf op2 op1))
     then mkBoolFalse
     else if (← exprEq op1 op2) then mkBoolTrue
     else match toBoolNotExpr op1, toBoolNotExpr op2 with
          | some e1, some e2 => optimizeBEq f #[args[0]!, args[1]!, e1, e2]
          | _, _ => mkAppExpr f #[args[0]!, args[1]!, op1, op2]
 else throwError f!"optimizeBEq: invalid BEq.beq expression: {f} {args}"


/-- Apply simplification and normalization rules on `Eq` and \BEq.beq` :
-/
def optimizeEquality (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
     match n with
      | ``Eq => some <$> optimizeEq f args
      | ``BEq.beq => some <$> optimizeBEq f args
      | _ => pure none
 | _ => pure none
end Solver.Optimize
