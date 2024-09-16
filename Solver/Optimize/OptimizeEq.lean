import Lean
import Solver.Optimize.OptimizeBool
import Solver.Optimize.OptimizeProp

open Lean Meta
namespace Solver.Optimize


/-- Return `some true` if op1 and op2 are constructors that are structurally equivalent modulo variable name/function equivalence
    Return `some false` if op1 and op2 are constructors that are NOT structurally equivalent.
    Return `none` otherwise.
    Assume that memoization is performed on expressions.
-/
partial def structEq? (op1 : Expr) (op2: Expr) : MetaM (Option Bool) := do
 let rec visit (op1 : Expr) (op2 : Expr) : MetaM (Option Bool) := do
   match op1, op2 with
    | Expr.lit _, Expr.lit _ => pure (some (← exprEq op1 op2))
    | Expr.const n1 _, Expr.const n2 _ =>
       if (← (isCtorName n1) <&&> (isCtorName n2))
       then pure (some (← exprEq op1 op2))
       else pure none -- function case not structurally equivalent
    | Expr.app .., Expr.app .. =>
        Expr.withApp op1 fun f1 as1 =>
         Expr.withApp op2 fun f2 as2 => do
          -- recursive call on visit instead of structEq? to properly handle case
          -- when f1 and f2 are fun calls with different arguments.
          -- Case when f1 and f2 are equal is handled when first calling structEq? (e.g., f x = f x)
          match (← visit f1 f2) with
          | some b =>
              if b && as1.size == as2.size then
                -- lattice to handle arguments
                -- some false -> some none -> some true
                let mut lat := some true
                for i in [:as1.size] do
                  lat := updateLattice lat (← structEq? as1[i]! as2[i]!)
                  unless (!isTop lat) do return lat -- break if false
                pure lat
              else pure (some false)
          | none => pure none
     | _, _ =>
       -- return `none` for all other cases if physically equality fails
       pure none
 if (← exprEq op1 op2)
 then pure (some true)
 else visit op1 op2

 where
   /-- update the lattice for application arguments such that:
        - some true corresponds to the bottom element
        - some false corresponds to the top element (the identity element)
        - some none the middle element
       The join rules applied on update are the following:
        - some true, some false ==> some false
        - none, some false ==> some false
        - some false, some false ==> some false
        - some true, none ==> none
        - none, none ==> none
        - some true, some true ==> some true

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
     - e = not e ==> False
     - e1 = e2 ==> True (if e1 =ₚₜᵣ e2)
     - e1 = e2 ==> False (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜₜ)
     - true = not e ==> false = e
     - false = not e ==> true = e
     - ¬ e1 = ¬ e2 ==> e1 = e2 (require classical)
     - not e1 = not e2 ==> e1 = e2
     - e1 = e2 ==> e2 = e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Eq.
   Do nothing if operator is partially applied (i.e., args.size < 3)
   An error is triggered when:
    - structEq? e1 e2 = some true
   NOTE: The `reduceApp` rule will not reduce any `Prop` operator (e.g., `Eq`) applied to constructors only.
   TODO: consider additional simplification rules
   TODO: seperate rewriting that require classical reasoning from others.
   TODO: add an option to activate/deactivate classical simplification (same for optimizeProp).
-/
partial def optimizeEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size == 3 then
   -- args[0] is sort parameter
   -- args[1] left operand
   -- args[2] right operand
   let opArgs ← reorderPropOp #[args[1]!, args[2]!]
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``False _, _ => optimizeNot (← mkPropNotOp) #[op2]
   | Expr.const ``True _, _ => pure op2
   | _, _ =>
     if (← (isNotExprOf op2 op1) <||> (isBoolNotExprOf op2 op1))
     then mkPropFalse
     else if (← exprEq op1 op2) then mkPropTrue
     else
       match (← structEq? op1 op2) with
       | some b =>
          if !b
          then mkPropFalse
          else throwError f!"optimizeEq: pointer equality expected for {op1} {op2}" -- should be unreachable if memoization properly done
       | none =>
         match (← notNegEqSimp? op1 op2) with
         | some (e1, e2) => optimizeEq f #[args[0]!, e1, e2]
         | none => mkAppExpr f #[args[0]!, op1, op2]
 else mkAppExpr f args

 where
   notNegEqSimp? (op1: Expr) (op2: Expr) : TranslateEnvT (Option (Expr × Expr)) := do
    match op1, toBoolNotExpr? op2, toBoolNotExpr? op1 with
    | Expr.const ``true _, some e, _ => pure (some (← mkBoolFalse, e))
    | Expr.const ``false _, some e, _ => pure (some (← mkBoolTrue, e))
    | _, some e2, some e1 => pure (some (e1, e2))
    | _, _, _ =>
      match toNotExpr? op1, toNotExpr? op2 with
      | some e1, some e2 => pure (some (e1, e2))
      | _, _ => pure none


/-- Apply the following simplification/normalization rules on `BEq.beq` :
     - false == e ==> not e
     - true == e ==> e
     - e == not e ==> false
     - e1 == e2 ==> true (if e1 =ₚₜᵣ e2)
     - not e1 == not e2 ==> e1 == e2
     - e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)

   Assume that f = Expr.const ``BEq.beq.
   This function simply returns the function application when:
     - `BEq.beq is partially applied (i.e., args.size < 4)
     - isOpaqueBeq f.constName args is not satisfied.

   NOTE: The above simplification rules are applied only on `BEq.beq` satisfiying `isOpaqueBeq` predicate.
   In fact, we can't assume that `BEq.beq` will properly be defined for user-defined types or parametric inductive types.

   NOTE: `BEq.beq` is expected to be unfolded if isOpaqueBEq predicate is not satisfied.
   However, class constraint [BEq α] for which there is no defined instance the unfolding will not be performed
   (see `getUnfoldFunDef?`).

   NOTE: Unlike `Eq there is no need to add an explicity rule for constructor operands as these
   are implicilty resolved via reduceApp.
   TODO: consider additional simplification rules
-/
partial def optimizeBEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if isOpaqueBeq f.constName args
 then
   if args.size == 4 then
     -- args[0] is sort parameter
     -- args[1] decidable instance parameter
     -- args[2] left operand
     -- args[3] right operand
     let opArgs ← reorderBoolOp #[args[2]!, args[3]!]
     let op1 := opArgs[0]!
     let op2 := opArgs[1]!
     match op1, op2 with
     | Expr.const ``false _, _ => optimizeBoolNot (← mkBoolNotOp) #[op2]
     | Expr.const ``true _, _ => pure op2
     | _, _ =>
       if (← isBoolNotExprOf op2 op1)
       then mkBoolFalse
       else if (← exprEq op1 op2) then mkBoolTrue
       else match toBoolNotExpr? op1, toBoolNotExpr? op2 with
            | some e1, some e2 => optimizeBEq f #[args[0]!, args[1]!, e1, e2]
            | _, _ => mkAppExpr f #[args[0]!, args[1]!, op1, op2]
    else mkAppExpr f args
 else mkAppExpr f args


/-- Apply simplification and normalization rules on `Eq` and \BEq.beq` :
-/
def optimizeEquality? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
     match n with
      | ``Eq => some <$> optimizeEq f args
      | ``BEq.beq => some <$> optimizeBEq f args
      | _ => pure none
 | _ => pure none
end Solver.Optimize
