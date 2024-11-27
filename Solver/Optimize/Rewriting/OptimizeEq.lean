import Lean
import Solver.Optimize.Rewriting.OptimizeBoolNot
import Solver.Optimize.Rewriting.OptimizePropNot

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
     | Expr.app .., Expr.const ..
     | Expr.const .., Expr.app .. => visit op1.getAppFn' op2.getAppFn'
     | _, _ =>
       -- return `none` for all other cases if physically equality fails
       pure none
 if (← exprEq op1 op2) then return (some true)
 visit op1 op2

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
     - e1 = e2 ==> False (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜᵣ)
     - true = not e ==> false = e
     - false = not e ==> true = e
     - ¬ e1 = ¬ e2 ==> e1 = e2 (require classical)
     - not e1 = not e2 ==> e1 = e2
     - e1 = e2 ==> e2 = e1 (if e2 <ₒ e1)

   Assume that f = Expr.const ``Eq.
   Do nothing if operator is partially applied (i.e., args.size < 3)
   NOTE: The `reduceApp` rule will not reduce any `Prop` operator (e.g., `Eq`) applied to constructors only.

   TODO: consider additional simplification rules
   TODO: seperate rewriting that require classical reasoning from others.
   TODO: add an option to activate/deactivate classical simplification (same for optimizeProp).
-/
partial def optimizeEq (f : Expr) (args: Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 3 then return (← mkAppExpr f args)
 -- args[0] is sort parameter
 -- args[1] left operand
 -- args[2] right operand
 let opArgs ← reorderPropOp #[args[1]!, args[2]!]
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _ := op1 then return (← optimizeNot (← mkPropNotOp) #[op2])
 if let Expr.const ``True _ := op1 then return op2
 if (← (isNotExprOf op2 op1) <||> (isBoolNotExprOf op2 op1)) then return (← mkPropFalse)
 if (← exprEq op1 op2) then return (← mkPropTrue)
 if let some false ← structEq? op1 op2 then return (← mkPropFalse)
 if let some (e1, e2) ← notNegEqSimp? op1 op2 then return (← optimizeEq f #[args[0]!, e1, e2] cacheResult)
 mkExpr (mkApp3 f args[0]! op1 op2) cacheResult

 where
   /- Given `op1` and `op2` corresponding to the operands for `Eq,
      - return `some (false, e)` when `op1 := true ∧ op2 := not e`
      - return `some (true, e)` when `op1 := false ∧ op2 := not e`
      - return `some (e1, e2)` when `op1 := not e1 ∧ op2 := not e2`
      - return `some (e1, e2)` when `op1 := ¬ e1 ∧ op2 := ¬ e2`
      Otherwise `none`.
   -/
   notNegEqSimp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
    match op1, boolNot? op2, boolNot? op1 with
    | Expr.const ``true _, some e, _ => return some (← mkBoolFalse, e)
    | Expr.const ``false _, some e, _ => return (some (← mkBoolTrue, e))
    | _, some e2, some e1 => return (some (e1, e2))
    | _, _, _ =>
      match propNot? op1, propNot? op2 with
      | some e1, some e2 => return (some (e1, e2))
      | _, _ => return none

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
 if !(isOpaqueBeq f.constName args) then return (← mkAppExpr f args)
 if args.size != 4 then return (← mkAppExpr f args)
 -- args[0] is sort parameter
 -- args[1] decidable instance parameter
 -- args[2] left operand
 -- args[3] right operand
 let opArgs ← reorderBoolOp #[args[2]!, args[3]!]
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``false _ :=  op1 then return (← optimizeBoolNot (← mkBoolNotOp) #[op2])
 if let Expr.const ``true _ := op1 then return op2
 if (← isBoolNotExprOf op2 op1) then return (←  mkBoolFalse)
 if (← exprEq op1 op2) then return (← mkBoolTrue)
 if let (some e1, some e2) := (boolNot? op1, boolNot? op2) then return (← optimizeBEq f #[args[0]!, args[1]!, e1, e2])
 mkExpr (mkApp4 f args[0]! args[1]! op1 op2)


mutual
 /- Given `e` of type `Bool`, return `b = e` on which simplifications
      rules on Eq are applied.
 -/
partial def mkEqBool (e : Expr) (b : Bool) : TranslateEnvT Expr := do
  let boolLit ← if b then mkBoolTrue else mkBoolFalse
  optimizeDecideEq (← mkEqOp) #[← mkBoolType, boolLit, e]

/- Call `optimizeEq f args` and apply the following `decide` simplification/normalization
   rules on the resulting `Eq` expression (if any):
     - true = (a == b) ==> a = b (if isCompatibleBeqType Type(a))
     - false = (a == b) ==> ¬ (a = b) (if isCompatibleBeqType Type(a))
     - c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if isCompatibleBeqType Type(a))
     - (B1 = a) = (B2 = b) ==> NOP(B1, a) = NOP(B2, b)
     - true = decide e ==> e
     - false = decide e ==> ¬ e
     - decide e1 = decide e2 ==> e1 = e2
     - decide e1 = e2 | e2 = decide e1 ===> e1 = (true = e2)

   with NOP(B, e) := e  if B
                  := !e otherwise

   Assume that f = Expr.const ``Eq.

   - TODO: may be we need to reverse the following simplification rules to maximize equivalence
      - true = (a == b) ==> a = b (if isCompatibleBeqType Type(a))
      - false = (a == b) ==> ¬ (a = b) (if isCompatibleBeqType Type(a))
      - c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if isCompatibleBeqType Type(a))
        This rule will not more be required if the two above rules are reversed.
      - The revering is essential to hanlde example like "EqBoolAndEqBoolUnchanged_7"

-/
partial def optimizeDecideEq (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeEq f args (cacheResult := false)
 let some (_, op1, op2) := e.eq? | return e
 if let some r ← beqToEq? op1 op2 then return r
 if let some r ← boolEqtoEq? op1 op2 then return r
 if let some r ← decideBoolEqSimp? op1 op2 then return r
 if let some r ← decideEqDecide? op1 op2 then return r
 mkExpr e

 where
   isBeqCompatibleType? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
     match beq? e with
     | r@(some (beq_sort, _, _, _)) =>
         if isCompatibleBeqType beq_sort then r else none
     | _ => none

   mkBeqToEq (beq_sort : Expr) (beq_op1 : Expr) (beq_op2 : Expr) (c : Expr) : TranslateEnvT Expr := do
      let op1Expr ← optimizeDecideEq f #[← mkBoolType, ← mkBoolTrue, c]
      let op2Expr ← optimizeDecideEq f #[beq_sort, beq_op1, beq_op2]
      optimizeDecideEq f #[← mkPropType, op1Expr, op2Expr]


   /- Given `op1` and `op2` corresponding to the operands for `Eq,
      - return `some (a = b)` when `op1 := true ∧ op2 := a == b ∧ `isCompatibleBeqType Type(a)`
      - return `some ¬ (a = b)` when `op1 := false ∧ op2 := a == b ∧ `isCompatibleBeqType Type(a)`
      - return `some (true = c) = (a = b)` when `op1 := c ∧ op2 := a == b ∧ `isCompatibleBeqType Type(a)`
      - return `some (true = c) = (a = b)` when `op1 := a == b ∧ op2 := c ∧ `isCompatibleBeqType Type(a)`
      Otherwise `none`.
   -/
   beqToEq? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match isBoolValue? op1 with
    | some bv =>
      match isBeqCompatibleType? op2 with
      | some (beq_sort, _, beq_op1, beq_op2) =>
          let eqExpr ← optimizeDecideEq f #[beq_sort, beq_op1, beq_op2]
          if bv then return some eqExpr -- return when bv = true
          some <$> mkExpr (mkApp (← mkPropNotOp) eqExpr)
      | _ => return none
    | none =>
       match isBeqCompatibleType? op1, isBeqCompatibleType? op2 with
         | some (beq_sort, _, beq_op1, beq_op2), _ =>
            some <$> mkBeqToEq beq_sort beq_op1 beq_op2 op2
         | _, some (beq_sort, _, beq_op1, beq_op2) =>
            some <$> mkBeqToEq beq_sort beq_op1 beq_op2 op1
         | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq,
      return `some NOP(B1, e1) = NOP(B2, e2)` only when
      `op1 := B1 = e1 ∧ op2 := B2 = e2`.
      Otherwise `none`.
   -/
   boolEqtoEq? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match op1.eq?, op2.eq? with
    | some (eq_sort, a_op1, a_op2), some (_, b_op1, b_op2) =>
       match isBoolValue? a_op1, isBoolValue? b_op1 with
       | some bv1, some bv2 => do
          some <$> optimizeDecideEq f #[eq_sort, (← toBoolNotExpr? bv1 a_op2), (← toBoolNotExpr? bv2 b_op2)]
       | _, _ => return none
    | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq,
       - return `some e` when `op1 := true ∧ op2 := decide e`
       - return `some ¬ e` when `op1 := false ∧ op2 := decide e`
      Otherwise `none`.
   -/
   decideBoolEqSimp? (op1: Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match op1, decide? op2 with
    | Expr.const ``true _, some (e, _d) => return some e
    | Expr.const ``false _, some (e, _d) => some <$> optimizeNot (← mkPropNotOp) #[e]
    | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq,
       - return `some e1 = e2` when `op1 := decide e1 ∧ op2 = decide e2`
       - return `some e1 = (true = e2)` when `op1 := decide e1 ∧ op2 := e2`
       - return `some e1 = (true = e2)` when `op1 := e2 ∧ op2 := decide e1`
      Otherwise `none`.
   -/
   decideEqDecide? (op1: Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match decide? op1, decide? op2 with
     | some (e1, _), some (e2, _) =>
         some <$> optimizeDecideEq (← mkEqOp) #[← mkPropType, e1, e2]
     | some (e1, _), _ =>
         some <$> optimizeDecideEq (← mkEqOp) #[← mkPropType, e1, ← mkEqBool op2 true]
     | _, some (e1, _) =>
         some <$> optimizeDecideEq (← mkEqOp) #[← mkPropType, e1, ← mkEqBool op1 true]
     | _, _ => return none
end

/-- Apply simplification and normalization rules on `Eq` and `BEq.beq` :
-/
def optimizeEquality? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 match f with
 | Expr.const n _ =>
     match n with
      | ``Eq => some <$> optimizeDecideEq f args
      | ``BEq.beq => some <$> optimizeBEq f args
      | _ => pure none
 | _ => pure none


end Solver.Optimize
