import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Lemmas.LemmasProp
import Blaster.Optimize.Lemmas.LemmasNat

open Lean Meta
namespace Blaster.Optimize

/-- Given `ne` the operand for `Not` apply the following normalization rules:
     - When `ne := false = e`
        - return `some (true = e, e, false)`
     - When `ne := true = e`
        - return `some (false = e, e, true)`
     - Otherwise:
        - return `none`.
-/
@[always_inline, inline]
def notEqSimp? (ne : Expr) : TranslateEnvT (Option (Expr × Expr × Bool)) := do
  match eq? ne with
  | some (eq_sort, op1, op2) =>
     match op1 with
     | Expr.const ``false _ =>
         return (← mkApp3Expr ne.getAppFn eq_sort (← mkBoolTrue) op2, op2, false)
     | Expr.const ``true _ =>
         return (← mkApp3Expr ne.getAppFn eq_sort (← mkBoolFalse) op2, op2, true)
     | _ => return none
  | none => return none

/-- Given `ne` the operand for `Not`, apply the following normalization rule:
    - When `ne := 0 < e` ∧ Type(a) = Nat:
       - return `some (0 = e)`
    - Otherwise:
       - return `none`
-/
def notLTNumNorm? (ne : Expr) (restart := true) : TranslateEnvT (Option Expr) := do
  let some (_t, _i, e1, e2) := lt? ne | return none
  if isZeroNat e1 then
    if restart then
      pushProofStep (.rewrite (mkConst ``Blaster.nat_not_zero_lt_eq_zero_eq))
      setRestart
    mkNatEqExpr e1 e2
  else return none


/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True             [proof: not_false_eq_true]
     - ¬ True ==> False             [proof: not_true_eq_false]
     - ¬ (¬ e) ==> e (classical)    [proof: Blaster.double_not_classical]
     - ¬ (false = e) ==> true = e   [proof: Blaster.not_false_is_true]
     - ¬ (true = e) ==> false = e   [proof: Blaster.not_true_is_false]
     - ¬ (0 < e) ==> (0 = e) (if Type(e) = Nat)   [proof: Blaster.nat_not_zero_lt_eq_zero_eq]
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Not` expected at this stage)
   With `restart := false` the call is a query (the result does not replace `¬ e`), hence no proof step is pushed.
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) (restart := true) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeNot: exactly one argument expected"
 let e := args[0]!
 if let Expr.const ``False _ := e then
  if restart then
    pushProofStep (.rewrite (mkConst ``not_false_eq_true))
    pushProofStep (.exact (mkConst ``True.intro))
  return (← mkPropTrue)
 if let Expr.const ``True _ := e then
  if restart then pushProofStep (.rewrite (mkConst ``not_true_eq_false))
  return (← mkPropFalse)
 if let some op := propNot? e then
  if restart then pushProofStep (.rewrite (mkConst ``Blaster.double_not_classical))
  return op
 if let some (r, _, boolLit) ← notEqSimp? e then
  -- here and not in `notEqSimp?`, which also derives hypotheses (see `addNotPropFacts`)
  if restart then
    pushProofStep (.rewrite (mkConst (if boolLit then ``Blaster.not_true_is_false else ``Blaster.not_false_is_true)))
  return r
 if let some r ← notLTNumNorm? e restart then return r
 mkAppExpr f e


/-- Given `ne` the operand for `Not` apply the following normalization rules:
     - When `ne := ¬ e1 ∧ ¬ e2`
        - return `e1 ∨ e2`
     - When `ne := ¬ e1 ∨ ¬ e2`
        - return `e1 ∧ e2`
     - Otherwise:
        - return `none`.
-/
def notLogicalSimp? (ne : Expr) (restart := true) : TranslateEnvT (Option Expr) := do
  match propAnd? ne with
  | some (ne1, ne2) => notPropagation? ne1 ne2 (← mkPropOrOp)
  | _ =>
    match propOr? ne with
    | some (ne1, ne2) => notPropagation? ne1 ne2 (← mkPropAndOp)
    | _ => return none

 where
   notPropagation? (ne1 : Expr) (ne2 : Expr) (op : Expr) : TranslateEnvT (Option Expr) := do
     match propNot? ne1, propNot? ne2 with
     | some e1, some e2 =>
           if restart then
             -- `op` is `Or` for `¬ (¬ e1 ∧ ¬ e2)` and `And` for `¬ (¬ e1 ∨ ¬ e2)`
             let lemma := if op.isConstOf ``Or then ``Blaster.not_and_not_eq_or else ``Blaster.not_or_not_eq_and
             -- applied to the operands, so that replay rewrites this site and not an enclosing match
             pushProofStep (.rewrite (mkApp2 (mkConst lemma) e1 e2))
             setRestart
           mkApp2Expr op e1 e2
     | _, _ => return none

/-- Call `optimizeNot f args` and apply the following simplification/normalization rules on `Not` :
     - ¬ (¬ e1 ∧ ¬ e2) ==> (e1 ∨ e2)   [proof: Blaster.not_and_not_eq_or]
     - ¬ (¬ e1 ∨ ¬ e2) ==> (e1 ∧ e2)   [proof: Blaster.not_or_not_eq_and]
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Not` expected at this stage)
   With `restart := false` the call is a query (the result does not replace `¬ e`), hence no proof step is pushed.
-/
def optimizeAdvancedNot (f : Expr) (args : Array Expr) (restart := true) : TranslateEnvT Expr := do
  let e ← optimizeNot f args restart
  let some ne := propNot? e | return e
  if let some r ← notLogicalSimp? ne restart then return r
  return e


/-- Apply simplification and normalization rules on proposition `Not` formulae. -/
def optimizePropNot? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  match f with
  | Expr.const ``Not _ => optimizeAdvancedNot f args
  | _ => return none

end Blaster.Optimize
