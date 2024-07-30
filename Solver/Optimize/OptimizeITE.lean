import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Given expression `ite s c d t e` and considering `x` and `y` as the
    last two parameters for the ITE decidable instance `d`, perform the following:
     - set `x` to `e1` and `y` to `e2` only when `y` =ₚₜᵣ `e1` and `x` =ₚₜᵣ `e2` and `c := e1 = e2`
     - add the new decidable instance in cache if required
     - return the new ite instance as result.
-/
def adjustDecidableITEInst (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 match isEqExpr? args[1]! with
 | some eq_args =>
    match args[2]! with
    | d@(Expr.app ..) =>
       Expr.withApp d fun df d_args => do
        -- replacing only last two operands when required
       let d_size := d_args.size
       if (← (exprEq eq_args.1 d_args[d_size - 1]!) <&&> (exprEq eq_args.2 d_args[d_size - 2]!))
       then do
         let d_args' := d_args.swap! (d_size - 2) (d_size - 1)
         -- check if decidable instance is already in cache
         let d' ← mkExpr (mkAppN df d_args')
         pure (mkAppN f (args.set! 2 d'))
       else pure (mkAppN f args)
    | _ => throwError "adjustDecidableITEInst: Expr.app expected as decidable instance"
 | none => pure (mkAppN f args)


/-- Apply the following simplification/normalization rules on `ite` :
     - if True then e1 else e2 ===> e1
     - if False then e1 else e2 ===> e2
     - if c then e1 else e2 ===> if c' then e2 else e1 (if c := ¬ c')
     - if c then e1 else e2 ===> if true = c' then e2 else e1 (if c := false = c') (TODO)
     - if c then e1 else e2 ===> e1 (if e1 =ₚₜᵣ e2)
     - if c then e1 else e2 ===> (c ∧ e1) ∨ (¬ c ∧ e2) (if Type(e1) = Prop) TODO
     - if c then e1 else e2 ===> (c && e1) || (not c && e2) (if Type(e1) = Bool) TODO
   Assume that f = Expr.const ``ite
   An error is triggered if args.size ≠ 5.
   TODO: consider additional simplification rules.
-/
partial def optimizeITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 5 then
   -- args[0] is sort parmeter
   -- args[1] is cond operand
   -- args[2] is decidable instance parameter on cond
   -- args[3] is then operand
   -- args[4] is else operand
   let c := args[1]!
   let t := args[3]!
   let e := args[4]!
   match c with
   | Expr.const ``True _ => pure t
   | Expr.const ``False _ => pure e
   | Expr.app (Expr.const ``Not _) ne =>
        let args' := args.set! 1 ne
        optimizeITE f (args'.swap! 3 4)
   | _ =>
     if (← exprEq t e)
     then pure t
     else adjustDecidableITEInst f args
 else throwError "optimizeITE: five arguments for ITE"


/-- Given an expression of the form `fun h : c => e` return `e` as result.
   An error is triggered when:
     - the provided expression is not a `then` or `else` dependent ite expression,
       i.e., not a lambda expression of the form `fun h : c => e`; or
     - the lambda type does not satisfy the provided predicate optPred.
-/
def extractDependentITEExpr (e : Expr) (optPred : Option (Expr -> Bool)) : MetaM Expr :=
  match e with
  | Expr.lam _n t b _bi =>
      match optPred with
      | some f =>
        if f t
        then pure b
        else throwError f!"extractDependentITEExpr: unexpected lambda type - got {reprStr t}"
      | none => pure b
  | _ => throwError f!"extractDependentITEExpr: lambda expression expected but got {reprStr e}"

/-- Apply simplification/normalization rules on `dite`.
    Note that dependent ite is written via notation `if h : c then t else e` is a
    syntactic sugar for `dite c (fun h : c => t) (fun h : ¬ c => e)`.

    The simplifcation/normalization rules applied are:
     - `dite True (fun h : True => e1) (fun h : False => e2)` ===> e1
     - `dite False (fun h : True => e1) (fun h : False => e2)` ===> e2
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ===> `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ===> `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ===> e1 (if e1 =ₚₜᵣ e2)
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ===> (c ∧ e1) ∨ (¬ c ∧ e2) (if Type(e1) = Prop) TODO
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ===> (c && e1) || (not c && e2) (if Type(e1) = Bool) TODO
    Assume that f = Expr.const ``dite
    An error is triggered if args.size ≠ 5.
    TODO: consider additional simplification rules.
-/
partial def optimizeDITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 5 then
   -- args[0] is sort parmeter
   -- args[1] is cond operand
   -- args[2] is decidable instance parameter on cond
   -- args[3] is then operand
   -- args[4] is else operand
   let c := args[1]!
   let t := args[3]!
   let e := args[4]!
   match c with
   | Expr.const ``True _ => extractDependentITEExpr t (some Expr.isTrue)
   | Expr.const ``False _ => extractDependentITEExpr t (some Expr.isFalse)
   | Expr.app (Expr.const ``Not _) ne =>
        let args' := args.set! 1 ne
        optimizeITE f (args'.swap! 3 4)
   | _ =>
     if (← exprEq t e)
     then extractDependentITEExpr t none
     else adjustDecidableITEInst f args
 else throwError "optimizeDITE: five arguments for DITE"


/-- Apply simplification/normalization rules of if then else expressions. -/
def optimizeIfThenElse (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
  | Expr.const n _ =>
     match n with
     | ``ite => some <$> optimizeITE f args
     | ``dite => some <$> optimizeDITE f args
     | _ => pure none
  | _ => pure none

end Solver.Optimize
