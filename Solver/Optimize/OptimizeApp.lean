import Lean
import Solver.Optimize.OptimizeBool
import Solver.Optimize.OptimizeEq
import Solver.Optimize.OptimizeInt
import Solver.Optimize.OptimizeITE
import Solver.Optimize.OptimizeMatch
import Solver.Optimize.OptimizeNat
import Solver.Optimize.OptimizeProp
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Determine if all explicit parameters of a function are constructors that
    may also contain free or bounded variables.
    Note that `false` is return when f corresponds to the internal const ``_recFun.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : MetaM Bool := do
  if isRecFunInternalExpr f
  then return false
  else
    let stop := args.size
    let fInfo ← getFunInfoNArgs f stop
    let rec loop (i : Nat) (atLeastOneExplicit : Bool := false) : MetaM Bool := do
      if i < stop then
        let e := args[i]!
        let aInfo := fInfo.paramInfo[i]!
        if aInfo.isExplicit
        then if (← isConstructor e)
             then loop (i+1) true
             else pure false
        else loop (i+1) atLeastOneExplicit
      else pure atLeastOneExplicit
    loop 0


/-- Try to reduce application `f args` when all explicit parameters are constructors.
    The reduced expression `re` is returned only when re != `f args` and one of the following conditions is satisfied:
      - `re` is a constructor that does not contain any variable; or
      - f is not an opaque function or a class function.
    NOTE: The explicit parameters in `args` are reduced to `match` discriminators when `f args` is a `match` application.
    NOTE: `reduceApp` will not be applied on a class function. This is so to avoid implicit opaque function reduction.
    NOTE: `whnf` will not perform any reduction on ``Prop operators (e.g. ``Eq, ``And, ``Or, ``Not, etc).
-/
def reduceApp? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 let appExpr := mkAppN f args
 if (← allExplicitParamsAreCtor f (← extractMatchDiscrs f args))
 then
   let re ← whnfExpr appExpr
   if (re != appExpr) && (← (isConstant re) <||> (pure !(isOpaqueFunExpr f args || (← isClassFun f))))
   then return (some re)
   else return none
 else return none

 where
   /- Extract match discriminators from `args` only when `f args` corresponds
     to a `match` application expression.
     Concretely given a match expression of the form:
        match e₁, ..., eₙ with
        | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
        ...
        | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     Extracts e₁, ..., eₙ from `args`.
     When `f args` does not correspond to a match expression `args` is returned by default.
   -/
   extractMatchDiscrs (f : Expr) (args: Array Expr) : MetaM (Array Expr) := do
     match f with
     | Expr.const n _ =>
         let some matcherInfo ← getMatcherInfo? n | return args
         let discrs := args[matcherInfo.getFirstDiscrPos : matcherInfo.getFirstAltPos]
         return discrs
     | _ => return args

/-- Perform constant propagation and apply simplifcation and normalization rules
    on application expressions.
-/
def optimizeApp (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  if let some e ← optimizeProp? f args then return e
  if let some e ← optimizeBool? f args then return e
  if let some e ← optimizeEquality? f args then return e
  if let some e ← optimizeIfThenElse? f args then return e
  if let some e ← optimizeNat? f args then return e
  if let some e ← optimizeInt? f args then return e
  if let some e ← structEqMatch? f args then return e
  mkAppExpr f args

end Solver.Optimize
