import Lean
import Solver.Optimize.Rewriting.OptimizeExists
import Solver.Optimize.Rewriting.OptimizeInt
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Rewriting.OptimizeMatch
import Solver.Optimize.Rewriting.OptimizeNat
import Solver.Optimize.Env

open Lean Meta

namespace Solver.Optimize

/-- Determine if all explicit parameters of a function are constructors that
    may also contain free or bounded variables.
    Note that `false` is return when f corresponds to the internal const ``_recFun.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : MetaM Bool := do
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
 if !(← allExplicitParamsAreCtor f (← extractMatchDiscrs f args)) then return none
 let re ← whnfExpr appExpr
 if (re != appExpr) && (← (isConstant re) <||> (pure !(isOpaqueFunExpr f args || (← isClassFun f))))
 then return (some re)
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
  if let some e ← optimizePropNot? f args then return e
  if let some e ← optimizePropBinary? f args then return e
  if let some e ← optimizeBoolNot? f args then return e
  if let some e ← optimizeBoolBinary? f args then return e
  if let some e ← optimizeEquality? f args then return e
  if let some e ← optimizeIfThenElse? f args then return e
  if let some e ← optimizeNat? f args then return e
  if let some e ← optimizeInt? f args then return e
  if let some e ← structEqMatch? f args then return e
  if let some e ← optimizeExists? f args then return e
  if let some e ← optimizeDecide? f args then return e
  mkAppExpr f args


/-- Given application `f x₁ ... xₙ` perform the following:
    - when `f` corresponds to a recursive definition `λ p₁ ... pₙ → fbody` the following actions are performed:
        - When entry `f x₁ ... xₖ := fdef` exists in the instance cache and `fdef := fₙ` is in the recursive function map.
             - return `optimizeApp fₙ xₖ₊₁ ... xₙ`
        - when no entry for `f x₁ ... xₖ` exists in the instance cache:
           - fbody' ← optimizer `(λ p₁ ... pₙ → fbody[f/_recFun]) x₁ ... xₖ`
           - entry `f x₁ ... xₖ := fbody` is added to the instance cache
           - return `optimizeApp fₙ xₖ₊₁ ... xₙ` IF entry `fbody' := fₙ` exists in recursive function map and `f` is not an opaque function
           - return `optimizeApp f x₁ ... xₙ` IF entry `fbody' := fₙ` exists in recursive function map and `f` is an opaque function, with:
                - `fbody' := f x₁ ... xₖ` added to the replay recursive function map,
           - return `optimizeApp f x₁ ... xₙ`  OTHERWISE, with:
                 - `fbody' := f x₁ ... xₖ` added to the recursive function map,
        where `x₁ ... xₖ` correspond to the implicit arguments of `f` (if any).
    - when `f` is not a recursive definition or is already in the recursive visited cache.
       - return optimizeApp `f x₁ ... xₙ`.
-/
def normOpaqueAndRecFun (f : Expr) (args: Array Expr) (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT Expr := do
 match f with
 | Expr.const n _ =>
     let isOpaque := isOpaqueFun n args
     if (← isRecursiveFun n)
     then
       -- retrieve implicit arguments
       let iargs ← getImplicitArgs f args
       let instApp ← mkAppExpr f iargs
       if (← isVisitedRecFun instApp)
       then optimizeApp f args -- already cached
       else
         if let some r ← hasRecFunInst? instApp isOpaque then return (← optimizeApp r args[iargs.size : args.size])
         cacheFunName instApp -- cache function name
         let some fbody ← getFunBody f | throwError "normOpaqueAndRecFun: recursive function body expected for {n}"
         -- instantiating polymorphic parameters in fun body
         let fdef := generalizeRecCall n (Expr.beta fbody iargs)
         -- optimize recursive fun definition and store
         let fn' ← storeRecFunDef instApp (← optimizer fdef) isOpaque
         -- only considering explicit args when instantiating
         -- as storeRecFunDef already handled implicit arguments
         optimizeApp fn' args[iargs.size : args.size] -- optimizations on cached opaque recursive functions
       else optimizeApp f args -- optimizations on opaque functions
 | _ => mkAppExpr f args


end Solver.Optimize
