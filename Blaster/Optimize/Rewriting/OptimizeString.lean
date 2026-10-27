import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env

open Lean Meta
namespace Blaster.Optimize

/-- Return `true` when `e` corresponds to the null string literal. -/
def isNullString (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.strVal "") => true
  | _ => false

/-- Normalize `String.ofList (List.cons c₁ (.. (List.cons cₙ List.nil)))` to `Expr.lit (Literal.strVal s)`
    only when the list of chars are constant values.
    Otherwise return `(mkApp f args[0]!)`.
    Assume that `f := Expr.const ``String.ofList.
    An error is triggered when args.size ≠ 1.
-/
def normStringValue (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "normStringValue: only one argument expected"
  let op := args[0]!
  if let Expr.app (Expr.const ``String.toList _) str := op then return str
  let some elms := getListChars? op | return ← mkAppExpr f op
  mkStrLitExpr (String.ofList elms)

  where
    getListChars? (e : Expr) : Option (List Char) :=
      let rec visit (e : Expr) (acc : List Char) : Option (List Char) :=
        match e with
        | Expr.app (Expr.const ``List.nil _) _ => some (List.reverse acc)
        | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) a) as =>
            if let some c := isCharValue? a
            then visit as (c :: acc)
            else none
        | _ => none
      visit e []


/-- Apply the following simplification/normalization rules on `String.append` :
     - S1 ++ S2 ==> S1 "++" S2
     - "" ++ e | e ++ "" ==> e
   Assume that f = Expr.const ``String.append.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `String.append` expected at this stage)
-/
def optimizeStrAppend (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeStrAppend: exactly two arguments expected"
 -- args[0] left operand
 -- args[1] right operand
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← cstStrAppend? op1 op2 then return r
 if let some r ← appendNull? op1 op2 then return r
 mkApp2Expr f op1 op2

 where
   /-- Given `op1` and `op2` corresponding to the operands for `String.append`
       return `some (S1 "++" S2)` when `op1 := S1 ∧ op2 := S2`.
       Otherwise `none`.
   -/
   cstStrAppend? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
    match op1, op2 with
    | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => mkStrLitExpr (s1 ++ s2)
    | _, _ => return none

   /-- Given `op1` and `op2` corresponding to the operands for `String.append`,
        - return `some op2` when op1 := ""`.
       - return `some op1` when op2 := ""`
       Otherwise `none`.
   -/
   appendNull? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     if isNullString op1 then return op2
     if isNullString op2 then return op1
     return none

/-- Apply the following simplification/normalization rules on `String.length` :
     - String.length S ==> "String.length" S
   Assume that f = Expr.const ``String.length.
   An error is triggered when args.size ≠ 1 (i.e., only fully applied `String.length` expected at this stage)
-/
def optimizeStrLength (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeStrLength: exactly one arguments expected"
 let op := args[0]!
 if let Expr.app (Expr.const ``String.ofList _) chars := op then
   setRestart
   return ← mkApp2Expr (← mkExpr (mkConst ``List.length [Level.zero])) (← mkCharType) chars
 if let some r ← cstStrLength? op then return r
 mkAppExpr f op

 where
   /-- Given `op` corresponding to the operand for `String.length`
       return `some ("String.length" S)` when `op := S`.
       Otherwise `none`.
   -/
   cstStrLength? (op : Expr) : TranslateEnvT (Option Expr) := do
    match op with
    | Expr.lit (Literal.strVal s) => mkNatLitExpr (String.length s)
    | _ => return none

/-- Specialize only the standard String-pattern/String-replacement searcher.
    All implicit parameters are compared with the native wrapper, so user-supplied
    iterator/searcher instances cannot silently acquire standard SMT semantics. -/
def normStringReplace (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let params := (← getFunEnvInfo f).paramsInfo
  unless args.size == params.size do
    throwEnvError "String.replace: fully applied standard string replacement expected"
  let explicitArgs := (args.zip params).filterMap fun (arg, param) =>
    if param.isExplicit then some arg else none
  let #[source, pattern, replacement] := explicitArgs
    | throwEnvError "String.replace: expected source, pattern and replacement arguments"
  let .defnInfo info ← getConstEnvInfo ``Blaster.stringReplace
    | throwEnvError "String.replace: standard wrapper definition expected"
  let canonical := info.value.beta explicitArgs
  let expected := canonical.getAppArgs
  unless canonical.getAppFn' == f && expected.size == args.size do
    throwEnvError "String.replace: only the standard String pattern and String replacement instances are supported"
  for ((actual, standard), param) in (args.zip expected).zip params do
    if !param.isExplicit then
      unless ← isDefEq actual standard do
        throwEnvError "String.replace: only the standard String pattern and String replacement instances are supported"
  setRestart
  mkApp3Expr (← mkExpr (mkConst ``Blaster.stringReplace)) source pattern replacement

/-- Constant propagation for the monomorphic standard replacement wrapper.
    Unlike SMT str.replace_all, Lean inserts the replacement at character boundaries
    for an empty pattern. Translation handles that branch separately. -/
def optimizeStrReplace (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let #[s, pattern, replacement] := args
    | throwEnvError "optimizeStrReplace: exactly three arguments expected"
  if exprEq pattern replacement then return s
  match isStrValue? s, isStrValue? pattern, isStrValue? replacement with
  | some source, some pattern, some replacement => mkStrLitExpr (source.replace pattern replacement)
  | _, _, _ => mkApp3Expr f s pattern replacement

/-- Observe constant slices through their copied string without replacing the slice
    structure itself: structural Slice equality and copied-text equality differ. -/
def sliceString? (e : Expr) : Option String :=
  match e with
  | .app (.const ``String.toSlice _) (.lit (.strVal s)) => some s
  | .app (.app (.const ``String.take _) (.lit (.strVal s))) (.lit (.natVal n)) =>
      some (s.take n).copy
  | .app (.app (.const ``String.drop _) (.lit (.strVal s))) (.lit (.natVal n)) =>
      some (s.drop n).copy
  | _ => none

def optimizeSliceCopy (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let #[slice] := args | throwEnvError "Slice.copy: exactly one argument expected"
  if let some s := sliceString? slice then return ← mkStrLitExpr s
  mkAppExpr f slice

def optimizeSliceBeq (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let #[left, right] := args | throwEnvError "Slice.beq: exactly two arguments expected"
  match sliceString? left, sliceString? right with
  | some s, some t => mkBoolLit (s == t)
  | _, _ => mkApp2Expr f left right

/-- Normalize the public list view, using `String.toList_ofList` and literals.
    These rewrites preserve Unicode scalar values rather than exposing UTF-8 bytes. -/
def optimizeStrToList (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "optimizeStrToList: exactly one argument expected"
  if let some chars ← stringListView? args[0]! then return chars
  mkAppExpr f args[0]!

/-- Apply simplification/normalization rules on `String` operators. -/
def optimizeString? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
 | ``String.ofList => normStringValue f args
 | ``String.toList => optimizeStrToList f args
 | ``String.append => optimizeStrAppend f args
 | ``String.length => optimizeStrLength f args
 | ``String.replace => normStringReplace f args
 | ``Blaster.stringReplace => optimizeStrReplace f args
 | ``String.Slice.copy => optimizeSliceCopy f args
 | ``String.Slice.beq => optimizeSliceBeq f args
 | _ => return none

end Blaster.Optimize
