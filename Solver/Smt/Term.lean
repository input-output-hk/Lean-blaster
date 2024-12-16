import Lean
import Solver.Command.Options
import Solver.Smt.Syntax

open Lean Meta

namespace Solver.Smt

/-! ## Lean Inductive types having an Smt counterpart -/

/-! Create a reserve smt symbol for `s` -/
def mkReservedSymbol (s : String) : SmtSymbol := .ReservedSymbol s

/-! Create a normal smt symbol for `s` -/
def mkNormalSymbol (s : String) : SmtSymbol := .NormalSymbol s

/-! ## Builtin Smt sort names. -/

/-! Smt Int symbol. -/
def intSymbol : SmtSymbol := mkReservedSymbol "Int"

/-! Smt Bool symbol. -/
def boolSymbol : SmtSymbol := mkReservedSymbol "Bool"

/-! Smt String symbol. -/
def stringSymbol : SmtSymbol := mkReservedSymbol "String"

/-! Smt Nat symbol. -/
def natSymbol : SmtSymbol := mkReservedSymbol "Nat"

/-! Smt Empty symbol. -/
def emptySymbol : SmtSymbol := mkReservedSymbol "Empty"

/-! Smt PEmpty symbol. -/
def pemptySymbol : SmtSymbol := mkReservedSymbol "PEmpty"

/-! Smt universal type symbol. -/
def typeSymbol : SmtSymbol := mkReservedSymbol "@@Type"


/-! ## Builtin Smt sorts. -/

/-! Smt Int Sort. -/
def intSort : SortExpr := .SymbolSort intSymbol

/-! Smt Bool Sort. -/
def boolSort : SortExpr := .SymbolSort boolSymbol

/-! Smt String Sort. -/
def stringSort : SortExpr := .SymbolSort stringSymbol

/-! Smt Array Sort -/
def arraySort (args: Array SortExpr) : SortExpr :=
  .ParamSort (mkReservedSymbol "Array") args

/-! Smt Nat Sort.
    NOTE: This sort is defined during translation whenever required.
    (see function `defineNatSort`)
-/
def natSort : SortExpr := .SymbolSort natSymbol

/-! Smt Empty Sort.
    NOTE: This sort is declared during translation whenever required.
    (see function `defineEmptySort`)
-/
def emptySort : SortExpr := .SymbolSort emptySymbol

/-! Smt PEmpty Sort.
    NOTE: This sort is declared during translation whenever required.
    (see function `definePEmptySort`)
-/
def pemptySort : SortExpr := .SymbolSort pemptySymbol

/-! Smt @@Type Sort used to denote universal sort
    NOTE: This sort is declared during translation whenever required.
    (see function `defineTypeSort`).
-/
def typeSort : SortExpr := .SymbolSort typeSymbol

-- TODO: add other sort once supported, e.g., BitVec, Unicode (for char), Seq, etc


/-! ## Builtin Smt symbols. -/

/-! equality Smt symbol. -/
def eqSymbol : SmtSymbol := mkReservedSymbol "="

/-! Boolean `not` Smt symbol -/
def notSymbol : SmtSymbol := mkReservedSymbol "not"

/-! Boolean `and` Smt symbol. -/
def andSymbol : SmtSymbol := mkReservedSymbol "and"

/-! Boolean `or` Smt symbol. -/
def orSymbol : SmtSymbol := mkReservedSymbol "or"

/-! Implies Smt symbol. -/
def impSymbol : SmtSymbol := mkReservedSymbol "=>"

/-! Integer addition Smt symbol. -/
def addSymbol : SmtSymbol := mkReservedSymbol "+"

/-! Integer subtraction Smt symbol. -/
def subSymbol : SmtSymbol := mkReservedSymbol "-"

/-! Integer multiplication Smt symbol. -/
def mulSymbol : SmtSymbol := mkReservedSymbol "*"

/-! Integer native Smt division symbol. -/
def divSymbol : SmtSymbol := mkReservedSymbol "div"

/-! Integer native Smt modulo symbol. -/
def modSymbol : SmtSymbol := mkReservedSymbol "mod"

/-! Integer Euclidean division Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def edivSymbol : SmtSymbol := mkReservedSymbol "Int.ediv"

/-! Integer Euclidean modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def emodSymbol : SmtSymbol := mkReservedSymbol "Int.emod"

/-! Integer truncate division Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tdivSymbol : SmtSymbol := mkReservedSymbol "Int.div"

/-! Integer truncate modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tmodSymbol : SmtSymbol := mkReservedSymbol "Int.mod"

/-! Integer floor division Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fdivSymbol : SmtSymbol := mkReservedSymbol "Int.fdiv"

/-! Integer floor modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fmodSymbol : SmtSymbol := mkReservedSymbol "Int.fmod"

/-! Integer to Nat Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def toNatSymbol : SmtSymbol := mkReservedSymbol "Int.toNat"

/-! Integer cast Smt symbol.
    NOTE: Only available in z3.
    This cast function is mainly used as a wrapper around power to
    to only handle positive exponentiation.
    Indeed, negative exponentiation can lead to a Real representation,
    which cannot be the case for Lean4 pow for both Int and Nat.
-/
def toIntSymbol : SmtSymbol := mkReservedSymbol "to_int"

/-! Native integer power Smt symbol. -/
def powSymbol : SmtSymbol := mkReservedSymbol "^"

/-! Integer power Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def intPowSymbol : SmtSymbol := mkReservedSymbol "Int.pow"

/-! Nat subtraction Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def natSubSymbol : SmtSymbol := mkReservedSymbol "Nat.sub"

/-! Integer absolute Smt symbol. -/
def absSymbol : SmtSymbol := mkReservedSymbol "abs"

/-! less than Smt symbol. -/
def ltSymbol : SmtSymbol := mkReservedSymbol "<"

/-! less than or equal to Smt symbol. -/
def leqSymbol : SmtSymbol := mkReservedSymbol "<="

/-! if-then-else Smt symbol. -/
def iteSymbol : SmtSymbol := mkReservedSymbol "ite"

/-! underscore Smt symbol. -/
def underSymbol : SmtSymbol := mkReservedSymbol "_"

/-! select Smt symbol. -/
def selectSymbol : SmtSymbol := mkReservedSymbol "select"

/-! as-array Smt symbol. -/
def asArraySymbol : SmtSymbol := mkReservedSymbol "as-array"

/-! less than Smt symbol for String. -/
def strLtSymbol : SmtSymbol := mkReservedSymbol "str.<"

/-! less than or equal to Smt symbol for String. -/
def strLeqSymbol : SmtSymbol := mkReservedSymbol "str.<="

/-! append Smt symbol for String. -/
def strAppendSymbol : SmtSymbol := mkReservedSymbol "str.++"

/-! replace Smt symbol for String.
    NOTE: Unlike the replace Lean4 function, this function only
    replaces the first occurrence of `src` by `dst` in `s`.
    The equivalent function for Lean4 is `str.replace_all`
-/
def strReplaceSymbol : SmtSymbol := mkReservedSymbol "str.replace"

/-! replace all Smt symbol for String. -/
def strReplaceAllSymbol : SmtSymbol := mkReservedSymbol "str.replace_all"

/-! length Smt symbol for String. -/
def strLengthSymbol : SmtSymbol := mkReservedSymbol "str.length"

/-! ## Builtin Smt functions. -/

/-! Create an Smt application term with function name `nm` and parameters `args`. -/
def mkSmtAppN (nm : SmtQualifiedIdent) (args : Array SmtTerm) : SmtTerm := .AppTerm nm args

/-! Same as mkSmtAppN but accepts an Smt symbol as function name. -/
def mkSimpleSmtAppN (nm : SmtSymbol) (args : Array SmtTerm) : SmtTerm :=
  mkSmtAppN (.SimpleIdent nm) args

/-! Create an Equality Smt application -/
def eqSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN eqSymbol #[op1, op2]

/-! Create an Boolean `not` Smt application -/
def notSmt (op : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN notSymbol #[op]

/-! Create an Boolean `and` Smt application -/
def andSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN andSymbol #[op1, op2]

/-! Create an Boolean `or` Smt application -/
def orSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN orSymbol #[op1, op2]

/-! Create an Implies Smt application -/
def impliesSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN impSymbol #[op1, op2]

/-! Create an Integer addtion Smt application -/
def addSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN addSymbol #[op1, op2]

/-! Create an Integer subtraction Smt application -/
def subSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN subSymbol #[op1, op2]


/-! Create an Integer multiplication Smt application -/
def mulSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN mulSymbol #[op1, op2]

/-! Create an Integer native division Smt application -/
def divSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN divSymbol #[op1, op2]

/-! Create an Integer native modulo Smt application -/
def modSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN modSymbol #[op1, op2]

/-! Create an Integer negation Smt application -/
def negSmt (op : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN subSymbol #[op]

/-! Create an Integer Euclidean division Smt application. -/
def edivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN edivSymbol #[op1, op2]

/-! Create an Integer Euclidean modulo Smt application. -/
def emodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN emodSymbol #[op1, op2]

/-! Create an Integer truncate division Smt application. -/
def tdivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN tdivSymbol #[op1, op2]

/-! Create an Integer truncate modulo Smt application. -/
def tmodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN tmodSymbol #[op1, op2]


/-! Create an Integer floor division Smt application. -/
def fdivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN fdivSymbol #[op1, op2]

/-! Create an Integer floor modulo Smt application. -/
def fmodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN fmodSymbol #[op1, op2]

/-! Create an Integer to Nat Smt conversion. -/
def toNatSmt (op : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN toNatSymbol #[op]

/-! Create a native Integer power Smt application. -/
def powSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN toIntSymbol #[mkSimpleSmtAppN powSymbol #[op1, op2]]

/-! Create an Integer power Smt application. -/
def intPowSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN intPowSymbol #[op1, op2]

/-! Create a Nat subtraction Smt application -/
def natSubSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN natSubSymbol #[op1, op2]

/-! Create a Nat division Smt application.
    NOTE: This is an alias to Int.ediv at Smt level.
-/
def natDivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  edivSmt op1 op2

/-! Create a Nat modulo Smt application.
    NOTE: This is an alias to Int.emod at Smt level.
-/
def natModSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  emodSmt op2 op1

/-! Create an Nat power Smt application.
    NOTE: This is an alias to Int.pow at Smt level.
-/
def natPowSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  intPowSmt op1 op2

/-! Create an Integer absolute Smt application. -/
def absSmt (op : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN absSymbol #[op]


/-! Create a less than Smt application. -/
def ltSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN ltSymbol #[op1, op2]

/-! Create a less than or equal to Smt application. -/
def leqSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN leqSymbol #[op1, op2]


/-! Create an if-then-else Smt application. -/
def iteSmt (c : SmtTerm) (t : SmtTerm) (e : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN iteSymbol #[c, t, e]

/-! Create a String less than Smt application. -/
def strLtSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strLtSymbol #[op1, op2]

/-! Create a String less than or equal to Smt application. -/
def strLeqSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strLeqSymbol #[op1, op2]

/-! Create a String append Smt application. -/
def strAppendSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strAppendSymbol #[op1, op2]

/-! Create a String replace Smt application. -/
def strReplaceSmt (s : SmtTerm) (src : SmtTerm) (dst : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strReplaceSymbol #[s, src, dst]

/-! Create a String replace all Smt application. -/
def strReplaceAllSmt (s : SmtTerm) (src : SmtTerm) (dst : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strReplaceAllSymbol #[s, src, dst]

/-! Create a String length Smt application. -/
def strLengthSmt (s : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN strLengthSymbol #[s]


/-! Create an as-array Smt application (i.e., converting a function to an array representation). -/
def asArraySmt (f : SmtQualifiedIdent) : SmtTerm :=
  mkSimpleSmtAppN underSymbol #[.SmtIdent (.SimpleIdent asArraySymbol), .SmtIdent f]

/-! Create a select Smt application (i.e., applying an fun array representation to its arguments). -/
def selectSmt (f : SmtQualifiedIdent) (args : Array SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN selectSymbol (#[.SmtIdent f] ++ args)

/-! Return `true` Smt term. -/
def trueSmt : SmtTerm := .BoolTerm true

/-! Return `false` Smt term. -/
def falseSmt : SmtTerm := .BoolTerm false


/-! Convert an Integer literal to an Smt representation. -/
def intLitSmt (n : Int) : SmtTerm :=
 match n with
 | Int.ofNat n => .NumTerm n
 | Int.negSucc n => negSmt (.NumTerm (Nat.add n 1))


/-! Convert an Nat literal to an Smt representation. -/
def natLitSmt (n : Nat) : SmtTerm := .NumTerm n

/-! Convert an String literal to an Smt representation. -/
def strLitSmt (s : String) : SmtTerm := .StrTerm s!"\"{s}\""

/-! Create an Smt variable identifier. -/
def smtSimpleVarId (nm : SmtSymbol) : SmtTerm := .SmtIdent (.SimpleIdent nm)

/-! Create an Smt qualified variable identifier. -/
def smtQualifiedVarId (nm : SmtSymbol) (t : SortExpr) : SmtTerm :=
  .SmtIdent (.QualifiedIdent nm t)

/-- Create an Smt symbol from a free variable id.
    The Smt symbol will correspond to the user-defined name
    associated to the free variable id.
-/
def fvarIdToSmtSymbol (v : FVarId) : MetaM SmtSymbol := do
  return (mkNormalSymbol s!"{← v.getUserName}")

/-! Create an Smt term from a free variable. -/
def fvarIdToSmtTerm (v : FVarId) : MetaM SmtTerm :=
  return smtSimpleVarId (← fvarIdToSmtSymbol v)

/-! Create an e-matching pattern to be used for a forall or an exists Smt term. -/
def mkPattern (patterns : Array SmtTerm) : SmtAttribute := .Pattern patterns

/-! Create a debug annotation name for a forall/exists Smt term. -/
def mkQid (n : String) : SmtAttribute := .Qid n

/-! Annotate an Smt term with an optional list of attributes. -/
def annotateTerm (t : SmtTerm) (opt : Option (Array SmtAttribute)) : SmtTerm :=
  match opt with
  | none => t
  | some atts => .AnnotatedTerm t atts

/-! Associate an optional name `nm` to an Smt term. -/
def nameTerm (t : SmtTerm) (nm : Option String) : SmtTerm :=
  match nm with
  | none => t
  | some nmThm => .AnnotatedTerm t #[.Named nmThm]

/-! Create a forall Smt Term, with quantifiers `vars` and body `b`.
    An optional theorem name `nmThm` can be provided as well as
    specific patterns to facilitate e-matching and debugging
    during solving.
-/
def mkForallTerm
  (nmThm : Option String) (vars : SortedVars)
  (b : SmtTerm) (att : Option (Array SmtAttribute)) : SmtTerm :=
  let bodyTerm := annotateTerm b att
  let forallTerm := .ForallTerm vars bodyTerm
  nameTerm forallTerm nmThm

/-! Create an existential Smt Term, with quantifiers `vars` and body `b`.
    An optional theorem name `nmThm` can be provided as well as
    specific patterns to facilitate e-matching and debugging
    during solving.
-/
def mkExistsTerm
  (nmThm : Option String) (vars : SortedVars)
  (b : SmtTerm) (att : Option (Array SmtAttribute)) : SmtTerm :=
  let bodyTerm := annotateTerm b att
  let existsTerm := .ExistsTerm vars bodyTerm
  nameTerm existsTerm nmThm

/-! Create a lambda Smt term with parameters `args` and body `b`. -/
def mkLambdaTerm (args : SortedVars) (b : SmtTerm) : SmtTerm := .LambdaTerm args b

/-! Create a let Smt term with bindings `binds` and body `b`. -/
def mkLetTerm (binds : Array (SmtSymbol × SmtTerm)) (b : SmtTerm) : SmtTerm :=
  .LetTerm binds b

/-! ## Helper functions. -/

/-! Return `true` when `t := BoolTerm true`.
    Otherwise `false`.
-/
def isTrueSmt (t : SmtTerm) : Bool :=
  match t with
  | .BoolTerm b => b
  | _ => false

/-! Return `true` when `t := AppTerm idt args`.
    Otherwise `false`.
-/
def isAppTerm (t : SmtTerm) : Bool :=
  match t with
  | .AppTerm .. => true
  | _ => false

/-! Determine if `t` is an equality Smt expression and return it's correponding arguments.
    Otherwise return `none`.
-/
def eqSmt? (t : SmtTerm) : Option (SmtTerm × SmtTerm) :=
 match t with
 | .AppTerm (.SimpleIdent sym) args =>
     if sym == eqSymbol
     then (args[0]!, args[1]!)
     else none
 | _ => none

/-! Return `true` when `t` corresponds to ParamSort with name `nm`.
   Otherwise `false`.
-/
def isParamSort (t : SortExpr) (sName : SmtSymbol) : Bool :=
  match t with
  | .ParamSort nm _ => nm == sName
  | .SymbolSort _ => false

end Solver.Smt
