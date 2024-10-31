import Lean
import Solver.Command.Options
import Solver.Smt.Syntax

open Lean Meta

namespace Solver.Smt

/-! ## Lean Inductive types having an SMT counterpart -/

/-! ## Builtin SMT sorts. -/

/-! Smt Int Sort. -/
def intSort : SortExpr := .SymbolSort "Int"

/-! Smt Bool Sort. -/
def boolSort : SortExpr := .SymbolSort "Bool"

/-! Smt String Sort. -/
def stringSort : SortExpr := .SymbolSort "String"

/-! Smt Array Sort -/
def arraySort (args: Array SortExpr) : SortExpr :=
  .ParamSort "Array" args

/-! Smt Nat Sort.
    NOTE: This sort is defined during translation whenever required.
    (see function `defineNatSort`)
-/
def natSort : SortExpr := .SymbolSort "Nat"

-- TODO: add other sort once supported, e.g., BitVec, Unicode (for char), Seq, etc


/-! ## Builtin SMT symbols. -/

/-! equality SMT symbol. -/
def eqSymbol : SmtSymbol := "="

/-! Boolean `not` SMT symbol -/
def notSymbol : SmtSymbol := "not"

/-! Boolean `and` SMT symbol. -/
def andSymbol : SmtSymbol := "and"

/-! Boolean `or` SMT symbol. -/
def orSymbol : SmtSymbol := "or"

/-! Implies SMT symbol. -/
def impSymbol : SmtSymbol := "=>"

/-! Integer addition SMT symbol. -/
def addSymbol : SmtSymbol := "+"

/-! Integer subtraction SMT symbol. -/
def subSymbol : SmtSymbol := "-"

/-! Integer multiplication SMT symbol. -/
def mulSymbol : SmtSymbol := "*"

/-! Integer native SMT division symbol. -/
def divSymbol : SmtSymbol := "div"

/-! Integer native SMT modulo symbol. -/
def modSymbol : SmtSymbol := "mod"

/-! Integer Euclidean division SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def edivSymbol : SmtSymbol := "Int.ediv"

/-! Integer Euclidean modulo SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def emodSymbol : SmtSymbol := "Int.emod"

/-! Integer truncate division SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tdivSymbol : SmtSymbol := "Int.div"

/-! Integer truncate modulo SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tmodSymbol : SmtSymbol := "Int.mod"

/-! Integer floor division SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fdivSymbol : SmtSymbol := "Int.fdiv"

/-! Integer floor modulo SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fmodSymbol : SmtSymbol := "Int.fmod"

/-! Integer to Nat SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def toNatSymbol : SmtSymbol := "Int.toNat"


/-! Nat subtraction SMT symbol.
    NOTE: This function is defined during translation whenever required.
-/
def natSubSymbol : SmtSymbol := "Nat.sub"

/-! Integer absolute SMT symbol. -/
def absSymbol : SmtSymbol := "abs"

/-! less than SMT symbol. -/
def ltSymbol : SmtSymbol := "<"

/-! less than or equal to SMT symbol. -/
def leqSymbol : SmtSymbol := "<="

/-! if-then-else SMT symbol. -/
def iteSymbol : SmtSymbol := "ite"

/-! underscore SMT symbol. -/
def underSymbol : SmtSymbol := "_"

/-! select SMT symbol. -/
def selectSymbol : SmtSymbol := "select"

/-! as-array Smt symbol. -/
def asArraySymbol : SmtSymbol := "as-array"

/-! Create an SMT application term with function name `nm` and parameters `args`. -/
def mkSmtAppN (nm : SmtSymbol) (args : Array SmtTerm) : SmtTerm := .AppTerm nm args

/-! ## Builtin SMT functions. -/

/-! Create an Equality SMT application -/
def eqSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN eqSymbol #[op1, op2]

/-! Create an Boolean `not` SMT application -/
def notSmt (op : SmtTerm) : SmtTerm :=
  mkSmtAppN notSymbol #[op]

/-! Create an Boolean `and` SMT application -/
def andSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN andSymbol #[op1, op2]

/-! Create an Boolean `or` SMT application -/
def orSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN orSymbol #[op1, op2]

/-! Create an Implies SMT application -/
def impliesSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN impSymbol #[op1, op2]

/-! Create an Integer addtion SMT application -/
def addSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN addSymbol #[op1, op2]

/-! Create an Integer subtraction SMT application -/
def subSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN subSymbol #[op1, op2]


/-! Create an Integer multiplication SMT application -/
def mulSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN mulSymbol #[op1, op2]

/-! Create an Integer native division SMT application -/
def divSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN divSymbol #[op1, op2]

/-! Create an Integer native modulo SMT application -/
def modSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN modSymbol #[op1, op2]

/-! Create an Integer negation SMT application -/
def negSmt (op : SmtTerm) : SmtTerm :=
  mkSmtAppN subSymbol #[op]

/-! Create an Integer Euclidean division SMT application. -/
def edivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN edivSymbol #[op1, op2]

/-! Create an Integer Euclidean modulo SMT application. -/
def emodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN emodSymbol #[op1, op2]

/-! Create an Integer truncate division SMT application. -/
def tdivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN tdivSymbol #[op1, op2]

/-! Create an Integer truncate modulo SMT application. -/
def tmodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN tmodSymbol #[op1, op2]


/-! Create an Integer floor division SMT application. -/
def fdivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN fdivSymbol #[op1, op2]

/-! Create an Integer floor modulo SMT application. -/
def fmodSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN fmodSymbol #[op1, op2]

/-! Create an Integer to Nat SMT conversion. -/
def toNatSmt (op : SmtTerm) : SmtTerm :=
  mkSmtAppN toNatSymbol #[op]

/-! Create a Nat subtraction SMT application -/
def natSubSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN natSubSymbol #[op1, op2]


/-! Create a Nat division SMT application.
    NOTE: This is an alias to Int.ediv at Smt level.
-/
def natDivSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN edivSymbol #[op1, op2]

/-! Create a Nat modulo SMT application.
    NOTE: This is an alias to Int.emod at Smt level.
-/
def natModSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN emodSymbol #[op1, op2]

/-! Create an Integer absolute SMT application. -/
def absSmt (op : SmtTerm) : SmtTerm :=
  mkSmtAppN absSymbol #[op]


/-! Create a less than Smt application. -/
def ltSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN ltSymbol #[op1, op2]

/-! Create a less or equal to Smt application. -/
def leqSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSmtAppN leqSymbol #[op1, op2]


/-! Create an if-then-else SMT application. -/
def iteSmt (c : SmtTerm) (t : SmtTerm) (e : SmtTerm) : SmtTerm :=
  mkSmtAppN iteSymbol #[c, t, e]

/-! Create an as-array SMT application (i.e., converting a function to an array representation). -/
def asArraySmt (f : SmtSymbol) : SmtTerm :=
  mkSmtAppN underSymbol #[.SmtIdent asArraySymbol, .SmtIdent f]

/-! Create a select SMT application (i.e., applying an fun array representation to its arguments). -/
def selectSmt (f : SmtSymbol) (args : Array SmtTerm) : SmtTerm :=
  mkSmtAppN selectSymbol (#[.SmtIdent f] ++ args)

/-! Convert an Integer literal to an SMT representation. -/
def intLitSmt (n : Int) : SmtTerm :=
 match n with
 | Int.ofNat n => .NumTerm n
 | Int.negSucc n => negSmt (.NumTerm (Nat.add n 1))


/-! Convert an Nat literal to an SMT representation. -/
def natLitSmt (n : Nat) : SmtTerm := .NumTerm n

/-! Convert an String literal to an SMT representation. -/
def strLitSmt (s : String) : SmtTerm := .StrTerm s!"\"{s}\""

/-! Create an SMT variable identifier. -/
def smtVarId (nm : SmtSymbol) : SmtTerm := .SmtIdent nm


/-! Create an e-matching pattern to be used for a forall or an exists SMT term. -/
def mkPattern (patterns : Array SmtTerm) : SmtAttribute := .Pattern patterns

/-! Create a debug annotation name for a forall/exists SMT term. -/
def mkQid (n : String) : SmtAttribute := .Qid n

/-! Annotate an SMT term with an optional list of attributes. -/
def annotateTerm (t : SmtTerm) (opt : Option (Array SmtAttribute)) : SmtTerm :=
  match opt with
  | none => t
  | some atts => .AnnotatedTerm t atts

/-! Associate an optional name `nm` to an SMT term. -/
def nameTerm (t : SmtTerm) (nm : Option String) : SmtTerm :=
  match nm with
  | none => t
  | some nmThm => .AnnotatedTerm t #[.Named nmThm]

/-! Create a forall SMT Term, with quantifiers `vars` and body `b`.
    An optional theorem name `nmThm` can be provided as well as
    specific patterns to facilitate e-matching and debugging
    during solving.
-/
def mkForallTerm (nmThm : Option String) (vars : SortedVars) (b : SmtTerm) (att : Option (Array SmtAttribute)) : SmtTerm :=
  let bodyTerm := annotateTerm b att
  let forallTerm := .ForallTerm vars bodyTerm
  nameTerm forallTerm nmThm

/-! Create an existential SMT Term, with quantifiers `vars` and body `b`.
    An optional theorem name `nmThm` can be provided as well as
    specific patterns to facilitate e-matching and debugging
    during solving.
-/
def mkExistsTerm (nmThm : Option String) (vars : SortedVars) (b : SmtTerm) (att : Option (Array SmtAttribute)) : SmtTerm :=
  let bodyTerm := annotateTerm b att
  let existsTerm := .ExistsTerm vars bodyTerm
  nameTerm existsTerm nmThm

/-! Create a lambda SMT term with parameters `args` and body `b`. -/
def mkLambdaTerm (args : SortedVars) (b : SmtTerm) : SmtTerm := .LambdaTerm args b

/-! Create a let SMT term with bindings `binds` and body `b`. -/
def mkLetTerm (binds : Array (SmtSymbol × SmtTerm)) (b : SmtTerm) : SmtTerm :=
  .LetTerm binds b


end Solver.Smt
