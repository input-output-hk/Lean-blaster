import Lean
import Blaster.Command.Options
import Blaster.Smt.Syntax

open Lean Meta

namespace Blaster.Smt

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

/-! Smt Prop symbol. -/
def propSymbol : SmtSymbol := mkReservedSymbol "Prop"

/-! Smt String symbol. -/
def stringSymbol : SmtSymbol := mkReservedSymbol "String"

/-! Smt Nat symbol. -/
def natSymbol : SmtSymbol := mkReservedSymbol "Nat"

/-! Smt Empty symbol. -/
def emptySymbol : SmtSymbol := mkReservedSymbol "Empty"

/-! Smt PEmpty symbol. -/
def pemptySymbol : SmtSymbol := mkReservedSymbol "PEmpty"

/-! Smt PUnit symbol. -/
def punitSymbol : SmtSymbol := mkReservedSymbol "PUnit"

/-! Smt PUnit.unit constructor symbol. -/
def punitCtorSymbol : SmtSymbol := mkReservedSymbol "PUnit.unit"

/-! ## Builtin Smt sorts. -/

/-! Smt Int Sort. -/
def intSort : SortExpr := .SymbolSort intSymbol

/-! Smt Bool Sort. -/
def boolSort : SortExpr := .SymbolSort boolSymbol

/-! Smt Prop Sort.
    NOTE: This sort is defined during translation whenever required.
    (see function `definePropSort`)
-/
def propSort : SortExpr := .SymbolSort propSymbol

/-! Smt String Sort. -/
def stringSort : SortExpr := .SymbolSort stringSymbol

/-! Smt Param Sort instance. -/
@[always_inline, inline]
def paramSort (s : SmtSymbol) (args : Array SortExpr) : SortExpr :=
  .ParamSort s args

/-! Smt Array Sort -/
def arraySort (args: Array SortExpr) : SortExpr :=
  paramSort (mkReservedSymbol "Array") args

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


/-! Smt PUnit datatype
    NOTE: This datatype is declared during translation whenever required.
    (see function `definePUnitType`)
-/
def punitSort : SortExpr := .SymbolSort punitSymbol

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
def edivSymbol : SmtSymbol := mkReservedSymbol "@Int.ediv"

/-! Integer Euclidean modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def emodSymbol : SmtSymbol := mkReservedSymbol "@Int.emod"

/-! Integer truncate division Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tdivSymbol : SmtSymbol := mkReservedSymbol "@Int.tdiv"

/-! Integer truncate modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def tmodSymbol : SmtSymbol := mkReservedSymbol "@Int.tmod"

/-! Integer floor division Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fdivSymbol : SmtSymbol := mkReservedSymbol "@Int.fdiv"

/-! Integer floor modulo Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def fmodSymbol : SmtSymbol := mkReservedSymbol "@Int.fmod"

/-! Integer to Nat Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def toNatSymbol : SmtSymbol := mkReservedSymbol "@Int.toNat"

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
def intPowSymbol : SmtSymbol := mkReservedSymbol "@Int.pow"

/-! Nat power Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def natPowSymbol : SmtSymbol := mkReservedSymbol "@Nat.pow"

/-! Nat subtraction Smt symbol.
    NOTE: This function is defined during translation whenever required.
-/
def natSubSymbol : SmtSymbol := mkReservedSymbol "@Nat.sub"

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
def strLengthSymbol : SmtSymbol := mkReservedSymbol "str.len"

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

/-! Create an Nat power Smt application. -/
def natPowSmt (op1 : SmtTerm) (op2 : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN natPowSymbol #[op1, op2]

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
def selectSmt (f : SmtTerm) (args : Array SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN selectSymbol (#[f] ++ args)

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

/-! Highest code point denotable in an Smt string.

    The Smt-Lib Unicode Strings theory fixes the string alphabet to
    "the set UC of all integers from 0x00000 to 0x2FFFF, representing the set of all code
    points for Unicode characters in Planes 0-2".
    Lean's `Char` ranges over the whole Unicode scalar range up to `0x10FFFF`, so not every
    Lean string is denotable -- see `escapeSmtStringLit`. -/
def maxSmtCodePoint : Nat := 0x2FFFF

/-! Escape a Lean string into the body of an Smt string literal.

    Two separate documents govern this, and only the first is the standard itself:

    * SMT-LIB Standard v2.6, §3.1 (Lexicon). A string literal is "any sequence of characters
      from ⟨printable_char⟩ or ⟨white_space_char⟩ delimited by the double quote character",
      where a ⟨printable_char⟩ is "any character from 32dec to 126dec (US-ASCII) and from
      128dec on". Its *only* escape sequence is `""`, denoting one `"`. The standard is
      explicit that the base language has no backslash escapes: within a literal the
      sequences `\n`, `\012`, `\x0A` and `\u0008` "are not escape sequences ... but regular
      sequences denoting their individual characters".

    * The Smt-Lib Unicode Strings theory (https://smt-lib.org/theories-UnicodeStrings.shtml,
      Tinelli/Barrett/Fontaine, 2020-02-01), published alongside the standard rather than in
      it, is what gives `\u{...}` its meaning. It recognises exactly `\ud₃d₂d₁d₀` and
      `\u{d₀}`..`\u{d₄d₃d₂d₁d₀}`, the five-digit form being restricted to `d₄ ∈ {0,1,2}` by
      the alphabet bound above. Every other backslash is taken literally.

    So `"` is doubled, `0x20`-`0x7E` is emitted verbatim, and everything else uses `\u{...}`.

    Characters from 128dec on would in fact be *lexically* legal verbatim, but §3.1 leaves the
    source encoding unspecified -- it "should be a compatible 8-bit extension of the 7-bit
    US-ASCII set, such as UTF-8" -- and z3 counts the raw UTF-8 bytes of such a character
    individually, turning a one-character Lean string into a multi-character Smt string.
    Escaping them removes the dependency on the encoding. Whitespace is likewise legal
    verbatim and escaped only for uniformity.

    The backslash is escaped as `\u{5c}` even though a lone backslash is legal, so that a Lean
    string containing the *text* `\u{41}` can never be re-read by the solver as the escape for
    `A`. Decoding is a single left-to-right pass with no rescanning, so `\u{5c}u{41}` denotes
    the six characters `\u{41}` as intended.

    Fails with the offending character when it is above `maxSmtCodePoint`: the theory has no
    such character and no escape denotes one, so there is nothing correct to emit. -/
private def escapeSmtStringLit (s : String) : Except Char String :=
  s.data.foldlM (init := "") (λ acc c =>
    let n := c.toNat
         if c == '"'             then .ok (acc ++ "\"\"")
    else if c == '\\'            then .ok (acc ++ "\\u{5c}")
    else if n ≥ 0x20 && n ≤ 0x7e then .ok (acc.push c)
    else if n ≤ maxSmtCodePoint  then .ok (acc ++ "\\u{" ++ (Nat.toDigits 16 n).asString ++ "}")
    else .error c
  )

/-! Quote `s` as a complete Smt string literal using `escapeSmtStringLit`.
    Characters above `maxSmtCodePoint` (which `strLitSmt` rejects) are emitted as
    `\u{…}` escapes here so that the result is total; this helper is only used
    for transcripts and model round-trips, never for translation.
    The mirror decoding lives in `Blaster.Smt.Sexp.decodeStringLit?`. -/
def quoteSmtString (s : String) : String :=
  match escapeSmtStringLit s with
  | .ok body => s!"\"{body}\""
  | .error _ =>
    s.foldl (init := "\"") (fun acc c =>
      if c == '"' then acc ++ "\"\""
      else if c == '\\' || c.toNat < 0x20 || c.toNat > 0x7e then
        acc ++ s!"\\u\{{String.mk (Nat.toDigits 16 c.toNat)}}"
      else acc.push c) ++ "\""

/-! Convert a String literal to an Smt representation.
    Fails with the offending character when `s` holds one outside the Smt string alphabet. -/
def strLitSmt (s : String) : Except Char SmtTerm :=
  (escapeSmtStringLit s).map (λ body => .StrTerm s!"\"{body}\"")

/-! Create an Smt variable identifier. -/
def smtSimpleVarId (nm : SmtSymbol) : SmtTerm := .SmtIdent (.SimpleIdent nm)

/-! Create an Smt qualified variable identifier. -/
def smtQualifiedVarId (nm : SmtSymbol) (t : SortExpr) : SmtTerm :=
  .SmtIdent (.QualifiedIdent nm t)

/-! Create an e-matching pattern to be used for a forall or an exists Smt term. -/
def mkPattern (patterns : Array SmtTerm) : SmtAttribute := .Pattern patterns

/-! Create a debug annotation name for a forall/exists Smt term. -/
def mkQid (s : SmtSymbol) : SmtAttribute := .Qid s

/-! Annotate an Smt term with an optional list of attributes. -/
def annotateTerm (t : SmtTerm) (opt : Option (Array SmtAttribute)) : SmtTerm :=
  match opt with
  | none => t
  | some atts => .AnnotatedTerm t atts

/-! Associate an optional name `nm` to an Smt term. -/
def nameTerm (t : SmtTerm) (nm : Option String) : SmtTerm :=
  match nm with
  | none => t
  | some nmThm => .AnnotatedTerm t #[.Named (mkNormalSymbol nmThm)]

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


/-! Append smt symbol `nm` with "_{s}". -/
def appendSymbol (nm : SmtSymbol) (s : String) : SmtSymbol :=
  match nm with
   | .ReservedSymbol str => mkReservedSymbol s!"{str}_{s}"
   | .NormalSymbol str => mkNormalSymbol s!"{str}_{s}"


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

/-! Determine if `t` is an equality Smt expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
def eqSmt? (t : SmtTerm) : Option (SmtTerm × SmtTerm) :=
 match t with
 | .AppTerm (.SimpleIdent sym) args =>
     if sym == eqSymbol
     then (args[0]!, args[1]!)
     else none
 | _ => none

/-! Determine if `t` is a not Smt expression and return its corresponding argument.
    Otherwise return `none`.
-/
def notSmt? (t : SmtTerm) : Option SmtTerm :=
 match t with
 | .AppTerm (.SimpleIdent sym) args =>
     if sym == notSymbol
     then args[0]!
     else none
 | _ => none

/-! Return `true` when `t` corresponds to ParamSort with name `nm`.
   Otherwise `false`.
-/
def isParamSort (t : SortExpr) (sName : SmtSymbol) : Bool :=
  match t with
  | .ParamSort nm _ => nm == sName
  | .SymbolSort _ => false

/-! Return the smt symbol associated to the given Smt qualified identifier.
-/
def getSymbol : SmtQualifiedIdent → SmtSymbol
 | .SimpleIdent nm => nm
 | .QualifiedIdent nm _ => nm

/-! Return the smt conjunction of two terms only when `prev` does not correspond to `true`.
    Otherwise, returns `next`.
    Assumes that both prev and next cannot be `false`
-/
def andCond (prev : SmtTerm) (next : SmtTerm) : SmtTerm :=
  match prev with
  | .BoolTerm true => next
  | _ => andSmt next prev

/-! ## cvc5 higher-order rendering of function values

    Blaster encodes a Lean function value as an SMT `Array` value: function
    types become `(Array α₁ … αₙ β)`, function bodies become `lambda` terms
    and applications become `select`. Z3 identifies arrays with functions and
    accepts this encoding as is.

    cvc5 only parses `lambda` under a higher-order logic (`HO_ALL`), where a
    `lambda` has the function sort `(-> α₁ … αₙ β)`, not an `Array` sort. The
    functions below therefore render a canonical command for cvc5 by:
      - replacing every `(Array α₁ … αₙ β)` sort with `(-> α₁ … αₙ β)`;
      - replacing every `(select f t₁ … tₙ)` with `(@ f t₁ … tₙ)` (cvc5's
        higher-order application);
      - keeping `lambda`, `=` and all other terms unchanged.
    Both `Array` sorts and `->` sorts denote the full extensional space of
    total functions from α₁ × … × αₙ to β, `select` and `@` both denote
    application, and `=` is extensional for both. The rendering is therefore
    semantics-preserving. Function-valued canonicalization (`@canon…`),
    application, equality and `get-value` requests on function terms are all
    covered, since they are built from these constructs.
    Blaster emits `Array` sorts only for Lean function types (see `arraySort`)
    and the reserved `select` symbol only for function application (see
    `selectSmt`), so no genuine SMT array is affected. Z3 commands are never
    rewritten.
-/

/-! cvc5 higher-order function sort symbol. -/
def arrowSymbol : SmtSymbol := mkReservedSymbol "->"

/-! cvc5 higher-order application symbol. -/
def hoApplySymbol : SmtSymbol := mkReservedSymbol "@"

/-! Render `Array` sorts as cvc5 function sorts (see cvc5 higher-order rendering). -/
partial def SortExpr.toHigherOrder : SortExpr → SortExpr
  | .SymbolSort nm => .SymbolSort nm
  | .ParamSort nm ps =>
      let ps := ps.map SortExpr.toHigherOrder
      match nm with
      | .ReservedSymbol "Array" => .ParamSort arrowSymbol ps
      | _ => .ParamSort nm ps

/-! Render sorted variables for cvc5 (see cvc5 higher-order rendering). -/
def SortedVars.toHigherOrder (vs : SortedVars) : SortedVars :=
  vs.map (λ (v, s) => (v, s.toHigherOrder))

/-! Render qualified identifiers for cvc5 (see cvc5 higher-order rendering). -/
def SmtQualifiedIdent.toHigherOrder : SmtQualifiedIdent → SmtQualifiedIdent
  | .SimpleIdent nm => .SimpleIdent nm
  | .QualifiedIdent nm t => .QualifiedIdent nm t.toHigherOrder

mutual
/-- Render attributes for cvc5 (see cvc5 higher-order rendering). -/
partial def SmtAttribute.toHigherOrder : SmtAttribute → SmtAttribute
  | .Pattern p => .Pattern (p.map SmtTerm.toHigherOrder)
  | a => a

/-- Render terms for cvc5 (see cvc5 higher-order rendering). -/
partial def SmtTerm.toHigherOrder : SmtTerm → SmtTerm
  | .SmtIdent nm => .SmtIdent nm.toHigherOrder
  | .AppTerm (.SimpleIdent (.ReservedSymbol "select")) args =>
      .AppTerm (.SimpleIdent hoApplySymbol) (args.map SmtTerm.toHigherOrder)
  | .AppTerm nm args => .AppTerm nm.toHigherOrder (args.map SmtTerm.toHigherOrder)
  | .LetTerm bs body => .LetTerm (bs.map (λ (v, t) => (v, t.toHigherOrder))) body.toHigherOrder
  | .ForallTerm bs body => .ForallTerm bs.toHigherOrder body.toHigherOrder
  | .ExistsTerm bs body => .ExistsTerm bs.toHigherOrder body.toHigherOrder
  | .LambdaTerm bs body => .LambdaTerm bs.toHigherOrder body.toHigherOrder
  | .AnnotatedTerm t annot => .AnnotatedTerm t.toHigherOrder (annot.map SmtAttribute.toHigherOrder)
  | t => t
end

/-! Render datatype declarations for cvc5 (see cvc5 higher-order rendering). -/
def SmtDatatypeDecl.toHigherOrder (d : SmtDatatypeDecl) : SmtDatatypeDecl :=
  { d with ctors := d.ctors.map (λ (c, sels) => (c, sels.map (·.map (λ (s, t) => (s, t.toHigherOrder))))) }

/-! Render function declarations for cvc5 (see cvc5 higher-order rendering). -/
def SmtFunDecl.toHigherOrder (d : SmtFunDecl) : SmtFunDecl :=
  { d with params := d.params.toHigherOrder, ret := d.ret.toHigherOrder }

/-! Render a canonical (Z3-encoded) command for cvc5 (see cvc5 higher-order rendering). -/
def SmtCommand.toHigherOrder : SmtCommand → SmtCommand
  | .assertTerm t => .assertTerm t.toHigherOrder
  | .checkSatAssuming args => .checkSatAssuming (args.map SmtTerm.toHigherOrder)
  | .declareConst nm t => .declareConst nm t.toHigherOrder
  | .declareDataType nm decl => .declareDataType nm decl.toHigherOrder
  | .declareMutualDataTypes nms decls => .declareMutualDataTypes nms (decls.map SmtDatatypeDecl.toHigherOrder)
  | .declareFun nm args rt => .declareFun nm (args.map SortExpr.toHigherOrder) rt.toHigherOrder
  | .defineFun isRec nm args rt body => .defineFun isRec nm args.toHigherOrder rt.toHigherOrder body.toHigherOrder
  | .defineFunsRec decls bodies =>
      .defineFunsRec (decls.map SmtFunDecl.toHigherOrder) (bodies.map SmtTerm.toHigherOrder)
  | .defineSort nm args body => .defineSort nm args body.toHigherOrder
  | .getValue t => .getValue t.toHigherOrder
  | c => c

/-! Command actually submitted to `solver`: the canonical encoding for z3 and
    its higher-order rendering for cvc5 (see cvc5 higher-order rendering). -/
def SmtCommand.renderFor (solver : Blaster.Options.SmtSolver) (c : SmtCommand) : SmtCommand :=
  match solver with
  | .z3 => c
  | .cvc5 => c.toHigherOrder

/-! Whether `s` contains an `Array` sort, i.e., a function type (see cvc5 higher-order rendering). -/
partial def SortExpr.usesFunctionValues : SortExpr → Bool
  | .SymbolSort _ => false
  | .ParamSort (.ReservedSymbol "Array") _ => true
  | .ParamSort _ ps => ps.any SortExpr.usesFunctionValues

mutual
/-- Whether `a` contains a function value (see cvc5 higher-order rendering). -/
partial def SmtAttribute.usesFunctionValues : SmtAttribute → Bool
  | .Pattern p => p.any SmtTerm.usesFunctionValues
  | _ => false

/-- Whether `t` contains a function value, i.e., an `Array` sort, a `select`
    or a `lambda` (see cvc5 higher-order rendering). -/
partial def SmtTerm.usesFunctionValues : SmtTerm → Bool
  | .SmtIdent (.QualifiedIdent _ t) => t.usesFunctionValues
  | .AppTerm (.SimpleIdent (.ReservedSymbol "select")) _ => true
  | .AppTerm nm args =>
      (SmtTerm.SmtIdent nm).usesFunctionValues || args.any SmtTerm.usesFunctionValues
  | .LetTerm bs body => bs.any (·.2.usesFunctionValues) || body.usesFunctionValues
  | .ForallTerm bs body
  | .ExistsTerm bs body => bs.any (·.2.usesFunctionValues) || body.usesFunctionValues
  | .LambdaTerm _ _ => true
  | .AnnotatedTerm t annot => t.usesFunctionValues || annot.any SmtAttribute.usesFunctionValues
  | _ => false
end

/-! Whether `c` contains a function value. cvc5 needs the higher-order logic
    `HO_ALL` for such commands (see cvc5 higher-order rendering). -/
def SmtCommand.usesFunctionValues : SmtCommand → Bool
  | .assertTerm t
  | .getValue t => t.usesFunctionValues
  | .checkSatAssuming args => args.any SmtTerm.usesFunctionValues
  | .declareConst _ t => t.usesFunctionValues
  | .declareDataType _ decl => usesInDecl decl
  | .declareMutualDataTypes _ decls => decls.any usesInDecl
  | .declareFun _ args rt => args.any SortExpr.usesFunctionValues || rt.usesFunctionValues
  | .defineFun _ _ args rt body =>
      args.any (·.2.usesFunctionValues) || rt.usesFunctionValues || body.usesFunctionValues
  | .defineFunsRec decls bodies =>
      decls.any (λ d => d.params.any (·.2.usesFunctionValues) || d.ret.usesFunctionValues) ||
      bodies.any SmtTerm.usesFunctionValues
  | .defineSort _ _ body => body.usesFunctionValues
  | _ => false
 where
   usesInDecl (d : SmtDatatypeDecl) : Bool :=
     d.ctors.any (λ (_, sels) => sels.any (·.any (·.2.usesFunctionValues)))

/-! ## Sorts of cvc5 model values holding function values

    cvc5 1.4.1 does not return reliable `get-value` results for function
    values stored in datatype fields. The value of a datatype constant can
    refer back to the constant itself (e.g. `(S.mk (S.mk.0 $0) 1)` for `$0`),
    and even a closed value can disagree with the value of one of its own
    selector terms in the same model. Function values of top-level function
    terms (e.g. `(get-value ((S.mk.0 $0)))`) are returned as closed `lambda`
    terms.

    Model retrieval for cvc5 therefore follows the sort of each counterexample
    term (see `retrieveTypedValue`): a datatype value holding function values
    is rebuilt from its constructor (confirmed by its tester) and one
    `get-value` request per selector term, so every function value is
    requested at a function sort. A
    `ModelSchema` gives the sorts that this requires. It is computed from the
    canonical commands, which hold every declaration sent to the solver.
-/

/-! Name of `s` as declared (without SMT-LIB quoting). -/
def SmtSymbol.name : SmtSymbol → String
  | .ReservedSymbol s
  | .NormalSymbol s => s

/-- Sort information of the canonical query used to retrieve cvc5 model
    values (see sorts of cvc5 model values holding function values). -/
structure ModelSchema where
  /-- Sort of each declared constant. -/
  consts : Std.HashMap SmtSymbol SortExpr := {}
  /-- Declaration of each datatype, by datatype name. -/
  datatypes : Std.HashMap SmtSymbol SmtDatatypeDecl := {}
  /-- Parameters and body of each `define-sort`, by sort name. -/
  aliases : Std.HashMap SmtSymbol (Option (Array SmtSymbol) × SortExpr) := {}
  /-- Names of declared constants and functions and of defined functions.
      None of them can occur free in a model value. -/
  symbols : Std.HashSet String := {}

namespace ModelSchema

/-! Add the declarations of `c` to `schema`. -/
private def addCommand (schema : ModelSchema) (c : SmtCommand) : ModelSchema :=
  match c with
  | .declareConst nm t =>
      { schema with consts := schema.consts.insert nm t, symbols := schema.symbols.insert nm.name }
  | .declareFun nm _ _
  | .defineFun _ nm _ _ _ => { schema with symbols := schema.symbols.insert nm.name }
  | .defineFunsRec decls _ =>
      { schema with symbols := decls.foldl (λ acc d => acc.insert d.name.name) schema.symbols }
  | .declareDataType nm decl => { schema with datatypes := schema.datatypes.insert nm decl }
  | .declareMutualDataTypes nms decls =>
      (nms.zip decls).foldl (λ acc (nm, decl) =>
        { acc with datatypes := acc.datatypes.insert nm.name decl }) schema
  | .defineSort nm args body => { schema with aliases := schema.aliases.insert nm (args, body) }
  | _ => schema

/-! Schema of the canonical commands `cs`. -/
def ofCommands (cs : Array SmtCommand) : ModelSchema :=
  cs.foldl addCommand {}

/-! Replace each parameter `params[i]` in `s` with `args[i]`. -/
private partial def instantiate (params : Array SmtSymbol) (args : Array SortExpr) : SortExpr → SortExpr
  | s@(.SymbolSort nm) =>
      match params.idxOf? nm with
      | some i => args[i]?.getD s
      | none => s
  | .ParamSort nm ps => .ParamSort nm (ps.map (instantiate params args))

/-! Unfold the `define-sort` aliases at the head of `s` (at most `fuel` times). -/
partial def unfold (schema : ModelSchema) (s : SortExpr) (fuel : Nat := 64) : SortExpr :=
  if fuel == 0 then s else
  let (nm, args) := match s with
    | .SymbolSort nm => (nm, #[])
    | .ParamSort nm ps => (nm, ps)
  match schema.aliases.get? nm with
  | some (params, body) =>
      let params := params.getD #[]
      if params.size == args.size
      then schema.unfold (instantiate params args body) (fuel - 1)
      else s
  | none => s

/-! Whether `s` is a function sort, i.e., an `Array` sort (see `arraySort`). -/
def isFunctionSort (schema : ModelSchema) (s : SortExpr) : Bool :=
  match schema.unfold s with
  | .ParamSort (.ReservedSymbol "Array") _ => true
  | _ => false

/-! Constructors of datatype sort `s`, with each selector and its field sort
    instantiated with the sort arguments of `s`; `none` when `s` is not a
    declared datatype. -/
def constructors? (schema : ModelSchema) (s : SortExpr) :
    Option (Array (SmtSymbol × Array (SmtSymbol × SortExpr))) :=
  let (nm, args) := match schema.unfold s with
    | .SymbolSort nm => (nm, #[])
    | .ParamSort nm ps => (nm, ps)
  schema.datatypes.get? nm |>.map λ decl =>
    let params := decl.params.getD #[]
    decl.ctors.map λ (c, sels) =>
      (c, (sels.getD #[]).map λ (sel, t) => (sel, instantiate params args t))

/-! Sorts directly reachable from `s`: the components of a parametric sort
    and, for a datatype, the sorts of its fields. -/
private def components (schema : ModelSchema) (s : SortExpr) : Array SortExpr :=
  let s := schema.unfold s
  let params := match s with
    | .SymbolSort _ => #[]
    | .ParamSort _ ps => ps
  match schema.constructors? s with
  | some ctors => params ++ ctors.flatMap (·.2.map (·.2))
  | none => params

/-! Whether a value of sort `s` can contain a function value. -/
partial def holdsFunctions (schema : ModelSchema) (s : SortExpr) : Bool :=
  (go s {}).1
 where
   go (s : SortExpr) (visited : Std.HashSet SortExpr) : Bool × Std.HashSet SortExpr :=
     if visited.contains s then (false, visited)
     else if schema.isFunctionSort s then (true, visited)
     else
       (schema.components s).foldl (init := (false, visited.insert s)) λ (found, visited) c =>
         if found then (true, visited) else go c visited

/-! Names of the constructors of the datatype sorts holding function values
    that a value of sort `s` can contain, including `s` itself. -/
partial def functionDatatypeConstructors (schema : ModelSchema) (s : SortExpr) : Std.HashSet String :=
  (go s {} {}).1
 where
   go (s : SortExpr) (found : Std.HashSet String) (visited : Std.HashSet SortExpr) :
       Std.HashSet String × Std.HashSet SortExpr :=
     if visited.contains s then (found, visited)
     else
       let found :=
         match schema.constructors? s with
         | some ctors =>
             if schema.holdsFunctions s then ctors.foldl (λ acc (c, _) => acc.insert c.name) found
             else found
         | none => found
       (schema.components s).foldl (init := (found, visited.insert s)) λ (found, visited) c =>
         go c found visited

end ModelSchema

end Blaster.Smt
