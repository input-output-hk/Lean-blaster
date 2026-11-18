import Blaster.Counterexample

namespace Blaster.Counterexample
open Lean Meta

/-- The model-value fragment of SMT-LIB. Strings and quoted symbols are distinct. -/
inductive SExpr where
  | atom (value : String)
  | string (value : String)
  | list (values : List SExpr)
  deriving Repr, Inhabited

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def codePoint (s : List Char) : Except String Char := do
  if s.isEmpty then throw "empty SMT Unicode escape"
  let n ← s.foldlM (fun n c => do
    let some d := hexDigit c | throw "invalid SMT Unicode escape"
    pure (16 * n + d)) 0
  if n > 0x10ffff || (0xd800 ≤ n && n ≤ 0xdfff) then throw "invalid Unicode scalar"
  return Char.ofNat n

private partial def quotedString : List Char → List Char → Except String (String × List Char)
  | [], _ => .error "unterminated SMT string"
  | '"' :: '"' :: rest, acc => quotedString rest ('"' :: acc)
  | '"' :: rest, acc => .ok (String.mk acc.reverse, rest)
  | '\\' :: 'u' :: '{' :: rest, acc => do
      let (digits, tail) := rest.span (· != '}')
      let '}' :: tail := tail | throw "unterminated SMT Unicode escape"
      quotedString tail ((← codePoint digits) :: acc)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, acc => do
      quotedString rest ((← codePoint [a,b,c,d]) :: acc)
  | c :: rest, acc => quotedString rest (c :: acc)

private partial def quotedSymbol : List Char → List Char → Except String (String × List Char)
  | [], _ => .error "unterminated SMT quoted symbol"
  | '|' :: rest, acc => .ok (String.mk acc.reverse, rest)
  | c :: rest, acc => quotedSymbol rest (c :: acc)

private partial def parseOne (input : List Char) : Except String (SExpr × List Char) := do
  let input := input.dropWhile Char.isWhitespace
  match input with
  | [] => throw "expected SMT value"
  | '(' :: rest => parseList rest []
  | ')' :: _ => throw "unexpected SMT closing parenthesis"
  | '"' :: rest => let (s, tail) ← quotedString rest []; pure (.string s, tail)
  | '|' :: rest => let (s, tail) ← quotedSymbol rest []; pure (.atom s, tail)
  | _ =>
      let (s, tail) := input.span fun c => !c.isWhitespace && c != '(' && c != ')'
      return (.atom (String.mk s), tail)
where
  parseList (input : List Char) (acc : List SExpr) : Except String (SExpr × List Char) := do
    match input.dropWhile Char.isWhitespace with
    | [] => throw "unterminated SMT list"
    | ')' :: rest => return (.list acc.reverse, rest)
    | rest => let (e, tail) ← parseOne rest; parseList tail (e :: acc)

/-- Parentheses inside SMT strings/quoted symbols do not delimit a response. -/
def responseComplete (s : String) : Bool :=
  scan s.toList 0 false false
where
  scan : List Char → Int → Bool → Bool → Bool
    | [], depth, str, sym => depth == 0 && !str && !sym
    | '"' :: '"' :: cs, depth, true, sym => scan cs depth true sym
    | '"' :: cs, depth, str, false => scan cs depth (!str) false
    | '|' :: cs, depth, false, sym => scan cs depth false (!sym)
    | '(' :: cs, depth, false, false => scan cs (depth + 1) false false
    | ')' :: cs, depth, false, false => scan cs (depth - 1) false false
    | _ :: cs, depth, str, sym => scan cs depth str sym

/-- Expand model-local `let`s using SMT-LIB's simultaneous-binding semantics. -/
private partial def expand (e : SExpr) (env : List (String × SExpr) := []) : Except String SExpr :=
  match e with
  | .atom n => pure ((env.lookup n).getD e)
  | .string _ => pure e
  | .list [.atom "let", .list bindings, body] => do
      let bindings ← bindings.mapM fun
        | .list [.atom n, rhs] => return (n, ← expand rhs env)
        | _ => throw "malformed SMT let binding"
      expand body (bindings ++ env)
  | .list xs => return .list (← xs.mapM (expand · env))

def parse (s : String) : Except String SExpr := do
  let (e, rest) ← parseOne s.toList
  unless (rest.dropWhile Char.isWhitespace).isEmpty do throw "trailing SMT model text"
  expand e

private def integer : SExpr → Except String Int
  | .atom n => match n.toInt? with | some n => pure n | none => throw "expected SMT integer"
  | .list [.atom "-", .atom n] => match n.toNat? with
      | some n => pure (- (Int.ofNat n)) | none => throw "expected SMT negative integer"
  | _ => throw "expected SMT integer"

private def constructor : SExpr → Except String (String × List SExpr)
  | .atom n => pure (n, [])
  | .list [.atom "as", .atom n, _] => pure (n, [])
  | .list (.atom n :: xs) => pure (n, xs)
  | .list (.list [.atom "as", .atom n, _] :: xs) => pure (n, xs)
  | _ => throw "unsupported SMT constructor value"

/-- Reconstruct only concrete first-order values. Unknown constructors, dependent
    indices, proof fields and functional values fail explicitly. Limits bound
    diagnostic work without truncating a value into a fabricated witness. -/
def reconstruct (type : Expr) (model : SExpr) (fuel : Nat := 256) : MetaM (Expr × Value) := do
  let fuel + 1 := fuel | throwError "counterexample reconstruction depth exceeded"
  let type ← whnf type
  if type.isConstOf ``Int then
    let n ← ofExcept (integer model)
    return (toExpr n, .integer n)
  if type.isConstOf ``Nat then
    let n ← ofExcept (integer model)
    if n < 0 then throwError "negative SMT value for Nat"
    return (toExpr n.toNat, .natural n.toNat)
  if type.isConstOf ``Bool then
    match model with
    | .atom "true" => return (toExpr true, .boolean true)
    | .atom "false" => return (toExpr false, .boolean false)
    | _ => throwError "expected SMT Boolean"
  if type.isConstOf ``String then
    let .string s := model | throwError "expected SMT string"
    return (toExpr s, .string s)
  let .const indName levels := type.getAppFn | throwError "unsupported counterexample type {type}"
  let .inductInfo ind ← getConstInfo indName | throwError "unsupported counterexample type {type}"
  unless ind.numIndices == 0 do throwError "indexed counterexample type unsupported: {type}"
  let (symbol, values) ← ofExcept (constructor model)
  let some ctor := ind.ctors.find? (·.toString == symbol)
    | throwError "SMT constructor {symbol} does not belong to {type}"
  let .ctorInfo info ← getConstInfo ctor | throwError "unknown constructor {ctor}"
  let params := type.getAppArgs.extract 0 ind.numParams
  let mut value := mkAppN (mkConst ctor levels) params
  let mut fields := []
  for raw in values do
    let .forallE name fieldType _ _ ← whnf (← inferType value)
      | throwError "too many SMT fields for {ctor}"
    if ← isProp fieldType then throwError "proof-valued counterexample field unsupported: {name}"
    let (field, tree) ← reconstruct fieldType raw fuel
    value := mkApp value field
    fields := fields ++ [(name.toString, tree)]
  unless values.length == info.numFields do throwError "wrong SMT field count for {ctor}"
  unless ← isDefEq (← inferType value) type do throwError "reconstructed value has wrong type"
  return (value, .constructor indName.toString ctor.toString fields)

/-- Parsing/type errors are attached to the assignment, never converted to a value. -/
def decode (id name : Name) (type : Expr) (raw : String) : MetaM Binding := do
  try
    let (value, tree) ← reconstruct type (← ofExcept (parse raw))
    check value
    return { id, name, type, raw, value := some value, tree := some tree }
  catch e =>
    if e.isInterrupt then throw e
    return { id, name, type, raw, error := some (← e.toMessageData.toString) }

end Blaster.Counterexample
