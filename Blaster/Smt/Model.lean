import Lean

/-!
Parses SMT model values and the named bindings returned by Blaster's solver API.
Handles string escapes, constructor trees and shared values expressed with let bindings.
Provides primitive decoders and a composition point for domain-specific model decoders.
-/

namespace Blaster.Smt.Model

/-- The value syntax returned by SMT model evaluation. -/
inductive SExpr where
  | atom : String → SExpr
  | text : String → SExpr
  | list : List SExpr → SExpr
  deriving BEq, Repr

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- SMT-LIB uses doubled quotes and Unicode escapes in strings. -/
private partial def text (acc : List Char) : List Char → Option (String × List Char)
  | '"' :: '"' :: rest => text ('"' :: acc) rest
  | '"' :: rest => some (String.mk acc.reverse, rest)
  | '\\' :: 'u' :: '{' :: rest => do
    let (digits, rest) := rest.span (· != '}')
    let '}' :: rest := rest | none
    let code ← digits.foldlM (fun n c => return n * 16 + (← hexDigit c)) 0
    text (Char.ofNat code :: acc) rest
  | c :: rest => text (c :: acc) rest
  | [] => none

private partial def parseSExpr : List Char → Option (SExpr × List Char)
  | input => do
    let input := input.dropWhile Char.isWhitespace
    match input with
    | '(' :: rest => do
      let (items, rest) ← items [] rest
      return (.list items, rest)
    | '"' :: rest => do
      let (s, rest) ← text [] rest
      return (.text s, rest)
    | [] => none
    | ')' :: _ => none
    | _ =>
      let (word, rest) := input.span (fun c => !c.isWhitespace && c != '(' && c != ')')
      return (.atom (String.mk word), rest)
where
  items (acc : List SExpr) (input : List Char) : Option (List SExpr × List Char) := do
    let input := input.dropWhile Char.isWhitespace
    match input with
    | ')' :: rest => return (acc.reverse, rest)
    | [] => none
    | _ =>
      let (item, rest) ← parseSExpr input
      items (item :: acc) rest

/-- Decode the SMT integer numeral forms, including unary negation. -/
def integer : SExpr → Option Int
  | .atom n => n.toInt?
  | .list [.atom "-", .atom n] => return -(Int.ofNat (← n.toNat?))
  | _ => none

/-- Constructor names carry a monomorphization suffix for polymorphic datatypes. -/
def constructor (name suffix : String) : Bool :=
  name == suffix || name.endsWith ("." ++ suffix) || name.startsWith (suffix ++ "_")

/-- Z3 shares constructor trees with SMT-LIB lets. Bindings in one let are
    simultaneous; nested lets can shadow names from the outer environment. -/
partial def expandLets (value : SExpr) (env : List (String × SExpr) := []) : Option SExpr := do
  match value with
  | .atom name => return (env.lookup name).getD value
  | .text _ => return value
  | .list [.atom "let", .list bindings, body] =>
    let locals ← bindings.mapM fun binding => do
      let .list [.atom name, rhs] := binding | none
      return (name, ← expandLets rhs env)
    unless (locals.map Prod.fst).eraseDups.length == locals.length do none
    expandLets body (locals ++ env)
  | .list items => return .list (← items.mapM (fun item => expandLets item env))

/-- Parse exactly one SMT value, rejecting trailing input. -/
def parse (input : String) : Option SExpr := do
  let (value, rest) ← parseSExpr input.data
  unless (rest.dropWhile Char.isWhitespace).isEmpty do none
  return value

/-- Decode a named binding returned by `Blaster.Smt.getModel`, expanding shared lets. -/
def bindingValue (binding : String) : Option (String × SExpr) := do
  let name :: parts := binding.splitOn ": " | none
  unless !parts.isEmpty do none
  let value ← parse (": ".intercalate parts)
  return (name.trim, ← expandLets value)

/-- Apply a domain decoder to a named model value. -/
def decodeBinding (decode : SExpr → Option α) (binding : String) : Option (String × α) := do
  let (name, value) ← bindingValue binding
  return (name, ← decode value)

/-- Decode a named Boolean model value. -/
def boolBinding (binding : String) : Option (String × Bool) :=
  decodeBinding (fun value => match value with
    | .atom "true" => some true
    | .atom "false" => some false
    | _ => none) binding

/-- Decode a named integer model value. -/
def integerBinding (binding : String) : Option (String × Int) :=
  decodeBinding integer binding

end Blaster.Smt.Model
