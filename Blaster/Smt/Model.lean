import Std.Data.HashMap
import Std.Data.HashSet

/-! ## Solver model-value reconstruction

`(get-value (t))` responses are S-expressions whose exact shape is
solver-specific. This module parses them and reconstructs a Lean-flavored
rendering of the returned value, so that counterexamples read as Lean values
regardless of the backend solver:

 - z3 wraps long values over several lines whereas cvc5 prints a single line;
 - cvc5 qualifies parametric-datatype constructors with `as` sort ascriptions,
   e.g. `(as Option.none (@Option Int))` and
   `((as Prod.mk (@Prod Int Bool)) 1 true)`;
 - cvc5 shares repeated subterms through `let` bindings, e.g.
   `(let ((_let_1 (as List.cons (@List Int)))) (_let_1 1 (_let_1 0 (as List.nil (@List Int)))))`;
 - both solvers print negative integers as `(- n)`, escape `"` in string
   literals by doubling it, and escape characters through `\u{…}` sequences.

Reconstruction is intentionally *total* over well-formed S-expressions:
values with no direct Lean counterpart (SMT arrays, lambdas, uninterpreted
constants, …) are rendered as raw S-expressions rather than rejected, and a
malformed response makes the entry points return `none` so that callers can
fall back to the raw solver output.

TODO(design note): the `Sexp` parser and `normalizeValue` pipeline are
deliberately independent of the string rendering below. This separation could
later support typed decoding of solver values into user-defined Lean types
(for example, through a `FromData`-style class) for programmatic counterexample
consumption.
-/

namespace Blaster.Smt

/-- S-expression view of a solver response. Atoms keep their raw spelling:
    simple symbols, `|quoted symbols|` (pipes included), `"string literals"`
    (quotes and `""` escapes included) and numerals. -/
inductive Sexp where
  | atom (s : String)
  | app (elems : Array Sexp)
deriving Repr, BEq, Inhabited

namespace Sexp

/-- Characters terminating a simple (unquoted) atom. -/
private def isAtomBreak (c : Char) : Bool :=
  c.isWhitespace || c == '(' || c == ')' || c == '"' || c == '|' || c == ';'

/-- Parse a sequence of S-expressions, stopping at an unmatched `)` (left
    unconsumed) or at the end of input. String literals keep their delimiting
    quotes (`""` escapes intact) and quoted symbols keep their pipes, so that
    atoms can be re-emitted verbatim. -/
private partial def parseSeq (cs : List Char) (acc : Array Sexp) :
    Except String (Array Sexp × List Char) :=
  match cs with
  | [] => .ok (acc, [])
  | ')' :: _ => .ok (acc, cs)
  | '(' :: rest =>
      match parseSeq rest #[] with
      | .error e => .error e
      | .ok (elems, rest) =>
          match rest with
          | ')' :: rest => parseSeq rest (acc.push (.app elems))
          | _ => .error "unbalanced '(' in solver response"
  | '"' :: rest =>
      match takeString rest ['"'] with
      | .error e => .error e
      | .ok (lit, rest) => parseSeq rest (acc.push (.atom lit))
  | '|' :: rest =>
      match takeQuotedSymbol rest ['|'] with
      | .error e => .error e
      | .ok (lit, rest) => parseSeq rest (acc.push (.atom lit))
  | ';' :: rest => parseSeq (rest.dropWhile (· != '\n')) acc
  | c :: rest =>
      if c.isWhitespace then parseSeq rest acc
      else
        let tok := cs.takeWhile (fun c => !isAtomBreak c)
        parseSeq (cs.drop tok.length) (acc.push (.atom (String.mk tok)))
 where
  -- NOTE: SMT-LIB escapes a quote inside a string literal by doubling it.
  takeString : List Char → List Char → Except String (String × List Char)
    | '"' :: '"' :: rest, acc => takeString rest ('"' :: '"' :: acc)
    | '"' :: rest, acc => .ok (String.mk (('"' :: acc).reverse), rest)
    | c :: rest, acc => takeString rest (c :: acc)
    | [], _ => .error "unterminated string literal in solver response"
  takeQuotedSymbol : List Char → List Char → Except String (String × List Char)
    | '|' :: rest, acc => .ok (String.mk (('|' :: acc).reverse), rest)
    | c :: rest, acc => takeQuotedSymbol rest (c :: acc)
    | [], _ => .error "unterminated quoted symbol in solver response"

/-- Parse all S-expressions of a solver response. -/
def parseMany (s : String) : Except String (Array Sexp) :=
  match parseSeq s.toList #[] with
  | .ok (es, []) => .ok es
  | .ok _ => .error "unbalanced ')' in solver response"
  | .error e => .error e

private def isBinderKeyword (name : String) : Bool :=
  name == "lambda" || name == "forall" || name == "exists"

private inductive AtomIdentity where
  | symbol (name : String)
  | other (raw : String)
deriving BEq, Hashable

private def isSimpleSymbolInitial (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
    "~!@$%^&*_-+=<>.?/".contains c

private def isReservedToken : String → Bool
  | "BINARY" => true
  | "DECIMAL" => true
  | "HEXADECIMAL" => true
  | "NUMERAL" => true
  | "STRING" => true
  | "_" => true
  | "!" => true
  | "as" => true
  | "let" => true
  | "exists" => true
  | "forall" => true
  | "match" => true
  | "par" => true
  | "lambda" => true
  | "assert" => true
  | "check-sat" => true
  | "check-sat-assuming" => true
  | "declare-const" => true
  | "declare-datatype" => true
  | "declare-datatypes" => true
  | "declare-fun" => true
  | "declare-sort" => true
  | "define-fun" => true
  | "define-fun-rec" => true
  | "define-funs-rec" => true
  | "define-sort" => true
  | "echo" => true
  | "exit" => true
  | "get-assertions" => true
  | "get-assignment" => true
  | "get-info" => true
  | "get-model" => true
  | "get-option" => true
  | "get-proof" => true
  | "get-unsat-assumptions" => true
  | "get-unsat-core" => true
  | "get-value" => true
  | "pop" => true
  | "push" => true
  | "reset" => true
  | "reset-assertions" => true
  | "set-info" => true
  | "set-logic" => true
  | "set-option" => true
  | _ => false

private def isSimpleSymbol (name : String) : Bool :=
  !isReservedToken name && match name.toList with
    | [] => false
    | first :: rest =>
        isSimpleSymbolInitial first &&
          rest.all fun c => isSimpleSymbolInitial c || c.isDigit

/-- Semantic identity of a parsed SMT-LIB atom. Quoting changes a symbol's
    spelling, not which symbol it denotes; non-symbol tokens remain a separate
    lexical category. Raw spellings stay in the syntax tree for rendering. -/
private def atomIdentity (name : String) : AtomIdentity :=
  if name.startsWith "|" && name.endsWith "|" then
    .symbol ((name.drop 1).dropRight 1)
  else if isSimpleSymbol name then
    .symbol name
  else
    .other name

private def binderNames (declarations : Array Sexp) : Array AtomIdentity :=
  declarations.filterMap fun declaration =>
    match declaration with
    | .app #[.atom name, _sort] => some (atomIdentity name)
    | _ => none

/-- Free semantic atom identities in term positions. Binder declarations, sort
    positions, and indexed-identifier components do not contribute. -/
private partial def freeAtoms (e : Sexp)
    (bound : Std.HashSet AtomIdentity := {}) : Std.HashSet AtomIdentity :=
  match e with
  | .atom name =>
      let identity := atomIdentity name
      if bound.contains identity then {} else ({} : Std.HashSet AtomIdentity).insert identity
  | .app #[.atom "let", .app bindings, body] =>
      let fromBindings := bindings.foldl (init := ({} : Std.HashSet AtomIdentity)) fun free binding =>
        match binding with
        | .app #[.atom _name, value] => free.union (freeAtoms value bound)
        | _ => free.union (freeAtoms binding bound)
      let names := bindings.filterMap fun binding =>
        match binding with
        | .app #[.atom name, _value] => some (atomIdentity name)
        | _ => none
      let bodyBound := names.foldl (init := bound) fun names name => names.insert name
      fromBindings.union (freeAtoms body bodyBound)
  | .app #[.atom "as", .atom "const", _sort] => {}
  | .app #[.atom "as", term, _sort] => freeAtoms term bound
  | binderExpr@(.app #[.atom binder, .app declarations, body]) =>
      if isBinderKeyword binder then
        let bodyBound := (binderNames declarations).foldl (init := bound) fun names name =>
          names.insert name
        freeAtoms body bodyBound
      else if binder == "_" then {}
      else
        match binderExpr with
        | .app elems =>
            elems.foldl (init := ({} : Std.HashSet AtomIdentity)) fun free elem =>
              free.union (freeAtoms elem bound)
        | _ => {}
  | .app elems =>
      match (elems[0]? : Option Sexp) with
      | some (.atom "_") => {}
      | _ =>
          elems.foldl (init := ({} : Std.HashSet AtomIdentity)) fun free elem =>
            free.union (freeAtoms elem bound)

private partial def allAtoms : Sexp → Std.HashSet AtomIdentity
  | .atom name => ({} : Std.HashSet AtomIdentity).insert (atomIdentity name)
  | .app elems =>
      elems.foldl (init := ({} : Std.HashSet AtomIdentity)) fun names elem =>
        names.union (allAtoms elem)

private partial def freshBinderName (used : Std.HashSet AtomIdentity) (index : Nat := 0) : String :=
  let candidate := s!"_blaster_bound_{index}"
  if used.contains (atomIdentity candidate) then freshBinderName used (index + 1) else candidate

/-- Normalize a solver *value*:
     - expand `let` bindings (cvc5 shares repeated subterms through them);
     - drop `as` sort ascriptions (cvc5 qualifies parametric-datatype
       constructors with the instantiated sort), except `(as const …)`,
       which denotes a constant array and carries no value by itself;
     - respect `lambda`, `forall`, and `exists` scopes, alpha-renaming a
       binder when an inserted free atom would otherwise be captured;
     - preserve any value containing an SMT-LIB `match` verbatim until match
       pattern binding is implemented.
    SMT-LIB `let` is parallel: bindings are evaluated in the enclosing
    environment and only the body sees them. -/
partial def normalizeValue (e : Sexp) : Sexp := go {} e
 where
  /-- `match` patterns bind variables in their branch terms. Until that scope is
      modeled, preserve the complete enclosing value rather than substituting
      through a pattern and changing its meaning. -/
  containsUnsupportedBinder : Sexp → Bool
    | .atom _ => false
    | .app elems =>
        match (elems[0]? : Option Sexp) with
        | some (.atom "match") => true
        | _ => elems.any containsUnsupportedBinder

  go (env : Std.HashMap AtomIdentity Sexp) (e : Sexp) : Sexp :=
    if containsUnsupportedBinder e then e
    else
      match e with
      | .atom a => env.getD (atomIdentity a) (.atom a)
      | .app #[.atom "let", .app bindings, body] =>
          let env' := bindings.foldl (init := env) fun acc b =>
            match b with
            | .app #[.atom x, v] => acc.insert (atomIdentity x) (go env v)
            | _ => acc
          go env' body
      | .app #[.atom "as", t, sort] =>
          if t == .atom "const" then .app #[.atom "as", t, sort]
          else go env t
      | binderExpr@(.app #[.atom binder, .app declarations, body]) =>
          if isBinderKeyword binder then
            let names := binderNames declarations
            let scopedEnv := names.foldl (init := env) fun env name => env.erase name
            let captures := scopedEnv.fold
              (fun free _name value => free.union (freeAtoms value))
              ({} : Std.HashSet AtomIdentity)
            let used := env.fold
              (fun used name value => (used.insert name).union (allAtoms value))
              (allAtoms binderExpr)
            let (bodyEnv, _used, declarations, _nextIndex) :=
              declarations.foldl (init := (scopedEnv, used, #[], 0)) fun state declaration =>
                let (bodyEnv, used, declarations, nextIndex) := state
                match declaration with
                | .app #[.atom name, sort] =>
                    let identity := atomIdentity name
                    if captures.contains identity then
                      let fresh := freshBinderName used nextIndex
                      (bodyEnv.insert identity (.atom fresh), used.insert (atomIdentity fresh),
                        declarations.push (.app #[.atom fresh, sort]), nextIndex + 1)
                    else
                      (bodyEnv, used, declarations.push declaration, nextIndex)
                | _ => (bodyEnv, used, declarations.push declaration, nextIndex)
            .app #[.atom binder, .app declarations, go bodyEnv body]
          else if binder == "_" then binderExpr
          else
            match binderExpr with
            | .app elems => .app (elems.map (go env))
            | _ => binderExpr
      | indexed@(.app elems) =>
          match (elems[0]? : Option Sexp) with
          | some (.atom "_") => indexed
          | _ => .app (elems.map (go env))

/-- Decode an SMT-LIB string literal (with its surrounding quotes) into the
    string it denotes: `""` undoubles to `"`, and `\u{X…}` / `\uXXXX` escape
    sequences (SMT-LIB Unicode strings theory) decode to their code point.
    A `\u` not forming a well-formed escape stands for itself. -/
partial def decodeStringLit? (lit : String) : Option String :=
  match lit.toList with
  | '"' :: cs => go cs []
  | _ => none
 where
  go : List Char → List Char → Option String
    | '"' :: '"' :: rest, acc => go rest ('"' :: acc)
    | ['"'], acc => some (String.mk acc.reverse)
    | '"' :: _, _ => none -- content after the closing quote
    | '\\' :: 'u' :: rest, acc =>
        match takeUniEscape? rest with
        | some (c, rest) => go rest (c :: acc)
        | none => go ('u' :: rest) ('\\' :: acc)
    | c :: rest, acc => go rest (c :: acc)
    | [], _ => none -- missing closing quote
  takeUniEscape? : List Char → Option (Char × List Char)
    | '{' :: rest => do
        let hex := rest.takeWhile (· != '}')
        if hex.isEmpty || hex.length > 6 then failure
        let c ← charOf? (← hexNat? hex)
        match rest.drop hex.length with
        | '}' :: rest => return (c, rest)
        | _ => failure
    | cs => do
        let hex := cs.take 4
        if hex.length != 4 then failure
        return (← charOf? (← hexNat? hex), cs.drop 4)
  hexNat? (cs : List Char) : Option Nat :=
    cs.foldlM (fun acc c => (hexVal? c).map (acc * 16 + ·)) 0
  hexVal? (c : Char) : Option Nat :=
    let n := c.toNat
    if 48 ≤ n && n ≤ 57 then some (n - 48) -- 0-9
    else if 97 ≤ n && n ≤ 102 then some (n - 87) -- a-f
    else if 65 ≤ n && n ≤ 70 then some (n - 55) -- A-F
    else none
  charOf? (n : Nat) : Option Char :=
    if n.isValidChar then some (Char.ofNat n) else none

/-- Render an S-expression in canonical single-line SMT-LIB form. Parsed atom
    spellings are preserved, but original whitespace and comments are not.
    Used for values that have no Lean counterpart (SMT arrays, lambdas, …). -/
partial def toRaw : Sexp → String
  | .atom a => a
  | .app es => s!"({String.intercalate " " (es.toList.map toRaw)})"

/-- `true` when `s` is a numeral. -/
private def isNumeral (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit

/-- SMT-LIB forms that never denote a datatype constructor: applications with
    such a head are rendered as raw S-expressions. -/
private def smtKeywordHeads : Array String :=
  #["let", "as", "lambda", "forall", "exists", "match", "ite",
    "store", "const", "select", "and", "or", "not", "xor", "distinct",
    "div", "mod", "abs", "to_int", "to_real"]

/-- `true` when `h` can denote a datatype constructor in a model value
    (identifier-like and not an SMT-LIB keyword). -/
private def isCtorHead (h : String) : Bool :=
  match h.toList with
  | [] => false
  | c :: _ => (c.isAlpha || c == '@' || c == '|') && !smtKeywordHeads.contains h

mutual

/-- Render `e` for an application-argument position: parenthesized when the
    rendering is not atomic (e.g. constructor applications, negative
    numbers). -/
private partial def renderArg (e : Sexp) : String :=
  let (s, atomic) := renderValue e
  if atomic then s else s!"({s})"

/-- Chain of `List.cons` applications ending in `List.nil` (a Lean list
    value), `none` otherwise. -/
private partial def asListElems? : Sexp → Option (List Sexp)
  | .atom "List.nil" => some []
  | .app #[.atom "List.cons", h, t] => (asListElems? t).map (h :: ·)
  | _ => none

/-- Components of a (right-nested) `Prod.mk` tuple tail. -/
private partial def tupleTail : Sexp → List Sexp
  | .app #[.atom "Prod.mk", x, y] => x :: tupleTail y
  | e => [e]

/-- Render a normalized value as Lean-flavored text; the Bool is `true` when
    the rendering needs no parentheses in argument position. -/
private partial def renderValue : Sexp → String × Bool
  | .atom a =>
      if a.startsWith "\"" then
        match decodeStringLit? a with
        | some s => (s.quote, true)
        | none => (a, true)
      else if a == "List.nil" then ("[]", true)
      else if a.startsWith "|" && a.endsWith "|" && a.length ≥ 2 then
        (a.drop 1 |>.dropRight 1, true)
      else (a, true)
  | e@(.app es) =>
      match asListElems? e with
      | some elems => (s!"[{renderCommaSep elems}]", true)
      | none =>
        match es with
        | #[.atom "-", .atom n] =>
            if isNumeral n then (s!"-{n}", false) else (toRaw e, true)
        | #[.atom "Prod.mk", a, b] =>
            (s!"({renderCommaSep (a :: tupleTail b)})", true)
        | _ =>
            match (es[0]? : Option Sexp) with
            | some (Sexp.atom h) =>
                if es.size ≥ 2 && isCtorHead h then
                  let head := (renderValue (.atom h)).1
                  let args := (es.toList.drop 1).map renderArg
                  (String.intercalate " " (head :: args), false)
                else (toRaw e, true)
            | _ => (toRaw e, true)

/-- Comma-separated rendering of `elems` (list/tuple components). -/
private partial def renderCommaSep (elems : List Sexp) : String :=
  String.intercalate ", " (elems.map (fun x => (renderValue x).1))

end

/-- Normalize and render a parsed value as Lean-flavored text. -/
def reconstructSexp (e : Sexp) : String :=
  (renderValue (normalizeValue e)).1

end Sexp

/-- Reconstruct the Lean-flavored value from a `get-value` response of the
    form `((t v))`. Returns `none` when the response has any other shape
    (parse failure, solver error report, …) so that callers can fall back to
    the raw output. -/
def reconstructGetValue? (response : String) : Option String :=
  match Sexp.parseMany response with
  | .ok #[.app #[.app #[_t, v]]] => some (Sexp.reconstructSexp v)
  | _ => none

/-- Reconstruct a single S-expression *value* (no `((t v))` wrapping).
    Mainly used by tests. -/
def reconstructValue? (value : String) : Option String :=
  match Sexp.parseMany value with
  | .ok #[e] => some (Sexp.reconstructSexp e)
  | _ => none

/-- Message of an `(error "…")` solver response, `none` for any other
    response shape. -/
def solverErrorMsg? (response : String) : Option String :=
  match Sexp.parseMany response with
  | .ok #[.app #[.atom "error", .atom lit]] =>
      Sexp.decodeStringLit? lit <|> some lit
  | _ => none

end Blaster.Smt
