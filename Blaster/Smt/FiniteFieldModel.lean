import Init.System.IO
import Init.Data.String.Extra

namespace Blaster.Smt.FiniteFieldModel

/-- Maximum UTF-8 byte length of a finite-field value response, including framing
and whitespace. The streaming reader also counts the terminating newline. -/
def maxResponseBytes : Nat := 4096

private def isSpace (c : UInt8) : Bool :=
  c == 32 || c == 9 || c == 10 || c == 13

private def isDigit (c : UInt8) : Bool :=
  48 ≤ c && c ≤ 57

private def isSimpleInitial (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) ||
    c == 126 || c == 33 || c == 64 || c == 36 || c == 37 ||
    c == 94 || c == 38 || c == 42 || c == 95 || c == 45 ||
    c == 43 || c == 61 || c == 60 || c == 62 || c == 46 ||
    c == 63 || c == 47

private def skipSpace (bytes : ByteArray) (start : Nat) : Nat := Id.run do
  let mut pos := start
  while pos < bytes.size && isSpace (bytes.get! pos) do
    pos := pos + 1
  return pos

private def expectByte (bytes : ByteArray) (pos : Nat) (expected : UInt8) :
    Except String Nat := do
  if pos ≥ bytes.size || bytes.get! pos != expected then
    throw "Malformed finite-field model response."
  return pos + 1

/-- Parse a canonical decimal without ever constructing a value above `limit`
by more than one decimal digit. The input has already passed the byte cap. -/
private def parseNumeral (bytes : ByteArray) (start limit : Nat) :
    Except String (Nat × Nat) := do
  if start ≥ bytes.size || !isDigit (bytes.get! start) then
    throw "Expected a canonical finite-field numeral."
  if bytes.get! start == 48 && start + 1 < bytes.size &&
      isDigit (bytes.get! (start + 1)) then
    throw "Noncanonical finite-field numeral."
  let mut pos := start
  let mut value := 0
  while pos < bytes.size && isDigit (bytes.get! pos) do
    value := value * 10 + ((bytes.get! pos).toNat - 48)
    if value > limit then
      throw "Finite-field numeral exceeds the expected range."
    pos := pos + 1
  return (value, pos)

private def parseLiteral (bytes : ByteArray) (start expectedModulus : Nat) :
    Except String (Nat × Nat) := do
  let pos ← expectByte bytes start 35
  let pos ← expectByte bytes pos 102
  let (value, pos) ← parseNumeral bytes pos (expectedModulus - 1)
  let pos ← expectByte bytes pos 109
  let (modulus, pos) ← parseNumeral bytes pos expectedModulus
  if modulus != expectedModulus then
    throw "Finite-field model modulus does not match the expected modulus."
  return (value, pos)

/-- Decode exactly `#f<value>m<modulus>`, with canonical unsigned decimals,
`modulus = expectedModulus ≥ 2`, and `value < modulus`. No surrounding whitespace
or alternate expressions are accepted. Check the UTF-8 byte cap before making
byte arrays or parsing numerals. Only the plain literal syntax observed in the
qualified solver fixtures is supported: `(as ...)`, `let`, and other typed or
computed representations are deliberately not guessed or normalized. -/
def decodeLiteral (expectedModulus : Nat) (raw : String) : Except String Nat := do
  if raw.utf8ByteSize > maxResponseBytes then
    throw "Finite-field model response exceeds the byte limit."
  if expectedModulus < 2 then
    throw "Expected finite-field modulus must be at least two."
  let bytes := raw.toUTF8
  let (value, pos) ← parseLiteral bytes 0 expectedModulus
  if pos != bytes.size then
    throw "Unexpected data after finite-field literal."
  return value

private def parseSymbol (bytes : ByteArray) (start : Nat) : Except String Nat := do
  if start ≥ bytes.size then
    throw "Missing finite-field model symbol."
  if bytes.get! start == 124 then
    let mut pos := start + 1
    while pos < bytes.size && bytes.get! pos != 124 do
      let c := bytes.get! pos
      if c == 92 || c ≥ 127 || (c < 32 && !isSpace c) then
        throw "Invalid quoted finite-field model symbol."
      pos := pos + 1
    if pos ≥ bytes.size then
      throw "Unterminated quoted finite-field model symbol."
    return pos + 1
  else
    if !isSimpleInitial (bytes.get! start) then
      throw "Invalid finite-field model symbol."
    let mut pos := start + 1
    while pos < bytes.size &&
        (isSimpleInitial (bytes.get! pos) || isDigit (bytes.get! pos)) do
      pos := pos + 1
    return pos

/-- Decode exactly one `((symbol #f<value>m<modulus>))` get-value entry, allowing
ASCII SMT whitespace between tokens and around the response. The symbol must
match the supplied SMT rendering byte-for-byte, including any `|...|` quoting.
Quoted symbols may contain spaces or parentheses; their contents are not parsed
as framing. Non-ASCII input, comments, extra entries, trailing data, truncated
frames, and nonliteral/optional typed value syntax are rejected. No generic SMT
AST or solver verdict is involved. Both strings are capped before conversion. -/
def decodeResponse (expectedSymbol : String) (expectedModulus : Nat) (raw : String) :
    Except String Nat := do
  if raw.utf8ByteSize > maxResponseBytes ||
      expectedSymbol.utf8ByteSize > maxResponseBytes then
    throw "Finite-field model response exceeds the byte limit."
  if expectedModulus < 2 then
    throw "Expected finite-field modulus must be at least two."
  let bytes := raw.toUTF8
  let symbol := expectedSymbol.toUTF8
  let pos ← expectByte bytes (skipSpace bytes 0) 40
  let pos ← expectByte bytes (skipSpace bytes pos) 40
  let start := skipSpace bytes pos
  let pos ← parseSymbol bytes start
  if pos - start != symbol.size then
    throw "Finite-field model symbol does not match the requested symbol."
  for i in [:symbol.size] do
    if bytes.get! (start + i) != symbol.get! i then
      throw "Finite-field model symbol does not match the requested symbol."
  if pos ≥ bytes.size || !isSpace (bytes.get! pos) then
    throw "Missing whitespace after finite-field model symbol."
  let (value, pos) ← parseLiteral bytes (skipSpace bytes pos) expectedModulus
  let pos ← expectByte bytes (skipSpace bytes pos) 41
  let pos ← expectByte bytes (skipSpace bytes pos) 41
  if skipSpace bytes pos != bytes.size then
    throw "Unexpected data after finite-field model response."
  return value

/-- Read one newline-terminated, balanced response without `getLine` or an
unbounded allocation. Single-byte reads never consume bytes after its final
newline. Leading whitespace and multiline framing are supported; bars protect
parentheses inside quoted symbols. After the outer frame closes, only whitespace
up to the newline is accepted. Malformed framing, invalid ASCII, EOF (including
a missing final newline), and the byte cap produce bounded static IO errors.
Semantic validation belongs to `decodeResponse`. A stalled/no-newline stream
must additionally be bounded by the caller's existing timeout; on any failure
the caller must retire the session rather than try to resynchronize it. -/
def readResponse (h : IO.FS.Handle) : IO String := do
  let mut bytes := ByteArray.emptyWithCapacity maxResponseBytes
  let mut depth := 0
  let mut started := false
  let mut complete := false
  let mut quoted := false
  while bytes.size < maxResponseBytes do
    let chunk ← try h.read 1 catch _ =>
      throw <| IO.userError "Could not read finite-field model response."
    if chunk.size == 0 then
      throw <| IO.userError "Unexpected EOF in finite-field model response."
    let c := chunk.get! 0
    if c ≥ 127 || (c < 32 && !isSpace c) then
      throw <| IO.userError "Invalid ASCII in finite-field model response."
    bytes := bytes.push c
    if complete then
      if !isSpace c then
        throw <| IO.userError "Unexpected data after finite-field model response."
      if c == 10 then
        match String.fromUTF8? bytes with
        | some response => return response
        | none => throw <| IO.userError "Invalid ASCII in finite-field model response."
    else if !started then
      if c == 40 then
        started := true
        depth := 1
      else if !isSpace c then
        throw <| IO.userError "Malformed finite-field model response framing."
    else if quoted then
      if c == 124 then
        quoted := false
      else if c == 92 then
        throw <| IO.userError "Invalid quoted finite-field model symbol."
    else if c == 124 then
      quoted := true
    else if c == 40 then
      depth := depth + 1
      if depth > 2 then
        throw <| IO.userError "Unsupported finite-field model response nesting."
    else if c == 41 then
      depth := depth - 1
      if depth == 0 then
        complete := true
    else if c == 34 || c == 59 then
      throw <| IO.userError "Unsupported finite-field model response syntax."
  throw <| IO.userError "Finite-field model response exceeds the byte limit."

end Blaster.Smt.FiniteFieldModel
