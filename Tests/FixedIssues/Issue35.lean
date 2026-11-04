import Blaster

namespace Tests.Issue35

-- Issue: Unexpected smt error / Unexpected Valid on String literals.
-- Diagnosis: `strLitSmt` wrapped the Lean string verbatim in double quotes instead of
--            escaping it for an Smt string literal.
--            Two documents govern the escaping; `escapeSmtStringLit` in Blaster/Smt/Term.lean
--            carries the full quotes:
--              * SMT-LIB Standard v2.6 §3.1 gives a string literal exactly one escape
--                sequence, `""` for a single `"`, and no backslash escapes at all;
--              * the Smt-Lib Unicode Strings theory -- published alongside the standard,
--                not in it -- is what defines `\u{d}`..`\u{ddddd}`, over the code point
--                alphabet 0x00000-0x2FFFF.
--            Passing the Lean bytes through unchanged breaks in three different ways:
--              1. an embedded `"` closes the literal early and the whole query is rejected;
--              2. an embedded `""` or `\u{..}` is silently re-read by the solver as a
--                 *different, shorter* string, so blaster answers about the wrong string;
--              3. a non-ASCII character reaches the solver as its raw UTF-8 bytes, so a
--                 one-character Lean string becomes a multi-character Smt string. Such a
--                 character is lexically legal -- §3.1 admits code 128dec on -- but 2.6
--                 leaves the source encoding unspecified, and z3 counts the bytes singly.
--            Cases 2 and 3 are the dangerous ones: no error is reported, blaster just
--            proves false statements Valid.

/-! 1. An embedded `"` closes the Smt literal early. -/

-- "a\"b" has 3 characters: 'a', '"', 'b'.
#blaster [∀ s : String, s = "a\"b" → s.length = 3]
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "a\"b" → s.length = 2]

/-! 2. `""` is the Smt-Lib escape for a single `"`, so a doubled quote silently shrinks. -/

-- "a\"\"b" has 4 characters: 'a', '"', '"', 'b'.
#blaster [∀ s : String, s = "a\"\"b" → s.length = 4]
-- Proved Valid by the old translation, since the solver only saw 3 characters.
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "a\"\"b" → s.length = 3]

/-! 3. A literal backslash is re-read by the solver as the start of a `\u{..}` escape. -/

-- "\\u{41}" is the 6-character string `\u{41}`, not the letter `A`.
#blaster [∀ s : String, s = "\\u{41}" → s.length = 6]
#blaster [∀ s : String, s = "\\u{41}" → s ≠ "A"]
-- Both proved Valid by the old translation, since the solver only saw `A`.
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "\\u{41}" → s.length = 1]
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "\\u{41}" → s = "A"]

/-! 4. Non-ASCII characters reach the solver as their raw UTF-8 bytes. -/

-- "é" is a single Lean character (U+00E9).
#blaster [∀ s : String, s = "é" → s.length = 1]
-- Proved Valid by the old translation, since the solver saw the two UTF-8 bytes.
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "é" → s.length = 2]

-- Escaped literals still compose with the other String operations.
#blaster [∀ s : String, s = "é" → s ++ "!" = "é!"]
#blaster [∀ s t : String, s = "é" → t = "!" → (s ++ t).length = 2]

/-! 5. Whitespace is legal verbatim -- §3.1 admits ⟨white_space_char⟩ inside a literal, and
       the standard even shows one spanning a line break -- so these already worked.
       Regression coverage for the `\u{a}` / `\u{9}` escapes now emitted for them. -/

#blaster [∀ s : String, s = "a\nb" → s.length = 3]
#blaster [∀ s : String, s = "a\tb" → s.length = 3]
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "a\nb" → s = "ab"]

/-! 6. Code points above the 0x2FFFF alphabet bound have no Smt representation at all.

       `Nat.toDigits 16` yields six hex digits above 0xFFFFF, and the braced escape takes at
       most five (the fifth restricted to 0-2). z3 agrees with the theory exactly:
       `\u{2ffff}` is one character, `\u{30000}` is nine and `\u{10ffff}` is ten. Emitting
       such an escape produced a *false counterexample on a true goal*, so translation now
       refuses the literal instead. -/

-- U+2FFFF is the last denotable code point.
def lastDenotable : String := ⟨[Char.ofNat 0x2FFFF]⟩
#blaster [∀ s : String, s = lastDenotable → s.length = 1]

-- An emoji is well inside the bound (U+1F600).
#blaster [∀ s : String, s = "😀" → s.length = 1]
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "😀" → s.length = 2]

-- One past the bound, and the top of Lean's Char range, are both rejected outright.
def firstUndenotable : String := ⟨[Char.ofNat 0x30000]⟩
def maxLeanChar : String := ⟨[Char.ofNat 0x10FFFF]⟩

/--
error: translateExpr: string literal holds the character with code point 196608, above the Smt string alphabet bound 196607
-/
#guard_msgs in
#blaster [∀ s : String, (s ++ firstUndenotable).length ≥ 1]

/--
error: translateExpr: string literal holds the character with code point 1114111, above the Smt string alphabet bound 196607
-/
#guard_msgs in
#blaster [∀ s : String, (s ++ maxLeanChar).length ≥ 1]

end Tests.Issue35
