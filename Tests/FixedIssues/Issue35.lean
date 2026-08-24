import Blaster

namespace Tests.Issue35

-- Issue: Unexpected smt error / Unexpected Valid on String literals.
-- Diagnosis: `strLitSmt` wrapped the Lean string verbatim in double quotes instead of
--            escaping it for an Smt-Lib 2.6 string literal. In Smt-Lib 2.6 only printable
--            ASCII (0x20-0x7E) may appear verbatim inside a string literal, a `"` is written
--            by doubling it, and every other character uses the `\u{d}`..`\u{ddddd}` form.
--            Passing the Lean bytes through unchanged breaks in three different ways:
--              1. an embedded `"` closes the literal early and the whole query is rejected;
--              2. an embedded `""` or `\u{..}` is silently re-read by the solver as a
--                 *different, shorter* string, so blaster answers about the wrong string;
--              3. a non-ASCII character reaches the solver as its raw UTF-8 bytes, so a
--                 one-character Lean string becomes a multi-character Smt string.
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

/-! 5. Control characters are not printable ASCII either and must be escaped. -/

#blaster [∀ s : String, s = "a\nb" → s.length = 3]
#blaster [∀ s : String, s = "a\tb" → s.length = 3]
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "a\nb" → s = "ab"]

end Tests.Issue35
