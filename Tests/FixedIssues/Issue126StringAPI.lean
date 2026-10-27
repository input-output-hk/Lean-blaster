import Tests.Utils

open Tests

namespace Tests.Issue126StringAPI

#testOptimize ["StringReplaceStandard"] "ééx".replace "é" "a" ===> "aax"
#testOptimize ["StringReplaceEmptyPattern"] "é∀".replace "" "x" ===> "xéx∀x"
#testOptimize ["StringReplaceOverlaps"] "aaaaa".replace "aa" "b" ===> "bba"
#testOptimize ["SliceTakeUnicode"] ("é∀x".take 2).copy ===> "é∀"
#testOptimize ["SliceDropUnicode"] ("é∀x".drop 2).copy ===> "x"
#testOptimize ["SliceTakePastEnd"] ("é∀x".take 20).copy ===> "é∀x"
#testOptimize ["SliceDropPastEnd"] ("é∀x".drop 20).copy ===> ""

-- These survive optimization and exercise the SMT replacement definition.
/-- info: ✅ Valid -/
#guard_msgs in
#blaster (timeout: 10) (gen-cex: 0) [∀ (s r : String), s.replace s r = r]

/-- info: ✅ Expected Falsified -/
#guard_msgs in
#blaster (timeout: 10) (gen-cex: 0) (solve-result: 1)
  [∀ (r : String), "".replace "" r = ""]

/-- info: ✅ Valid -/
#guard_msgs in
#blaster (timeout: 10) (gen-cex: 0) [∀ (s : String), s.replace "" "x" ≠ ""]

-- A custom replacement conversion must not inherit the standard SMT meaning.
def customReplace (s p r : String) : String :=
  letI : String.ToSlice String := ⟨fun _ => "bad".toSlice⟩
  s.replace p r

/-- error: String.replace: only the standard String pattern and String replacement instances are supported -/
#guard_msgs in
#blaster [customReplace "aaa" "a" "b" = "badbadbad"]

-- Other native pattern types must not acquire String-pattern SMT semantics.
/-- error: String.replace: only the standard String pattern and String replacement instances are supported -/
#guard_msgs in
#blaster ["aaa".replace 'a' "b" = "bbb"]

end Tests.Issue126StringAPI
