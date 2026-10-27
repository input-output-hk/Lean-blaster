import Tests.Utils

open Tests

namespace Tests.Issue126Structures

-- Structure reduction must inspect value fields rather than type parameters.
-- Array.mk's element type is an inductive parameter, not a constructor field.
#testOptimize ["Utf8ByteArrayDistinct"] "a".toUTF8 == "b".toUTF8 ===> false
#testOptimize ["Utf8ByteArrayReflexive"] "é".toUTF8 == "é".toUTF8 ===> true
#testOptimize ["Utf8ByteCount"] (norm-result: 1) "é∀".toUTF8.size ===> 5
#testOptimize ["Utf8FullLeanScalar"] (norm-result: 1)
  (String.mk [Char.ofNat 0x10FFFF]).toUTF8.size ===> 4

end Tests.Issue126Structures
