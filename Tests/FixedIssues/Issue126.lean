import Tests.Utils

open Tests

namespace Tests.Issue126

-- Lean's public character-list view must preserve the full Unicode scalar range.
#testOptimize ["StringOfListUnicode"] String.ofList ['é', '∀'] ===> "é∀"
#testOptimize ["StringToListUnicode"] (norm-result: 1) "é∀".toList ===> ['é', '∀']
#testOptimize ["StringToListOfList"] ∀ (xs : List Char), (String.ofList xs).toList = xs ===> True
#testOptimize ["StringOfListToList"] ∀ (s : String), String.ofList s.toList = s ===> True
#testOptimize ["StringScalarLength"] (norm-result: 1) (String.ofList [Char.ofNat 0x30000, Char.ofNat 0x10FFFF]).length ===> 2
#testOptimize ["StringOfListLength"] ∀ (c : Char), (String.ofList [c, c]).length = 2 ===> True
#testOptimize ["StringOfListDistinctLength"] ∀ (a b : Char), String.ofList [a, b] = "x" ===> False
#testOptimize ["StringScalarRoundTrip"] (norm-result: 1)
  (String.ofList [Char.ofNat 0x2FFFF, Char.ofNat 0x30000, Char.ofNat 0x10FFFF]).toList ===>
  [Char.ofNat 0x2FFFF, Char.ofNat 0x30000, Char.ofNat 0x10FFFF]

-- These are the kernel-checked laws used by the view rewrites.
example (xs : List Char) : (String.ofList xs).toList = xs := String.toList_ofList
example (s : String) : String.ofList s.toList = s := String.ofList_toList
example (xs ys : List Char) : String.ofList xs = String.ofList ys ↔ xs = ys := String.ofList_inj

end Tests.Issue126
