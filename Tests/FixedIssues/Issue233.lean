import Tests.Utils

namespace Tests.Issue233

example (xs : List Nat) : [1, 2] ++ xs = 1 :: 2 :: xs := rfl
example (xs : List Nat) : (1 :: 2 :: xs).drop 2 = xs := rfl

#testOptimize ["AppendSymbolicTail"]
  (∀ xs : List Nat, [1, 2] ++ xs = 1 :: 2 :: xs) ===> True
#testOptimize ["AppendPartialPrefix"]
  (∀ xs ys : List Nat, (1 :: 2 :: xs) ++ ys = 1 :: 2 :: (xs ++ ys)) ===> True
#testOptimize ["AppendNilLeft"]
  (∀ α : Type, ∀ xs : List α, [] ++ xs = xs) ===> True
#testOptimize ["AppendNilRight"]
  (∀ α : Type, ∀ xs : List α, xs ++ [] = xs) ===> True
#testOptimize ["AppendPolymorphicPrefix"]
  (∀ α : Type, ∀ x : α, ∀ xs ys : List α, (x :: xs) ++ ys = x :: (xs ++ ys)) ===> True
#testOptimize ["DropSymbolicTail"]
  (∀ xs : List Nat, (1 :: 2 :: xs).drop 2 = xs) ===> True
#testOptimize ["DropPartialPrefix"]
  (∀ xs : List Nat, (1 :: 2 :: xs).drop 3 = xs.drop 1) ===> True
#testOptimize ["DropInsidePrefix"]
  (∀ xs : List Nat, (1 :: 2 :: xs).drop 1 = 2 :: xs) ===> True
#testOptimize ["DropZeroSymbolic"]
  (∀ α : Type, ∀ xs : List α, xs.drop 0 = xs) ===> True
#testOptimize ["DropNilSymbolicIndex"]
  (∀ α : Type, ∀ n : Nat, ([] : List α).drop n = []) ===> True
#testOptimize ["DropPastEnd"]
  (([1, 2] : List Nat).drop 1000000 = []) ===> True

#blaster (only-optimize: 1)
  [∀ xs : List Nat, ([1, 2] ++ xs).drop 2 = xs]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ xs : List Nat, (1 :: 2 :: xs).drop 1 = xs]

end Tests.Issue233
