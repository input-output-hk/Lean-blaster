import Lean
import Blaster

namespace Tests.Issue9

-- Issue: Unexpected smt error: (error "line 21 column 695: unknown constant α")
-- Diagnosis: Function `replaceGenericRecFun` in `Translate.Application` was not properly
--            instantiating explicit arguments (i.e., IdxArg was not incremented for all cases).

#blaster [∀ (α : Type) (x y : α) (xs ys : List α), [BEq α] → (x :: xs) == (y :: ys) → x == y]

inductive GenericGroup (α : Type) [LE α] where
 | first (n1 : α) (n2 : α) (h1 : n1 ≥ n2) : GenericGroup α
 | next (n : GenericGroup α)

def sizeOfGenericGroup [LE α] (a : GenericGroup α) : Nat :=
  match a with
  | .first .. => 1
  | .next n => 1 + (sizeOfGenericGroup n)

#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Type), [LE α] → ∀ (a : GenericGroup α), sizeOfGenericGroup a ≥ 10]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Type), [LE α] → ∀ (a : GenericGroup α), sizeOfGenericGroup a < 10]

mutual
 structure FunGroup (α : Type) [LE α] where
   f : α → GenericGroupFun α

inductive GenericGroupFun (α : Type) [LE α] where
 | first (n1 : α) (n2 : α) (h1 : n1 ≥ n2) : GenericGroupFun α
 | next (f : FunGroup α) (n1 : α) (n2 : GenericGroupFun α) : GenericGroupFun α
end

def sizeOfGenericGroupFun [LE α] [LE (GenericGroupFun α)] [DecidableLE (GenericGroupFun α)] (a : GenericGroupFun α) : Nat :=
  match a with
  | .first .. => 1
  | .next fg n1 n2 =>
          if fg.f n1 ≥ n2 then
            1 + sizeOfGenericGroupFun n2
          else 2

#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (α : Type), [LE α] →
    [LE (GenericGroupFun α)] →
    [DecidableLE (GenericGroupFun α)] →
    ∀ (a : GenericGroupFun α), sizeOfGenericGroupFun a ≥ 10 ]


end Tests.Issue9
