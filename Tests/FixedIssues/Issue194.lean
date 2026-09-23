
import Blaster

namespace Tests.Issue194

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/152
--        Unexpected Valid on a false theorem, giving a kernel-accepted `False`.
-- Diagnosis: There is a need to consider predicate qualifiers for arguments when defining lambda terms
--          Since we now use Array to model HOF, there is a need to generate a default codomain value, which
--            is used only when the predicate qualifiers on the arguments are not satisfied.
--            This is essential to guarantee extenstionality.
--            Hence, lambda terms must be defined as follows:
--             (lambda (x₁, st₁) ... (xₘ, stₘ) (ite (and (@isType₁ @x₁) ... (@isType₁ @xₘ)) sb default_codomain))
-- The two lambdas below agree on all of Nat exactly when they agree on
-- {0, 1, 2} ∪ {y | y ≥ 3}; with the inconsistent theory Blaster proved the
-- (false) claim Valid for every list. Now it is correctly falsified,
-- e.g. by l = [3].

def lambda_cex_1 : Prop :=
  ∀ (l : List Nat),
     (l.all (fun y => decide (y < 3)) && l.all (fun y => decide (y = 0 ∨ y = 1 ∨ y = 2))) = true

#blaster (gen-cex: 0) (solve-result: 1) [lambda_cex_1]

def lambda_cex_2 : Prop :=
    ∀ (l : List Nat),
    (l.all (fun y => decide (y < 3)) && l.all (fun y => decide (y = 0 ∨ y = 1 ∨ y = 2))) = true

#blaster (gen-cex: 0) (solve-result: 1) [lambda_cex_2]


def optionAny (x : Option Nat) (xs : List Nat) : Bool :=
  match x with
  | none => false
  | some x' => List.any xs (λ y => y == x')

def lambda_cex_3 : Prop :=
  ∀ (x : Option Nat) (xs : List Nat), optionAny x xs → xs.all (λ y => y > 0)

#blaster (gen-cex: 0) (solve-result: 1) [lambda_cex_3]

end Tests.Issue194
