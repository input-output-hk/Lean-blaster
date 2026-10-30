import Blaster

namespace Tests.Issue195

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/152
--        `@isFun` membership unsatisfiable for lambdas over qualified codomain arrows.
-- Diagnosis: There is a need to consider predicate qualifiers for arguments when defining the @isFun predicate
--            Since we now use Array to model HOF, there is a need to generate a default codomain value, which
--            is used only when the predicate qualifiers on the arguments are not satisfied.
--            This is essential to guarantee extenstionality.
--            Hence, the @isFun predicate is now defined as follows:
--              - `(declare-const @default_codmain{n} sαₙ)`
--              - `(assert (@isTypeₙ @default_codmain{n}))`
--              - `(declare-fun @isFun.xxx ((@g₀ gt₀) .. (@gₘ gtₘ) (@f st)) Bool
--                   (forall ((@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁))
--                     (ite (and (@isType₁ @x₁) ... (@isType₁ @xₙ₋₁))
--                          (@isTypeₙ (select @f @x₁ ... @xₙ₋₁))
--                          (= (select @f @x₁ ... @xₙ₋₁) @default_codmain{n}))))`

-- 1. True by funext; needs `@apply_ext_fun`, whose `@isFun` premises were vacuous.
--    Reported ❌ Falsified before the fix."
#blaster (solve-result: 0) [∀ (f : Nat → Nat), (∀ x, f x = x + 1) → f = fun x => x + 1]

-- 2. Congruence through a hypothesis equality with a lambda; pins the guarded path.
--    (Also "Valid" before the fix, but only because the context was inconsistent.)
#blaster (solve-result: 0) [∀ (f : Nat → Nat), f = (fun x => x + 1) → f 2 = 3]

-- 3. The unsoundness vector: this statement is FALSE (take f := fun x => x + 1).
--    Reported ✅ Valid before the fix: `(assert (@isFun $f))` + `$f = L` +
--    unguarded cstr forced `∀ x:Int. @isNat (@apply L x)`, contradicting the
--    def_cstr's off-domain value `(@apply L -2) = -1`. Falsified is the honest answer.

def example_fun_cex_1 := ∀ (f : Nat → Nat), (f = fun x => x + 1) → False
#blaster (gen-cex: 0) (solve-result: 1) [example_fun_cex_1]

def example_fun_cex_2 := ∀ (g : (Nat → Nat) → Nat), g (fun x => x * (x + 1)) + g (fun x => x) = 1000 → False
#blaster (gen-cex: 0) (solve-result: 1) [example_fun_cex_2]


end Tests.Issue195
