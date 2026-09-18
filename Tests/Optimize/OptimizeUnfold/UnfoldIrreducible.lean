import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldIrreducible

/-! ## Test objectives to validate that `@[irreducible]` definitions are not unfolded

    `getFunBody` reads a non-recursive definition's value straight out of the environment, so
    unlike the `Expr.proj` case -- which reduces through `whnf` and therefore honours the
    reducibility setting already -- the setting has to be consulted explicitly. A sealed
    definition reaches the solver as an uninterpreted function, exactly like an `opaque`,
    which is what makes a goal stated over it provable from premises *about* it instead of
    from its body. -/

/-! Unsealed, for contrast: the body is unfolded, as `UnfoldFun` pins in more detail. -/

def f (a : Nat) (b : Nat) : Nat := a + b
#testOptimize [ "UnfoldIrreducible_1" ] ∀ (x y : Nat), f x y = x + y ===> True

def g (a : Nat) (b : Nat) : Nat := a + b
#blaster [∀ (x y : Nat), g x y = x + y]
#blaster [∀ (x y : Nat), g x y = g y x]

/-! Sealed from here on. The attribute is `local`, so it cannot escape this file, and it
    takes effect at this position, so the tests above measure the unsealed behaviour. -/

attribute [local irreducible] g

/-! The body is no longer reachable, so the application is left as it stands. -/

#testOptimize [ "UnfoldIrreducible_2" ] ∀ (x y : Nat), g x y = x + y ===>
                                        ∀ (x y : Nat), Nat.add x y = g x y

/-! And `g` is now a genuine uninterpreted function: congruence holds, nothing else does. -/

#blaster [∀ (a b c d : Nat), a = c → b = d → g a b = g c d]
#blaster (solve-result: 1) (gen-cex: 0) [∀ (x y : Nat), g x y = x + y]
#blaster (solve-result: 1) (gen-cex: 0) [∀ (x y : Nat), g x y = g y x]

/-! A premise over the sealed symbol is usable, which is the reason to seal one. -/

#blaster [(∀ (x y : Nat), g x y = 7) → ∀ (x y : Nat), g (g x y) y = 7]

/-! Definitions `Lean` itself marks `@[irreducible]` -- every function compiled by
    well-founded recursion, `Nat.gcd` among them -- are unfolded through their equation
    theorems rather than through their value, so they must be unaffected. -/

#blaster [Nat.gcd   12  18 =  6]
#blaster [Nat.gcd 1071 462 = 21]

end Tests.UnfoldIrreducible
