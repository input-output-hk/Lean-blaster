import Tests.Utils

namespace Tests.Issue228

-- The rewrite identity is proved by Lean, including zero factors/divisors.
example (z x y : Nat) : (z * x) % (z * y) = z * (x % y) :=
  Nat.mul_mod_mul_left z x y

#testOptimize ["ModCommonFactorLeftLeft"]
  (∀ x y z : Nat, (z*x) % (z*y) = z*(x%y)) ===> True
#testOptimize ["ModCommonFactorLeftRight"]
  (∀ x y z : Nat, (z*x) % (y*z) = z*(x%y)) ===> True
#testOptimize ["ModCommonFactorRightLeft"]
  (∀ x y z : Nat, (x*z) % (z*y) = z*(x%y)) ===> True
#testOptimize ["ModCommonFactorRightRight"]
  (∀ x y z : Nat, (x*z) % (y*z) = z*(x%y)) ===> True
#testOptimize ["ModCommonFactorZeroDivisor"]
  (∀ x z : Nat, (z*x) % (z*0) = z*x) ===> True
#testOptimize ["ModCommonFactorZeroFactor"]
  (∀ x y : Nat, (0*x) % (0*y) = 0) ===> True
#testOptimize ["ModCommonFactorNested"]
  (∀ a b x y : Nat, (a*(b*x)) % (a*(b*y)) = a*(b*(x%y))) ===> True

#blaster (only-optimize: 1)
  [∀ x y z : Nat, (z*x) % (z*y) = z*(x%y)]
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ x y z : Nat, (z*x) % (z*y) = x%y]

end Tests.Issue228
