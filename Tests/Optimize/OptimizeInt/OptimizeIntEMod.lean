import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeIntEMod

/-! ## Tests for the mod cancellation proof steps on `Int.emod`.
    Cases: `n % n ==> 0` and `(m * n) % m | (n * m) % m ==> 0`. These hold
    unconditionally, so no hypothesis is required. -/

/-! `n % n ==> 0`. -/

-- x % x = 0
#testOptimize [ "IntEModSelf_1", proof ]
  ∀ (x : Int), x % x = 0 ===> True

-- (x + 0) % (x + 0) = 0  (operands reduced to the same fvar)
#testOptimize [ "IntEModSelf_2", proof ]
  ∀ (x : Int), (x + 0) % (x + 0) = 0 ===> True

/-! `(m * n) % m ==> 0` and `(n * m) % m ==> 0`. -/

-- (x * y) % x = 0
#testOptimize [ "IntMulEModCancel_1", proof ]
  ∀ (x y : Int), (x * y) % x = 0 ===> True

-- (x * y) % y = 0
#testOptimize [ "IntMulEModCancel_2", proof ]
  ∀ (x y : Int), (x * y) % y = 0 ===> True

end Test.OptimizeIntEMod
