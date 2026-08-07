import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeIntEDiv

/-! ## Tests for the div cancellation proof steps on `Int.ediv`.
    Cases: `n / n ==> 1` and `(m * n) / m | (n * m) / m ==> n`, each under a
    hypothesis ensuring the divisor is nonzero (`0 < n`, `n < 0`, or `0 ≠ n`). -/

/-! `n / n ==> 1`. -/

-- x / x = 1  (with 0 < x)
#testOptimize [ "IntEDivSelf_1", proof ]
  ∀ (x : Int), 0 < x → x / x = 1 ===> True

-- x / x = 1  (with 0 ≠ x)
#testOptimize [ "IntEDivSelf_2", proof ]
  ∀ (x : Int), 0 ≠ x → x / x = 1 ===> True

-- x / x = 1  (with x < 0)
#testOptimize [ "IntEDivSelf_3", proof ]
  ∀ (x : Int), x < 0 → x / x = 1 ===> True

-- (x + 0) / (x + 0) = 1  (operands reduced to the same fvar)
#testOptimize [ "IntEDivSelf_4", proof ]
  ∀ (x : Int), 0 < x → (x + 0) / (x + 0) = 1 ===> True

/-! `(m * n) / m ==> n` and `(n * m) / m ==> n`. -/

-- (x * y) / y = x  (with 0 < y)
#testOptimize [ "IntMulEDivCancel_1", proof ]
  ∀ (x y : Int), 0 < y → (x * y) / y = x ===> True

-- (y * x) / y = x  (with 0 < y)
#testOptimize [ "IntMulEDivCancel_2", proof ]
  ∀ (x y : Int), 0 < y → (y * x) / y = x ===> True

-- (x * y) / y = x  (with 0 ≠ y)
#testOptimize [ "IntMulEDivCancel_3", proof ]
  ∀ (x y : Int), 0 ≠ y → (x * y) / y = x ===> True

-- (y * x) / y = x  (with y < 0)
#testOptimize [ "IntMulEDivCancel_4", proof ]
  ∀ (x y : Int), y < 0 → (y * x) / y = x ===> True

end Test.OptimizeIntEDiv
