import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Probe

-- Probe A: does `==` on the derived BEq instance translate? (addRatio is commutative
-- unconditionally — NaN guard is symmetric, Int + and * commute.)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  (addRatio (ratio a_n a_d) (ratio b_n b_d) == addRatio (ratio b_n b_d) (ratio a_n a_d)) = true ]

-- Probe B: does a term-level `let` inside the proposition translate?
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  (addRatio a b == addRatio b a) = true ]

end Tests.Ratio.Probe
