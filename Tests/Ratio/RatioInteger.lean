import Ratio.Ratio

open Ratio

namespace Tests.Ratio.RatioInteger

/- RatioGtIntegerBasics -/

-- RATIO_GT_INTEGER_CONSTANT_1: ~ R_ZERO > 0
#blaster [ (ratioGtInteger R_ZERO 0) = false ]

-- RATIO_GT_INTEGER_CONSTANT_2: R_ONE > 0
#blaster [ (ratioGtInteger R_ONE 0) = true ]

-- RATIO_GT_INTEGER_CONSTANT_3: R_HALF > 0
#blaster [ (ratioGtInteger R_HALF 0) = true ]

-- RATIO_GT_INTEGER_CONSTANT_4: (32/3) > 10
#blaster [ (ratioGtInteger (ratio 32 3) 10) = true ]

-- RATIO_GT_INTEGER_CONSTANT_5: ~ (15/3) > 10
#blaster [ (ratioGtInteger (ratio 15 3) 10) = false ]

-- RATIO_GT_INTEGER_CONSTANT_6: ~ (16/13) > 16
#blaster [ (ratioGtInteger (ratio 16 13) 16) = false ]

-- RATIO_GT_INTEGER_CONSTANT_7: ~ (-16/13) > 16
#blaster [ (ratioGtInteger (ratio (-16) 13) 16) = false ]

-- RATIO_GT_INTEGER_CONSTANT_8: (209/13) > 16
#blaster [ (ratioGtInteger (ratio 209 13) 16) = true ]

-- RATIO_GT_INTEGER_CONSTANT_9: ~ (208/13) > 16
#blaster [ (ratioGtInteger (ratio 208 13) 16) = false ]

-- RATIO_GT_INTEGER_CONSTANT_10: ~ (208/-13) > 16
#blaster [ (ratioGtInteger (ratio 208 (-13)) 16) = false ]

/- RatioGtIntegerValidity -/

-- RATIO_GT_INTEGER_NOT_VALIDRATIO
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (ratioGtInteger a i) = false ]

-- RATIO_GT_INTEGER_CORRECTNESS
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (ratioGtInteger a i == gtRatio a (fromInteger i)) = true ]

/- RatioGeqIntegerBasics -/

-- RATIO_GEQ_INTEGER_CONSTANT_1: R_ZERO >= 0
#blaster [ (ratioGeqInteger R_ZERO 0) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_2: R_ONE >= 0
#blaster [ (ratioGeqInteger R_ONE 0) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_3: R_HALF >= 0
#blaster [ (ratioGeqInteger R_HALF 0) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_4: (32/3) >= 10
#blaster [ (ratioGeqInteger (ratio 32 3) 10) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_5: ~ (15/3) >= 10
#blaster [ (ratioGeqInteger (ratio 15 3) 10) = false ]

-- RATIO_GEQ_INTEGER_CONSTANT_6: ~ (16/13) >= 16
#blaster [ (ratioGeqInteger (ratio 16 13) 16) = false ]

-- RATIO_GEQ_INTEGER_CONSTANT_7: ~ (-16/13) >= 16
#blaster [ (ratioGeqInteger (ratio (-16) 13) 16) = false ]

-- RATIO_GEQ_INTEGER_CONSTANT_8: (209/13) >= 16
#blaster [ (ratioGeqInteger (ratio 209 13) 16) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_9: (208/13) >= 16
#blaster [ (ratioGeqInteger (ratio 208 13) 16) = true ]

-- RATIO_GEQ_INTEGER_CONSTANT_10: ~ (208/-13) >= 16
#blaster [ (ratioGeqInteger (ratio 208 (-13)) 16) = false ]

/- RatioGeqIntegerValidity -/

-- RATIO_GEQ_INTEGER_NOT_VALIDRATIO
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (ratioGeqInteger a i) = false ]

-- RATIO_GEQ_INTEGER_CORRECTNESS
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (ratioGeqInteger a i == geqRatio a (fromInteger i)) = true ]

/- RatioLtIntegerBasics -/

-- RATIO_LT_INTEGER_CONSTANT_1: ~ R_ZERO < 0
#blaster [ (ratioLtInteger R_ZERO 0) = false ]

-- RATIO_LT_INTEGER_CONSTANT_2: R_ZERO < 1
#blaster [ (ratioLtInteger R_ZERO 1) = true ]

-- RATIO_LT_INTEGER_CONSTANT_3: R_HALF < 1
#blaster [ (ratioLtInteger R_HALF 1) = true ]

-- RATIO_LT_INTEGER_CONSTANT_4: ~ (32/3) < 10
#blaster [ (ratioLtInteger (ratio 32 3) 10) = false ]

-- RATIO_LT_INTEGER_CONSTANT_5: (15/3) < 10
#blaster [ (ratioLtInteger (ratio 15 3) 10) = true ]

-- RATIO_LT_INTEGER_CONSTANT_6: (16/13) < 16
#blaster [ (ratioLtInteger (ratio 16 13) 16) = true ]

-- RATIO_LT_INTEGER_CONSTANT_7: (-16/13) < 16
#blaster [ (ratioLtInteger (ratio (-16) 13) 16) = true ]

-- RATIO_LT_INTEGER_CONSTANT_8: ~ (209/13) < 16
#blaster [ (ratioLtInteger (ratio 209 13) 16) = false ]

-- RATIO_LT_INTEGER_CONSTANT_9: ~ (208/13) < 16
#blaster [ (ratioLtInteger (ratio 208 13) 16) = false ]

-- RATIO_LT_INTEGER_CONSTANT_10: (208/-13) < 16
#blaster [ (ratioLtInteger (ratio 208 (-13)) 16) = true ]

/- RatioLtIntegerValidity -/

-- RATIO_LT_INTEGER_NOT_VALIDRATIO
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (ratioLtInteger a i) = false ]

-- RATIO_LT_INTEGER_CORRECTNESS
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (ratioLtInteger a i == ltRatio a (fromInteger i)) = true ]

/- RatioLeqIntegerBasics -/

-- RATIO_LEQ_INTEGER_CONSTANT_1: R_ZERO <= 0
#blaster [ (ratioLeqInteger R_ZERO 0) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_2: ~ R_ONE <= 0
#blaster [ (ratioLeqInteger R_ONE 0) = false ]

-- RATIO_LEQ_INTEGER_CONSTANT_3: R_HALF <= 1
#blaster [ (ratioLeqInteger R_HALF 1) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_4: ~ (32/3) <= 10
#blaster [ (ratioLeqInteger (ratio 32 3) 10) = false ]

-- RATIO_LEQ_INTEGER_CONSTANT_5: (15/3) <= 10
#blaster [ (ratioLeqInteger (ratio 15 3) 10) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_6: (16/13) <= 16
#blaster [ (ratioLeqInteger (ratio 16 13) 16) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_7: (-16/13) <= 16
#blaster [ (ratioLeqInteger (ratio (-16) 13) 16) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_8: ~ (209/13) <= 16
#blaster [ (ratioLeqInteger (ratio 209 13) 16) = false ]

-- RATIO_LEQ_INTEGER_CONSTANT_9: (208/13) <= 16
#blaster [ (ratioLeqInteger (ratio 208 13) 16) = true ]

-- RATIO_LEQ_INTEGER_CONSTANT_10: (208/-13) <= 16
#blaster [ (ratioLeqInteger (ratio 208 (-13)) 16) = true ]

/- RatioLeqIntegerValidity -/

-- RATIO_LEQ_INTEGER_NOT_VALIDRATIO
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (ratioLeqInteger a i) = false ]

-- RATIO_LEQ_INTEGER_CORRECTNESS
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (ratioLeqInteger a i == leqRatio a (fromInteger i)) = true ]

end Tests.Ratio.RatioInteger
