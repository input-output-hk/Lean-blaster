import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Addition

/- AdditionBasics -/

-- ADD_ZERO_TWICE: 0 + 0 = 0
#blaster [ ((addRatio R_ZERO R_ZERO == R_ZERO) && eqRatio (addRatio R_ZERO R_ZERO) R_ZERO) = true ]

-- ONE_SUCC: 0 + 1 = 1
#blaster [ ((addRatio R_ZERO R_ONE == R_ONE) && eqRatio (addRatio R_ZERO R_ONE) R_ONE) = true ]

-- ADD_HALF_TWICE: 0.5 + 0.5 = 1
#blaster [ (eqRatio (addRatio R_HALF R_HALF) R_ONE) = true ]

-- ADD_ONE_TWICE: 1 + 1 = 2
#blaster [ ((addRatio R_ONE R_ONE == fromInteger 2) && eqRatio (addRatio R_ONE R_ONE) (fromInteger 2)) = true ]

-- ONE_NEGATE: 1 + (-1) = 0
#blaster [ (addRatio R_ONE (negate R_ONE) == R_ZERO) = true ]

-- ADD_CONSTANTS_1: 85/100 + 15/100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 100)) R_ONE) = true ]

-- ADD_CONSTANTS_2: 85/100 + 150/1000 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 150 1000)) R_ONE) = true ]

-- ADD_CONSTANTS_3: 85/100 + -15/100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) 100)) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_4: 85/100 + 15/-100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 (-100))) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_5: 85/100 + -15/-100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) (-100))) R_ONE) = true ]

end Tests.Ratio.Addition
