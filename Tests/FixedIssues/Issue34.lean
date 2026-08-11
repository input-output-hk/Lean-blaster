import Lean
import Blaster

namespace Tests.Issue34

-- Issue: unexpected falsified
-- Diagnosis: The shared helpers that constant fold integer division and modulo hardcode Int.ediv and Int.emod.
--            These helpers are also used by tdiv, fdiv, tmod, and fmod.
--            On negative operands the rounding conventions disagree,
--            so blaster folds to the wrong literal and returns an incorrect verdict.


-- tdiv truncates toward zero: -7 / 2 = -3   (ediv folds to -4)
#blaster [(-7 : Int).tdiv 2 = -3]
#blaster (gen-cex: 0) (solve-result: 1) [(-7 : Int).tdiv 2 = -4]

-- tmod takes the sign of the dividend: -7 % 2 = -1   (emod folds to 1)
#blaster [(-7 : Int).tmod 2 = -1]
#blaster (gen-cex: 0) (solve-result: 1) [(-7 : Int).tmod 2 = 1]

-- fdiv floors toward -∞: 7 / -2 = -4   (ediv folds to -3)
#blaster [(7 : Int).fdiv (-2) = -4]
#blaster (gen-cex: 0) (solve-result: 1) [(7 : Int).fdiv (-2) = -3]

-- fmod takes the sign of the divisor: 7 % -2 = -1   (emod folds to 1)
#blaster [(7 : Int).fmod (-2) = -1]
#blaster (gen-cex: 0) (solve-result: 1) [(7 : Int).fmod (-2) = 1]
end Tests.Issue34
