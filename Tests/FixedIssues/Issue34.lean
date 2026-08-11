import Lean
import Blaster

namespace Tests.Issue34

-- Issue 1: unexpected falsified
-- Diagnosis: The shared helpers that constant fold integer division and modulo hardcode Int.ediv and Int.emod.
--            These helpers are also used by tdiv, fdiv, tmod, and fmod.
--            On negative operands the rounding conventions disagree,
--            so blaster folds to the wrong literal and returns an incorrect verdict.


-- Should be valid
#blaster [(-7: Int).tdiv 2 = -3]
-- Should be falsified
#blaster (solve-result: 1) [(-7: Int).tdiv 2 = -4]

-- Should be falsified
#blaster (solve-result: 1) [(-7: Int).fdiv 2 = -3]
-- Should be valid
#blaster [(-7: Int).fdiv 2 = -4]

-- Should be valid
#blaster [(-7: Int).tmod 2 = -1]
-- Should be falsified
#blaster (solve-result: 1) [(-7: Int).tmod 2 = 1]

-- Should be falsified
#blaster (solve-result: 1) [(-7: Int).fmod 2 = -1]
-- Should be valid
#blaster [(-7: Int).fmod 2 = 1]
end Tests.Issue34
