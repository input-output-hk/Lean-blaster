import Blaster
namespace Test.SmtIntArith

#blaster [∀ (x y : Int8), x + y = y + x]
#blaster [(127 : Int8) + 1 < (0 : Int8)]
#blaster [∀ (x y : Int8), x < y → ¬ (y < x)]
#blaster [(-1 : Int8) < (0 : Int8)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int8), x ≤ x + 1]
