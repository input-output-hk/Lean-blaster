import Lean
import Solver.Command.Tactic

namespace Test.SmtLtArith

#solve [∀ (m n x : Nat), m + x < n + x → m < n]
#solve [∀ (m n x : Int), m + x < n + x → m < n]

#solve (only-optimize: 1) [∀ (x : Nat), 10 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 100 + x]

#solve (only-optimize: 1) [∀ (x : Int), 10 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 100 + x]

end Test.SmtLtArith
