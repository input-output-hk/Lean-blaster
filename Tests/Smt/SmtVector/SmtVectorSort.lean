import Blaster

namespace Test.SmtVectorSort

/-! # Vector sort translation -/

#blaster [∀ (v : Vector Int 3), v = v]

#blaster [∀ (v : Vector (BitVec 8) 4), v = v]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (v w : Vector Int 3), v = w]
