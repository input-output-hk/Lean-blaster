import Blaster

namespace Test.SmtVectorOps

/-! # Vector get/set/push/replicate/getElem -/

#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get ⟨0, by omega⟩ = x]

#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get ⟨1, by omega⟩ = v.get ⟨1, by omega⟩]

-- getElem syntax `v[i]` (reduces to Vector.get via the optimizer)
#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 2 x)[(2 : Fin 5)] = x]

#blaster [∀ (v : Vector Int 3) (x : Int), (v.push x).get ⟨3, by omega⟩ = x]

#blaster [∀ (x : Int) (i : Fin 4), (Vector.replicate 4 x).get i = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get ⟨1, by omega⟩ = x]

-- Vector (BitVec 8) get/set composition
#blaster [∀ (v : Vector (BitVec 8) 4) (x : BitVec 8), (v.set 0 x).get ⟨0, by omega⟩ = x]

#blaster [∀ (v : Vector (BitVec 8) 4) (x : BitVec 8), (v.set 1 x).get ⟨0, by omega⟩ = v.get ⟨0, by omega⟩]

end Test.SmtVectorOps
