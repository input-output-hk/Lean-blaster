import Blaster

namespace Test.SmtBitVecHyp

/-! # BitVec in theorem-hypothesis position (tactic mode).

Same normalization regression as `Fin`: a parameterized indexed type whose
bound arrives as a proj-form `OfNat.ofNat 8` from a reverted hypothesis binder
must canonicalize to the same cache key as the literal form, or the qualifier
lookup misses. (Masked for nullary types like `UInt8`, and for props that fold
to `True` such as reflexive `x = x`.) -/

theorem bv_hyp_comm (x y : BitVec 8) : x &&& y = y &&& x := by blaster

theorem bv_hyp_add (x : BitVec 8) : x + 0#8 = x := by blaster

end Test.SmtBitVecHyp
