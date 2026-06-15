import Blaster

namespace Test.SmtVectorEq

/-! # Vector pointwise equality (faithful over [0,n))

  The key issue: SMT array `=` is extensional over ALL integers, but Lean `Vector α n`
  equality is element-wise over `[0,n)` only. The interception in `translateEq?` rewrites
  `@Eq (Vector α n) v w` into a pointwise conjunction (or bounded forall for n>16),
  making blaster faithful for Vector equality conclusions.
-/

-- Reflexive: always valid under both extensional and pointwise
#blaster [∀ (v : Vector Int 3), v = v]

-- Congruence: hypothesis equality implies element access equality
#blaster [∀ (v w : Vector Int 3), v = w → v.get ⟨0, by omega⟩ = w.get ⟨0, by omega⟩]

-- THE DISCRIMINATOR: agree at ALL indices ⇒ equal (n=2).
-- ✅ Valid under pointwise equality (correct).
-- ❌ Falsified under extensional equality with spurious cex at index 4 (out-of-range).
-- This flip from Falsified→Valid proves the interception is working.
#blaster [∀ (v w : Vector Int 2), v.get ⟨0, by omega⟩ = w.get ⟨0, by omega⟩ → v.get ⟨1, by omega⟩ = w.get ⟨1, by omega⟩ → v = w]

-- Agree at index 0 only must NOT prove equality → Falsified under both (sanity check)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (v w : Vector Int 2), v.get ⟨0, by omega⟩ = w.get ⟨0, by omega⟩ → v = w]

-- n=0: empty vectors are trivially equal → trueSmt → Valid
#blaster [∀ (v w : Vector Int 0), v = w]

-- n>16 bounded-forall: agree at all Fin 20 indices ⇒ equal (exercises bounded-forall path)
#blaster [∀ (v w : Vector Int 20), (∀ i : Fin 20, v.get i = w.get i) → v = w]

-- Equality of Vector (BitVec 8): discriminator for non-Int element type
#blaster [∀ (v w : Vector (BitVec 8) 2),
    v.get ⟨0, by omega⟩ = w.get ⟨0, by omega⟩ →
    v.get ⟨1, by omega⟩ = w.get ⟨1, by omega⟩ →
    v = w]

-- Nested Vector equality: `Vector (Vector Int 2) 2` discriminator.
-- The outer equality is pointwise; the inner element equality is ALSO pointwise
-- (each `(select v k) = (select w k)` of type `Vector Int 2` recurses).
-- Without recursive element equality, this would be spuriously Falsified.
#blaster [∀ (v w : Vector (Vector Int 2) 2),
    v.get ⟨0, by omega⟩ = w.get ⟨0, by omega⟩ →
    v.get ⟨1, by omega⟩ = w.get ⟨1, by omega⟩ →
    v = w]

-- NOTE: `v == w` (BEq.beq) on Vector unfolds through Vector.instBEq to `Vector.isEqv`,
-- which uses `Vector.toArray` — an unsupported operation in blaster. The BEq interception
-- added to `translateRelational?` is correct code but in practice unreachable since the
-- optimizer unfolds the BEq instance before translation. Propositional `=` (above) is the
-- canonical equality path for Vector in blaster.

end Test.SmtVectorEq
