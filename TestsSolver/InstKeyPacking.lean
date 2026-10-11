import Blaster

namespace Test.InstKeyPacking

open Blaster.Optimize

/-! `InstKey` packs an object address and a binder offset for the
    instantiation/abstraction and beta-reduction caches. It must be injective
    for every 8-byte-aligned user-space address below 2^52 (48-bit address
    spaces such as aarch64 place heap objects at `0xffff…`, above 2^47).

    The former packing `addr ||| (offset <<< 47)` mapped the pairs below to the
    same key, so a cache lookup for one subterm could return the cached result
    of another. On aarch64 this showed up as nondeterministic, wrong
    translation errors in `Tests/Smt/SmtLtArith.lean` and wrong verdicts in
    `Tests/Smt/SmtNat/SmtNatMul.lean` under parallel builds. -/

-- An aarch64-style heap address with bit 47 set
private def highAddr : USize := 0xffffb8f42010
-- The address that collided with it under the old packing, one offset higher
private def lowAddr : USize := highAddr - ((1 : USize) <<< 47)

-- Old packing collided on these pairs
#guard (highAddr ||| ((0 : USize) <<< 47)) == (lowAddr ||| ((1 : USize) <<< 47))
-- New packing distinguishes them
#guard (packInstKey highAddr 0).packed != (packInstKey lowAddr 1).packed

-- Same address, different offsets (scalar path)
#guard (packInstKey highAddr 0).packed != (packInstKey highAddr 1).packed
#guard (packInstKey highAddr 8191).packed != (packInstKey highAddr 8190).packed
-- Different aligned addresses, same offset
#guard (packInstKey highAddr 5).packed != (packInstKey (highAddr + 8) 5).packed
-- Largest supported address (2^52 - 8) does not reach the offset bits
#guard (packInstKey (((1 : USize) <<< 52) - 8) 0).packed != (packInstKey 0 1).packed

-- Scalar fast path stays below 2^63 (no bignum allocation)
#guard (packInstKey (((1 : USize) <<< 52) - 8) 8191).packed < 2 ^ 63
-- The bignum path (offset ≥ 2^13) is exact and agrees in layout
#guard (packInstKey highAddr 8192).packed == ((highAddr >>> 3).toNat ||| ((8192 : Nat) <<< 49))
#guard (packInstKey highAddr 8192).packed != (packInstKey highAddr 8193).packed
#guard (packInstKey highAddr 8191).packed == ((highAddr >>> 3).toNat ||| ((8191 : Nat) <<< 49))

end Test.InstKeyPacking
