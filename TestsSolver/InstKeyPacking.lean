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

/-! ## Addresses outside the packed layout

    The packed layout needs a 64-bit platform and an 8-byte-aligned address
    below 2^52. Anything else (x86-64 LA57 or aarch64 52-bit address spaces,
    tagged pointers, unaligned addresses) must take the exact fallback key
    rather than overlap the offset bits. Without the fallback, `(2^52, 0)`
    and `(0, 1)` both packed to `2^49`. -/

private def two52 : USize := (1 : USize) <<< 52

-- First address past the packed range vs. the offset bit it used to overlap
#guard (packInstKey two52 0).packed != (packInstKey 0 1).packed
#guard ((two52 >>> 3) ||| ((0 : USize) <<< 49)) == ((0 : USize) ||| ((1 : USize) <<< 49))
-- Unaligned addresses no longer lose their low bits
#guard (packInstKey 1 0).packed != (packInstKey 0 0).packed
#guard (packInstKey (highAddr + 4) 7).packed != (packInstKey highAddr 7).packed
-- The fallback range starts at 2^113, above every packed key
#guard (packInstKey two52 0).packed ≥ 2 ^ 113
#guard (packInstKey 1 0).packed ≥ 2 ^ 113
-- The largest packed bignum key stays below 2^113
#guard (packInstKey (two52 - 8) (0 - 1)).packed < 2 ^ 113
-- Fallback vs. packed bignum: a naive `addr ||| (offset <<< 64)` fallback
-- would equal the packed key of `(0, 2^13)` for `(2^62, 0)`
#guard (packInstKey ((1 : USize) <<< 62) 0).packed != (packInstKey 0 8192).packed
-- In-range keys keep the packed layout and the scalar fast path
#guard (packInstKey (two52 - 8) 8191).packed == (((two52 - 8) >>> 3).toNat ||| ((8191 : Nat) <<< 49))
#guard (packInstKey (two52 - 8) 8191).packed < 2 ^ 62

/-- Boundary addresses (in range, unaligned, at/above 2^52, top of the address
    space) and offsets (scalar bound, 2^15 hash period, word extremes). -/
private def boundaryAddrs : List USize :=
  [0, 1, 7, 8, 16, highAddr, lowAddr, highAddr + 4, two52 - 8, two52 - 1, two52, two52 + 8,
   (1 : USize) <<< 55, (1 : USize) <<< 62, (1 : USize) <<< 63, 0 - 8, 0 - 1]

private def boundaryOffsets : List USize :=
  [0, 1, 2, 8190, 8191, 8192, 8193, 32768, 32769, (1 : USize) <<< 15 ||| 8191,
   (1 : USize) <<< 49, (1 : USize) <<< 63, 0 - 1]

private def boundaryKeys : List Nat :=
  boundaryAddrs.flatMap fun a => boundaryOffsets.map fun o => (packInstKey a o).packed

-- Every boundary (address, offset) pair gets its own key
#guard boundaryKeys.length == boundaryAddrs.length * boundaryOffsets.length
#guard boundaryKeys.eraseDups.length == boundaryKeys.length

-- Same address, offsets 2^15 apart: distinct keys and, for fallback keys,
-- distinct hashes (the offset is mixed into the hash)
#guard (packInstKey two52 0).packed != (packInstKey two52 32768).packed
#guard hash (packInstKey two52 0) != hash (packInstKey two52 1)

end Test.InstKeyPacking
