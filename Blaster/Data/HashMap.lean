import Lean

namespace Blaster.Data.HashMap

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- Per-slot control byte: `0` = empty, `1` = tombstone (erased), and
      otherwise `0x80 ||| top 7 bits` of the scrambled hash of the key
      stored in the same slot — so "occupied" is exactly "high bit set".
      `ctrl.size` is always a power of two ≥ 8. -/
  ctrl : ByteArray
  /-- Interleaved entries: key of slot `i` at `2i`, value at `2i + 1`,
      both `unsafeCast` to `NonScalar`. Either empty (before the first
      `insert`) or of size `2 * ctrl.size`, with unoccupied pairs holding
      an arbitrary placeholder (the first key ever inserted, or — after
      an `erase` — a duplicate of a neighboring slot's pair). -/
  slots : Array NonScalar
  /-- Number of entries stored. -/
  size : Nat
  /-- Number of tombstones. `size + tombs` is the number of non-empty
      control bytes and drives the load factor, so probe sequences stay
      bounded no matter how many erasures happen between rehashes. -/
  tombs : Nat

namespace HashMap

variable {α : Type u} {β : Type v} [Inhabited α] [BEq α] [Hashable α]

/-- Fold the high 32 bits of the hash into the low bits (see
    `Bench.HashSet.scramble`). -/
@[always_inline, inline] private def scramble (h : UInt64) : UInt64 :=
  h ^^^ (h >>> 32)

/-- Control byte for an occupied slot: tag bit + top 7 bits of the
    (scrambled) hash. -/
@[always_inline, inline] private def fragOf (h : UInt64) : UInt8 :=
  (h >>> 57).toUInt8 ||| 0x80

/-- 4096 zero bytes, built once per program run (a closed term). -/
private def zeroChunk : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 4096
  for _ in [0:4096] do
    b := b.push 0
  return b

/-- An all-zero control array of `n` bytes in a **single allocation**:
    reserve the full capacity, then `memcpy` the static zero chunk in.
    (The previous doubling `b ++ b` build allocated log₂ n intermediate
    arrays per table creation/resize.) -/
private def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut k := 0
  while k < n do
    b := zeroChunk.copySlice 0 b k (min 4096 (n - k)) false
    k := k + 4096
  return b

/-- Create an empty map. The real capacity is the next power of two `≥ max capacity 8`. -/
def emptyWithCapacity (capacity : Nat := 8) : HashMap α β :=
  ⟨zeroBytes (Nat.nextPowerOfTwo (max capacity 8)), #[], 0, 0⟩

instance : EmptyCollection (HashMap α β) := ⟨emptyWithCapacity⟩
instance : Inhabited (HashMap α β) := ⟨∅⟩

/-! ## Lookups -/

@[specialize] private unsafe def containsImpl (m : HashMap α β) (a : α) : Bool :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := m.ctrl.usize - 1
  let rec go (i : USize) : Bool :=
    let c := m.ctrl.uget i lcProof
    if c == 0 then
      false
    else if c == frag then
      let x : α := unsafeCast (m.slots.uget (i <<< 1) lcProof)
      if ptrEq x a || x == a then true
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- `O(1)` expected; touches only the control array and the key half of
    the probed pair. -/
@[inline] def contains (m : HashMap α β) (a : α) : Bool :=
  unsafe containsImpl m a

@[specialize] private unsafe def getDImpl (m : HashMap α β) (a : α) (fallback : β) : β :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := m.ctrl.usize - 1
  let rec go (i : USize) : β :=
    let c := m.ctrl.uget i lcProof
    if c == 0 then
      fallback
    else if c == frag then
      let x : α := unsafeCast (m.slots.uget (i <<< 1) lcProof)
      if ptrEq x a || x == a then
        -- the value shares the key's cache line 75% of the time
        unsafeCast (m.slots.uget ((i <<< 1) + 1) lcProof)
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- Value for `a`, or `fallback` if absent. `O(1)` expected and
    allocation-free (unlike `get?`, which boxes the result in `some`).

    Declared via `@[implemented_by]` because the `unsafe` term wrapper
    requires `Nonempty` of the closed function type, which is not
    synthesizable for a bare `β` result. Safe code cannot decode the
    untyped slots, so no faithful safe model exists either; the model
    body is a stub and only `getDImpl` is ever executed. -/
@[implemented_by getDImpl]
def getD (_m : HashMap α β) (_a : α) (fallback : β) : β :=
  fallback

@[always_inline, inline, specialize] private unsafe def get?Impl (m : HashMap α β) (a : α) : Option β :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := m.ctrl.usize - 1
  let rec go (i : USize) : Option β :=
    let c := m.ctrl.uget i lcProof
    if c == 0 then
      none
    else if c == frag then
      let x : α := unsafeCast (m.slots.uget (i <<< 1) lcProof)
      if ptrEq x a || x == a then some (unsafeCast (m.slots.uget ((i <<< 1) + 1) lcProof))
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- Value for `a`, if present. `O(1)` expected. -/
@[always_inline, inline] def get? (m : HashMap α β) (a : α) : Option β :=
  unsafe get?Impl m a

/-! ## `insert` -/

/-- Rehash all *live* entries (tombstones are dropped). If the live load
    is at least 1/2 the table quadruples (see `Bench.HashSet.growImpl`
    for why ×4); otherwise (the table is mostly tombstones) it is rebuilt
    at the same capacity, which just cleans the tombstones out. `filler`
    (any key) initializes the unoccupied pairs of the new `slots` array.
    Stored control bytes are reused — they are a pure function of the
    hash. -/
@[specialize] private unsafe def growImpl
    (ctrl : ByteArray) (slots : Array NonScalar) (size : Nat) : HashMap α β :=
  -- ×4 while small, ×2 from 2^27 slots up — same reasoning as
  -- `Bench.HashSet.growImpl`: at large sizes the ×4 transient old+new
  -- peak and retained slack dominate the fewer-rehashes saving.
  let newCap :=
    if size * 2 ≥ ctrl.size then
      if ctrl.size ≥ 134217728 then ctrl.size * 2 else ctrl.size * 4
    else ctrl.size
  let mask := newCap.toUSize - 1
  let rec findEmpty (nctrl : ByteArray) (j : USize) : USize :=
    if nctrl.uget j lcProof == 0 then j else findEmpty nctrl ((j + 1) &&& mask)
  let rec copy (i : Nat) (nctrl : ByteArray) (nslots : Array NonScalar) : HashMap α β :=
    if i < ctrl.size then
      let c := ctrl.uget i.toUSize lcProof
      if c &&& 0x80 == 0 then  -- empty or tombstone
        copy (i + 1) nctrl nslots
      else
        let k := i.toUSize <<< 1
        let x : α := unsafeCast (slots.uget k lcProof)
        let v := slots.uget (k + 1) lcProof
        let j := findEmpty nctrl ((scramble (hash x)).toUSize &&& mask)
        let l := j <<< 1
        copy (i + 1) (nctrl.uset j c lcProof)
          ((nslots.uset l (unsafeCast x) lcProof).uset (l + 1) v lcProof)
    else
      ⟨nctrl, nslots, size, 0⟩
  copy 0 (zeroBytes newCap) (Array.replicate (newCap * 2) (unsafeCast (default : α)))

/-- Mutation step of `insertImpl`, applied to the read-only probe's
    outcome `r` (see `insertImpl` for the encoding): at most one
    copy-on-write per array even when the map is shared, and exactly one
    record (re)construction. A separate definition rather than the tail
    of `insertImpl` because the kernel hits its recursion limit when a
    `let rec` result is used as a `uset` index in the same definition
    body; as a plain parameter it typechecks instantly. -/
@[specialize] private unsafe def insertFinish
    (m : HashMap α β) (a : α) (b : β) (frag : UInt8) (szu cap r : USize) (insertIfNew := false) : HashMap α β :=
  if r < cap then
    let ⟨ctrl, slots, size, tombs⟩ := m
    -- consume the empty slot `r`; first insert materializes the pair
    -- array, with `a` filling both halves
    let slots := if slots.isEmpty then Array.replicate (ctrl.size * 2) (unsafeCast (default : α)) else slots
    let ctrl := ctrl.uset r frag lcProof
    let k := r <<< 1
    -- the two stores share a cache line 75% of the time
    let slots := slots.uset k (unsafeCast a) lcProof
    let slots := slots.uset (k + 1) (unsafeCast b) lcProof
    -- grow when load factor (incl. tombstones) > 3/4
    if szu * 4 > cap * 3 then
      growImpl ctrl slots (size + 1)
    else
      ⟨ctrl, slots, size + 1, tombs⟩
  else if r < cap + cap then
    if insertIfNew then
      -- key already present: return untouched
      m
    else
      let ⟨ctrl, slots, size, tombs⟩ := m
      -- key already present: replace the value (`Std.HashMap.insert` semantics)
      let i := r - cap
      ⟨ctrl, slots.uset ((i <<< 1) + 1) (unsafeCast b) lcProof, size, tombs⟩
  else
    let ⟨ctrl, slots, size, tombs⟩ := m
    -- reclaim a tombstone: occupancy is unchanged, so no growth check
    let i := r - cap - cap
    let slots := if slots.isEmpty then Array.replicate (ctrl.size * 2) (unsafeCast (default : α)) else slots
    let ctrl := ctrl.uset i frag lcProof
    let k := i <<< 1
    let slots := slots.uset k (unsafeCast a) lcProof
    let slots := slots.uset (k + 1) (unsafeCast b) lcProof
    ⟨ctrl, slots, size + 1, tombs - 1⟩

@[specialize] private unsafe def insertImpl (m : HashMap α β) (a : α) (b : β) (insertIfNew := false) : HashMap α β :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := m.ctrl.usize - 1
  -- occupancy-after-insert (incl. tombstones) and capacity as USize, for
  -- a machine-arithmetic load check
  let szu := (m.size + m.tombs).toUSize + 1
  let cap := mask + 1
  -- Read-only probe: borrows `m`, allocates nothing, touches no
  -- refcounts. Outcome encoding (slot indices are < `cap`, ranges
  -- disjoint): `i` = insert into empty slot `i`; `cap + i` = key found
  -- at `i` (replace its value); `2*cap + i` = reclaim the tombstone at
  -- `i`. `free`/`hasFree` remember the first tombstone passed: if the
  -- probe proves `a` absent, the new key reclaims that slot instead of
  -- consuming an empty one.
  -- (An earlier version threaded the whole record through the loop to
  -- enable reset/reuse — optimal when the map is exclusively owned, but
  -- on a *shared* map it allocated a fresh record and inc/dec'd all
  -- fields on every probe step.)
  let rec probe (i free : USize) (hasFree : Bool) : USize :=
    let c := m.ctrl.uget i lcProof
    if c == 0 then
      if hasFree then cap + cap + free else i
    else if c == frag then
      let x : α := unsafeCast (m.slots.uget (i <<< 1) lcProof)
      if ptrEq x a || x == a then cap + i
      else probe ((i + 1) &&& mask) free hasFree
    else if c == 1 then
      probe ((i + 1) &&& mask) (if hasFree then free else i) true
    else
      probe ((i + 1) &&& mask) free hasFree
  insertFinish m a b frag szu cap (probe (h.toUSize &&& mask) 0 false) insertIfNew


/-- Insert the entry `a ↦ b`; if `a` is already present its value is
    replaced. `O(1)` amortized expected. In-place when used linearly. -/
@[inline] def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  unsafe insertImpl m a b

/-- Insert the entry `a ↦ b` only if `a` is NOT already present.
    `O(1)` amortized expected. In-place when used linearly. -/
@[inline] def insertIfNew (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  unsafe insertImpl m a b (insertIfNew := true)

/-! ## `erase` -/

/-- Mutation step of `eraseImpl` (`r == cap` means "not found"); a
    separate definition for the same kernel-limit reason as
    `insertFinish`. Tombstones the slot, and replaces *both* halves of
    its stale pair with the neighbor's (already array-owned) ones so the
    erased key and value do not stay artificially alive. -/
@[specialize] private unsafe def eraseFinish
    (m : HashMap α β) (mask cap r : USize) : HashMap α β :=
  if r == cap then
    m  -- not present: returned untouched, no allocation at all
  else
    let ⟨ctrl, slots, size, tombs⟩ := m
    let ctrl := ctrl.uset r 1 lcProof
    let k := r <<< 1
    let nb := ((r + 1) &&& mask) <<< 1
    let slots := slots.uset k (slots.uget nb lcProof) lcProof
    let slots := slots.uset (k + 1) (slots.uget (nb + 1) lcProof) lcProof
    ⟨ctrl, slots, size - 1, tombs + 1⟩

/-- Tombstone deletion (the SwissTable strategy), identical in spirit to
    `Bench.HashSet.erase`: the slot's control byte becomes `1`, so
    `contains`/`getD`/`get?` need no changes (a tombstone simply falls
    into the existing "no match, keep probing" branch) and erase itself
    does no neighbor hashing. Tombstones count toward the load factor and
    are swept out by the rehash in `growImpl`, so probe lengths stay
    bounded under churn. -/
@[specialize] private unsafe def eraseImpl (m : HashMap α β) (a : α) : HashMap α β :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := m.ctrl.usize - 1
  let cap := mask + 1
  -- read-only probe (see `insertImpl`): returns the match's slot index,
  -- or `cap` (an impossible slot) if `a` is absent
  let rec probe (i : USize) : USize :=
    let c := m.ctrl.uget i lcProof
    if c == 0 then
      cap
    else if c == frag then
      let x : α := unsafeCast (m.slots.uget (i <<< 1) lcProof)
      if ptrEq x a || x == a then i
      else probe ((i + 1) &&& mask)
    else
      probe ((i + 1) &&& mask)
  -- nothing was ever inserted: `slots` may not be materialized yet
  if m.slots.isEmpty then m
  else
    eraseFinish m mask cap (probe (h.toUSize &&& mask))

/-- Remove the entry for `a`; if `a` is absent the map is unchanged.
    `O(1)` expected. The table never shrinks (matching `Std.HashMap`),
    but heavily-erased tables are compacted by the tombstone sweep on the
    next rehash. -/
@[inline] def erase (m : HashMap α β) (a : α) : HashMap α β :=
  unsafe eraseImpl m a

/-! ## Diagnostics -/

@[specialize] private unsafe def probeStatsImpl (m : HashMap α β) : Nat × Float × Nat :=
  let cap := m.ctrl.size
  if m.slots.isEmpty || m.size == 0 then
    (cap, 0.0, 0)
  else
    let rec go (i total maxd : Nat) : Nat × Float × Nat :=
      if i < cap then
        if m.ctrl.uget i.toUSize lcProof &&& 0x80 != 0 then  -- occupied (not empty, not tombstone)
          let x : α := unsafeCast (m.slots.uget (i.toUSize <<< 1) lcProof)
          let home := (scramble (hash x)).toNat % cap
          let d := (i + cap - home) % cap
          go (i + 1) (total + d) (max maxd d)
        else
          go (i + 1) total maxd
      else
        (cap, total.toFloat / m.size.toFloat, maxd)
    go 0 0 0

/-- `(capacity, average probe distance, max probe distance)` — see
    `Bench.HashSet.probeStats`. Not performance-sensitive (but still
    `unsafe` underneath: safe code cannot decode the untyped slots). -/
def probeStats (m : HashMap α β) : Nat × Float × Nat :=
  unsafe probeStatsImpl m

@[specialize] private unsafe def valsImpl (m : HashMap α β) : Array β := Id.run do
  let cap := m.ctrl.size
  if m.slots.isEmpty || m.size == 0 then
    return #[]
  let mut out := Array.emptyWithCapacity m.size
  for i in [0:cap] do
    if m.ctrl.uget i.toUSize lcProof &&& 0x80 != 0 then  -- occupied (not empty, not tombstone)
      out := out.push (unsafeCast (m.slots.uget ((i.toUSize <<< 1) + 1) lcProof))
  return out

/-- All live values, in slot order. `O(capacity)`; intended for diagnostics
    only (retention profiling of nested tables), never on a hot path.
    `@[implemented_by]` for the same reason as `getD`: safe code cannot
    decode the untyped slots. -/
@[implemented_by valsImpl]
def vals (_m : HashMap α β) : Array β :=
  #[]

end HashMap

end Blaster.Data.HashMap
