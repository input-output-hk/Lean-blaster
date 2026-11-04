

namespace Blaster.Data.HashSet

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  /-- Per-slot control byte: `0` = empty, `1` = tombstone (erased), and
      otherwise `0x80 ||| top 7 bits` of the scrambled hash of the
      element stored in `data` at the same index — so "occupied" is
      exactly "high bit set". `ctrl.size` is always a power of two ≥ 8. -/
  ctrl : ByteArray
  /-- Slot contents. Either empty (before the first `insert`) or of size
      `ctrl.size`, with unoccupied slots holding an arbitrary placeholder
      (the first element ever inserted, or — after an `erase` — a
      duplicate of a neighboring slot's element). -/
  data : Array α
  /-- Number of elements stored. -/
  size : Nat
  /-- Number of tombstones. `size + tombs` is the number of non-empty
      control bytes and drives the load factor, so probe sequences stay
      bounded no matter how many erasures happen between rehashes. -/
  tombs : Nat

namespace HashSet
variable {α : Type u} [Inhabited α] [BEq α] [Hashable α]

/-- Fold the high 32 bits of the hash into the low bits: slot indexing
    masks with `n - 1` and would otherwise ignore the high bits, where
    pointer-derived hashes carry most of their entropy. -/
@[always_inline, inline] private def scramble (h : UInt64) : UInt64 :=
  h ^^^ (h >>> 32)

/-- Control byte for an occupied slot: tag bit + top 7 bits of the
    (scrambled) hash. Always non-zero, and independent of the low bits
    used for the slot index. -/
@[always_inline, inline] private def fragOf (h : UInt64) : UInt8 :=
  (h >>> 57).toUInt8 ||| 0x80

/-- 4096 zero bytes, built once per program run (a closed term). -/
private def zeroChunk : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 4096
  for _ in [0:4096] do
    b := b.push 0
  return b

/-- An all-zero (all-empty) control array of `n` bytes in a **single
    allocation**: reserve the full capacity, then `memcpy` the static
    zero chunk in. (The previous doubling `b ++ b` build allocated
    log₂ n intermediate arrays per table creation/resize; the
    `ByteArray.mk (Array.replicate n 0)` route is 11× slower still —
    see the `zeros` benchmark mode.) -/
private def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut k := 0
  while k < n do
    b := zeroChunk.copySlice 0 b k (min 4096 (n - k)) false
    k := k + 4096
  return b

/-- Create an empty set. The real capacity is the next power of two `≥ max capacity 8`. -/
def emptyWithCapacity (capacity : Nat := 8) : HashSet α :=
  ⟨zeroBytes (Nat.nextPowerOfTwo (max capacity 8)), #[], 0, 0⟩

instance : EmptyCollection (HashSet α) := ⟨emptyWithCapacity⟩
instance : Inhabited (HashSet α) := ⟨∅⟩

/-! ## `contains` -/

@[specialize] private unsafe def containsImpl (s : HashSet α) (a : α) : Bool :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let rec go (i : USize) : Bool :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then false
    else if c == frag then
      -- reference-equality fast path: skips the `BEq` call (and its
      -- refcount traffic on the stored element) for physical matches
      let x := s.data.uget i lcProof
      if ptrEq x a || x == a then true
      else go ((i + 1) &&& mask)
    else go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- `O(1)` expected; reads the element only on a 7-bit hash-fragment match. -/
@[inline] def contains (s : HashSet α) (a : α) : Bool :=
  unsafe containsImpl s a

@[specialize] private unsafe def getImpl (s : HashSet α) (a : α) : Option α :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let rec go (i : USize) : Option α :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then none
    else if c == frag then
      -- reference-equality fast path: skips the `BEq` call (and its
      -- refcount traffic on the stored element) for physical matches
      let x := s.data.uget i lcProof
      if ptrEq x a || x == a then some x
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- `O(1)` expected; checks if the element is contained and returns the stored element. -/
@[inline] def get? (s : HashSet α) (a : α) : Option α :=
  unsafe getImpl s a

@[specialize] private unsafe def getDImpl (s : HashSet α) (a : α) (fallback : α) : α :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let rec go (i : USize) : α :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then fallback
    else if c == frag then
      let x := s.data.uget i lcProof
      if ptrEq x a || x == a then x
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- Stored element equal to `a`, or `fallback` if absent. `O(1)` expected and
    allocation-free (unlike `get?`, which boxes the result in `some`).
    Declared via `@[implemented_by]` for the same reason as `HashMap.getD`. -/
@[implemented_by getDImpl]
def getD (_s : HashSet α) (_a : α) (fallback : α) : α :=
  fallback

@[specialize] private unsafe def getByImpl (s : HashSet α) (h : UInt64) (eq : α → Bool) : Option α :=
  let h := scramble h
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let rec go (i : USize) : Option α :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then none
    else if c == frag then
      let x := s.data.uget i lcProof
      if eq x then some x
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- Probe the set with a *precomputed* hash `h` and a predicate `eq` that must
    accept exactly the elements whose `Hashable` hash is `h` and that are
    `BEq`-equal to the (possibly not yet constructed) key. This allows callers
    to look up a composite element without allocating it first.
    `O(1)` expected. -/
@[inline] def getBy? (s : HashSet α) (h : UInt64) (eq : α → Bool) : Option α :=
  unsafe getByImpl s h eq

@[specialize] private unsafe def getByDImpl (s : HashSet α) (h : UInt64) (eq : α → Bool) (fallback : α) : α :=
  let h := scramble h
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let rec go (i : USize) : α :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then fallback
    else if c == frag then
      let x := s.data.uget i lcProof
      if eq x then x
      else go ((i + 1) &&& mask)
    else
      go ((i + 1) &&& mask)
  go (h.toUSize &&& mask)

/-- Same as getBy but returns the provided default value when no entry is found. -/
@[implemented_by getByDImpl]
def getByD (_s : HashSet α) (_h : UInt64) (_eq : α → Bool) (fallback : α) : α :=
  fallback

/-! ## `insert` -/

/-- Rehash all *live* entries (tombstones are dropped). If the live load
    is at least 1/2 the table quadruples — aggressive growth in the
    CPython-dict spirit: rehash passes drop ~4× versus doubling, total
    moves from ~2n to ~1.33n, and the transient old+new peak during the
    last grow is *smaller* because the second-to-last table is 4×
    smaller. Otherwise (the table is mostly tombstones) it is rebuilt at
    the same capacity, which just cleans the tombstones out. `filler`
    (any element) initializes the unoccupied slots of the new `data`
    array. Stored control bytes are reused — they are a pure function of
    the hash. -/
@[specialize] private unsafe def growImpl
    (ctrl : ByteArray) (data : Array α) (size : Nat) : HashSet α :=
  let newCap := if size * 2 ≥ ctrl.size then ctrl.size * 4 else ctrl.size
  let mask := newCap.toUSize - 1
  let rec findEmpty (nctrl : ByteArray) (j : USize) : USize :=
    if nctrl.uget j lcProof == 0 then j else findEmpty nctrl ((j + 1) &&& mask)
  let rec copy (i : Nat) (nctrl : ByteArray) (ndata : Array α) : HashSet α :=
    if i < ctrl.size then
      let c := ctrl.uget i.toUSize lcProof
      if c &&& 0x80 == 0 then  -- empty or tombstone
        copy (i + 1) nctrl ndata
      else
        let x := data.uget i.toUSize lcProof
        let j := findEmpty nctrl ((scramble (hash x)).toUSize &&& mask)
        copy (i + 1) (nctrl.uset j c lcProof) (ndata.uset j x lcProof)
    else
      ⟨nctrl, ndata, size, 0⟩
  copy 0 (zeroBytes newCap) (Array.replicate newCap default)

/-- Mutation step of `insertImpl`, applied to the read-only probe's
    outcome `r` (see `insertImpl` for the encoding): at most one
    copy-on-write per array even when the set is shared, and exactly one
    record (re)construction. A separate definition rather than the tail
    of `insertImpl` because the kernel hits its recursion limit when a
    `let rec` result is used as a `uset` index in the same definition
    body; as a plain parameter it typechecks instantly. -/
@[specialize] private unsafe def insertFinish
    (s : HashSet α) (a : α) (frag : UInt8) (szu cap r : USize) : HashSet α :=
  if r < cap then
    -- consume the empty slot `r`
    let ⟨ctrl, data, size, tombs⟩ := s
    -- first insert: materialize the slot array, with `a` as the filler
    let data := if data.isEmpty then Array.replicate ctrl.size default else data
    let ctrl := ctrl.uset r frag lcProof
    let data := data.uset r a lcProof
    -- rehash when load factor (incl. tombstones) > 3/4
    if szu * 4 > cap * 3 then
      growImpl ctrl data (size + 1)
    else
      ⟨ctrl, data, size + 1, tombs⟩
  else if r < cap + cap then
    s  -- already present: returned untouched, no allocation at all
  else
    -- reclaim a tombstone: occupancy is unchanged, so no growth check
    let i := r - cap - cap
    let ⟨ctrl, data, size, tombs⟩ := s
    let data := if data.isEmpty then Array.replicate ctrl.size default else data
    ⟨ctrl.uset i frag lcProof, data.uset i a lcProof, size + 1, tombs - 1⟩

@[specialize] private unsafe def insertImpl (s : HashSet α) (a : α) : HashSet α :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  -- occupancy-after-insert as USize: keeps the per-insert load-factor
  -- check in machine arithmetic (no boxed `Nat` multiplications)
  let szu := (s.size + s.tombs).toUSize + 1
  let cap := mask + 1
  -- Read-only probe: borrows `s`, allocates nothing, touches no
  -- refcounts. Outcome encoding (slot indices are < `cap`, so the
  -- ranges are disjoint): `i` = insert into empty slot `i`;
  -- `cap + i` = element found at `i`; `2*cap + i` = reclaim the
  -- tombstone at `i`. `free`/`hasFree` remember the first tombstone
  -- passed: if the probe proves `a` absent, the new element reclaims
  -- that slot instead of consuming an empty one.
  -- (An earlier version threaded the whole record through the loop to
  -- enable reset/reuse — optimal when the set is exclusively owned, but
  -- on a *shared* set it allocated a fresh record and inc/dec'd all
  -- fields on every probe step.)
  let rec probe (i free : USize) (hasFree : Bool) : USize :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then
      if hasFree then cap + cap + free else i
    else if c == frag then
      let x := s.data.uget i lcProof
      if ptrEq x a || x == a then cap + i
      else probe ((i + 1) &&& mask) free hasFree
    else if c == 1 then
      probe ((i + 1) &&& mask) (if hasFree then free else i) true
    else
      probe ((i + 1) &&& mask) free hasFree
  insertFinish s a frag szu cap (probe (h.toUSize &&& mask) 0 false)

/-- Insert `a`; if an equal element is already present the set is unchanged.
    `O(1)` amortized expected. In-place when the set is used linearly. -/
@[inline] def insert (s : HashSet α) (a : α) : HashSet α :=
  unsafe insertImpl s a

/-! ## `erase` -/

/-- Mutation step of `eraseImpl` (`r == cap` means "not found"); a
    separate definition for the same kernel-limit reason as
    `insertFinish`. Tombstones the slot, and replaces its stale element
    reference with the neighbor's (already array-owned) one so the
    erased element does not stay artificially alive. -/
@[specialize] private unsafe def eraseFinish
    (s : HashSet α) (mask cap r : USize) : HashSet α :=
  if r == cap then
    s  -- not present: returned untouched, no allocation at all
  else
    let ⟨ctrl, data, size, tombs⟩ := s
    let ctrl := ctrl.uset r 1 lcProof
    let data := data.uset r (data.uget ((r + 1) &&& mask) lcProof) lcProof
    ⟨ctrl, data, size - 1, tombs + 1⟩

/-- Tombstone deletion (the SwissTable strategy). The slot's control
    byte becomes `1`: `contains` needs no changes at all (a tombstone
    simply falls into the existing "no match, keep probing" branch), and
    erase itself does no neighbor hashing — unlike backward-shift
    deletion (Knuth's Algorithm R), which was tried first and measured
    ~75% slower on the erase phase because moving each neighbor back
    requires recomputing its hash, an extra random `Expr` dereference
    per considered slot. Tombstones count toward the load factor and are
    swept out by the rehash in `growImpl`, so probe lengths stay bounded
    under churn. -/
@[specialize] private unsafe def eraseImpl (s : HashSet α) (a : α) : HashSet α :=
  let h := scramble (hash a)
  let frag := fragOf h
  let mask := s.ctrl.usize - 1
  let cap := mask + 1
  -- read-only probe (see `insertImpl`): returns the match's slot index,
  -- or `cap` (an impossible slot) if `a` is absent
  let rec probe (i : USize) : USize :=
    let c := s.ctrl.uget i lcProof
    if c == 0 then
      cap
    else if c == frag then
      let x := s.data.uget i lcProof
      if ptrEq x a || x == a then i
      else probe ((i + 1) &&& mask)
    else
      probe ((i + 1) &&& mask)
  -- nothing was ever inserted: `data` may not be materialized yet
  if s.data.isEmpty then s
  else
    eraseFinish s mask cap (probe (h.toUSize &&& mask))

/-- Remove `a`; if no equal element is present the set is unchanged.
    `O(1)` expected. The table never shrinks (matching `Std.HashSet`),
    but heavily-erased tables are compacted by the tombstone sweep on
    the next rehash. -/
@[inline] def erase (s : HashSet α) (a : α) : HashSet α :=
  unsafe eraseImpl s a

/-! ## `union` -/

/-- Fold every occupied slot of `other` into `base` with `insertImpl`.
    `other` is only borrowed (read-only slot walk); `base` is updated in
    place when exclusively owned. Tombstones and empty slots of `other`
    are skipped by the control-byte tag check, with no element access. -/
@[specialize] private unsafe def unionImpl (base other : HashSet α) : HashSet α :=
  let n := other.ctrl.size
  let rec go (i : Nat) (acc : HashSet α) : HashSet α :=
    if i < n then
      let c := other.ctrl.uget i.toUSize lcProof
      if c &&& 0x80 == 0 then  -- empty or tombstone
        go (i + 1) acc
      else
        go (i + 1) (insertImpl acc (other.data.uget i.toUSize lcProof))
    else
      acc
  go 0 base

/-- Union of two sets. Like `Std.HashSet.union`, the smaller set is
    merged into the larger one, so the expected runtime is
    `O(min(s₁.size, s₂.size))` inserts (plus rehashing if the base must
    grow). For elements present in both sets the representative kept is
    the base's — i.e. the larger set's, with ties favoring `s₁`; with a
    lawful `BEq` the choice is unobservable (`Std` makes the same kind
    of trade). In-place when the larger set is used linearly. -/
@[inline] def union (s₁ s₂ : HashSet α) : HashSet α :=
  if s₁.size ≥ s₂.size then
    unsafe unionImpl s₁ s₂
  else
    unsafe unionImpl s₂ s₁

instance : Union (HashSet α) := ⟨union⟩

/-! ## Diagnostics -/

/-- `(capacity, average probe distance, max probe distance)` — the
    open-addressing analogue of chain statistics, for checking that the
    `Hashable` instance distributes well. Not performance-sensitive. -/
@[always_inline, inline] def probeStats (s : HashSet α) : Nat × Float × Nat := Id.run do
  let cap := s.data.size
  if cap == 0 || s.size == 0 then
    return (s.ctrl.size, 0.0, 0)
  let mut total := 0
  let mut maxd := 0
  for i in [0:cap] do
    if s.ctrl.get! i &&& 0x80 != 0 then  -- occupied (not empty, not tombstone)
      if let some x := s.data[i]? then
        let home := (scramble (hash x)).toNat % cap
        let d := (i + cap - home) % cap
        total := total + d
        maxd := max maxd d
  return (cap, total.toFloat / s.size.toFloat, maxd)

end HashSet

end Blaster.Data.HashSet
