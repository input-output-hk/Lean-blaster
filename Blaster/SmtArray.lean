/-! # SMTArray — a Nat-indexed array API friendly to SMT translation.

`Array.get` requires a `Fin a.size` index (a dynamically-sized bound the
translator cannot model). `SMTArray` exposes total `Nat`-indexed `get`/`set`
so user code never produces `Fin a.size`, and it translates to the SMT array
theory (`select`/`store`).

It is a *single-field structure* wrapping `Array` (not an `abbrev`/`def`):
Lean represents single-field structures identically to the field, so this is
zero runtime cost, but — unlike an `abbrev` — `SMTArray α` does NOT reduce to
`Array α` during translation. That distinction is essential: raw `Array α` is
translated as an opaque datatype (so concrete arrays keep structural equality),
while `SMTArray α` opts into the SMT array theory. -/

namespace Blaster

structure SMTArray (α : Type u) where
  ofArray ::
  toArray : Array α

/-- Total Nat-indexed read; out-of-bounds yields `default`. -/
def SMTArray.get [Inhabited α] (a : SMTArray α) (i : Nat) : α := a.toArray.getD i default

/-- Total Nat-indexed write; out-of-bounds is a no-op. -/
def SMTArray.set (a : SMTArray α) (i : Nat) (v : α) : SMTArray α := ⟨a.toArray.setIfInBounds i v⟩

/-- Number of elements; translated to the SMT `size` selector of the datatype-pair encoding. -/
def SMTArray.size (a : SMTArray α) : Nat := a.toArray.size

end Blaster
