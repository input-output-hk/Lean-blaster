/-! # SMTArray — a Nat-indexed array API friendly to SMT translation.

`Array.get` requires a `Fin a.size` index (a dynamically-sized bound the
translator cannot model). `SMTArray` exposes total `Nat`-indexed `get`/`set`
so user code never produces `Fin a.size`. It is `Array` at runtime (zero cost)
and translates to the SMT array theory (`select`/`store`). -/

namespace Blaster

abbrev SMTArray (α : Type u) := Array α

/-- Total Nat-indexed read; out-of-bounds yields `default`. -/
def SMTArray.get [Inhabited α] (a : SMTArray α) (i : Nat) : α := a.getD i default

/-- Total Nat-indexed write; out-of-bounds is a no-op. -/
def SMTArray.set (a : SMTArray α) (i : Nat) (v : α) : SMTArray α := a.setIfInBounds i v

end Blaster
