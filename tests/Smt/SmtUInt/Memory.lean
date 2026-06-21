import Blaster

structure MemoryCell where
  val: UInt32
deriving Repr, Inhabited

structure Memory where
  cells: Array MemoryCell := Array.empty
  prop_length: cells.size = 50000
deriving Repr

def load (m: Memory) (i: Fin 50000) : UInt32 :=
  m.cells[i.val]!.val

def store (m: Memory) (i: Fin 50000) (v: UInt32) : Memory :=
  { m with cells := m.cells.set! i.val { val := v },
           prop_length := by
             simp only [Array.set!, Array.size_setIfInBounds]; exact m.prop_length }
-- blaster on only store
#blaster [∃ (s: Nat), ∀ (m: Memory), m.cells.size = s+8]

#blaster [∀ (m: Memory) (i: Fin 50000) (v: UInt32), load (store m i v)

 i = v]


structure MemoryDummy where
  a : Nat
  b : Nat
  prop :  (a + b = 0) = true









#blaster [∀ (m: MemoryDummy), (m.a + m.b = 0) = true]
