import Lean

namespace Blaster.Cli

/-- OS services are supplied by the executable; importing Blaster needs no native adapter. -/
structure Platform where
  output : Option IO.FS.Stream := none
  signal : BaseIO UInt32 := pure 0
  columns : BaseIO Nat := pure 0
  clip : String → Nat → BaseIO String := fun text width => pure (String.mk (text.toList.take width))
  forceKill : UInt32 → IO Unit := fun _ => pure ()

end Blaster.Cli
