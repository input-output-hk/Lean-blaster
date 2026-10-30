import Blaster
import BlasterCliPlatform

open Blaster.Cli.Native

-- Lean's frontend needs native initializers when importing compiled project modules.
unsafe def main (args : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  consoleOpen
  try
    let stderr ← IO.getStderr
    let report : IO.FS.Stream := { stderr with
      write := reportWrite
      putStr := fun text => reportWrite text.toUTF8
      flush := pure ()
      isTty := reportTty }
    Blaster.Cli.run args {
      output := some report
      signal := interruptSignal
      columns := do return (← terminalColumns).toNat
      clip := fun text width => clipDisplay text width.toUInt32
      forceKill }
  finally
    consoleClose
