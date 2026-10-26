import Blaster

-- Lean's frontend needs native initializers when importing compiled project modules.
unsafe def main (args : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  Blaster.Cli.run args
