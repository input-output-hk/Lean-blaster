import Lake
open Lake DSL

package «Tests» where
  -- add package configuration options here
  -- temporary options until whnf no more used for match reduction
  moreGlobalServerArgs := #["--threads=4", "-DmaxHeartbeats=500000"]
  moreLeanArgs := #["--threads=4", "-DmaxHeartbeats=500000"]
  require Solver from "../Solver"
  require PlutusCore from "../PlutusCore"
  require PlutusTx from "../PlutusTx"


lean_lib «Tests» where
  -- add library configuration options here

@[default_target]
lean_exe «solveProfiling» where
  root := `Profiling.SolveProfiling
  supportInterpreter := true
  moreLinkArgs := #["-Og", "-pg"]
