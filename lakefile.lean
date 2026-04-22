import Lake
open Lake DSL

package «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

require «Pigment» from git "https://github.com/RSoulatIOHK/Pigment.git" @ "main"

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  root := `Z3Check

lean_exe blast_check where
  root := `BlastCheck
