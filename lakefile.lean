import Lake
open Lake DSL

package «Solver» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib «Solver» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  -- add executable configuration options here
  root := `Z3Check
