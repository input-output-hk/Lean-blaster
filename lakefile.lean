import Lake
open Lake DSL

package «Blaster» where
  weakLeanArgs := if System.Platform.isWindows then #["-s65536"] else #[]
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  -- add executable configuration options here
  root := `Z3Check
