import Lake
open Lake DSL

package «Blaster» where
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

lean_exe solvercheck where
  root := `SolverCheck

/-- Tests that require a cvc5 executable (and, for the concurrent modes, Z3 as
    well). Kept out of the `Tests` tree so that the default suite only needs Z3. -/
lean_lib «TestsCvc5» where
  moreLeanArgs := #["--threads=4"]
