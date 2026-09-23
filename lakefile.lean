import Lake
open Lake DSL

package «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

extern_lib blaster_process pkg := do
  let source ← inputTextFile (pkg.dir / "Blaster" / "Smt" / "process.c")
  let object ←
    if System.Platform.isWindows then
      buildLeanO (pkg.buildDir / "native" / "process.o") source #[] #["-O2"]
    else
      buildO (pkg.buildDir / "native" / "process.o") source
        #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc" getLeanTrace
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "blaster_process") #[object]

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
