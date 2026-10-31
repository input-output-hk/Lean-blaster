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

target cliNative pkg : System.FilePath := do
  let source ← inputTextFile (pkg.dir / "native" / "cli.c")
  buildO (pkg.buildDir / "native" / "cli.o") source
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc" getLeanTrace

lean_lib BlasterCliPlatform where
  moreLinkObjs := #[cliNative]

lean_exe «lean-blaster» where
  root := `BlasterCli
  -- Source elaboration interprets initializers, macros, tactics, and #eval.
  supportInterpreter := true
  -- Leave room for the installer to add the matching Lean toolchain's macOS runpath.
  moreLinkArgs := if System.Platform.isOSX then #["-Wl,-headerpad_max_install_names"] else #[]
