import Lake
open Lake DSL System

private unsafe def z3LinkArgsImpl : Array String :=
  let libPath := match unsafeBaseIO (IO.getEnv "Z3_LIB_PATH") with
    | some p => p | none => "/opt/homebrew/lib"
  #[s!"-L{libPath}", "-lz3"]
@[implemented_by z3LinkArgsImpl]
private opaque z3LinkArgs : Array String := #["-lz3"]

package «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]
  moreLinkArgs := z3LinkArgs

def cWeakArgs : FetchM (Array String) := do
  let leanInc := (← getLeanIncludeDir).toString
  let mut args := #["-I", leanInc, "-I/opt/homebrew/include", "-I", "Blaster/Smt/FFI/c"]
  if let some inc ← IO.getEnv "Z3_INC_PATH" then args := args.push s!"-I{inc}"
  return args

input_file «z3_shim_context.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_context.c"
  text := true

input_file «z3_shim_solver.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_solver.c"
  text := true

input_file «z3_shim_sorts.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_sorts.c"
  text := true

input_file «z3_shim_terms.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_terms.c"
  text := true

target «z3_shim_context.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_context.o"
  buildO o (← «z3_shim_context.c».fetch) (← cWeakArgs) #["-O2"]

target «z3_shim_solver.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_solver.o"
  buildO o (← «z3_shim_solver.c».fetch) (← cWeakArgs) #["-O2"]

target «z3_shim_sorts.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_sorts.o"
  buildO o (← «z3_shim_sorts.c».fetch) (← cWeakArgs) #["-O2"]

target «z3_shim_terms.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_terms.o"
  buildO o (← «z3_shim_terms.c».fetch) (← cWeakArgs) #["-O2"]

extern_lib «libz3shim» (pkg : NPackage _package.name) := do
  let oCtx ← «z3_shim_context.o».fetch
  let oSol ← «z3_shim_solver.o».fetch
  let oSorts ← «z3_shim_sorts.o».fetch
  let oTerms ← «z3_shim_terms.o».fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "z3shim") #[oCtx, oSol, oSorts, oTerms]

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  root := `Z3Check
