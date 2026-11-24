import Lake
open Lake DSL System

private unsafe def gccArchive (name : String) : String :=
  match unsafeIO do
    let result ← IO.Process.output { cmd := "g++", args := #[s!"-print-file-name={name}"] }
    if result.exitCode != 0 then
      throw <| IO.userError s!"g++ could not locate {name}: {result.stderr}"
    let path := result.stdout.trim
    if path == name || !(← (FilePath.mk path).pathExists) then
      throw <| IO.userError s!"Install the static GCC C++ runtime archive {name} to link Z3 on Linux"
    pure path with
  | .ok path => path
  | .error e => panic! s!"{e}"

private unsafe def z3LinkArgsImpl : Array String :=
  let libPath := match unsafeBaseIO (IO.getEnv "Z3_LIB_PATH") with
    | some p => p | none => if System.Platform.isOSX then "/opt/homebrew/lib" else "/usr/local/lib"
  if System.Platform.isOSX || System.Platform.isWindows then
    #[s!"-L{libPath}", "-lz3"]
  else
    -- Lean's Linux runtime exports part of LLVM's unwinder. A shared libz3 built
    -- against libstdc++ can therefore abort on an internally caught exception.
    -- Keep Z3, libstdc++, and libgcc's unwinder together inside libz3shim.so.
    #[s!"{libPath}/libz3.a", gccArchive "libstdc++.a", gccArchive "libgcc_eh.a",
      "-Wl,--exclude-libs,libz3.a",
      "-Wl,--exclude-libs,libstdc++.a", "-Wl,--exclude-libs,libgcc_eh.a"]
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

/-- The shim archive is linked into a shared library by Lake. Keep PIC in the
    traced arguments so changing this flag rebuilds cached object files. -/
private def z3ShimOArgs : Array String :=
  if System.Platform.isWindows then #["-O2"] else #["-O2", "-fPIC"]

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

input_file «z3_shim_datatypes.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_datatypes.c"
  text := true

target «z3_shim_context.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_context.o"
  buildO o (← «z3_shim_context.c».fetch) (← cWeakArgs) z3ShimOArgs

target «z3_shim_solver.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_solver.o"
  buildO o (← «z3_shim_solver.c».fetch) (← cWeakArgs) z3ShimOArgs

target «z3_shim_sorts.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_sorts.o"
  buildO o (← «z3_shim_sorts.c».fetch) (← cWeakArgs) z3ShimOArgs

target «z3_shim_terms.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_terms.o"
  buildO o (← «z3_shim_terms.c».fetch) (← cWeakArgs) z3ShimOArgs

target «z3_shim_datatypes.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_datatypes.o"
  buildO o (← «z3_shim_datatypes.c».fetch) (← cWeakArgs) z3ShimOArgs

extern_lib «libz3shim» (pkg : NPackage _package.name) := do
  let oCtx ← «z3_shim_context.o».fetch
  let oSol ← «z3_shim_solver.o».fetch
  let oSorts ← «z3_shim_sorts.o».fetch
  let oTerms ← «z3_shim_terms.o».fetch
  let oDt ← «z3_shim_datatypes.o».fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "z3shim") #[oCtx, oSol, oSorts, oTerms, oDt]

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  root := `Z3Check
