import Lake
open Lake DSL

package «Solver» where
  -- add package configuration options here
  precompileModules := true
  moreLeancArgs := #["-O3"]

lean_lib «Solver» where
  -- add library configuration options here
  precompileModules := true
  moreLeancArgs := #["-O3"]
