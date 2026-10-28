import Lake
open Lake DSL

package «BlasterFFTests»

require Blaster from ".."

@[default_target]
lean_lib TestsFF where
  -- Include the root and recursively discover future cases without import-list edits.
  globs := #[.andSubmodules `TestsFF]
