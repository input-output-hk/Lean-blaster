import Lean

namespace Blaster.Optimize

/-- Scalar-only diagnostics: never retain expressions, contexts or metavariables. -/
structure NormalizationProfileEntry where
  calls : Nat := 0
  selfNs : Nat := 0
deriving Inhabited

/-- A separate instance is allocated for each profiled `Optimize.main` invocation.
The stack mirrors uncached expression-normalization frames, not CEK execution.
-/
structure NormalizationProfile where
  startedNs : Nat
  lastNs : Nat
  owners : List Lean.Name := []
  entries : Std.HashMap Lean.Name NormalizationProfileEntry := {}
  events : Std.HashMap Lean.Name Nat := {}
  misses : Nat := 0
  hits : Nat := 0
  bypasses : Nat := 0
  imbalances : Nat := 0
deriving Inhabited

end Blaster.Optimize
