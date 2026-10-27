import Lean

namespace Blaster

/-- Monomorphic standard string-pattern replacement. Keeping this boundary explicit
    prevents a custom searcher instance from being assigned SMT string semantics. -/
def stringReplace (s pattern replacement : String) : String :=
  s.replace pattern replacement

end Blaster
