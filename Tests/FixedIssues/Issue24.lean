import Lean
import Blaster

open Lean Meta
namespace Tests.Issue24

-- Issue: translateApp: unexpected application Lean.Expr.app (Lean.Expr.const `Tests.Issue24.hash []) ...
-- Diagnosis : We need to consider not prop axiom during smt translation to properly
--             generate global variables.


structure DigestHash (α : Type u) where
  payload : α

def digestHash (x : String) : DigestHash String := ⟨x⟩

axiom digestToString : DigestHash String → String
axiom digest_hash_injectivity : ∀ (s1 s2 : String), digestHash s1 = digestHash s2 → s1 = s2

noncomputable def hash (s : String) := digestToString (digestHash s)
axiom hash_size : ∀ (s : String), (hash s).length = 128

-- check if we have a counterexample of length 128
#blaster (gen-cex: 0) (solve-result: 1) [∀ (s : String), (hash s).length < 128]

-- validate axiom
#blaster (only-optimize: 1) [∀ (s : String), (hash s).length = 128]

-- check if we are not wrongly applying axiom on another function
axiom hash2 : String → String
#blaster (gen-cex: 0) (solve-result: 1) [∀ (s : String), (hash2 s).length = 128]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (s : String) (f : String → String), (f s).length = 128]

-- check when axiom function is passed as argument
#blaster [∀ (xs : List String), !(List.isEmpty xs) → (List.head! (List.map hash xs)).length = 128 ]

end Tests.Issue24
