import Lean
import Blaster

open Lean Meta
namespace Tests.Issue24

-- Issue: translateApp: unexpected application Lean.Expr.app (Lean.Expr.const `Tests.Issue24.blake256 []) ...
-- Diagnosis : We need to consider not prop axiom during smt translation to properly
--             generate global variables.


axiom hash : String → String
axiom hash_collision_prop : ∀ (s1 s2 : String), hash s1 = hash s2 → s1 = s2
axiom hash_size : ∀ (s : String), (hash s).length = 256

-- check if we have a counterexample of length 256
-- Remove solver options once performance issue resolved
#blaster (timeout: 5) (solve-result: 2) [∀ (s : String), (hash s).length < 256]

-- validate axiom
#blaster (only-optimize: 1) [∀ (s : String), (hash s).length = 256]

-- check if we are not wrongly applying axiom on another function
axiom hash2 : String → String
-- Remove solver options once performance issue resolved
#blaster (timeout: 5) (solve-result: 2) [∀ (s : String), (hash2 s).length = 256]
#blaster (timeout: 5) (solve-result: 2) [∀ (s : String) (f : String → String), (f s).length = 256]

-- check when axiom function is passed as argument
#blaster (random-seed: 1)
       [ ∀ (xs : List String), !(List.isEmpty xs) → (List.head! (List.map hash xs)).length = 256 ]


end Tests.Issue24
