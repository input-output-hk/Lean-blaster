import Lean
import Blaster

open Lean Meta
namespace Tests.Issue25

-- Issue: translateType: unexpected sort type Lean.Expr.sort (Lean.Level.param `u_1)
-- Diagnosis : We need to normalize `sort (.mvar m)` to `sort l`
--             during optimization phase. It is expected that `m` must be assigned to `l`
--             in the Lean4 environment. Otherwise we error.
--             We also need to generate a distinct type universe at the smt level for each
--             unique `·sort ..` expression.

axiom hash : α → String
axiom hash_collision_prop1 : ∀ (α : Type) (s1 s2 : α), hash s1 = hash s2 → s1 = s2
axiom hash_collision_prop2 : ∀ (α : Type) (s1 s2 : α), s1 = s2 → hash s1 = hash s2
axiom hash_size : ∀ (α : Type) (s : α), (hash s).length = 256

-- check if we have a counterexample of length 256
#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Type) (s : α), (hash s).length < 256]

-- validate axiom
#blaster (only-optimize: 1) [∀ (α : Type) (s : α), (hash s).length = 256]
-- Need to handle instantiation of polymorphic function as we need to instantiate the axioms
-- #blaster [∀ (s : String), (hash s).length = 256]

-- check if we are not wrongly applying axiom on another function
axiom hash2 : α → String
#blaster (gen-cex: 0) (solve-result: 1) [∀ (s : String), (hash2 s).length = 256]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Type) (s : α), (hash2 s).length = 256]
#blaster (gen-cex: 0) (solve-result: 1) (random-seed: 3) [∀ (s : String) (f : String → String), (f s).length = 256]

-- check when axiom function is passed as argument
#blaster [ ∀ (α : Type) (xs : List α), !(List.isEmpty xs) → (List.head! (List.map hash xs)).length = 256 ]

end Tests.Issue25
