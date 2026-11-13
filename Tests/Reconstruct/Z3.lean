import Blaster

set_option warningAsError true

namespace Tests.Reconstruct.Z3

open Lean Elab Command in
elab "#standard_axioms " n:ident : command => do
  let decl ← resolveGlobalConstNoOverload n
  let axioms ← liftCoreM (collectAxioms decl)
  let forbidden := axioms.filter fun a => ![``propext, ``Classical.choice, ``Quot.sound].contains a
  unless forbidden.isEmpty do throwError "unexpected axioms: {forbidden.toList}"

-- Actual TxPipe optimization, certificate replay, then Z3 reconstruction.
theorem square (x : Int) : 0 ≤ -(-x) * -(-x) := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms square

theorem local_let (x : Int) : 0 ≤ (x + 1) * (x + 1) := by
  let y := x + 1
  change 0 ≤ y * y
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms local_let

theorem hypothesis_transport (x y : Int) (h : -(-x) ≤ y) : x + 1 ≤ y + 1 := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms hypothesis_transport

theorem quantified_transport : ∀ (x y : Int), -(-x) ≤ y → x + 1 ≤ y + 1 := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms quantified_transport

theorem optimizer_only (x : Int) : -(-x) = x := by
  blaster (gen-proof: 1) (only-optimize: 1)
#standard_axioms optimizer_only

theorem string_assoc (s t u : String) : (s ++ t) ++ u = s ++ (t ++ u) := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms string_assoc

theorem nat_power (x : Nat) : x ^ 2 = x * x := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_power

theorem nat_div (x y : Nat) : x / (y + 1) ≤ x := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_div

-- Existential bodies retain Nat constructors after optimization. They must be
-- lowered before SMT translation, rather than emitted as undeclared functions.
theorem nat_successor : ∀ x : Nat, x ≠ 0 → ∃ y, x = Nat.succ y := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_successor

-- Several delayed assignments connect this goal to the normalized residual.
-- Both the optimizer certificates and the residual proof must be used.
theorem nat_mul_mono : ∀ (w x y z : Nat), w ≤ x → y ≤ z → w * y ≤ x * z := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_mul_mono

abbrev Natural := Nat
theorem nat_alias_mono (x y z : Natural) (h : x ≤ y) : x * z ≤ y * z := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_alias_mono

theorem nat_alias_zero (x y : Natural) (h : x * y = 0) : x = 0 ∨ y = 0 := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms nat_alias_zero

-- Function type aliases and concrete class dictionaries, as used by Set.
abbrev Predicate (α : Type) := α → Prop
class PredicateOps (α : Type) where
  union : Predicate α → Predicate α → Predicate α
  inter : Predicate α → Predicate α → Predicate α
instance (α : Type) : PredicateOps α where
  union a b := fun x => a x ∨ b x
  inter a b := fun x => a x ∧ b x

theorem predicate_distributivity : ∀ (α : Type) (a b c : Predicate α),
    PredicateOps.union a (PredicateOps.inter b c) =
      PredicateOps.inter (PredicateOps.union a b) (PredicateOps.union a c) := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms predicate_distributivity

def predicateSubset (a b : Predicate α) : Prop := ∀ x, a x → b x
theorem predicate_subset : ∀ (α : Type) (a b c : Predicate α),
    predicateSubset a (PredicateOps.inter b c) ↔ predicateSubset a b ∧ predicateSubset a c := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms predicate_subset

theorem predicate_equality_hypothesis : ∀ (α : Type) (a b : Predicate α),
    PredicateOps.inter a b = a → PredicateOps.union a b = b := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms predicate_equality_hypothesis

theorem poly_option (α : Type) (x : Option α) : x.isSome = true → x ≠ none := by
  blaster (gen-proof: 1) (timeout: 5)
#standard_axioms poly_option

-- Checked command path and option order must both enforce reconstruction.
#blaster (gen-proof: 1) (timeout: 5) [∀ x : Int, 0 ≤ x * x]
#blaster (gen-proof: 1) (reconstruct: 0) (timeout: 5) [∀ x : Int, 0 ≤ x * x]

-- A strict command must not silently succeed without producing a proof.
/-- error: blaster: strict reconstruction requires a valid result; got Undetermined -/
#guard_msgs (error, drop warning) in
set_option warningAsError false in
#blaster (gen-proof: 1) (only-optimize: 1) [∀ x : Int, 0 ≤ x * x]

-- False claims and an optimizer-only run that leaves a residual are rejected.
example : True := by
  fail_if_success
    have impossible : (1 : Int) = 0 := by blaster (gen-proof: 1) (timeout: 5)
  fail_if_success
    have unfinished (x : Int) : 0 ≤ x * x := by
      blaster (gen-proof: 1) (only-optimize: 1)
  fail_if_success
    have unequal_functions : (fun x : Bool => x) = (fun _ : Bool => false) := by
      blaster (gen-proof: 1) (timeout: 5)
  trivial

-- A cyclic SMT macro must become a failed replay, rather than an unbounded
-- interpreter/native recursion. It is not a certificate of any proposition.
open Lean Meta Elab Command Blaster.Reconstruct.SmtProof in
run_cmd liftTermElabM do
  let body := STerm.app "cycle" #[]
  let syms := ({} : Std.HashMap String SymInterp).insert "cycle" (SymInterp.macro #[] body)
  let table : SymTable := { syms }
  let rejected ← withOptions (fun o => o.setNat `maxRecDepth 64) do
    tryCatchRuntimeEx (do
      discard <| (interp (.app "cycle" #[])).run { table }
      pure false) fun ex => do
        return ((← ex.toMessageData.toString).splitOn "maximum recursion depth").length > 1
  unless rejected do throwError "cyclic SMT macro was not rejected at the recursion limit"

-- The audit must resolve private names inside namespaces. An unresolved name
-- would otherwise silently produce an empty axiom set in `collectAxioms`.
namespace AuditGuard
set_option warn.sorry false in
private theorem forbidden : True := @sorryAx True false
/-- error: unexpected axioms: [sorryAx] -/
#guard_msgs in
#standard_axioms forbidden
end AuditGuard

end Tests.Reconstruct.Z3
