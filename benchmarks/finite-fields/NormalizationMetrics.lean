/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import fixtures.«finite-fields».audit.Semantic
import fixtures.«finite-fields».audit.Circuits
import Tests.FF04.Corpus

/- FFM-20 measurement support. Original reflected definitions are imported, never
   copied. This helper is compiled once outside measured invocations. -/
namespace FFM20.Normalization

open Lean Elab Command
open Blaster.FiniteField

-- Reproduce the nominal Residue instances, not the older Fin representation.
-- Ring normalization requires nonzero moduli, not a field-law assumption.
instance historicalNeZero : NeZero 65537 := ⟨by decide⟩
instance smallNeZero : NeZero 7 := ⟨by decide⟩
instance compositeNeZero : NeZero 6 := ⟨by decide⟩
instance selectedNeZero : NeZero Test.FiniteFieldLargePrime.curve25519 := ⟨by decide⟩

theorem selectedPrime : Prime Test.FiniteFieldLargePrime.curve25519 :=
  Test.FiniteFieldLargePrime.curve25519_prime

-- Count the expression tree, including binder types and repeated occurrences.
-- Constants are single nodes: their declarations are deliberately NOT unfolded.
def proofExprNodes : Lean.Expr → Nat
  | .app f a => 1 + proofExprNodes f + proofExprNodes a
  | .lam _ t b _ => 1 + proofExprNodes t + proofExprNodes b
  | .forallE _ t b _ => 1 + proofExprNodes t + proofExprNodes b
  | .letE _ t v b _ => 1 + proofExprNodes t + proofExprNodes v + proofExprNodes b
  | .mdata _ e => 1 + proofExprNodes e
  | .proj _ _ e => 1 + proofExprNodes e
  | _ => 1

def auditedAxioms (declaration : Name) : CommandElabM (Array Name) := do
  let axioms ← Lean.collectAxioms declaration
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {declaration}"
  return axioms

def emit (declaration : Name) : CommandElabM Unit := do
  let info ← Lean.getConstInfo declaration
  let .thmInfo theoremInfo := info
    | throwError "expected theorem {declaration}"
  let axioms ← auditedAxioms declaration
  let metric := Json.mkObj [
    ("declaration", toJson declaration.toString),
    ("proof_expr_nodes", toJson (proofExprNodes theoremInfo.value)),
    ("proof_expr_nodes_definition", toJson "recursive Lean.Expr tree nodes; constants not unfolded"),
    ("axioms", toJson (axioms.map Name.toString)),
    ("reification_ms", Json.null),
    ("reification_reason", toJson "already-reflected imported corpus; no reifier is run"),
    ("normalization_ms", Json.null),
    ("reconstruction_ms", Json.null),
    ("kernel_ms", Json.null),
    ("stage_timing_reason", toJson "per-declaration timing unavailable here; parent records whole-file exclusive Lean profiler components separately"),
    ("compiled_artifact_bytes", Json.null),
    ("compiled_artifact_reason", toJson "parent measures emitted .olean bytes separately; not proof size")]
  liftIO <| IO.println ("FFM20_METRIC " ++ metric.compress)

run_cmd do
  for declaration in #[``historicalNeZero, ``smallNeZero, ``compositeNeZero,
      ``selectedNeZero, ``selectedPrime] do
    discard <| auditedAxioms declaration

end FFM20.Normalization
