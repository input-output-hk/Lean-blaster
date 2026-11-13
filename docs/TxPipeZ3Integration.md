# TxPipe + Z3 reconstruction integration branch

This experimental branch combines all 29 open TxPipe optimizer-reconstruction PR heads captured on 13 November 2026 with Seungheon Oh's Z3 proof reconstruction and the Z3-specific fixes from the rebased development branch.

**Base:** the assembled TxPipe feature stack at `2ee3bd3c`, descended from `feat/proof-reconstruction`. This branch is **not rebased onto current main**. Updating the stack to main remains a separate integration task; a trial merge of the full stack produced 35 conflicting files.

All 29 PR heads are ancestors of this branch. Their original history is preserved, including the two existing merge reconciliations in the assembled review branch. Exact PR heads and Z3 source commits are listed in [txpipe-z3-sources.json](txpipe-z3-sources.json). The Z3 code was extracted from `76ee5ddeca3c268185f2228768758ce4bc25890f`; Seungheon's original fork snapshot is `8bcd4f6abd54c3f0e137062f84db9e1a9048ed44`. The port retains its proof parser, symbol interpretation, Lean/SMT encoding bridge, recursive-function support and checked replay. It does not bring over his optimizer evidence engine. The Alethe/cvc5 backend is excluded.

To try checked reconstruction:

```lean
import Blaster

example (x : Int) : 0 ≤ -(-x) * -(-x) := by
  blaster (gen-proof: 1) (timeout: 10)

#blaster (gen-proof: 1) (timeout: 10)
  [∀ x : Int, 0 ≤ x * x]
```

- The default keeps TxPipe's existing optimizer replay and trusted SMT fallback.
- `(reconstruct: 1)` tries checked reconstruction, warning and falling back to the existing behavior on failure.
- `(reconstruct: 2)` requires a complete kernel-checked proof and rejects `sorryAx` and Blaster's trusted-result axiom.
- `(gen-proof: 1)` also requires that the proof depend only on `propext`, `Classical.choice` and `Quot.sound`. It enforces reconstruction level 2 regardless of option order.
- Both `blaster` and `#blaster` support these options. The command validates a proof; this port does not add the separate theorem-export API.
- `BLASTER_RECONSTRUCT=2` or `BLASTER_GEN_PROOF=1` supplies defaults for running existing benchmark sources without editing their tactic calls. Explicit options can override defaults, except that an enabled `gen-proof` always requires strict reconstruction.

The integration preserves the actual residual metavariables left by TxPipe certificate replay. It closes each residual over its local context, lowers supported operators only after a definitional-equality check, and invokes the Z3 driver. Local lets and dependent hypotheses retain their context; elaborator implementation details are included only when the input depends on them. The combined proof is kernel-checked and its axioms are audited. Pending auxiliary kernel checks are awaited before acceptance. Checked failures never use the trusted-result axiom.

The optimizer-only `#testOptimize [..., proof]` gate remains independent of Z3. A small improvement closes already definitionally true String computations before replay unfolds them into noncomputable conditionals; this repairs the four String proof flags that failed on the original assembled review tree. The remaining `NormChoiceAppDite_10` optimizer proof gap is retained as a failing test rather than weakening its proof expectation.

The port adapts the Z3 driver to the TxPipe translation environment and initializes translation caches without assuming that the optimizer's new result equals the actual replay residual. The translator also contracts beta redexes exposed by proof replay. This is an integration branch, not a claim that every solver-valid example is reconstructible.

Validation uses Lean 4.24.0 and Z3 5.4.0. The focused [Z3 suite](../Tests/Reconstruct/Z3.lean) covers arithmetic, local lets, hypothesis transport, leading binders, optimizer-only closure, String associativity, natural powers/division, polymorphic Option values, checked commands, option ordering and rejection of false/incomplete proofs. Each named positive theorem is audited for standard axioms.

```sh
lake build Blaster
BLASTER_SMTPROOF_BACKENDS=z3 BLASTER_SMTPROOF_SEEDS=1 lake build Tests.Reconstruct.Z3
lake test
```

For replay diagnostics, `BLASTER_SMTPROOF_LOG=/path/to/log.jsonl` records accepted residual replays with their backend, step count and source location. `BLASTER_SMTPROOF_BACKENDS` selects Z3 variants (default `z3,z3rec,z3+`); the optional simplifier-preserving variant remains subject to the solver's proof support. `BLASTER_SMTPROOF_TIMEOUT` overrides the proof-backend timeout.

The full-suite outcome is recorded in [txpipe-z3-validation.md](txpipe-z3-validation.md). No PR is opened for this branch.
