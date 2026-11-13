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

The integration preserves the actual residual metavariables left by TxPipe certificate replay, excluding assigned and delayed-assigned wrappers. It closes each residual over its local context and lowers supported operators only after a definitional-equality check. Before invoking the Z3 driver, it exposes predicate aliases and heads definitionally, and replaces function equalities by pointwise equalities using an explicit extensionality proof, including inside hypotheses. The SMT proof is transported back to the original residual. Local lets and dependent hypotheses retain their context; elaborator implementation details are included only when the input depends on them. The combined proof is kernel-checked and its axioms are audited. Pending auxiliary kernel checks are awaited before acceptance. Checked failures never use the trusted-result axiom.

The optimizer-only `#testOptimize [..., proof]` gate remains independent of Z3. A small improvement closes already definitionally true String computations before replay unfolds them into noncomputable conditionals; this repairs the four String proof flags that failed on the original assembled review tree. The remaining `NormChoiceAppDite_10` optimizer proof gap is retained as a failing test rather than weakening its proof expectation.

The port adapts the Z3 driver to the TxPipe translation environment and initializes translation caches without assuming that the optimizer's new result equals the actual replay residual. The translator also contracts beta redexes exposed by proof replay. This is an integration branch, not a claim that every solver-valid example is reconstructible.

The latest benchmarks use Lean 4.24.0 and Z3 5.3.3; the earlier integration validation used Z3 5.4.0. The focused [Z3 suite](../Tests/Reconstruct/Z3.lean) covers arithmetic, local lets, hypothesis transport, leading binders, optimizer-only closure, String associativity, natural powers/division, scalar and predicate aliases, pointwise equality in goals and hypotheses, polymorphic Option values, checked commands, option ordering and rejection of false/incomplete proofs and cyclic macros. Each of its 16 named positive theorems is audited for standard axioms. A private negative fixture checks that forbidden axioms are detected even for namespace-relative names.

```sh
lake build Blaster Tests.Reconstruct.Z3 Blaster:shared
python3 scripts/check_reconstruction_suite.py --mode strict --out /tmp/blaster-tests
```

For replay diagnostics, `BLASTER_SMTPROOF_LOG=/path/to/log.jsonl` records accepted residual replays with their backend, step count, source location, elapsed/check time, and per-rule methods/timings. By default, quantifier-free nonlinear queries first try `z3arith2` with a two-second solver cap and a ten-second replay deadline checked between steps; the fallback is `z3,z3rec,z3+`. `BLASTER_SMTPROOF_BACKENDS` selects an explicit ordered portfolio with the requested budgets. The optional simplifier-preserving variant remains subject to the solver's proof support. `BLASTER_SMTPROOF_TIMEOUT` overrides the proof-backend timeout.

The latest [benchmark report](txpipe-z3-benchmarks.md) records 426 checked successes out of 466 trusted successes across 671 corpus goals, the 40 remaining losses, proof sizes and native source-suite outcomes. The full suite still has failures. Earlier integration validation is retained in [txpipe-z3-validation.md](txpipe-z3-validation.md). No PR is opened for this branch.

An opt-in [certificate-directed prototype](Z3CertificatePrototype.md) additionally tests a checked input-encoding contract and a standalone Farkas checker, including a comparison with the official Z3 Lean exporter. It has not established a performance improvement; the default reconstruction path remains unchanged.

## Inspecting a proof and measuring its size

Use a named theorem rather than `#blaster` when you want to inspect the resulting term:

```lean
theorem testProof (x y : Nat) (h : 0 < y) : x % y < y := by
  blaster (gen-proof: 1) (timeout: 10)

#print axioms testProof
```

`set_option pp.proofs true in #print testProof` displays the proof, often as a reference to generated auxiliary lemmas. The following counts the proof with helpers under the theorem's namespace expanded, without printing the potentially very large term:

```lean
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let root := ``testProof
  let info ← getConstInfo root
  let proof ← deltaExpand info.value! (fun n => root.isPrefixOf n)
  let (nodes, _) := Blaster.Reconstruct.SmtProof.dagStats proof
  logInfo m!"Proof: {nodes} distinct nodes"
```

This counts distinct Lean expression objects, preserving sharing, including generated helpers under the theorem's name. Helpers under other names and existing library lemmas remain references. It is not a measurement of printed text, allocated bytes or `.olean` file size. Counting only the outer `id (id testProof._proof_...)` would miss the certificate. For comparisons that expand **all reachable newly generated helpers**, use `scripts/benchmark_reconstruction.py`; its environment-based expansion is broader than the quick namespace filter above.

The latest checked `isInjective square` benchmark on `Nat` has a median of 12,031 expanded DAG nodes across three paired measurements with the full harness. An earlier 9,667-node count used the narrower namespace filter and is not directly comparable. Reconstruction is not optimized for a short human proof; the expanded display repeats shared subterms and can be much larger. `Tests/Smt/SmtNat/SmtNatMod.lean` contains a named `mod_lt` example that prints only its node count.
