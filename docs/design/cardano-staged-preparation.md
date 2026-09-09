# Staged preparation for fixed UPLC programs

Status: proposed architecture, not an implemented or measured speedup.

The [Cardano review](../reviews/cardano-preparation-2026-09-09.md) measures a
nonlinear preparation cliff: the production global validator takes 11 s in the
optimizer at fuel 1,400, 59 s at 1,600, and exceeds 240 s wall time at 1,800.
The conservative cache experiments do not remove that cliff. The next prototype
should avoid repeatedly interpreting the same static program and expanding
independent data choices through its machine state.

## First implementation slice

Compile a fixed decoded UPLC program into a graph of residual blocks. The static
part consists of the program's syntax, known builtin identity, and known
continuation shape. Dynamic values remain typed residual expressions. Give
static syntax and continuations stable node IDs, so execution does not repeatedly
copy, abstract and instantiate the complete syntax/environment representation.

Start with a bounded fragment: variables, lambdas, application, delay/force,
constants, error, and the builtins needed by one small Cardano script. An
unsupported instruction must fall back to the existing interpreter with the
exact remaining state and fuel. It must not be treated as an arbitrary value,
success, or error merely to finish preparation.

Use this first slice to answer a concrete question: how much preparation work
comes from repeatedly walking static CEK control, versus dynamic ledger data?
Do not build loop summaries, a new SMT theory, and a new symbolic executor at the
same time.

## Data representation and branching

Keep symbolic values as shared expressions. Constructing a record or list with
independent choices should not enumerate their Cartesian product. Split a path
when an operation needs to inspect a choice's discriminator. When paths join,
share the common continuation and represent differing values with conditional
fields where their types permit it.

Interpreter values and control structures require different treatment. The
measured global switch disabling all constructor hoisting improves some
preparation-only times but regresses other workloads and proof time. A new
representation must make the distinction explicit rather than assume that a
normalization flag implements a complete demand-driven evaluator.

Input serialization is another boundary to preserve. A deferred `toData` field
must denote exactly the same total Lean conversion as the eager version.
Proving which fields a builtin demands can avoid constructing unrelated fields;
replacing an unsupported conversion with unconstrained data would change the
property being proved.

## Semantic obligations

For the first prototype, preserve the bounded semantics exactly:

- Count original CEK transitions, not residual-block dispatches. A block may
  consume several original steps; reaching fuel zero must match `runSteps`,
  including its error behavior and already-halted cases.
- Preserve builtin semantics, language/semantics variant, evaluation order,
  errors and the distinction between halting and fuel exhaustion.
- Keep binders and closure environments explicit. State sharing must not reuse
  a value under sibling hypotheses or capture a variable from a closed scope.
- Relate each residual block to its original CEK fragment. Prefer kernel-checked
  local simulation lemmas that compose; do not infer equivalence from matching
  solver verdicts on a sample.
- Keep the existing `.exec` semantics available as the reference. A certificate
  may be reused only for the same program, imports/definitions, semantics
  variant and conversion definition. A fuel-specific residual must include
  that fuel in its cache identity.

The current prepared `.prop` is not supplied with such an equivalence theorem.
This proposal must not describe existing trusted Blaster verdicts as a new
kernel-checked proof of compilation correctness.

## Telemetry and gates

Record compile-once cost, per-property specialization cost, SMT translation,
solver time and peak memory separately. Useful structural counters include
static block count, block visits, residual value nodes, distinct symbolic
states, forks/joins, expanded constructor choices, and cache hits whose reuse
actually skips work. A high cache hit count alone was not predictive in the
measured substitution experiment.

Use the same source/bytecode pins and native build configuration as the existing
harness. The first performance gates are SellNFT, Governance and production
CIP-153 global at fuel 1,400/1,600/1,800. Include ParamFeed to expose fixed-cost
regressions. A later gate should reach enough fuel for a known accepting global
witness, not merely a larger number in a rejecting theorem.

For each proposed improvement, require:

1. The original positive properties and expected counterexamples, including a
   non-vacuity/acceptance control where the workload supplies one.
2. Small differential cases covering fuel boundaries, errors, constructor
   choices, dependent binders and closure capture.
3. At least three uncontended, paired timing runs on representative cases.
4. Full preparation-plus-proof comparisons. A faster preparation that leaves
   much more work in the proof phase is not the target improvement.

Only after this bounded implementation is validated should recurrence summaries
or cross-path memoization be attempted. A summary requires an explicit inductive
invariant/simulation proof; it cannot silently replace bounded semantics with
an unbounded approximation.

## Research basis

[GenSym (ICSE 2023)](https://continuation.passing.style/static/papers/icse23.pdf)
uses staged compilation and continuations for symbolic execution.
[GenWasym](https://arxiv.org/abs/2608.18327) specializes a definitional
WebAssembly interpreter and uses continuations and snapshots. These support
trying a staged representation, but their concolic/test-generation performance
results do not predict a speedup for universally quantified Cardano proofs.
