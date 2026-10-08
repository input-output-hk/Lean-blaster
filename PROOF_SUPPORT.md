# Automatic induction, summaries, and proof export

Import `Blaster` to use the proof front end. Ordinary `blaster` invocations
keep their existing syntax. Two additional tactic options support recursive
programs:

```lean
blaster (induction: auto) (timeout: 10) (gen-cex: 0)
blaster (induction: auto) (summaries: [insert_sorted]) (timeout: 10)
```

`(summaries: [proof₁, …])` instantiates already proved facts at calls reached
from the goal. It also works without automatic induction. Facts are passed
as proof terms; their instances are proved, rather than inserted as axioms.

`(induction: auto)` first tries symbolic exploration when the goal contains a
supported machine run. Otherwise it tries functional induction on discovered
recursive definitions. Recursive calls stay uninterpreted at induction leaves;
constructor equations and the induction hypotheses justify the reductions.
[Tests/Proof/Lists.lean](Tests/Proof/Lists.lean) proves insertion sort in two
stages, using the insertion theorem as the sort theorem's summary.

## Machine exploration

The explorer extracts control transitions from recursive Lean definitions,
constructs Horn clauses, and searches for invariants with Z3 and Houdini.
The search result is a proposal: every verification condition is replayed
before an induction proof is assembled. A supplied model that fails replay
is rejected even when the original theorem is true.

[Tests/Proof/Machine.lean](Tests/Proof/Machine.lean) exercises a loop and a
recursive procedure with a growing continuation, without any Cardano or
Plutus dependencies. [Tests/Proof/Houdini.lean](Tests/Proof/Houdini.lean)
checks invariant search and solver failures directly.

The search is incomplete. Unsupported programs, unsuccessful invariant
search, and unproved verification conditions leave the tactic unsuccessful.
`blaster.explore.enabled` disables exploration; `blaster.explore.jobs`
controls its parallelism (default 4), and `blaster.explore.timeoutMs`
caps an invariant search (default 900000 ms). Functional induction is bounded
by `blaster.induction.maxGoals` (64) and `blaster.induction.maxDepth` (6).

## Facts owned by libraries

```lean
@[blaster_library] theorem insert_sorted (y : Int) (xs : List Int) :
    sorted xs = true → sorted (insert y xs) = true := by
  blaster (induction: auto) (timeout: 10)
```

Register a monomorphic theorem after proving it with Blaster. The attribute
checks its transitive axioms: it must use `Blaster.Tactic.blasterProven`, and
may otherwise depend only on `propext`, `Quot.sound`, and `Classical.choice`.
Definitions, polymorphic facts, proofs using `sorryAx`, and foreign axioms
are rejected. These restrictions apply to the library attribute; explicit
summaries may be other already proved theorems.

Only facts from imported modules are discovered automatically. Selection
uses the library definitions reached from the goal, avoiding indiscriminate
instantiation of every registered theorem. Within a fact module, name any
needed earlier facts explicitly as summaries.
[Tests/Proof/Library.lean](Tests/Proof/Library.lean) checks imported fact
selection and rejected registrations.

The generic selection machinery lives here. Facts about CEK evaluation,
builtins, or ledger encodings belong in the libraries that define those
operations, which may offer them as optional proof packages. This separation
is between modules and dependency layers; it does not require separate PRs.

## Export and trust boundary

Set `blaster.induction.export` to a directory to write successful automatic
induction proofs as standalone Lean files:

```sh
lake build Blaster:shared Tests.Proof.Machine
lake env lean --plugin=.lake/build/lib/libBlaster.so \
  -Dblaster.induction.export=.lake/exports Tests/Proof/Machine.lean
lake env lean .lake/exports/Tests.Machine.bounded_accepts.lean
```

The exporter preserves dependencies and emits large terms through `kernel%`,
which reads the kernel's syntax directly. Set
`blaster.induction.exportTextAbove=0` to exercise the text form. Exported files
can be compiled without an explicit Blaster plugin and with Lean's default
stack. [scripts/test_proof_exports.sh](scripts/test_proof_exports.sh) checks
both forms and six generated proofs.

Induction structure, summary application, and replay assembly are checked by
Lean's kernel. SMT leaves still depend on the existing
`Blaster.Tactic.blasterProven` axiom: this is not SMT proof reconstruction.
Exported proofs preserve that dependency and contain no `sorryAx`.

## Optimizer and translation changes

The front end requires reductions to respect opaque recursive calls and
branch-local facts. Rewrites record the contexts, generation, and variable
footprints they depend on; shared and alpha-template cache reuse checks that
those dependencies remain applicable. Memoized expression queries avoid
repeated scans during symbolic evaluation.

Constructor fields retain their choices instead of lifting every conditional
outward and multiplying whole values. Consumers can still reduce the relevant
field. Deferred match translation skips unreachable alternatives and registers
function-valued pattern variables when their first use precedes the scrutinee.
Other regression fixes bound quantified `Fin` values, preserve signed integer
division semantics, and guard boolean-equality normalization with a closed
`LawfulBEq` instance.

Tests distinguish semantic regressions from improved normalization. Issue33
expects `Falsified` for its unchanged universal claim because an empty verifier
list cannot meet a positive threshold; a kernel-checked concrete counterexample
records why. Kernel proofs also justify natural-subtraction cancellation and
the surjective `Int.toNat` quantified-image rewrite.

```sh
lake build Blaster
lake test
./scripts/test_proof_exports.sh
```
