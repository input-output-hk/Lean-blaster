# FF-01: continuation base and interfaces

## Approved base and public references

Scope: approved job #3, FF-01, in `input-output-hk/lean-blaster` only.
No branch merge, upstream modification, deployment or push was performed.
The coordinator's publication target remains `agent/plan-lean-blaster-finite-fields`.

The supplied checkout had a clean synthetic root commit
`4535e72848e5b5829f465a597384b9d04d29c6f9` (`base`), with no configured remote.
The approved commit was initially absent from its object database. Fetching the
named public commits established exact tree identity:

- Approved #290: `12bb8a03bfd5fd5f96a31d359e7467d27b315201`.
- Both approved and supplied trees: `8074ab4587d1955a05cfe60dd58b535e52effe21`.
- `git diff --stat <approved> <supplied>`: empty.
- Approved parent: `3a99f4245d47ac960f2fa4b2fa1ea199447c616f`.
- Public `refs/pull/290/head` and
  `refs/heads/agent/plan-lean-blaster-finite-fields` both resolved to the approved
  commit. The supplied synthetic history was not rewritten to manufacture ancestry.

Frozen comparison inputs, observed on 2026-10-20:

| Label | Exact commit | Public source |
| --- | --- | --- |
| B: approved base | `12bb8a03bfd5fd5f96a31d359e7467d27b315201` | [#290](https://github.com/input-output-hk/lean-blaster/pull/290) |
| M: current main snapshot | `6c27ff9faa662512cafb54f618505bce2927fedb` | [commit](https://github.com/input-output-hk/lean-blaster/commit/6c27ff9faa662512cafb54f618505bce2927fedb) |
| I: indexed types | `7d052ca8e5b4f2bd1249189afb238ac8625dc6ac` | [commit](https://github.com/input-output-hk/lean-blaster/commit/7d052ca8e5b4f2bd1249189afb238ac8625dc6ac) |
| P: proof reconstruction | `1f29a78859bf0ba0e5e2a29ff6ca55be7aec8b5f` | [commit](https://github.com/input-output-hk/lean-blaster/commit/1f29a78859bf0ba0e5e2a29ff6ca55be7aec8b5f) |
| F: closed generic Fin | `01ae099a4e84e4e82f68394e9f57e180d0b85d84` | [#334](https://github.com/input-output-hk/lean-blaster/pull/334) |

Exact relationships from `git merge-base A B` and
`git rev-list --left-right --count A...B`:

| Pair | Merge base | Left-only / right-only commits |
| --- | --- | --- |
| B / M | `585c5fc1370196a03cfceec674f5a5ac2ed3c2f2` | 55 / 6 |
| B / I | `402f6d22c1fc42e6e26255faac77e15b2450e4ab` | 63 / 70 |
| B / P | `074940438077c44815674e60e6becc1b203452a7` | 60 / 94 |
| B / F | `c0ef8c0ddef1666aa3d3c1e382ba6a90d0882d3a` | 43 / 12 |
| M / I | `402f6d22c1fc42e6e26255faac77e15b2450e4ab` | 14 / 70 |
| M / P | `074940438077c44815674e60e6becc1b203452a7` | 11 / 94 |
| M / F | `585c5fc1370196a03cfceec674f5a5ac2ed3c2f2` | 6 / 24 |
| I / P | `402f6d22c1fc42e6e26255faac77e15b2450e4ab` | 70 / 97 |
| I / F | `402f6d22c1fc42e6e26255faac77e15b2450e4ab` | 70 / 32 |
| P / F | `074940438077c44815674e60e6becc1b203452a7` | 94 / 29 |

Thus no listed tip is an ancestor of another. Main's six commits after its
merge base with B change only two benchmark workflows and README; none supplies
a needed source interface. I and P use an older monolithic optimizer environment
and differ extensively from #290. Replacing those files would discard backend,
concurrency, model-retrieval, hash-consing and scoped-context work.

## Executable adaptations

### Closed modulus normalization

`Blaster/Optimize/Basic.lean` now exports:

```lean
getNatModulus? : Expr → TranslateEnvT (Option Nat)
```

Contract:

- Use an environment initialized by `Optimize.main`/`mainAux`, as required by
  `optimizeExpr`. No repeated optimizer initialization inside translation.
- Reject free variables, metavariables and loose bound variables before any
  normalization. A caller can explicitly instantiate assigned metavariables
  and submit the resulting closed term.
- Return raw Nat literals immediately; no cache allocation for literal inputs.
- Hash-cons nonliteral inputs and reuse the original canonical expression as
  the key. Require the inferred type to be recognized as `Nat`.
- Reuse `optimizeExpr`, not a new evaluator or `whnf` bound-normalization path.
- Recognize raw Nat literals and the exact
  `OfNat` projection over `instOfNatNat` used in F's final commit.
- Cache successful results only in
  `TranslateEnv.natModulusCache : HashMap PtrExpr Nat`. Preserve `some 0`,
  `some 1` and composite values. Unsupported nonnumeral results return `none`;
  optimizer errors propagate.
- This is numeric recognition, not primality validation, a field recognizer,
  a normalization certificate or a new proof-trust path.

The cache is per `TranslateEnv`, not global or shared between concurrent solver
sessions. Its top-level placement avoids extending the many positional
`OptimizeEnv` and `MemoizeEnv` patterns. The existing environment-update helpers
preserve it. The required positional-pattern adaptations are confined to
`Env/Types.lean`, `Env/Utils.lean` and `Rewriting/OptimizeMatch.lean`; no match or
recursive-function behavior is otherwise changed.

F's `translateFinType` supplied the optimizer/numeral-recognition pattern.
Neither I nor F contained this dedicated modulus-result cache or this exported
helper: this is a selective adaptation, not a claimed cherry-pick.

### Opaque recognition and translation

Already sufficient, unchanged:

- `Env/Utils.lean`: `isOpaqueFun (Name) (Array Expr)` and
  `isOpaqueFunExpr (Expr) (Array Expr)`.
- `Rewriting/Utils.lean`: `isNotFoldable (Expr) (Array Expr)`.
- `Smt/Translate/Application.lean`: `translateOpaqueFun (Expr) (Name)
  (Array Expr)` and `translateApp` already retain application arguments.

Concrete gap closed in `Smt/Translate/Quantifier.lean`:
`translateTypeAux` now passes the **full applied type** to `translateOpaqueType`.
The dispatcher examines `getAppFn` internally and preserves the bare-head
keys for all existing non-indexed sorts. Unknown heads still return `none` and
fall through to the original generic inductive translator. No field or Fin
recognizer was installed, and no operator was added to `opaqueFuns`.

Continuation constraints:

- A modulus-dependent operator must key declarations by its instantiated type
  or modulus, not only the operator name. `funInstCache`/`getOpaqueSmtEquivFun`
  cannot be used with a shared name-only key for different moduli.
- Declaration writers and predicate lookup must agree on canonical keys.
  I's `canonicalizeIndexedType` and `getPredicateDeclaration` illustrate that
  contract, but their `whnf` implementation was not imported.
- `Basic.lean` depends on the lower-level environment utilities. Calling the
  new helper from `Env/Utils.isOpaqueFun` would introduce an import cycle.
  No callback registry or FF-04 architecture prototype was added to hide that
  future integration decision.

## Existing generic Fin and replay continuations

### Generic Fin: reuse existing work, not a second field encoding

[I's translator](https://github.com/input-output-hk/lean-blaster/blob/7d052ca8e5b4f2bd1249189afb238ac8625dc6ac/Blaster/Smt/Translate/Application.lean)
has `translateFinOp?` and `translateFinArith?` for representative construction,
projection and modular add/mul/sub.
[F's translator](https://github.com/input-output-hk/lean-blaster/blob/01ae099a4e84e4e82f68394e9f57e180d0b85d84/Blaster/Smt/Translate/Quantifier.lean)
has `translateFinType (fin) (args)`, a cache-first bound lookup and exact
`0 ≤ x ∧ x < n` predicates over the existing Nat/Int representation, including
Fin fields. These satisfy generic bounded-domain prerequisites in their own
branches; neither establishes a nominal field or field division.

Neither generic Fin implementation is integrated here. The approved base's
`TestsSolver/SmtFinBaseline.lean` and `TestsCvc5/Cvc5FinBaseline.lean` deliberately
expect quantified Fin translation rejection. Those files and expectations stay
unchanged. Closed Fin computations still run through the optimizer.
`Fin.div` remains truncating Nat division, including division by zero; it must
never be silently translated as finite-field inversion.

A future generic-Fin cutover must reconcile those existing expectations through
the scoped existing-test policy; this job neither bypasses that gate nor claims
that #334 is already part of #290.

### Optimization proofs: concrete reference interfaces, not an inert stack

[#182](https://github.com/input-output-hk/lean-blaster/issues/182) concerns Lean
proof reconstruction for optimization and rewriting, not SMT certificates.
Its description of existing Nat replay refers to work outside this approved
base. Neither B nor the inspected main M contains the generic replay pipeline.

Reusable P interfaces in
[`Optimize/Env.lean`](https://github.com/input-output-hk/lean-blaster/blob/1f29a78859bf0ba0e5e2a29ff6ca55be7aec8b5f/Blaster/Optimize/Env.lean):

- `ProofStep.rewrite (proof : Expr) (symm : Bool := false)` and
  `ProofStep.exact (proof : Expr)`.
- `OptimizeEnv.proofStack`, `localProofStack`, `optBinders`.
- `pushProofStep`, `getProofStack`, `clearProofStack`, `pushOptBinder` and
  recursive-body stack save/restore helpers.
- `RecFunOptResult { optimizedBody, proofStack }`, consumed by recursive
  equivalence reconstruction rather than merely storing an unverified body.

P has actual rewrite producers in `OptimizeNat`, `OptimizeEq`, Boolean/Prop
rewriting and arithmetic reordering. Its
[`Command/Tactic.lean`](https://github.com/input-output-hk/lean-blaster/blob/1f29a78859bf0ba0e5e2a29ff6ca55be7aec8b5f/Blaster/Command/Tactic.lean)
provides `substProofStackFVars`, `applyProofStack`, `liftForallEq` and
`proveByProofStack`. This is the generic continuation to reuse rather than
inventing an FF-specific replay mechanism.

Trust limits are material: P skips failed rewrite attempts, uses positional
and name-based binder correspondence, and still calls `blasterAdmit` when replay
and reflexivity fail. Its diagnostic change is not elimination of admission.
It is not an axiom-free verified finite-field path.

B's `OptimizeStack` is an execution stack, not a proof stack.
`Hypotheses.BackProofStack` repairs proof arguments from hypotheses, not the
whole optimization trace. `Translate.main` already returns `(Result, Expr)` in
`TranslateEnvT`; `.run` returns final state, which the tactic currently discards.
No additional result wrapper is needed simply to make state available later.
B's `.Valid` branch still uses the existing `blasterProven`, including
optimizer-only success. That boundary is unchanged, not widened.

A real replay integration must connect producers, scoped binder/context reuse,
recursive cache consumers and tactic replay together. Adding unused proof-state
fields would not satisfy that prerequisite, so none were added. No new axiom,
`sorry`, `admit`, solver admission path, nominal field implementation or FF-04
prototype is part of this change.

## Environment and baseline observations

- Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`,
  `aarch64-unknown-linux-gnu`, Release.
- Lake: `5.0.0-src+797c613`.
- Z3: `5.1.0`, 64-bit, build
  `ca39e58c525c5b03c2484f118ade2b92fae31215`.
- cvc5: `1.4.1 [git 2b2e844 on branch HEAD]`;
  `cvc5 --show-config` reported `cocoa : yes`.
- A direct `cvc5 --lang smt2` QF_FF probe asserted `x*x = 2` in
  `(_ FiniteField 7)` and returned exit 0, `sat`, `((x #f4m7))`, no stderr.
  This demonstrates installed solver capability, not Blaster field translation.
- No toolchain, solver pin, build configuration, existing test, script or CI
  file was changed. No dependency or native solver replacement was needed.

Before source edits, on the tree-identical unmodified approved base:

| Command | Observed result |
| --- | --- |
| `lake build Blaster` | exit 0, 213 jobs, 219.97 s |
| `LEAN_NUM_THREADS=5 lake test` | exit 0, 160.05 s |
| `lake env lean TestsSolver/SmtFinBaseline.lean` | exit 0 |
| `lake env lean TestsCvc5/Cvc5FinBaseline.lean` | exit 0 |
| `make solvercheck` | exit 0; both solvers accepted |

The last three commands ran sequentially in 37.00 s. The Fin baseline reproduces
both the existing quantified-Fin rejection and the closed division semantics;
these are known limitations, not regressions introduced by FF-01. The new
`FiniteFieldInterfaces.lean` also failed before implementation with unknown
identifier `getNatModulus?`, demonstrating the absent API, not a baseline bug.

## Interface smoke and regression coverage

`TestsSolver/FiniteFieldInterfaces.lean` is a new regression file, picked up by
`make test-solver` without changing its command. It exercises zero, one,
composite and distinct moduli; reducible arithmetic; a 381-bit bound; repeated
normalization; the elaborated Nat projection; non-Nat/open/bound/metavariable
rejection; and successful resubmission after explicit metavariable instantiation.

A temporary `FF01Smoke.lean`, run with `lake env lean` and removed afterwards,
printed the same value on first/repeated normalization of `2^381 - 19`:

```text
4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788333
successful normalization entries: 1
symbolic bound: none
applied Fin remains outside opaque-sort dispatch: true
Fin.mul remains unfoldable: true
```

It also observed Valid for `(1 : Fin 7) / 2 = 0`, Expected Falsified for
`(1 : Fin 7) / 2 = 4`, and Valid for `∀ n : Nat, n + 1 > n` with each backend.
The build/check/regression/smoke sequence exited 0 in 221.44 s. This is interface
validation, not a before/after solver-performance claim.

The first adapted `make check_blaster` failed on an omitted positional
`TranslateEnv` pattern. All affected patterns were then migrated; the clean
rebuild passed. This was an implementation error, not a baseline failure.

## Worker execution

The installed `omp` was version `18.11.1`; no separate `omp-codex` executable
was found on PATH. The configured OMP worker was invoked for a read-only
interface/trust review with:

```text
omp --no-session --no-tools --no-extensions --no-skills --mode json -p <review prompt>
```

The event stream reported provider `openai-codex`, API
`openai-codex-responses`, model `gpt-5.6-luna`. No model or thinking argument
was supplied; the observed `defaultThinkingLevel` configuration was `high`.
That configuration is not a claim about an independently inspected request
payload. The worker completed the review; no startup failure or fallback was
reported. It did not edit source or execute the checks listed here.

## Validated continuation

Source and regression commit:
`6005fc56458f9cc61db4d4a16e3e32730b05fc3c`
(`Establish finite-field continuation interfaces`), parent
`4535e72848e5b5829f465a597384b9d04d29c6f9`.
This is a local patch on the verified tree-identical synthetic snapshot, not
a claim of Git ancestry from #290. The coordinator can apply this patch to the
approved target without importing any comparison branch.

Changed executable files:

- `Blaster/Optimize/Basic.lean`: closed modulus normalization/cache API.
- `Blaster/Optimize/Env/Types.lean`: per-translation cache and preserving updates.
- `Blaster/Optimize/Env/Utils.lean`: migrate the recursive-cache environment pattern.
- `Blaster/Optimize/Rewriting/OptimizeMatch.lean`: migrate two environment patterns.
- `Blaster/Smt/Translate/Quantifier.lean`: retain applied types at opaque dispatch.
- `TestsSolver/FiniteFieldInterfaces.lean`: new boundary regressions.

Final build and Lean test commands on that source tree:

| Command | Result |
| --- | --- |
| `make check_blaster` | exit 0, clean compilation check |
| `lake build Blaster` | exit 0, 213 jobs |
| `lake env lean TestsSolver/FiniteFieldInterfaces.lean` | exit 0 |
| `lake env lean FF01Smoke.lean` | exit 0; temporary file subsequently removed |
| `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests` | exit 0 |
| `LEAN_NUM_THREADS=5 lake test` | exit 0 |

The last two commands ran sequentially in 187.29 s, concurrently with the solver
gate sequence. The compilation script rebuilt the suite; the subsequent
`lake test` invocation replayed its successful cached results. No existing-test
failure was observed on either the unmodified base or this source tree in
these runs. All existing protected files remain untouched.

### Solver-gate timeout investigation

The first combined invocation
`make test-solver && make test-cvc5 && make solvercheck && lake exe z3check`
timed out after 3,600.11 s while still in `make test-solver`. It printed no
failed assertion or `FAILED:` marker. It did print the expected model-response
timeout/unavailable-evidence warnings from `ResponseLifecycle.lean`. The later
commands in that invocation did not run; their results cannot be inferred
from the chain.

Each of the 14 current `TestsSolver/*.lean` files was then run directly with
`LEAN_NUM_THREADS=5 lake env lean <file>`, at most four concurrently and a
90-second diagnostic deadline per file. All exited 0. `CrashLifecycle.lean`
took 21.49 s and `ResponseLifecycle.lean` 24.01 s; all other files finished
within 4.64 s. No protected file was instrumented or edited.

Separately executed gates:

| Command | Result |
| --- | --- |
| `make test-cvc5` | exit 0, 37.69 s |
| `make solvercheck` | exit 0; both installed backends accepted |
| `lake exe z3check` | exit 0; `recfun-finder available` |

The latter two ran sequentially in 6.74 s. Their successful independent runs
do not retroactively make the timed-out combined invocation successful.

The exact `make test-solver` command subsequently exited 0 on the changed tree
in 28.57 s, with all 14 files included and no source changes between attempts.
For the baseline comparison, an immutable `git archive` of
`12bb8a03bfd5fd5f96a31d359e7467d27b315201` was extracted under
`.lake/ff01-base`, built from scratch, and its unchanged `make test-solver`
exited 0 in 248.39 s including compilation. It ran the original 13 files.
The expected model-failure warnings appeared there too.

The first timeout was **not reproduced or causally classified**: neither a
baseline lifecycle defect nor an FF-01 regression was established. A passing
retry does not erase that observation. All requested commands have a successful
completed run on the final source tree, and the unmodified pinned source
comparison is recorded rather than attributing the timeout to the patch.

An attempted nested `git worktree add` timed out after 15 s and left a recursive
unregistered working-directory copy instead of a usable worktree. That copy was
removed; it was not used as baseline evidence. The archive method above used
only the exact approved commit. The temporary archive/extracted build were
removed after validation.

## Remaining limits and handoff

- No nominal finite-field type, field operator translation, primality check,
  field proof certificate, trusted-field axiom or FF-04 prototype is implemented.
- Generic Fin translation and generic optimization replay remain separate
  continuations at I/F and P respectively, with the policy and trust limitations
  described above. No verified-proof guarantee is inferred from numeric caching.
- Modulus normalization inherits the existing optimizer's supported expressions
  and resource behavior; symbolic inputs and nonnumeral results are unsupported.
- The one initial solver-gate timeout remains unexplained despite the successful
  per-file, exact-command and pinned-base comparisons.
- No protected-file exception or solver/toolchain prerequisite change was needed
  for this patch. Publication and completion signoff remain with the coordinator.
