# CVC5 backend solver — design

**Date:** 2026-07-06
**Branch:** `feat/cvc5`
**Status:** approved

## Goal

Add cvc5 as a selectable backend SMT solver alongside Z3. Selection is per
invocation via a `(solver: ...)` option on `#blaster`, the `blaster` tactic,
`#bmc`, and `#kind`. The whole test suite must pass with both solvers: every
test invocation that reaches the backend gets an inline sibling invocation
running cvc5.

Z3 remains the default. The exact command stream sent to Z3 must remain
bit-for-bit identical to today, so existing behavior cannot drift.

## Background: verified solver divergences

Probed against cvc5 1.3.4 (installed locally) with the exact command patterns
blaster emits:

| Divergence | Z3 | cvc5 |
|---|---|---|
| Spawn | `z3 -in -smt2` | `cvc5 --incremental --parsing-mode=lenient --dt-nested-rec` (stdin works bare; `--incremental` required for the multiple `check-sat-assuming` queries issued by BMC/K-Induction) |
| Version probe | `z3 -version` | `cvc5 --version` |
| Tuning options | `:smt.mbqi`, `:smt.pull-nested-quantifiers`, `:auto_config`, `:smt.macro_finder`, `:smt.case_split`, `:smt.qi.eager_threshold`, `:smt.delay_units`, `:smt.relevancy` | none of these — cvc5 answers `unsupported`, which trips the `print-success` check in `trySubmitCommand!`; quantifier strength comes from `:full-saturate-quant` instead |
| Timeout | `:timeout` (ms) | `:tlimit-per` (ms) |
| Random seed | `:smt.random-seed` | `:seed` |
| Model value query | `(eval t)` → bare value | `(get-value (t))` → `((t value))` wrapper |

Compatible as emitted today (verified): `(get-model)` output format
(`(` … `)\n`), `sat`/`unsat`/`unknown` lines, `success` echoes,
`declare-datatype(s)`, `define-fun(s)-rec`, quantifier annotations
(`:qid`, `:pattern`, `:named`), `to_int`, `^`, `check-sat-assuming`.

`(get-proof)` / `getProof` is dead code (defined, never called) and is out of
scope; it stays Z3-shaped.

## Components

### 1. Solver selection (`Blaster/Command/Options.lean`, `Blaster/Command/Syntax.lean`)

- `inductive SmtSolver where | z3 | cvc5` (deriving `Repr`, `DecidableEq`).
- `BlasterOptions.solver : SmtSolver := .z3`.
- New syntax in the shared `solveOption` category:
  `syntax "(solver:" ident ")" : solveOption`, parsed by a new
  `parseSolver` folded into `parseSolveOption`. Accepted identifiers: `z3`,
  `cvc5`; anything else → `throwUnsupportedSyntax` (elaboration error).
- Because `solveOption` is shared, `#blaster`, `blaster`, `#bmc` and `#kind`
  all pick the option up with no per-command work.

### 2. `SolverConfig` descriptor (new file `Blaster/Smt/SolverConfig.lean`)

One record per solver holding every divergence point:

```
structure SolverConfig where
  candidates     : Array String          -- e.g. #["cvc5", "wsl cvc5"]
  spawnArgs      : Array String          -- e.g. #["--incremental", "--parsing-mode=lenient", "--dt-nested-rec"]
  versionFlag    : String                -- "-version" / "--version"
  minVersion     : String                -- "4.15.2" / "1.3.4"
  defaultOptions : Array (String × String) -- startup set-option pairs
  timeoutOption  : String                -- ":timeout" / ":tlimit-per" (both ms)
  seedOption     : String                -- ":smt.random-seed" / ":seed"
  usesGetValue   : Bool                  -- model-value strategy
```

- `def SmtSolver.config : SmtSolver → SolverConfig` with `z3Config` and
  `cvc5Config` values.
- Z3's `defaultOptions` reproduces today's `setDefaultSmtOptions` sequence
  (print-success, produce-models, produce-proofs,
  smt.pull-nested-quantifiers, smt.mbqi, auto_config false, macro_finder).
  With the default `randomSeed = none` the Z3 command stream is bit-for-bit
  identical to today; when a seed is provided it is now emitted after
  macro_finder instead of before (set-option order is insensitive here).
- cvc5's `defaultOptions`: `:print-success true`, `:produce-models true`,
  plus quantifier tuning — starting point `:full-saturate-quant true`,
  finalized empirically against the suite. No `:produce-proofs` (dead
  feature, expensive in cvc5).
- The existing per-call helpers that are not part of the default sequence
  (`setCaseSplit`, `setQiEagerThreshold`, `setDelayUnits`, `setRelevancy`)
  are Z3-only tuning knobs and currently unused by the default flow; they
  keep their Z3 spelling and are not abstracted.

### 3. Solver interface changes (`Blaster/Smt/Env.lean`)

- `findZ3CmdAndVersion` → `findSolverCmd (cfg : SolverConfig)`: iterate
  `cfg.candidates`, probe with `cfg.versionFlag`, same error-report style
  (mentioning `cfg.minVersion`). As today, the probe checks the binary runs;
  it does not parse the version number.
- `createBlasterProcess` reads the active solver from
  `optEnv.options.solverOptions.solver` and spawns
  `cfg.candidates`-resolved command with `cfg.spawnArgs`. It moves from `IO`
  into `TranslateEnvT` (it needs the options), which its single caller
  `setBlasterProcess` already provides.
- `setDefaultSmtOptions` iterates `cfg.defaultOptions`, then applies seed
  (`cfg.seedOption`, when provided) and timeout (`cfg.timeoutOption`,
  seconds → ms as today).
- `evalTerm`:
  - Z3 (`usesGetValue = false`): unchanged, emits `(eval t)`.
  - cvc5: emits new `SmtCommand.getValue t` → `(get-value (t))`; reads the
    response with the existing paren-tally reader; unwraps the outer
    `((t value))` to return the bare value string. The single call site
    passes a simple variable symbol, so unwrapping = strip outer parens,
    drop the leading symbol token, strip one more paren layer,
    trim whitespace.
- New `SmtCommand.getValue (t : SmtTerm)` constructor in
  `Blaster/Smt/Syntax.lean` (+ `toString`) and `Blaster/Smt/EmitCommand.lean`.

### 4. Tests

- Every test invocation that actually reaches the backend gets an inline
  sibling with `(solver: cvc5)` appended to its option list, in the same
  file, directly after the original. Invocations with `only-optimize: 1` or
  `only-smt-lib: 1` never spawn a solver and are not duplicated.
- cvc5 siblings carry their own expectations where outcomes legitimately
  differ:
  - `tests/StateMachine/Counter04–06.lean` `#guard_msgs` blocks hard-code
    model values; the cvc5 siblings get baselines captured from actual cvc5
    1.3.4 output.
  - Invocations expecting `Undetermined` (`solve-result: 2`, 18 occurrences)
    are re-baselined per empirical cvc5 outcome (cvc5 may answer where Z3
    says `unknown`, and vice versa).
- Baseline stability rests on version pinning in CI, the same assumption the
  existing Z3 baselines make.

### 5. Tooling & CI

- New `Cvc5Check.lean` + `lean_exe cvc5check` in `lakefile.lean`, mirroring
  `Z3Check.lean` (runs `cvc5 --version`, prints result).
- `.github/workflows/ci-linux.yaml`: install pinned cvc5 1.3.4 (GitHub
  release binary) alongside Z3; the single `lake test` run covers both
  solvers because coverage is inline.
- `README.md`: document the `(solver: ...)` option and cvc5 installation.

## Known cvc5 limitations (verified on 1.3.4)

- **Model production for falsified quantified goals** requires cvc5's
  finite-model-finding machinery: the defaults now include
  `:finite-model-find true` + `:fmf-fun true` (suggested by JFE, validated
  2026-07-06), which upgrade falsifications over recursively-defined
  functions (e.g. `isEven`/`isOdd`) from `unknown` to `sat` + model while
  keeping valid goals `unsat`. (`:fmf-fun` assumes admissible/terminating
  definitions — guaranteed for Lean `def`s.)
- **Falsifications blocked by the qualifier bridge-axiom pattern.** For
  each inductive type Blaster emits `(declare-fun @isX ...)` (uninterpreted)
  plus a quantified bridge axiom `∀x. @isX_LRec(x) = @isX(x)` tying it to
  the real recursive definition. Z3 handles this because
  `:smt.macro_finder` eliminates `@isX` by inlining; cvc5 has no working
  macro elimination for this shape (verified: `--macros-quant` in all
  modes, both equality orientations, with/without `:pattern` — all
  `unknown`), so answering `sat` would require certifying the ∀-equality
  over an infinite datatype. Affected: falsified goals over recursive
  datatypes (`NatGroup`, `List.head!/map`, nested `Term α`). PROVEN FIX
  (follow-up, out of scope here): emit the qualifier directly as
  `(define-fun @isX ((@x T)) Bool (@isX_LRec @x))` — hand-editing a dumped
  query this way makes cvc5 answer `sat` instantly; mutual datatypes can
  put the wrappers in the same `define-funs-rec` block. Until then the
  affected cvc5 siblings carry `(timeout: N)` and terminate as
  `⚠️ Undetermined` (warning, suite stays green).

## Error handling

- cvc5 binary missing → same error style as Z3 today:
  `❌ Could not find a working cvc5 ≥ 1.3.4.` plus per-candidate attempt log.
- `(solver: foo)` with unknown name → elaboration error (unsupported syntax).
- Unexpected solver output paths (non-`success` echo, unexpected `check-sat`
  line) are already handled generically and stay unchanged.

## Testing the feature itself

- The duplicated suite is the primary regression net for both solvers.
- Z3 non-regression: Z3's config reproduces today's command stream (see the
  seed-ordering note above); the unchanged existing test invocations verify it.

## Out of scope

- Proof reconstruction / `get-proof` for cvc5.
- Version-number parsing for either solver (today's behavior: probe only).
- Exposing per-solver tuning knobs beyond the defaults.
- Making cvc5 the default solver.

## Future work (agreed 2026-07-06, phase 2 after this lands)

`(solver: all)` (run every solver, require agreement — differential testing of
the translation; `sat` vs `unsat` conflict = hard error) and `(solver: any)`
(parallel portfolio race, first definitive answer wins). Needs its own spec:
`SolverChoice` type, multi-process emit layer (`smtProc` → array,
handle-parameterized emit), race/join logic, stale-response bookkeeping for
the incremental `#bmc`/`#kind` loops, and stdin-backpressure mitigation
(default per-check timeouts, kill-and-replay of laggards from the stored
command list).
