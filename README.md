# Blaster - An SMT Backend for Lean4

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](https://github.com/leanprover/lean4)
[![Z3 Version](https://img.shields.io/badge/Z3-v4.15.2-green.svg)](https://github.com/Z3Prover/z3)
[![cvc5 Version](https://img.shields.io/badge/cvc5-v1.2.1-green.svg)](https://github.com/cvc5/cvc5)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](CONTRIBUTING.md)

Blaster provides an SMT backend for Lean4 proofs, supporting both the Z3 (default) and cvc5 solvers. Blaster works by first aggressively optimizing the Lean expression of a theorem, sometimes up to a `True` goal, before sending the remaining goal and context to an SMT solver.

## Table of Contents

- [Table of Contents](#table-of-contents)
- [Installation](#installation)
  - [Prerequisites](#prerequisites)
  - [Installing Lean4](#installing-lean4)
  - [Installing Z3](#installing-z3)
  - [Installing cvc5](#installing-cvc5)
- [How to use?](#how-to-use)
  - [Using lakefile.toml](#using-lakefiletoml)
  - [Using lakefile.lean](#using-lakefilelean)
  - [Solver options](#solver-options)
  - [Call to the solver](#call-to-the-solver)
    - [Command](#command)
    - [Tactic](#tactic)
- [Features](#features)
- [Examples](#examples)
  - [Fixed Issues](#fixed-issues)
  - [Optimize](#optimize)
  - [Validator examples](#validator-examples)
  - [State Machine](#state-machine)
- [Benchmarks](#benchmarks)
- [General description of Blaster](#general-description-of-blaster)
  - [First step: optimization and normalization](#first-step-optimization-and-normalization)
    - [Boolean Operations](#boolean-operations)
    - [Natural Number Arithmetic](#natural-number-arithmetic)
    - [Control Flow and Pattern Matching](#control-flow-and-pattern-matching)
    - [Function propagation](#function-propagation)
  - [Second-step: SMT Translation](#second-step-smt-translation)
  - [Final step: SMT Solver Interaction](#final-step-smt-solver-interaction)
- [Installing the Z3 Solver](#installing-the-z3-solver)
- [Contributing](#contributing)
  - [Ways to Contribute](#ways-to-contribute)


## Installation

### Prerequisites

Blaster requires Lean. Invoking a solver additionally requires the selected
backend executable; solver-independent translation and pure tests require neither:

- **Lean4** v4.24.0 (or compatible version);
- **Z3** v4.15.2 or later — required for the default/explicit Z3 path and
  every concurrent solver mode;
- **cvc5** v1.2.1 or later — required when selecting cvc5 or using `first` /
  `agree`.

### Installing Lean4

We strive to stay in sync with the latest **stable release** of Lean4.

**Currently supported version:** Lean4 v4.24.0

Please follow the official installation guidelines from the [Lean4 GitHub repository](https://github.com/leanprover/lean4).

### Installing Z3

We do our best to stay updated with the latest release of Z3. However, regressions can occur and often require extensive research and resolution, so Blaster might be slightly behind the latest version.

**Currently tested version:** Z3 v4.15.2

> **Note:** Blaster should work with later releases, though no guarantees are made.

The section on [Installing the Z3 Solver](#installing-the-z3-solver)
below explains how to get the right version of Z3 installed and check that
Lean is using that version.  If you need more help, please see the official
installation guidelines from the [Z3 GitHub repository](https://github.com/Z3Prover/z3).

### Installing cvc5

The cvc5 backend is optional for single-solver use: Blaster looks for `cvc5`
when `(solver: cvc5)`, `BLASTER_SOLVER=cvc5`, or either concurrent solver mode
is used. The test entry points preserve single-backend isolation:

- `make test-pure` runs parser, model-reconstruction, version-policy, launch-spec,
  setup-command, and configuration-precedence tests without either solver;
- `make test-z3` runs the default backend suite and requires only Z3;
- `make test-cvc5` runs the cvc5 backend suite in strict result-conformance mode
  and requires only cvc5;
- `make test-all-solvers` checks every test module plus same-process backend
  selection and requires both solvers;
- `make test-cvc5-floor` requires exactly cvc5 1.2.1 and runs the focused
  support-floor checks described below.

`make check_tests` runs the pure and Z3 tiers. Linux CI mirrors this topology in
separate Z3-only, cvc5-only, dual-solver, and cvc5-support-floor matrix legs.

**Full-suite tested version:** cvc5 v1.3.4. Version 1.2.1 is the hard support
floor enforced by Blaster's solver-version validation. A dedicated CI leg
downloads the official cvc5 1.2.1 static binary and requires
discovery/version validation, one satisfiable query, one unsatisfiable query,
and one counterexample/model query to pass.

Install a release binary from the [cvc5 GitHub repository](https://github.com/cvc5/cvc5/releases)
and make sure it is available in your `PATH` as `cvc5`. You can check the setup with:

```bash
lake exe solvercheck cvc5
```

Solver executables are validated before use: a candidate whose version banner
cannot be parsed, or reports a version below the supported minimum, is
rejected with a diagnostic listing every candidate tried (fail-closed; this
also applies to `z3`). On Windows, Blaster makes a best-effort fallback by
probing `wsl` with `z3` / `cvc5` as its first argument when no native solver
is found. Automated Linux CI does not exercise this fallback, so it is not a
tested Windows-support guarantee.

## How to use?

In order to use Blaster, your project needs to depend on `lean-blaster`.

### Using lakefile.toml
If you use `lakefile.toml` then, simply add a dependency to this repository:
```toml
[[require]]
name = "Blaster"
git = "https://github.com/input-output-hk/Lean-blaster"
rev = "main"
```

### Using lakefile.lean
If you use `lakefile.lean` then, simply add a dependency to this repository:
```lean4
require «Blaster» from git
  "https://github.com/input-output-hk/Lean-blaster" @ "main"
```

### Solver options
  - `timeout`: timeout in seconds for the backend solver. Precedence is the explicit
               option, then `BLASTER_TIMEOUT`, then no timeout (∞). Surrounding
               whitespace is ignored; an unset or blank environment value means ∞,
               and any other environment value must be a natural number.
  - `verbose:` activating debug info (default: 0)
  - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
  - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
  - `dump-smt-lib`: display the SMT-LIB query to stdout (default: 0). Concurrent
                    modes emit separate labeled runnable Z3 and cvc5 transcripts.
  - `random-seed`: seed for the random number generator (default: none)
  - `solver`: backend SMT solver (`z3` or `cvc5`). Precedence is the explicit option,
              then `BLASTER_SOLVER`, then `z3`. Surrounding whitespace in the
              environment value is ignored, but names are case-sensitive lowercase;
              any other value is rejected with the valid choices.
  - `solver-mode`: `single` (default), `first`, or `agree`; see
                   [Concurrent solver modes](#concurrent-solver-modes).
  - `gen-cex`: generate counterexample for falsified theorems (default: 1)
  - `solve-result`: specify the expected result from the #blaster command, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)


#### Concurrent solver modes

`solver-mode` controls execution without changing the existing `solver`
selection:

| Configuration | Behavior |
|---|---|
| no `solver-mode`, or `(solver-mode: single)` | Use `(solver: ...)`, then `BLASTER_SOLVER`, then Z3 |
| `(solver-mode: first)` | Run Z3 and cvc5 concurrently; first decisive verdict wins |
| `(solver-mode: agree)` | Run both and require compatible verdicts |

`first` treats only `Valid` and `Falsified` as decisive. `Undetermined`, a
Blaster-side deadline, a process failure, or a protocol failure cannot beat a
still-running solver. If a backend rejects a later declaration/assertion, that
session is retired and the healthy backend remains usable; a later incremental
check may recreate the retired session and replay the canonical query. When no
backend decides, ordinary `Undetermined` is returned only if both backends
returned `unknown`; infrastructure failures remain visible errors.

After a winning `Falsified` verdict, Blaster retrieves that solver's
counterexample while the loser is still alive, then kills and reaps the loser.
Model retrieval failure does not erase `Falsified`; it emits a precise
counterexample-unavailable diagnostic. The winning backend is printed only at
maintenance verbosity (`verbose: 2` or higher).

`agree` compares verdicts, not model text:

| Z3 | cvc5 | Result |
|---|---|---|
| `Valid` | `Valid` | `Valid` |
| `Falsified` | `Falsified` | `Falsified` |
| `Undetermined` | `Undetermined` | `Undetermined` |
| `Valid` | `Falsified` (or the reverse) | hard disagreement |
| decisive | `Undetermined` (or the reverse) | incomplete/coverage disagreement |
| any verdict | timeout, process failure, or protocol failure | infrastructure failure |

Matching falsified results do not require identical counterexamples. Evidence
is selected by quality: complete evidence from a completed model step, then
partial evidence from a `modelFailed` step, then no evidence. Z3 precedes cvc5
only as the tie-breaker between equal-quality candidates. A complete cvc5
counterexample therefore outranks a partial Z3 counterexample; the Z3 model
diagnostic is still retained.

Every hard/incomplete disagreement, infrastructure failure, or incomplete
model step writes `.blaster/agreement-*`. Each directory contains deterministic
`z3.smt2` and `cvc5.smt2` transcripts for the exact current check plus
`summary.txt` with solver version, invocation, verdict, status, elapsed time,
configured timeout, failed stage/command, stdout, stderr, and raw model
responses.

The `timeout`/`BLASTER_TIMEOUT` value is translated to each backend's native
option and enforced independently for each check. After that native deadline,
Blaster allows a fixed 1 s response-drain grace so a backend's terminal
`unknown` is not raced by process retirement. Expiry after the grace retires,
kills, and reaps that session and produces a structured `timedOut` status. In
`first` it cannot beat a healthy solver; in `agree` it is an infrastructure
failure; in `single` it is a visible solver failure. A solver's ordinary
`unknown` response remains `Undetermined` and is not inferred to be a timeout.

Concurrent modes always require supported Z3 and cvc5 binaries at startup.
There is no mode environment variable and no single-solver fallback. Combining
an explicit `solver:` with `first`/`agree` is rejected, as is combining
`only-smt-lib` with a concurrent mode. `only-optimize` starts no solver.
Random-seed options are translated independently for both backends.
`gen-cex: 0` skips model retrieval.

Examples:

```lean
#blaster (solver-mode: first) [∀ (x y : Int), x + y = y + x]
#blaster (solver-mode: agree) (solve-result: 1) [∀ (x : Int), x ≠ 3]

example : ∀ (x y : Int), x + y = y + x := by
  blaster (solver-mode: first)
```
### Call to the solver

#### Command

You can call the solver by invoking the `#blaster` command on a theorem name or on a propositional expression.
The syntax is as follows:
 - `#blaster (option1: n) (option2: n) [theoremName]`; or
 - `#blaster (option1: n) (option2: n) [theoremBody]`

For example,
```lean
theorem addCommute : ∀ (a b : Nat), a + b = b + a := by sorry
#blaster (only-optimize: 1) (solve-result: 0) [addCommute]
-- or
#blaster (only-optimize: 1) (solve-result: 0) [∀ (a b : Nat), a + b = b + a]
-- or
#blaster [∀ (a b : Nat), a + b = b + a]
```

#### Tactic

The solver can also be invoked via the `blaster` tactic. This tactic can be combined with other Lean4 tactics when trying to prove a theorem.
The syntax is as follows: `by blaster (option1: n) (option2: n)`.

For example,
```lean
theorem addCommute : ∀ (a b : Nat), a + b = b + a := by
  blaster (only-optimize: 1)
-- or
theorem length_set {as : List α} {i : Nat} {a : α} : (as.set i a).length = as.length := by
  induction as generalizing i <;> blaster
```

> [!NOTE]
> The tool does not perform proof reconstruction right now.
> - When the solver declares a goal as `Valid`, the tactic currently concludes the proof with an `admit`.
> - When the solver declares a goal as `Falsified`, the tactic fails and a counterexample is provided as witness.
> No counterexample is provided when a goal is reduced to `False` at the optimization phase.
> - When the solver returns `Undetermined` (i.e., the back-end solver was not able to prove/refute the goal),
> the tactic returns the current goal to be solved.

## Features

### Supported

#### Parametric Inductive Data Types
```lean
inductive Either (α : Type u) (β : Type v) where
 | Left : α -> Either α β
 | Right : β -> Either α β

def isLeft : Either a b -> Bool
 | Either.Left _  => true
 | Either.Right _ => false

def isRight : Either a b -> Bool
 | Either.Left _  => false
 | Either.Right _ => true

theorem isLeft_not_isRight_iff : ∀ (x : Either α β), ¬ (isRight x) = isLeft x := by blaster
```

#### Mutually Inductive Data Types
```lean
mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

mutual
def A.sizeA : A → Nat
  | .self a => a.sizeA + 1
  | .other b => b.sizeB + 1
  | .empty => 0

def B.sizeB : B → Nat
  | .self b => b.sizeB + 1
  | .other a => a.sizeA + 1
  | .empty => 0
end

theorem A_self_size (a : A) : (A.self a).sizeA = a.sizeA + 1 := by blaster
```

#### Recursive Functions
```lean
#blaster [ ∀ (x : Nat) (xs : List Nat), List.length xs + 1 = List.length (x :: xs) ]
```

#### Mutually Recursive Functions
```lean
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end

#blaster [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

#blaster [ ∀ (n : Nat), isEven (n+2) → isEven n ]
```

#### Polymorphism
```lean
inductive Either (α : Type u) (β : Type v) where
 | Left : α -> Either α β
 | Right : β -> Either α β

instance [BEq a] [BEq b] : BEq (Either a b) where
  beq | Either.Left a1, Either.Left a2 => a1 == a2
      | Either.Right b1, Either.Right b2 => b1 == b2
      | _, _ => false

#blaster
  [ (∀ (α : Type) (a b : α), [BEq α] → a == b → a = b) →
      (∀ (α : Type) (β : Type) (x y : Either α β), [BEq α] → [BEq β] → x == y → x = y)
  ]
```

#### Higher-Order Logic
##### Quantification over Functions
```lean
#blaster [ (∀ (β : Type) (x : Term (List β)) (f : Term (List β) → Nat), f x > 10) →
         (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 20)
       ]
```
##### Higher-Order Functions
```lean
#blaster [ ∀ (x : Nat) (xs : List Nat), !(List.isEmpty xs) →
         List.head! (List.map (Nat.add x) xs) ≥ x
       ]
```
#### Counterexample Generation for Recursive Data Types/Functions
```lean
def sizeOfTerm (t : Term α) : Nat :=
  match t with
  | .Ident _ => 1
  | .Seq xs => List.length xs
  | .App _ args => List.length args
  | .Annotated t' _ => 1 + sizeOfTerm t'

#blaster [ ∀ (α : Type) (x : Term α), sizeOfTerm x < 10 ]

❌ Falsified
Counterexample:
 - x: Test.SmtPredQualifier.Term.Annotated (Test.SmtPredQualifier.Term.Annotated
   (Test.SmtPredQualifier.Term.Annotated (... (Test.SmtPredQualifier.Term.Ident "!9!") []) ...) []) []
```
(exact model values vary with the backend solver and its version)

##### Counterexample display rendering

Counterexample values are read back from the solver through `(get-value …)`
and normalized into Lean-flavored display text; Blaster does not reconstruct
typed Lean values. For supported value shapes, the renderer smooths
backend-specific formatting differences: `let`-shared subterms are expanded,
cvc5's `as` constructor qualifiers are dropped, negative integers are
rendered `-n`, SMT-LIB string escapes are decoded back to Lean string
literals, and `List`/`Prod` values use Lean's `[x, y]` and `(x, y)` notations.

Verdicts, evidence, and infrastructure status are separate:

- **The solver produced a value with no Lean counterpart** — e.g.
  uninterpreted-sort elements or function values. Blaster displays the raw
  SMT term. This is a rendering fallback, not a missing model.
- **Model retrieval or rendering failed after `sat`** — the result remains
  `Falsified`. Blaster reports that counterexample evidence is unavailable and
  retains the exact model command and raw response in level-3 diagnostics
  (and agreement artifacts). A per-variable failure is displayed as
  `<counterexample unavailable>`.
- **The solver answered `unknown`** — no model command is sent; the verdict is
  `Undetermined`.
- **The solver process or protocol failed** — this remains an infrastructure
  failure and is never converted into an ordinary solver `unknown`.

`verbose: 3` captures the Lean goal, optimized expression, complete labeled
SMT transcript, solver name/version/invocation, `check-sat` response,
`topLevelVars`, exact model command, raw response, parsed S-expression,
Lean-facing rendering, and stderr stage. See `Tests/Smt/CounterexampleSpike.lean`.

#### State-Machine Formalization
```lean
instance counterStateMachine : StateMachine Request CounterState where
  init _ := { state := .Ready, timer := 0}
  next i s :=
    match s.state with
    | .Ready =>
         match i with
         | .Tr => { state := .Delay, timer := 0}
         | _ => s
    | .Delay =>
         if s.timer < 3
         then {s with timer := s.timer + 1}
         else {s with state := .Busy }
    | .Busy =>
         match i with
         | .Fa => {s with state := .Ready}
         | _ => s

  assumptions _ _ := True -- no assumptions

  invariants _ s :=
    (s.timer > 0 → s.timer < 3 → s.state = .Delay) ∧
    s.timer ≥ 0 ∧
    s.timer ≤ 3
```
##### Bounded Model Checking (BMC)
Command `#bmc` is provided to search for counterexamples up to a specified depth `k` on a given state machine instance.
When no provided, depth `k` defaults to `10`.
For example, a counterexample is detected at Depth `4`, when invariant `s.timer ≤ 3` is changed to `s.timer < 3`
```lean
#bmc (max-depth: 8) (verbose: 1) [counterStateMachine]

❌ Falsified
Counterexample detected at Depth 4:
 - «Test.Counter02.counterStateMachine.input@1»: Test.Counter02.Request.Tr
 - «Test.Counter02.counterStateMachine.input@2»: Test.Counter02.Request.Fa
 - «Test.Counter02.counterStateMachine.input@3»: Test.Counter02.Request.Fa
 - «Test.Counter02.counterStateMachine.input@4»: Test.Counter02.Request.Tr
BMC at Depth 0
BMC at Depth 1
BMC at Depth 2
BMC at Depth 3
BMC at Depth 4
```

##### K-Induction
Command `#kind` is provided to prove that a state machine's invariants are always satisfied.
It basically conducts an inductive proof in which the base case is handled via BMC, and the step case verifies that
whenever the invariants hold for an arbitrary state, they must also hold for all states reachable from it.
```lean
#kind (max-depth: 1) (verbose: 2) [counterStateMachine]
✅ Valid
KInd at Depth 0
KInd at Depth 1
```

### Currently Unsupported
#### Indexed Inductive Data Types
Indexed inductive data types are not yet supported because they lack a native representation at SMT-LIB level.
We expect to add support soon via a suitable encoding that faithfully preserves the Lean4 semantics.
For example,
```lean
inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)
```

#### Inductive Predicates
Inductive predicates are not yet supported, but our plan is to enable them by translating each predicate
into an equivalent boolean function at SMT-LIB level.

#### Implicit Induction Proof
Blaster does not currently attempt induction on its own.
Users can work around this by pairing `blaster` with the `induction` tactic in Lean4.
We plan to enhance this by introducing heuristics that enable automatic inductive reasoning.
For example,
```lean
inductive Path where
 | Here : Path
 | There : Path -> Path

def check_valid_path {α : Type}[BEq α](v : α)(p : Path)(ls : List α)
 : Bool
 := match p , ls with
    | .Here , .cons l _ls     => v == l
    | .There rs , .cons _ ls  => check_valid_path v rs ls
    | _ , _ => false

theorem validProof {α : Type}[BEq α](v : α)(p : Path)(ls : List α)
 : check_valid_path v p ls == true -> List.elem v ls := by
   induction ls generalizing p <;> blaster
```

#### Implicit Case Analysis
Currently, Blaster does not perform case analysis to split a goal into subgoals.
Users can address this by using the `blaster` tactic alongside Lean4’s `by_cases` tactic.
Our plan is to support automatic goal decomposition so that smaller SMT queries are
generated instead of one monolithic query. This will highlight the harder subgoals
and make them simpler for users to examine manually.


## Examples

Examples are provided in the `Tests` folder.

### Fixed Issues

The `Tests/FixedIssues` folder contains examples that were, at some point, not properly handled by our tool.

### Optimize

The `Tests/Optimize` folder contains examples of just the optimization step of the tool.

### Validator examples

The `Tests/Smt/Benchmarks/ValidatorsExamples` contains simplified examples of Cardano validators. It contains two examples `HelloWorld` and `Vesting`.

### State Machine

The `Tests/StateMachine` folder contains example on how to use the state machine formalization.

## Benchmarks

Blaster has been benchmarked against a variety of well-known benchmarks to evaluate its performance and correctness.
The evaluation can be found on this public repository: [Blaster-benchmarking](https://github.com/input-output-hk/Blaster-benchmarking)

<details>
<summary><b>Backend solver comparison (z3 vs cvc5)</b></summary>

Historical measurement recorded when the cvc5 backend was introduced, using
the then-current local builds: Z3 4.15.4 and cvc5 1.3.4. This table is retained
as a historical snapshot; this branch's CI does not regenerate it. The
measurement collected the 425 `#blaster` queries in the two suites below and
ran each in batch mode through both solvers with a 15s wall clock; *match*
means the solver's verdict agrees with the test's expected result
(`solve-result:`).

| Suite | Queries | z3 | cvc5 |
|---|---|---|---|
| Tests/FixedIssues | 71 | 69 | 59 |
| Tests/Smt | 354 | 351 | 313 |
| **Total** | **425** | **420 (98.8%)** | **372 (87.5%)** |

The measurement records agreement with the expected result for 420 of 425
queries under z3 and 372 of 425 under cvc5. The accompanying cvc5 result
records include `Undetermined` outcomes with `unknown`/timeout diagnostics;
neither the table nor those diagnostics establishes a solver-strategy cause.
Successful `(get-value …)` responses from either backend pass through the same
Lean-flavored text renderer (see
[Counterexample display rendering](#counterexample-display-rendering)).

##### Known cvc5 backend limitations

These describe current backend-facing behavior visible to Blaster, separate
from model-value normalization and display rendering:

- **Timeout behavior**: the `timeout:` option maps to cvc5's `tlimit-per`
  and z3's `timeout`. Blaster independently enforces that deadline around each
  backend's `check-sat`/`check-sat-assuming` response, with a fixed 1 s grace
  for the native timeout response to reach the pipe. Expiry after that grace is
  `timedOut`, not `Undetermined`; the child is retired, killed, and reaped.
  Suite-wide bounding via `BLASTER_TIMEOUT` is recommended for cvc5 runs. The
  strict cvc5-only CI leg uses 120s; the local target defaults to 30s.
- **`unknown` yields no model**: an ordinary solver `unknown` remains
  `Undetermined` and is never inferred to be a timeout. Blaster does not query
  a model after `unknown`.
- **Nested recursive datatypes** rely on cvc5's experimental
  `--dt-nested-rec` support (z3 accepts them natively).

Known display-rendering limitations, common to both solvers:

- goals without top-level quantified variables fall back to a raw
  `(get-model)` dump; an error on that dump leaves the verdict `Falsified`
  and reports unavailable counterexample evidence;
- variables bound only by nested SMT quantifiers are not entries in
  `topLevelVars`; their local witnesses cannot be queried with a top-level
  `(get-value ...)` command and are currently absent from rendered evidence;
- function-typed variables and abstracted `Type` parameters are modeled by
  SMT arrays/lambdas and uninterpreted-sort elements, which have no Lean
  counterpart and are displayed as raw solver terms
  (e.g. z3's `U!val!0`, cvc5's `@U_0`).

</details>

<details>
<summary><b>Lean Natural Number Game</b></summary>
  
- **Repository:** [NNG4](https://github.com/leanprover-community/NNG4)
- **Results:** 103/117
- **Notes:**
  - Failed on the examples that are not considered theorems by Lean
  - Failed on most of the Power examples
  - It includes Fermat's Last Theorem so 100% is unlikely to happen

</details>

<details>
<summary><b>Lean Set Theory Game</b></summary>

- **Repository:** [STG4](https://github.com/djvelleman/STG4)
- **Results:** 51/52
- **Notes:**
  - Failed on the `singleton` theorem from FamCombo

</details>

<details>
<summary><b>Verina.io</b></summary>

- **Repository:** [Add link here]
- **Results:** [Add results here]

</details>

<details>
<summary><b>"Lean-Book"</b></summary>

- **Repository:** [Add link here]
- **Results:** [Add results here]

</details>

## General description of Blaster

Blaster uses a three-step process to automatically reason about Lean theorems.

### First step: optimization and normalization

Before translation to SMT-LIB, blaster optimizes the Lean expression (see `Blaster/Optimize/Basic.lean`). This step simplifies the expression and prepares it for SMT translation by applying various transformations and rewriting rules, which can significantly improve the SMT solver's performance.
These rules are applied recursively to the expression tree and are designed to reduce the complexity of the SMT query.

The core optimization logic is orchestrated in `Blaster/Optimize/Basic.lean`, which applies a variety of strategies, including:

- **Beta Reduction**: Lambda applications are simplified by substituting arguments into the lambda body.
- **Function Unfolding**: Non-recursive and non-opaque functions are unfolded to their definitions.
- **Let-Expression Inlining**: Let-bindings are inlined to simplify the expression.

In addition to these general strategies, Lean-blaster applies a set of specific rewriting rules for different types of expressions, primarily located in the `Blaster/Optimize/Rewriting/` directory. We give a few examples in this section to illustrate the goal of those rules.

#### Boolean Operations

Boolean expressions are simplified using a set of rules. These rules include:

- **Identity**: `true && e` simplifies to `e`, and `false || e` simplifies to `e`.
- **Annihilation**: `false && e` simplifies to `false`, and `true || e` simplifies to `true`.
- **Constants**: `e && not e` simplifies to `false`, and `e || not e` simplifies to `true`.
- **Hypothesis-based simplification**: If an expression is known to be true or false from the current context, it is simplified accordingly.

#### Natural Number Arithmetic

Arithmetic operations on natural numbers are optimized using a variety of algebraic simplifications and constant folding rules, which can be found in `Blaster/Optimize/Rewriting/OptimizeNat.lean`. These include:

- **Constant Folding**: Expressions with constant values are evaluated (e.g., `2 + 3` is replaced with `5`).
- **Identity and Annihilation**:
  - `0 + n` simplifies to `n`.
  - `n - 0` simplifies to `n`.
  - `1 * n` simplifies to `n`.
  - `0 * n` simplifies to `0`.
  - And many more.
- **Algebraic Simplifications**: More complex rules are applied, such as:
  - `(m * n) / m`, where `n` and `m` are expressions, simplifies to `n` if `m` is known to be non-zero in the current context.
- **Normalization**: Arguments to commutative operators like `Nat.add` and `Nat.mul` are reordered to a canonical form, which helps in identifying further optimization opportunities.

These are just a few examples of the many optimization rules that Blaster applies to simplify expressions before they are sent to the SMT solver. This pre-processing step is crucial for the tool's performance and allows it to handle more complex verification tasks.

#### Control Flow and Pattern Matching

Blaster also includes a set of rules for simplifying control flow expressions like `if-then-else` (ITE), `dependent if-then-else` (DITE) and `match` expressions. These rules, found in `Blaster/Optimize/Rewriting/OptimizeITE.lean` and `Blaster/Optimize/Rewriting/OptimizeMatch.lean`, are designed to reduce the complexity of the expression by eliminating redundant branches and propagating constants.

- **ITE/DITE Simplification**: `if-then-else` expressions are simplified in several ways:
  - If the condition is a constant (`true` or `false`), the expression is replaced with the corresponding branch.
  - If the `then` and `else` branches are equivalent expressions, the whole `if-then-else` is replaced with that branch.
  - And many more.

- **Match Expression Optimization**: `match` expressions are optimized by:
  - **Constant Propagation**: If a discriminator (the value being matched on) is a known constant, the `match` expression is replaced with the corresponding branch.
  - **Unreachable Branch Elimination**: If a branch is determined to be unreachable based on the current context, it is eliminated.
  - **Normalization**: In some cases, `match` expressions are normalized into a series of `if-then-else` expressions to enable further simplification.

#### Function propagation

Function propagation is another key optimization strategy, detailed in `Blaster/Optimize/Rewriting/FunPropagation.lean`. This technique simplifies expressions by "pushing" function calls into their arguments. For example, a function applied to an `if-then-else` expression can be transformed into an `if-then-else` expression where the function is applied to both the `then` and `else` branches. This can be particularly effective when one of the branches can be further simplified after the function is applied using other optimization rules.

### Second-step: SMT Translation

Using the whole set of optimization rules, it may happen that a theorem can be reduced to `True`.  This concludes the proof and the theorem is considered as `Valid`. For some other cases, a theorem may also be reduced to `False` and will therefore be declared as `Falsified`. Most of the time, a proof might not be concluded at the optimization phase. In this case, the optimized Lean expression is translated into an SMT-LIB format and submitted to the backend solver.
The translation step is handled in `Blaster/Smt/Translate.lean`. This process involves several key steps:

1. **Expression Traversal**: The tool recursively traverses the Lean expression tree.
2. **Type and Function Translation**: Lean types and functions are mapped to their SMT-LIB equivalents.
3. **Quantifier Handling**: Universal and existential quantifiers are translated into SMT-LIB quantifiers.
4. **Application Translation**: Function applications are translated into SMT-LIB function calls.

### Final step: SMT Solver Interaction

Once an expression has been translated, Blaster interacts with an external SMT solver (Z3 by default, or cvc5 when selected through the `solver:` option) to verify the SMT-LIB formula. This is done by asserting  the negation of the formula to determine its satisfiability. The results are interpreted as follows:

- **unsat**: The original expression is valid.
- **sat**: The original expression is falsified, and a counterexample may be generated.
- **unknown**: The solver could not determine the validity of the expression.

---

## Installing the Z3 Solver

The Z3 backend's supported minimum is version 4.15.2. To install it, you need to

1. **Check out** the 4.15.2 tagged branch of the Z3 repo;
2. **Install** Z3 in a location that doesn't conflict with possible existing versions
   on your machine (e.g., in `/usr/bin/z3`)
3. **Ensure** Lean 4 is using the right version of Z3.

Below are instructions for accomplishing these objectives.  (They are aimed at
.deb-based Linux, but the same or similar steps should work on other platforms.)

### 1. Build and install Z3 v4.15.2 from source

Z3 releases are tagged on GitHub; the tag you want is `z3-4.15.2`.

**1.1 Install build dependencies**

```bash
sudo apt update
sudo apt install -y build-essential python3 git
```

**1.2 Clone the 4.15.2 tag**

Do **not** clone the `master` branch; it will give you a newer version (e.g., 4.15.4) that we do not yet fully support. Instead:

```bash
# Shallow clone just the 4.15.2 tag, into a directory named z3-4.15.2
git clone --branch z3-4.15.2 --depth 1 https://github.com/Z3Prover/z3.git z3-4.15.2
cd z3-4.15.2

# Sanity check: this should print something like "z3-4.15.2"
git describe --tags
```

**1.3 Configure build with a safe prefix**

By default, `mk_make.py` uses a prefix like `/usr`, which can clash with files installed by
package managers (e.g., `apt`).  The Z3 README documentation recommends using
`--prefix` to choose a custom install directory, typically `/usr/local`, as follows:

```bash
python3 scripts/mk_make.py --prefix=/usr/local
cd build
make -j"$(nproc)"
sudo make install
```

This installs

+  `z3` to `/usr/local/bin/z3`
+  libraries to `/usr/local/lib`
+  header files to `/usr/local/include`

### 2. Make sure **4.15.2** comes first in your `PATH`

Check which `z3` you’re actually picking up:

```bash
which z3
z3 --version
```

Ideally you will see
`/usr/local/bin/z3` and `Z3 version 4.15.2 - 64 bit`.

If `which z3` shows something else, e.g., `/usr/bin/z3`, then `/usr/local/bin` isn’t ahead
of `/usr/bin` in your `PATH`; fix this by either removing the version of `z3` that's
in `/usr/bin` (use `sudo apt remove z3` if you installed the old version of Z3 with
`apt`) or by adding the following to your shell config file (`~/.bashrc`, `~/.zshrc`, etc.):

```bash
export PATH=/usr/local/bin:$PATH
```

Then reload your shell and re-run `which z3`.

### 3. Make sure Lean 4 uses the right Z3

Lean just calls `z3` as an external process (via `IO.Process` or tactics that use Z3).

It doesn’t have its own embedded Z3. So:

**If the shell you run `lake` from sees `/usr/local/bin/z3` (4.15.2), then Lean will also use 4.15.2.**

Just to be sure, you can run the simple test we provide in this repository, as follows:

```bash
lake build z3check
lake exe z3check
```

If Z3 is installed correctly, you should see the following output:

```
Successfully ran z3:
Z3 version 4.15.2 - 64 bit
```

---

## Contributing

We welcome all contributions! Whether it's bug reports, feature requests, documentation improvements, or code contributions, your help is appreciated.

<!-- Please see our [Contributing Guidelines](CONTRIBUTING.md) for more information on how to get started. -->

### Ways to Contribute

- Report bugs and issues
- Suggest new features or improvements
- Improve documentation
- Submit pull requests

**Maintained by:**
- [Jean-Frédéric Etienne](https://github.com/etiennejf)
- [Romain Soulat](https://github.com/RSoulatIOHK)

**Questions?** Feel free to [open an issue](../../issues) or reach out to the maintainers.
