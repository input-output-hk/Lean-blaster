# Blaster - An SMT Backend for Lean4

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](https://github.com/leanprover/lean4)
[![Z3 Version](https://img.shields.io/badge/Z3-v4.15.2-green.svg)](https://github.com/Z3Prover/z3)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](CONTRIBUTING.md)

Blaster provides an SMT backend for Z3 proofs. Blaster works by first aggressively optimizing the Lean expression of a theorem, sometimes up to a `True` goal, before sending the remaining goal and context to an SMT solver.

## Table of Contents

- [Table of Contents](#table-of-contents)
- [Installation](#installation)
  - [Prerequisites](#prerequisites)
  - [Installing Lean4](#installing-lean4)
  - [Installing Z3](#installing-z3)
- [How to use?](#how-to-use)
  - [Using lakefile.toml](#using-lakefiletoml)
  - [Using lakefile.lean](#using-lakefilelean)
  - [Solver options](#solver-options)
  - [Call to the solver](#call-to-the-solver)
    - [Command](#command)
    - [Tactic](#tactic)
- [Features](#features)
- [Examples](#examples)
  - [Issues](#issues)
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
- [Contributing](#contributing)
  - [Ways to Contribute](#ways-to-contribute)

## Installation

### Prerequisites

Blaster is built with the philosophy that fewer dependencies mean better maintainability and more optimization opportunities. That said, Blaster requires:

- **Lean4** v4.24.0 (or compatible version)
- **Z3** v4.15.2 (or compatible version)

### Installing Lean4

We strive to stay in sync with the latest **stable release** of Lean4.

**Currently supported version:** Lean4 v4.24.0

Please follow the official installation guidelines from the [Lean4 GitHub repository](https://github.com/leanprover/lean4).

### Installing Z3

We do our best to stay updated with the latest release of Z3. However, regressions can occur and often require extensive research and resolution, so Blaster might be slightly behind the latest version.

**Currently tested version:** Z3 v4.15.2

> **Note:** Blaster should work with later releases, though no guarantees are made.

Please follow the official installation guidelines from the [Z3 GitHub repository](https://github.com/Z3Prover/z3).

## How to use?

In order to use Blaster, your project needs to depend on `lean-blaster`. 

### Using lakefile.toml
If you use `lakefile.toml` then, simply add a dependency to this repository:
```toml
[[require]]
name = "Solver"
git = "https://github.com/input-output-hk/Lean-blaster"
rev = "main"
```

### Using lakefile.lean
If you use `lakefile.lean` then, simply add a dependency to this repository:
```lean4
require «Solver» from git
  "https://github.com/input-output-hk/Lean-blaster" @ "main"
```

### Solver options
  - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
  - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
  - `verbose:` activating debug info (default: 0)
  - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
  - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
  - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
  - `random-seed`: seed for the random number generator (default: none)
  - `gen-cex`: generate counterexample for falsified theorems (default: 1)
  - `solve-result`: specify the expected result from the #solve command, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)

### Call to the solver

#### Command

You can call the solver through the `#solve` command. The syntax is:
`#solve (option1: n) (option2: n) [theoremName]`
or
`#solve (option1: n) (option2: n) [theoremBody]`

For example,
```lean
theorem addCommute : ∀ (a b : Nat), a + b = b + a := by sorry
#solve (only-optimize: 1) (solve-result: 0) [addCommute]
-- or
#solve (only-optimize: 1) (solve-result: 0) [∀ (a b : Nat), a + b = b + a]
```

#### Tactic

You can call the solver through the `blaster` tactic. The syntax is:
`by blaster (option1: n) (option2: n)`

For example,
```lean
theorem addCommute : ∀ (a b : Nat), a + b = b + a := by
  blaster (only-optimize: 1)
```

> [!NOTE]
> The tool does not perform proof reconstruction right now.
> If the solver returns `Valid`, the tactic returns an `admit`.
> If the solver returns `Falsified`, the tactif fails.
> If the solver returns `Undetermined`, the tactic returns the current goal to be solved.

## Features

> **Coming soon:** Detailed feature list

## Examples

Examples are provided in the `Tests` folder.

### Issues

The `Tests/Issues` folder contains examples that were, at some point, not properly handled by our tool. 

### Optimize

The `Tests/Optimize` folder contains examples of just the optimization step of the tool.

### Validator examples

The `Tests/Smt/Benchmarks/ValidatorsExamples` contains simplified examples of Cardano validators. It contains two examples `HelloWorld` and `Vesting`.

### State Machine

The `Tests/StateMachine` folder contains example on how to use the state machine formalization. 

## Benchmarks

Blaster has been benchmarked against a variety of well-known benchmarks to evaluate its performance and correctness.

<details>
<summary><b>Lean Natural Number Game</b></summary>

- **Repository:** [Add link here]
- **Results:** [Add results here]

</details>

<details>
<summary><b>Lean Set Theory Game</b></summary>

- **Repository:** [Add link here]
- **Results:** [Add results here]

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

Before translation to SMT-LIB, blaster optimizes the Lean expression in `Solver/Optimize/Basic.lean`. This step simplifies the expression and prepares it for SMT translation by applying various transformations and rewriting rules, which can significantly improve the SMT solver's performance.
These rules are applied recursively to the expression tree and are designed to reduce the complexity of the SMT query.

The core optimization logic is orchestrated in `Solver/Optimize/Basic.lean`, which applies a variety of strategies, including:

- **Beta Reduction**: Lambda applications are simplified by substituting arguments into the lambda body.
- **Function Unfolding**: Non-recursive and non-opaque functions are unfolded to their definitions.
- **Let-Expression Inlining**: Let-bindings are inlined to simplify the expression.

In addition to these general strategies, Lean-blaster applies a set of specific rewriting rules for different types of expressions, primarily located in the `Solver/Optimize/Rewriting/` directory. We give a few examples in this section to illustrate the goal of those rules.

#### Boolean Operations

Boolean expressions are simplified using a set of rules. These rules include:

- **Identity**: `true && e` simplifies to `e`, and `false || e` simplifies to `e`.
- **Annihilation**: `false && e` simplifies to `false`, and `true || e` simplifies to `true`.
- **Constants**: `e && not e` simplifies to `false`, and `e || not e` simplifies to `true`.
- **Hypothesis-based simplification**: If an expression is known to be true or false from the current context, it is simplified accordingly.

#### Natural Number Arithmetic

Arithmetic operations on natural numbers are optimized using a variety of algebraic simplifications and constant folding rules, which can be found in `Solver/Optimize/Rewriting/OptimizeNat.lean`. These include:

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

Blaster also includes a set of rules for simplifying control flow expressions like `if-then-else` (ITE), `dependent if-then-else` (DITE) and `match` expressions. These rules, found in `Solver/Optimize/Rewriting/OptimizeITE.lean`, `Solver/Optimize/Rewriting/OptimizeDITE.lean` and `Solver/Optimize/Rewriting/OptimizeMatch.lean`, are designed to reduce the complexity of the expression by eliminating redundant branches and propagating constants.

- **ITE/DITE Simplification**: `if-then-else` expressions are simplified in several ways:
  - If the condition is a constant (`true` or `false`), the expression is replaced with the corresponding branch.
  - If the `then` and `else` branches are equivalent expressions, the whole `if-then-else` is replaced with that branch.
  - And many more.

- **Match Expression Optimization**: `match` expressions are optimized by:
  - **Constant Propagation**: If a discriminator (the value being matched on) is a known constant, the `match` expression is replaced with the corresponding branch.
  - **Unreachable Branch Elimination**: If a branch is determined to be unreachable based on the current context, it is eliminated.
  - **Normalization**: In some cases, `match` expressions are normalized into a series of `if-then-else` expressions to enable further simplification.

#### Function propagation

Function propagation is another key optimization strategy, detailed in `Solver/Optimize/Rewriting/FunPropagation.lean`. This technique simplifies expressions by "pushing" function calls into their arguments. For example, a function applied to an `if-then-else` expression can be transformed into an `if-then-else` expression where the function is applied to both the `then` and `else` branches. This can be particularly effective when one of the branches can be further simplified after the function is applied using other optimization rules.

### Second-step: SMT Translation

Using the whole set of optimization rules, it happens that the theorem being proved will reduce to `True`. This concludes the proof, and the theorem is `Valid`. In some instances, it will happen that it is reduced to `False` and the theorem is therefore `Falsified`. Most of the time, the theorem expression will not have been reduced to either and the solver will then translate the remaining Lean expression into the SMT-LIB format.
This is handled in `Solver/Smt/Translate.lean`. This process involves several key steps:

1. **Expression Traversal**: The tool recursively traverses the Lean expression tree.
2. **Type and Function Translation**: Lean types and functions are mapped to their SMT-LIB equivalents.
3. **Quantifier Handling**: Universal and existential quantifiers are translated into SMT-LIB quantifiers.
4. **Application Translation**: Function applications are translated into SMT-LIB function calls.

### Final step: SMT Solver Interaction

After translating the expression, Blaster interacts with an external SMT solver, Z3, to verify the translated SMT-LIB formula. The tool asserts the negation of the expression and checks for satisfiability. The results are interpreted as follows:

- **unsat**: The original expression is valid.
- **sat**: The original expression is falsified, and a counterexample may be generated.
- **unknown**: The solver could not determine the validity of the expression.

## Contributing

We welcome all contributions! Whether it's bug reports, feature requests, documentation improvements, or code contributions, your help is appreciated.

Please see our [Contributing Guidelines](CONTRIBUTING.md) for more information on how to get started.

### Ways to Contribute

- Report bugs and issues
- Suggest new features or improvements
- Improve documentation
- Submit pull requests

**Maintained by:**
- [Jean-Frédéric Etienne](https://github.com/etiennejf)
- [Romain Soulat](https://github.com/RSoulatIOHK)

**Questions?** Feel free to [open an issue](../../issues) or reach out to the maintainers.
