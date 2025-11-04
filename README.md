# Blaster - An SMT Backend for Lean4

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](https://github.com/leanprover/lean4)
[![Z3 Version](https://img.shields.io/badge/Z3-v4.15.2-green.svg)](https://github.com/Z3Prover/z3)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](CONTRIBUTING.md)

Blaster provides an SMT backend for Z3 proofs. Blaster works by first aggressively optimizing the Lean expression of a theorem, sometimes up to a `True` goal, before sending the remaining goal and context to an SMT solver.

## Table of Contents

- [Blaster - An SMT Backend for Z3](#blaster---an-smt-backend-for-z3)
  - [Table of Contents](#table-of-contents)
  - [Installation](#installation)
    - [Prerequisites](#prerequisites)
    - [Installing Lean4](#installing-lean4)
    - [Installing Z3](#installing-z3)
  - [How to use?] (#how-to-use)
  - [Features](#features)
  - [Benchmarks](#benchmarks)
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
TODO
### Using lakefile.lean
TODO

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

## Contributing

We welcome all contributions! Whether it's bug reports, feature requests, documentation improvements, or code contributions, your help is appreciated.

Please see our [Contributing Guidelines](CONTRIBUTING.md) for more information on how to get started.

### Ways to Contribute

- Report bugs and issues
- Suggest new features or improvements
- Improve documentation
- Submit pull requests


**Maintained by:**
- [Romain Soulat](https://github.com/RSoulatIOHK)
- [Jean-Frédéric Etienne](https://github.com/etiennejf)

**Questions?** Feel free to [open an issue](../../issues) or reach out to the maintainers.
