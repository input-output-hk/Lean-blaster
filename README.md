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
- [Installing the Z3 Solver](#installing-the-z3-solver)
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

The section on [Installing the Z3 Solver](#installing-the-z3-solver)
below explains how to get the right version of Z3 installed and check that
Lean is using that version.  If you need more help, please see the official
installation guidelines from the [Z3 GitHub repository](https://github.com/Z3Prover/z3).

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

You can call the solver by invoking the `#solve` command on a theorem name or on a propositional expression.
The syntax is as follows:
 - `#solve (option1: n) (option2: n) [theoremName]`; or
 - `#solve (option1: n) (option2: n) [theoremBody]`

For example,
```lean
theorem addCommute : ∀ (a b : Nat), a + b = b + a := by sorry
#solve (only-optimize: 1) (solve-result: 0) [addCommute]
-- or
#solve (only-optimize: 1) (solve-result: 0) [∀ (a b : Nat), a + b = b + a]
-- or
#solve [∀ (a b : Nat), a + b = b + a]
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
#solve [ ∀ (x : Nat) (xs : List Nat), List.length xs + 1 = List.length (x :: xs) ]
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

#solve [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

#solve [ ∀ (n : Nat), isEven (n+2) → isEven n ]
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

#solve
  [ (∀ (α : Type) (a b : α), [BEq α] → a == b → a = b) →
      (∀ (α : Type) (β : Type) (x y : Either α β), [BEq α] → [BEq β] → x == y → x = y)
  ]
```

#### Higher-Order Logic
##### Quantification over Functions
```lean
#solve [ (∀ (β : Type) (x : Term (List β)) (f : Term (List β) → Nat), f x > 10) →
         (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 20)
       ]
```
##### Higher-Order Functions
```lean
#solve [ ∀ (x : Nat) (xs : List Nat), !(List.isEmpty xs) →
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

#solve [ ∀ (α : Type) (x : Term α), sizeOfTerm x < 10 ]

❌ Falsified
Counterexample:
 - x: (let ((a!1 (Test.SmtPredQualifier.Term.Annotated
             (Test.SmtPredQualifier.Term.Annotated
               (Test.SmtPredQualifier.Term.Annotated
                 (Test.SmtPredQualifier.Term.Ident "!a!")
                 (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))
               (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))
             (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))))
(let ((a!2 (Test.SmtPredQualifier.Term.Annotated
             (Test.SmtPredQualifier.Term.Annotated
               (Test.SmtPredQualifier.Term.Annotated
                 (Test.SmtPredQualifier.Term.Annotated
                   a!1
                   (as List.nil
                       (@List (@Test.SmtPredQualifier.Attribute @@Type))))
                 (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))
               (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))
             (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))))
  (Test.SmtPredQualifier.Term.Annotated
    (Test.SmtPredQualifier.Term.Annotated
      a!2
      (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))
    (as List.nil (@List (@Test.SmtPredQualifier.Attribute @@Type))))))
```
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
The `#solve` command and the `#blaster` tactic do not currently attempt induction on their own.
Users can work around this by pairing `#blaster` with the `induction` tactic in Lean4.
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
Currently, neither `#solve` nor `#blaster` performs case analysis to split a goal into subgoals.
Users can address this by using `#blaster` alongside Lean4’s `by_cases` tactic.
Our plan is to support automatic goal decomposition so that smaller SMT queries are
generated instead of one monolithic query. This will highlight the harder subgoals
and make them simpler for users to examine manually.


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
The evaluation can be found on this public repository: [Blaster-benchmarking](https://github.com/input-output-hk/Blaster-benchmarking)

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

Before translation to SMT-LIB, blaster optimizes the Lean expression (see `Solver/Optimize/Basic.lean`). This step simplifies the expression and prepares it for SMT translation by applying various transformations and rewriting rules, which can significantly improve the SMT solver's performance.
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

Blaster also includes a set of rules for simplifying control flow expressions like `if-then-else` (ITE), `dependent if-then-else` (DITE) and `match` expressions. These rules, found in `Solver/Optimize/Rewriting/OptimizeITE.lean` and `Solver/Optimize/Rewriting/OptimizeMatch.lean`, are designed to reduce the complexity of the expression by eliminating redundant branches and propagating constants.

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

Using the whole set of optimization rules, it may happen that a theorem can be reduced to `True`.  This concludes the proof and the theorem is considered as `Valid`. For some other cases, a theorem may also be reduced to `False` and will therefore be declared as `Falsified`. Most of the time, a proof might not be concluded at the optimization phase. In this case, the optimized Lean expression is translated into an SMT-LIB format and submitted to the backend solver.
The translation step is handled in `Solver/Smt/Translate.lean`. This process involves several key steps:

1. **Expression Traversal**: The tool recursively traverses the Lean expression tree.
2. **Type and Function Translation**: Lean types and functions are mapped to their SMT-LIB equivalents.
3. **Quantifier Handling**: Universal and existential quantifiers are translated into SMT-LIB quantifiers.
4. **Application Translation**: Function applications are translated into SMT-LIB function calls.

### Final step: SMT Solver Interaction

Once an expression has been translated, Blaster interacts with an external SMT solver (i.e.,  Z3) to verify the SMT-LIB formula. This is done by asserting  the negation of the formula to determine its satisfiability. The results are interpreted as follows:

- **unsat**: The original expression is valid.
- **sat**: The original expression is falsified, and a counterexample may be generated.
- **unknown**: The solver could not determine the validity of the expression.

---

## Installing the Z3 Solver

Blaster requires Z3 version 4.15.2.  To install that, you need to

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

Just to be sure, you can run a simple test in the `Solver` package of this
repository:

```bash
cd Solver
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
