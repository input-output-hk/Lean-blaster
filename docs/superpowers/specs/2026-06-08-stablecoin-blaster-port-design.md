# Design: Porting the Lustre StableCoin Formalization to Lean 4 + Blaster

**Date:** 2026-06-08
**Status:** Proposed

## Background

`stablecoin-plutus/fm/stablecoin/` is a Kind2/Z3-verified Lustre formalization of a
reserve-backed stablecoin bank (the Djed-style protocol). Unlike the combinational
`Ratio` library (already ported), this is a **stateful transition system**:

- `Base.lus` — enums (`Order`, `Proceed`, `ErrorInfo`, `Stable`), structs (`InputMsg`,
  `OutputMsg`, `Fees`, `Parameters`), constants, and combinational helpers
  (`min`, `max`, `abs`, `computeFee`).
- `StableCoin.lus` — combinational economic functions (`equity`, `price_sc`, `price_rc`,
  `mintSC`, `mintRC`) and the stateful node `StableCoin_InitState` (transition over bank
  state `(reserve, n_sc, n_rc)` using `pre`/`->`), plus `StableCoin` (init = `(0,0,0)`).
- `Constraints.lus` — `ParameterConstraints`: magnitude bounds on the abstract parameters
  plus a temporal "params unchanged" assertion.
- `theorems/Theorem*.lus` — 31 files / ~50 `check`s. Some combinational (no `pre`,
  e.g. Theorems 1–2, 13–15, 32–38); some temporal/inductive (use `pre`/`->` observers,
  e.g. Theorem 3, Theorem 7 "no reserve draining").

We verify with Blaster's `StateMachine` class (`#bmc` for counterexamples, `#kind` for
k-induction) — the analogue of how Kind2 verified these (BMC + IND).

## Decisions (locked)

1. **Uniform StateMachine model.** Model StableCoin as Blaster `StateMachine` instance(s);
   verify ALL theorems (combinational and temporal) as invariants via `#bmc`/`#kind`,
   mirroring Kind2's BMC+IND method. (Rejected: a hybrid that proves combinational
   theorems as `#blaster` props over the one-step transition — risks reachability
   unsoundness for theorems that are combinational-looking but actually need an inductive
   prev-state, which Kind2's `unroll_max 2` hints at.)

2. **One `StateMachine` instance per Lustre theorem node.** Each node has its own extra
   inputs, observer state, assumptions, and checks, so each becomes its own instance
   sharing the common core transition.

3. **`div`/`mod` → `Int.ediv`/`Int.emod`** (Euclidean, matching Kind2/SMT-LIB), reusing
   the resolution validated in the Ratio port.

4. **Abstract `params`** modeled as an opaque/uninterpreted `Parameters` constant, with
   `ParameterConstraints` (magnitude bounds) carried in each instance's `assumptions`.
   "Params unchanged over time" falls out automatically (a constant cannot change). The
   exact mechanism (opaque `def` vs `axiom`) is decided empirically in the gate task.

## Architecture

### File layout (new `Stablecoin/` lib + `Tests/Stablecoin/`, mirroring `Ratio/`)

- `Stablecoin/Base.lean` — enums, structs, constants, `min`/`max`/`abs`/`computeFee`.
- `Stablecoin/StableCoin.lean` — `equity`, `price_sc`, `price_rc`, `mintSC`, `mintRC`,
  and the core transition `stepStableCoin : Input → CoreState → CoreState × OutputMsg`
  (the `StableCoin_InitState` body; the incoming `CoreState` is the `pre` state, so
  `p_reserve/p_sc/p_rc` are exactly the argument).
- `Stablecoin/Params.lean` — the abstract `params` + a `paramConstraints : … → Prop`
  predicate capturing `ParameterConstraints`'s magnitude bounds.
- `Tests/Stablecoin/ThmNN.lean` — one file per Lustre theorem file; each defines the
  per-theorem `StateMachine` instance(s) and the `#bmc`/`#kind` command(s).

### Core types

- `CoreState = { reserve : Int, n_sc : Int, n_rc : Int }` (deriving `BEq`, `Repr`).
- `Input = { i_msg : InputMsg, rate : Int }` (extended per-theorem with extra inputs).
- `stepStableCoin (i : Input) (s : CoreState) : CoreState × OutputMsg` mirrors
  `StableCoin_InitState`: `p_reserve = s.reserve`, etc.; compute `o_msg` via
  `mintSC`/`mintRC`; produce the next `CoreState`.

### Per-theorem StateMachine instance

For each theorem node:
- `β` (state) = `CoreState` **plus the node's `-> pre` observer fields** (e.g. Theorem 7's
  `reserve_0`, `constant_rate`, `coins_positive`). An observer `x = e0 -> pre f` becomes:
  `init` sets `x := e0`; `next` sets `x := f(prev observers, …)`.
- `α` (input) = `Input` plus the node's extra inputs (e.g. `rational_user : Bool`,
  `s_market : SecondaryMarket`).
- `init : α → β` from the node's initial values (Theorem 2: core `(0,0,0)`; Theorem 7:
  arbitrary-but-constrained `(i_reserve, i_sc, i_rc)` and observers seeded from inputs).
- `next : α → β → β` = `stepStableCoin` on the core fields + observer recurrences.
- `assumptions : α → β → Prop` = `paramConstraints` + the node's `assert`s.
- `invariants : α → β → Prop` = **the conjunction of ALL `check`s in the node — the main
  property AND every lemma check.** HARD RULE (see below).
- Verify with `#kind (max-depth: N) [inst]` (and `#bmc` for cex hunting), where `N` comes
  from the Lustre `unroll_max` comment in the file header.

## Hard rules

1. **`invariants` = conjunction of every `check` in the node**, not just the labeled main
   theorem. The lemma checks (Theorem 7 has ~13) exist precisely because the main property
   is not inductive alone — k-induction needs them as mutual strengthening. Dropping them
   breaks the induction. Never include only the headline check.

2. **Encode the source exactly; never strengthen to force a proof.** Because Blaster's
   `#kind` is *plain* k-induction with **no invariant generation** (verified: `KInduction.lean`
   has no IC3/PDR/invgen), some temporal theorems that relied on Kind2's auto-generated
   invariants (Theorem 7's header: "Proof by Induction + invariant generation", 600s) will
   **not discharge** on the hand lemmas alone. The deliverable is **faithful encodings of
   all theorems; prove what discharges; report `⚠️ Undetermined` / "couldn't establish
   induction up to depth N" faithfully** — exactly like the Ratio port's timeout handling.
   The absolute prohibition (analogue of "don't alter the math", but harder to detect):
   never add an assumption the source lacks, weaken an invariant, or drop a lemma to make
   `#kind` go green. A spuriously strengthened assumption makes `#kind` pass silently.

3. **Faithfulness over green.** A passing `#bmc`/`#kind` on a mis-encoded machine is a
   silent failure. Each theorem's `assumptions`/`invariants`/observer recurrences are
   reviewed against the Lustre node line-by-line.

## Risks

1. **Plain k-induction may not close the hard temporal theorems** (Risk-driving; see Hard
   Rule 2). Acceptable, documented outcome: `⚠️ Undetermined`. Not a failure to mask.
2. **Nonlinear arithmetic across k steps.** The economic invariants multiply
   `n_sc * rate * r_min`, `reserve div n_sc`, etc., across unrolled steps — far heavier
   than Ratio's bounded cross-multiplication. Expect `(timeout: N)` tuning and some
   undetermined results.
3. **`params` encoding mechanism** (opaque `def` vs `axiom`) is unverified on paper —
   resolved empirically in the gate task.
4. **StateMachine class on rich struct state** (`CoreState` + observers, enum-bearing
   `OutputMsg`) — validate the class handles it in the gate task (the `Counter` examples
   use `Nat` state).

## Execution order

1. **Gate task — a genuinely inductive theorem end-to-end.** Port `Base.lean` +
   `StableCoin.lean` core + `Params.lean`, then **Theorem 3** (smallest temporal: 1 check,
   1 `pre`) as a full `StateMachine` instance, and drive it through `#kind`. This validates:
   observer-state modeling, params encoding (decide opaque-vs-axiom here), conjoined
   invariants, depth from `unroll_max`, and — critically — whether plain `#kind` can close
   a real inductive property at all. Also port one combinational theorem (Theorems 1–2) to
   confirm the `#bmc`/low-depth path. **If the inductive gate cannot close even Theorem 3
   with its lemmas, stop and reopen scope with the user** (the honest finding, learned at
   task 1 not task 25).
2. Scale group-by-group through the remaining theorem files, one `StateMachine` instance
   per node, with per-group faithfulness checks against the Lustre source and faithful
   recording of each theorem's outcome (Valid / Undetermined / cex).
3. Wire all into `Tests.lean`; final faithfulness + coverage review (≈50 theorems / ~all
   `check`s represented).

## Success criteria

- `Stablecoin/` library type-checks; core transition faithfully mirrors `StableCoin_InitState`.
- Every Lustre theorem node has a faithful `StateMachine` encoding (correct state, input,
  init, next, assumptions, and invariants = ∧ of all its checks).
- Each theorem's verification outcome is recorded faithfully: `✅` discharged, or
  `⚠️ Undetermined` with no source-altering workaround applied.
- No invariant weakened, no assumption added beyond the source, no lemma dropped.
