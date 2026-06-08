# StableCoin → Blaster StateMachine Port Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the Kind2-verified Lustre StableCoin formalization to Lean 4, modeling it as Blaster `StateMachine` instances and verifying every theorem via `#bmc`/`#kind`.

**Architecture:** A shared core (types + economic functions + a one-step transition `stepStableCoin`) plus one `StateMachine` instance per Lustre theorem node. The state `β` is the bank *pre-state* plus the node's `-> pre` observer fields; `invariants` recomputes the current step via `stepStableCoin` and asserts the node's checks (conjoined). Verification mirrors Kind2's BMC + k-induction.

**Tech Stack:** Lean 4, Lake, in-repo `Blaster` library + its `StateMachine` class (`Blaster/StateMachine/`), Z3.

**Reference source:** `/Users/romainsoulat/Documents/GitHub/stablecoin/stablecoin-plutus/fm/stablecoin/` — `Base.lus`, `Constraints.lus`, `StableCoin.lus`, `theorems/Theorem*.lus`.

**Spec:** `docs/superpowers/specs/2026-06-08-stablecoin-blaster-port-design.md`

---

## Cardinal rules (apply to EVERY task — repeat to every subagent)

1. **Encode the Lustre source exactly.** Never add an assumption the source lacks, weaken an invariant, or drop a lemma check to make `#kind` pass. Blaster's `#kind` is *plain* k-induction (no invariant generation), so some temporal theorems **will not discharge** — a `⚠️ Undetermined` / "couldn't establish induction up to depth N" is an **acceptable, documented outcome**, NOT a failure to fix by altering the model.
2. **`invariants` = conjunction of ALL `check`s in the node** (main property AND every lemma), not just the headline theorem. The lemmas are the inductive strengthening.
3. **`div`/`mod` → `Int.ediv`/`Int.emod`** (Euclidean, matches Kind2/SMT-LIB).
4. Report each theorem's outcome faithfully (Valid / Undetermined / counterexample).

## Conventions

- Run a file: `lake env lean <path>` (after `lake build Blaster Stablecoin`). `#bmc`/`#kind` print progress and a final ✅/⚠️/cex.
- StateMachine API (see `tests/StateMachine/Counter01.lean` for the shape):
  ```lean
  instance myThm : StateMachine InputType StateType where
    init i := ...          -- α → β
    next i s := ...        -- α → β → β
    assumptions i s := ... -- α → β → Prop
    invariants i s := ...  -- α → β → Prop
  #bmc (max-depth: N) [myThm]
  #kind (max-depth: N) [myThm]
  ```
  `max-depth` N comes from the Lustre file header's `--unroll_max N` comment.
- **Framework pairing (critical):** `st₀ = init in₀`, `stₖ₊₁ = next inₖ stₖ`, and `invariants inₖ stₖ` / `assumptions inₖ stₖ`. So `β` is the bank **pre-state** for the step about to be applied; the invariant computes the current step's output + new state *inside itself* via `stepStableCoin`.

---

## Task 1: `Stablecoin/Base.lean` — types, constants, helpers

**Files:** Create `Stablecoin/Base.lean`; Create `Stablecoin.lean` (lib root); Modify `lakefile.lean`.

- [ ] **Step 1: Register the lib.** In `lakefile.lean`, after the `lean_lib «Ratio»` block, add:
```lean
lean_lib «Stablecoin» where
  precompileModules := true
```

- [ ] **Step 2: Create lib root** `Stablecoin.lean`:
```lean
import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
```

- [ ] **Step 3: Create** `Stablecoin/Base.lean` (faithful to `Base.lus`):
```lean
import Lean
import Blaster

namespace Stablecoin

inductive Order where | MintSC | MintRC | NoOrder
deriving BEq, Repr, DecidableEq, Inhabited

inductive Proceed where | MintedSC | MintedRC | RedeemedSC | RedeemedRC | Error | NoReply
deriving BEq, Repr, DecidableEq, Inhabited

inductive ErrorInfo where | Min_Ratio_Violated | Max_Ratio_Violated | Invalid_Mint_Value | None
deriving BEq, Repr, DecidableEq, Inhabited

inductive Stable where | Undefined | Variable | Constant
deriving BEq, Repr, DecidableEq, Inhabited

structure InputMsg where
  order : Order
  qnt   : Int
deriving BEq, Repr, Inhabited

structure OutputMsg where
  ack   : Proceed
  err   : ErrorInfo
  price : Int
deriving BEq, Repr, Inhabited

structure Fees where
  fee_b_sc : Int
  fee_s_sc : Int
  fee_b_rc : Int
  fee_s_rc : Int
deriving BEq, Repr, Inhabited

structure Parameters where
  r_min  : Int
  r_max  : Int
  fees   : Fees
  n_sc_s : Int
  p_min  : Int
deriving BEq, Repr, Inhabited

def PER : Int := 100
def ZERO : Int := 0
def TWOPER : Int := 200

def ErrorCode1 : OutputMsg := { ack := .Error, err := .Min_Ratio_Violated, price := 0 }
def ErrorCode2 : OutputMsg := { ack := .Error, err := .Max_Ratio_Violated, price := 0 }
def ErrorCode3 : OutputMsg := { ack := .Error, err := .Invalid_Mint_Value, price := 0 }
def NullReply  : OutputMsg := { ack := .NoReply, err := .None, price := 0 }

/-- Lustre `min` (named `minR` to avoid clashing with `_root_.min`). -/
def minR (a b : Int) : Int := if a < b then a else b
/-- Lustre `max`. -/
def maxR (a b : Int) : Int := if a < b then b else a
/-- Lustre `abs`. -/
def absR (a : Int) : Int := if a < 0 then -a else a

/-- computeFee: rounds the fee toward +∞ via the +99 trick; `div` → `Int.ediv`. -/
def computeFee (baseFee t_price : Int) : Int :=
  let delta_fee := if t_price > 0 then baseFee - PER else PER - baseFee
  let t_fee := Int.ediv (absR t_price * delta_fee + 99) PER
  t_price + t_fee

end Stablecoin
```

- [ ] **Step 4: Build.** `lake build Blaster Stablecoin 2>&1 | tail -3`. Expected: success. (If a `deriving` clause fails for an enum/struct, adjust minimally — every type used in SMT needs `BEq`; `Parameters`/`Fees` need `Inhabited` for the opaque `params` in Task 2.)

- [ ] **Step 5: Commit.** `git add lakefile.lean Stablecoin.lean Stablecoin/Base.lean && git commit -m "feat: Stablecoin Base types and helpers"`

---

## Task 2: `Stablecoin/Params.lean` — abstract parameters

**Files:** Create `Stablecoin/Params.lean`.

- [ ] **Step 1: Create** `Stablecoin/Params.lean`:
```lean
import Lean
import Blaster
import Stablecoin.Base

namespace Stablecoin

/-- Abstract stablecoin parameters: an uninterpreted constant (proven for all valid
    parameter values). "Params unchanged over time" is automatic — it is a constant. -/
opaque params : Parameters

/-- `ParameterConstraints` (Constraints.lus) magnitude bounds. The temporal
    "params unchanged" assert is automatic (params is a constant). -/
def paramConstraints : Prop :=
  params.r_max ≥ params.r_min ∧
  params.fees.fee_b_sc > PER ∧ params.fees.fee_b_sc ≤ TWOPER ∧
  params.fees.fee_s_sc ≥ ZERO ∧ params.fees.fee_s_sc < PER ∧
  params.fees.fee_b_rc > PER ∧ params.fees.fee_b_rc ≤ TWOPER ∧
  params.fees.fee_s_rc ≥ ZERO ∧ params.fees.fee_s_rc < PER ∧
  params.n_sc_s > ZERO ∧ params.p_min > ZERO ∧
  params.r_min > Int.ediv (params.fees.fee_b_sc + 99) PER

end Stablecoin
```

- [ ] **Step 2: Build.** `lake build Stablecoin 2>&1 | tail -3`. Expected: success. If `opaque params : Parameters` errors (needs `Nonempty Parameters`), confirm `Parameters`/`Fees` derive `Inhabited` (Task 1). **Do NOT switch to `axiom` yet** — the opaque-vs-axiom translation question is resolved empirically in Task 4 (the gate). Leave a comment noting this.

- [ ] **Step 3: Commit.** `git add Stablecoin/Params.lean && git commit -m "feat: abstract Stablecoin params + ParameterConstraints"`

---

## Task 3: `Stablecoin/StableCoin.lean` — economic functions + transition

**Files:** Create `Stablecoin/StableCoin.lean`.

- [ ] **Step 1: Create** `Stablecoin/StableCoin.lean` (faithful to `StableCoin.lus`; `div` → `Int.ediv`):
```lean
import Lean
import Blaster
import Stablecoin.Base
import Stablecoin.Params

namespace Stablecoin

/-- The bank state (reserve, number of stablecoins, number of reserve coins). -/
structure CoreState where
  reserve : Int
  n_sc    : Int
  n_rc    : Int
deriving BEq, Repr, Inhabited

/-- equity = reserve - min(reserve, n_sc*rate), expressed as the source's if-form. -/
def equity (reserve n_sc rate : Int) : Int :=
  if reserve > n_sc * rate then reserve - (n_sc * rate) else ZERO

def price_sc (reserve n_sc rate : Int) : Int :=
  if n_sc > ZERO then
    (if reserve ≥ n_sc * rate then rate else Int.ediv reserve n_sc)
  else rate

def price_rc (d_rc reserve n_sc n_rc rate : Int) : Int :=
  if n_rc = ZERO then params.p_min
  else if d_rc ≥ ZERO then maxR (Int.ediv (equity reserve n_sc rate) n_rc) params.p_min
  else Int.ediv (equity reserve n_sc rate) n_rc

def mintSC (d_sc rate reserve n_sc : Int) : OutputMsg :=
  let s_price := price_sc reserve n_sc rate * d_sc
  let b_fee := if d_sc ≥ ZERO then params.fees.fee_b_sc else params.fees.fee_s_sc
  let t_price := computeFee b_fee s_price
  let t_reserve := reserve + t_price
  if d_sc ≥ ZERO then
    if rate > ZERO ∧ t_reserve ≥ (n_sc + d_sc) * rate * params.r_min then
      { ack := .MintedSC, err := .None, price := t_price }
    else ErrorCode1
  else if -d_sc ≤ n_sc ∧ rate > ZERO then
    { ack := .RedeemedSC, err := .None, price := t_price }
  else ErrorCode3

def mintRC (d_rc rate reserve n_sc n_rc : Int) : OutputMsg :=
  let r_price := price_rc d_rc reserve n_sc n_rc rate * d_rc
  let b_fee := if d_rc ≥ ZERO then params.fees.fee_b_rc else params.fees.fee_s_rc
  let t_price := computeFee b_fee r_price
  let t_reserve := reserve + t_price
  if d_rc ≥ ZERO then
    if n_sc < params.n_sc_s ∨ t_reserve ≤ n_sc * rate * params.r_max then
      { ack := .MintedRC, err := .None, price := t_price }
    else ErrorCode2
  else if -d_rc ≤ n_rc then
    if n_sc = ZERO ∨ (rate > ZERO ∧ t_reserve ≥ n_sc * rate * params.r_min) then
      { ack := .RedeemedRC, err := .None, price := t_price }
    else ErrorCode1
  else ErrorCode3

/-- One transition step (the `StableCoin_InitState` body). Given the previous bank
    state `p` (= `(p_reserve, p_sc, p_rc)`) and the input, returns `(output, new state)`. -/
def stepStableCoin (i_msg : InputMsg) (rate : Int) (p : CoreState) : OutputMsg × CoreState :=
  let o_msg :=
    if i_msg.order = .NoOrder then NullReply
    else if i_msg.order = .MintSC then mintSC i_msg.qnt rate p.reserve p.n_sc
    else mintRC i_msg.qnt rate p.reserve p.n_sc p.n_rc
  let reserve := if o_msg.ack = .Error then p.reserve else p.reserve + o_msg.price
  let n_sc := if o_msg.ack = .MintedSC ∨ o_msg.ack = .RedeemedSC then p.n_sc + i_msg.qnt else p.n_sc
  let n_rc := if o_msg.ack = .MintedRC ∨ o_msg.ack = .RedeemedRC then p.n_rc + i_msg.qnt else p.n_rc
  (o_msg, { reserve := reserve, n_sc := n_sc, n_rc := n_rc })

end Stablecoin
```

- [ ] **Step 2: Build.** `lake build Stablecoin 2>&1 | tail -3`. Expected: success. (Enum equality in conditions uses `=`; it is Decidable via the derived `DecidableEq`, so `if i_msg.order = .NoOrder then …` elaborates. If Lean prefers `==`, switch those conditions to `==`.)

- [ ] **Step 3: Commit.** `git add Stablecoin/StableCoin.lean && git commit -m "feat: StableCoin economic functions and transition step"`

---

## Task 4: GATE — Theorem 3 as a StateMachine, verified by `#kind`

This is the decision gate. It validates the entire encoding (observer state, params, conjoined invariants, depth) on a genuinely inductive theorem, and reveals whether plain `#kind` can close a real inductive property.

**Source:** `theorems/Theorem3.lus` (header `--unroll_max 3`; one observer `p_rate = rate -> pre rate`; main check THEOREM_3 + 2 lemma checks).

**Files:** Create `Tests/Stablecoin/Theorem3.lean`.

- [ ] **Step 1: Create** `Tests/Stablecoin/Theorem3.lean`:
```lean
import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem3

/-- Input for the StableCoin step. -/
structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + the one observer `p_rate` (= previous step's rate). -/
structure St where
  core   : CoreState
  p_rate : Int          -- `rate -> pre rate`
deriving BEq, Repr, Inhabited

instance theorem3 : StateMachine Inp St where
  init i :=
    -- StableCoin starts from (0,0,0); p_rate at step 0 = rate (`-> pre rate` ⇒ current).
    let (_, c) := stepStableCoin i.i_msg i.rate ⟨0, 0, 0⟩
    { core := c, p_rate := i.rate }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c, p_rate := s.p_rate_then_rate i }   -- see note below
  assumptions _ _ := paramConstraints
  invariants i s :=
    -- Recompute this step's output + new state from the pre-state `s.core`.
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve := c.reserve
    let n_sc := c.n_sc
    let rate := i.rate
    let p_rate := s.p_rate
    -- THEOREM_3 + the 2 lemma checks, conjoined:
    ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate ∧
        (rate - p_rate) * reserve ≤ (reserve - n_sc * p_rate) * rate) →
          price_sc reserve n_sc rate = rate )
    ∧ ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate ∧
        (rate - p_rate) * reserve ≤ (reserve - n_sc * p_rate) * rate) →
          reserve ≥ n_sc * rate )
    ∧ ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate) →
          (reserve - n_sc * p_rate) * rate > 0 )

#kind (max-depth: 3) [theorem3]

end Tests.Stablecoin.Theorem3
```

> **NOTE on the observer in `next`:** the placeholder `s.p_rate_then_rate i` above is wrong on purpose — you must encode `p_rate = rate -> pre rate` correctly. The framework gives `stₖ₊₁ = next inₖ stₖ`, and `invariants inₖ₊₁ stₖ₊₁` must see `p_rate = rateₖ` (the rate of the step that produced `stₖ₊₁`). So **`next i s` must set `p_rate := i.rate`** (the current input's rate becomes the *previous* rate for the next step). Replace the `next` line with:
> ```lean
>   next i s :=
>     let (_, c) := stepStableCoin i.i_msg i.rate s.core
>     { core := c, p_rate := i.rate }
> ```
> Verify this against the framework semantics in `Blaster/StateMachine/BMC.lean` (the `cex(k)` formula) and `KInduction.lean` before proceeding — if the pairing differs, fix the observer accordingly. Getting this exactly right is the point of the gate.

- [ ] **Step 2: Empirically resolve the `params` encoding.** Run `lake build Blaster Stablecoin && lake env lean Tests/Stablecoin/Theorem3.lean 2>&1 | tail -20`. If the run errors that the `opaque params` constant cannot be translated (uninterpreted-constant failure), switch `Stablecoin/Params.lean` from `opaque params : Parameters` to an axiomatized form Blaster accepts (e.g. `axiom params : Parameters`, or a `variable`/section binder, or an axiom giving its existence) — consult how `tests/FixedIssues/Issue25.lean` declares `axiom`s that Blaster translates. Iterate until `params` translates.

- [ ] **Step 3: Drive `#kind` and record the outcome.** Re-run the file. Capture the full output. Outcomes:
  - `✅ No counterexample up to Depth 3` / induction established → the encoding + plain `#kind` close Theorem 3. 
  - `⚠️ … couldn't establish induction up to Depth N` → record it; try raising `(max-depth: N)` modestly and `(timeout: N)`, but **do not** add assumptions or weaken the invariant. If it still won't close, that is the honest finding.
  - A counterexample → inspect: is it a *real* encoding bug (wrong observer, wrong transition) or a genuine cex? Fix encoding bugs; never mask a genuine result.

- [ ] **Step 4: DECISION GATE.** 
  - If Theorem 3 (or, after Step 3, a clear "Undetermined but faithfully encoded" result) is reached **with the model faithful to the source**, the machinery works — proceed to Task 5.
  - If the encoding cannot even be made to *elaborate and run* (framework can't handle struct state / params / the observer pattern), **STOP and report to the controller** — the StateMachine approach needs rethinking before scaling. (This is the cheap-failure point the gate exists for.)

- [ ] **Step 5: Commit.** `git add Tests/Stablecoin/Theorem3.lean Stablecoin/Params.lean && git commit -m "feat: Theorem 3 StateMachine gate (inductive, #kind)"` (include Params.lean if the encoding changed).

---

## Task 5: Theorem 1–2 (combinational + extra inputs) and Theorem 4

Confirms the combinational path and the extra-input pattern (`rational_user`, `s_market`) on top of the validated core.

**Source:** `theorems/Theorem1_and_2.lus` (node `Theorem2`, extra inputs `rational_user : bool`, `s_market : SecondaryMarket`; uses `StableCoin` init `(0,0,0)`; no `pre`; 2 checks + behavioral asserts). `theorems/Theorem4.lus` (1 check, `equity ≥ 0`, no extra inputs).

**Files:** Create `Tests/Stablecoin/Theorem1_and_2.lean`, `Tests/Stablecoin/Theorem4.lean`.

- [ ] **Step 1: Theorem 4** (simplest invariant). Create `Tests/Stablecoin/Theorem4.lean` following the Task 4 exemplar: `Inp = {i_msg, rate}`, `St = {core : CoreState}` (no observer), `init`/`next` via `stepStableCoin` from `(0,0,0)`/`s.core`, `assumptions := paramConstraints`, `invariants i s := let (_, c) := stepStableCoin i.i_msg i.rate s.core; equity c.reserve c.n_sc i.rate ≥ 0`. `#kind (max-depth: 3) [theorem4]`. Run; record outcome.

- [ ] **Step 2: Theorem 1–2.** Create `Tests/Stablecoin/Theorem1_and_2.lean`. Add the `SecondaryMarket` types:
```lean
inductive MarketAction where | BuyOffer | SellOffer | NoOffer
deriving BEq, Repr, DecidableEq, Inhabited
structure SecondaryMarket where
  action : MarketAction
  price  : Int
deriving BEq, Repr, Inhabited
```
  `Inp = { i_msg : InputMsg, rate : Int, rational_user : Bool, s_market : SecondaryMarket }`; `St = { core : CoreState }`. `assumptions i s` = `paramConstraints ∧ <the four rational-user behavioral asserts from Theorem1_and_2.lus, verbatim>` (each `assert A => B` becomes `A → B`; read them from the source and reproduce exactly — they reference `p_reserve = s.core.reserve`, `p_sc = s.core.n_sc`, `rate`, `computeFee`, `price_sc`). `invariants i s` = the conjunction of THEOREM_1 and THEOREM_2, where `sufficient_reserve`, `p_reserve`, `p_sc` are taken from `s.core` (the pre-state) and `o_msg` from `stepStableCoin i.i_msg i.rate s.core`. `#bmc (max-depth: 2) [theorem12]` and `#kind (max-depth: 2) [theorem12]`. Run; record outcomes.

- [ ] **Step 3: Faithfulness check + commit.** Verify the assert/invariant encodings line-by-line against the two source files (especially that no behavioral assert is dropped or strengthened). `git add Tests/Stablecoin/Theorem4.lean Tests/Stablecoin/Theorem1_and_2.lean && git commit -m "feat: Theorems 1,2,4 StateMachine instances"`

---

## Tasks 6–N: Remaining theorem files (port group-by-group)

Each remaining `theorems/Theorem*.lus` file becomes one `Tests/Stablecoin/<same-name>.lean`, encoded by **following the Task 4 (temporal) and Task 5 (combinational) exemplars exactly**. For each file the implementer MUST:

1. **Read the Lustre file fully.** Identify: extra inputs (→ fields of `Inp`); every stream defined with `-> pre` (→ observer fields of `St`, with `init` seeding the `->` initial value and `next` setting the `pre` update — e.g. `x = e0 -> pre f` ⇒ `init: x := e0`, `next: x := <f evaluated on the pre-state/inputs>`); the `assert`s (→ `assumptions`, verbatim, `=>`→`→`); ALL `check`s (→ `invariants` as their **conjunction**); init source (`StableCoin` ⇒ from `(0,0,0)`; `StableCoin_InitState` ⇒ from the node's `i_reserve/i_sc/i_rc` inputs); and `--unroll_max N` (→ `max-depth: N`).
2. Encode `Inp`, `St`, the `StateMachine` instance, and `#kind (max-depth: N) [inst]` (plus `#bmc` if useful for cex).
3. Run `lake env lean <file>`, record each check's outcome faithfully. Apply `(timeout: N)` for heavy nonlinear ones. **Never** add/weaken/drop to force green (Cardinal Rule 1).
4. Do a line-by-line faithfulness check vs the source; commit the file.

**Grouping (one task per group; disjoint files — may run in small parallel batches with central commit):**

- [ ] **Task 6 — Single-theorem combinational nodes:** `Theorem5`, `Theorem6`, `Theorem8`, `Theorem9`, `Theorem10`, `Theorem11`, `Theorem12` (check each header for `pre`; `Theorem5/6/8/9` have some `pre` — treat as temporal with observers).
- [ ] **Task 7 — Bundled combinational nodes:** `Theorem13_to_15`, `Theorem16`, `Theorem17`, `Theorem18`, `Theorem19`, `Theorem20`.
- [ ] **Task 8 — Bundled nodes:** `Theorem21_and_22`, `Theorem23_and_24`, `Theorem25_and_26`, `Theorem27_to_29`, `Theorem30_and_31`.
- [ ] **Task 9 — Bundled nodes:** `Theorem32_to_38`, `Theorem39_and_40`, `Theorem41`, `Theorem42`, `Theorem43`.
- [ ] **Task 10 — Bundled nodes:** `Theorem44_to_46`, `Theorem47`, `Theorem48`, `Theorem49_and_50`.
- [ ] **Task 11 — The hard temporal one:** `Theorem7` (no reserve draining; observers `reserve_0`, `n_sc_0`, `n_rc_0`, `constant_rate`, `coins_positive`; `--unroll_max 3`, 600s). This is the most likely to land `⚠️ Undetermined` under plain `#kind` — encode faithfully (all ~13 lemma checks conjoined), give it a generous `(timeout: …)`, and record the outcome honestly without altering the model.

For each task: dispatch reads the listed `.lus` files, encodes per the recipe, runs, records per-check outcomes, faithfulness-checks vs source, commits each `Tests/Stablecoin/<name>.lean`.

---

## Task 12: Wire into the test driver + final review

**Files:** Modify `Tests.lean`.

- [ ] **Step 1:** Append `import Tests.Stablecoin.<Name>` for every created file under `Tests/Stablecoin/`.
- [ ] **Step 2:** `lake build Stablecoin` then build the test modules: `lake build Tests.Stablecoin.Theorem3 …` (list all). Confirm they elaborate. `⚠️ Undetermined` is not a build failure.
- [ ] **Step 3:** Final faithfulness + coverage review (dispatch a capable reviewer): every Lustre theorem node has a faithful instance; `invariants` = ∧ of all node checks for each; no assumption added/invariant weakened/lemma dropped anywhere; produce a per-file table of outcomes (Valid / Undetermined / cex). 
- [ ] **Step 4:** Commit. `git add Tests.lean && git commit -m "test: register Stablecoin StateMachine suite"`

---

## Self-review notes (for the executor)

- **Spec coverage:** Base/Params/StableCoin (Tasks 1–3); StateMachine model + per-theorem instances (Tasks 4–11); uniform `#bmc`/`#kind` (every instance); abstract params (Task 2, empirically finalized Task 4); `invariants` = ∧ of checks (recipe + Cardinal Rule 2); `div`→`Int.ediv` (Tasks 1,3 + Rule 3); honesty rule (Cardinal Rule 1, Task 4 gate, Task 11); gate-first ordering (Task 4 decision gate).
- **The gate (Task 4) is load-bearing.** Do not skip its decision step or proceed to Tasks 6–11 if the machinery isn't validated.
- **Observer encoding** is the recurring subtlety: every `-> pre` stream is a `St` field, seeded in `init`, updated in `next`; the invariant recomputes the current step via `stepStableCoin` on the pre-state `s.core`.
- **Out of scope:** any change to the Lustre source; proving theorems Kind2 only closed via invariant generation (record as Undetermined).
