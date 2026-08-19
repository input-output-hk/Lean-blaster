# `ask_claude_with_blaster` — design

Date: 2026-08-19
Status: implemented and tested end-to-end (see `Blaster/AskClaude.lean`)

## Goal

Turn the proof-of-concept `ask_claude` tactic into `ask_claude_with_blaster`, a
tactic whose job is to **unstuck `blaster`**, not to prove goals with an LLM:

1. Run Blaster first. If Blaster proves the goal, we are done (via Blaster's
   special admit, `blasterProven` — accepted as valid until proof
   reconstruction exists). If Blaster **falsifies** the goal, the tactic
   **errors out with the counterexample** and never consults the LLM.
2. Otherwise, show Claude the goal *as Blaster sees it* (its
   `blaster (only-optimize: 1)` form) and ask it for the minimal
   **structural preparation** — the right `induction`, or the right
   `by_cases` split(s) — with every branch closed by `blaster`.

The LLM remains an untrusted oracle: nothing it emits reaches the environment
except through `evalTactic`.

## Flow

```
ask_claude_with_blaster
  │
  ├─ Phase 1: Blaster probe (no LLM, no API key, no network)
  │    revert Prop hypotheses (same as `blaster`), run Translate.main with a
  │    bounded solver timeout (Config.blasterTimeoutSec, default 10s)
  │    ├─ Valid            → close goal via blasterAdmit; suggest `blaster`; DONE
  │    ├─ Falsified cex    → throwError with the counterexample; STOP
  │    ├─ Undetermined     → pretty-print the optimized expression, RESTORE the
  │    │                     original tactic state (see "non-defeq" below)
  │    └─ exception        → restore state; carry Blaster's error text into the
  │                          prompt; work from the original goal
  │
  └─ Phase 2: Claude strategy loop (Config.rounds, default 3)
       system prompt: emit ONLY structural preparation (intro / induction …
       with | … / cases / rcases / obtain / by_cases / generalize); every
       branch MUST end with `blaster (timeout: N)`; no finishing tactics
       user prompt: original goal + optimized form (advisory, truncated) +
       probe error (if any) + user hint (if any)
       ├─ reply parses & evalTactic (against the ORIGINAL goal) leaves 0 goals
       │     → addSuggestion of the bare script; DONE
       └─ failure → feed back the parse/elab error, or the pretty-printed
             subgoals blaster left open (blaster's Undetermined branch swaps in
             their optimized form before we print them — precise "this is where
             I am stuck" feedback), and retry
```

## Key decisions

- **One probe, both directions.** A single full `Translate.main` run returns
  `(Result, optExpr)`: it detects Valid/Falsified *and* yields the optimized
  expression shown to the model. Running `only-optimize` separately would cost
  the counterexample detection.
- **Falsified ⇒ hard error.** The tactic refuses to ask an LLM to "prove" a
  statement Blaster has a countermodel for. The error embeds the model lines
  (`Result.Falsified (cex : List String)`), in addition to Blaster's own
  `❌ Falsified` log.
- **The optimized form is advisory, never the target (non-defeq!).** The first
  implementation replaced the goal with `optExpr` via `replaceTargetDefEq`,
  mirroring `blaster`'s own Undetermined branch. The kernel rejected the
  resulting proofs: the optimizer preserves provability, **not definitional
  equality** — e.g. it rewrote `2 * sumTo n = n * (n + 1)` to
  `n * (1 + n) = 2 * sumTo n` (equation flipped), and the implicit `id`-cast
  between the two types fails kernel typechecking once the leaves are admitted.
  So the script is validated against the *original* goal; `blaster` leaves
  re-optimize internally and admit at the leaf's own type, so no cast exists
  anywhere. ⚠️ Note this means `blaster`'s own Undetermined goal-replacement
  has the same latent issue for users who then prove the optimized goal by
  hand — filed as an observation, not fixed here.
- **`blasterProven` admit = success.** Leaves closed by `blaster` assign the
  `blasterProven` axiom; the loop counts a candidate as successful when zero
  goals remain, which includes admitted ones. Each leaf logs Blaster's
  "declaration uses 'blasterProven'" warning.
- **Pay once, replay free.** On success the script is offered as a `Try this:`
  suggestion (code action in the editor, printed in CLI builds). Since it runs
  against the original goal, inlining it yields a self-contained proof that
  replays with local Z3 only. Round-trip verified: the pretty-printer renders
  `blaster(timeout:10)` (no spaces) and that reparses fine. The on-disk
  response cache (`.lake/claude-cache`, keyed on the full request body) covers
  un-inlined calls.
- **Leaves carry a timeout.** Claude is instructed to close branches with
  `blaster (timeout: N)` (N = `Config.blasterTimeoutSec`) so a bad split can
  never hang a repair round on Blaster's default infinite timeout.
- **A falsified *leaf* is candidate failure,** not a hard error (it may mean a
  wrong split); only the initial probe's counterexample means "goal is
  unsatisfiable".

## Code changes

- `Blaster/Command/Tactic.lean`: expose `blasterAdmit` (drop `private`) and
  lift `revertHypotheses` out of `blasterTacticImp`'s `where` clause so
  `AskClaude` reuses them. No behavior change.
- `Blaster/AskClaude.lean`: keep transport (curl), `.env` resolution, on-disk
  cache, parsing and the original `ask_claude`; add `Config.blasterTimeoutSec`,
  the probe (`ProbeOutcome`), strategy prompts, `tryStrategy` (rich subgoal
  feedback) and the `ask_claude_with_blaster` elab.
- `Blaster.lean`: root imports `Blaster.AskClaude` so `import Blaster` brings
  the tactics in (needed for the language server to resolve the module).

## Verified behavior (2026-08-19, scratch tests)

- `∀ x y : Nat, x + y ≥ x` → probe closes it, warns `blasterProven`, suggests
  `blaster`.
- `∀ x y : Nat, x + y > x` → hard error with counterexample `x: 0, y: 0`,
  no API call.
- `double n = 2 * n` and `2 * sumTo n = n * (n + 1)` (recursive defs) → probe
  stuck, Claude proposed `induction n with | zero => blaster (timeout: 10)
  | succ n ih => blaster (timeout: 10)`, all leaves SMT-verified, kernel
  accepted, suggestion emitted; pasted suggestion replays offline.
- `spec01_HelloWorld` (validator benchmark) → probe closes it directly.

## Planned next (user feedback, 2026-08-19)

1. Allow keeping `blaster (only-optimize: 1)` as a *step* in accepted scripts
   (useful prep even before induction/by_cases). Requires a final whole-proof
   `Meta.check` in validation, because only-optimize materializes the
   optimizer's non-defeq rewrite as a cast — candidates whose cast is not
   definitionally equal must be rejected in-loop, not by the kernel later.
2. Interactive sessions: Claude proposes one step at a time, sees the
   resulting goals, can propose the next step or REVERT the last one; on
   success the accepted steps are assembled, re-validated from the initial
   state, and suggested.

## Out of scope (deliberately)

- Proof reconstruction (tracked elsewhere; `blasterProven` stays an axiom).
- Exposing all Blaster `solveOption`s on the tactic syntax — only the string
  hint is exposed; timeouts/model/rounds live in `AskClaude.Config`.
- Fixing `blaster`'s own non-defeq `replaceTargetDefEq` goal replacement.
