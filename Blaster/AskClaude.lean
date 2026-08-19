/-
  AskClaude.lean — LLM-assisted tactics built around Blaster.

  Two tactics live here:

  * `ask_claude` — the original proof-of-concept: ask the Anthropic Messages
    API for a plain tactic script, then *elaborate it locally* so that the
    Lean kernel, not the model, decides whether the proof is valid.

  * `ask_claude_with_blaster` — the Blaster-aware version. Its job is to
    *unstuck `blaster`*, not to prove goals with an LLM:

      1. Run Blaster first (bounded solver timeout). No API key needed here.
         - Blaster proves the goal → done, via Blaster's special admit
           (`blasterProven`, accepted as valid until proof reconstruction).
         - Blaster *falsifies* the goal → error out with the counterexample;
           the LLM is never consulted about an unprovable statement.
      2. Otherwise, run an *interactive session*: Claude is shown the goal as
         Blaster sees it (its `only-optimize` form, advisory — the optimizer
         preserves provability, not definitional equality) and proposes ONE
         tactic step at a time (structural preparation such as `induction` or
         `by_cases`, `blaster (only-optimize: 1)` prep steps, and
         `blaster (timeout: _)` leaves), sees the resulting goals or errors,
         and can REVERT a step. When all goals are closed, the steps are
         assembled, re-validated from the initial goal (with a proof-term
         check that rejects non-defeq optimizer casts), and offered as a
         `Try this:` suggestion that replays with local Z3 only — inline it
         and never pay for the same proof again.

  Design invariant: the LLM is an untrusted oracle. Nothing it emits reaches
  the environment except through `evalTactic`, so a hallucinated lemma name or
  a bogus rewrite is a tactic failure, never an unsound proof.

  Requirements:
    * `curl` on PATH (Lean core has no HTTP client)
    * z3 on PATH (for `ask_claude_with_blaster`)
    * ANTHROPIC_API_KEY, resolved in this order:
        1. the environment of the elaborator process
        2. a `.env` file, searched upward from the directory of the .lean file
           being elaborated (so `lake build` and the language server agree)

  Usage:
    example (a b : Nat) : a + b = b + a := by ask_claude
    example (n : Nat)   : n ≤ n + 1     := by ask_claude "induction is overkill here"
    example (n : Nat)   : 2 * sum n = n * (n + 1) := by ask_claude_with_blaster
    example (l : List Nat) : p l := by ask_claude_with_blaster "induct on the list"
-/
import Lean
import Blaster.Command.Tactic

open Lean Elab Tactic Meta
open Lean.Meta.Tactic.TryThis
open Blaster.Optimize Blaster.Smt Blaster.Options Blaster.Tactic

namespace AskClaude

/-! ## Configuration -/

structure Config where
  /-- Pinned model snapshot. `claude-opus-5` for hard goals, `claude-haiku-4-5-20251001` for cheap ones. -/
  model      : String := "claude-sonnet-5"
  maxTokens  : Nat    := 2048
  /-- Number of generate → elaborate → feed-back-the-error rounds. -/
  rounds     : Nat    := 3
  timeoutSec : Nat    := 120
  /-- On-disk response cache; keeps rebuilds deterministic and offline. -/
  cacheDir   : String := ".lake/claude-cache"
  /-- Solver timeout (seconds) for the initial Blaster probe and for the
      `blaster (timeout: _)` leaves of generated strategies. Bounded so a bad
      case split can never hang a repair round on Blaster's default ∞. -/
  blasterTimeoutSec : Nat := 10
  /-- Interaction budget for `ask_claude_with_blaster`'s step-by-step session:
      every model reply (a step, a REVERT, or a retry after an error) spends
      one interaction. -/
  maxSteps : Nat := 12
  deriving Inhabited

/-! ## Secrets: `.env` resolution

Deliberately a `List (String × String)` rather than a `HashMap` — the `Std`/`Lean`
HashMap namespaces have moved around across toolchains and this is a 5-line file.
-/

/-- Minimal dotenv parser: `KEY=value`, tolerating an `export ` prefix, `#`
    comment lines, surrounding single/double quotes, and trailing ` # comment`
    on unquoted values. No variable interpolation, no multi-line values. -/
def parseDotenv (contents : String) : List (String × String) := Id.run do
  let mut acc := []
  for raw in contents.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    let line := if line.startsWith "export " then (line.drop 7).trim else line
    match line.splitOn "=" with
    | [] | [_] => continue
    | k :: rest =>
      let key := k.trim
      let v := ("=".intercalate rest).trim
      let quoted (c : String) := v.length ≥ 2 && v.startsWith c && v.endsWith c
      let v :=
        if quoted "\"" || quoted "'" then (v.drop 1).dropRight 1
        else (v.splitOn " #").headD v |>.trim
      unless key.isEmpty do acc := (key, v) :: acc
  return acc.reverse

/-- Walk up the directory tree looking for a `.env`. Stops at the filesystem root. -/
partial def findDotenv (dir : System.FilePath) : IO (Option System.FilePath) := do
  let candidate := dir / ".env"
  if ← candidate.pathExists then return some candidate
  match dir.parent with
  | some p => if p == dir then return none else findDotenv p
  | none   => return none

/-- Anchor the search at the file being elaborated, not at the process cwd: the
    language server's cwd is not reliably your project root.

    `getFileName` is not guaranteed absolute — under `lake build` it is often
    relative to the project root, in which case a naive upward walk terminates
    at `.` immediately. Normalise first, and fall back to walking up from cwd. -/
def anchorDir : CoreM System.FilePath := do
  let p : System.FilePath := (← getFileName)
  let cwd ← IO.currentDir
  let p := if p.isAbsolute then p else cwd / p
  match p.parent with
  | some d => return d
  | none   => IO.currentDir

def loadDotenv : CoreM (List (String × String)) := do
  let found ← findDotenv (← anchorDir)
  let found ← match found with
    | some p => pure (some p)
    | none   => findDotenv (← IO.currentDir)
  match found with
  | some p => return parseDotenv (← IO.FS.readFile p)
  | none   => return []

/-- Environment wins over `.env`, so CI can override without editing files.
    Returns `none` when no key is available — `query` only needs a key on a
    cache miss, so fully-cached sessions replay offline with no key at all. -/
def getApiKey? : CoreM (Option String) := do
  if let some k ← IO.getEnv "ANTHROPIC_API_KEY" then
    if !k.trim.isEmpty then return some k.trim
  if let some v := (← loadDotenv).lookup "ANTHROPIC_API_KEY" then
    if !v.trim.isEmpty then return some v.trim
  return none

/-! ## Transport: shell out to curl -/

/-- POST `body` to `url` with the given headers, returning the raw response body.
    The request body goes over stdin so it never hits the argv length limit and
    needs no shell quoting (`IO.Process.spawn` does not go through a shell). -/
def curlPost (url : String) (headers : Array String) (body : String)
    (timeoutSec : Nat) : IO String := do
  let hdrArgs := headers.foldl (init := #[]) fun acc h => (acc.push "-H").push h
  let args := #["-sS", "--max-time", toString timeoutSec, "-X", "POST", url]
              ++ hdrArgs ++ #["--data-binary", "@-"]
  let child ← IO.Process.spawn
    { cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr body
  stdin.flush
  -- `stdin` goes out of scope here; its finalizer closes the pipe, which is what
  -- tells curl the body is complete.
  let outTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept outTask.get
  unless code == 0 do
    throw <| IO.userError s!"curl exited with code {code}: {err}"
  return out

/-! ## Anthropic Messages API -/

/-- A conversation turn: ("user" | "assistant", content). -/
abbrev Turn := String × String

def mkBody (cfg : Config) (system : String) (turns : Array Turn) : String :=
  let messages := turns.map fun (role, content) =>
    Json.mkObj [("role", toJson role), ("content", toJson content)]
  Json.mkObj
    [ ("model",      toJson cfg.model)
    , ("max_tokens", toJson cfg.maxTokens)
    , ("temperature", toJson (1 : Nat))   -- diversity across repair rounds
    , ("system",     toJson system)
    , ("messages",   Json.arr messages) ]
  |>.compress

/-- Concatenate the `text` blocks of a Messages API response. -/
def extractText (raw : String) : Except String String := do
  let j ← Json.parse raw
  if let .ok e := j.getObjVal? "error" then
    throw s!"Anthropic API error: {e.compress}"
  let blocks ← (← j.getObjVal? "content").getArr?
  let mut out := ""
  for b in blocks do
    match b.getObjValAs? String "type", b.getObjValAs? String "text" with
    | .ok "text", .ok t => out := out ++ t
    | _, _ => pure ()
  if out.trim.isEmpty then throw s!"no text block in response: {raw}"
  return out

/-- Models like to wrap code in ``` fences despite instructions. Strip them. -/
def stripFences (s : String) : String :=
  let s := s.trim
  if s.startsWith "```" then
    let lines := (s.splitOn "\n").drop 1
    let lines := lines.filter fun l => !(l.trim.startsWith "```")
    ("\n".intercalate lines).trim
  else s

/-! ## Cache -/

def cachePath (cfg : Config) (key : UInt64) : System.FilePath :=
  (cfg.cacheDir : System.FilePath) / s!"{key}.tactic"

def cacheGet? (cfg : Config) (key : UInt64) : IO (Option String) := do
  let p := cachePath cfg key
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

def cachePut (cfg : Config) (key : UInt64) (v : String) : IO Unit := do
  IO.FS.createDirAll cfg.cacheDir
  IO.FS.writeFile (cachePath cfg key) v

/-- Cached, deterministic-on-replay call. Keyed on the whole request body, so
    repair rounds are cached too and a rebuild replays the entire session.
    The API key is only needed on a cache miss. -/
def query (cfg : Config) (apiKey? : Option String) (system : String) (turns : Array Turn) :
    IO String := do
  let body := mkBody cfg system turns
  let key  := hash body
  if let some hit ← cacheGet? cfg key then return hit
  let some apiKey := apiKey?
    | throw <| IO.userError "ask_claude: ANTHROPIC_API_KEY not found in the environment \
nor in any .env file searched upward from the elaborated file (and this request is not \
in the cache). Run #ask_claude_doctor to see what the elaborator sees."
  let raw ← curlPost "https://api.anthropic.com/v1/messages"
    #[ "content-type: application/json"
     , s!"x-api-key: {apiKey}"
     , "anthropic-version: 2023-06-01" ] body cfg.timeoutSec
  let txt := stripFences (← IO.ofExcept (extractText raw))
  cachePut cfg key txt
  return txt

/-! ## Prompt -/

def systemPrompt : String :=
"You are a Lean 4 proof engineer. You are given a Lean 4 goal state.

Reply with ONLY a Lean 4 tactic script that closes the goal. Hard rules:
- Lean 4 / Mathlib syntax. Never Lean 3: no `begin`/`end`, no `λ x, e` (use `fun x => e`),
  no `nat.succ` style names (use `Nat.succ`).
- Output tactics only. No prose, no markdown fences, no comments, no `theorem` header.
- Emit a SINGLE tactic. Sequence with `;` and combine with `<;>` where needed,
  e.g. `constructor <;> simp [Nat.add_comm]` or `(intro h; omega)`.
- Prefer short, robust scripts: `simp`, `omega`, `linarith`, `decide`, `exact <term>`.
- Every constant you mention must plausibly exist in the imported environment.
  If you are unsure of a lemma name, prove it inline with `have ... := by ...`."

def userPrompt (goal : String) (hint : Option String) : String :=
  let h := match hint with | some s => s!"\n\nHint from the user: {s}" | none => ""
  s!"Goal state:\n\n{goal}{h}"

/-! ## Parsing the reply back into syntax -/

/-- Try the reply as a single tactic; failing that, wrap it as a bracketed
    tactic sequence (indented, so `sepByIndent` accepts multi-line output). -/
def parseTactic? (code : String) : CoreM (Option (TSyntax `tactic)) := do
  let env ← getEnv
  let attempt (s : String) : Option (TSyntax `tactic) :=
    match Parser.runParserCategory env `tactic s "<ask_claude>" with
    | .ok stx => some ⟨stx⟩
    | .error _ => none
  if let some stx := attempt code then return some stx
  let indented := "\n".intercalate ((code.splitOn "\n").map ("  " ++ ·))
  return attempt s!"(\n{indented}\n)"

/-- Run a candidate against the main goal. Returns `none` on success, or the
    error message on failure, with the tactic state fully restored either way. -/
def tryScript (stx : TSyntax `tactic) : TacticM (Option String) := do
  let saved ← saveState
  try
    focus do
      withoutRecover <| evalTactic stx
      unless (← getGoals).isEmpty do
        throwError "script did not close the goal; {(← getGoals).length} goal(s) remain"
    return none
  catch e =>
    let msg ← e.toMessageData.toString
    saved.restore
    return some msg

/-- Cap a string destined for a prompt; huge optimized goals would otherwise
    blow the request up. -/
def truncateStr (s : String) (maxChars : Nat := 4000) : String :=
  if s.length ≤ maxChars then s
  else s.take maxChars ++ s!"\n… (truncated, {s.length - maxChars} characters omitted)"

/-! ## The `ask_claude` tactic -/

def run (cfg : Config) (hint : Option String) (ref : Syntax) : TacticM Unit := do
  let apiKey? ← getApiKey?
  let goalStr ← withMainContext do
    return (← Meta.ppGoal (← getMainGoal)).pretty
  let mut turns : Array Turn := #[("user", userPrompt goalStr hint)]
  let mut lastErr := "no candidate parsed"
  for _ in [0:cfg.rounds] do
    let reply ← query cfg apiKey? systemPrompt turns
    match ← parseTactic? reply with
    | none =>
      lastErr := "reply did not parse as Lean 4 tactic syntax"
      turns := (turns.push ("assistant", reply)).push
        ("user", s!"That did not parse as Lean 4 tactic syntax. Emit exactly one tactic, nothing else.")
    | some stx =>
      match ← tryScript stx with
      | none =>
        -- Success: the kernel accepted it. Offer it as an editable suggestion so
        -- the source becomes self-contained and the next build needs no network.
        addSuggestion ref stx
        return
      | some err =>
        lastErr := err
        turns := (turns.push ("assistant", reply)).push
          ("user", s!"Lean rejected that script:\n\n{err}\n\nThe goal is unchanged:\n\n{goalStr}\n\nTry a different approach.")
  throwError "ask_claude: no candidate closed the goal after {cfg.rounds} round(s).\nLast error: {lastErr}"

/--
`ask_claude` asks the Anthropic API for a plain tactic script and elaborates it
locally; the Lean kernel, not the model, decides whether the proof is valid.
An optional string argument is passed to the model as a hint.
-/
elab (name := askClaude) tk:"ask_claude" hint:(str)? : tactic => do
  run {} (hint.map (·.getString)) tk

/-! ## `ask_claude_with_blaster`: Blaster-guided strategy search

### Phase 1 — the Blaster probe -/

/-- Outcome of running Blaster once on the main goal. -/
inductive ProbeOutcome where
  /-- Blaster proved the goal; it has been closed via `blasterProven`. -/
  | closed
  /-- Blaster found a countermodel: the goal is not provable. -/
  | falsified (cex : List String)
  /-- Undetermined: `optGoal` is the pretty-printed optimized proposition
      (what `blaster (only-optimize: 1)` would turn the goal into). It is
      advisory context for the model only — the tactic state is restored, so
      strategy scripts run against the *original* goal. The optimizer is only
      guaranteed to preserve provability, not definitional equality (it may
      e.g. flip an equation), so materializing it as the new target would
      leave a cast the kernel rejects once the leaves are admitted. -/
  | prepped (optGoal : String)
  /-- Blaster errored (e.g. unsupported construct); the tactic state was
      restored and the original goal is untouched. -/
  | unsupported (err : String)

/-- Run Blaster on the main goal, mirroring the `blaster` tactic: revert `Prop`
    hypotheses, optimize, solve with a bounded timeout. Proved goals are
    admitted via `blasterProven`; otherwise the state is restored and the
    outcome carries the counterexample / the optimized form / the error. -/
def runBlasterProbe (timeoutSec : Nat) : TacticM ProbeOutcome := do
  let saved ← saveState
  try
    let goal ← revertHypotheses (← getMainGoal)
    replaceMainGoal [goal]
    let sOpts : BlasterOptions := { timeout := some timeoutSec }
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    let ((result, optExpr), _) ←
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
        IO.setNumHeartbeats 0
        Translate.main (← goal.getType) (logUndetermined := false) |>.run env
    match result with
    | .Valid =>
        blasterAdmit goal
        pruneSolvedGoals
        return .closed
    | .Falsified cex =>
        saved.restore
        return .falsified cex
    | .Undetermined =>
        let optGoal ← goal.withContext do return (← ppExpr optExpr).pretty
        saved.restore
        return .prepped optGoal
  catch e =>
    let msg ← e.toMessageData.toString
    saved.restore
    return .unsupported msg

/-- Render Blaster's countermodel (`Result.Falsified` payload) for an error
    message; the model lines carry a trailing newline, as in `logResult`. -/
def formatCex (cex : List String) : String :=
  match cex with
  | [] => " the optimizer reduced the goal to False (no model needed)."
  | _ => "\n" ++ "\n".intercalate (cex.map fun s => s!" - {s.dropRight 1}")

/-! ### Phase 2 — the interactive session

Claude drives the tactic state one step at a time: it proposes a step, sees the
resulting goals (or the error), and can `REVERT` its last step. When all goals
are closed, the accepted steps are assembled into one script, re-validated from
the initial state — including a `Meta.check` of the final proof term, which
catches non-defeq casts from kept `blaster (only-optimize: 1)` steps — and
offered as the `Try this:` suggestion. -/

def interactiveSystemPrompt (leaf : String) : String :=
s!"You are driving Lean 4 interactively to prepare goals for `blaster`, an SMT-based Lean 4 tactic backed by Z3.

Protocol — each of your replies must be EXACTLY ONE of:
1. ONE Lean 4 tactic step (no prose, no markdown fences, no comments). I apply it and reply with the new goal state, or with the error if it fails (state unchanged).
2. The single word REVERT — undoes your last successful step.

How to play:
- `blaster (only-optimize: 1)` rewrites the goal into blaster's simplified form without solving it. Often a good first step — also inside a branch, after `intro` or `induction` — to see what you are really working with. It may be kept in the final script.
- Close every goal with `{leaf}` — blaster proves goals by SMT. Never finish with simp, omega, linarith, decide or exact.
- blaster decides linear Int/Nat arithmetic, equalities, and bounded reasoning over algebraic data types; it CANNOT do induction, unfolds recursion only boundedly, and misses case splits.
- Structural steps: intro, induction x with | … => …, cases, rcases, obtain, by_cases h : P, generalize, constructor. A step may be compound (e.g. a whole `induction … with` block whose branches end in `{leaf}`).
- Most tactics act on the FIRST open goal; `case name => …` targets a named goal.
- When all goals are closed I re-validate your assembled steps from the initial goal, including a proof check. If that fails you will be told why and the session restarts from the initial goal.
- Lean 4 syntax only: `fun x => e`, `Nat.succ`; never `begin`/`end` or `λ x, e`."

def strategyUserPrompt (origGoal : String) (optGoal? : Option String)
    (probeErr? : Option String) (hint : Option String) : String :=
  let opt := match optGoal? with
    | some g => s!"\n\nblaster ran and got stuck (undetermined). After blaster's optimizer \
(hypotheses reverted into the statement), the form it is stuck on is:\n\n{g}\n\n\
Use this to pick the right structure, but your tactic script will run against the \
original goal state above."
    | none => ""
  let err := match probeErr? with
    | some e => s!"\n\nblaster failed on this goal with the error below, so your case splits \
should produce subgoals that avoid the unsupported construct. Your tactic script will run \
against the original goal.\n\n{e}"
    | none => ""
  let h := match hint with | some s => s!"\n\nHint from the user: {s}" | none => ""
  s!"Original goal state:\n\n{origGoal}{opt}{err}{h}"

/-- Apply one interactive step to the current tactic state. `none` on success
    (state advanced), or the error message (state restored). -/
def applyStep (stx : TSyntax `tactic) : TacticM (Option String) := do
  let saved ← saveState
  try
    withoutRecover <| evalTactic stx
    pruneSolvedGoals
    return none
  catch e =>
    let msg ← e.toMessageData.toString
    saved.restore
    return some msg

/-- Render the open goals for the model: count, then up to `maxGoals` states.
    `blaster` leaves that went Undetermined have already swapped in their
    optimized form, so this is precise "where blaster is stuck" feedback. -/
def ppGoalsForPrompt (maxGoals : Nat := 4) : TacticM String := do
  let gs ← getGoals
  if gs.isEmpty then return "No goals remain."
  let mut shown : Array String := #[]
  for g in gs.take maxGoals do
    shown := shown.push (← g.withContext do return (← Meta.ppGoal g).pretty)
  let rest := if gs.length > maxGoals then s!"\n\n… and {gs.length - maxGoals} more goal(s)" else ""
  let body := "\n\n---\n\n".intercalate shown.toList
  return truncateStr s!"{gs.length} open goal(s):\n\n{body}{rest}" 6000

/-- Validate a full candidate script against the main goal: it must leave zero
    goals (`blaster`'s `blasterProven` admits count as closed) AND the final
    proof term must pass `Meta.check` — this catches casts introduced by a kept
    `blaster (only-optimize: 1)` step whose rewrite is not definitionally equal
    to the goal (the kernel would otherwise reject the declaration long after
    this tactic succeeded). `none` on success (state advanced), or the error
    (state restored). -/
def tryStrategyChecked (stx : TSyntax `tactic) : TacticM (Option String) := do
  let saved ← saveState
  let root ← getMainGoal
  try
    focus do
      withoutRecover <| evalTactic stx
      pruneSolvedGoals
      let gs ← getGoals
      unless gs.isEmpty do
        let mut shown : Array String := #[]
        for g in gs.take 4 do
          shown := shown.push (← g.withContext do return (← Meta.ppGoal g).pretty)
        let rest := if gs.length > 4 then s!"\n\n… and {gs.length - 4} more subgoal(s)" else ""
        let body := "\n\n---\n\n".intercalate shown.toList
        throwError "blaster could not close {gs.length} subgoal(s). \
Remaining subgoals, as blaster sees them after optimization:\n\n{body}{rest}"
    root.withContext do
      Meta.check (← instantiateMVars (mkMVar root))
    return none
  catch e =>
    let msg ← e.toMessageData.toString
    saved.restore
    return some msg

def interactiveSession (cfg : Config) (ref : Syntax) (origGoal : String)
    (optGoal? : Option String) (probeErr? : Option String)
    (hint : Option String) : TacticM Unit := do
  let apiKey? ← getApiKey?
  let leaf := s!"blaster (timeout: {cfg.blasterTimeoutSec})"
  let sys := interactiveSystemPrompt leaf
  let mut turns : Array Turn :=
    #[("user", strategyUserPrompt (truncateStr origGoal) optGoal? probeErr? hint ++
        s!"\n\nYou have {cfg.maxSteps} interaction(s). Reply with your first step.")]
  -- Each accepted step pairs the tactic state saved *before* it with its text.
  let mut accepted : Array (Tactic.SavedState × String) := #[]
  let mut lastErr := "the interaction budget ran out before any step was accepted"
  for i in [0:cfg.maxSteps] do
    let left := cfg.maxSteps - i - 1
    let reply ← query cfg apiKey? sys turns
    turns := turns.push ("assistant", reply)
    let replyT := reply.trim
    if replyT == "REVERT" then
      match accepted.back? with
      | none =>
        turns := turns.push ("user",
          s!"Nothing to revert — you are at the initial goal:\n\n{truncateStr origGoal}\n\n\
({left} interaction(s) left.)")
      | some (saved, txt) =>
        saved.restore
        accepted := accepted.pop
        turns := turns.push ("user",
          s!"Reverted `{txt}`.\n\n{← ppGoalsForPrompt}\n\n({left} interaction(s) left.)")
      continue
    match ← parseTactic? replyT with
    | none =>
      lastErr := "reply did not parse as Lean 4 tactic syntax"
      turns := turns.push ("user",
        s!"That did not parse as Lean 4 tactic syntax. Reply with exactly one tactic step, \
or REVERT. ({left} interaction(s) left.)")
    | some stx =>
      let saved ← saveState
      match ← applyStep stx with
      | some err =>
        lastErr := err
        turns := turns.push ("user",
          s!"That step failed:\n\n{truncateStr err}\n\nThe goal state is unchanged:\n\n\
{← ppGoalsForPrompt}\n\n({left} interaction(s) left.)")
      | none =>
        accepted := accepted.push (saved, replyT)
        if (← getGoals).isEmpty then
          -- All goals closed: re-validate the assembled script from the initial
          -- state, so the Try-this suggestion is guaranteed to replay — and so
          -- a non-defeq only-optimize cast is caught here, not by the kernel.
          let script := "\n".intercalate (accepted.map (·.2)).toList
          let some scriptStx ← parseTactic? script
            | throwError "ask_claude_with_blaster: the accepted steps no longer parse as one script:\n{script}"
          let some (initState, _) := accepted[0]? | unreachable!
          initState.restore
          match ← tryStrategyChecked scriptStx with
          | none =>
            addSuggestion ref scriptStx
            return
          | some err =>
            lastErr := err
            accepted := #[]
            turns := turns.push ("user",
              s!"All goals were closed, but re-validating the assembled script from the initial \
goal failed:\n\n{truncateStr err}\n\nA common cause is a kept `blaster (only-optimize: 1)` step \
whose rewrite is not definitionally equal to the original goal — if so, redo the proof without \
keeping that step (you can still use what it showed you). The session restarts at the initial \
goal:\n\n{truncateStr origGoal}\n\n({left} interaction(s) left.)")
        else
          turns := turns.push ("user",
            s!"Step applied.\n\n{← ppGoalsForPrompt}\n\n({left} interaction(s) left.)")
  throwError "ask_claude_with_blaster: no strategy closed the goal within {cfg.maxSteps} \
interaction(s).\nLast error: {lastErr}"

def runWithBlaster (cfg : Config) (hint : Option String) (ref : Syntax) : TacticM Unit := do
  let origGoal ← withMainContext do
    return (← Meta.ppGoal (← getMainGoal)).pretty
  match ← withMainContext (runBlasterProbe cfg.blasterTimeoutSec) with
  | .closed =>
      logInfoAt ref "ask_claude_with_blaster: blaster closed the goal on its own"
      if (← getOptions).getBool `warn.sorry true then
        logWarningAt ref "declaration uses 'blasterProven' (SMT-verified, no proof term)"
      addSuggestion ref (← `(tactic| blaster))
  | .falsified cex =>
      throwError "ask_claude_with_blaster: blaster FALSIFIED the goal — it admits a \
counterexample and is not provable, so no proof strategy will be searched for. \
Counterexample:{formatCex cex}"
  | .prepped optGoal =>
      interactiveSession cfg ref origGoal (some (truncateStr optGoal)) none hint
  | .unsupported err =>
      interactiveSession cfg ref origGoal none (some (truncateStr err)) hint

/--
`ask_claude_with_blaster` unstucks `blaster` with LLM-suggested structure.

It first runs Blaster on the goal (with a bounded timeout, no API key needed):
* Blaster proves it → the goal is closed via Blaster's `blasterProven` admit
  and `blaster` is suggested as the replacement tactic.
* Blaster falsifies it → the tactic **fails with the counterexample**; no LLM
  round is attempted for an unprovable goal.
* Otherwise Claude drives an interactive session: shown the goal (plus its
  optimized form as context), it proposes ONE tactic step at a time —
  `induction`, `by_cases`/`cases` splits, `intro`, `generalize`, and
  `blaster (only-optimize: 1)` prep steps are all fair game — sees the
  resulting goals or the error after each, and can `REVERT` its last step.
  Every branch is closed with `blaster (timeout: _)`. Once no goals remain,
  the accepted steps are assembled, re-validated from the initial goal
  (including a proof-term check that rejects non-defeq optimizer casts), and
  offered as a `Try this:` suggestion; inlining it makes the proof replay with
  local Z3 only, so the same proof is never paid for twice.

An optional string argument is passed to the model as a hint, e.g.
`ask_claude_with_blaster "induct on the list, not on n"`.
-/
elab (name := askClaudeWithBlaster) tk:"ask_claude_with_blaster" hint:(str)? : tactic => do
  runWithBlaster {} (hint.map (·.getString)) tk

/-! ## Diagnostics -/

/-- Prints exactly what the elaborator sees. Run it in the editor (goes through
    the language server) and compare with `lake env lean YourFile.lean`.
    Only key *names* are printed, never values. -/
elab "#ask_claude_doctor" : command => Command.liftCoreM do
  let fname ← getFileName
  let anchor ← anchorDir
  let cwd ← IO.currentDir
  let found ← findDotenv anchor
  let foundStr : String := match found with
    | some p => p.toString
    | none   => "NOT FOUND"
  let envOpt ← IO.getEnv "ANTHROPIC_API_KEY"
  let envStr : String := if envOpt.isSome then "set" else "unset"
  let vars ← loadDotenv
  let names : String := String.intercalate ", " (vars.map Prod.fst)
  logInfo <|
    "fileName : " ++ fname ++
    "\nanchor   : " ++ anchor.toString ++
    "\ncwd      : " ++ cwd.toString ++
    "\n.env     : " ++ foundStr ++
    "\nenv var  : " ++ envStr ++
    "\n.env keys: " ++ names

end AskClaude
