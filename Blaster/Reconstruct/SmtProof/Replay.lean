import Lean
import Blaster.Reconstruct.SmtProof.IR
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.SmtProof.Prop
import Blaster.Reconstruct.SmtProof.Local
import Blaster.Reconstruct.SmtProof.Farkas
import Blaster.Optimize.Expr

/-!
# Replay of SMT proofs

Each step of a proof (see `IR.lean`) is replayed as a Lean proof of the interpretation of its
conclusion (see `Interp.lean`), given the proofs of its premises:
 - structural rules (resolution, modus ponens, equality reasoning, quantifier instantiation,
   hypotheses and lemmas) are replayed with explicit proof terms;
 - theory and rewriting rules are replayed by proving the implication `premises → conclusion` with
   a portfolio of tactics. Since steps are small, tactics usually succeed quickly;
 - leaves (asserted formulas) and steps that can't be replayed otherwise are proved directly with
   the bridge tactics provided by the caller (e.g., from the negated goal).
-/

open Lean Meta Elab Term Tactic

namespace Blaster.Reconstruct.SmtProof

/-- Statistics on replayed steps. -/
structure ReplayStats where
  /-- per rule: number of steps replayed by each method -/
  byRule : Std.HashMap String (Std.HashMap String Nat) := {}
  /-- per rule: time (ms) spent in replay attempts, including failed ones -/
  msByRule : Std.HashMap String Nat := {}
  failures : Array String := #[]
  deriving Inhabited

def ReplayStats.record (s : ReplayStats) (rule method : String) : ReplayStats :=
  let m := s.byRule.getD rule {}
  { s with byRule := s.byRule.insert rule (m.insert method (m.getD method 0 + 1)) }

def ReplayStats.addTime (s : ReplayStats) (rule : String) (ms : Nat) : ReplayStats :=
  { s with msByRule := s.msByRule.insert rule (s.msByRule.getD rule 0 + ms) }

structure ReplayConfig where
  /-- Experimental certificate-directed arithmetic, enabled explicitly by the driver. -/
  certificates : Bool := false
  /-- Input assertions whose proofs were certified before the solver call. -/
  inputAssertions : Array (Expr × Expr) := #[]
  /-- tactic proving a closed formula directly (used for asserted formulas and as fallback);
      returns `none` when the formula can't be proved. -/
  proveDirect : Expr → TermElabM (Option Expr)
  /-- tactic proving `p₁ → ... → pₙ → c` for a step of the given rule -/
  proveStep : String → Expr → TermElabM (Option (Expr × String))
  /-- the first of the closed goals proved (with the rules of their tactics, see `proveStep`), e.g., attempted in
      parallel -/
  proveSteps? : Option (Array (String × Expr) → TermElabM (Option (Nat × Expr × String))) := none
  /-- proof of a lemma of Z3's theory of recursive functions (`th-lemma recfun`), given the interpretation
      of its clause and its number of literals (see `RecFun.lean`) -/
  proveRecFun : Expr → Nat → TermElabM (Option Expr) := fun _ _ => pure none
  /-- whether the lemmas of recursive functions are only replayed by `proveRecFun` (the generic tactics being
      costly and unlikely to succeed on them) -/
  recFunOnly : Bool := false
  /-- the recursive functions with definitional equations (see `proveRecFun`) -/
  recHeads : NameSet := {}

structure ReplayCtx where
  proof : Proof
  interp : InterpCtx
  cfg : ReplayConfig
  /-- facts available in the current scope (e.g., hypotheses of a `lemma`): proposition and proof -/
  facts : Array (Expr × Expr) := #[]
  /-- nesting depth of scopes (hypotheses, bound variables) -/
  depth : Nat := 0
  /-- time (`IO.monoMsNow`) after which the replay is abandoned -/
  deadline : Nat := 0
  /-- maximal number of direct proof attempts (see `replayCore`) -/
  maxDirect : Nat := 32
  /-- set during `prepass` (no direct proof attempts) -/
  prepass : Bool := false
  /-- steps that don't depend on a scope (see `scopedSteps`): their proofs are valid at depth 0 -/
  global : Array Bool := #[]
  /-- open hypotheses of the steps (see `openHypotheses`) -/
  openHyps : Array (Array Nat) := #[]
  /-- index of the step being replayed (see `replayCore'`) -/
  stepIdx : Nat := 0
  /-- local context at depth 0, in which the steps that don't depend on a scope are replayed -/
  baseLCtx : LocalContext := {}
  baseInsts : LocalInstances := #[]

structure ReplayState where
  /-- proofs of steps replayed at depth 0 -/
  cache : Std.HashMap Nat Expr := {}
  /-- proofs of steps replayed in the current scope -/
  scopeCache : Std.HashMap Nat Expr := {}
  /-- interpretation of the conclusions of steps at depth 0 -/
  conclCache : Std.HashMap Nat Expr := {}
  /-- steps that could not be replayed at depth 0 -/
  failed : Std.HashSet Nat := {}
  /-- steps that could not be replayed in the current scope -/
  scopeFailed : Std.HashSet Nat := {}
  directAttempts : Nat := 0
  /-- time spent in direct proof attempts on large statements (see `replayCore'`) -/
  largeDirectMs : Nat := 0
  stats : ReplayStats := {}
  /-- maximal sharing of the interpreted conclusions: structurally equal terms are pointer equal, such that the
      comparisons of the explicit constructions (e.g., `congrDescent` on large CEK terms) are constant time -/
  share : ShareCommon.State.{0} Lean.ShareCommon.objectFactory := default
  /-- proofs of the global steps, in the order of their replay (premises first), represented in the proofs by the
      metavariables (unassigned, such that no instantiation inlines them, see `liftGlobalProofs`) -/
  globalProofs : Array (MVarId × Expr) := #[]
  /-- the steps of the proofs of `globalProofs` -/
  globalSteps : Array Nat := #[]

abbrev ReplayM := ReaderT ReplayCtx (StateRefT ReplayState TermElabM)

def liftInterp (x : InterpM α) : ReplayM α := do
  let ctx ← read
  x.run ctx.interp

/-- The default of the undetermined type parameters of the interpretation (see `stepConcl`). -/
def defaultTypeParam : ReplayM Expr := do
  let instTy := (← read).interp.table.sorts.toList.find? (·.1.startsWith "@Instance") |>.map (·.2)
  match instTy with
  | some t => do if (← inferType t).isSort then pure t else pure (Lean.mkConst ``Unit)
  | none => pure (Lean.mkConst ``Unit)

/-- Interpretation of the conclusion of step `i`. -/
def stepConcl (i : Nat) : ReplayM Expr := do
  let ctx ← read
  let isGlobal := ctx.depth == 0 || ctx.global.getD i false
  if isGlobal then
    if let some e := (← get).conclCache.get? i then return e
  let step := ctx.proof.steps[i]!
  -- NOTE: the conclusion of `proof-bind` is a lambda over the conclusion of its premise, i.e.,
  -- the premise holds for all values of the bound variables (a new term, kept alive by the memo of the
  -- interpretation, see `TermMemo`)
  let c := match step.rule, step.concl with
    | "proof-bind", .quant .lambda vars body => .quant .forall vars body
    | _, c => c
  let t0 ← IO.monoMsNow
  -- NOTE: the hints of the constructor applications whose instance the conclusion leaves undetermined (see
  -- `SortInfer`) are applied before the defaults
  let e ← instantiateMVars
    (← liftInterp (withSortHints (withReader (fun c => { c with deferTypes := true }) (interpProp c))))
  -- NOTE: undetermined type parameters are most likely the sort variable of a polymorphic goal (e.g., `List.nil`
  -- in a goal on `List α`), and otherwise irrelevant (e.g., `Option.none` under a tester)
  let e ← defaultTypes (← fillDefaults e) (← defaultTypeParam)
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := s.stats.addTime "(interpretation)" (t1 - t0) }
  if e.hasExprMVar then
    -- an application with a metavariable argument (e.g., a constructor of an unknown instance)
    let site := (e.find? fun s => s.isApp && s.getAppArgs.any (·.isMVar)).getD e
    throwError "smt proof: can't infer the types of {site}"
  let e ← modifyGet fun s => let (e, share) := s.share.shareCommon e; (e, { s with share })
  if isGlobal then modify fun s => { s with conclCache := s.conclCache.insert i e }
  return e

/-- Time of a phase of the replay of a step (written to `BLASTER_SMTPROOF_TRACE` when above 100 ms). -/
def timed (phase : String) (x : ReplayM α) : ReplayM α := do
  let start ← IO.monoMsNow
  try x finally
    let ms := (← IO.monoMsNow) - start
    if ms > 100 then
      if let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" then
        let h ← IO.FS.Handle.mk f .append
        h.putStrLn s!"  phase {phase}: {ms} ms"

/-- Run `x`, recording its start and its duration in the file given by `BLASTER_SMTPROOF_TRACE` (if set), e.g., the
    phases of the construction of the final proof. -/
def traceTimed (phase : String) (x : TermElabM α) : TermElabM α := do
  let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" | x
  let log (msg : String) : IO Unit := do
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s!"smtproof: {msg}"
  log phase
  let t0 ← IO.monoMsNow
  let r ← x
  log s!"{phase}: {(← IO.monoMsNow) - t0} ms"
  return r

/-- `traceTimed` for the phases taking at least `minMs` milliseconds, of which only the end is written. -/
def traceSlow (phase : String) (x : TermElabM α) (minMs := 200) : TermElabM α := do
  let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" | x
  let t0 ← IO.monoMsNow
  let r ← x
  let ms := (← IO.monoMsNow) - t0
  if ms ≥ minMs then (← IO.FS.Handle.mk f .append).putStrLn s!"    {phase}: {ms} ms"
  return r

/-- Debugging output (environment variable `BLASTER_SMTPROOF_DEBUG`: file receiving the failures of the steps;
    messages would be discarded with the state restored after a failed replay). -/
def debugLog (msg : MessageData) : MetaM Unit := do
  let some f ← IO.getEnv "BLASTER_SMTPROOF_DEBUG" | return
  let h ← IO.FS.Handle.mk f .append
  h.putStrLn s!"{← msg.toString}"

/-- Printing of a large term with its shared subterms named (`#n`), for debugging: printed as a tree, the terms of
    the interpretation may be exponentially large (e.g., nested selectors of recursive types). -/
partial def dagString (e : Expr) (maxLen := 30000) : MetaM String := do
  -- shared subterms (occurring at least twice, of size at least 2)
  let mut counts : Std.HashMap Expr Nat := {}
  let mut stack := #[e]
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    let n := counts.getD s 0
    counts := counts.insert s (n + 1)
    if n > 0 then continue
    match s with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  let ids ← IO.mkRef ({} : Std.HashMap Expr Nat)
  let defs ← IO.mkRef (#[] : Array String)
  let rec go (s : Expr) : MetaM String := do
    if let some k := (← ids.get).get? s then return s!"#{k}"
    let str ← match s with
      | .app .. =>
          let args ← s.getAppArgs.mapM go
          pure s!"({← go s.getAppFn} {" ".intercalate args.toList})"
      | .lam n t b _ => pure s!"(fun ({n} : {← go t}) => {← go b})"
      | .forallE n t b _ => pure s!"(∀ ({n} : {← go t}), {← go b})"
      | .mdata _ b => go b
      | .proj _ i b => pure s!"{← go b}.{i + 1}"
      | .fvar x => pure (match (← getLCtx).find? x with | some d => toString d.userName | none => s!"?{x.name}")
      | .const n _ => pure (toString n)
      | .bvar i => pure s!"!{i}"
      | s => pure (toString s)
    if counts.getD s 0 > 1 && str.length > 20 then
      let k := (← ids.get).size
      ids.modify (·.insert s k)
      defs.modify (·.push s!"#{k} := {str}")
      return s!"#{k}"
    return str
  let top ← go e
  return ("\n".intercalate ((← defs.get).toList ++ [top])).take maxLen

/-- Debugging: report the subterms of `p` applying free variables that are not in the local context. -/
def reportEscapedFVars (p : Expr) : MetaM Unit := do
  let lctx ← getLCtx
  let bad := (collectFVars {} p).fvarIds.filter (!lctx.contains ·)
  if bad.isEmpty then return
  debugLog m!"escaped free variables: {bad.size} {bad.map (·.name)}"
  let subs := p.find? fun e => e.isApp && (e.getAppFn.isFVar && bad.contains e.getAppFn.fvarId! ||
    e.getAppArgs.any fun a => a.isFVar && bad.contains a.fvarId!)
  if let some e := subs then debugLog m!"escaped in:\n{← dagString e 4000}"
  -- the enclosing lambda (its binder types hint at the construction)
  let lam? := p.find? fun e => e.isLambda && (e.bindingBody!.find? fun s => s.isFVar && bad.contains s.fvarId!).isSome &&
    !(e.bindingBody!.find? (·.isLambda)).isSome
  if let some e := lam? then debugLog m!"innermost lambda:\n{← dagString e 4000}"

def record (rule method : String) : ReplayM Unit :=
  modify fun s => { s with stats := s.stats.record rule method }

def orArgs? (e : Expr) : Option (Expr × Expr) := e.app2? ``Or

/-- `fun (h : t) => k h`, abstracting `h` syntactically: unlike `mkLambdaFVars`, the metavariables of the body
    are not instantiated, such that the cost does not depend on the size of the proofs they stand for
    (see `replay`). The body must not contain metavariables depending on `h`. -/
def withLam {m : Type → Type} [Monad m] [MonadControlT MetaM m] (n : Name) (t : Expr) (k : Expr → m Expr) : m Expr :=
  withLocalDeclD n t fun h => do
    let b ← k h
    return mkLambda n .default t (b.abstract #[h])

/-- Decompose a right-nested disjunction `l₁ ∨ (l₂ ∨ ... ∨ lₙ)` into its literals, given the
    expected number of literals `n`. -/
def disjuncts (e : Expr) (n : Nat) : Array Expr := Id.run do
  let mut r := #[]
  let mut cur := e
  for _ in [0:n-1] do
    match orArgs? cur with
    | some (a, b) => r := r.push a; cur := b
    | none => break
  r.push cur

/-- Number of literals of a clause conclusion `(or l₁ ... lₙ)` (`false` has none). -/
def clauseSize (t : STerm) : Nat :=
  match t.stripAnnot with
  | .app "or" args => args.size
  | .sym "false" => 0
  | _ => 1

/-- Number of literals of the conclusion of `s` (explicit clause literals take precedence). -/
def Step.clauseSize (s : Step) : Nat :=
  match s.clause? with
  | some lits => lits.size
  | none => SmtProof.clauseSize s.concl

/-- Syntactic equality of propositions (up to instantiation of metavariables). -/
def propEq (a b : Expr) (deep := false) : MetaM Bool := do
  if a == b then return true
  if ← withReducible <| isDefEq a b then return true
  -- e.g., `Int.toNat (↑n)` and `n`
  if deep then withDefault <| isDefEq a b else return false

/-- The suffixes `lⱼ ∨ (lⱼ₊₁ ∨ ... ∨ lₙ₋₁)` of the right-nested disjunction of `lits`, built once (and shared) for the
    injections into the disjunction (see `mkOrInjWith`). -/
def orSuffixes (lits : Array Expr) : Array Expr := Id.run do
  let n := lits.size
  if n == 0 then return #[]
  let mut sfx := Array.replicate n lits[n-1]!
  for k in (List.range (n - 1)).reverse do
    sfx := sfx.set! k (mkOr lits[k]! sfx[k+1]!)
  return sfx

/-- Proof of the `i`-th injection into the right-nested disjunction `lits`, given its suffixes `sfx` (see
    `orSuffixes`): `Or.inr^i (Or.inl p)` (`Or.inr^i p` for the last literal). -/
def mkOrInjWith (lits sfx : Array Expr) (i : Nat) (p : Expr) : Expr := Id.run do
  let n := lits.size
  if n == 1 then return p
  let mut proof := if i == n - 1 then p else mkApp3 (Lean.mkConst ``Or.inl) lits[i]! sfx[i+1]! p
  let mut j := i
  while j > 0 do
    j := j - 1
    proof := mkApp3 (Lean.mkConst ``Or.inr) lits[j]! sfx[j+1]! proof
  return proof

/-- Proof of the `i`-th injection into the right-nested disjunction `lits` (of size `n`). -/
def mkOrInj (lits : Array Expr) (i : Nat) (p : Expr) : MetaM Expr :=
  return mkOrInjWith lits (orSuffixes lits) i p

/-- Case analysis on a proof `d` of the disjunction of `lits`: `k i hᵢ δ` builds a proof of `goal` from a proof `hᵢ` of
    the `i`-th literal, under `δ` binders of the case analysis (by which the loose bound variables of the terms it
    places must be lifted, e.g., the premises of a step as bound variables, see `replayRule`). The cases are built under
    their binders without abstraction, i.e., without traversing the literals again at each case (quadratic on the large
    clauses of CEK evaluations, a third of their replays). -/
partial def orElim (lits : Array Expr) (d : Expr) (goal : Expr) (k : Nat → Expr → Nat → MetaM Expr) : MetaM Expr := do
  -- empty clause: `d : False`
  if lits.isEmpty then return mkApp2 (Lean.mkConst ``False.elim [← getLevel goal]) goal d
  let sfx := orSuffixes lits
  let n := lits.size
  -- the case analysis of the suffix `i` on its proof `d` (under `δ` binders)
  let rec go (i : Nat) (d : Expr) (δ : Nat) : MetaM Expr := do
    if i + 1 ≥ n then return ← k i d δ
    let left := Expr.lam `h lits[i]! (← k i (.bvar 0) (δ + 1)) .default
    let right := Expr.lam `h sfx[i+1]! (← go (i + 1) (.bvar 0) (δ + 1)) .default
    return mkApp6 (Lean.mkConst ``Or.elim) lits[i]! sfx[i+1]! goal d left right
  go 0 d 0

/-- Given a proof `d` of a clause with literals `lits`, refutations of some literals and the target
    clause `target`, build a proof of `target` (each literal is either refuted or occurs in `target`). -/
def weakenClause (lits : Array Expr) (d : Expr) (refute : Expr → MetaM (Option Expr)) (targetLits : Array Expr) : MetaM Expr := do
  let sfx := orSuffixes targetLits
  let target := sfx[0]?.getD (Lean.mkConst ``False)
  orElim lits d target fun i h δ => do
    let l := lits[i]!
    -- NOTE: syntactic matches first (the definitional ones are costly on large literals)
    for j in [:targetLits.size] do
      if targetLits[j]! == l then return mkOrInjWith targetLits sfx j h
    if let some r ← refute l then
      return mkApp2 (Lean.mkConst ``False.elim [levelZero]) target (mkApp (r.liftLooseBVars 0 δ) h)
    for j in [:targetLits.size] do
      if ← propEq targetLits[j]! l then return mkOrInjWith targetLits sfx j h
    throwError "smt proof: literal {l} is neither refuted nor in the conclusion"

/-- Proof built by `k` from the premises `ps` (propositions and proofs), given local hypotheses standing for the
    proofs of the premises: the construction does not traverse these proofs (e.g., the large proofs of the steps
    replayed in a scope, which are not shared through metavariables, see `replay`). -/
def withPremiseVars (ps : Array (Expr × Expr)) (k : Array (Expr × Expr) → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (hs : Array Expr) : MetaM Expr := do
    if h : i < ps.size then
      withLocalDeclD (Name.mkSimple s!"p{i}") ps[i].1 fun x => go (i + 1) (hs.push x)
    else
      let body ← k ((ps.zip hs).map fun ((t, _), x) => (t, x))
      return mkAppN (← mkLambdaFVars hs body) (ps.map (·.2))
  go 0 #[]

/-- Refutation of `l` by one of the unit proofs: `u : ¬ l` or `u : a` with `l = ¬ a` (the proofs may be loose bound
    variables, e.g., the premises of a step, see `replayRule`). -/
def refuteBy (units : Array (Expr × Expr)) (l : Expr) : MetaM (Option Expr) := do
  let neg (u : Expr) : Expr := .lam `h l (mkApp (.bvar 0) (u.liftLooseBVars 0 1)) .default
  -- NOTE: syntactic matches first (the definitional ones are costly on large literals)
  for (t, u) in units do
    if let some a := t.not? then
      if a == l then return some u
    if let some a := l.not? then
      if a == t then return some (neg u)
  for (t, u) in units do
    if let some a := t.not? then
      if ← propEq a l then return some u
    if let some a := l.not? then
      if ← propEq a t then return some (neg u)
  return none

/-- Propositional replay by unit propagation (RUP): given clauses (literals and proofs of their
    disjunction), prove the disjunction of `target` literals. The negation of the target is assumed,
    and unit propagation on the clauses must derive a conflict. This justifies resolution steps
    (e.g., Alethe's `resolution`, Z3's `unit-resolution`) independently of pivot annotations. -/
partial def rupProof (clauses : Array (Array Expr × Expr)) (target : Array Expr) : MetaM Expr := do
  let sfx := orSuffixes target
  let goal := sfx[0]?.getD (Lean.mkConst ``False)
  let r ← withLam `hn (mkNot goal) fun hn => do
    -- refuted propositions ↦ proof of their negation (refutations are computed once, when facts are added)
    let mut falses : Std.HashMap Expr Expr := {}
    let mut trues : Std.HashSet Expr := {}
    for k in [:target.size] do
      let l := target[k]!
      let nl ← withLam `h l fun h => return mkApp hn (mkOrInjWith target sfx k h)
      falses := falses.insert l nl
    let mut used := Array.replicate clauses.size false
    let mut changed := true
    let mut conflict : Option Expr := none
    while changed && conflict.isNone do
      changed := false
      for ci in [:clauses.size] do
        if used[ci]! then continue
        let (lits, pc) := clauses[ci]!
        let mut unknown : Option Nat := none
        let mut nbUnknown := 0
        for i in [:lits.size] do
          if !falses.contains lits[i]! then
            nbUnknown := nbUnknown + 1
            unknown := some i
            if nbUnknown > 1 then break
        if nbUnknown == 0 then
          -- conflict: all literals are refuted
          -- NOTE: the proofs of the facts have no loose bound variables (see `orElim`)
          conflict := some (← orElim lits pc (Lean.mkConst ``False) fun i h _ => return mkApp falses[lits[i]!]! h)
          break
        if nbUnknown == 1 then
          let some k := unknown | continue
          let l := lits[k]!
          used := used.set! ci true
          if trues.contains l then continue
          let p ← orElim lits pc l fun i h _ => do
            if i == k then return h
            return mkApp2 (Lean.mkConst ``False.elim [levelZero]) l (mkApp falses[lits[i]!]! h)
          trues := trues.insert l
          -- `l` refutes `¬ l`, and `l = ¬ a` refutes `a`
          let nl := mkNot l
          if !falses.contains nl then
            falses := falses.insert nl (← withLam `h nl fun h => return mkApp h p)
          if let some a := l.not? then
            if !falses.contains a then falses := falses.insert a p
          changed := true
    let some pf := conflict | throwError "smt proof: unit propagation did not derive a conflict"
    return pf
  return mkApp2 (Lean.mkConst ``Classical.byContradiction) goal r

/-- Whether the step `s` (`lemma` or `subproof`) discharges the hypothesis of step `h`: a Z3 `lemma` discharges the
    hypotheses whose negation is one of its literals (matched on shared term objects, then structurally), an Alethe
    `subproof` the assumptions it lists. -/
def discharges (p : Proof) (s : Step) (h : Nat) : Bool :=
  if s.rule == "subproof" then s.discharged.contains h
  else if s.rule == "lemma" then
    let lits := match s.concl.stripAnnot with
      | .app "or" ls => ls
      | l => #[l]
    let negated : Array USize := lits.filterMap fun l => (STerm.not? l).map termAddr
    let plain : Array USize := lits.map fun l => termAddr l.stripAnnot
    let φ := p.steps[h]!.concl
    -- discharged: `¬ φ` is a literal, or `φ = ¬ a` and `a` is a literal
    negated.contains (termAddr φ) || negated.contains (termAddr φ.stripAnnot) ||
      ((STerm.not? φ).map (fun a => plain.contains (termAddr a.stripAnnot))).getD false ||
      -- NOTE: the same terms may be printed as different objects (e.g., small terms not shared by `let`)
      lits.any fun l =>
        ((STerm.not? l).map (fun a => STerm.eqBounded a φ.stripAnnot)).getD false ||
        ((STerm.not? φ).map (fun a => STerm.eqBounded a.stripAnnot l.stripAnnot)).getD false
  else false

/-- Open hypotheses of each step (indices of `hypothesis` steps not discharged, see `discharges`). -/
def openHypotheses (p : Proof) : Array (Array Nat) := Id.run do
  let n := p.steps.size
  let mut hyps : Array (Array Nat) := Array.replicate n #[]
  for i in [:n] do
    let s := p.steps[i]!
    if s.rule == "hypothesis" then hyps := hyps.set! i #[i]
    else
      let mut hs : Array Nat := #[]
      for j in s.premises do
        for h in hyps[j]! do
          if !hs.contains h then hs := hs.push h
      if s.rule == "subproof" || s.rule == "lemma" then hs := hs.filter (!discharges p s ·)
      hyps := hyps.set! i hs
  return hyps

/-- Run `x` in a new scope (hypotheses or bound variables): the proofs (and failures) of the
    current scope are saved and restored, also when `x` fails. -/
def withScope (x : ReplayM α) (inherit := false) (keep : Nat → Expr → Bool := fun _ _ => false) : ReplayM α := do
  let saved := ((← get).scopeCache, (← get).scopeFailed)
  -- NOTE: with `inherit`, the proofs of the current scope stay available in the new scope (e.g., for the hypotheses
  -- of nested lemmas, which extend the context of the enclosing ones), and the new proofs satisfying `keep` (e.g., not
  -- using the hypothesis of a nested lemma) are kept, such that the steps shared by the subproofs of nested lemmas are
  -- not replayed in each of them
  modify fun s => { s with scopeCache := if inherit then s.scopeCache else {}, scopeFailed := {} }
  try x finally
    modify fun s =>
      let inner := if inherit then
          s.scopeCache.fold (fun m i p => if saved.1.contains i || !keep i p then m else m.insert i p) saved.1
        else saved.1
      { s with scopeCache := inner, scopeFailed := saved.2 }

/-- Definitional equality with a heartbeat budget (default transparency when `unfold`, reducible otherwise). -/
def defeqBudget (a b : Expr) (budget : Nat) (unfold : Bool) : MetaM Bool := do
  return (← Local.withBudget? budget ((if unfold then withDefault else withReducible) <| isDefEq a b)).getD false

/-- Rules whose steps are propositional reasoning on their atoms. -/
def propositionalRules : Array String :=
  #["def-axiom", "not-or-elim", "and-elim", "iff~", "nnf-pos", "nnf-neg", "rewrite", "unit-resolution"]

/-- Proof of `stmt := p₁ → ... → pₙ → c` by the propositional engine, with the propositional atoms generalized. -/
def propOnAtoms (stmt : Expr) : MetaM (Option Expr) := do
  let some (g, vals) ← Local.generalizePropAtoms stmt | return none
  forallTelescope g fun zs body => do
    -- the premises as hypotheses
    let r ← forallTelescope body fun hs c => do
      let hyps ← hs.mapM fun h => do return (← inferType h, h)
      match ← PropEngine.prove hyps c with
      | some p => some <$> mkLambdaFVars hs p
      | none => pure none
    match r with
    | some p => return some (mkAppN (← mkLambdaFVars zs p) vals)
    | none => return none

/-- The free variables of `e` and, transitively, of their types and values, in the order of the local context. -/
def usedFVars (e : Expr) : MetaM (Array Expr) := do
  let mut todo := (collectFVars {} e).fvarIds
  let mut seen : FVarIdSet := {}
  let mut decls := #[]
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if seen.contains f then continue
    seen := seen.insert f
    let d ← f.getDecl
    decls := decls.push d
    let s := collectFVars {} d.type
    let s := match d.value? with | some v => collectFVars s v | none => s
    todo := todo ++ s.fvarIds
  return (decls.qsort (·.index < ·.index)).map (·.toExpr)

/-- Debugging output (environment variable `BLASTER_SMTPROOF_GOALDUMP`: file receiving the closed statements on
    which the step tactics failed, as Lean `example`s). -/
def dumpGoal (g : Expr) : MetaM Unit := do
  let some f ← IO.getEnv "BLASTER_SMTPROOF_GOALDUMP" | return
  let s ← withOptions (fun o => o.setBool `pp.numericTypes true |>.setBool `pp.coercions.types true
      |>.setBool `pp.fieldNotation false |>.setNat `pp.maxSteps 100000000 |>.setBool `pp.deepTerms true) do
    return toString (← ppExpr g)
  let h ← IO.FS.Handle.mk f .append
  h.putStrLn s!"example : {s} := by\n  blaster_nlarith\n"

/-- Tactics on a statement, closed over the free variables it uses and proved in the empty local context:
    a step is valid by itself (its premises are hypotheses of the statement), and the hypotheses of the
    context (e.g., the negated goal) would only slow down the tactics (e.g., `simp_all` on the negated goal,
    case analyses splitting the variables of the goal). -/
def proveClosed (cfg : ReplayConfig) (rule : String) (g : Expr) : TermElabM (Option (Expr × String)) := do
  if !g.hasFVar then
    let r ← withLCtx {} {} (cfg.proveStep rule g)
    if r.isNone then dumpGoal g
    return r
  let fvs ← usedFVars g
  let g' ← mkForallFVars fvs g
  if g'.hasFVar then return ← cfg.proveStep rule g
  let some (pf, m) ← withLCtx {} {} (cfg.proveStep rule g') | dumpGoal g'; return none
  -- NOTE: let-bound variables are abstracted as `let`s (not applied)
  let args ← fvs.filterM fun x => return !(← x.fvarId!.getDecl).isLet
  return some (mkAppN pf args, m)

/-- The first of the goals `gs` (with the rules of their tactics) proved by `proveClosed`, with its index (attempted in
    parallel with `cfg.proveSteps?` when the goals are closed). -/
def proveClosedFirst (cfg : ReplayConfig) (gs : Array (String × Expr)) : TermElabM (Option (Nat × Expr × String)) := do
  if let some proveSteps := cfg.proveSteps? then
    if gs.size > 1 && gs.all fun (_, g) => !g.hasFVar && !g.hasMVar then
      return ← withLCtx {} {} (proveSteps gs)
  for (rule, g) in gs, i in [0:gs.size] do
    if let some (p, m) ← proveClosed cfg rule g then return some (i, p, m)
  return none

/-- Debugging: the goals proved by tactics in at least 200 ms, with the method (environment variable
    `BLASTER_SMTPROOF_SLOWGOALS`: file receiving them). -/
def slowGoal (g : Expr) (what : String) (x : TermElabM (Option (Expr × String))) :
    TermElabM (Option (Expr × String)) := do
  let some f ← IO.getEnv "BLASTER_SMTPROOF_SLOWGOALS" | x
  let t0 ← IO.monoMsNow
  let r ← x
  let ms := (← IO.monoMsNow) - t0
  if ms ≥ 200 then
    let s ← if Local.sizeLe g 5000 then pure (toString (← ppExpr g)) else dagString g
    (← IO.FS.Handle.mk f .append).putStrLn s!"=== {what} ({(r.map (·.2)).getD "failed"}): {ms} ms\n{s.take 8000}\n"
  return r

/-- The results of the tactics on the closed generalizations of the local differences (see `localProof`), per rule:
    the same generalization over other subterms (e.g., in the steps of a CEK evaluation, a third of the
    generalizations) is proved (or not) once. Cleared at the start of each replay (see `clearLocalCache`). -/
initialize localCache : IO.Ref (Std.HashMap (String × Expr) (Option (Expr × String))) ← IO.mkRef {}

def clearLocalCache : IO Unit := localCache.set {}

/-- `x`, the tactics on the closed generalization `g` of a local difference within the time budget `budget?` (if any),
    with its result cached (see `localCache`).
    NOTE: failures due to the time budget are not cached (e.g., an attempt of a prepass under load), nor proofs using
    declarations of the current module (e.g., auxiliary lemmas of tactics, which a backtracking may remove from the
    environment). -/
def cachedLocal (rule : String) (g : Expr) (budget? : Option Nat) (x : TermElabM (Option (Expr × String))) :
    TermElabM (Option (Expr × String)) := do
  if g.hasFVar || g.hasMVar then return ← x
  if let some r := (← localCache.get)[(rule, g)]? then return r
  let start ← IO.monoMsNow
  let r ← x
  if r.isNone && budget?.any ((← IO.monoMsNow) - start ≥ ·) then return r
  let env ← getEnv
  let local? := r.any fun (p, _) => (p.find? fun e => match e with
    | .const n _ => (env.getModuleIdxFor? n).isNone
    | _ => false).isSome
  if !local? then localCache.modify (·.insert (rule, g) r)
  return r

/-- Proof of a local difference `∀ hs, l = r` of a step (see `Local.diffEq`, `hs` are hypotheses of the
    context of the difference): definitional equality, then the propositional engine and tactics on the
    statement with the subterms common to `l` and `r` generalized. -/
def localProof (cfg : ReplayConfig) (rule : String) (largeStep : Bool) (eq : Expr) : TermElabM (Option Expr) := do
  -- NOTE: the tactics on the local differences of large terms are bounded in time (environment variable
  -- `BLASTER_SMTPROOF_LOCAL_MS`, default 1000 ms, and half of it for the lossless generalization; a tactic running past
  -- the deadline is interrupted), with `largeStep` (the differences of large steps): on the CEK terms of validators,
  -- the differences proved take at most a few hundred ms (about 80 ms for the lossless ones), while the ones not proved
  -- (e.g., Z3's normal forms of nested integer divisions, whose step is then proved otherwise) took up to 17 s each.
  -- The other differences of large terms are only bounded against runaway attempts, at 120 times the budget (e.g., the
  -- polynomial normal forms of the steps of nonlinear goals are proved after more than 10 s, while a difference of the
  -- same tests did not terminate), and the ones of small terms are not bounded.
  if Local.sizeLe eq 2000 then return ← localProofCore cfg rule eq none
  let budget := ((← IO.getEnv "BLASTER_SMTPROOF_LOCAL_MS").bind String.toNat?).getD 1000
  let budget := if largeStep then budget else 120 * budget
  localProofCore cfg rule eq (some (budget, budget / 2))
where
  /-- the tactics on the local difference, with the time budgets of the two generalizations (if any) -/
  bounded {α : Type} (b : Option Nat) (x : TermElabM α) : TermElabM α :=
    match b with
    | some ms => Local.withPortfolioDeadline ms x
    | none => x
  localProofCore (cfg : ReplayConfig) (rule : String) (eq : Expr) (budgets : Option (Nat × Nat)) :
      TermElabM (Option Expr) := do
  -- NOTE: `l` and `r` don't depend on the hypotheses
  let some (l, r) ← forallTelescope eq fun _ body => pure (body.eq?.map fun (_, l, r) => (l, r)) | return none
  if l.hasLooseBVars || r.hasLooseBVars then return none
  -- definitional differences (e.g., testers of constructor applications)
  let small := Local.sizeLe eq 2000
  if ← defeqBudget l r 5000 small then
    return some (← forallTelescope eq fun hs body => do
      mkLambdaFVars hs (← mkExpectedTypeHint (← mkEqRefl l) body))
  let t0 ← IO.monoMsNow
  let some (g, vals) ← Local.generalizeCommon eq l r
    | if small then return (← proveClosed cfg rule eq).map (·.1) else return none
  let t1 ← IO.monoMsNow
  -- propositional differences (e.g., associativity of connectives, `ite` on propositions): exact proof
  let pp? ← forallTelescope g fun zs body => do
    let some (ty, _, _) := body.eq? | return none
    if !ty.isProp then return none
    match ← PropEngine.prove #[] body with
    | some p => some <$> mkLambdaFVars zs p
    | none => pure none
  if let some pp := pp? then return some (mkAppN pp vals)
  -- NOTE: no tactic on a generalization refuted by its small instances (e.g., the common subterms of the two sides
  -- generalized as the same variable, while their relations make the difference hold), checked on cache misses only
  let mut res ← cachedLocal rule g (budgets.map (·.1)) do
    if ← Local.refuted g then return none
    bounded (budgets.map (·.1)) (slowGoal g "local" (proveClosed cfg rule g))
  let t2 ← IO.monoMsNow
  -- the generalization without loss of the relations between the generalized subterms (see `Local.commonSubterms`)
  let mut vals := vals
  let mut lossless := ""
  -- NOTE: not when the tactics ran out of time on the generalization (on CEK evaluations, the lossless generalization
  -- of such a difference was never proved, e.g., normal forms of nested divisions, while it cost half the budget again)
  let timedOut := budgets.any fun (b, _) => t2 - t1 ≥ b
  if res.isNone && !timedOut then
    if let some (g', vals') ← Local.generalizeCommon eq l r (lossless := true) then
      if g' != g then
        let t3 ← IO.monoMsNow
        res ← cachedLocal rule g' (budgets.map (·.2)) do
          if ← Local.refuted g' then return none
          bounded (budgets.map (·.2)) (proveClosed cfg rule g')
        vals := vals'
        lossless := s!", lossless: generalization {t3 - t2} ms, tactics {(← IO.monoMsNow) - t3} ms"
        if (← IO.getEnv "BLASTER_SMTPROOF_TRACE").isSome && res.isNone then
          lossless := lossless ++ s!" (lossless statement: {(toString (← ppExpr g')).take 1500})"
  if res.isNone && (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
    debugLog m!"local difference not proved:\n{← dagString eq 8000}"
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" then
    let t4 ← IO.monoMsNow
    if t4 - t0 > 100 then
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn s!"    local difference: generalization {t1 - t0} ms, tactics {t2 - t1} ms{lossless}, total {t4 - t0} ms ({res.map (·.2)}): {(toString (← ppExpr g)).take 1500}"
  return res.map fun (pf, _) => mkAppN pf vals

/-- `quant-intro` (Z3): from `h : ∀ xs, a xs = b xs` (resp. `∀ xs, a xs → b xs`), a proof of
    `(∀ xs, a xs) = (∀ xs, b xs)` (resp. `(∀ xs, a xs) → (∀ xs, b xs)`), when `concl` has this form. -/
partial def quantIntro (t h concl : Expr) : MetaM (Option Expr) := do
  match t, concl with
  -- equality: `forall_congr` under each binder
  | .forallE n ty body bi, _ =>
      if let some (_, .forallE _ ty₁ b₁ _, .forallE _ ty₂ b₂ _) := concl.eq? then
        if ty == ty₁ && ty == ty₂ then
          return ← withLocalDecl n bi ty fun x => do
            let inner := mkApp h x
            let innerTy := body.instantiate1 x
            let concl' ← mkEq (b₁.instantiate1 x) (b₂.instantiate1 x)
            -- deeper binders, or the equality itself
            let some p ← (if innerTy.isForall then quantIntro innerTy inner concl'
                          else do if ← isDefEq innerTy concl' then pure (some inner) else pure none) | return none
            return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] p])
      -- implication (`~` is interpreted as `→`)
      if let .forallE _ (.forallE _ ty₁ b₁ _) (.forallE _ ty₂ _ _) _ := concl then
        if ty == ty₁ && ty == ty₂ then
          return ← withLocalDeclD `h₁ (.forallE n ty₁ b₁ bi) fun h₁ => do
            let r ← withLocalDecl n bi ty fun x => do
              let p := mkApp h x
              let a := mkApp h₁ x
              let pt ← whnfR (← inferType p)
              if pt.isArrow then return some (← mkLambdaFVars #[x] (mkApp p a))
              -- `a x = b x`
              if let some _ := pt.eq? then return some (← mkLambdaFVars #[x] (← mkEqMP p a))
              return none
            match r with
            | some f => return some (← mkLambdaFVars #[h₁] f)
            | none => return none
      return none
  | _, _ => return none

/-- `l₀ ∨ (l₁ ∨ ... ∨ lₙ)` from a proof `p` of `lᵢ`. -/
def orIntro (ls : Array Expr) (i : Nat) (p : Expr) : Expr :=
  go 0
where
  go (j : Nat) : Expr :=
    if j + 1 ≥ ls.size then p else
    let rest := (ls.extract (j + 1) ls.size).pop.foldr mkOr ls.back!
    if i == j then mkApp3 (mkConst ``Or.inl) ls[j]! rest p
    else mkApp3 (mkConst ``Or.inr) ls[j]! rest (go (j + 1))
  termination_by ls.size - j

/-- Proof of the literal `l` by evaluation: `True`, `¬ False` and `a = a` up to definitional unfolding (e.g., the
    testers and selectors of the interpretation applied to constructors, reduced by `casesOn`). -/
def evalLit? (l : Expr) : MetaM (Option Expr) := do
  let defeq (a b : Expr) : MetaM Bool := do return (← Local.withBudget? 5000 (withDefault <| isDefEq a b)).getD false
  if let some a := l.not? then
    if (← whnfD a).isConstOf ``False then return some (← mkExpectedTypeHint (mkLambda `h .default a (.bvar 0)) l)
    return none
  if let some (_, a, b) := l.eq? then
    if ← defeq a b then return some (← mkExpectedTypeHint (← mkEqRefl a) l)
    return none
  if (← whnfD l).isConstOf ``True then return some (← mkExpectedTypeHint (mkConst ``True.intro) l)
  return none

/-- Datatype lemmas by case analysis on a term `x` of a datatype, e.g., `x = C (C.0 x) ∨ ¬ is-C x` where the tester
    and the selectors are interpreted by `casesOn` on `x` (see `mkTester`): `T.casesOn x`, with, for each
    constructor, a literal of the clause `lits` that holds by evaluation (see `evalLit?`). The candidates for
    `x` are the major premises of the testers. -/
def caseLemma? (concl : Expr) (lits : Array Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let isTester (e : Expr) : Option Expr := Id.run do
    let .const n _ := e.getAppFn | return none
    if !isCasesOnRecursor env n then return none
    let some (.inductInfo info) := env.find? n.getPrefix | return none
    let args := e.getAppArgs
    if info.numIndices != 0 || args.size != info.numParams + 2 + info.ctors.length then return none
    let .lam _ _ (.sort .zero) _ := args[info.numParams]! | return none
    return some args[info.numParams + 1]!
  let mut cands : Array Expr := #[]
  for l in lits do
    for x in collectTesters isTester l #[] 64 do
      if !x.hasLooseBVars && !cands.contains x then cands := cands.push x
  for x in cands do
    if let some p ← caseOn? x then return some p
  return none
where
  /-- Major premises of the testers in `e` (bounded depth). -/
  collectTesters (isTester : Expr → Option Expr) (e : Expr) (acc : Array Expr) (fuel : Nat) : Array Expr :=
    if fuel == 0 then acc else
    let acc := match isTester e with | some x => acc.push x | none => acc
    match e with
    | .app f a => collectTesters isTester a (collectTesters isTester f acc (fuel - 1)) (fuel - 1)
    | .lam _ t b _ | .forallE _ t b _ => collectTesters isTester b (collectTesters isTester t acc (fuel - 1)) (fuel - 1)
    | .mdata _ b | .proj _ _ b => collectTesters isTester b acc (fuel - 1)
    | _ => acc
  caseOn? (x : Expr) : MetaM (Option Expr) := do
    let xt ← whnfD (← inferType x)
    let .const T lvls := xt.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? T | return none
    if info.numIndices != 0 then return none
    let some casesOn := (← getEnv).find? (T ++ `casesOn) | return none
    if casesOn.levelParams.length != lvls.length + 1 then return none
    let params := xt.getAppArgs.extract 0 info.numParams
    let absLits ← lits.mapM fun l => kabstract l x
    let absConcl ← kabstract concl x
    if !absConcl.hasLooseBVars then return none
    let mut minors := #[]
    for c in info.ctors do
      let ci ← getConstInfo c
      let some minor ← forallTelescopeReducing (← instantiateForall (ci.instantiateTypeLevelParams lvls) params) fun fs _ => do
          let v := mkAppN (mkConst c lvls) (params ++ fs)
          let ls := absLits.map (·.instantiate1 v)
          for i in [:ls.size] do
            if let some p ← evalLit? ls[i]! then
              return some (← mkLambdaFVars fs (← mkExpectedTypeHint (orIntro ls i p) (absConcl.instantiate1 v)))
          return none
        | return none
      minors := minors.push minor
    let motive := mkLambda `z .default xt absConcl
    let pf := mkAppN (mkConst (T ++ `casesOn) (levelZero :: lvls)) (params ++ #[motive, x] ++ minors)
    return some (← mkExpectedTypeHint pf concl)

/-- `f as = f bs` from the proofs `diffs` of `asᵢ = bsᵢ` for the arguments that differ: congruence on the partial
    applications `f as[0..i)` when their types are not dependent, and otherwise on the full applications
    `fun z => f bs[0..i) z as(i..n]` when only the type of the application depends on `z` and it reduces to a type
    not depending on `z` (e.g., the major premise of a `casesOn` with a constant motive). -/
def congrArgs (f : Expr) (as bs : Array Expr) (diffs : Array (Nat × Expr)) : MetaM (Option Expr) := do
  let partialApps : MetaM (Option Expr) := do
    let mut pf ← mkEqRefl f
    let mut cur := f
    let mut changed := false
    let mut k := 0
    for i in [:as.size] do
      if k < diffs.size && diffs[k]!.1 == i then
        let pi := diffs[k]!.2
        k := k + 1
        if !(← whnfR (← inferType cur)).isArrow then return none
        pf ← if changed then mkCongr pf pi else mkCongrArg cur pi
        cur := mkApp cur bs[i]!
        changed := true
      else
        pf ← if changed then mkCongrFun pf as[i]! else pure pf
        cur := mkApp cur as[i]!
        if !changed then pf ← mkEqRefl cur
    return some pf
  if let some pf ← partialApps then return some pf
  let info ← getFunInfoNArgs f as.size
  let mut pf ← mkEqRefl (mkAppN f as)
  let mut cur := as
  for (i, pi) in diffs do
    if (info.paramInfo.extract (i + 1) info.paramInfo.size).any (·.backDeps.contains i) then return none
    let ctx ← withLocalDeclD `z (← inferType as[i]!) fun z => mkLambdaFVars #[z] (mkAppN f (cur.set! i z))
    let .forallE _ _ body _ ← whnfR (← inferType ctx) | return none
    if body.hasLooseBVars then return none
    pf ← mkEqTrans pf (← mkCongrArg ctx pi)
    cur := cur.set! i bs[i]!
  return some pf


/-- Implementation of `dagStats`: the cache is keyed by the addresses of the subterms (the structural equality of large
    terms is costly). -/
unsafe def dagStatsImpl (e : Expr) : Nat × Nat :=
  let (d, s) := (go e).run {}
  (s.size, d)
where
  go (e : Expr) : StateM (Std.HashMap USize Nat) Nat := do
    if let some d := (← get).get? (ptrAddrUnsafe e) then return d
    let d ← match e with
      | .app f a => pure (max (← go f) (← go a))
      | .lam _ t b _ | .forallE _ t b _ => pure (max (← go t) ((← go b) + 1))
      | .letE _ t v b _ => pure (max (max (← go t) (← go v)) ((← go b) + 1))
      | .mdata _ b | .proj _ _ b => go b
      | _ => pure 0
    modify (·.insert (ptrAddrUnsafe e) d)
    return d

/-- Number of distinct subterms (pointers) of `e` and maximal nesting of binders in `e` (e.g., for the trace of a
    large proof). -/
@[implemented_by dagStatsImpl] opaque dagStats (e : Expr) : Nat × Nat

/-- Number of bits set in `n`. -/
partial def popCount (n : Nat) (acc : Nat := 0) : Nat :=
  if n == 0 then acc else
    let w : UInt64 := n.toUInt64
    let w : UInt64 := w - ((w >>> 1) &&& (0x5555555555555555 : UInt64))
    let w : UInt64 := (w &&& (0x3333333333333333 : UInt64)) + ((w >>> 2) &&& (0x3333333333333333 : UInt64))
    let w : UInt64 := (w + (w >>> 4)) &&& (0x0f0f0f0f0f0f0f0f : UInt64)
    let w : UInt64 := (w * (0x0101010101010101 : UInt64)) >>> 56
    popCount (n >>> 64) (acc + w.toNat)

/-- Implementation of `instantiationStats`. -/
unsafe def instantiationStatsImpl (e : Expr) : Nat × Nat × Array Nat :=
  let (_, (_, total, hist)) := (go e).run ({}, 0, Array.replicate 12 0)
  (hist.foldl (· + ·) 0, total, hist)
where
  -- NOTE: the closed subterms are traversed too (e.g., the closed lambda terms of `liftGlobalProofs`)
  go (e : Expr) : StateM (Std.HashMap USize Nat × Nat × Array Nat) Nat := do
    if let some s := (← get).1.get? (ptrAddrUnsafe e) then return s
    let s ← match e with
      | .bvar i => pure (1 <<< i)
      | .app f a => pure ((← go f) ||| (← go a))
      | .lam _ t b _ | .forallE _ t b _ => pure ((← go t) ||| ((← go b) >>> 1))
      | .letE _ t v b _ => pure ((← go t) ||| (← go v) ||| ((← go b) >>> 1))
      | .mdata _ b | .proj _ _ b => go b
      | _ => pure 0
    let k := popCount s
    modify fun (m, total, hist) =>
      (m.insert (ptrAddrUnsafe e) s, total + k, if k == 0 then hist else hist.modify (min (Nat.log2 k) 11) (· + 1))
    return s

/-- Cost of the instantiations of the binders of `e` by the kernel (e.g., in `infer_lambda`), which rebuild the subterms
    referring to the instantiated binder: the number of distinct subterms with loose bound variables, the sum over them
    of the number of distinct binders they refer to (the number of copies of the subterms built by the instantiations),
    and the histogram of these numbers (bucket `k`: from `2^k` to `2^(k+1) - 1` binders). -/
@[implemented_by instantiationStatsImpl] opaque instantiationStats (e : Expr) : Nat × Nat × Array Nat

/-- Implementation of `abstractFVar`: the caches are keyed by the addresses of the subterms (the structural equality of
    large terms is costly). -/
unsafe def abstractFVarImpl (e : Expr) (x : FVarId) : Expr :=
  (go e 0).run' ({}, {})
where
  contains (e : Expr) : StateM (Std.HashMap USize Bool × Std.HashMap (USize × Nat) Expr) Bool := do
    if !e.hasFVar then return false
    if let some b := (← get).1.get? (ptrAddrUnsafe e) then return b
    let b ← match e with
      | .fvar y => pure (y == x)
      | .app f a => pure ((← contains f) || (← contains a))
      | .lam _ t b _ | .forallE _ t b _ => pure ((← contains t) || (← contains b))
      | .letE _ t v b _ => pure ((← contains t) || (← contains v) || (← contains b))
      | .mdata _ b | .proj _ _ b => contains b
      | _ => pure false
    modify fun (c, m) => (c.insert (ptrAddrUnsafe e) b, m)
    return b
  go (e : Expr) (off : Nat) : StateM (Std.HashMap USize Bool × Std.HashMap (USize × Nat) Expr) Expr := do
    if !(← contains e) then return e
    if let some r := (← get).2.get? (ptrAddrUnsafe e, off) then return r
    let r ← match e with
      | .fvar _ => pure (.bvar off)
      | .app f a => pure (e.updateApp! (← go f off) (← go a off))
      | .lam _ t b _ => pure (e.updateLambdaE! (← go t off) (← go b (off + 1)))
      | .forallE _ t b _ => pure (e.updateForallE! (← go t off) (← go b (off + 1)))
      | .letE _ t v b _ => pure (e.updateLetE! (← go t off) (← go v off) (← go b (off + 1)))
      | .mdata _ b => pure (e.updateMData! (← go b off))
      | .proj _ _ b => pure (e.updateProj! (← go b off))
      | _ => pure e
    modify fun (c, m) => (c, m.insert (ptrAddrUnsafe e, off) r)
    return r

/-- `e` with the free variable `x` replaced by the loose bound variable of index 0 (the body of `fun x => e`): only the
    subterms containing `x` are traversed (`Expr.abstract` traverses the subterms with free variables, e.g., in a proof
    of the backend, the large terms over the variables of the goal, once per binder depth, i.e., per nested `lemma`). -/
@[implemented_by abstractFVarImpl] opaque abstractFVar (e : Expr) (x : FVarId) : Expr

/-- The proof `p` of the root (in which the proofs `globals` of the global steps are metavariables, see `replay`), with
    the proof `G` of each global step lifted to the closed lambda term `Λ := fun fvs => G`, used as `Λ fvs` (`fvs`: the
    variables of the base local context, e.g., the variables of the goal and the negated goal).
    The proofs of the global steps are shared by the proofs of the scopes (nested `lemma` steps) at various binder
    depths, such that abstracting a variable in the instantiated proof (e.g., the negated goal) copies each subterm
    containing it once per binder depth (e.g., 10M subterms at binder depth 216 for a CEK evaluation of a validator):
    the closed lambda terms are neither traversed nor copied by the abstractions, and are checked once by the kernel.
    NOTE: the proofs use placeholders `P fvs` for the proofs of the global steps they use (such that they are not
    inlined), are abstracted by a single (native) abstraction sharing its cache (e.g., the interpreted terms of the goal
    shared by the proofs of the steps), and the placeholders are then replaced in the order of the steps (premises
    first). Nothing is lifted when a proof has metavariables.
    With `aux?`, each closed lambda term is replaced by the term that `aux? i (∀ fvs, φᵢ) Λ` returns (e.g., the
    constant of an auxiliary theorem proved by `Λ`, see `proveBySmtProof`), in the order of the substitutions. -/
def liftGlobalProofs (p : Expr) (globals : Array (MVarId × Expr)) (fvs : Array Expr)
    (aux? : Option (Nat → Expr → Expr → MetaM Expr) := none) : MetaM Expr := do
  -- the proofs inlined (no lifting)
  let inline : MetaM Expr := do
    for (m, v) in globals do m.assign v
    instantiateMVars p
  -- NOTE: let-variables would become lambda-bound (their values are needed by the proofs)
  if fvs.isEmpty || globals.isEmpty || (← fvs.anyM fun x => return (← x.fvarId!.getDecl).isLet) then return ← inline
  let ps ← globals.mapM fun _ => mkFreshFVarId
  for ((m, _), P) in globals.zip ps do m.assign (mkAppN (.fvar P) fvs)
  let ws ← globals.mapM fun (_, v) => instantiateMVars v
  let root ← instantiateMVars p
  if root.hasMVar || ws.any (·.hasMVar) then return ← inline
  -- the binders `fun fvs =>` (shared by the lambda terms)
  let template ← mkLambdaFVars fvs (mkConst ``True)
  let rec withBody (t : Expr) (k : Nat) (body : Expr) : Expr :=
    match k, t with
    | k + 1, .lam n d b bi => .lam n d (withBody b k body) bi
    | _, _ => body
  -- NOTE: a balanced tree of the proofs (a single application of all of them would be traversed recursively)
  let rec bundle (es : Array Expr) (lo hi : Nat) : Expr :=
    if hi ≤ lo + 1 then es.getD lo (mkConst ``True)
    else mkApp2 (mkConst ``And) (bundle es lo ((lo + hi) / 2)) (bundle es ((lo + hi) / 2) hi)
  termination_by hi - lo
  decreasing_by all_goals omega
  let rec unbundle (e : Expr) (lo hi : Nat) (acc : Array Expr) : Array Expr :=
    if hi ≤ lo + 1 then (if lo < hi then acc.push e else acc)
    else unbundle e.appArg! ((lo + hi) / 2) hi (unbundle e.appFn!.appArg! lo ((lo + hi) / 2) acc)
  termination_by hi - lo
  decreasing_by all_goals omega
  let bodies := unbundle ((bundle ws 0 ws.size).abstract fvs) 0 ws.size #[]
  let subst (finals : Std.HashMap FVarId Expr) (e : Expr) : Expr :=
    e.replace fun s => if !s.hasFVar then some s else match s with
      | .fvar x => finals.get? x
      | _ => none
  -- the order of the substitutions: the placeholders of a proof before it (a proof may use the proof of a step of
  -- greater index, e.g., in a `lemma` scope)
  let index : Std.HashMap FVarId Nat := ps.zipIdx.foldl (fun m (x, i) => m.insert x i) {}
  -- NOTE: the bodies have no other free variables (traversal of the subterms with free variables only)
  let deps := bodies.map fun b => ((collectFVars {} b).fvarIds.filterMap index.get?)
  let mut order : Array Nat := #[]
  let mut state : Array Nat := Array.replicate bodies.size 0  -- 0: new, 1: visiting, 2: done
  for r in [:bodies.size] do
    if state[r]! != 0 then continue
    let mut stack : Array (Nat × Nat) := #[(r, 0)]
    state := state.set! r 1
    while h : stack.size > 0 do
      let (i, k) := stack[stack.size - 1]
      if h' : k < deps[i]!.size then
        stack := stack.set! (stack.size - 1) (i, k + 1)
        let j := deps[i]![k]!
        if state[j]! == 0 then
          state := state.set! j 1
          stack := stack.push (j, 0)
      else
        stack := stack.pop
        state := state.set! i 2
        order := order.push i
  let mut finals : Std.HashMap FVarId Expr := {}
  for i in order do
    let v := subst finals (withBody template fvs.size bodies[i]!)
    -- the closed term replaced by the term `aux?` builds from its type and itself (e.g., an auxiliary theorem)
    let v ← match aux? with
      | some aux => aux i (← mkForallFVars fvs (← instantiateMVars (← globals[i]!.1.getType))) v
      | none => pure v
    finals := finals.insert ps[i]! v
  return subst finals root

/-- The steps being replayed (innermost last), written to the file given by `BLASTER_SMTPROOF_CURRENT` (if set)
    when a step starts, e.g., to locate a step that takes long (the modification time of the file). -/
initialize currentSteps : IO.Ref (Array String) ← IO.mkRef #[]

mutual

/-- Proof of the interpretation of the conclusion of step `i`. -/
partial def replay (i : Nat) : ReplayM Expr := do
  let ctx ← read
  if let some p := (← get).cache.get? i then return p
  -- steps not depending on a scope are cached globally, also when first replayed in a scope
  let isGlobal := ctx.depth == 0 || ctx.global.getD i false
  if isGlobal && (← get).failed.contains i then throwError "smt proof: step {i} already failed"
  if !isGlobal then
    if let some p := (← get).scopeCache.get? i then return p
    if (← get).scopeFailed.contains i then throwError "smt proof: step {i} already failed"
  -- NOTE: a step that doesn't depend on a scope is replayed outside of the scope (in particular, its proof
  -- doesn't use the hypotheses of the scope), such that its proof can be cached globally
  let atBase := ctx.depth > 0 && isGlobal
  let p ← try
      if atBase then
        -- NOTE: the proofs of the current scope are not available at depth 0 (e.g., for nested lemmas)
        withReader (fun c => { c with depth := 0, facts := #[], interp := { c.interp with locals := {} } }) <|
          withLCtx ctx.baseLCtx ctx.baseInsts (withScope (replayCore i))
      else replayCore i
    catch ex =>
      if isGlobal then modify fun s => { s with failed := s.failed.insert i }
      else modify fun s => { s with scopeFailed := s.scopeFailed.insert i }
      -- NOTE: premises are replayed before their consumers, i.e., the first failures are the deepest ones
      let step := ctx.proof.steps[i]!
      let msg := s!"step {i} ({step.rule}): {toString step.concl |>.take 300}: {(← ex.toMessageData.toString).take 300}"
      if let some f ← IO.getEnv "BLASTER_SMTPROOF_FAILDUMP" then
        let h ← IO.FS.Handle.mk f .append
        let c ← try (do
            let c ← stepConcl i
            -- NOTE: large terms are printed with their sharing
            if Local.sizeLe c 20000 then pure (toString (← ppExpr c)) else dagString c) catch _ => pure "?"
        h.putStrLn s!"=== step {i} ({step.rule} {step.attrs}) premises {step.premises}: {(← ex.toMessageData.toString).take 500}\n{c.take 30000}\n"
      modify fun s => { s with stats := { s.stats with failures := s.stats.failures.push msg } }
      throw ex
  if (← IO.getEnv "BLASTER_SMTPROOF_CHECK").isSome then
    let lctx ← getLCtx
    let p' ← instantiateMVars p
    if p'.hasAnyFVar (fun f => !lctx.contains f) then
      let bad := ((collectFVars {} p').fvarIds).filter (!lctx.contains ·)
      let sub? := p'.find? fun e => e.isApp && e.getAppFn.isConst && e.getAppArgs.any (fun a => a.isFVar && bad.contains a.fvarId!)
      IO.eprintln s!"unknown fvar in step {i} ({ctx.proof.steps[i]!.rule}) depth {ctx.depth}: {bad.map (·.name)} in {← (MessageData.ofExpr (sub?.getD p')).toString}"
      throwError "smt proof: step {i} ({ctx.proof.steps[i]!.rule}) has a proof with an unknown free variable: {p'}"
  if isGlobal then
    -- the proof is represented by a metavariable of the base context, such that the proofs using it stay small; it
    -- is not assigned (the instantiations of the proofs using it would inline it, e.g., in the abstractions of the
    -- scopes), but held by `globalProofs` (see `liftGlobalProofs`)
    let p ← if p.isFVar || p.isMVar then pure p else do
      let m ← withLCtx ctx.baseLCtx ctx.baseInsts <| mkFreshExprMVar (← stepConcl i) (kind := .syntheticOpaque)
      modify fun s => { s with globalProofs := s.globalProofs.push (m.mvarId!, p), globalSteps := s.globalSteps.push i }
      pure m
    modify fun s => { s with cache := s.cache.insert i p }
    return p
  else modify fun s => { s with scopeCache := s.scopeCache.insert i p }
  return p

partial def replayCore (i : Nat) : ReplayM Expr := do
  let ctx ← read
  let step := ctx.proof.steps[i]!
  -- premises are replayed first, such that the time of the step only accounts for the step itself
  -- NOTE: premises of `lemma` (resp. `proof-bind`) are replayed under hypotheses (resp. bound variables)
  if !(["lemma", "proof-bind", "subproof", "bind", "sko_ex", "sko_forall"].contains step.rule) then
    for j in step.premises do
      try discard <| replay j catch _ => pure ()
  if (← IO.monoMsNow) > ctx.deadline then throwError "smt proof: replay deadline exceeded"
  let start ← IO.monoMsNow
  let (tac0, goals0) ← Local.portfolioTime.get
  let current ← IO.getEnv "BLASTER_SMTPROOF_CURRENT"
  if let some f := current then
    currentSteps.modify (·.push s!"step {i} ({step.rule}): {(toString step.concl).take 300}")
    IO.FS.writeFile f ("\n".intercalate (← currentSteps.get).toList)
  try replayCore' i step
  finally
    if current.isSome then currentSteps.modify (·.pop)
    let ms := (← IO.monoMsNow) - start
    modify fun s => { s with stats := s.stats.addTime step.rule ms }
    -- profiling (environment variable `BLASTER_SMTPROOF_TRACE`: file receiving the steps taking more than 100 ms)
    if ms > 100 then
      if let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" then
        let h ← IO.FS.Handle.mk f .append
        let (tac1, goals1) ← Local.portfolioTime.get
        h.putStrLn s!"step {i} {step.rule} depth {ctx.depth}: {ms} ms (tactics {tac1 - tac0} ms on \
          {goals1 - goals0} goals); {(toString step.concl).take 200}"

partial def replayCore' (i : Nat) (step : Step) : ReplayM Expr := do
  let ctx ← read
  let concl ← stepConcl i
  -- debugging: the conclusions of the steps `BLASTER_SMTPROOF_STEPS` (indices) as Lean statements, in the file
  -- `BLASTER_SMTPROOF_STEPDUMP`
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_STEPDUMP" then
    if (((← IO.getEnv "BLASTER_SMTPROOF_STEPS").getD "").splitOn ",").contains (toString i) then
      let g ← mkForallFVars (← usedFVars concl) concl
      let s ← withOptions (fun o => o.setBool `pp.numericTypes true |>.setBool `pp.coercions.types true
          |>.setBool `pp.fieldNotation false |>.setNat `pp.maxSteps 100000000 |>.setBool `pp.deepTerms true) do
        return toString (← ppExpr g)
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn s!"-- step {i} ({step.rule})\nexample : {s} := by\n  sorry\n"
  -- NOTE: the runtime exceptions (e.g., the maximum recursion depth in a tactic) are failures of the attempt too
  let attempt : ReplayM (Option Expr) := do
    tryCatchRuntimeEx (some <$> withReader (fun c => { c with stepIdx := i }) (replayRule step concl)) fun ex => do
      debugLog m!"step {i} ({step.rule}) failed: {ex.toMessageData}"
      return none
  if let some p ← attempt then return p
  -- fallback: unit propagation (e.g., for clauses whose literals are disjunctions)
  if ["unit-resolution", "resolution", "th_resolution"].contains step.rule then
    if let some p ← tryCatchRuntimeEx (some <$> replayRup step concl) fun _ => pure none then return p
  -- fallback: tactics on `premises → conclusion` (e.g., when an explicit construction fails due to casts)
  if !(["asserted", "goal", "hypothesis", "lemma", "proof-bind"].contains step.rule) then
    let p? ← tryCatchRuntimeEx (some <$> replayByTactic step concl) fun ex => do
      debugLog m!"step {i} ({step.rule}) by tactics failed: {ex.toMessageData}"
      return none
    if let some p := p? then return p
  -- fallback: direct proof of the conclusion (except for `False`, which amounts to proving the goal
  -- without the proof of the backend)
  if concl.isConstOf ``False then
    throwError "smt proof: could not replay step {i} ({step.rule}) concluding false"
  -- NOTE: direct proofs are costly; they are attempted a bounded number of times, and for a bounded total time on
  -- large statements (e.g., the steps of a CEK evaluation depending on a failed step: each attempt exhausted the
  -- budgets of the bridge tactics, about 15 s)
  let large := !Local.sizeLe concl Local.largeTermSize
  if !ctx.prepass && (← get).directAttempts < ctx.maxDirect && (!large || (← get).largeDirectMs < 60000) then
    modify fun s => { s with directAttempts := s.directAttempts + 1 }
    let start ← IO.monoMsNow
    -- NOTE: in the local context of depth 0 when possible: the proof must not use the hypotheses of the scopes (e.g.,
    -- the negations of the clauses of lemmas), which the step does not depend on
    let base := !concl.hasAnyFVar (!ctx.baseLCtx.contains ·)
    let p? ← try (if base then withLCtx ctx.baseLCtx ctx.baseInsts (ctx.cfg.proveDirect concl) else ctx.cfg.proveDirect concl)
      finally
        if large then
          let ms := (← IO.monoMsNow) - start
          modify fun s => { s with largeDirectMs := s.largeDirectMs + ms }
    if let some p := p? then
      record step.rule "direct"
      return p
  throwError "smt proof: could not replay step {i} ({step.rule})"

/-- Premise proofs with their propositions. -/
partial def premises (step : Step) : ReplayM (Array (Expr × Expr)) :=
  step.premises.mapM fun j => do return (← stepConcl j, ← replay j)

partial def replayRule (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  match step.rule with
  | "asserted" | "goal" | "assume" =>
      for (formula, proof) in ctx.cfg.inputAssertions do
        if ← propEq formula concl then
          record step.rule "encoding-contract"
          return proof
      let some p ← ctx.cfg.proveDirect concl | throwError "asserted formula not proved"
      record step.rule "bridge"
      return p
  | "hypothesis" =>
      -- NOTE: syntactic matches first (the definitional ones are costly on large propositions)
      for (t, p) in ctx.facts do
        if t == concl then record step.rule "exact"; return p
      for (t, p) in ctx.facts do
        if ← propEq t concl then record step.rule "exact"; return p
      throwError "hypothesis not found"
  | "lemma" | "subproof" => replayLemma step concl
  | "true-axiom" => record step.rule "exact"; return Lean.mkConst ``True.intro
  | "mp" | "mp~" =>
      let ps ← premises step
      let #[(a, pa), (eq, peq)] := ps | throwError "mp: two premises expected"
      let r ← do
        if let some (_, l, r) := eq.eq? then
          if ← propEq l a then pure (some (← mkEqMP peq pa, r)) else pure none
        else if let some (l, r) := eq.iff? then
          if ← propEq l a then pure (some (mkApp3 (Lean.mkConst ``Iff.mp) l r peq |>.app pa, r)) else pure none
        else if eq.isArrow then
          pure (some (mkApp peq pa, eq.bindingBody!))
        else pure none
      let some (p, r) := r | throwError "mp: unexpected premises"
      if ← propEq r concl (deep := true) then record step.rule "exact"; return p
      throwError "mp: conclusion mismatch"
  | "refl" | "intro-def" =>
      if let some (_, a, b) := concl.eq? then
        if !(← propEq a b (deep := true)) then throwError "refl: sides differ"
        record step.rule "exact"; return ← mkEqRefl a
      if concl.isArrow then
        record step.rule "exact"
        return ← withLocalDeclD `h concl.bindingDomain! fun h => mkLambdaFVars #[h] h
      throwError "refl: unexpected conclusion"
  | "symm" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "symm: one premise expected"
      let r ← mkEqSymm p
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "symm: conclusion mismatch"
  | "trans" =>
      let ps ← premises step
      let #[(tp, p), (tq, q)] := ps | throwError "trans: two premises expected"
      let some (_, _, m₁) := tp.eq? | throwError "trans: equality expected"
      let some (_, m₂, _) := tq.eq? | throwError "trans: equality expected"
      if !(← propEq m₁ m₂) then throwError "trans: middle terms differ"
      let r ← mkEqTrans p q
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "trans: conclusion mismatch"
  | "trans*" =>
      -- transitivity of possibly symmetric equalities: a path between the sides of the conclusion
      let ps ← premises step
      let some (_, l, r) := concl.eq? | throwError "trans*: equality expected"
      let edges ← ps.filterMapM fun (t, p) => do
        let some (_, a, b) := t.eq? | return none
        return some (a, b, p)
      -- breadth-first search from `l`
      let mut frontier : Array (Expr × Expr) := #[(l, ← mkEqRefl l)]
      let mut seen : Array Expr := #[l]
      let mut found : Option Expr := none
      for _ in [0:edges.size + 1] do
        if found.isSome || frontier.isEmpty then break
        let mut next := #[]
        for (x, px) in frontier do
          if x == r then found := some px; break
          for (a, b, p) in edges do
            let step? ← if a == x then pure (some (b, ← mkEqTrans px p))
              else if b == x then pure (some (a, ← mkEqTrans px (← mkEqSymm p)))
              else pure none
            if let some (y, py) := step? then
              if !seen.contains y then
                seen := seen.push y
                next := next.push (y, py)
        if found.isNone then
          if let some (_, py) := next.find? (·.1 == r) then found := some py
        frontier := next
      let some pf := found | throwError "trans*: no path"
      if ← propEq (← inferType pf) concl then record step.rule "exact"; return pf
      throwError "trans*: conclusion mismatch"
  | "iff-true" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "iff-true: one premise expected"
      let r ← mkAppM ``eq_true #[p]
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "iff-true: conclusion mismatch"
  | "iff-false" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "iff-false: one premise expected"
      let r ← mkAppM ``eq_false #[p]
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "iff-false: conclusion mismatch"
  | "resolution" | "th_resolution" | "reordering" | "contraction" => replayRup step concl
  | "unit-resolution" =>
      let ps ← timed "premises" (premises step)
      let some (c, _) := ps[0]? | throwError "unit-resolution: premises expected"
      -- the clause premise is `(or l₁ ... lₙ)`
      let n := ctx.proof.steps[step.premises[0]!]!.clauseSize
      let lits := disjuncts c n
      -- NOTE: the conclusion may be a single literal of the clause which is a disjunction
      let single ← pure (lits.any (· == concl)) <||> lits.anyM fun l => propEq l concl
      let targetLits :=
        if step.clauseSize == 0 then #[]
        else if single then #[concl]
        else disjuncts concl step.clauseSize
      -- the premises as the bound variables of `fun p₀ ... pₖ => ...` applied to their proofs (see `withPremiseVars`),
      -- the proof being built under the binders (see `orElim`)
      let r ← timed "weaken" do
        let k := ps.size
        let vs := ps.zipIdx.map fun ((t, _), j) => (t, Expr.bvar (k - 1 - j))
        let body ← weakenClause lits vs[0]!.2 (refuteBy (vs.extract 1 vs.size)) targetLits
        pure (mkAppN (ps.foldr (fun (t, _) acc => .lam `p t acc .default) body) (ps.map (·.2)))
      record step.rule "exact"
      return r
  | "quant-inst" | "forall_inst" =>
      -- `(or (not (forall xs. P)) P[ts])`
      let some (nq, inst) := orArgs? concl | throwError "quant-inst: disjunction expected"
      let some q := nq.not? | throwError "quant-inst: negated quantifier expected"
      let pending ← IO.mkRef #[]
      let ts ← liftInterp (withReader (fun c => { c with pendingHints := some pending }) (step.args.mapM interpInt?))
      let ts ← ts.mapM fun t => liftM (fillDefaults t)
      let dflt ← defaultTypeParam
      let r ← withLocalDeclD `h q fun h => do
        let hi ← instantiateWithCoercion h ts
        if !(← propEq (← inferType hi) inst (deep := true)) then throwError "quant-inst: instance mismatch"
        -- the hints of the instantiation terms whose instance is still undetermined (see `SortInfer`)
        liftInterp (applySortHints (← pending.get))
        let hi ← assignDefaultTypes hi dflt
        mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inr) nq inst hi)
      let rn ← withLocalDeclD `h nq fun h => mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inl) nq inst h)
      record step.rule "exact"
      return mkApp6 (Lean.mkConst ``Or.elim) q nq concl (mkApp (Lean.mkConst ``Classical.em) q) r rn
  | "proof-bind" => replayBind step
  | "quant-intro" =>
      -- `∀ xs, a xs = b xs` (resp. `→`, for `~`) gives `(∀ xs, a xs) = (∀ xs, b xs)` (resp. `→`)
      let ps ← premises step
      let #[(t, p)] := ps | throwError "quant-intro: one premise expected"
      let r ← quantIntro t p concl
      let some pf := r | throwError "quant-intro: unexpected forms"
      if ← propEq (← inferType pf) concl then record step.rule "exact"; return pf
      throwError "quant-intro: conclusion mismatch"
  | "monotonicity" | "cong" => replayCongr step concl
  | "commutativity" => replayComm concl
  | "sk" =>
      -- `(¬ ∀ x, φ) → ¬ φ[ε]` or `(∃ x, φ) → φ[ε]` (see the interpretation of skolem constants), one bound
      -- variable at a time: `¬ ∀ x₁ x₂, φ` gives `¬ ∀ x₂, φ[x₁ := ε₁]`, then `¬ φ[x₁ := ε₁, x₂ := ε₂]`
      let some (a, b) := (if concl.isArrow then some (concl.bindingDomain!, concl.bindingBody!) else none)
        | throwError "sk: implication expected"
      let r ← withLocalDeclD `h a fun h => do
        let mut pf := h
        let mut ty := a
        for _ in [0:64] do
          let ex ← if let some q := ty.not? then
              -- `¬ ∀ x, φ x` gives `∃ x, ¬ φ x`
              let .forallE n t body bi := q | throwError "sk: negated forall expected"
              let p := mkLambda n bi t body
              let iff := mkApp2 (Lean.mkConst ``Classical.not_forall [← getLevel t]) t p
              mkAppM ``Iff.mp #[iff, pf]
            else pure pf
          pf ← mkAppM ``Classical.epsilon_spec #[ex]
          ty ← instantiateMVars (← inferType pf)
          if ← propEq ty b then return ← mkLambdaFVars #[h] pf
          -- another bound variable
          let more := match ty.not? with
            | some (.forallE ..) => true
            | some _ => false
            | none => ty.isAppOfArity ``Exists 2
          if !more then break
        throwError "sk: skolem mismatch"
      record step.rule "exact"
      return r
  | _ => replayByTactic step concl

/-- Whether the metavariable `m` occurs in `e` (the subterms without metavariables are not traversed). -/
partial def containsMVar (e : Expr) (m : MVarId) : Bool :=
  (go e).run' {}
where
  go (e : Expr) : StateM (Std.HashSet Expr) Bool := do
    if !e.hasMVar || (← get).contains e then return false
    modify (·.insert e)
    match e with
    | .mvar m' => return m' == m
    | .app f a => return (← go f) || (← go a)
    | .lam _ t b _ | .forallE _ t b _ => return (← go t) || (← go b)
    | .letE _ t v b _ => return (← go t) || (← go v) || (← go b)
    | .mdata _ b | .proj _ _ b => go b
    | _ => return false

/-- `e` with the metavariable `m` replaced by the loose bound variable of index 0 (the body of `fun x => e[m := x]`):
    only the subterms with metavariables are traversed (`Expr.abstract` traverses the subterms with free variables,
    e.g., all the large terms over the variables of the goal in the proofs of the steps). -/
partial def abstractMVar (e : Expr) (m : MVarId) : Expr :=
  (go e 0).run' {}
where
  go (e : Expr) (off : Nat) : StateM (Std.HashMap (Expr × Nat) Expr) Expr := do
    if !e.hasMVar then return e
    if let some r := (← get).get? (e, off) then return r
    let r ← match e with
      | .mvar m' => pure (if m' == m then .bvar off else e)
      | .app f a => pure (e.updateApp! (← go f off) (← go a off))
      | .lam _ t b _ => pure (e.updateLambdaE! (← go t off) (← go b (off + 1)))
      | .forallE _ t b _ => pure (e.updateForallE! (← go t off) (← go b (off + 1)))
      | .letE _ t v b _ => pure (e.updateLetE! (← go t off) (← go v off) (← go b (off + 1)))
      | .mdata _ b => pure (e.updateMData! (← go b off))
      | .proj _ _ b => pure (e.updateProj! (← go b off))
      | _ => pure e
    modify (·.insert (e, off) r)
    return r

/-- `lemma`: the premise derives `false` under hypotheses; the conclusion is the disjunction of the
    negations of the hypotheses. -/
partial def replayLemma (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  let some j := step.premises[0]? | throwError "lemma: premise expected"
  let n := step.clauseSize
  let lits := disjuncts concl n
  -- NOTE: the hypothesis `hn` is a metavariable (abstracted at the end by `abstractMVar`), such that the abstraction
  -- does not traverse the large terms of the proof of the subproof
  let hn ← mkFreshExprMVar (mkNot concl) (kind := .syntheticOpaque) (userName := `hn)
  let r ← timed "lemma" <| timed "lemma body" do
    let t0 ← IO.monoMsNow
    -- facts derived from `¬ (l₁ ∨ ... ∨ lₙ)`: `¬ lᵢ`, and `a` when `lᵢ = ¬ a`
    let facts ← timed "lemma facts" do
      let mut facts := ctx.facts.push (mkNot concl, hn)
      let sfx := orSuffixes lits
      for k in [:lits.size] do
        let l := lits[k]!
        let nl ← withLam `h l fun h => return mkApp hn (mkOrInjWith lits sfx k h)
        facts := facts.push (mkNot l, nl)
        if let some a := l.not? then
          facts := facts.push (a, mkApp2 (Lean.mkConst ``Classical.byContradiction) a nl)
      return facts
    -- the proofs of the steps not depending on the hypotheses discharged by the lemma stay valid after it
    -- NOTE: the hypotheses are matched on their propositions (see `hypothesis`), hence the occurrences of `hn`
    -- NOTE: the open hypotheses of the premise that are not open hypotheses of the lemma (see `openHypotheses`; the
    -- matching of the hypotheses with the literals, see `discharges`, is costly on large clauses)
    let own : Std.HashSet Nat := (ctx.openHyps.getD ctx.stepIdx #[]).foldl (·.insert ·) {}
    let disch : Std.HashSet Nat := (ctx.openHyps.getD j #[]).foldl (fun s h => if own.contains h then s else s.insert h) {}
    -- NOTE: `containsFVar` skips the closed subterms (e.g., the large terms of a CEK evaluation)
    let keep (k : Nat) (p : Expr) : Bool := !ctx.openHyps.isEmpty && (ctx.openHyps.getD k #[]).all (!disch.contains ·) &&
      !containsMVar p hn.mvarId!
    let inherit := (← IO.getEnv "BLASTER_SMTPROOF_NOINHERIT").isNone
    let ms := (← IO.monoMsNow) - t0
    if ms > 100 then
      if let some f ← IO.getEnv "BLASTER_SMTPROOF_TRACE" then
        (← IO.FS.Handle.mk f .append).putStrLn s!"  phase lemma setup: {ms} ms"
    let pf ← timed "subproof" <| withScope (inherit := inherit) (keep := keep) (withReader (fun c => { c with facts, depth := c.depth + 1 }) do
      let pj ← replay j
      -- the premise derives `false` (Z3's `lemma`) or a literal of the conclusion (Alethe's `subproof`)
      let cj ← stepConcl j
      if cj.isConstOf ``False then return pj
      for (t, p) in facts do
        if let some a := t.not? then
          if a == cj then return mkApp p pj
      for (t, p) in facts do
        if let some a := t.not? then
          if ← propEq a cj then return mkApp p pj
      throwError "lemma: the premise is not refuted by the hypotheses")
    timed "lemma abstract" do
      -- NOTE: `hn'` bound in the computation, such that the abstraction is computed in it (timing)
      let hn' ← pure hn
      return mkLambda `hn .default (mkNot concl) (abstractMVar pf hn'.mvarId!)
  record step.rule "exact"
  return mkApp2 (Lean.mkConst ``Classical.byContradiction) concl r

/-- `proof-bind`: proof of the body of a quantifier rewrite, under bound variables. The conclusion is
    interpreted as a universally quantified formula. -/
partial def replayBind (step : Step) : ReplayM Expr := do
  let .quant _ vars _ := step.concl | throwError "proof-bind: lambda expected"
  let some j := step.premises[0]? | throwError "proof-bind: premise expected"
  let types ← liftInterp (vars.mapM fun (_, s) => sortToType s)
  let rec go (k : Nat) (fvars : Array Expr) : ReplayM Expr := do
    if h : k < vars.size then
      withLocalDeclD (Name.mkSimple vars[k].1) types[k]! fun x =>
        withReader (fun c => { c with interp := { c.interp with locals := c.interp.locals.insert vars[k].1 x } })
          (go (k + 1) (fvars.push x))
    else
      let pf ← withScope (withReader (fun c => { c with depth := c.depth + 1 }) (replay j))
      mkLambdaFVars fvars pf
  let r ← go 0 #[]
  record step.rule "exact"
  return r

/-- Proof of `l = r` from equalities `eqs` (`aᵢ = bᵢ` with proof `pᵢ`) by congruence, descending in the
    applications whose heads are equal. -/
partial def congrDescent (eqs : Array (Expr × Expr × Expr)) (l r : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if l == r then return some (← mkEqRefl l)
  for (a, b, p) in eqs do
    if l == a && r == b then return some p
    if l == b && r == a then return some (← mkEqSymm p)
  if fuel == 0 then return none
  if !l.isApp || !r.isApp then return none
  let lf := l.getAppFn
  let rf := r.getAppFn
  let las := l.getAppArgs
  let ras := r.getAppArgs
  if lf != rf || las.size != ras.size then return none
  -- conditionals (the instance depends on the condition)
  if let some p ← Local.iteCongr? l r (congrDescent eqs · · (fuel - 1)) then return some p
  -- congruence on each argument (dependent arguments must be equal)
  let mut diffs := #[]
  for i in [:las.size] do
    if las[i]! == ras[i]! then continue
    let some pi ← congrDescent eqs las[i]! ras[i]! (fuel - 1) | return none
    diffs := diffs.push (i, pi)
  congrArgs lf las ras diffs

/-- Congruence (`monotonicity`): from premises `aᵢ = bᵢ`, prove `L = R` by abstracting the
    occurrences of each `aᵢ` in `L` and applying `congrArg` (premises not occurring are ignored). -/
partial def replayCongr (step : Step) (concl : Expr) : ReplayM Expr := do
  let some (ty, l, r) := concl.eq? | throwError "monotonicity: equality expected"
  let ps ← premises step
  -- structural descent: linear in the size of the paths to the differences (no traversal of the shared
  -- subterms, unlike `kabstract`)
  let eqs := ps.filterMap fun (t, p) => (t.eq?).map fun (_, a, b) => (a, b, p)
  if let some pf ← congrDescent eqs l r 64 then
    record step.rule "exact"
    return pf
  -- the occurrences of the premises abstracted (e.g., below binders), syntactically first (see
  -- `Local.abstractOccurrences`), then up to reducible definitional equality
  let byAbstraction (abstr : Expr → Expr → MetaM Expr) : ReplayM (Option Expr) := do
    let mut cur := l
    let mut pf ← mkEqRefl l
    for (t, p) in ps do
      let some (_, a, b) := t.eq? | throwError "monotonicity: equality premise expected"
      let abst ← abstr cur a
      if !abst.hasLooseBVars then continue
      let motive := mkLambda `x .default (← inferType a) abst
      let next := abst.instantiate1 b
      let u ← getLevel ty
      let v ← getLevel (← inferType a)
      let c := mkApp6 (Lean.mkConst ``congrArg [v, u]) (← inferType a) ty a b motive p
      pf := mkApp6 (Lean.mkConst ``Eq.trans [u]) ty l cur next pf c
      cur := next
    if !(← propEq cur r) then return none
    return some pf
  let some pf ← (do
      if let some pf ← byAbstraction Local.abstractOccurrences then pure (some pf)
      else byAbstraction kabstract)
    | throwError "monotonicity: congruence mismatch"
  record step.rule "exact"
  return pf

/-- `commutativity`: `f a b = f b a` for commutative operations (equality, `∧`, `∨`, `+`, `*` on `Int`). -/
partial def replayComm (concl : Expr) : ReplayM Expr := do
  let some (_, l, r) := concl.eq? | throwError "commutativity: equality expected"
  let swapped (op : Name) (n : Nat) : Option (Expr × Expr) :=
    if l.isAppOfArity op n && r.isAppOfArity op n then
      let la := l.getAppArgs; let ra := r.getAppArgs
      if la[n-2]! == ra[n-1]! && la[n-1]! == ra[n-2]! then some (la[n-2]!, la[n-1]!) else none
    else none
  let pf ← do
    if let some (a, b) := swapped ``Or 2 then mkAppM ``propext #[← mkAppOptM ``or_comm #[a, b]]
    else if let some (a, b) := swapped ``And 2 then mkAppM ``propext #[← mkAppOptM ``and_comm #[a, b]]
    else if let some (a, b) := swapped ``Eq 3 then mkAppM ``propext #[← mkAppOptM ``eq_comm #[none, a, b]]
    else if let some (a, b) := swapped ``HAdd.hAdd 6 then mkAppM ``Int.add_comm #[a, b]
    else if let some (a, b) := swapped ``HMul.hMul 6 then mkAppM ``Int.mul_comm #[a, b]
    else throwError "commutativity: unsupported operation"
  if !(← propEq (← inferType pf) concl) then throwError "commutativity: mismatch"
  record "commutativity" "exact"
  return pf

/-- Datatype facts as clauses: constructor injectivity `¬ (C a⃗ = C b⃗) ∨ aᵢ = bᵢ` and distinctness
    `¬ (C a⃗ = D b⃗)` (Z3's `th-lemma datatype`), with explicit proofs (`C.inj`, `noConfusion`). -/
partial def replayDatatype (concl : Expr) : MetaM (Option Expr) := do
  let lits := disjuncts concl 2
  -- distinctness
  if lits.size == 1 then
    let some eq := concl.not? | return none
    let some (_, l, r) := eq.eq? | return none
    let (lf, rf) := (l.getAppFn, r.getAppFn)
    let (.const lc _, .const rc _) := (lf, rf) | return none
    let env ← getEnv
    if !(env.find? lc |>.any (·.isCtor)) || !(env.find? rc |>.any (·.isCtor)) || lc == rc then return none
    return some (← withLam `h eq fun h => mkNoConfusion (mkConst ``False) h)
  -- injectivity
  if lits.size == 2 then
    let some eq := lits[0]!.not? | return none
    let some (_, l, r) := eq.eq? | return none
    let some (_, x, y) := lits[1]!.eq? | return none
    let .const c _ := l.getAppFn | return none
    let some (.ctorInfo info) := (← getEnv).find? c | return none
    if !r.isAppOf c then return none
    let la := l.getAppArgs
    let ra := r.getAppArgs
    let some _ := (List.range info.numFields).find? fun k =>
      la[info.numParams + k]! == x && ra[info.numParams + k]! == y | return none
    let injName := c ++ `inj
    if !(← getEnv).contains injName then return none
    -- `C.inj h : a₁ = b₁ ∧ ... ∧ aₙ = bₙ` (only the non-trivial equalities of fields)
    let pos ← withLam `h eq fun h => do
      let conj ← mkAppM injName #[h]
      let mut cur := conj
      let mut ty ← whnfR (← inferType conj)
      -- find the equality `x = y` in the conjunction
      let mut found : Option Expr := none
      for _ in [0:info.numFields + 1] do
        if let some (a, b) := ty.and? then
          if let some (_, x', y') := a.eq? then
            if x' == x && y' == y then found := some (mkApp3 (mkConst ``And.left) a b cur); break
          cur := mkApp3 (mkConst ``And.right) a b cur
          ty ← whnfR b
        else
          if let some (_, x', y') := ty.eq? then
            if x' == x && y' == y then found := some cur
          break
      let some p := found | throwError "datatype: field equality not found"
      return mkApp3 (mkConst ``Or.inr) (mkNot eq) lits[1]! p
    let neg ← withLam `h (mkNot eq) fun h => return mkApp3 (mkConst ``Or.inl) (mkNot eq) lits[1]! h
    return some (mkApp6 (mkConst ``Or.elim) eq (mkNot eq) concl (mkApp (mkConst ``Classical.em) eq) pos neg)
  return none

/-- Resolution steps: unit propagation on the premise clauses (see `rupProof`). -/
partial def replayRup (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  let t0 ← IO.monoMsNow
  let mut ps := #[]
  for j in step.premises do ps := ps.push (← stepConcl j, ← replay j)
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := s.stats.addTime "rup-premises" (t1 - t0) }
  let n := step.clauseSize
  let target := if n == 0 then #[] else disjuncts concl n
  let t0 ← IO.monoMsNow
  let sizes := step.premises.map (ctx.proof.steps[·]!.clauseSize)
  let r ← withPremiseVars ps fun vs => do
    let mut clauses := #[]
    for ((c, pc), n) in vs.zip sizes do
      let lits := if n == 0 then #[] else disjuncts c n
      clauses := clauses.push (lits, pc)
      -- NOTE: a clause whose single literal is a disjunction is also given as is
      if n > 1 then clauses := clauses.push (#[c], pc)
    rupProof clauses target
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := s.stats.addTime "rup-core" (t1 - t0) }
  record step.rule "exact"
  return r

/-- Prove `p₁ → ... → pₙ → c` with tactics and apply it to the premise proofs. -/
partial def replayByTactic (step : Step) (concl : Expr) : ReplayM Expr := do
  let cfg := (← read).cfg
  if cfg.certificates && step.rule == "th-lemma" && step.attrs[1]? == some (.atom "farkas") then
    if let some p ← Farkas.replay? step (← premises step) concl then
      record step.rule "certificate-farkas"
      return p
  -- unfoldings of recursive functions by cases (Z3)
  if step.rule == "th-lemma" && step.premises.isEmpty && step.attrs[0]? == some (.atom "recfun") then
    if let some p ← timed "recfun" (cfg.proveRecFun concl step.clauseSize) then
      record step.rule "recfun"
      return p
    if cfg.recFunOnly then throwError "recfun lemma not replayed"
  if step.rule == "th-lemma" && step.premises.isEmpty then
    if let some p ← (try replayDatatype concl catch _ => pure none) then
      if ← propEq (← inferType p) concl then
        record step.rule "datatype"
        return p
    -- case analyses on a datatype term (e.g., `x = C (C.0 x) ∨ ¬ is-C x`)
    if let some p ← timed "datatype cases" (try caseLemma? concl (disjuncts concl (clauseSize step.concl)) catch _ => pure none) then
      record step.rule "datatype cases"
      return p
  -- large statements (e.g., the CEK evaluation of validators): tactics are only applied to their local
  -- differences (see `Local`)
  let large := !(Local.sizeLe concl Local.largeTermSize)
  let unfoldable := Local.sizeLe concl 2000
  -- identical sides (e.g., rewrites of Z3 normalizing the n-ary connectives folded by the interpretation)
  if let some (_, a, b) := concl.eq? then
    if a == b then
      record step.rule "refl"
      return ← mkEqRefl a
    -- definitional rewrites (e.g., testers of single-constructor types, by structure eta), with a budget
    -- (only reducible definitions for large terms)
    if ← timed "defeq" (defeqBudget a b 20000 unfoldable) then
      record step.rule "defeq"
      return ← mkExpectedTypeHint (← mkEqRefl a) concl
  -- unfoldings of recursive functions by Z3's rewriter (e.g., applications to constructors): instances of their
  -- definitional equations (see `RecFun.proveLemma`)
  if step.rule == "rewrite" && step.premises.isEmpty && cfg.recFunOnly then
    -- the head function of an application, through the conversions of the interpretation
    let head? (e : Expr) : Option Name :=
      let e := if e.isAppOfArity ``Eq 3 && (e.getArg! 2).isConstOf ``Bool.true then e.getArg! 1 else e
      let e := if e.isAppOfArity ``Nat.cast 3 then e.appArg! else e
      e.getAppFn.constName?
    if let some (_, l, r) := concl.eq? then
      if [l, r].any fun e => (head? e).any cfg.recHeads.contains then
        if let some p ← timed "recfun" (cfg.proveRecFun concl 1) then
          record step.rule "recfun"
          return p
  let ps ← premises step
  -- NOTE: premises with a bound-variable body (`proof-bind`) are universally quantified propositions
  let stmt := ps.foldr (fun (t, _) acc => mkForall `h .default t acc) concl
  let applyPremises (pf : Expr) : Expr := mkAppN pf (ps.map (·.2))
  -- propositional steps (e.g., `def-axiom`, `not-or-elim`, propositional rewrites): exact proof
  if let some p ← timed "prop" (PropEngine.prove ps concl (splits := if unfoldable then 2 else 0)) then
    record step.rule "prop"
    return p
  -- propositional steps over large atoms (e.g., atoms in different but definitionally equal forms are
  -- identified by generalization): exact proof on the generalized statement
  if propositionalRules.contains step.rule && !(Local.sizeLe stmt 200) then
    if let some p ← timed "prop atoms" (propOnAtoms stmt) then
      record step.rule "prop atoms"
      return applyPremises p
  -- large equalities without premises (e.g., rewrites): congruence on the common structure, and tactics
  -- on the differences with their common subterms generalized
  if ps.isEmpty then
    if let some (_, a, b) := concl.eq? then
      if a.approxDepth.toNat > 8 || b.approxDepth.toNat > 8 then
        -- NOTE: a budget of tactic attempts on the differences, larger for the large statements (e.g., the many
        -- simplifications of a CEK evaluation under the conditions of its conditionals)
        let budget := if large then 24 else 6
        if let some p ← timed "local" (Local.diffEq (localProof cfg step.rule large) (← IO.mkRef budget) a b) then
          record step.rule "local"
          return ← mkExpectedTypeHint p concl
  -- theory lemmas over large terms: the subterms common to the literals are generalized (e.g., datatype
  -- lemmas `x = C (C.0 x) ∨ ¬ is-C x` over a large term `x`)
  if step.rule == "th-lemma" then
    -- the parts of the statement: premises and literals of the conclusion
    let parts := ps.map (·.1) ++ disjuncts concl (clauseSize step.concl)
    -- the generalization of the subterms common to the literals, and the one of the datatype atoms relating different
    -- terms (e.g., `¬ is-nil a → ¬ is-cons b → a = b → False`), attempted together
    let restE := (parts.extract 1 parts.size).foldl (fun acc l => mkAnd acc l) (mkConst ``True)
    -- Arithmetic clauses need their shared algebraic structure. Generalizing
    -- it as datatype atoms both loses these relations and runs an expensive
    -- case-analysis portfolio before the arithmetic tactics.
    let arith := step.attrs[0]? == some (.atom "arith")
    let common? ← if !arith && parts.size ≥ 2 then Local.generalizeCommon stmt restE parts[0]! else pure none
    let atoms? ← if arith then pure none else Local.generalizeDatatypeAtoms stmt
    let gens := (common?.toArray.map ("common", ·)) ++ (atoms?.toArray.map ("datatype atoms", ·))
    if !gens.isEmpty then
      let r ← timed "datatype" (proveClosedFirst cfg (gens.map fun (_, g, _) => ("datatype", g)))
      if let some (k, pf, method) := r then
        let (what, _, vals) := gens[k]!
        record step.rule s!"{method} ({what})"
        return applyPremises (mkAppN pf vals)
      if (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
        if let some (g, _) := common? then debugLog m!"th-lemma (common) failed: {← dagString g}"
    -- arithmetic lemmas over large atoms: the atoms are generalized
    if stmt.approxDepth.toNat > 8 then
      if let some (g, vals) ← Local.generalizeAtoms stmt then
        if let some (pf, method) ← proveClosed cfg step.rule g then
          record step.rule s!"{method} (atoms)"
          return applyPremises (mkAppN pf vals)
  if large then throwError "tactics are not applied to large statements"
  if let some (pf, method) ← timed "tactics" (proveClosed cfg step.rule stmt) then
    record step.rule method
    return applyPremises pf
  -- datatype lemmas over variables (e.g., `x = C (C.0 x) ∨ ¬ is-C x`): case analyses
  -- NOTE: only for statements with testers or selectors (case analyses of the interpretation); the other
  -- tactics of the portfolio were tried above
  let env ← getEnv
  let hasCases := (stmt.find? fun s => match s.getAppFn with
    | .const n _ => isCasesOnRecursor env n
    | _ => false).isSome
  if step.rule == "th-lemma" && hasCases then
    if let some (pf, method) ← timed "datatype" (proveClosed cfg "datatype" stmt) then
      record step.rule s!"{method} (datatype)"
      return applyPremises pf
  throwError "tactics failed"

/-- Instantiate the universally quantified proof `h` with `ts`, coercing arguments when necessary. -/
partial def instantiateWithCoercion (h : Expr) (ts : Array Expr) : MetaM Expr := do
  let mut p := h
  for t in ts do
    let ty ← whnf (← inferType p)
    let .forallE _ d _ _ := ty | throwError "quant-inst: too many instantiations"
    p := mkApp p (← coerce t (← inferType t) d)
  return p

end

/-- Steps that can only be replayed in a scope: steps depending on hypotheses that are not discharged
    (by `lemma` or `subproof`), and steps below binders (premises of `proof-bind`, `bind`, `sko_ex`,
    `sko_forall`). A Z3 `lemma` discharges the hypotheses whose negation is one of its literals (matched on
    shared term objects), an Alethe `subproof` the assumptions it lists. -/
def scopedSteps (p : Proof) : Array Bool := Id.run do
  let n := p.steps.size
  let hyps := openHypotheses p
  let mut inScope := hyps.map (!·.isEmpty)
  -- subtrees below binders
  let mut todo : Array Nat := #[]
  for i in [:n] do
    let s := p.steps[i]!
    if ["proof-bind", "bind", "sko_ex", "sko_forall"].contains s.rule then todo := todo ++ s.premises
  while !todo.isEmpty do
    let j := todo.back!
    todo := todo.pop
    if inScope[j]! && p.steps[j]!.rule != "proof-bind" then continue
    inScope := inScope.set! j true
    todo := todo ++ p.steps[j]!.premises
  return inScope

/-- Replay the reachable steps that don't need a scope in increasing order (premises precede the steps
    using them), such that the recursion depth of `replay` stays bounded on deep proofs. Failures are
    recorded (and reported when replaying the root). -/
def prepass : ReplayM Unit := do
  let p := (← read).proof
  let reach := p.reachable
  let inScope := scopedSteps p
  withReader (fun c => { c with prepass := true }) do
    for i in [:p.root] do
      if reach[i]! && !inScope[i]! then
        try discard <| replay i catch _ => pure ()
  -- failures of the prepass are retried by the replay from the root (with direct fallbacks)
  modify fun s => { s with failed := {} }

end Blaster.Reconstruct.SmtProof
