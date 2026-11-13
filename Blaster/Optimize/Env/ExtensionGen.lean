import Lean
import Blaster.Optimize.Env.ExprBuilder
import Blaster.Optimize.Hypotheses
import Blaster.Optimize.Rewriting.OptimizeApp

/-!
# Generation of optimization functions from theorems/axioms

Given a theorem (or a `Prop` axiom) of the form

  `∀ x₁ … xₙ, P₁ → … → Pₖ → lhs = rhs`

this module generates (and compiles) a Lean definition of type

  `(f : Expr) → (args : Array Expr) → TranslateEnvT (Option Expr)`

that, given the effective arguments of the head constant of `lhs`:
  - matches them structurally against the arguments of `lhs` (binding `x₁ … xₙ`),
  - checks that every premise `Pᵢ` is in the hypothesis map (`hypMapContains`),
  - builds `rhs` with the `ExprBuilder` operators (so that the result is hash-consed),
  - optionally sets the `restart` flag.

The conclusion may also be:
  - `lhs ↔ rhs` (handled as `lhs = rhs`)
  - `¬ p`        (handled as `p = False`)
  - `p`          (handled as `p = True`)

The theorem is expected to be written in the normalized form used by the optimizer
(e.g., `Nat.add a b` rather than `a + b`); only `Nat`, `Int` and `String` literals are normalized
(`OfNat.ofNat Nat n _` ==> `Expr.lit n`, `OfNat.ofNat Int n _` ==> `Int.ofNat (Expr.lit n)`, `-n` ==> `Int.negSucc (n - 1)`).
-/

open Lean Meta Elab Blaster.Optimize
open Lean.Parser.Term (doSeqItem matchAltExpr)

namespace Blaster.ThmOptFn

/-- Parameters of the optimization function to be generated. -/
structure Config where
  /-- Name of the theorem/axiom. -/
  thmName : Name
  /-- Type of the theorem/axiom. -/
  thmType : Expr
  /-- When `true`, `setRestart` is NOT called before returning the rewritten term. -/
  noRestart : Bool := false
  /-- Head constant specified in the attribute (if any); it must be the head of the lhs. -/
  headOverride? : Option Name := none

/-- Result of the generation. -/
structure Result where
  /-- Head constant of the lhs, i.e., the target of the generated optimization function. -/
  head : Name
  /-- Name of the generated (and compiled) definition. -/
  declName : Name
  /-- Generated source (for tracing purposes). -/
  code : Term


/-- Given a theorem (or a `Prop` axiom) of the form `∀ x₁ … xₙ, P₁ → … → Pₖ → lhs = rhs`,
    annotated lhs with `__Blaster.rewriteLhs`.
-/
def tagRewriteLhs (thmExpr : Expr) : MetaM Expr := do
  forallTelescope thmExpr fun xs concl =>
    match eq? concl with
    | some (psort, e1, e2) =>
       let concl' := mkApp3 concl.getAppFn psort (tagAsRewriteLhs e1) e2
       mkForallFVars xs concl'
    | none => mkForallFVars xs concl

/-! ## Normalization hook

The optimizer modules sit above this module in the import graph, so the normalization of the
theorem components is delegated to hooks installed at initialization time (see `Blaster.Optimize.Basic`).
-/

abbrev TheoremNormalizer := Expr → MetaM Expr

initialize theoremNormalizerRef : IO.Ref (Option TheoremNormalizer) ← IO.mkRef none

def normalizeTheorem (thmExpr : Expr) : MetaM Expr := do
  let thmExpr ← if thmExpr.hasMVar then instantiateMVars thmExpr else pure thmExpr
  match ← theoremNormalizerRef.get with
  | some f => f thmExpr
  | none => throwError "blaster: normalization hook not initialized"

/-! ## Code generation monad -/

structure GenState where
  /-- Pattern variables bound so far (theorem binder ↦ generated identifier). -/
  bound : FVarIdMap Ident := {}
  /-- Universe level parameters recoverable from the lhs (param name ↦ extraction term). -/
  levels : NameMap Term := {}
  /-- Identifiers already generated. -/
  used : NameSet := {}
  /-- Equality checks to perform for non-linear occurrences of pattern variables. -/
  eqChecks : Array (Ident × Ident) := #[]
  /-- Level checks to perform for non-linear occurrences of universe level parameters:
      level bound by the pattern ↦ expected level (built from the recovered parameters). -/
  levelChecks : Array (Term × Level) := #[]
  /-- Constant-name checks: identifier bound by the pattern ↦ expected name.
      Names are not matched structurally (a `Name` literal in a pattern is compiled into a nested
      match on each of its components, which makes the generated C code exceed clang's nesting
      limit on deep patterns); they are compared with `==` after the structural match. -/
  nameChecks : Array (Ident × Name) := #[]
  /-- Literal checks: identifier bound by the pattern ↦ expected literal (same reason). -/
  litChecks : Array (Ident × Literal) := #[]
  /-- `let` bindings emitted so far (in order). -/
  items : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
  /-- Sub-expressions already built (for sharing). -/
  built : ExprMap Ident := {}
  /-- Counter for fresh names. -/
  counter : Nat := 0

abbrev GenM := StateRefT GenState MetaM

/-- Return a fresh identifier based on `base` that does not clash with any global constant,
    nor with a previously generated identifier.
-/
def freshIdent (base : Name) : GenM Ident := do
  let base := base.eraseMacroScopes
  let base := if base.isAnonymous || base.hasNum then `x else Name.mkSimple base.toString
  let mut candidate := base
  let mut i := 0
  repeat
    let st ← get
    if !st.used.contains candidate && (← resolveGlobalName candidate).isEmpty then break
    i := i + 1
    candidate := Name.mkSimple s!"{base}_{i}"
  modify fun st => { st with used := st.used.insert candidate }
  return mkIdent candidate

/-- Emit `let x ← rhs` and return `x`. -/
def emit (base : Name) (rhs : Term) : GenM Ident := do
  let x ← freshIdent base
  let item ← `(doSeqItem| let $x:ident ← $rhs:term)
  modify fun st => { st with items := st.items.push item }
  return x

/-- Emit a `doElem`. -/
def emitElem (e : TSyntax `doElem) : GenM Unit := do
  let item ← `(doSeqItem| $e:doElem)
  modify fun st => { st with items := st.items.push item }

/-! ## Patterns (lhs) -/

/-- Return `true` when `l` is of the form `u + k` with `u` a level parameter not recorded yet. -/
def isUnrecordedLevelParam (l : Level) : GenM Bool := do
  match l with
  | .param u => return !(← get).levels.contains u
  | .succ l => isUnrecordedLevelParam l
  | _ => return false

/-- Record the universe level parameter of `l` (if any), given the term `t` bound to the level matched
    at runtime: `u` is recovered as `t` for `u`, and as the `k`-th predecessor of `t` for `u + k` (a check
    that the matched level is a successor is emitted, e.g., `Type u` must not match `Prop`).
    Levels of the form `max`/`imax` are not inverted. -/
partial def recordLevelParam (t : Term) (l : Level) : GenM Unit := do
  match l with
  | .param u =>
      unless (← get).levels.contains u do
        modify fun st => { st with levels := st.levels.insert u t }
  | .succ l =>
      if ← isUnrecordedLevelParam l then
        let d ← freshIdent `ld
        emitElem (← `(doElem| let some $d := Level.dec $t | return none))
        recordLevelParam d l
  | _ => return ()

/-- Given the term `t` bound to the level matched at runtime for the level `l` of the lhs: record the
    level parameter of `l` when it is not recovered yet (see `recordLevelParam`), otherwise defer an
    equivalence check between `t` and `l` (see `GenState.levelChecks`), e.g., the two occurrences of `u`
    in `f (Type u) (Type u)` must be matched by the same level. -/
def bindLevel (t : Term) (l : Level) : GenM Unit := do
  if ← isUnrecordedLevelParam l then recordLevelParam t l
  else if l.hasParam then
    modify fun st => { st with levelChecks := st.levelChecks.push (t, l) }

/-- Pattern for a universe level (level parameters/meta variables are matched by `_`). -/
partial def mkLevelPat (l : Level) : GenM Term := do
  match l with
  | .zero => `(Level.zero)
  | .succ l => `(Level.succ $(← mkLevelPat l))
  | .max l₁ l₂ => `(Level.max $(← mkLevelPat l₁) $(← mkLevelPat l₂))
  | .imax l₁ l₂ => `(Level.imax $(← mkLevelPat l₁) $(← mkLevelPat l₂))
  | .param .. | .mvar .. => `(_)

/-- Generate the match pattern for `e` (an argument of the lhs). -/
partial def mkPat (e : Expr) : GenM Term := do
  match e with
  | .mdata _ b => mkPat b
  | .fvar id =>
      match (← get).bound.get? id with
      | some x =>
          -- non linear occurrence: bind a fresh identifier and check equality afterwards
          let x' ← freshIdent x.getId
          modify fun st => { st with eqChecks := st.eqChecks.push (x, x') }
          return x'
      | none =>
          let decl ← id.getDecl
          let x ← freshIdent decl.userName
          modify fun st => { st with bound := st.bound.insert id x }
          return x
  | .lit l =>
      -- bind the literal and compare it afterwards (see `GenState.litChecks`)
      let x ← freshIdent `lit
      modify fun st => { st with litChecks := st.litChecks.push (x, l) }
      `(Expr.lit $x)
  | .const n ls =>
      -- bind the name and compare it afterwards (see `GenState.nameChecks`)
      let c ← freshIdent `c
      modify fun st => { st with nameChecks := st.nameChecks.push (c, n) }
      if ls.any Level.hasParam then
        -- bind the level list so that level parameters can be reused when building the rhs
        let lv ← freshIdent `lv
        let mut i := 0
        for l in ls do
          bindLevel (← `($lv[$(quote i)]!)) l
          i := i + 1
        `(Expr.const $c $lv)
      else `(Expr.const $c _)
  | .app f a => `(Expr.app $(← mkPat f) $(← mkPat a))
  | .sort l =>
      if l.hasParam then
        -- bind the level of `Sort u` / `Type u` so that `u` can be reused when building the rhs
        let sl ← freshIdent `sl
        bindLevel sl l
        `(Expr.sort $sl)
      else `(Expr.sort $(← mkLevelPat l))
  | .lam _ t b _ => `(Expr.lam _ $(← mkPat t) $(← mkPat b) _)
  | .forallE _ t b _ => `(Expr.forallE _ $(← mkPat t) $(← mkPat b) _)
  | .letE _ t v b _ => `(Expr.letE _ $(← mkPat t) $(← mkPat v) $(← mkPat b) _)
  | .proj n i s => `(Expr.proj $(quote n) $(quote i) $(← mkPat s))
  | .bvar i => `(Expr.bvar $(quote i))
  | .mvar .. => throwError "blaster: unexpected meta variable in theorem statement: {e}"

/-! ## Builders (premises and rhs) -/

/-- Term for a universe level; level parameters must be recoverable from the lhs. -/
partial def mkLevelTerm (l : Level) : GenM Term := do
  match l with
  | .zero => `(Level.zero)
  | .succ l => `(Level.succ $(← mkLevelTerm l))
  | .max l₁ l₂ => `(Level.max $(← mkLevelTerm l₁) $(← mkLevelTerm l₂))
  | .imax l₁ l₂ => `(Level.imax $(← mkLevelTerm l₁) $(← mkLevelTerm l₂))
  | .param u =>
      match (← get).levels.get? u with
      | some t => return t
      | none => throwError "blaster: universe level parameter `{u}` cannot be recovered from the lhs"
  | .mvar .. => throwError "blaster: unexpected universe level meta variable"

/-- Return `true` when `l` contains a `max` or an `imax`. -/
partial def containsMaxOrIMax (l : Level) : Bool :=
  match l with
  | .max .. | .imax .. => true
  | .succ l => containsMaxOrIMax l
  | _ => false

/-- Same as `mkLevelTerm`, but the built level is normalized when `l` contains a `max`/`imax`
    (e.g., `max u v` instantiated with `u := 0` and `v := 0` must be `0`, as elaborated by Lean). -/
def mkLevelTermNorm (l : Level) : GenM Term := do
  let t ← mkLevelTerm l
  if containsMaxOrIMax l then `(Level.normalize $t) else return t

def mkLevelsTerm (ls : List Level) : GenM Term := do
  let ts ← ls.toArray.mapM mkLevelTermNorm
  `([$ts,*])

/-- Constants for which a dedicated (cached) builder exists, with the expected universe levels.
    NOTE: This list needs to be in synch with CommonExpr and the mkXXX functions in `ExprBuilder`.
-/
def constBuilders : List (Name × List Level × Name) :=
  [ (``BEq.beq, [levelZero], ``mkBeqOp)
  , (``Blaster.dite', [levelOne], ``mkBlasterDIteOp)
  , (``Blaster.decide', [], ``mkBlasterDecideConst)
  , (``Bool, [], ``mkBoolType)
  , (``true, [], ``mkBoolTrue)
  , (``false, [], ``mkBoolFalse)
  , (``not, [], ``mkBoolNotOp)
  , (``or, [], ``mkBoolOrOp)
  , (``and, [], ``mkBoolAndOp)
  , (``Decidable, [], ``mkDecidableConst)
  , (``DecidableEq, [], ``mkDecidableEqConst)
  , (``Eq, [levelOne], ``mkEqOp)
  , (``Inhabited, [levelOne], ``mkInhabitedConst)
  , (``instBEqOfDecidableEq, [levelZero], ``mkInstBEqOfDecEq)
  , (``instDecidableEqNat, [], ``mkInstDecEqNat)
  , (``Int.instLTInt, [], ``mkInstLTInt)
  , (``instLTNat, [], ``mkInstLTNat)
  , (``Int, [], ``mkIntType)
  , (``Int.add, [], ``mkIntAddOp)
  , (``Int.ediv, [], ``mkIntEDivOp)
  , (``Int.emod, [], ``mkIntEModOp)
  , (``Int.fdiv, [], ``mkIntFDivOp)
  , (``Int.fmod, [], ``mkIntFModOp)
  , (``Int.mul, [], ``mkIntMulOp)
  , (``Int.neg, [], ``mkIntNegOp)
  , (``Int.negSucc, [], ``mkIntNegSucc)
  , (``Int.ofNat, [], ``mkIntOfNat)
  , (``Int.pow, [], ``mkIntPowOp)
  , (``Int.sub, [], ``mkIntSubOp)
  , (``Int.tdiv, [], ``mkIntTDivOp)
  , (``Int.tmod, [], ``mkIntTModOp)
  , (``Int.toNat, [], ``mkIntToNatOp)
  , (``LE.le, [levelZero], ``mkLeOp)
  , (``LT.lt, [levelZero], ``mkLtOp)
  , (``LT, [levelZero], ``mkLTConst)
  , (``LawfulBEq, [levelZero], ``mkLawfulBEqConst)
  , (``Nat.add, [], ``mkNatAddOp)
  , (``Nat.beq, [], ``natBeq)
  , (``Nat.ble, [], ``natBle)
  , (``Nat.blt, [], ``mkNatBltOp)
  , (``Nat.div, [], ``mkNatDivOp)
  , (``Nat.mod, [], ``mkNatModOp)
  , (``Nat.mul, [], ``mkNatMulOp)
  , (``Nat.pow, [], ``mkNatPowOp)
  , (``Nat.sub, [], ``mkNatSubOp)
  , (``Nat, [], ``mkNatType)
  , (``not_false, [], ``mkNotFalse)
  , (``And, [], ``mkPropAndOp)
  , (``False, [], ``mkPropFalse)
  , (``Not, [], ``mkPropNotOp)
  , (``Or, [], ``mkPropOrOp)
  , (``True, [], ``mkPropTrue)
  , (``String.mk, [], ``mkStringMk)
  , (``String, [], ``mkStringType)
  , (``True.intro, [], ``mkTrueIntro)
  , (``Decidable.decide, [], ``Blaster.Optimize.mkDecide)
  , (``of_decide_eq_true, [], ``mkOfDecideEqTrue)
  , (``of_decide_eq_false, [], ``mkOfDecideEqFalse)
  , (``Char.ofNat, [], ``mkCharOfNat)
  , (``Char.toNat, [], ``mkCharToNat)
  , (``Char, [], ``mkCharType)
  ]

/-- Builder call for the constant `n` with universe levels `ls`. -/
def mkConstTerm (n : Name) (ls : List Level) : GenM Term := do
  match constBuilders.find? (fun (c, ls', _) => c == n && ls' == ls) with
  | some (_, _, builder) => return mkCIdent builder
  | none => `(mkExpr (Expr.const $(quote n) $(← mkLevelsTerm ls)))

def mkBinderInfoTerm (bi : BinderInfo) : Term :=
  match bi with
  | .default => mkCIdent ``BinderInfo.default
  | .implicit => mkCIdent ``BinderInfo.implicit
  | .strictImplicit => mkCIdent ``BinderInfo.strictImplicit
  | .instImplicit => mkCIdent ``BinderInfo.instImplicit

/-- Emit the `let` bindings constructing `e` with the `ExprBuilder` operators and return
    the identifier bound to the result.
-/
partial def mkBuild (e : Expr) : GenM Ident := do
  if let some x := (← get).built.get? e then return x
  let x ← build
  modify fun st => { st with built := st.built.insert e x }
  return x
 where
  build : GenM Ident := do
    match e with
    | .mdata _ b => mkBuild b
    | .fvar id =>
        match (← get).bound.get? id with
        | some x => return x
        | none =>
            let decl ← id.getDecl
            throwError "blaster: variable `{decl.userName}` does not occur in the lhs of the theorem"
    | .lit (.natVal n) => emit `n (← `(mkNatLitExpr $(quote n)))
    | .lit (.strVal s) => emit `s (← `(mkStrLitExpr $(quote s)))
    | .bvar i => emit `bv (← `(mkBVarExpr $(quote i)))
    | .sort l =>
        if l.isZero then emit `prop (← `(mkPropType))
        else emit `sort (← `(mkSortExpr $(← mkLevelTermNorm l)))
    | .const n ls => emit `c (← mkConstTerm n ls)
    | .app .. => buildApp
    | .lam n t b bi =>
        let t ← mkBuild t
        let b ← mkBuild b
        emit `lam (← `(mkLambdaExpr $(quote n) $(mkBinderInfoTerm bi) $t $b))
    | .forallE n t b bi =>
        let t ← mkBuild t
        let b ← mkBuild b
        emit `pi (← `(mkForallExpr $(quote n) $(mkBinderInfoTerm bi) $t $b))
    | .letE n t v b nd =>
        let t ← mkBuild t
        let v ← mkBuild v
        let b ← mkBuild b
        emit `lt (← `(mkLetExpr $(quote n) $t $v $b $(quote nd)))
    | .proj n i s =>
        let s ← mkBuild s
        emit `proj (← `(mkProjExpr $(quote n) $(quote i) $s))
    | .mvar .. => throwError "blaster: unexpected meta variable in theorem statement: {e}"

  buildApp : GenM Ident := do
    let f := e.getAppFn
    let args := e.getAppArgs
    let fx ← mkBuild f
    let xs ← args.mapM mkBuild
    let rhs ← `(optimizeAppExt $fx #[$xs,*])
    emit `app rhs

/-! ## Main generation -/

/-- Split the conclusion of the theorem into `(lhs, rhs)` (see module documentation). -/
def splitConclusion (concl : Expr) : MetaM (Expr × Expr) := do
  match concl.getAppFn, concl.getAppArgs with
  | .const ``Eq _, #[_, lhs, rhs] => return (lhs.consumeMData, rhs)
  | .const ``Iff _, #[lhs, rhs] => return (lhs, rhs)
  | .const ``Not _, #[p] => return (p, mkConst ``False)
  | _, _ => return (concl, mkConst ``True)

/-- Unique name for the optimization function generated from theorem `thm`. -/
def mkOptFnName (thm : Name) : Name :=
 match thm with
 | .str p s => Name.str p s!"blaster_opt_{s}"
 | _ => thm ++ `blaster_opt

/-- Remove macro scopes from identifiers (for readable traces). -/
partial def eraseSyntaxMacroScopes : Syntax → Syntax
  | .ident info ss val pre => .ident info ss val.eraseMacroScopes pre
  | .node info k args => .node info k (args.map eraseSyntaxMacroScopes)
  | s => s

/-- Term of type `TranslateEnvT Bool` for an arbitrary premise. -/
partial def mkHypCheck (p : Expr) : GenM Term := do
  if let some (a, b) := propAnd? p then
    `($(← mkHypCheck a) <&&> $(← mkHypCheck b))
  else if let some (a, b) := propOr? p then
    `($(← mkHypCheck a) <||> $(← mkHypCheck b))
  else
    let hp ← mkBuild p
    `(isTruePremise $hp)

def generateHyp (p : Expr) : GenM Unit := do
  if isTrueExpr p then return () -- skip true premises
  else
    emitElem (← `(doElem| if !(← $(← mkHypCheck p)) then return none))


/-- Generate the source of the optimization function for the given theorem.
    Returns the head constant of the lhs, and the generated `fun` term.
-/
def generateCode (cfg : Config) : MetaM (Option (Name × Term)) := do
  forallTelescope cfg.thmType fun xs concl => do
    -- classify binders: premises (proofs) vs pattern variables
    let mut premises : Array (Expr × Expr) := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then premises := premises.push (x, t)
    let (lhs, rhs) ← splitConclusion concl
    if exprEq lhs rhs then return none
    let .const head _ := lhs.getAppFn
      | throwError "blaster: the lhs of `{cfg.thmName}` must be an application of a constant, but got {lhs}"
    if let some h := cfg.headOverride? then
      unless h == head do
        throwError "blaster: the head of the lhs of `{cfg.thmName}` is `{head}`, not `{h}`"
    -- Why do we need to do this ???
    for (h, _) in premises do
      if lhs.containsFVar h.fvarId! || rhs.containsFVar h.fvarId! then
        throwError "blaster: proof variable `{← h.fvarId!.getUserName}` must not occur in the conclusion of `{cfg.thmName}`"
    let args := lhs.getAppArgs
    let argsId := mkIdent `args
    let fId := mkIdent `_f
    let (body, _) ← (do
        modify fun st => { st with used := st.used.insert `args |>.insert `_f }
        -- patterns for the arguments of the lhs
        let mut argLets : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
        let mut discrs : Array Term := #[]
        let mut pats : Array Term := #[]
        let mut i := 0
        for a in args do
          let discr ← `($argsId[$(quote i)]!)
          let pat ← mkPat a
          if a.consumeMData.isFVar then
            -- bind pattern variables with `let` (non-linear occurrences are checked afterwards)
            argLets := argLets.push (← `(doSeqItem| let $(⟨pat⟩):ident := $discr))
          else
            discrs := discrs.push discr
            pats := pats.push pat
          i := i + 1
        -- universe level parameters not occurring in a constant or a sort of the arguments are
        -- recovered from the head expression `_f` (e.g., `u` in `@box.{u} α x = @some.{u} α x`,
        -- where `α : Type u` is a pattern variable)
        let .const _ hls := lhs.getAppFn | unreachable!
        if ← hls.anyM isUnrecordedLevelParam then
          let flv ← freshIdent `flv
          emitElem (← `(doElem| let Expr.const _ $flv := $fId | return none))
          let mut j := 0
          for l in hls do
            bindLevel (← `($flv[$(quote j)]!)) l
            j := j + 1
        -- non-linear occurrences of universe level parameters
        for (t, l) in (← get).levelChecks do
          emitElem (← `(doElem| if !(Level.isEquiv $t $(← mkLevelTerm l)) then return none))
        -- constant names and literals of the patterns
        for (c, n) in (← get).nameChecks do
          emitElem (← `(doElem| if $c != $(quote n) then return none))
        for (x, l) in (← get).litChecks do
          let lt ← match l with
            | .natVal n => `(Literal.natVal $(quote n))
            | .strVal s => `(Literal.strVal $(quote s))
          emitElem (← `(doElem| if $x != $lt then return none))
        -- non-linear occurrences
        for (x, x') in (← get).eqChecks do
          emitElem (← `(doElem| if !(exprEq $x $x' || Expr.eqv $x $x') then return none))
        -- premises
        for (_, p) in premises do
          generateHyp p
        -- rhs
        let r ← mkBuild rhs
        if !cfg.noRestart then emitElem (← `(doElem| setRestart))
        emitElem (← `(doElem| return some $r))
        let items := (← get).items
        let inner : Array (TSyntax ``Lean.Parser.Term.doSeqItem) ←
          if discrs.isEmpty then pure items
          else do
            let rhs ← `(do $items:doSeqItem*)
            let wilds ← discrs.mapM fun _ => `(_)
            let alt ← `(matchAltExpr| | $[$pats:term],* => $rhs)
            let dflt ← `(matchAltExpr| | $[$wilds:term],* => return none)
            let m ← `(match $[$discrs:term],* with $alt:matchAlt $dflt:matchAlt)
            pure #[← `(doSeqItem| $m:term)]
        let sizeCheck ← `(doSeqItem| if ($argsId).size != $(quote args.size) then return none)
        let items := #[sizeCheck] ++ argLets ++ inner
        `(fun ($fId:ident : Expr) ($argsId:ident : Array Expr) => do $items:doSeqItem*)
      : GenM Term).run {}
    return (head, body)

/-- Generate and compile the optimization function for the given theorem.
    `optFnType` is the expected type of optimization functions (i.e., `Blaster.OptFn`).
    Return `none` when the theorem is already handled natively by the Blaster, i.e., theorem normalizes to `True`
    Trigger an error when theorem normalizes to `False`.
-/
def generate (cfg : Config) (optFnType : Expr) : MetaM (Option Result) := do
  let thmType ← normalizeTheorem (← tagRewriteLhs cfg.thmType)
  if isTrueExpr thmType then return none
  if isFalseExpr thmType then throwError "blaster: theorem {cfg.thmName} is unsound"
  if let some (head, code) ← generateCode {cfg with thmType := thmType} then
    let value ← Term.TermElabM.run' do
      let v ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize code (some optFnType)
      instantiateMVars v
    if value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "blaster: failed to elaborate the optimization function generated for `{cfg.thmName}`:{indentD code}"
    let declName := mkOptFnName cfg.thmName
    addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe declName [] optFnType value .opaque))
    return some { head, declName, code := ⟨eraseSyntaxMacroScopes code⟩ }
  else return none
end Blaster.ThmOptFn
