import Lean.Util.ShareCommon
import Blaster.Smt.Syntax

/-!
# Sharing-preserving SMT emission (SharingBlowup Pathology A)

`SmtTerm` values are DAGs in memory (`translateCache` dedups), but the
printers (`toString`/`emit`) walk the TREE: query text doubles per sharing
level. `SmtTerm.shareLets` binds every subterm that occurs ≥ 2 times (by
pointer identity, after `Lean.ShareCommon.shareCommon`) and prints as
≥ `minSize` nodes in an SMT `(let ((s e)) …)` prefix. Z3 parses `let` by
substitution into its internally hash-consed AST, so the solver side is
unaffected (measured flat Solve times in Tests/IssuesToSolve/SharingBlowup.lean).

v1 scoping rule (conservative): a subterm mentioning ANY symbol bound
anywhere inside the term (forall/exists/lambda/let binders) is never lifted —
it might not be closed at the root. Goals are skolemized before translation,
so the validator/BMC shapes are quantifier-free where the blowup lives.

All walks are pointer-keyed (`ptrAddrUnsafe`): structural hashing/equality on
`SmtTerm` would itself walk the tree and reintroduce the exponential cost.
-/

namespace Blaster.Smt

/-- Default minimum print-size (in nodes) for a shared subterm to earn a
    `let` binding — below it, duplicated text is cheaper than the binding. -/
def shareLetsMinSize : Nat := 16

/-- Saturation cap for subterm size accounting (sizes only gate the
    `minSize` threshold; exact big values are useless). -/
private def sizeCap : Nat := 100000

private def identSymbol : SmtQualifiedIdent → SmtSymbol
  | .SimpleIdent nm => nm
  | .QualifiedIdent nm _ => nm

/-- SMT identifier identity is independent of the Lean symbol constructor.
    Both representations can print the same identifier (Issue232). -/
private def symbolKey : SmtSymbol → String
  | .NormalSymbol s => s
  | .ReservedSymbol s =>
      -- A quoted SMT token and its unquoted spelling denote the same name.
      if s.startsWith "|" && s.endsWith "|" && s.length ≥ 2 then
        String.mk ((s.toList.drop 1).dropLast)
      else s

/-! ## Pass 0 — collect binder symbols and all used symbol strings -/

private structure ScanSt where
  visited : Std.HashSet USize := ∅
  bound   : Std.HashSet String := ∅
  used    : Std.HashSet String := ∅

private def scanSym (s : SmtSymbol) : StateM ScanSt Unit :=
  modify fun st => { st with used := st.used.insert (symbolKey s) }

private def scanBinder (s : SmtSymbol) : StateM ScanSt Unit := do
  scanSym s
  modify fun st => { st with bound := st.bound.insert (symbolKey s) }

private unsafe def scanTerm : SmtTerm → StateM ScanSt Unit
  | t => do
    let p := ptrAddrUnsafe t
    if (← get).visited.contains p then return ()
    modify fun st => { st with visited := st.visited.insert p }
    match t with
    | .SmtIdent nm => scanSym (identSymbol nm)
    | .AppTerm nm args => do
        scanSym (identSymbol nm)
        args.forM scanTerm
    | .LetTerm bs body => do
        bs.forM fun (n, val) => do scanBinder n; scanTerm val
        scanTerm body
    | .ForallTerm bs body | .ExistsTerm bs body | .LambdaTerm bs body => do
        bs.forM fun (n, _) => scanBinder n
        scanTerm body
    | .AnnotatedTerm t' annot => do
        scanTerm t'
        -- Deliberate asymmetry: this pass DOES descend into `:pattern`
        -- payloads (so their symbols land in `used`, keeping generated `$sN`
        -- names from colliding with a trigger term), but `countTerm` and
        -- `rebuildTerm` below never do — annotation payloads are never
        -- counted, never lifted into a `let`, and never rewritten in place,
        -- so a `$sN` reference can never end up inside a `:pattern`/`:named`.
        annot.forM fun
          | .Pattern ps => ps.forM scanTerm
          | .Named n => scanSym n
          | .Qid n => scanSym n
    | _ => return ()

/-! ## Pass 1 — per-pointer occurrence count, taint, saturating size -/

private structure CountSt where
  counts  : Std.HashMap USize Nat := ∅
  tainted : Std.HashMap USize Bool := ∅
  sizes   : Std.HashMap USize Nat := ∅

/-- Returns `(tainted, size)`. Counts every arrival; recurses only on the
    first — O(DAG). Binder nodes and annotated nodes are self-tainted (never
    shared themselves); their untainted subterms remain shareable. -/
private unsafe def countTerm (bound : Std.HashSet String) :
    SmtTerm → StateM CountSt (Bool × Nat)
  | t => do
    let p := ptrAddrUnsafe t
    if let some n := (← get).counts.get? p then
      modify fun st => { st with counts := st.counts.insert p (n + 1) }
      let st ← get
      return (st.tainted.getD p true, st.sizes.getD p 1)
    modify fun st => { st with counts := st.counts.insert p 1 }
    let (tainted, size) ← do
      match t with
      | .NumTerm _ | .DecTerm _ | .BoolTerm _ | .BinTerm _ | .HexTerm _ | .StrTerm _ =>
          pure (false, 1)
      | .SmtIdent nm => pure (bound.contains (symbolKey (identSymbol nm)), 1)
      | .AppTerm nm args => do
          let mut tainted := bound.contains (symbolKey (identSymbol nm))
          let mut size := 1
          for a in args do
            let (ta, sa) ← countTerm bound a
            tainted := tainted || ta
            size := Nat.min sizeCap (size + sa)
          pure (tainted, size)
      | .LetTerm bs body => do
          let mut size := 1
          for (_, val) in bs do
            let (_, sv) ← countTerm bound val
            size := Nat.min sizeCap (size + sv)
          let (_, sb) ← countTerm bound body
          pure (true, Nat.min sizeCap (size + sb))
      | .ForallTerm _ body | .ExistsTerm _ body | .LambdaTerm _ body => do
          let (_, sb) ← countTerm bound body
          pure (true, Nat.min sizeCap (sb + 1))
      | .AnnotatedTerm t' _ => do
          let (_, st') ← countTerm bound t'
          pure (true, Nat.min sizeCap (st' + 1))
    modify fun st =>
      { st with tainted := st.tainted.insert p tainted, sizes := st.sizes.insert p size }
    return (tainted, size)

/-! ## Pass 2 — rebuild with `let` references, bindings in dependency order -/

private structure BuildSt where
  built    : Std.HashMap USize SmtTerm := ∅
  bindings : Array (SmtSymbol × SmtTerm) := #[]
  nextIdx  : Nat := 0

/-- Next `$sN` not colliding with any symbol already in the term. Bounded
    probe: at most `used.size + 1` candidates can collide. -/
private def freshSym (used : Std.HashSet String) : StateM BuildSt SmtSymbol := do
  let start := (← get).nextIdx
  for i in [start : start + used.size + 1] do
    if !used.contains s!"$s{i}" then
      modify fun st => { st with nextIdx := i + 1 }
      return .NormalSymbol s!"$s{i}"
  -- Unreachable by pigeonhole (at most `used.size` of the `used.size + 1`
  -- candidates above can collide) — a total fallback would have to return a
  -- name that might collide, which is worse than crashing on a broken invariant.
  panic! "freshSym: pigeonhole exhausted"

private unsafe def rebuildTerm (cst : CountSt) (used : Std.HashSet String)
    (minSize : Nat) : SmtTerm → StateM BuildSt SmtTerm
  | t => do
    let p := ptrAddrUnsafe t
    if let some r := (← get).built.get? p then return r
    let node ← match t with
      | .AppTerm nm args =>
          pure (SmtTerm.AppTerm nm (← args.mapM (rebuildTerm cst used minSize)))
      | .LetTerm bs body =>
          pure (SmtTerm.LetTerm
            (← bs.mapM fun (n, val) => do pure (n, ← rebuildTerm cst used minSize val))
            (← rebuildTerm cst used minSize body))
      | .ForallTerm bs body =>
          pure (SmtTerm.ForallTerm bs (← rebuildTerm cst used minSize body))
      | .ExistsTerm bs body =>
          pure (SmtTerm.ExistsTerm bs (← rebuildTerm cst used minSize body))
      | .LambdaTerm bs body =>
          pure (SmtTerm.LambdaTerm bs (← rebuildTerm cst used minSize body))
      | .AnnotatedTerm t' annot =>
          pure (SmtTerm.AnnotatedTerm (← rebuildTerm cst used minSize t') annot)
      | leaf => pure leaf
    let share := cst.counts.getD p 0 ≥ 2
              && !(cst.tainted.getD p true)
              && cst.sizes.getD p 0 ≥ minSize
    let r ← if share then do
        let sym ← freshSym used
        modify fun st => { st with bindings := st.bindings.push (sym, node) }
        pure (SmtTerm.SmtIdent (.SimpleIdent sym))
      else
        pure node
    modify fun st => { st with built := st.built.insert p r }
    return r

private unsafe def shareLetsUnsafe (t : SmtTerm) (minSize : Nat) : SmtTerm :=
  -- shareCommon guarantees maximal pointer sharing even for structurally
  -- equal subterms translation happened to build separately.
  let t := Lean.ShareCommon.shareCommon t
  let (_, scan) := (scanTerm t).run {}
  let (_, cst) := (countTerm scan.bound t).run {}
  let (body, bst) := (rebuildTerm cst scan.used minSize t).run {}
  if bst.bindings.isEmpty then t
  else
    -- bindings are recorded in postorder (dependencies first). Each gets its
    -- OWN single-binding `let` (nested, not one flat group), BECAUSE an SMT
    -- `let` group is parallel — bindings in one group cannot reference each
    -- other — so a later (shallower, dependent) binding must sit in the BODY
    -- of an earlier (deeper, depended-upon) one's `let`, never alongside it.
    bst.bindings.foldr (init := body) fun b acc => .LetTerm #[b] acc

/-- Bind every subterm occurring ≥ 2 times (pointer identity after
    `shareCommon`) and printing as ≥ `minSize` nodes in an SMT
    `(let ((s e)) …)` prefix, so emitted text is DAG-sized, not tree-sized.
    Subterms mentioning a symbol bound anywhere inside `t` are never lifted.
    Sound because an SMT `let` is definitionally its substituted body — the
    term-level `unsafe` below makes this safe constant OPAQUE to the kernel
    (no unfolding), implemented by the `unsafe` walker; it does not change
    what the function computes. -/
def SmtTerm.shareLets (t : SmtTerm) (minSize : Nat := shareLetsMinSize) : SmtTerm :=
  unsafe shareLetsUnsafe t minSize

/-- Apply `SmtTerm.shareLets` to the commands whose term payloads can blow
    up: asserts, define-fun bodies, and each body of a mutually recursive
    define-funs-rec block. -/
def SmtCommand.shareLets : SmtCommand → SmtCommand
  | .assertTerm t => .assertTerm t.shareLets
  | .defineFun isRec nm args rt body => .defineFun isRec nm args rt body.shareLets
  | .defineFunsRec decls bodies => .defineFunsRec decls (bodies.map (·.shareLets))
  | c => c

end Blaster.Smt
