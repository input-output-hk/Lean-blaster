import Blaster.Proof.Explore.Core

/-!
# Symbolic exploration: matching and anti-unification

Templates are states whose non-rootish variables are pattern variables.
Anti-unification keeps existing template parameters (it only splits a
parameter that meets inconsistent values), descends through any common
application head, and may expose constructors by bounded weak-head reduction.
-/
namespace Blaster.Proof.Explore
open Lean Meta

/-- Pattern variables of a template: its non-rootish free variables. -/
def patternVars (e : Expr) : ExM (Std.HashSet FVarId) := do
  let vars := (← get).vars
  return (collectFVars {} e).fvarIds.foldl (init := {}) fun s id =>
    if vars[id]?.any (·.rootish) then s else s.insert id

/-- Pattern variables that occur more than once in `e` (sharing-aware). Only
for these can skipping an equal subterm hide an inconsistent binding. -/
def multiOccurring (vars : Std.HashSet FVarId) (e : Expr) : Std.HashSet FVarId := Id.run do
  -- below[node] = pattern variables under it; a node reached twice doubles them
  let mut below : Std.HashMap Expr (Array FVarId) := {}
  let mut seenVar : Std.HashSet FVarId := {}
  let mut multi : Std.HashSet FVarId := {}
  let mut stack : Array (Expr × Bool) := #[(e, false)]
  while !stack.isEmpty do
    let (t, done) := stack.back!
    stack := stack.pop
    if !t.hasFVar then continue
    if !done then
      if let some vs := below[t]? then
        for v in vs do multi := multi.insert v
        continue
      match t with
      | .fvar id =>
        if vars.contains id then
          if seenVar.contains id then multi := multi.insert id
          seenVar := seenVar.insert id
          below := below.insert t #[id]
        else below := below.insert t #[]
      | .app f a => stack := stack.push (t, true) |>.push (a, false) |>.push (f, false)
      | .lam _ d b _ | .forallE _ d b _ => stack := stack.push (t, true) |>.push (b, false) |>.push (d, false)
      | .mdata _ b | .proj _ _ b => stack := stack.push (t, true) |>.push (b, false)
      | .letE _ d v b _ => stack := stack.push (t, true) |>.push (b, false) |>.push (v, false) |>.push (d, false)
      | _ => below := below.insert t #[]
    else
      let kids := match t with
        | .app f a => #[f, a]
        | .lam _ d b _ | .forallE _ d b _ => #[d, b]
        | .mdata _ b | .proj _ _ b => #[b]
        | .letE _ d v b _ => #[d, v, b]
        | _ => #[]
      let mut vs : Array FVarId := #[]
      for k in kids do
        for v in (below.getD k #[]) do
          unless vs.contains v do vs := vs.push v
      below := below.insert t vs
  return multi

/-- Can an equal subterm be skipped without checking its pattern variables? -/
@[inline] def skippable (multi : Std.HashSet FVarId) (t : Expr) : Bool :=
  !t.hasFVar || multi.isEmpty || !t.hasAnyFVar multi.contains

/-- Extend `bind` so that `pat` with its variables `vars` replaced is `tgt`;
`multi` are the variables occurring more than once in `pat` (`multiOccurring`). -/
partial def matchPat (vars multi : Std.HashSet FVarId) (pat tgt : Expr)
    (bind : Std.HashMap FVarId Expr) : Option (Std.HashMap FVarId Expr) := do
  if let .fvar id := pat then
    if vars.contains id then
      match bind[id]? with
      | some b => if b == tgt then return bind else none
      | none => return bind.insert id tgt
  if pat == tgt && skippable multi pat then return bind
  if !pat.hasFVar then none
  match pat, tgt with
  | .app f a, .app g b => do
    let bind ← matchPat vars multi f g bind
    matchPat vars multi a b bind
  | .proj n i x, .proj n' i' y => if n == n' && i == i' then matchPat vars multi x y bind else none
  | .mdata _ x, _ => matchPat vars multi x tgt bind
  | _, .mdata _ y => matchPat vars multi pat y bind
  | .lam _ t1 b1 _, .lam _ t2 b2 _ | .forallE _ t1 b1 _, .forallE _ t2 b2 _ => do
    let bind ← matchPat vars multi t1 t2 bind
    matchPat vars multi b1 b2 bind
  | _, _ => if pat == tgt then some bind else none

/-- Is `e` the constructor `C fs` with `fs` the canonical split fields of the
rootish variable `atom` (the value `atom` has on the path that split it)? -/
def isSplitOf (atom e : Expr) : ExM Bool := do
  let .fvar id := atom | return false
  unless (← get).vars[id]?.any (·.rootish) do return false
  let .const c _ := e.getAppFn | return false
  let some fs := (← get).splitVars[(id, c)]? | return false
  let args := e.getAppArgs
  return fs.size ≤ args.size && args.extract (args.size - fs.size) args.size == fs

/-- The state of an anti-unification (`lgg`). -/
structure LggState where
  /-- The holes so far: the two terms a hole generalizes, and its variable. -/
  holes : Array (Expr × Expr × Expr) := #[]
  /-- The value each pattern variable of the template met. -/
  seen : Std.HashMap FVarId Expr := {}
  /-- The pattern variables occurring more than once (`multiOccurring`). -/
  multi : Std.HashSet FVarId := {}
  /-- holes of function or type-former type: differing code or motives -/
  codeHoles : Nat := 0
  /-- template parameters the arriving path has decided facts about: never
  reused as a generalization (the new version would inherit those facts) -/
  noReuse : Std.HashSet FVarId := {}

/-- A closed numeral: a raw literal, `OfNat.ofNat _ n _`, or `Int.ofNat`,
`Int.negSucc` or negation of one. -/
partial def isNumeral (e : Expr) : Bool :=
  e.isRawNatLit ||
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit) ||
  ((e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1) && isNumeral e.appArg!) ||
  (e.isAppOfArity ``Neg.neg 3 && isNumeral e.appArg!)

/-- Anti-unify template body `a` (pattern variables `vars`) with `b`. -/
partial def lgg (vars : Std.HashSet FVarId) (a b : Expr) : StateRefT LggState ExM Expr := do
  -- an equal subterm is its own generalization, but its pattern variables
  -- must still be bound (to themselves) so later occurrences stay consistent
  if a == b && skippable (← get).multi a then return a
  if let .fvar id := a then
    if vars.contains id then
      match (← get).seen[id]? with
      | none => modify fun s => {s with seen := s.seen.insert id b}; return a
      | some b0 => if b0 == b then return a else pure ()
  let isVar := match a with | .fvar id => vars.contains id | _ => false
  if a == b && !isVar && !a.isApp then return a
  -- distinct numerals are generalized whole: descending into them would
  -- make a hole inside the literal (`OfNat.ofNat Int p _`)
  let numeral := !isVar && isNumeral a && isNumeral b
  -- a root against its own split (`r` / `head :: tail` of `r`): the same value
  if !isVar then
    if ← isSplitOf a b then return a
    if ← isSplitOf b a then return b
  if !isVar && !numeral && a.isApp && b.isApp && a.getAppFn == b.getAppFn && a.getAppFn.isConst &&
      a.getAppNumArgs == b.getAppNumArgs then
    let mut args := #[]
    for (u, v) in a.getAppArgs.zip b.getAppArgs do args := args.push (← lgg vars u v)
    return mkAppN a.getAppFn args
  if !isVar && !numeral then
    -- projections (structural recursion's `below` tables, `(T.rec … x).1 …`):
    -- the same projection of two terms generalizes inside it
    if let .proj n i x := a then
      if let .proj n' i' y := b then
        if n == n' && i == i' then return .proj n i (← lgg vars x y)
    if a.isApp && b.isApp && a.getAppFn.isProj && b.getAppFn.isProj &&
        a.getAppNumArgs == b.getAppNumArgs then
      let f ← lgg vars a.getAppFn b.getAppFn
      let mut args := #[]
      for (u, v) in a.getAppArgs.zip b.getAppArgs do args := args.push (← lgg vars u v)
      return mkAppN f args
  if !isVar && !numeral then
    let M := (← getThe Core).machine
    if let some a' ← inCtx (M.whnf a (some 2000)) then
      if let some b' ← inCtx (M.whnf b (some 2000)) then
        if (a' != a || b' != b) && (← inCtx (isCtorApp a')) && (← inCtx (isCtorApp b')) &&
            a'.getAppFn == b'.getAppFn && a'.getAppNumArgs == b'.getAppNumArgs then
          return ← lgg vars a' b'
  if let some (_, _, h) := (← get).holes.find? (fun (x, y, _) => x == a && y == b) then return h
  -- the state already holds a template parameter here (it comes from a more
  -- general version): that parameter is the generalization, so successive
  -- versions of a generalized segment share their parameters
  if let .fvar bid := b then
    let isParam := match (← getThe Core).vars[bid]? with
      | some {origin := .param, ..} => true
      | _ => false
    if isParam && !vars.contains bid && !(← get).noReuse.contains bid &&
        !(← get).holes.any (fun (_, y, _) => y == b) then
      modify fun s => {s with holes := s.holes.push (a, b, b)}
      return b
  let ty ← inCtx (inferType a)
  if ← inCtx (do let t ← whnf ty; pure (t.isForall || t.isSort)) then
    modify fun s => {s with codeHoles := s.codeHoles + 1}
  let h ← mkVar `p ty .param false
  modify fun s => {s with holes := s.holes.push (a, b, h)}
  return h

/-- `multiOccurring` of a template body, cached. -/
def templateMulti (vars : Std.HashSet FVarId) (tpl : Expr) : ExM (Std.HashSet FVarId) := do
  if let some m := (← get).multiCache[tpl]? then return m
  let m := multiOccurring vars tpl
  modify fun c => {c with multiCache := c.multiCache.insert tpl m}
  return m

/-- Anti-unify; returns the generalization and the number of new holes. -/
def antiUnify (tpl s : Expr) (extraVars : Array FVarId := #[]) : ExM (Expr × Nat) := do
  let vars := extraVars.foldl (·.insert ·) (← patternVars tpl)
  let (e, st) ← (lgg vars tpl s).run {multi := ← templateMulti vars tpl}
  return (e, st.holes.size)

/-- `antiUnify`, or `none` when the generalization needs a hole for differing
code (a function) or a motive: the two states are at different program points. -/
def antiUnifyData? (tpl s : Expr) (extraVars : Array FVarId := #[])
    (noReuse : Std.HashSet FVarId := {}) : ExM (Option (Expr × Nat)) := do
  let vars := extraVars.foldl (·.insert ·) (← patternVars tpl)
  let (e, st) ← (lgg vars tpl s).run {multi := ← templateMulti vars tpl, noReuse}
  if st.codeHoles > 0 then return none
  return some (e, st.holes.size)

/-- A value in constructor form, when it computes to one within a small budget. -/
def ctorFormOf (e : Expr) : ExM Expr := do
  if (← inCtx (isCtorApp e)) then return e
  let M := (← get).machine
  match ← inCtx (M.whnf e (some 2000)) with
  | some w => if (← inCtx (isCtorApp w)) then pure w else pure e
  | none => pure e

/-- Do `a` and `b` hold different constructors of a non-recursive inductive type
(with several constructors) at the same position? Such states come from sibling
branches of a case split; generalizing them would forget which branch the data
(and every value computed from it) belongs to. -/
partial def ctorConflict (a b : Expr) (fuel : Nat := 100000) (allowRec : Bool := false) : ExM Bool := do
  let env ← getEnv
  let fuelRef ← IO.mkRef fuel
  -- a conflict found through a computed value's constructor form (`[]` against
  -- `mkCons x []`) separates a producer's cases, not a growing list: it counts
  -- for recursive types too
  let viaForm ← IO.mkRef false
  -- different constructors of a type with several, non-recursive unless
  -- allowed; Booleans are left out: two states holding different Booleans
  -- usually hold different results of the same check, which a template
  -- generalizes
  let distinct (ca cb : Name) : ExM Bool := do
    if ca == cb then return false
    let (some (.ctorInfo ia), some (.ctorInfo ib)) := (env.find? ca, env.find? cb) | return false
    unless ia.induct == ib.induct && ia.induct != ``Bool do return false
    let some (.inductInfo ind) := env.find? ia.induct | return false
    return (!ind.isRec || allowRec || (← viaForm.get)) && ind.ctors.length > 1
  let rec go (a b : Expr) : ExM Bool := do
    if a == b then return false
    let f ← fuelRef.get
    if f == 0 then return false
    fuelRef.set (f - 1)
    -- a constructor against a computed value (`[]` against `mkCons x []`):
    -- the value's constructor form decides
    let (a, b) ← do
      let ha := a.getAppFn
      let hb := b.getAppFn
      if ha.isConst && hb.isConst && ha != hb then
        let ca ← inCtx (isCtorApp a)
        let cb ← inCtx (isCtorApp b)
        if ca != cb then
          let a' ← ctorFormOf a
          let b' ← ctorFormOf b
          if a' != a || b' != b then viaForm.set true
          pure (a', b')
        else pure (a, b)
      else pure (a, b)
    match a, b with
    | .app .., .app .. =>
      let (.const ca _, .const cb _) := (a.getAppFn, b.getAppFn) | return false
      if ca != cb then return ← distinct ca cb
      let xs := a.getAppArgs
      let ys := b.getAppArgs
      if xs.size != ys.size then return false
      for (x, y) in xs.zip ys do
        if ← go x y then return true
      return false
    | .const ca _, .const cb _ => distinct ca cb
    | .const ca _, .app .. | .app .., .const ca _ =>
      -- a nullary constructor against an applied one of the same type
      let other := if a.isApp then a else b
      let .const cb _ := other.getAppFn | return false
      distinct ca cb
    | .mdata _ x, _ => go x b
    | _, .mdata _ y => go a y
    | _, _ => return false
  go a b

/-- Is `s` an instance of template `tpl`? Returns the substitution of pattern
variables; `none` if not. Instances modulo bounded reduction are accepted (the
kernel re-checks conversion when the substitution is used). -/
def instanceOf? (tpl s : Expr) (extraVars : Array FVarId := #[]) :
    ExM (Option (Std.HashMap FVarId Expr)) := do
  let vars := extraVars.foldl (·.insert ·) (← patternVars tpl)
  let multi ← templateMulti vars tpl
  if let some b := matchPat vars multi tpl s {} then return some b
  let (_, st) ← (lgg vars tpl s).run {multi}
  if st.holes.isEmpty then return some st.seen else return none

end Blaster.Proof.Explore
