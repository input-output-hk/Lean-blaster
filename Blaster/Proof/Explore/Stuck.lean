import Blaster.Proof.Explore.Core

/-!
# Symbolic exploration: why is a reduction stuck?

Given a weak-head normal expression that is neither a leaf nor a machine
state, find the subterm whose value is needed next and decide how to make
progress. The answer abstracts only the scrutinized *occurrence* (the motive);
other occurrences of the same variable are left unchanged.

Rules for a stuck discriminant `d` with weak-head normal form `d'`:
1. control-typed (can contain program code): descend into `d'`;
2. decision instance: split on the decision;
3. free variable: split on its constructors;
4. projection of a structure variable: split the structure;
5. application of an encoder-like function (one unfolding after splitting a
   variable argument yields a constructor): split that argument;
6. otherwise: generalize `d` as a whole and split the result.
Rule 6 never looks inside data computations, which keeps library internals
(for example builtin implementations) out of the exploration.
-/
namespace Blaster.Proof.Explore
open Lean Meta

/-- What a step is stuck on, and how to make progress (see the module documentation). -/
inductive Stuck where
  /-- Split `atom` (a variable) or generalize it (any other data expression).
  `motive` is `fun x => e[x]` with `x` at the scrutinized occurrence. -/
  | data (atom : Expr) (motive : Expr)
  /-- Decide `prop`; `inst : Decidable prop` is the scrutinized occurrence. -/
  | cond (inst : Expr) (prop : Expr) (motive : Expr)
  /-- Rewrite every occurrence of `lhs` into `rhs` with the checked
  `proof : lhs = rhs`, inside `motive.beta #[focus]` (the rebuilt expression). -/
  | rewrite (lhs rhs proof focus motive : Expr)
  /-- No way to make progress: the exploration aborts here. -/
  | other (e : Expr) (why : String)
deriving Inhabited

/-- `fun x : ty => rebuild x`; the hole is never under a binder. -/
def mkMotive (ty : Expr) (rebuild : Expr → Expr) : ExM Expr := do
  let tmp ← mkFreshFVarId
  let body := rebuild (.fvar tmp)
  return .lam `x ty (body.abstract #[.fvar tmp]) .default

/-- `s` found inside a subterm, as seen from the expression that `rebuild`
reassembles around that subterm. -/
def Stuck.compose (s : Stuck) (rebuild : Expr → Expr) : ExM Stuck := do
  match s with
  | .data a m => return .data a (← mkMotive m.bindingDomain! fun x => rebuild (m.beta #[x]))
  | .cond i p m => return .cond i p (← mkMotive m.bindingDomain! fun x => rebuild (m.beta #[x]))
  | .rewrite l r p f m => return .rewrite l r p f (← mkMotive m.bindingDomain! fun x => rebuild (m.beta #[x]))
  | o => return o

/-- Is `f` encoder-like at some argument: after splitting that (variable)
argument into any constructor, one weak-head reduction yields a constructor? -/
def encoderArg? (e : Expr) : ExM (Option Nat) := do
  let args := e.getAppArgs
  let M := (← get).machine
  for i in [0:args.size] do
    let ok ← inCtx do
      let a ← whnf args[i]!
      unless a.isFVar do return false
      let ty ← whnf (← inferType a)
      let some info ← inductiveType? ty | return false
      if info.numIndices != 0 then return false
      let ls := ty.getAppFn.constLevels!
      let params := ty.getAppArgs.extract 0 info.numParams
      for c in info.ctors do
        let cinfo ← getConstInfo c
        let cty ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params
        let good ← forallTelescope cty fun fields _ => do
          let app := mkAppN (mkAppN (mkConst c ls) params) fields
          let some r ← M.whnf (mkAppN e.getAppFn (args.set! i app)) (some 2000) | return false
          isCtorApp r
        unless good do return false
      return true
    if ok then return some i
  return none

/-- Projection `s.i` (structure projection or projection function) with its structure. -/
def projOf? (e : Expr) : MetaM (Option (Expr × (Expr → Expr))) := do
  match e with
  | .proj n i s => return some (s, fun x => .proj n i x)
  | .app .. =>
    let .const fn _ := e.getAppFn | return none
    let some info := (← getEnv).getProjectionFnInfo? fn | return none
    let args := e.getAppArgs
    unless args.size == info.numParams + 1 do return none
    return some (args[info.numParams]!, fun x => mkAppN e.getAppFn (args.set! info.numParams x))
  | _ => return none

/-- Constant-headed applications inside `e` (outermost first), without loose
bound variables. -/
partial def appSubtermsOf (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isApp && e.getAppFn.isConst && !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app .. => e.getAppArgs.foldl (fun acc a => appSubtermsOf a acc) acc
  | .mdata _ b | .proj _ _ b => appSubtermsOf b acc
  | _ => acc

/-- A subterm `List.drop n (producer l)` with an element-wise producer: its
checked rewrite to `List.map element (List.drop n l)`. -/
def dropRewrite? (d : Expr) (motive : Expr) : ExM (Option Stuck) := do
  let some t := d.find? fun t => t.isAppOfArity ``List.drop 3 &&
      (t.appArg!.isAppOfArity ``List.map 4 ||
        (t.appArg!.getAppNumArgs == 1 && t.appArg!.getAppFn.isConst)) | return none
  let cache ← IO.mkRef (← get).mappings
  let r ← inCtx (Induction.MappedLists.dropOfMapped? t cache)
  let updated ← cache.get
  modify fun c => {c with mappings := updated}
  let some (rhs, proof) := r | return none
  return some (.rewrite t rhs proof d motive)

/-- A discriminant of `d'` that an element-wise producer computes
(`encodeList xs`, a local recursive map): its checked rewrite to
`List.map element xs`, so that the typed list is what gets a value. -/
partial def producerRewrite? (d' focus motive : Expr) : ExM (Option Stuck) := do
  let some m ← inCtx (matchMatcherApp? d' (alsoCasesOn := true)) | return none
  for x in m.discrs do
    let x' ← inCtx (whnfR x)
    unless x'.getAppNumArgs == 1 && x'.getAppFn.isConst do continue
    let cache ← IO.mkRef (← get).mappings
    let r ← inCtx (Induction.MappedLists.asMap? x' cache)
    let updated ← cache.get
    modify fun c => {c with mappings := updated}
    if let some (rhs, proof) := r then
      return some (.rewrite x' rhs proof focus motive)
  return none

/-- A discriminant stuck on `List.map f y` (an element-wise encoding): the
typed list `y` is what needs a value. -/
partial def mapInner? (d' : Expr) : ExM (Option Expr) := do
  let some m ← inCtx (matchMatcherApp? d' (alsoCasesOn := true)) | return none
  for x in m.discrs do
    let x' ← inCtx (whnfR x)
    if x'.isAppOfArity ``List.map 4 then
      let y := x'.appArg!
      let y' ← inCtx (whnf y)
      if y'.isFVar then return some y'
      if !(← inCtx (isCtorApp y')) then return some y
  return none

/-- The equations of the local context, `(lhs, rhs, proof)` in context order. -/
def contextEquations : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let some (_, lhs, rhs) := type.eq? | continue
    out := out.push (lhs, rhs, declaration.toExpr)
  return out

/-- A hypothesis of the context stating `t = rhs` (for example an equation a
decomposed success hypothesis provides): rewrite `t` with it instead of
generalizing it, so that the value the hypothesis fixes is the one explored. -/
def assumedRewrite? (t focus motive : Expr) : ExM (Option Stuck) := do
  if t.isFVar then return none
  let assumptions? := (← get).assumptions?
  let found ← inCtx do
    -- (the replay's: those of the context the exploration had)
    let equations ← match assumptions? with
      | some equations => pure equations
      | none => contextEquations
    for (lhs, rhs, proof) in equations do
      if lhs == t || (← withReducible (isDefEq lhs t)) then
        return some (rhs, proof)
    return none
  let some (rhs, proof) := found | return none
  return some (.rewrite t rhs proof focus motive)

/-- What the reduced step `e` (neither a leaf nor a state) is stuck on: the
occurrence to split, generalize, decide or rewrite, by the rules of the
module documentation; `fuel` bounds the descent into stuck discriminants. -/
partial def findStuck (e : Expr) (fuel : Nat := 64) : ExM Stuck := do
  if fuel == 0 then return .other e "depth"
  let M := (← get).machine
  let ty ← inCtx do whnf (← inferType e)
  if ty.isAppOf ``Decidable then
    return .cond e ty.appArg! (← mkMotive ty id)
  let encoderSplit? (d : Expr) (rebuild : Expr → Expr) : ExM (Option Stuck) := do
    let .const fn _ := d.getAppFn | return none
    if (← getEnv).find? fn |>.any (·.isCtor) then return none
    -- only a positive answer is a property of the function: a negative one
    -- may just mean this call's argument is not a variable yet
    let enc ← match (← get).encoders[fn]? with
      | some (some r) => pure (some r)
      | _ => do
        let r ← encoderArg? d
        if r.isSome then modify fun c => {c with encoders := c.encoders.insert fn r}
        pure r
    let some j := enc | return none
    let args := d.getAppArgs
    let some a := args[j]? | return none
    let a ← inCtx (whnf a)
    unless a.isFVar do
      -- an encoded field of a structure variable (`toData r.resolved.datum`):
      -- give the root structure its constructor first, so the field becomes a
      -- variable the encoding can then be split on
      let mut root := a
      for _ in [0:8] do
        let some (s, _) ← inCtx (projOf? root) | break
        root ← inCtx (whnf s)
      unless root.isFVar && root != a do return none
      let rty ← inCtx (inferType root)
      return some (.data root (← mkMotive rty fun x => rebuild (replaceTerm d root x)))
    let aty ← inCtx (inferType a)
    return some (.data a (← mkMotive aty fun x => rebuild (mkAppN d.getAppFn (args.set! j x))))
  let classify (d : Expr) (rebuild : Expr → Expr) : ExM (Option Stuck) := do
    let some d' ← inCtx (M.whnf d) | return some (.other d "discriminant budget")
    if ← inCtx (isCtorApp d') then return none
    let dty ← inCtx do whnf (← inferType d)
    if dty.isAppOf ``Decidable then
      return some (.cond d' dty.appArg! (← mkMotive dty rebuild))
    if ← isControl dty then
      let r ← findStuck d' (fuel - 1)
      return some (← r.compose rebuild)
    if d'.isFVar then return some (.data d' (← mkMotive dty rebuild))
    if let some (s, proj) ← inCtx (projOf? d') then
      let s' ← inCtx (whnf s)
      if s'.isFVar then
        let sty ← inCtx (inferType s')
        return some (.data s' (← mkMotive sty fun x => rebuild (proj x)))
    if let some r ← encoderSplit? d rebuild then return some r
    if let some r ← encoderSplit? d' rebuild then return some r
    -- an encoding nested in the discriminant (`unConstrData (toData datum)`):
    -- give the encoded typed value its constructor
    -- only encodings of fields of split structures (the selected record's datum)
    let vars := (← get).vars
    let isField := fun (a : Expr) => match a with
      | .fvar id => match vars[id]? with
        | some {origin := .field .., ..} => true
        | _ => false
      | _ => false
    let cands := (appSubtermsOf d').filter fun t => t != d' && t.getAppArgs.back?.any isField
    for t in cands.toList.take 4 do
      if let some r ← encoderSplit? t (fun x => rebuild (replaceTerm d' t x)) then return some r
    -- typed lifting: move `drop` inside element-wise encodings, then give the
    -- typed list a value rather than the encoded one
    if let some r ← dropRewrite? d (← mkMotive dty rebuild) then return some r
    if let some r ← producerRewrite? d' d (← mkMotive dty rebuild) then return some r
    if let some y ← mapInner? d' then
      if let some r ← assumedRewrite? y d (← mkMotive dty rebuild) then return some r
      let yty ← inCtx (inferType y)
      return some (.data y (← mkMotive yty fun x => rebuild (replaceTerm d y x)))
    if (← inCtx (inductiveType? dty)).isSome && !(← inCtx (isProp d)) then
      if let some r ← assumedRewrite? d d (← mkMotive dty rebuild) then return some r
      return some (.data d (← mkMotive dty rebuild))
    -- the discriminant reduced to a stuck recursor or matcher (`Decidable.rec …
    -- (instDecidableEqBool b true)`): the stuck point is inside it
    let env ← getEnv
    let isRec := match d'.getAppFn with
      | .const c _ => match env.find? c with
        | some (.recInfo _) => true
        | _ => false
      | _ => false
    if isRec || (← inCtx (matchMatcherApp? d' (alsoCasesOn := true))).isSome then
      match ← findStuck d' (fuel - 1) with
      | .other .. => pure ()
      | r => return some (← r.compose rebuild)
    return some (.other d' "discriminant")
  if let some m ← inCtx (matchMatcherApp? e (alsoCasesOn := true)) then
    for i in [0:m.discrs.size] do
      let d := m.discrs[i]!
      if let some r ← classify d (fun c => { m with discrs := m.discrs.set! i c }.toExpr) then
        return r
    if let some e' ← inCtx (unfoldHead? e) then
      let e' ← inCtx (whnfCore e')
      if e' != e then return ← findStuck e' (fuel - 1)
    return .other e "matcher"
  match e.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.recInfo info) =>
      let args := e.getAppArgs
      let rebuild := fun c => mkAppN e.getAppFn (args.set! info.getMajorIdx c)
      if let some r ← classify args[info.getMajorIdx]! rebuild then return r
      return .other e "recursor on constructor"
    | _ =>
      if ← inCtx (isProp e) then return .other e "proposition"
      if (← inCtx (inductiveType? ty)).isNone then return .other e "application"
      if ← isControl ty then
        if let some e' ← inCtx (unfoldHead? e) then
          let some e'' ← inCtx (M.whnf e') | return .other e "control application budget"
          if e'' != e then return ← findStuck e'' (fuel - 1)
        return .other e "control application"
      return .data e (← mkMotive ty id)
  | .fvar _ =>
    if (← inCtx (inductiveType? ty)).isSome then return .data e (← mkMotive ty id)
    return .other e "variable"
  | .proj n i s =>
    if let some (s, proj) ← inCtx (projOf? e) then
      let s' ← inCtx (whnf s)
      if s'.isFVar then
        let sty ← inCtx (inferType s')
        return .data s' (← mkMotive sty proj)
    -- a projection of a stuck recursor or matcher (structural recursion's
    -- `below` table, `(T.rec … major).1 args`): the stuck point is inside it
    let s' ← inCtx (whnf s)
    let env ← getEnv
    let isRec := match s'.getAppFn with
      | .const c _ => match env.find? c with
        | some (.recInfo _) => true
        | _ => false
      | _ => false
    if isRec || (← inCtx (matchMatcherApp? s' (alsoCasesOn := true))).isSome then
      let args := e.getAppArgs
      let r ← findStuck s' (fuel - 1)
      match r with
      | .other .. => pure ()
      | r => return ← r.compose fun x => mkAppN (.proj n i x) args
    if (← inCtx (inductiveType? ty)).isSome then return .data e (← mkMotive ty id)
    return .other e "projection"
  | _ => return .other e "head"

end Blaster.Proof.Explore
