import Blaster.Proof.Explore.Machine
import Blaster.Proof.Induction.MappedLists

/-!
# Symbolic exploration: state, variables, control structure and keys

Exploration introduces local variables for split fields, generalized
subterms, and decision hypotheses. They are *canonical*: splitting the same
variable into the same constructor, or generalizing the same subterm, always
yields the same variables. Constructor injectivity makes this consistent, and
it lets states reached along different paths be compared syntactically.

*Control* types are the types that can contain program code. Control positions
of a state are normalized and keyed exactly; data positions are abstracted in
keys. Without program code every position is data.
-/
namespace Blaster.Proof.Explore
open Lean Meta

/-- How an exploration variable was introduced. -/
inductive VarOrigin where
  /-- A variable of the original goal. -/
  | root
  /-- Field `index` of `atom` in constructor `ctor`. -/
  | field (atom : Expr) (ctor : Name) (index : Nat)
  /-- A generalized subterm. -/
  | gen (expr : Expr)
  /-- A decision hypothesis. -/
  | hyp (prop : Expr) (positive : Bool)
  /-- A template parameter introduced by anti-unification. -/
  | param
  /-- A procedure continuation. -/
  | kappa
  /-- A value returned by a procedure (hole of an exit shape). -/
  | ret
deriving Inhabited

/-- What the exploration knows of one of its variables. -/
structure VarInfo where
  origin : VarOrigin
  /-- Determined by the original goal variables alone (not by a loop). -/
  rootish : Bool
deriving Inhabited

/-- The state of an exploration: its variables (canonical, see the module
documentation) and caches. -/
structure Core where
  /-- The context of the goal's variables and of every variable introduced since. -/
  lctx : LocalContext
  machine : Machine
  vars : Std.HashMap FVarId VarInfo := {}
  /-- The fields of each variable split into each constructor. -/
  splitVars : Std.HashMap (FVarId × Name) (Array Expr) := {}
  /-- The variable of each generalized subterm. -/
  genVars : Std.HashMap Expr Expr := {}
  /-- The hypothesis of each decision (and its polarity). -/
  hypVars : Std.HashMap (Expr × Bool) Expr := {}
  /-- Whether a type is a control type (`isControl`). -/
  control : Std.HashMap Expr Bool := {}
  /-- The control positions of constructor applications and states. -/
  ctorMask : Std.HashMap Expr (Array Bool) := {}
  keyCache : Std.HashMap Expr UInt64 := {}
  normCache : Std.HashMap Expr Expr := {}
  /-- The argument at which a function is encoder-like (`encoderArg?`). -/
  encoders : Std.HashMap Name (Option Nat) := {}
  /-- Certified element-wise list producers (see `Induction.MappedLists`). -/
  mappings : Std.HashMap Expr (Option (Expr × Expr)) := {}
  /-- Heads known not to be element-wise list producers (see `Search.producerHead?`). -/
  nonProducers : Std.HashSet Name := {}
  /-- Producer constants `f` certified element-wise: `(List.map g, f = List.map g)`. -/
  producerMaps : Std.HashMap Expr (Option (Expr × Expr)) := {}
  /-- Multiply occurring pattern variables of template bodies. -/
  multiCache : Std.HashMap Expr (Std.HashSet FVarId) := {}
  /-- During the proof replay: the equations of the exploration's context,
  `(lhs, rhs, proof)` in context order. The rewrites the exploration recorded
  come from that context only (see `Stuck.assumedRewrite?`), not from the
  replay's own locals. -/
  assumptions? : Option (Array (Expr × Expr × Expr)) := none

abbrev ExM := StateRefT Core MetaM

/-- Run `k` in the exploration's local context. -/
def inCtx (k : MetaM α) : ExM α := do withLCtx (← get).lctx #[] k

/-- A new exploration variable. -/
def mkVar (name : Name) (ty : Expr) (origin : VarOrigin) (rootish : Bool) : ExM Expr := do
  let fv ← mkFreshFVarId
  modify fun c => {c with
    lctx := c.lctx.mkLocalDecl fv name ty
    vars := c.vars.insert fv {origin, rootish}}
  return .fvar fv

/-- Whether `e` is determined by the goal's variables alone. -/
def isRootish (e : Expr) : ExM Bool := do
  match e with
  | .fvar id => return (← get).vars[id]?.any (·.rootish)
  | _ =>
    let vars := (← get).vars
    return (collectFVars {} e).fvarIds.all fun id => vars[id]?.any (·.rootish)

/-- Canonical fields for splitting variable `atom` into constructor `c`. -/
def splitFields (atom : Expr) (c : Name) (cty : Expr) : ExM (Array Expr) := do
  let key := (atom.fvarId!, c)
  if let some fs := (← get).splitVars[key]? then return fs
  let rootish ← isRootish atom
  let mut fields := #[]
  let mut t := cty
  let mut i := 0
  while t.isForall do
    let .forallE fn fty b _ := t | unreachable!
    let v ← mkVar fn fty (.field atom c i) rootish
    fields := fields.push v
    t := b.instantiate1 v
    i := i + 1
  modify fun s => {s with splitVars := s.splitVars.insert key fields}
  return fields

/-- Canonical variable for a generalized subterm. -/
def genVar (e : Expr) : ExM Expr := do
  if let some v := (← get).genVars[e]? then return v
  let ty ← inCtx (inferType e)
  let v ← mkVar `g ty (.gen e) (← isRootish e)
  modify fun s => {s with genVars := s.genVars.insert e v}
  return v

/-- Canonical hypothesis for a decision. -/
def hypVar (p : Expr) (positive : Bool) : ExM Expr := do
  if let some v := (← get).hypVars[(p, positive)]? then return v
  let v ← mkVar `h (if positive then p else mkNot p) (.hyp p positive) (← isRootish p)
  modify fun s => {s with hypVars := s.hypVars.insert (p, positive) v}
  return v

/-! ## Control structure -/

/-- Whether values of `ty` can contain program code (the machine's code type). -/
partial def isControl (ty : Expr) (visiting : List Name := []) : ExM Bool := do
  let some code := (← get).machine.codeType? | return false
  if let some r := (← get).control[ty]? then return r
  if ty == code then return true
  let r ← do
    let some info ← inCtx (inductiveType? ty) | pure false
    if visiting.contains info.name then return false
    let ls := ty.getAppFn.constLevels!
    let params := ty.getAppArgs.extract 0 info.numParams
    let mut found := false
    for c in info.ctors do
      let cinfo ← getConstInfo c
      let fieldTys ← inCtx do
        let cty ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params
        forallTelescope cty fun fields _ => fields.mapM fun f => do whnf (← inferType f)
      for fty in fieldTys do
        if fty.hasLooseBVars || fty.hasFVar then continue
        if ← isControl fty (info.name :: visiting) then found := true; break
      if found then break
    pure found
  modify fun x => {x with control := x.control.insert ty r}
  return r

/-- For a constructor application, which arguments are control positions. -/
def ctorMaskOf (e : Expr) : ExM (Array Bool) := do
  let f := e.getAppFn
  let .const c ls := f | return #[]
  let some (.ctorInfo cinfo) := (← getEnv).find? c | return #[]
  let params := e.getAppArgs.extract 0 cinfo.numParams
  let key := mkAppN f params
  if let some m := (← get).ctorMask[key]? then return m
  let fieldTys ← inCtx do
    let cty ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params
    forallTelescope cty fun fields _ => fields.mapM fun fl => do whnf (← inferType fl)
  let mut mask := Array.replicate cinfo.numParams false
  for fty in fieldTys do
    let b ← if fty.hasLooseBVars || fty.hasFVar then pure false else isControl fty
    mask := mask.push b
  modify fun x => {x with ctorMask := x.ctorMask.insert key mask}
  return mask

/-- Argument mask of a machine state: control-typed arguments (per predicate). -/
def stateMask (s : Expr) : ExM (Array Bool) := do
  let f := s.getAppFn
  if let some m := (← get).ctorMask[f]? then return m
  let fty ← inCtx (inferType f)
  let tys ← inCtx <| forallBoundedTelescope fty (some s.getAppNumArgs) fun xs _ =>
    xs.mapM fun x => do whnf (← inferType x)
  let mut mask := #[]
  for t in tys do
    mask := mask.push (← if t.hasFVar || t.hasLooseBVars then pure false else isControl t)
  modify fun x => {x with ctorMask := x.ctorMask.insert f mask}
  return mask

/-- Structural key: control positions exactly, data positions abstracted. -/
partial def keyOf (e : Expr) (control : Bool := true) : ExM UInt64 := do
  if control then
    if let some h := (← get).keyCache[e]? then return h
    let h ← do
      if !e.hasFVar then
        match (← get).machine.codeType? with
        | some code =>
          if (← inCtx (inferType e)) == code then return hash e
        | none => pure ()
      if ← inCtx (isCtorApp e) then
        let mask ← ctorMaskOf e
        let mut h : UInt64 := hash e.getAppFn
        let args := e.getAppArgs
        for i in [0:args.size] do
          let isCtl := i < mask.size && mask[i]!
          h := mixHash h (← keyOf args[i]! isCtl)
        pure h
      else if !e.hasFVar then pure (hash e) else pure 11
    modify fun x => {x with keyCache := x.keyCache.insert e h}
    return h
  else
    -- Data is abstracted: revisiting the same control structure with different
    -- data is a loop. The exception is a closed value of an enumeration type
    -- (all constructors nullary): finitely many, code-like values such as
    -- builtin tags or flags, which never cause unbounded unrolling.
    if e.hasFVar then return 17
    let .const c _ := e.getAppFn | return 17
    let some (.ctorInfo ci) := (← getEnv).find? c | return 17
    if (← isEnum ci.induct) then return hash e
    return 17
where
  isEnum (n : Name) : ExM Bool := do
    let some (.inductInfo info) := (← getEnv).find? n | return false
    info.ctors.allM fun c => do
      let some (.ctorInfo ci) := (← getEnv).find? c | return false
      return ci.numFields == 0

/-- Key of a machine state. -/
def stateKey (s : Expr) : ExM UInt64 := do
  let mask ← stateMask s
  let mut h : UInt64 := hash s.getAppFn
  let args := s.getAppArgs
  for i in [0:args.size] do
    h := mixHash h (← keyOf args[i]! (mask[i]?.getD false))
  return h

/-- Weak-head normalize control positions deeply (constructor structure only). -/
partial def normControl (e : Expr) : ExM Expr := do
  if let some r := (← get).normCache[e]? then return r
  let M := (← get).machine
  let some w ← inCtx (M.whnf e) | throwError "explore: control normalization budget"
  let r ← do
    if ← inCtx (isCtorApp w) then
      let mask ← ctorMaskOf w
      let args := w.getAppArgs
      let mut out := #[]
      for i in [0:args.size] do
        if i < mask.size && mask[i]! then out := out.push (← normControl args[i]!)
        else out := out.push args[i]!
      pure (mkAppN w.getAppFn out)
    else pure w
  modify fun x => {x with normCache := x.normCache.insert e r}
  return r

/-- Normalize a machine state: control arguments deeply, projections of
constructor applications everywhere. -/
def normState (s : Expr) : ExM Expr := do
  let mask ← stateMask s
  let args := s.getAppArgs
  let mut out := #[]
  for i in [0:args.size] do
    if mask[i]?.getD false then out := out.push (← normControl args[i]!)
    else out := out.push args[i]!
  inCtx (projReduce (mkAppN s.getAppFn out))

end Blaster.Proof.Explore
