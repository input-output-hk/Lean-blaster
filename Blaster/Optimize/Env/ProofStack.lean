import Lean
import Blaster.Optimize.Env.Types

open Lean Meta

namespace Blaster.Optimize

/-! Proof-stack functions used by proof emission. They read the optimizer state and write
    only the proof reconstruction state `TranslateEnv.proofEnv`, so that emission leaves the
    optimizer state unchanged. -/

@[always_inline, inline]
def modifyProofEnv (f : ProofEnv → ProofEnv) : TranslateEnvT Unit :=
  modify fun ⟨s, o, p⟩ => ⟨s, o, f p⟩

/-- Push a proof step onto the appropriate proof stack.
    When optimizing a recursive function body, steps go to `localProofStack`;
    otherwise they go to the global `proofStack`.
    A rewrite step records the binders open when it is pushed. -/
@[always_inline, inline]
def pushProofStep (step : ProofStep) : TranslateEnvT Unit :=
  modifyProofEnv fun p =>
    let step := match step with
      | .rewrite pf symm _ => .rewrite pf symm p.openBinders
      | s => s
    if p.optimizeRecFunBody then { p with localProofStack := p.localProofStack.push step }
    else { p with proofStack := p.proofStack.push step }

/-- Return the size of the proof stack targeted by `pushProofStep`. -/
@[always_inline, inline]
def getProofStackSize : TranslateEnvT Nat := do
  let p := (← get).proofEnv
  if p.optimizeRecFunBody
  then return p.localProofStack.size
  else return p.proofStack.size

/-- Drop the steps pushed after the proof stack targeted by `pushProofStep` had size `n`. -/
@[always_inline, inline]
def shrinkProofStack (n : Nat) : TranslateEnvT Unit :=
  modifyProofEnv fun p =>
    if p.optimizeRecFunBody then { p with localProofStack := p.localProofStack.shrink n }
    else { p with proofStack := p.proofStack.shrink n }

/-- Push the step `e = r` of type `t` when both sides are defeq, as in a constant fold where `r`
    is the literal value of the ground operation `e`. The proof is `Eq.refl r` ascribed to `e = r`
    via `id`, so the kernel checks it by evaluation and emission needs no lemma nor instance synthesis.
    `t` must live in `Type` (the optimizer's `Eq` has level one). -/
@[always_inline, inline]
def pushFoldStep (t e r : Expr) : TranslateEnvT Unit :=
  pushProofStep (.rewrite (mkApp2 (mkConst ``id [levelZero])
    (mkApp3 (mkConst ``Eq [levelOne]) t e r) (mkApp2 (mkConst ``Eq.refl [levelOne]) t r)))

/-- Start the optimization of a recursive function body: the steps pushed until the matching
    `exitRecFunBody` go to a fresh `localProofStack`, so that they stay out of the goal's
    `proofStack`. The enclosing body's local stack, if any (mutually recursive case), is saved in
    `recFunBodyCtx`. -/
@[always_inline, inline]
def enterRecFunBody : TranslateEnvT Unit :=
  modifyProofEnv fun p =>
    { p with recFunBodyCtx := (p.localProofStack, p.optimizeRecFunBody) :: p.recFunBodyCtx,
             localProofStack := #[],
             optimizeRecFunBody := true }

/-- End the optimization of the recursive function body entered by `enterRecFunBody`: drop the
    body's local proof stack and restore the enclosing context saved in `recFunBodyCtx`, i.e., the
    enclosing body's `localProofStack`, or the goal's `proofStack` as target of `pushProofStep`.
    Without a matching `enterRecFunBody` there is no context to restore. -/
@[always_inline, inline]
def exitRecFunBody : TranslateEnvT Unit :=
  modifyProofEnv fun p =>
    match p.recFunBodyCtx with
    | (l, b) :: ctx => { p with localProofStack := l, optimizeRecFunBody := b, recFunBodyCtx := ctx }
    | [] => p

/-- Discard the proof steps and the binders recorded so far (e.g., during cache initialization). -/
@[always_inline, inline]
def clearProofStacks : TranslateEnvT Unit :=
  modifyProofEnv fun p => { p with proofStack := #[], localProofStack := #[], optBinders := {} }

/-- Record a goal binder FVarId created during optimization, or `none` for a goal binder dropped
    before it is opened, in `optBinders.rhs` when `rhs`. -/
@[always_inline, inline]
def pushOptBinder (id? : Option FVarId) (rhs : Bool) : TranslateEnvT Unit :=
  modifyProofEnv fun p =>
    if rhs then { p with optBinders.rhs := p.optBinders.rhs.push id? }
    else { p with optBinders.goal := p.optBinders.goal.push id? }

/-- Record a binder the optimizer opens. -/
@[always_inline, inline]
def pushOpenBinder (x type : Expr) : TranslateEnvT Unit :=
  modifyProofEnv fun p => { p with openBinders := { fvar := x.fvarId!, type } :: p.openBinders }

/-- Record the binder `x` that the optimizer opens again (context reuse), with the type of its
    declaration in the optimizer local context. The optimizer local context only grows, so the
    declaration is always found. -/
@[always_inline, inline]
def pushReusedOpenBinder (x : Expr) : TranslateEnvT Unit := do
  if let some d := (← get).optEnv.ctx.ctx.find? x.fvarId! then pushOpenBinder x d.type

/-- Record, next to the entry `lhs := rhs` that `updateEqualityMap` makes in context `ctxId`, its
    proof `h : lhs = rhs`, or `h : rhs = lhs` when `symm`, as the step rewriting `lhs` into `rhs`.
    Same key and context id as the optimizer's entry, so the proof is visible exactly where the
    entry is. -/
@[always_inline, inline]
def updateEqProofMap (lhs rhs h : Expr) (symm : Bool) (ctxId : CtxId) : TranslateEnvT Unit := do
  let entry := (ctxId, (rhs, ProofStep.rewrite h symm))
  match (← get).proofEnv.eqProofMap.get? lhs with
  | none =>
      let refEntry ← IO.mkRef [entry]
      modifyProofEnv fun p => { p with eqProofMap := p.eqProofMap.insert lhs refEntry }
  | some refEntry => refEntry.modify (entry :: ·)

/-- Push the step of the substitution of `lhs` by `rhs` that the equality map makes in the current
    context, looked up with the active context ids, as the optimizer looks up the entry. An entry
    made from a match pattern (see `unifyAndUpdateEqMap`) has no proof, and may shadow one made
    from a hypothesis of an outer context: a proof is pushed only if it is for this `rhs`. -/
@[always_inline, inline]
def pushEqMapStep (lhs rhs : Expr) : TranslateEnvT Unit := do
  let m := (← get).proofEnv.eqProofMap
  if m.size == 0 then return ()
  if let some (r, step) ← ContextMap.findRaw m (← get).optEnv.options.active lhs then
    if exprEq r rhs then pushProofStep step

/-- Forget the binder `x` when the optimizer closes it, before the rules on the binder itself. -/
@[always_inline, inline]
def popOpenBinder (x : Expr) : TranslateEnvT Unit :=
  modifyProofEnv fun p => match p.openBinders with
    | b :: bs => if x.fvarId! == b.fvar then { p with openBinders := bs } else p
    | [] => p

end Blaster.Optimize
