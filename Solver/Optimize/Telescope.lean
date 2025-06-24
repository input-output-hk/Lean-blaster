import Lean
import Solver.Optimize.Env

open Lean Meta

namespace Solver.Optimize

/-- Return `some className` if `n` corresponds to a class or is transitively an abbrevation
    to a class definition (e.g., DecidableEq, DecidableLT, DecidableRel, etc).
-/
partial def isClassConstraint? (n : Name) : MetaM (Option Name) := do
 if isClass (← getEnv) n then pure n
 else
   match (← getConstInfo n) with
   | ConstantInfo.defnInfo defnInfo =>
       match (getForallLambdaBody defnInfo.value).getAppFn' with
       | Expr.const c _ => isClassConstraint? c
       | _ => pure none
   | _ => pure none


/-- Return `true` if `e` corresponds to a class constraint expression
    (see function `isClassConstraint`).
-/
@[always_inline, inline]
def isClassConstraintExpr? (e : Expr) : MetaM (Option Name) := do
 match e.getAppFn' with
 | Expr.const n _ => isClassConstraint? n
 | _ => return none

variable [MonadControlT MetaM n] [Monad n]

private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true

@[always_inline, inline]
private def updateLocalInstance
  (fvar fvarType : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM LocalInstances := do
  if let some c ← isClassConstraintExpr? fvarType
  then
    match lctx.find? fvar.fvarId! with
    | none => throwError f!"updateLocalInstance: unknown free variable '{fvar}'"
    | some localDecl =>
       if localDecl.isImplementationDetail
       then return localInsts
       else return localInsts.push { className := c, fvar := fvar }
  else return localInsts

structure TelescopeEnv where
  lctx : LocalContext
  localInsts : LocalInstances
  fvars : Array Expr

abbrev TelescopeEnvT := StateRefT TelescopeEnv MetaM

private def mkDecl (fvar : Expr) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : TelescopeEnvT Unit := do
  let optClass ← isClassConstraintExpr? type
  modify (fun env =>
            let idx  := env.lctx.decls.size
            let decl := LocalDecl.cdecl idx fvar.fvarId! userName type bi kind
            let localInsts' :=
              match optClass with
              | none => env.localInsts
              | some c =>
                if decl.isImplementationDetail
                then env.localInsts
                else env.localInsts.push { className := c, fvar := fvar }
            { env with
                   lctx.fvarIdToDecl := env.lctx.fvarIdToDecl.insert fvar.fvarId! decl,
                   lctx.decls := env.lctx.decls.push decl
                   localInsts := localInsts'
                   fvars := env.fvars.push fvar
            })

private partial def forallTelescopeAuxAux
    (maxFVars? : Option Nat)
    (type : Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let rec process (type : Expr) : TelescopeEnvT Expr := do
    match type with
    | .forallE n t b bi =>
      if fvarsSizeLtMaxFVars (← get).fvars maxFVars? then
        let fvarId ← mkFreshFVarId
        let fvar  := mkFVar fvarId
        mkDecl fvar n t bi
        process (b.instantiate1 fvar)
      else return type
    | _ => return type
  let (body, env) ← process type|>.run {lctx := ← getLCtx, localInsts := ← getLocalInstances, fvars := #[]}
  withLCtx env.lctx env.localInsts do
    k env.fvars body

private partial def forallTelescopeAux
  (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match maxFVars? with
  | some 0 => k #[] type
  | _ =>
     if type.isForall then
       forallTelescopeAuxAux maxFVars? type k
     else
       k #[] type

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def forallTelescope (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => forallTelescopeAux type none k) k

/--
  Similar to `forallTelescope`, stops constructing the telescope when
  it reaches size `maxFVars`.
-/
@[always_inline, inline]
def forallBoundedTelescope (type : Expr) (maxFVars : Nat) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => forallTelescopeAux type (some maxFVars) k) k

private partial def lambdaTelescopeImp
  (e : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let (body, env) ← process e |>.run {lctx := ← getLCtx, localInsts := ← getLocalInstances, fvars := #[]}
  withLCtx env.lctx env.localInsts do
    k env.fvars body
where
  process (e : Expr) : TelescopeEnvT Expr := do
    match e with
    | .lam n t b bi =>
       if fvarsSizeLtMaxFVars (← get).fvars maxFVars? then
         let fvarId ← mkFreshFVarId
         let fvar := mkFVar fvarId
         mkDecl fvar n t bi
         process (b.instantiate1 fvar)
       else return e
    | _ => return e

/--
  Given `e` of the form `fun ..xs => A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def lambdaTelescope (e : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => lambdaTelescopeImp e none k) k


/--
  Given `e` of the form `fun ..xs ..ys => A`, execute `k xs (fun ..ys => A)` where
  `xs.size ≤ maxFVars`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def lambdaBoundedTelescope (e : Expr) (maxFVars : Nat) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => lambdaTelescopeImp e (some maxFVars) k) k

end Solver.Optimize
