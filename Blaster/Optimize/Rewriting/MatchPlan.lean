import Blaster.Optimize.Rewriting.Utils

open Lean Meta

namespace Blaster.Optimize

/-- A constructor view with inductive parameters omitted. -/
def isCtorPattern (p : Expr) : TranslateEnvT (Option (Name × Array Expr)) := do
  let .const n _ := p.getAppFn' | return none
  let .ctorInfo info ← getConstEnvInfo n | return none
  let args := p.getAppArgs
  return (n, args[info.numParams:args.size].toArray)

/-- Analysis of an alternative, independent of its body and of unifier assignments.
    `unsupported` is distinct from `impossible`: it must preserve the original matcher. -/
inductive MatchPatternPlan where
  | impossible
  | unsupported
  | residual (tests : Array Expr) (bindings : Array Expr)

/-- Constructor decomposition is restricted to non-indexed families with independent fields.
    Parameters may occur in field types; earlier fields may not. This avoids introducing
    transports when specializing dependent patterns. No reduction is performed here. -/
private def canDecomposeCtor (n : Name) : TranslateEnvT Bool := do
  let .ctorInfo info ← getConstEnvInfo n | return false
  let .inductInfo family ← getConstEnvInfo info.induct | return false
  if family.numIndices != 0 then return false
  let mut type := info.type
  for i in [:info.numParams + info.numFields] do
    let .forallE _ t b _ := type | return false
    if i >= info.numParams then
      for j in [:i - info.numParams] do
        if t.hasLooseBVar j then return false
    type := b
  return true

/-- Partially match known constructor structure, retaining equalities for symbolic leaves.
    Only `params` are pattern variables. In particular, input free variables are never
    assigned or turned into local let declarations. An explicit worklist bounds stack use.
    Unsupported pairs do not stop the scan: another discriminator may prove impossibility. -/
def planMatchPatterns (patterns discrs params : Array Expr) : TranslateEnvT MatchPatternPlan := do
  if patterns.size != discrs.size then return .unsupported
  let mut pending := patterns.zip discrs
  let mut bindings : Array (Option Expr) := params.map (fun _ => none)
  let mut tests : Array Expr := #[]
  let mut supported := true
  while !pending.isEmpty do
    let (pattern, discr) := pending.back!
    pending := pending.pop
    if let some idx := params.findIdx? (exprEq pattern) then
      match bindings[idx]! with
      | none => bindings := bindings.set! idx (some discr)
      | some value =>
          if !exprEq value discr then
            tests := tests.push (← mkApp3Expr (← mkEqOp) (← inferTypeEnv discr) value discr)
    else if exprEq pattern discr then
      pure ()
    else
      match (← isCtorPattern pattern), (← isCtorPattern discr) with
      | some (pc, ps), some (dc, ds) =>
          if pc != dc then return .impossible
          if ps.size != ds.size || !(← canDecomposeCtor pc) then
            supported := false
          else
            pending := pending ++ ps.zip ds
      | _, _ =>
          -- A closed pattern needs only an equality test. Extracting fields from an
          -- unknown constructor requires a residual matcher, so conservatively defer it.
          if pattern.hasFVar || pattern.hasMVar then
            supported := false
          else
            tests := tests.push (← mkApp3Expr (← mkEqOp) (← inferTypeEnv discr) pattern discr)
  if !supported then return .unsupported
  let mut values := #[]
  for i in [:bindings.size] do
    -- Lean may add a dummy argument to an alternative without pattern variables.
    -- Keep unbound parameters temporarily; the caller must check they disappear
    -- after beta substitution, rather than inventing an inhabitant of their type.
    values := values.push (bindings[i]!.getD params[i]!)
  return .residual tests values

/-- A residual alternative whose pattern variables have already been substituted. -/
structure MatchAlternativePlan where
  tests : Array Expr
  rhs : Expr
  deriving Inhabited

/-- Emit ordered alternatives. Exhaustiveness of the original matcher makes the final
    surviving alternative unconditional; impossible alternatives need no default value. -/
def emitMatchPlan (retType : Expr) (alts : Array MatchAlternativePlan) : TranslateEnvT (Option Expr) := do
  if alts.isEmpty then return none
  let mut result := alts.back!.rhs
  for i in [1:alts.size] do
    let alt := alts[alts.size - i - 1]!
    if alt.tests.isEmpty then
      result := alt.rhs
    else
      let mut cond := alt.tests.back!
      for j in [1:alt.tests.size] do
        cond ← mkApp2Expr (← mkPropAndOp) alt.tests[alt.tests.size - j - 1]! cond
      let hName ← Elab.Term.mkFreshBinderName
      let thenExpr ← mkLambdaExpr hName .default cond alt.rhs
      let elseExpr ← mkLambdaExpr hName .default (← mkAppExpr (← mkPropNotOp) cond) result
      result ← mkApp4Expr (← mkBlasterDIteOp) retType cond thenExpr elseExpr
  return result

end Blaster.Optimize
