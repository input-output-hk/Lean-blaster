import Lean

/-!
Discover recursion from ordinary definitions. Unfolding equations are
reconstructed from Lean's equation theorems and checked by the kernel before
use. This pass does not propose or prove postconditions.
-/
namespace Blaster.Proof.Induction.Source
open Lean Meta

/-- A kernel-checked defining equation `name = body`, proved by `proof`. -/
structure Equation where
  name : Name
  body : Expr
  proof : Name
  deriving Inhabited

register_option blaster.induction.maxDefinitions : Nat := {
  defValue := 2048
  descr := "Maximum definitions inspected while discovering recursive source calls" }

/-- The definitions a goal reaches, up to the first recursive ones. -/
structure Discovery where
  /-- Nonrecursive wrappers on a path to recursion. -/
  wrappers : Array Name := #[]
  /-- The recursive definitions reached. -/
  recursive : Array Name := #[]
  /-- Those among them that are fuel-recursive predicates (`… → Nat → Prop`). -/
  predicates : Array Name := #[]

/-- Definitions with backend semantics or core logic, never inspected for
recursion. -/
def primitive (name : Name) : Bool :=
  #[`Nat, `Int, `Bool, `String, `BitVec, `UInt8, `UInt16, `UInt32, `UInt64,
    `USize, `HAdd, `HSub, `HMul, `HDiv, `HMod, `HPow, `Neg, `OfNat,
    `LE, `LT, `BEq, `Decidable, `And, `Or, `Not, `Eq, `Ne, `Exists,
    `ite, `dite, `Blaster].any (·.isPrefixOf name)

private def fuelPredicate (name : Name) : MetaM Bool := do
  let .defnInfo info ← getConstInfo name | return false
  unless info.safety == .safe && info.levelParams.isEmpty do return false
  forallTelescope info.type fun arguments result => do
    return !arguments.isEmpty && result == mkSort levelZero &&
      (← isDefEq (← inferType arguments.back!) (mkConst ``Nat))

/-- Inspect definitions up to the first recursive calls. Recursive bodies are
not unfolded here; a concrete fuel argument must not drive proof search. -/
def discover (roots : Array Name) : MetaM Discovery := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut edges : NameMap (Array Name) := {}
  let mut result : Discovery := {}
  let limit := blaster.induction.maxDefinitions.get (← getOptions)
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name || primitive name then continue
    seen := seen.insert name
    if seen.size > limit then
      throwError "blaster source discovery exceeded its definition limit ({limit})"
    let .defnInfo info ← getConstInfo name | continue
    unless info.safety == .safe do continue
    if ← isRecursiveDefinition name then
      result := {result with recursive := result.recursive.push name}
      if ← fuelPredicate name then
        result := {result with predicates := result.predicates.push name}
    else
      let dependencies := info.value.getUsedConstants
      edges := edges.insert name dependencies
      pending := pending ++ dependencies
  let mut reachable := Std.HashSet.ofArray result.recursive
  repeat
    let before := reachable.size
    for (name, dependencies) in edges do
      if dependencies.any reachable.contains then reachable := reachable.insert name
    if reachable.size == before then break
  result := {result with wrappers := edges.toArray.filterMap fun (name, _) =>
    if reachable.contains name then some name else none}
  return result

/-- Monadic `Expr.replace`: `f` decides each subterm (binders included). -/
private partial def replaceM (f : Expr → MetaM (Option Expr)) (e : Expr) : MetaM Expr := do
  if let some r ← f e then return r
  match e with
  | .app g a => return e.updateApp! (← replaceM f g) (← replaceM f a)
  | .lam _ t b _ => return e.updateLambdaE! (← replaceM f t) (← replaceM f b)
  | .forallE _ t b _ => return e.updateForallE! (← replaceM f t) (← replaceM f b)
  | .letE _ t v b nondep => return e.updateLet! (← replaceM f t) (← replaceM f v) (← replaceM f b) nondep
  | .mdata _ b => return e.updateMData! (← replaceM f b)
  | .proj _ _ b => return e.updateProj! (← replaceM f b)
  | _ => return e

/-- Reveal wrapper calls without evaluating a recursive definition, including
when its decreasing argument is a numeral. Only closed calls are unfolded: a
wrapper call under a binder (for example in a match alternative) stays folded
until a case split brings it out, so that facts about it can be instantiated
at the call before it disappears. Wrappers inside the arguments of a recursive
call (for example `get? k (getD c l [])`) are unfolded by one delta step only.
Every returned expression is definitionally equal to its input; callers must
retain the kernel's conversion check when replacing a goal or a hypothesis. -/
partial def expose (discovery : Discovery) (expression : Expr) (everywhere : Bool := false)
    (oneStep : Bool := false) : MetaM Expr := do
  let wrappers := Std.HashSet.ofArray discovery.wrappers
  let recursive := Std.HashSet.ofArray discovery.recursive
  let isWrapperCall := fun (t : Expr) => match t.getAppFn with
    | .const n _ => wrappers.contains n
    | _ => false
  -- `everywhere`: also under binders (the final solver attempt needs every
  -- recursive call visible, so that one hidden in a match alternative is
  -- reported instead of being translated apart from its abstraction)
  if everywhere then
    -- Under a binder (a match alternative, say) a wrapper is unfolded by one
    -- delta step only: `whnf` would lower its conditionals to recursor and
    -- instance code that the translation does not accept.
    let initial := (collectFVars {} expression).fvarSet
    return ← Meta.transform expression (pre := fun node => do
      let .const name _ := node.getAppFn | return .continue
      if recursive.contains name then return .continue
      unless wrappers.contains name do return .continue
      if (← inferType node).isForall then return .continue
      let underBinder := (collectFVars {} node).fvarIds.any fun id => !initial.contains id
      if underBinder then
        let some unfolded ← unfoldDefinition? node | return .continue
        return .visit unfolded.headBeta
      let exposed ← withCanUnfoldPred (fun _ info => do
        return !(← isRecursiveDefinition info.name)) (whnf node)
      if exposed == node then return .continue
      return .visit exposed)
  let rec delta (e : Expr) : MetaM Expr := do
    replaceM (e := e) fun node => do
      if node.hasLooseBVars || !isWrapperCall node then return none
      -- a partial application is closed even when the full call is not
      if (← inferType node).isForall then return none
      let some unfolded ← unfoldDefinition? node | return none
      return some (← delta unfolded.headBeta)
  let rec go (e : Expr) : MetaM Expr := do
    replaceM (e := e) fun node => do
      if node.hasLooseBVars then return none
      let .const name _ := node.getAppFn | return none
      if recursive.contains name then
        if node.getAppArgs.any fun a => (a.find? isWrapperCall).isSome then
          return some (mkAppN node.getAppFn (← node.getAppArgs.mapM delta))
        return some node
      unless wrappers.contains name do return none
      -- a partial application is closed even when the full call is not
      if (← inferType node).isForall then return none
      -- `oneStep`: one unfolding step at a time, keeping `if`/`match` (for the
      -- solver); otherwise weak-head evaluation (for case splitting)
      if oneStep then
        let some unfolded ← unfoldDefinition? node | return none
        return some (← go unfolded.headBeta)
      let exposed ← withCanUnfoldPred (fun _ info => do
        return !(← isRecursiveDefinition info.name)) (whnf node)
      if exposed == node then return none
      return some (← go exposed)
  go expression

/-- From `proof : f arguments = g arguments` (over the locals `arguments`),
a proof of `f = g`, by function extensionality. -/
partial def extensional (arguments : Array Expr) (proof : Expr) : MetaM Expr := do
  if arguments.isEmpty then return proof
  let proof ← mkLambdaFVars #[arguments.back!] proof
  extensional arguments.pop (← mkAppM ``funext #[proof])

/-- Turn an ordinary defining equation into a function equality. Only the
definition and its kernel-checked equation theorem are dependencies. -/
def equationFor (name : Name) : MetaM Equation := do
  let some unfold ← getUnfoldEqnFor? name
    | throwError "no checked unfolding equation for recursive predicate {name}"
  let info ← getConstInfo unfold
  unless info.levelParams.isEmpty do
    throwError "automatic fuel equations currently require monomorphic definitions"
  let (body, proof) ← forallTelescope info.type fun arguments equation => do
    let some (_, left, right) := equation.eq?
      | throwError "unfolding theorem is not an equality: {unfold}"
    unless left == mkAppN (mkConst name) arguments do
      throwError "unfolding theorem does not expose the complete source telescope: {unfold}"
    return (← mkLambdaFVars arguments right,
      ← extensional arguments (mkAppN (mkConst unfold) arguments))
  let environment ← getEnv
  let proofName := environment.asyncPrefix?.getD environment.mainModule ++
    `blasterSourceEquation ++ name
  let type ← mkEq (mkConst name) body
  if let some previous := (← getEnv).find? proofName then
    unless previous.type == type do throwError "source equation name collision: {proofName}"
  else
    addDecl (.thmDecl {name := proofName, levelParams := [], type, value := proof})
  return {name, body, proof := proofName}

end Blaster.Proof.Induction.Source
