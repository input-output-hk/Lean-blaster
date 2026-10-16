import Lean

/-! Checked representation transport for ordinary element-wise list producers.
Mappings are recognized from their nil/cons equations, not from names or
application annotations. No execution postcondition is introduced. -/
namespace Blaster.Proof.Induction.MappedLists
open Lean Meta

private theorem ofEquations {α : Type u} {β : Type v} (producer : List α → List β) (element : α → β)
    (empty : producer [] = [])
    (step : ∀ head tail, producer (head :: tail) = element head :: producer tail) :
    ∀ values, producer values = values.map element := by
  intro values
  induction values with
  | nil => exact empty
  | cons head tail ih => rw [step, List.map_cons, ih]

private structure Mapping where
  element : Expr
  source : Expr
  equality : Option Expr

/-- Certified producers: the element function and the kernel-checked
equation `producer = List.map element`, or `none` for an uncertified one. -/
abbrev MappingCache := Std.HashMap Expr (Option (Expr × Expr))

/-- A unary producer must have exactly the ordinary map equations. Both
equations and the resulting generic induction proof are kernel checked. -/
private def equations? (producer : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
    withTransparency .default do
  let .const name _ := producer | return none
  let .defnInfo info ← getConstInfo name | return none
  unless info.safety == .safe do return none
  let type ← inferType producer
  let .forallE _ domain codomain _ := type | return none
  if codomain.hasLooseBVars then return none
  -- list types spelled through abbreviations (`Withdrawals`) are lists
  let domain ← whnfR domain
  let codomain ← whnfR codomain
  unless domain.isAppOfArity ``List 1 && codomain.isAppOfArity ``List 1 do return none
  let sourceType := domain.getAppArgs[0]!
  let outputType := codomain.getAppArgs[0]!
  let empty ← mkAppOptM ``List.nil #[some sourceType]
  let expected ← mkAppOptM ``List.nil #[some outputType]
  unless ← isDefEq (mkApp producer empty) expected do return none
  let emptyProof ← mkEqRefl (mkApp producer empty)
  let result ← withLocalDeclD `head sourceType fun head =>
    withLocalDeclD `tail domain fun tail => do
      let cons ← mkAppM ``List.cons #[head, tail]
      let call := mkApp producer cons
      let result ← whnf call
      unless result.isAppOfArity ``List.cons 3 do return none
      let fields := result.getAppArgs
      if fields[1]!.containsFVar tail.fvarId! then return none
      unless ← isDefEq fields[2]! (mkApp producer tail) do return none
      let element ← mkLambdaFVars #[head] fields[1]!
      let proof ← mkLambdaFVars #[head, tail] (← mkEqRefl call)
      return some (element, proof)
  let some (element, step) := result | return none
  return some (element, emptyProof, step)

private def certify? (producer : Expr) : MetaM (Option (Expr × Expr)) := do
  -- This is optional recognition, not proof search. An expensive or
  -- unsupported producer is left unchanged; no equation is assumed.
  let description ← tryCatchRuntimeEx
    (withCurrHeartbeats <|
      withTheReader Core.Context (fun context => {context with maxHeartbeats := 100000})
        (equations? producer)) fun error => do
          if error.isRuntime then return none
          throw error
  let some (element, emptyProof, step) := description | return none
  let proof ← mkAppM ``ofEquations #[producer, element, emptyProof, step]
  let environment ← getEnv
  let proofName := environment.asyncPrefix?.getD environment.mainModule ++
    `blasterListViews ++ `mappedList ++ (← mkFreshId)
  addDecl (.thmDecl {name := proofName, levelParams := [], type := ← inferType proof, value := proof})
  return some (element, mkConst proofName)

private def mapping? (expression : Expr) (cache : IO.Ref MappingCache) :
    MetaM (Option Mapping) := do
  if expression.isAppOfArity ``List.map 4 then
    let args := expression.getAppArgs
    return some {element := args[2]!, source := args[3]!, equality := none}
  unless expression.getAppNumArgs == 1 && expression.getAppFn.isConst do return none
  let producer := expression.getAppFn
  let description ← if let some found := (← cache.get)[producer]? then pure found else do
    let found ← certify? producer
    cache.modify (·.insert producer found)
    pure found
  let some (element, proof) := description | return none
  let source := expression.getAppArgs[0]!
  return some {element, source, equality := some (mkApp proof source)}

/-- For `producer source` with an element-wise producer (certified from its
nil/cons equations, for example the local function a `map`-like notation
expands to): the kernel-checked equality with `List.map element source`. -/
def asMap? (expression : Expr) (cache : IO.Ref MappingCache) : MetaM (Option (Expr × Expr)) := do
  if expression.isAppOfArity ``List.map 4 then return none
  let some mapping ← mapping? expression cache | return none
  let some equality := mapping.equality | return none
  let some (_, _, rhs) := (← inferType equality).eq? | return none
  return some (rhs, equality)

/-- For `List.drop n (producer source)` with an element-wise producer (certified
from its nil/cons equations): the kernel-checked equality with
`List.map element (List.drop n source)`. -/
def dropOfMapped? (expression : Expr) (cache : IO.Ref MappingCache) : MetaM (Option (Expr × Expr)) := do
  unless expression.isAppOfArity ``List.drop 3 do return none
  let args := expression.getAppArgs
  let some mapping ← mapping? args[2]! cache | return none
  let context ← withLocalDeclD `mapped (← inferType args[2]!) fun mapped =>
    mkLambdaFVars #[mapped] (mkAppN expression.getAppFn #[args[0]!, args[1]!, mapped])
  let commute ← mkEqSymm (← mkAppOptM ``List.map_drop
    #[none, none, some mapping.element, some mapping.source, some args[1]!])
  let proof ← if let some equality := mapping.equality then
      mkEqTrans (← mkAppM ``congrArg #[context, equality]) commute
    else pure commute
  let some (_, _, result) := (← inferType proof).eq? | return none
  return some (result, proof)

end Blaster.Proof.Induction.MappedLists
