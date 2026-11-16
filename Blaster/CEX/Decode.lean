import Lean

namespace Blaster.CEX

/-- A structured Z3 model value. `raw` marks a value that the native model
    inspector cannot interpret; it must never be turned into a Lean term. -/
inductive Value where
  | numeral (text : String)
  | bool (value : Bool)
  | str (value : String)
  | app (ctor : String) (fields : Array Value)
  | raw (text : String)
deriving Repr

open Lean Meta

mutual
/-- Build a Lean value from a Z3 model value under an expected Lean type.
    Constructor names, field count and field types come from Lean metadata; the
    final expression is accepted only if `inferType` agrees with `expected`.
    Unsupported model forms return `none` and keep their raw diagnostic. -/
partial def decode? (expected : Expr) (value : Value) (fuel : Nat := 256) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  try
    let expected ← whnf expected
    let candidate? ← decodeCandidate? expected value fuel
    let some candidate := candidate? | return none
    let candidateType ← inferType candidate
    unless ← isDefEq candidateType expected do return none
    let candidate ← instantiateMVars candidate
    if !expected.hasMVar && candidate.hasMVar then return none
    return some candidate
  catch _ => return none

private partial def decodeCandidate? (expected : Expr) (value : Value)
    (fuel : Nat) : MetaM (Option Expr) := do
  if expected.isConstOf ``Nat then
    match value with
    | .numeral s => return (s.toNat?).map mkNatLit
    | _ => return none
  if expected.isConstOf ``Int then
    match value with
    | .numeral s => return (s.toInt?).map mkIntLit
    | _ => return none
  if expected.isConstOf ``Bool then
    match value with
    | .bool true => return some (mkConst ``Bool.true)
    | .bool false => return some (mkConst ``Bool.false)
    | _ => return none
  if expected.isConstOf ``String then
    match value with
    | .str s => return some (mkStrLit s)
    | _ => return none
  if expected.isAppOf ``BitVec then
    match value, expected.getAppArgs[0]? with
    | .numeral s, some width =>
        return (s.toNat?).map fun n => mkApp2 (mkConst ``BitVec.ofNat) width (mkNatLit n)
    | _, _ => return none
  match value, expected.getAppFn with
  | .app ctorName fields, .const indName levels =>
      let indInfo ← getConstInfoInduct indName
      let some ctorName := indInfo.ctors.find? (fun n => n.toString == ctorName)
        | return none
      let ctorInfo ← getConstInfoCtor ctorName
      let params := expected.getAppArgs
      if params.size < ctorInfo.numParams || fields.size != ctorInfo.numFields then
        return none
      let mut term := mkConst ctorName levels
      let mut termType ← inferType term
      for p in params[:ctorInfo.numParams] do
        let .forallE _ _ body _ ← whnf termType | return none
        term := mkApp term p
        termType := body.instantiate1 p
      for field in fields do
        let .forallE _ fieldType body _ ← whnf termType | return none
        let some fieldTerm ← decode? fieldType field (fuel - 1) | return none
        term := mkApp term fieldTerm
        termType := body.instantiate1 fieldTerm
      return some term
  | _, _ => return none
end

end Blaster.CEX
