import Lean

/-! Recover ordinary case splits from recursors whose recursive results are
unused. Every replacement is checked by definitional equality. -/
namespace Blaster.Proof.Verification.Recursors
open Lean Meta

/-- `expression`, a recursor application whose minor premises use no recursive
result, as the corresponding `casesOn` (checked by definitional equality). -/
def nonrecursiveCases? (expression : Expr) : MetaM (Option Expr) := do
  let .const name levels := expression.getAppFn | return none
  let .recInfo info ← getConstInfo name | return none
  -- A nested datatype also has motives and minor premises for its nested
  -- containers. Those do not imply that the major case actually uses a
  -- recursive result. Recover the primary datatype's cases from its rules;
  -- auxiliary container recursors retain their original representation.
  unless info.all.length == 1 && info.getMajorInduct == info.all.head! do return none
  let args := expression.getAppArgs
  unless args.size > info.getMajorIdx do return none
  let mut alts := #[]
  for rule in info.rules do
    let rhs := (rule.rhs.instantiateLevelParams info.levelParams levels).beta
      (args.extract 0 info.getFirstIndexIdx)
    let alt ← lambdaBoundedTelescope rhs rule.nfields fun fields body => do
      let body ← Meta.transform body (pre := fun e =>
        pure <| if e.isHeadBetaTarget then .visit e.headBeta else .continue)
      for constant in body.getUsedConstants do
        if let .recInfo recursive ← getConstInfo constant then
          if recursive.all == info.all then return none
      return some (← mkLambdaFVars fields body)
    let some alt := alt | return none
    alts := alts.push alt
  let casesName := info.getMajorInduct ++ `casesOn
  let result := mkAppN (mkConst casesName levels)
    ((args.extract 0 (info.numParams + 1)) ++
      (args.extract info.getFirstIndexIdx (info.getMajorIdx + 1)) ++ alts ++
      (args.extract (info.getMajorIdx + 1) args.size))
  unless ← isDefEq expression result do return none
  return some result

/-- A decision recursor with a constant motive is the unfolding of `dite`
(`if h : c then t h else e h`); weak-head evaluation of an `if` produces it.
Recover the conditional: the translation reads a conditional through its
condition, whereas the recursor's major premise is a decidability instance
it has no reading of. Checked by definitional equality. -/
def decision? (expression : Expr) : MetaM (Option Expr) := do
  let .const name _ := expression.getAppFn | return none
  let args := expression.getAppArgs
  unless args.size == 5 do return none
  let recursor := name == ``Decidable.rec
  unless recursor || name == ``Decidable.casesOn do return none
  let condition := args[0]!
  let motive := args[1]!
  let major := if recursor then args[4]! else args[2]!
  let isFalse := if recursor then args[2]! else args[3]!
  let isTrue := if recursor then args[3]! else args[4]!
  let .lam _ _ body _ := motive | return none
  if body.hasLooseBVars then return none
  let level ← getLevel body
  let result := mkApp5 (mkConst ``dite [level]) body condition major isTrue isFalse
  unless ← isDefEq expression result do return none
  return some result

/-- This is representation recovery, not loop unrolling or an induction
hypothesis. Recursors which use recursive results are left unchanged. -/
def normalize (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun node => do
    if node.isHeadBetaTarget then return .visit node.headBeta
    return .continue) (post := fun node => do
    if let some result ← decision? node then return .done result
    -- Recover inner case splits first. An unused-recursion outer recursor
    -- may contain an independent recursor of the same datatype in a branch;
    -- a preorder check would mistake it for use of the outer recursive result.
    if let some result ← nonrecursiveCases? node then return .visit result
    return .continue)

end Blaster.Proof.Verification.Recursors
