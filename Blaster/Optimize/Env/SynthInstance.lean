import Lean
import Blaster.Optimize.Env.HashConsing
import Blaster.Optimize.Opaque

open Lean Meta

namespace Blaster.Optimize

/-- Probe-miss sentinel for `synthInstanceCache`: a static `some instCacheMiss`.
    Genuine cached values are `none` or `some d` with `d` a hash-consed
    instance (or the queried constraint itself, see `synthDecidableWithNotFound!`),
    so no genuine `some d` can hold the private dummy `instCacheMiss` constant. -/
private def synthCacheMiss : Option Expr := some instCacheMiss

/-- Return `b` if `a := b` is already in the synthesize cache
    Otherwise, the following actions are performed:
      - execute `b ← f ()`
      - update cache with `a := b`
      - return `b`

    Assume that `f` returns a hashconsed expression.
-/
@[always_inline, inline]
def withSynthInstanceCache (a : Expr) (f: Unit → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  -- allocation-free probe: `getD` with a sentinel instead of `get?`'s `Option` box
  match (← get).optEnv.synthInstanceCache.getD a synthCacheMiss with
  | none => return none
  | v@(some d) =>
      if !exprEq d instCacheMiss then return v
      else
        let b ← withLocalContext $ do f ()
        updateSynthCache a b
        return b

/-- Return `d` if there is already a synthesize instance for `cstr` in the synthesize cache.
    Otherwise, the following actions are performed:
     - When `LOption.some d ← trySynthInstance cstr`
         - add `cstr := some d` to synthesize cache
         - return `some d`
    - When `trySynthInstance` does not return `LOption.some`:
         - add `cstr := none` to synthesize cache
         - return `none`
-/
def trySynthConstraintInstance? (cstr : Expr) : TranslateEnvT (Option Expr) := do
  withSynthInstanceCache cstr $ fun _ =>
    try
      match (← withConfig (λ c => {c with iota := false, proj := .no}) $ trySynthInstance cstr) with
      | LOption.some d => hashcons d
      | _ => return none
    catch _ =>
      -- catch typeCheck error due to unfolding
      return none

/-- Try to find an instance for `[Decidable e]`. -/
def trySynthDecidableInstance? (e : Expr) : TranslateEnvT (Option Expr) := do
  let dCstr ← mkDecidableConstraint e
  trySynthConstraintInstance? dCstr

/-- Same as `trySynthDecidableInstance` but throws an error when a decidable instance cannot be found. -/
def synthDecidableInstance! (e : Expr) : TranslateEnvT Expr := do
  let some d ← trySynthDecidableInstance? e
    | throwEnvError "synthesize instance for [Decidable {reprStr e}] cannot be found"
  return d

/-- Same as `trySynthDecidableInstance` but cache and return the queried decidable
    constraint when no decidable instance cannot be found.
    In fact, after definitions have been unfolded, it can sometimes be the case
    that Lean can't infer the proper Decidable instance. In this case, we return the queried decidable
    instance.
-/
def synthDecidableWithNotFound! (e : Expr) : TranslateEnvT Expr := do
  match (← trySynthDecidableInstance? e) with
  | none =>
      let cstr ← mkDecidableConstraint e
      updateSynthCache cstr cstr
      return cstr
  | some d => return d

/-- Return `true` only when an instance for `[Inhabited n]` can be found.
    Assume that `n` is a name expression for an inductive datatype.
-/
@[always_inline, inline]
def hasInhabitedInstance (n : Expr) : TranslateEnvT Bool := do
  let inhCstr ← mkAppExpr (← mkInhabitedConst) n
  return (← trySynthConstraintInstance? inhCstr).isSome


/-- Return `true` only when an instance for `[LawfulBEq t beqInst]` can be found. -/
@[always_inline, inline]
def hasLawfulBEqInstance (t : Expr) (beqInst : Expr) : TranslateEnvT Bool := do
  let lawfulCstr ← mkApp2Expr (← mkLawfulBEqConst) t beqInst
  return (← trySynthConstraintInstance? lawfulCstr).isSome


/-- Given an expression `c` and a boolean value `b`, perform the following:
     - When `some d ← trySynthDecidableInstance? c`
        - When b is `true`:
           - return `some $ of_decide_eq_true c d (rfl (Decidable.decide c d))`
        - Otherwise:
            - return `some $ of_decide_eq_false c d (rfl (Decidable.decide c d))`
     - Otherwise (i.e., decidable instance not found)
         - return `none`
-/
def mkOfDecideEqProof? (c : Expr) (b : Bool) : TranslateEnvT (Option Expr) := do
 match (← trySynthDecidableInstance? c) with
 | none => return none
 | some d =>
    let rflInst ← mkApp2Expr (← mkRfl [levelOne]) (← mkBoolType) (← mkApp2Expr (← mkDecide) c d)
    if b
    then mkApp3Expr (← mkOfDecideEqTrue) c d rflInst
    else mkApp3Expr (← mkOfDecideEqFalse) c d rflInst

/-- Given an expression `c` and a boolean value `b`, perform the following:
     let d ← synthDecidableWithNotFound! c
      - When b is `true`:
         - return `some $ of_decide_eq_true c d (rfl (Decidable.decide c d))`
      - Otherwise:
         - return `some $ of_decide_eq_false c d (rfl (Decidable.decide c d))`
-/
def mkOfDecideEqProof (c : Expr) (b : Bool) : TranslateEnvT Expr := do
 let d ← synthDecidableWithNotFound! c
 let rflInst ← mkApp2Expr (← mkRfl [levelOne]) (← mkBoolType) (← mkApp2Expr (← mkDecide) c d)
 if b
 then mkApp3Expr (← mkOfDecideEqTrue) c d rflInst
 else mkApp3Expr (← mkOfDecideEqFalse) c d rflInst

/-- Given `f x₁ ... xₙ`, return `true` only when one of the following conditions is satisfied:
     - `f := BEq.beq` with sort parameter that has a `LawfulBEq` instance
     - `f := LT.lt` with sort parameter in `relationalCompatibleTypes`
     - `f : LE.le` with sort parameter in `relationalCompatibleTypes`

In fact, we can't assume that `BEq.beq`, `LT.lt` and `LE.le` will properly be defined
for any user-defined types or parametric inductive types (e.g., List, Option, etc).
-/
def isOpaqueRelational (f : Name) (args : Array Expr) : TranslateEnvT Bool := do
  match f with
  | `BEq.beq =>
      if args.size < 2 then throwEnvError "isOpaqueRelational: implicit arguments expected"
      hasLawfulBEqInstance args[0]! args[1]!
  | `LT.lt
  | `LE.le =>
      if args.size < 2 then throwEnvError "isOpaqueRelational: implicit arguments expected"
      return (isCompatibleRelationalType args[0]!)
  | _ => return false

end Blaster.Optimize
