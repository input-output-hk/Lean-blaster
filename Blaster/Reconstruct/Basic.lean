import Lean

open Lean Meta

namespace Blaster.Reconstruct

/-- Compose two proof certificates `p₁ : a = b` and `p₂ : b = c` into `p : a = c` via `Eq.trans`. -/
def composeProofs (p₁ p₂ : Expr) : MetaM Expr :=
  mkAppM ``Eq.trans #[p₁, p₂]

/-- Compose two optional proof certificates via `Eq.trans`.
    If either is `none`, the other is returned unchanged. -/
def composeProofs? (opt_p₁ opt_p₂ : Option Expr) : MetaM (Option Expr) :=
  match opt_p₁, opt_p₂ with
  | none, p => return p
  | p, none => return p
  | some p₁, some p₂ => return some (← composeProofs p₁ p₂)

/-- Given a function application f(args) and a proof that one argument was rewritten
    (argProof : origArg = optArg), build a congruence proof that lifts the argument
    rewrite to the application level.

    Finds i such that args[i] = optArg, then builds:
    congrArg (f args[0] ... args[i-1]) argProof : f(..,origArg,..) = f(..,optArg,..)

    Returns none if the rewritten argument cannot be identified. -/
def buildCongrArgFromProof (f : Expr) (args : Array Expr)
    (argProof : Expr) : MetaM (Option Expr) := do
  let proofType ← inferType argProof
  let some (_, _, optArg) := proofType.eq? | return none
  let mut idx : Option Nat := none
  for i in [:args.size] do
    if ← isDefEq args[i]! optArg then
      idx := some i
      break
  let some i := idx | return none
  let partialApp := mkAppN f (args.extract 0 i)
  return some (← mkAppM ``congrArg #[partialApp, argProof])

end Blaster.Reconstruct
