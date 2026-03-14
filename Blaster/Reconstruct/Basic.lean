import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

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

/-- Tag for annotating the argument position from the end. -/
def argPosFromEndKey : Name := `_blaster.argPosFromEnd

/-- Annotate the proof with the position relative to the end, so it survives
    unfolding (which strips implicit args from the front).
    Compares args against origArgs via isDefEq to find which argument
    was actually rewritten, ignoring definitionally equal changes. -/
def annotateProofWithPosFromEnd
    (args : Array Expr) (origArgs : Array Expr) (argProofs : Array (Option Expr))
    (proof : Option Expr) : TranslateEnvT (Option Expr) := do
  match proof with
  | none => return none
  | some p =>
    let mut proofIdx? : Option Nat := none
    for i in [:argProofs.size] do
      if (argProofs[i]!).isSome then
        let unchanged ← try
            withLocalContext $
              withNewMCtxDepth $
              withReducible $
              isDefEq args[i]! origArgs[i]!
          catch _ => pure false
        if !unchanged then
          proofIdx? := some i
    match proofIdx? with
    | some proofIdx =>
      let posFromEnd := args.size - 1 - proofIdx
      return some (Expr.mdata (MData.empty.setNat argPosFromEndKey posFromEnd) p)
    | none => return some p

/-- Given a function application f(args) and a proof that one argument was rewritten
    (argProof : origArg = optArg), build a congruence proof that lifts the rewrite
    to the full application level.
    Finds i such that args[i] was rewritten, using either an MData annotation
    encoding position-from-end, or a reverse isDefEq search as fallback.
    Then builds:
      congrFun (... (congrFun (congrArg (f a₀..a_{i-1}) proof) a_{i+1}) ...) a_{n-1}
    Returns none if the rewritten argument cannot be identified. -/
def buildCongrArgFromProof (f : Expr) (args : Array Expr) (argProof : Expr)
    : MetaM (Option Expr) := do
  let (proof, annotatedIdx?) := match argProof with
    | Expr.mdata d p =>
      let posFromEnd := d.getNat argPosFromEndKey args.size
      if posFromEnd < args.size then
        let idx := args.size - 1 - posFromEnd
        (p, some idx)
      else
        (argProof, none)
    | _ => (argProof, none)
  let proofType ← inferType proof
  let some (_, _origArg, optArg) := proofType.eq? | return none
  let idx? ← match annotatedIdx? with
    | some idx => pure (some idx)
    | none =>
      let mut found := none
      for i in [:args.size] do
        let i' := args.size - 1 - i
        if ← isDefEq args[i']! optArg then
          found := some i'
          break
      pure found
  match idx? with
  | some idx =>
    let partialApp := mkAppN f (args[:idx])
    let mut p ← mkCongrArg partialApp proof
    for j in [idx + 1 : args.size] do
      p ← mkCongrFun p args[j]!
    return some p
  | none => return none

end Blaster.Reconstruct
