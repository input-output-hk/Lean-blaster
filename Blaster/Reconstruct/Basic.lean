import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster.Reconstruct

/-- Compose two proof certificates `p₁ : a = b` and `p₂ : b = c` into `p : a = c` via `Eq.trans`. -/
def composeProofs (p₁ p₂ : Expr) : MetaM Expr := do
  let t₁ ← inferType p₁
  let some (α, a, b) := t₁.eq? | throwError "composeProofs: p₁ is not an equality proof"
  let t₂ ← inferType p₂
  let some (_, _, c) := t₂.eq? | throwError "composeProofs: p₂ is not an equality proof"
  let u ← getLevel α
  return mkApp6 (mkConst ``Eq.trans [u]) α a b c p₁ p₂

/-- Compose two optional proof certificates via `Eq.trans`.
    If either is `none`, the other is returned unchanged. -/
def composeProofs? (opt_p₁ opt_p₂ : Option Expr) : MetaM (Option Expr) :=
  match opt_p₁, opt_p₂ with
  | none, p => return p
  | p, none => return p
  | some p₁, some p₂ =>
      try
        return some (← composeProofs p₁ p₂)
      catch _ => return none

/-- Detect if the difference between `origExpr` and `optExpr` is a simple
    commutativity swap at the top level, and return the corresponding proof.
    Returns `some (a_comm a b : a ⊕ b = b ⊕ a)` when `origExpr = a ⊕ b`
    and `optExpr = b ⊕ a`. -/
def detectReorderProof (origExpr optExpr : Expr) : Option Expr :=
  if Blaster.Optimize.exprEq origExpr optExpr then none
  else
    let origAll := origExpr.getAppArgs
    let optAll := optExpr.getAppArgs
    if origAll.size < 2 || optAll.size < 2 then none
    else
      let origA := origAll[origAll.size - 2]!
      let origB := origAll[origAll.size - 1]!
      let optA := optAll[optAll.size - 2]!
      let optB := optAll[optAll.size - 1]!
      if !exprEqOrNatEq origA optB || !exprEqOrNatEq origB optA then none
      else
        let (f, _) := Blaster.Optimize.getAppFnWithArgs optExpr
        match f with
        | Expr.const n _ =>
          match n with
          | ``Nat.add => some (mkApp2 (mkConst ``Nat.add_comm) optB optA)
          | ``Nat.mul => some (mkApp2 (mkConst ``Nat.mul_comm) optB optA)
          | _ => none
        | _ => none
  where
    getNatValue? (e : Expr) : Option Nat :=
      match Blaster.Optimize.isNatValue? e with
      | some n => some n
      | none =>
        match e.getAppFn with
        | Expr.const ``OfNat.ofNat _ =>
            let args := e.getAppArgs
            if args.size >= 2 then Blaster.Optimize.isNatValue? args[1]!
            else none
        | _ => none
    exprEqOrNatEq (a b : Expr) : Bool :=
      if Blaster.Optimize.exprEq a b then true
      else match getNatValue? a, getNatValue? b with
        | some n1, some n2 => n1 == n2
        | _, _ => false

/-- Fallback for detecting commutativity between expressions in different
    representations (e.g., `HAdd.hAdd` vs `Nat.add`). Uses `isDefEq` to compare operands.
    Returns a proof `origExpr = targetExpr` via the appropriate commutativity lemma.
    Only invoked when `detectReorderProof` fails due to representation mismatch. -/
def detectReorderBridge (origExpr targetExpr : Expr) : MetaM (Option Expr) := do
  let origAll := origExpr.getAppArgs
  let tgtAll := targetExpr.getAppArgs
  if origAll.size < 2 || tgtAll.size < 2 then return none
  let origA := origAll[origAll.size - 2]!
  let origB := origAll[origAll.size - 1]!
  let tgtA := tgtAll[tgtAll.size - 2]!
  let tgtB := tgtAll[tgtAll.size - 1]!
  let swapped ← withNewMCtxDepth do
    if !(← isDefEq origA tgtB) then return false
    isDefEq origB tgtA
  if !swapped then return none
  let commLemma? := findCommLemma origExpr <|> findCommLemma targetExpr
  match commLemma? with
  | some lemma => return some (mkApp2 (mkConst lemma) tgtB tgtA)
  | none => return none
where
  findCommLemma (e : Expr) : Option Name :=
    match e.getAppFn' with
    | Expr.const ``Nat.add _ => some ``Nat.add_comm
    | Expr.const ``Nat.mul _ => some ``Nat.mul_comm
    | Expr.const ``HAdd.hAdd _ =>
        let args := e.getAppArgs
        if args.size >= 1 then
          if let Expr.const ``Nat _ := args[0]! then some ``Nat.add_comm else none
        else none
    | Expr.const ``HMul.hMul _ =>
        let args := e.getAppArgs
        if args.size >= 1 then
          if let Expr.const ``Nat _ := args[0]! then some ``Nat.mul_comm else none
        else none
    | _ => none

/-- Tag for annotating proofs already at the application level -/
def appLevelProofKey : Name := `_blaster.appLevelProof

/-- Given a function application `f(args)` and a proof that one argument was rewritten
    (`argProof : origArg = optArg`), build a congruence proof that lifts the rewrite
    to the full application level.

    Uses a reverse `isDefEq` search to find `i` such that `args[i]` matches `optArg`.
    Then builds:
      `congrFun (... (congrFun (congrArg (f a₀..a_{i-1}) proof) a_{i+1}) ...) a_{n-1}`

    If `argProof` is annotated with `appLevelProofKey` (i.e., it is already an app-level
    proof from `buildMultiArgCongrProof`), it is returned as-is to avoid double-lifting.

    Returns `none` if the rewritten argument cannot be identified. -/
def buildCongrArgFromProof (f : Expr) (args : Array Expr) (argProof : Expr)
    : MetaM (Option Expr) := do
  if let Expr.mdata d _ := argProof then
    if d.getBool appLevelProofKey false then
      return some argProof
  try
    let proofType ← inferType argProof
    let some (_, _origArg, optArg) := proofType.eq? | return none
    let mut idx? : Option Nat := none
    for i in [:args.size] do
      let i' := args.size - 1 - i
      if ← isDefEq args[i']! optArg then
        idx? := some i'
        break
    match idx? with
    | some idx =>
        let partialApp := mkAppN f (args[:idx])
        let mut p ← mkCongrArg partialApp argProof
        for j in [idx + 1 : args.size] do
          p ← mkCongrFun p args[j]!
        return some p
    | none => return none
  catch _ => return none

/-- Build a combined congruence proof when multiple arguments were rewritten.

    Given `f(origArgs)` where some `origArgs[i]` were rewritten to `args[i]` with
    `argProofs[i]`, composes individual congruence steps:
      `f(orig₀, orig₁, ...) = f(opt₀, orig₁, ...) = f(opt₀, opt₁, ...) = ...`

    The result is annotated with `appLevelProofKey` so that downstream calls to
    `buildCongrArgFromProof` return it as-is rather than attempting to double-lift. -/
def buildMultiArgCongrProof (f : Expr) (origArgs args : Array Expr)
    (argProofs : Array (Option Expr)) (carriedProof : Option Expr)
    : MetaM (Option Expr) := do
  let mut rewrittenIndices := #[]
  for i in [:argProofs.size] do
    if let some _ := argProofs[i]! then
      if !exprEq origArgs[i]! args[i]! then
        rewrittenIndices := rewrittenIndices.push i
  if rewrittenIndices.isEmpty then return carriedProof
  let mut composedProof : Option Expr := carriedProof
  let mut currentArgs := origArgs
  for i in rewrittenIndices do
    if let some ap := argProofs[i]! then
      try
        let partialApp := mkAppN f (currentArgs[:i])
        let mut step ← mkCongrArg partialApp ap
        for j in [i + 1 : currentArgs.size] do
          step ← mkCongrFun step currentArgs[j]!
        currentArgs := currentArgs.set! i args[i]!
        composedProof ← composeProofs? composedProof (some step)
      catch _ => currentArgs := currentArgs.set! i args[i]!
  return match composedProof with
    | some p => some (Expr.mdata (MData.empty.setBool appLevelProofKey true) p)
    | none => none

/-- Resolve the proof for an `Eq` argument, bridging a potential gap between
    the proof source and the original expression.

    When `argProof` is `none`, falls back to `detectReorderProof`.

    When `argProof` is `some p` with `p : source = optArg`:
    - If `source` matches `origArg` syntactically, returns `some p` unchanged.
    - Otherwise, tries `detectReorderProof` (pure) then `detectReorderBridge` (MetaM)
      to obtain `bridge : origArg = source`, and composes `Eq.trans bridge p`. -/
def resolveArgProof (argProof : Option Expr) (origArg optArg : Expr) : MetaM (Option Expr) :=
  match argProof with
  | none => pure (detectReorderProof origArg optArg)
  | some p => do
    let proofType ← inferType p
    match proofType.eq? with
    | some (_, proofSrc, _) =>
        if Blaster.Optimize.exprEq proofSrc origArg then
          pure (some p)
        else
          match detectReorderProof origArg proofSrc with
          | some bridge => composeProofs? (some bridge) (some p)
          | none =>
              match ← detectReorderBridge origArg proofSrc with
              | some bridge => composeProofs? (some bridge) (some p)
              | none => pure (some p)
    | none => pure (some p)

/-- Build a proof of `orig_lhs = orig_rhs` from individual `Eq` argument proofs
    when both sides have been optimized to the same expression.

    Given:
    - `lhsProof : orig_lhs = opt_lhs` (or `none` if LHS unchanged)
    - `rhsProof : orig_rhs = opt_rhs` (or `none` if RHS unchanged)
    - `opt_lhs` and `opt_rhs` are definitionally equal

    Constructs `Eq.trans lhsProof (Eq.symm rhsProof) : orig_lhs = orig_rhs`
    with the appropriate simplification when either side is `none` (rfl). -/
def buildEqReflProof (lhsProof rhsProof : Option Expr) : MetaM (Option Expr) :=
  match lhsProof, rhsProof with
  | none, none => pure none
  | some p, none => pure (some p)
  | none, some p => do
      try return some (← mkAppM ``Eq.symm #[p])
      catch _ => return none
  | some p1, some p2 => do
      try
        let p2' ← mkAppM ``Eq.symm #[p2]
        return some (← mkAppM ``Eq.trans #[p1, p2'])
      catch _ => return none

end Blaster.Reconstruct
