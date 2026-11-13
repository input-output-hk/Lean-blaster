import Blaster.Reconstruct.Support

open Lean Meta Elab Term
namespace Blaster.Reconstruct

def kernelOptions (o : Options) : Options := maxHeartbeats.set o 0

/-- `goal` and `proof` closed over the declarations of the local context they depend on (see `fvarClosure`), together
    with these declarations, or `none` when metavariables remain (e.g., in the declarations of the local context, such
    as the universe levels of the hypotheses introduced by `induction`). -/
def closeOverContext? (goal proof : Expr) : MetaM (Option (Array LocalDecl × Expr × Expr)) := do
  let decls ← fvarClosure #[goal, proof]
  let xs := decls.map (·.toExpr)
  let goal ← instantiateMVars (← mkForallFVars xs goal)
  let proof ← instantiateMVars (← mkLambdaFVars xs proof)
  if goal.hasMVar || proof.hasMVar then return none
  return some (decls, goal, proof)

/-- Check `proof` against `goal` with the elaborator's type checker. -/
def elabCheck (goal proof : Expr) : TermElabM (Option MessageData) :=
  tryCatchRuntimeEx (do
      Meta.check proof
      if ← isDefEq (← inferType proof) goal then return none
      return some m!"proof term does not have the expected type")
    fun ex => return some ex.toMessageData

/-- Check `proof` against `goal` with the Lean kernel (in a declaration that is not added to the environment), both
    closed over the declarations of the local context they depend on (e.g., the hypotheses of a goal of the `blaster`
    tactic, see `closeOverContext?`). Incomplete contexts are rejected.
    NOTE: the kernel rather than `Meta.check`, which runs out of recursion depth on deep proofs (e.g., the proofs of the
    `Auction` validator of CardanoLedgerApiBlaster).
-/
def kernelCheck (goal : Expr) (proof : Expr) : TermElabM (Option MessageData) := do
  let goal ← instantiateMVars goal
  let proof ← instantiateMVars proof
  if proof.hasMVar then return some m!"proof term contains metavariables"
  let some (_, goal', proof') ← closeOverContext? goal proof
    | return some m!"the proof or its local context contains unresolved metavariables"
  let lvls := (collectLevelParams {} goal').params.toList
  let name ← mkFreshUserName `_blaster_reconstructed
  let decl := Declaration.thmDecl { name, levelParams := lvls, type := goal', value := proof' }
  -- NOTE: `addDecl` may perform kernel checking asynchronously, i.e., errors are reported
  -- as messages instead of exceptions. We here call the kernel synchronously.
  match Lean.Kernel.Environment.addDecl (← getEnv).toKernelEnv (kernelOptions (← getOptions)) decl with
  | .ok _ => return none
  | .error ex => return some m!"kernel rejected the reconstructed proof: {ex.toMessageData (← getOptions)}"


def checkedProof (checked : IO.Ref (Array (Name × Expr))) (goal proof : Expr) : TermElabM (Except MessageData Expr) := do
  let goal ← instantiateMVars goal
  let proof ← instantiateMVars proof
  -- NOTE: `sorryAx` may occur in auxiliary declarations created by tactics (e.g., after an elaboration
  -- error), which the kernel accepts.
  if ← withProfile "sorryCheck" (dependsOnSorry proof (← checked.get)) then
    return .error m!"the reconstructed proof depends on sorryAx"
  let closed? ← if proof.hasMVar then pure none else closeOverContext? goal proof
  let some (decls, goal', proof') := closed?.filter fun (decls, _, _) => !decls.any (·.isLet)
    | return match ← kernelCheck goal proof with
      | some msg => .error msg
      | none => .ok proof
  let s ← saveState
  tryCatchRuntimeEx (do
      -- NOTE: the declaration is checked synchronously, i.e., kernel errors are reported as exceptions
      let lvls := (collectLevelParams {} goal').params.toList
      let n ← withOptions (fun o => kernelOptions (Elab.async.set o false)) <|
        mkAuxLemma lvls goal' proof' (cache := false)
      checked.modify (·.push (n, proof'))
      return .ok (mkAppN (Lean.mkConst n (lvls.map mkLevelParam)) (decls.map (·.toExpr))))
    fun ex => do
      s.restore
      return .error m!"kernel rejected the reconstructed proof: {ex.toMessageData}"


def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Return the axioms the expression `e` (transitively) depends on. -/
def exprAxioms (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let consts := e.getUsedConstants
  let (_, s) := ((consts.forM fun c => Lean.CollectAxioms.collect c).run env).run {}
  return s.axioms.qsort Name.lt

/-- Check that a proof term only depends on the standard axioms and on `allowed` (e.g., the local
    axioms used as hypotheses). Return the axioms used, or an error message.
-/
def checkProofAxioms (proof : Expr) (allowed : List Name := []) : CoreM (Except MessageData (Array Name)) := do
  let axs ← exprAxioms proof
  let bad := axs.filter fun a => !(standardAxioms.contains a || allowed.contains a)
  if bad.isEmpty then return .ok axs
  return .error m!"the reconstructed proof depends on non-standard axioms: {bad.toList}"


end Blaster.Reconstruct
