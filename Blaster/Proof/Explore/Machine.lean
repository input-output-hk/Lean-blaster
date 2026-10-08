import Blaster.Proof.Explore.Basic

/-!
# Symbolic exploration: the machine interface

A *machine* is a family of Prop-valued predicates whose last argument is fuel,
each with a checked unfolding equation (for example the predicates produced by
`Induction.Observed`). A *state* is a fuel-less application `P a₁ … aₖ` of such
a predicate. One exploration step instantiates `P`'s equation with fuel
`m + pad`, keeps every machine predicate opaque, and weak-head reduces. The
result is `True`, `False`, some other leaf proposition, another state applied to
fuel, or an expression stuck on symbolic data. Nothing here refers to a
particular object language.
-/
namespace Blaster.Proof.Explore
open Lean Meta

/-- A predicate of a machine. -/
structure Pred where
  /-- Closed lambda `fun a₁ … aₖ n => body` (the checked equation's right side). -/
  body : Expr
  /-- `k`: its arguments besides the fuel. -/
  arity : Nat
  /-- Checked theorem `name = body`, used to unfold the predicate in proofs. -/
  eqn? : Option Name := none
deriving Inhabited

/-- A machine: its predicates, and how a step is taken. -/
structure Machine where
  preds : Std.HashMap Name Pred
  /-- The fuel variable used for exploration steps. -/
  fuel : Expr
  /-- Fuel padding: one step is taken at fuel `fuel + pad`. -/
  pad : Nat
  /-- Type of program code, if the initial state contains a large closed term. -/
  codeType? : Option Expr := none
deriving Inhabited

/-- Result of reducing a step or a resumed step. -/
inductive StepResult where
  /-- `True`. -/
  | accept
  /-- `False`. -/
  | reject
  /-- A proposition that is neither a machine state nor `True`/`False`. -/
  | leaf (p : Expr)
  /-- Another state, to be applied to the fuel. -/
  | next (state : Expr)
  /-- A reduction stuck on symbolic data. -/
  | stuck (e : Expr)
deriving Inhabited

/-- The predicate of the state `s`, if it is one of the machine's. -/
def Machine.pred? (M : Machine) (s : Expr) : Option Pred :=
  match s.getAppFn with
  | .const n _ => M.preds[n]?
  | _ => none

/-- The fuel expression `m + k`. -/
def fuelPlus (m : Expr) (k : Nat) : Expr :=
  if k == 0 then m else mkNatAdd m (mkNatLit k)

/-- Run `k` with every machine predicate irreducible, so that weak-head
reduction stops at predicate applications. The environment is restored. -/
def Machine.withOpaque (M : Machine) (k : MetaM α) : MetaM α := do
  let names := M.preds.toList.map (·.1)
  let saved ← names.mapM fun n => do return (n, ← getReducibilityStatus n)
  try
    for n in names do setReducibilityStatus n .irreducible
    k
  finally
    for (n, st) in saved do setReducibilityStatus n st

/-- Weak-head reduction (inside `withOpaque` it never unfolds a predicate). -/
def Machine.whnf (_M : Machine) (e : Expr) (hb? : Option Nat := none) : MetaM (Option Expr) :=
  whnfB e hb?

/-- What the reduced step `r` is. -/
def Machine.classify (M : Machine) (r : Expr) : StepResult :=
  if r.isConstOf ``True then .accept
  else if r.isConstOf ``False then .reject
  else match M.pred? r with
    | some p =>
      if r.getAppNumArgs == p.arity + 1 then .next r.appFn!
      else .stuck r
    | none => .stuck r

/-- For `P a₁ … aₖ n`: a proof of `P a₁ … aₖ n = body a₁ … aₖ n` and the
right side, from the predicate's checked equation. -/
def Machine.unfoldProof? (M : Machine) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some p := M.pred? e | return none
  unless e.getAppNumArgs == p.arity + 1 do return none
  let some eqn := p.eqn? | return none
  let mut h := mkConst eqn
  for a in e.getAppArgs do h ← mkAppM ``congrFun #[h, a]
  return some (h, p.body.beta e.getAppArgs)

/-- The expression whose reduction takes one step from state `s`. -/
def Machine.stepExpr (M : Machine) (s : Expr) : Option Expr := do
  let p ← M.pred? s
  return p.body.beta (s.getAppArgs.push (fuelPlus M.fuel M.pad))

/-- Continue reducing an expression produced while resolving a stuck step. -/
def Machine.resume (M : Machine) (e : Expr) : MetaM (Option StepResult) := do
  let some r ← M.whnf e | return none
  let res := M.classify r
  match res with
  | .stuck r =>
    -- a proposition that is not a machine state is a leaf
    if (← isProp r) && !(← isStuckMatch r) then return some (.leaf r) else return some res
  | _ => return some res
where
  /-- Propositions that are still matches/recursor applications are stuck, not leaves. -/
  isStuckMatch (r : Expr) : MetaM Bool := do
    if (← matchMatcherApp? r (alsoCasesOn := true)).isSome then return true
    match r.getAppFn with
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.recInfo _) => return true
      | _ => return false
    | _ => return false

/-- The argument arrays of the occurrences of constant `n` in `e`: of each
application of `n` (its whole spine) and of each unapplied reference. -/
private partial def occurrences (n : Name) (e : Expr) (acc : Array (Array Expr) := #[]) :
    Array (Array Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let acc := if fn.isConstOf n then acc.push e.getAppArgs else occurrences n fn acc
    e.getAppArgs.foldl (fun acc a => occurrences n a acc) acc
  | .const .. => if e.isConstOf n then acc.push #[] else acc
  | .lam _ d b _ | .forallE _ d b _ => occurrences n b (occurrences n d acc)
  | .letE _ t v b _ => occurrences n b (occurrences n v (occurrences n t acc))
  | .mdata _ b | .proj _ _ b => occurrences n b acc
  | _ => acc

/-- Does every step of predicate `n` pass its argument `i` on unchanged (each
application of `n` in its equation repeats the parameter)? Such an argument (a
table of procedures, say) is fixed for the whole run. `false` when the equation
applies `n` nowhere. -/
def Machine.passesThrough (M : Machine) (n : Name) (i : Nat) : MetaM Bool := do
  let some p := M.preds[n]? | return false
  lambdaBoundedTelescope p.body (p.arity + 1) fun params body => do
    let some x := params[i]? | return false
    let calls := occurrences n body
    return !calls.isEmpty && calls.all (·[i]? == some x)

/-- One step from state `s`. `none` when the reduction budget is exhausted. -/
def Machine.step (M : Machine) (s : Expr) : MetaM (Option StepResult) := do
  let some e := M.stepExpr s | return some (.stuck s)
  M.resume e

private partial def maxClosed (e : Expr) (best : Option (Nat × Expr)) :
    StateT (Std.HashMap UInt64 Nat) MetaM (Option (Nat × Expr)) := do
  let size ← sizeOf' e
  if !e.hasFVar && !e.hasLooseBVars && e.isApp then
    if best.any (·.1 ≥ size) then return best
    let ty0 ← inferType e
    -- instance dictionaries (an `IsData` encoder) are closed data, not program code
    if (← isClass? ty0).isSome then return best
    let ty ← whnf ty0
    if (← inductiveType? ty).isSome then return some (size, e)
  match e with
  | .app f a => do
    let best ← maxClosed f best
    maxClosed a best
  | .lam _ t b _ | .forallE _ t b _ => do
    let best ← maxClosed t best
    maxClosed b best
  | .mdata _ b | .proj _ _ b => maxClosed b best
  | .letE _ t v b _ => do
    let best ← maxClosed t best
    let best ← maxClosed v best
    maxClosed b best
  | _ => return best
where
  sizeOf' (e : Expr) : StateT (Std.HashMap UInt64 Nat) MetaM Nat := do
    let h := hash e
    if let some n := (← get)[h]? then return n
    let n ← match e with
      | .app f a => do pure ((← sizeOf' f) + (← sizeOf' a) + 1)
      | .lam _ t b _ | .forallE _ t b _ => do pure ((← sizeOf' t) + (← sizeOf' b) + 1)
      | .mdata _ b | .proj _ _ b => do pure ((← sizeOf' b) + 1)
      | .letE _ t v b _ => do pure ((← sizeOf' t) + (← sizeOf' v) + (← sizeOf' b) + 1)
      | _ => pure 1
    modify (·.insert h n)
    return n

/-- The type of program code: the inductive type of the largest closed
application in the initial state, when it is substantially large. For a list
(a program as a sequence of statements) it is the element type: the machine's
continuations are then lists of code too. -/
def detectCodeType (initial : Expr) (minSize : Nat := 64) : MetaM (Option Expr) := do
  let (best, _) ← (maxClosed initial none).run {}
  let some (size, e) := best | return none
  if size < minSize then return none
  let mut ty ← whnf (← inferType e)
  if ty.isAppOfArity ``List 1 then ty ← whnf ty.appArg!
  if (← inductiveType? ty).isNone then return none
  return some ty

/-- Build a machine from predicate equations `P = fun a₁ … aₖ n => body`.
The fuel padding is the smallest one (up to 8) at which no predicate's unfolding
is stuck on the fuel variable. -/
def Machine.ofEquations (eqs : Array (Name × Expr × Option Name)) (fuel : Expr) : MetaM Machine := do
  let mut preds : Std.HashMap Name Pred := {}
  for (name, body, eqn?) in eqs do
    let arity := body.getNumHeadLambdas - 1
    preds := preds.insert name {body, arity, eqn?}
  let M0 : Machine := {preds, fuel, pad := 0}
  M0.withOpaque do
  let mut pad := 1
  for (_, p) in preds.toList do
    let ty ← inferType p.body
    let need ← forallBoundedTelescope ty (some p.arity) fun args _ => do
      for d in [1:9] do
        let some r ← M0.whnf (p.body.beta (args.push (fuelPlus fuel d))) | return d
        unless ← stuckOnFuel r do return d
      return 8
    pad := max pad need
  return {M0 with pad}
where
  stuckOnFuel (r : Expr) : MetaM Bool := do
    if let some m ← matchMatcherApp? r (alsoCasesOn := true) then
      for d in m.discrs do
        let d ← whnfR d
        if d == fuel then return true
        if d.isAppOfArity ``HAdd.hAdd 6 && d.appFn!.appArg! == fuel then return true
    return false

end Blaster.Proof.Explore
