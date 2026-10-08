import Lean
import Lean.Meta.Match.MatcherApp.Basic

/-!
# Symbolic exploration: basic utilities

Generic helpers for exploring applications of Prop-valued, fuel-recursive
predicates (for example the observed form of an interpreter's run function).
Nothing here refers to any particular object language or library: the explorer
works with ordinary Lean definitions, their equation theorems, weak-head
reduction, and inductive-type metadata. Exploration only proposes structure;
every step it relies on is later re-checked by the kernel.
-/
namespace Blaster.Proof.Explore
open Lean Meta

register_option blaster.explore.whnfBudget : Nat := {
  defValue := 20000
  descr := "Heartbeat budget (in thousands) for a single weak-head reduction during exploration" }

register_option blaster.explore.progress : Bool := {
  defValue := true
  descr := "Report the explorer's progress on standard error" }

register_option blaster.explore.jobs : Nat := {
  defValue := 4
  descr := "Parallelism of the explorer: its proof statements are replayed on this many \
    threads; twice as many provers (each with its own solver) prove its facts and \
    verification conditions, and four Z3 processes per job search its invariants" }

/-- Whether the explorer reports its progress on standard error. -/
def progressEnabled [Monad m] [MonadOptions m] : m Bool := do
  return blaster.explore.progress.get (← getOptions)

/-- The number of threads for the explorer's independent work (`blaster.explore.jobs`). -/
def jobCount [Monad m] [MonadOptions m] : m Nat := do
  return max 1 (blaster.explore.jobs.get (← getOptions))

/-- `f` on every element of `xs`, on up to `jobs` threads. Each thread starts
from the current state and keeps its own across the elements it takes (its
caches stay warm); no change to the state is returned, so `f` must not depend
on what another element did. An exception of `f` is rethrown (the first, in
the order of `xs`). -/
def parallelMap (jobs : Nat) (xs : Array α) (f : α → MetaM β) : MetaM (Array β) := do
  if jobs ≤ 1 || xs.size ≤ 1 then return ← xs.mapM f
  let next ← IO.mkRef 0
  let worker : MetaM (Array (Nat × Except Exception β)) := do
    let mut out : Array (Nat × Except Exception β) := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some x := xs[i]? | break
      let r ← try pure (Except.ok (← f x)) catch e => pure (Except.error e)
      out := out.push (i, r)
    return out
  let metaCtx ← read
  let metaSt ← get
  let cancelTk? := (← readThe Core.Context).cancelTk?
  let tasks ← (Array.range (min jobs xs.size)).mapM fun _ => do
    -- (each thread with its own names: what one creates never meets another's)
    let (child, parent) := (← getNGen).mkChild
    setNGen parent
    let act ← Core.wrapAsync (fun (_ : Unit) => do
      setNGen child
      worker.run' metaCtx metaSt) cancelTk?
    EIO.asTask (act ()) (prio := .dedicated)
  let mut results : Array (Option (Except Exception β)) := Array.replicate xs.size none
  for task in tasks do
    match ← IO.wait task with
    | .ok rs => for (i, r) in rs do results := results.set! i (some r)
    | .error e => throw e
  results.mapM fun
    | some (.ok b) => pure b
    | some (.error e) => throw e
    | none => throwError "parallelMap: an element was not processed"

/-- Whether `e` is headed by a constructor or is a literal. -/
def isCtorApp (e : Expr) : MetaM Bool := do
  match e.getAppFn with
  | .const n _ => return (← getEnv).find? n |>.any (·.isCtor)
  | .lit _ => return true
  | _ => return false

/-- Inductive type information of a (weak-head normalized) type. -/
def inductiveType? (ty : Expr) : MetaM (Option InductiveVal) := do
  let .const tn _ := ty.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  return some info

/-- `whnf` bounded by a heartbeat budget; `none` when the budget is exhausted. -/
def whnfB (e : Expr) (hb? : Option Nat := none) : MetaM (Option Expr) := do
  let hb := hb?.getD (blaster.explore.whnfBudget.get (← getOptions))
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => {c with maxHeartbeats := hb * 1000})
      (some <$> whnf e))
    fun ex => if ex.isRuntime then return none else throw ex

/-- Delta-expand the head constant of `e` once (including matchers). -/
def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let .const n ls := e.getAppFn | return none
  let some info := (← getEnv).find? n | return none
  let some v := info.value? (allowOpaque := true) | return none
  return some ((v.instantiateLevelParams info.levelParams ls).beta e.getAppArgs)

/-- Replace a subterm by another, skipping closed subterms. -/
def replaceTerm (e a b : Expr) : Expr :=
  e.replace fun t => if !t.hasFVar then some t else if t == a then some b else none

/-- Replace every occurrence of the constant `f` (closed subterms included). -/
def replaceConstTerm (e f b : Expr) : Expr :=
  e.replace fun t => if t == f then some b else none

/-- One top-down pass reducing projections of constructor applications. -/
def projReduce1 (e : Expr) : MetaM Expr := do
  let env ← getEnv
  return e.replace fun t =>
    if !t.hasFVar then some t else
    match t with
    | .proj _ i s =>
      match s.getAppFn with
      | .const c _ =>
        match env.find? c with
        | some (.ctorInfo ci) => s.getAppArgs[ci.numParams + i]?
        | _ => none
      | _ => none
    | .app .. =>
      match t.getAppFn with
      | .const fn _ =>
        match env.getProjectionFnInfo? fn with
        | some info =>
          let args := t.getAppArgs
          if args.size == info.numParams + 1 then
            let s := args[info.numParams]!
            match s.getAppFn with
            | .const c _ =>
              match env.find? c with
              | some (.ctorInfo ci) => s.getAppArgs[ci.numParams + info.i]?
              | _ => none
            | _ => none
          else none
        | none => none
      | _ => none
    | _ => none

/-- Projection reduction to a fixpoint (nested projections of literals). -/
partial def projReduce (e : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let e' ← projReduce1 e
  if e' == e || fuel == 0 then return e' else projReduce e' (fuel - 1)

/-- Constructor applications of an inductive type at given parameters, with the
field types instantiated; used to enumerate split alternatives. -/
def ctorTelescopes (ty : Expr) : MetaM (Option (InductiveVal × Array (Name × Expr))) := do
  let tyW ← whnf ty
  let some info ← inductiveType? tyW | return none
  if info.numIndices != 0 then return none
  let ls := tyW.getAppFn.constLevels!
  let params := tyW.getAppArgs.extract 0 info.numParams
  let mut out := #[]
  for c in info.ctors do
    let cinfo ← getConstInfo c
    let cty ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params
    out := out.push (c, cty)
  return some (info, out)

end Blaster.Proof.Explore
