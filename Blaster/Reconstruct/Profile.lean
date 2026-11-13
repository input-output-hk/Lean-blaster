import Lean

open Lean

namespace Blaster.Reconstruct

/-! # Profiling of proof reconstruction

When the environment variable `BLASTER_RECON_PROFILE` refers to a file, the duration of the phases of
proof reconstruction (and of the costly proof obligations) are appended to it, together with the
resident memory of the process, i.e., one line `phase ms rss=… peak=… info` per event.
-/

/-- Return the current and peak resident memory of the process (in MB), as reported by `/proc/self/status`. -/
def residentMemory : IO (Nat × Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let field (k : String) : Nat := Id.run do
      for l in s.splitOn "\n" do
        if l.startsWith k then
          let kb := (l.drop k.length).trim.takeWhile Char.isDigit
          return kb.toNat! / 1024
      return 0
    return (field "VmRSS:", field "VmHWM:")
  catch _ => return (0, 0)

/-- Append `phase` (with duration `ms` and information `info`, only computed when profiling) to the profile
    (see `BLASTER_RECON_PROFILE`). -/
def profileLog (phase : String) (ms : Nat) (info : Unit → String := fun _ => "") : IO Unit := do
  let some f ← IO.getEnv "BLASTER_RECON_PROFILE" | return
  let (rss, peak) ← residentMemory
  let h ← IO.FS.Handle.mk f .append
  h.putStrLn s!"{phase} {ms}ms rss={rss}MB peak={peak}MB {info ()}"

/-- Execute `x` and record its duration as `phase` in the profile (see `BLASTER_RECON_PROFILE`). -/
@[inline] def withProfile [Monad m] [MonadLiftT IO m] (phase : String) (x : m α) (info : α → String := fun _ => "") :
    m α := do
  let start ← (IO.monoMsNow : IO Nat)
  let r ← x
  profileLog phase ((← (IO.monoMsNow : IO Nat)) - start) (fun _ => info r)
  return r

/-- Return `true` when profiling is enabled (see `BLASTER_RECON_PROFILE`). -/
def isProfiling : IO Bool := return (← IO.getEnv "BLASTER_RECON_PROFILE").isSome

/-- Total duration (in ms), number of attempts and number of successes of each strategy used to discharge
    proof obligations (see `profileAttempt`). -/
initialize attemptStats : IO.Ref (Std.HashMap String (Nat × Nat × Nat)) ← IO.mkRef {}

/-- Execute the attempt `x` of strategy `name` and record its outcome in `attemptStats` when profiling. -/
@[inline] def profileAttempt [Monad m] [MonadLiftT IO m] (name : String) (x : m (Option α)) : m (Option α) := do
  if !(← (isProfiling : IO Bool)) then return ← x
  let start ← (IO.monoMsNow : IO Nat)
  let r ← x
  let ms := (← (IO.monoMsNow : IO Nat)) - start
  (attemptStats.modify fun s =>
    let (t, n, k) := s.getD name (0, 0, 0)
    s.insert name (t + ms, n + 1, if r.isSome then k + 1 else k) : IO Unit)
  return r

/-- Report the statistics of the strategies attempted so far in the profile and reset them. -/
def reportAttempts : IO Unit := do
  let s ← attemptStats.swap {}
  for (name, (t, n, k)) in s.toArray.qsort (fun a b => a.2.1 > b.2.1) do
    profileLog s!"attempt:{name}" t fun _ => s!"n={n} ok={k}"

/-- Return the number of distinct subterms (by pointer) of `e` (partial applications excluded), i.e., the size of
    its DAG representation, as visited by the native `Expr.findExt?`. -/
unsafe def dagSizeImpl (e : Expr) : Nat := unsafeBaseIO do
  let n ← IO.mkRef 0
  let step (_ : Expr) : Expr.FindStep := unsafeBaseIO do n.modify (· + 1); return .visit
  -- NOTE: the result of the traversal is used, such that the traversal is not eliminated
  if (e.findExt? step).isSome then return 0
  n.get

@[implemented_by dagSizeImpl]
opaque dagSize (e : Expr) : Nat

/-- Whether the DAG size of `e` (see `dagSize`) is at most `n`, visiting at most `n + 1` subterms. -/
unsafe def dagSizeLeImpl (e : Expr) (n : Nat) : Bool := unsafeBaseIO do
  let k ← IO.mkRef 0
  let step (_ : Expr) : Expr.FindStep := unsafeBaseIO do
    k.modify (· + 1)
    return if (← k.get) > n then .found else .visit
  return (e.findExt? step).isNone

@[implemented_by dagSizeLeImpl]
opaque dagSizeLe (e : Expr) (n : Nat) : Bool

/-- A term containing the terms `es` as a balanced tree of `And` applications (not meant to be type correct), such that
    they are traversed as a whole (e.g., by `dagSizeLe` or `dependsOnSorry`, their shared subterms once) with a
    logarithmic recursion depth. -/
partial def balancedBundle (es : Array Expr) (lo := 0) (hi := es.size) : Expr :=
  if hi ≤ lo + 1 then es.getD lo (mkConst ``True)
  else mkApp2 (mkConst ``And) (balancedBundle es lo ((lo + hi) / 2)) (balancedBundle es ((lo + hi) / 2) hi)

end Blaster.Reconstruct
