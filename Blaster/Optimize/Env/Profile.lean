import Blaster.Optimize.Env.Types

open Lean
namespace Blaster.Optimize

register_option blaster.profileNormalize : Bool := {
  defValue := false
  descr := "Emit opt-in normalization-head timing and rewrite-cache diagnostics"
}

/-- Charge elapsed wall time to the innermost uncached normalization head.
Anonymous expressions inherit their enclosing head. `selfNs` is exclusive of
nested named heads, includes diagnostic overhead, and is not CPU time.
-/
private def charge (p : NormalizationProfile) (now : Nat) : NormalizationProfile := Id.run do
  let owner := p.owners.headD `_normalizer
  let entry := p.entries.getD owner {}
  return { p with
    lastNs := now
    entries := p.entries.insert owner { entry with selfNs := entry.selfNs + now - p.lastNs } }

def profileReport (status : String) : TranslateEnvT Unit := do
  let some ref := (← get).optEnv.options.profile? | return
  let now ← IO.monoNanosNow
  ref.modify (charge · now)
  let p ← ref.get
  let o := (← get).optEnv
  let entries := p.entries.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let heads := entries.map fun (name, e) => Json.mkObj [
    ("head", toJson name.toString), ("calls", toJson e.calls), ("self_ns", toJson e.selfNs)]
  let events := p.events.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let payload := (Json.mkObj [
    ("schema", toJson (1 : Nat)), ("status", toJson status),
    ("elapsed_ns", toJson (now - p.startedNs)),
    ("active_frames", toJson p.owners.length), ("imbalances", toJson p.imbalances),
    ("cache_hits", toJson p.hits), ("cache_misses", toJson p.misses),
    ("cache_bypasses", toJson p.bypasses),
    ("hashcons", toJson o.hashConsCache.size), ("contexts", toJson o.options.nextCtxId),
    ("heads", Json.arr heads),
    ("events", Json.mkObj (events.toList.map fun (n, count) => (n.toString, toJson count)))]).compress
  if let some path ← IO.getEnv "BLASTER_PROFILE_FILE" then
    -- Lean may buffer command stdout. Flush a separate JSONL stream so the
    -- benchmark runner can retain progress even when it kills the process.
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn payload
      handle.flush
  else
    IO.println ("BLASTER_PROFILE " ++ payload)

@[inline] def profileEvent (name : Name) : TranslateEnvT Unit := do
  if let some ref := (← get).optEnv.options.profile? then
    ref.modify fun p => { p with events := p.events.insert name (p.events.getD name 0 + 1) }

@[inline] def profileCacheHit : TranslateEnvT Unit := do
  if let some ref := (← get).optEnv.options.profile? then
    ref.modify fun p => { p with hits := p.hits + 1 }

def profileEnter (e : Expr) (bypass : Bool) : TranslateEnvT Unit := do
  let some ref := (← get).optEnv.options.profile? | return
  let now ← IO.monoNanosNow
  ref.modify fun p =>
    let p := charge p now
    let owner := match e.getAppFn with
      | .const n _ => n
      | _ => p.owners.headD `_normalizer
    let entry := p.entries.getD owner {}
    { p with
      owners := owner :: p.owners
      entries := p.entries.insert owner { entry with calls := entry.calls + 1 }
      misses := p.misses + (if bypass then 0 else 1)
      bypasses := p.bypasses + (if bypass then 1 else 0) }
  let p ← ref.get
  -- Bounded-frequency snapshots survive a benchmark runner's time/memory kill.
  if (p.misses + p.bypasses) % 1000000 == 0 then profileReport "progress"

def profileLeave : TranslateEnvT Unit := do
  let some ref := (← get).optEnv.options.profile? | return
  let now ← IO.monoNanosNow
  ref.modify fun p =>
    let p := charge p now
    match p.owners with
    | [] => { p with imbalances := p.imbalances + 1 }
    | _ :: rest => { p with owners := rest }

end Blaster.Optimize
