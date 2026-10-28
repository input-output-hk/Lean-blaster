import Blaster.Smt.Env

open Lean

namespace Blaster.Smt

/-- Require affirmative setup, solving, and model observations from the offline
    probe. Proof export and checked proof-rule coverage are deliberately not
    admission requirements: this is solving/model qualification, not proof
    reconstruction or a claim that native finite-field proofs are checked. -/
def evalFiniteFieldCapabilities (summary : Json) : Except String Unit := do
  let profile ← (← summary.getObjVal? "profile").getStr?
  if profile != "solving" then
    throw "Finite-field capability probe must qualify the solving profile."
  if !(← (← summary.getObjVal? "passed").getBool?) then
    throw "Finite-field offline qualification did not pass."
  let configuration ← summary.getObjVal? "configuration"
  for name in #["version", "config"] do
    if !(← (← (← configuration.getObjVal? name).getObjVal? "passed").getBool?) then
      throw s!"Finite-field offline qualification lacks affirmative {name} validation."
  let capabilities ← summary.getObjVal? "capabilities"
  for name in #["setup", "solving", "model"] do
    if !(← (← (← capabilities.getObjVal? name).getObjVal? "passed").getBool?) then
      throw s!"Finite-field solver lacks affirmative {name} capability."

/-- Parse the offline adapter's summary and exact launch specification. The
    adapter adds `executable` and `argv` from the same validated manifest and
    inventory consumed by `offline_check`; neither is rediscovered from PATH.
    This pure seam performs no IO and can test negative capability observations
    without an installed solver. Supported staged inventories are Linux-only. -/
def parseFiniteFieldCapability (output : String) : Except String SolverCandidate := do
  let summary ← Json.parse output
  evalFiniteFieldCapabilities summary
  let cmd ← (← summary.getObjVal? "executable").getStr?
  if !cmd.startsWith "/" then
    throw "Finite-field qualification must name an absolute staged executable."
  let argv ← (← summary.getObjVal? "argv").getArr?
  let args ← argv.mapM Json.getStr?
  if args.isEmpty then
    throw "Finite-field qualification must include its exact solver argv."
  return { cmd, spawnArgs? := some args }

/-- Adapt the existing offline contract, not a second qualification policy.
    The manifest is loaded once: inventory hashes/identity, configuration and
    protocol fixtures are checked by `offline_check`, then the exact executable
    and argv from that same inventory are attached to its summary. Network
    acquisition is prohibited; missing staging is a hard failure. -/
private def finiteFieldOfflineAdapter : String :=
  "import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from probe_solver import prohibit_network, validate_manifest, offline_check
prohibit_network()
manifest_path = Path(sys.argv[2]).absolute()
root = Path(sys.argv[3]).absolute()
manifest = validate_manifest(manifest_path)
profile = manifest['profiles']['solving']
summary = offline_check(manifest, manifest_path, root, 'solving')
summary['executable'] = str(root / 'solving' / profile['staging']['executable'])
summary['argv'] = profile['argv']
print(json.dumps(summary))
"

/-- Resolve the repository-owned profile from a working directory inside the
checkout, including the isolated child test package. Never search PATH for a
replacement manifest or solver. -/
private partial def finiteFieldProfileRoot (directory : System.FilePath) : IO System.FilePath := do
  if ← (directory / "docs/finite-fields/solver-manifest.json").pathExists then
    return directory
  match directory.parent with
  | some parent =>
      if parent != directory then finiteFieldProfileRoot parent
      else throw <| IO.userError "Finite-field profile manifest not found in this checkout; run from the staged repository"
  | none => throw <| IO.userError "Finite-field profile manifest not found in this checkout; run from the staged repository"

/-- Qualify the separately staged `.artifacts/finite-fields/solving` inventory
    offline and return its exact cvc5 launch candidate. Uses the existing pinned
    manifest/probe contract, never downloads or falls back to ordinary cvc5.
    Call only on the live eligible finite-field branch: dry runs must not call
    this function. Failure is reported before the production SMT session starts.
    Successful setup/solving/model probes do not imply native proof checking. -/
def probeFiniteFieldSolver : IO SolverCandidate := do
  let root ← finiteFieldProfileRoot (← IO.currentDir)
  let result ← try
      IO.Process.output {
        cmd := "python3"
        args := #["-c", finiteFieldOfflineAdapter, "scripts/finite_fields",
          "docs/finite-fields/solver-manifest.json", ".artifacts/finite-fields"]
        cwd := some root
      }
    catch error =>
      throw <| IO.userError s!"Finite-field offline capability probe could not run: {error}"
  if result.exitCode != 0 then
    throw <| IO.userError
      s!"Finite-field offline capability probe failed (exit {result.exitCode}); expected a separately staged .artifacts/finite-fields/solving inventory. No solver fallback or download is permitted.\n{result.stderr}\n{result.stdout}"
  match parseFiniteFieldCapability result.stdout with
  | .ok candidate => return candidate
  | .error error =>
      throw <| IO.userError s!"Finite-field offline capability qualification rejected: {error}"

end Blaster.Smt
