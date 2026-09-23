import Blaster

namespace Test.SolverVersion

open Blaster.Smt Blaster.Options

/-! ## Test objectives to validate solver version parsing and enforcement

    These tests exercise the pure version policy of `Blaster.Smt.Env`:
    version-token extraction from solver banners (`parseVersionNumbers`),
    dotted-version comparison (`versionAtLeast`), the fail-closed banner
    check (`checkVersionBanner`) and the per-candidate acceptance policy
    (`evalCandidateProbe`) shared by solver discovery and the `solvercheck`
    executable. Probe outcomes are pure data (`ProbeOutcome`), so no process
    is spawned: the banners below are synthetic fixtures representing supported
    z3/cvc5 banner shapes. Rejection reasons are asserted by selected prefixes
    and substrings rather than whole sentences, keeping each guard focused while
    intentionally pinning its actionable wording.
-/

/-! # `parseVersionNumbers`: version-token extraction from banners -/

-- A bare dotted version (the shape of `SolverDescriptor.minVersion`)
#guard parseVersionNumbers "4.15.2" == some [4, 15, 2]
-- Synthetic z3 banner fixture in a supported release shape
#guard parseVersionNumbers "Z3 version 4.15.2 - 64 bit" == some [4, 15, 2]
-- Synthetic cvc5 release-banner fixture (the `[git …]` suffix must not confuse parsing)
#guard parseVersionNumbers "cvc5 version 1.2.1 [git abc on branch HEAD]" == some [1, 2, 1]
-- Synthetic cvc5 dev/nightly fixture: parsing stops before the `-dev…` suffix
#guard parseVersionNumbers "cvc5 version 1.3.5-dev.105.abcdef" == some [1, 3, 5]
-- The version token may be preceded by arbitrary words
#guard parseVersionNumbers "some solver wrapper reporting 9.8.7 here" == some [9, 8, 7]
-- No dotted version anywhere → `none` (feeds the fail-closed policy below)
#guard parseVersionNumbers "unknown build" == none
#guard parseVersionNumbers "" == none
-- A lone integer is not a version token: a dot is required
#guard parseVersionNumbers "version 4" == none

/-! # `versionAtLeast`: dotted-version comparison -/

-- A version satisfies itself
#guard versionAtLeast [4, 15, 2] [4, 15, 2]
-- Strictly newer in major / minor / patch position
#guard versionAtLeast [5, 0, 0] [4, 15, 2]
#guard versionAtLeast [4, 16, 0] [4, 15, 2]
#guard versionAtLeast [4, 15, 3] [4, 15, 2]
-- Strictly older in major / minor / patch position (large later components
-- cannot compensate for a smaller earlier one)
#guard !versionAtLeast [3, 99, 99] [4, 15, 2]
#guard !versionAtLeast [4, 14, 99] [4, 15, 2]
#guard !versionAtLeast [4, 15, 1] [4, 15, 2]
-- Missing components count as zero: `1.2` and `1.2.0` are equal both ways
#guard versionAtLeast [1, 2] [1, 2, 0]
#guard versionAtLeast [1, 2, 0] [1, 2]
-- Longer vs shorter beyond the zero-padding case
#guard versionAtLeast [1, 2, 1] [1, 2]
#guard !versionAtLeast [1, 2] [1, 2, 1]

/-! # `checkVersionBanner`: fail-closed banner check -/

-- Exactly the minimal version is accepted
#guard checkVersionBanner "4.15.2" "Z3 version 4.15.2 - 64 bit" == .ok
-- Newer than the minimal version is accepted
#guard checkVersionBanner "1.2.1" "cvc5 version 1.3.4 [git tag 1.3.4]" == .ok
-- Below the minimal version: rejected, carrying the components found
#guard checkVersionBanner "4.15.2" "Z3 version 4.8.10 - 64 bit" == .tooOld [4, 8, 10]
-- Fail closed: a banner without a parseable version is rejected…
#guard checkVersionBanner "4.15.2" "unknown build" == .unparseable
-- …but an unparseable `minVersion` (a Blaster bug, not a user error) imposes
-- no lower bound instead of rejecting every solver
#guard checkVersionBanner "unset" "Z3 version 0.1.0 - 64 bit" == .ok

/-! # `evalCandidateProbe`: the candidate acceptance policy

     Probe outcomes are replayed as pure data against the real z3/cvc5
     descriptors, so the actual minimal supported versions are enforced. -/

/-- The rejection reason of a probe verdict, `""` when accepted. -/
private def rejectionOf : Except String Unit → String
  | .ok () => ""
  | .error reason => reason

/-- `true` iff the verdict is a rejection whose reason mentions `part`. -/
private def rejectedMentioning (part : String) (verdict : Except String Unit) : Bool :=
  ((rejectionOf verdict).splitOn part).length > 1

/-- `true` iff the candidate is accepted. -/
private def accepted : Except String Unit → Bool
  | .ok () => true
  | .error _ => false

private def z3Desc := SmtSolver.z3.descriptor
private def cvc5Desc := SmtSolver.cvc5.descriptor

-- Pin cvc5's production floor at the exact supported boundary. These guards
-- deliberately use the real descriptor rather than repeating the floor as the
-- minimum argument: lowering `cvc5Desc.minVersion` makes the second guard fail.
#guard checkVersionBanner cvc5Desc.minVersion
  "cvc5 version 1.2.1 [git tag 1.2.1]" == .ok
#guard checkVersionBanner cvc5Desc.minVersion
  "cvc5 version 1.2.0 [git tag 1.2.0]" == .tooOld [1, 2, 0]

/-! # `SolverCandidate`: exact native and WSL process invocations -/

private def nativeZ3 := z3Desc.candidates[0]!
private def wslZ3 := z3Desc.candidates[1]!
private def nativeCvc5 := cvc5Desc.candidates[0]!
private def wslCvc5 := cvc5Desc.candidates[1]!

private def nativeZ3ProbeInvocation : Bool :=
  z3Desc.probeInvocation nativeZ3 == ("z3", #["-version"])
private def nativeZ3SpawnInvocation : Bool :=
  z3Desc.spawnInvocation nativeZ3 == ("z3", #["-in", "-smt2"])
private def nativeCvc5ProbeInvocation : Bool :=
  cvc5Desc.probeInvocation nativeCvc5 == ("cvc5", #["--version"])
private def nativeCvc5SpawnInvocation : Bool :=
  cvc5Desc.spawnInvocation nativeCvc5 ==
    ("cvc5", #["--lang", "smt2", "--incremental", "--parsing-mode=lenient", "--dt-nested-rec"])
private def wslZ3ProbeInvocation : Bool :=
  z3Desc.probeInvocation wslZ3 == ("wsl", #["z3", "-version"])
private def wslZ3SpawnInvocation : Bool :=
  z3Desc.spawnInvocation wslZ3 == ("wsl", #["z3", "-in", "-smt2"])
private def wslCvc5ProbeInvocation : Bool :=
  cvc5Desc.probeInvocation wslCvc5 == ("wsl", #["cvc5", "--version"])
private def wslCvc5SpawnInvocation : Bool :=
  cvc5Desc.spawnInvocation wslCvc5 ==
    ("wsl", #["cvc5", "--lang", "smt2", "--incremental", "--parsing-mode=lenient", "--dt-nested-rec"])

#guard nativeZ3ProbeInvocation
#guard nativeZ3SpawnInvocation
#guard nativeCvc5ProbeInvocation
#guard nativeCvc5SpawnInvocation
#guard wslZ3ProbeInvocation
#guard wslZ3SpawnInvocation
#guard wslCvc5ProbeInvocation
#guard wslCvc5SpawnInvocation

-- A probe that could not run at all is reported as an IO error…
#guard rejectedMentioning "IO error"
  (evalCandidateProbe z3Desc nativeZ3 (.failed "no such file or directory"))
-- …and every report line names the exact candidate that was probed
#guard "Candidate 'wsl z3'".isPrefixOf
  (rejectionOf (evalCandidateProbe z3Desc wslZ3 (.failed "wsl: not found")))
-- A probe that ran but exited non-zero is rejected with its exit code
#guard rejectedMentioning "exit code" (evalCandidateProbe z3Desc nativeZ3 (.ran 1 ""))
-- Synthetic healthy-banner fixtures are accepted (z3 at exactly the minimal
-- version and cvc5 above it, with an additional output line)
#guard accepted (evalCandidateProbe z3Desc nativeZ3 (.ran 0 "Z3 version 4.15.2 - 64 bit\n"))
#guard accepted (evalCandidateProbe cvc5Desc nativeCvc5
  (.ran 0 "cvc5 version 1.3.4 [git tag 1.3.4]\nThis is cvc5.\n"))
-- An outdated solver is rejected, telling the user the minimal supported version
#guard rejectedMentioning z3Desc.minVersion
  (evalCandidateProbe z3Desc nativeZ3 (.ran 0 "Z3 version 4.8.10 - 64 bit\n"))
#guard rejectedMentioning cvc5Desc.minVersion
  (evalCandidateProbe cvc5Desc nativeCvc5 (.ran 0 "cvc5 version 1.0.8 [git abc]\n"))
-- Garbage stdout is rejected because no version can be parsed (fail closed)
#guard rejectedMentioning "parse"
  (evalCandidateProbe cvc5Desc nativeCvc5 (.ran 0 "Segmentation fault\n"))
-- A later dotted notice cannot rescue an unparseable first-line banner.
#guard rejectedMentioning "parse"
  (evalCandidateProbe cvc5Desc nativeCvc5
    (.ran 0 "unknown build\nlinked library 9.8.7\n"))

/-! # `ProbeOutcome.banner`: first-line extraction -/

-- Synthetic multiline cvc5 output: only the first line is treated as the banner
#guard ProbeOutcome.banner
    (.ran 0 "cvc5 version 1.3.4 [git tag 1.3.4]\nThis is cvc5.\nCopyright notice.\n")
  == "cvc5 version 1.3.4 [git tag 1.3.4]"
-- Windows-style line endings: the trailing `\r` is trimmed away
#guard ProbeOutcome.banner (.ran 0 "Z3 version 4.15.2 - 64 bit\r\n") == "Z3 version 4.15.2 - 64 bit"
-- A probe that never ran has no banner
#guard ProbeOutcome.banner (.failed "spawn failure") == ""

end Test.SolverVersion
