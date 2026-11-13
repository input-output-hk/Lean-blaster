#!/usr/bin/env python3
"""Run the existing BlasterBenchmarking corpus against this checkout.

Reuses the corpus's extraction functions. Mathlib is read from an existing Lean
4.24 project; neither its dependencies nor the benchmark corpus are modified.
Every success in strict mode must pass an independent printed-axiom audit.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def command(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def extract(corpus):
    # Same statement/context and first-theorem semantics as the corpus harness.
    script = r'''
source benchmarks/benchmark_config.sh
source benchmarks/benchmark_utils.sh
source benchmarks/benchmark_core.sh
for spec in "${BENCHMARK_FILES[@]}"; do
    IFS=: read -r imp path suite budget kind <<< "$spec"
    if [[ "$kind" == taskdir ]]; then
        for task in "$path"/*.lean; do
            printf '%s\0' "$suite" "$(basename "$task" .lean)" "$budget" "$task" "$(swap_proof "$task" __TACTIC__)"
        done
    else
        context=$(extract_context "$path")
        while IFS= read -r name; do
            statement=$(extract_theorem_info "$path" "$name") || exit 1
            printf '%s\0' "$suite" "$name" "$budget" "$path" "$context
theorem benchmark_proof $statement := by __TACTIC__"
        done < <(get_all_theorems "$path")
    fi
done
'''
    bash = "/opt/homebrew/bin/bash" if Path("/opt/homebrew/bin/bash").exists() else "bash"
    fields = subprocess.check_output([bash, "-c", script], cwd=corpus).decode().split("\0")
    assert fields.pop() == "" and len(fields) % 5 == 0
    cases = []
    for i in range(0, len(fields), 5):
        suite, name, budget, source, body = fields[i:i + 5]
        theorem = re.search(r"^\s*theorem\s+([^\s:({]+)", body, re.M)
        assert theorem and body.count("__TACTIC__") == 1
        original = (corpus / source).read_text()
        cases.append(dict(suite=suite, name=name, budget=int(budget), source=source,
                          theorem=theorem[1], body=body,
                          source_theorems=len(re.findall(r"^\s*theorem\s+", original, re.M))))
    return cases


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--corpus", type=Path, default=ROOT.parent / "blaster-benchmarking-reconstruction")
    p.add_argument("--mathlib-project", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--workers", type=int, default=3)
    p.add_argument("--limit", type=int, help="First N goals per suite (smoke test)")
    p.add_argument("--suites", help="Comma-separated suite allowlist")
    p.add_argument("--modes", default="trusted,strict")
    args = p.parse_args()
    corpus = args.corpus.resolve()
    project = (args.mathlib_project or corpus / "reconstruction/rebase-project").resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    cases = extract(corpus)
    if args.suites:
        suites = set(args.suites.split(","))
        assert suites <= {c["suite"] for c in cases}
        cases = [c for c in cases if c["suite"] in suites]
    if args.limit:
        counts = Counter()
        cases = [c for c in cases if (counts.update([c["suite"]]) or counts[c["suite"]] <= args.limit)]
    modes = args.modes.split(",")
    assert set(modes) <= {"trusted", "strict"} and args.workers > 0
    env = {k: v for k, v in os.environ.items() if not k.startswith("BLASTER_")}
    paths = command("lake", "env", "printenv", "LEAN_PATH", cwd=project).split(os.pathsep)
    paths = [str((project / path).resolve()) for path in paths if path]
    env.update(LEAN_NUM_THREADS="2", LEAN_PATH=os.pathsep.join([str(ROOT / ".lake/build/lib/lean"), *paths]))
    lean = command("elan", "which", "lean")
    native = next(p for p in (ROOT / ".lake/build/lib").glob("libBlaster.*") if p.suffix in (".dylib", ".so"))
    metadata = dict(head=command("git", "rev-parse", "HEAD"),
                    diff_sha256=hashlib.sha256(subprocess.check_output(["git", "diff", "HEAD"], cwd=ROOT)).hexdigest(),
                    corpus_head=command("git", "rev-parse", "HEAD", cwd=corpus),
                    z3=command("z3", "--version"), toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                    runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    native_sha256=hashlib.sha256(native.read_bytes()).hexdigest(),
                    modes=modes, cases=cases, workers=args.workers, threads_per_process=2,
                    memory_limit_mib=8192, environment_overrides="none", solver_seeds="backend default")
    manifest = out / "manifest.json"
    if manifest.exists():
        assert json.loads(manifest.read_text()) == metadata, "Use a new output directory for a changed configuration"
    else:
        manifest.write_text(json.dumps(metadata, indent=2) + "\n")
    resultfile = out / "results.jsonl"
    rows = [json.loads(s) for s in resultfile.read_text().splitlines()] if resultfile.exists() else []
    done = {(r["suite"], r["name"], r["mode"]) for r in rows}

    def run(case, mode):
        directory = out / "attempts" / case["suite"] / case["name"] / mode
        directory.mkdir(parents=True, exist_ok=True)
        replay = directory / "replay.jsonl"
        replay.unlink(missing_ok=True)
        local_env = dict(env, BLASTER_SMTPROOF_LOG=str(replay))
        tactic = "blaster (gen-proof: 1)" if mode == "strict" else "blaster (reconstruct: 0)"
        source = "import Blaster\n" + case["body"].replace("__TACTIC__", tactic)
        source += f'\n#print axioms {case["theorem"]}\n'
        leanfile = directory / "Attempt.lean"
        leanfile.write_text(source)
        start = time.monotonic()
        timed_out = False
        with (directory / "lean.log").open("w") as log:
            proc = subprocess.Popen([lean, "--threads=2", "--memory=8192", f"--load-dynlib={native}", str(leanfile)],
                                    cwd=ROOT, env=local_env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                proc.wait(timeout=case["budget"])
            except subprocess.TimeoutExpired:
                timed_out = True
            finally:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        text = (directory / "lean.log").read_text(errors="replace")
        status = "timeout" if timed_out else "passed" if proc.returncode == 0 else "crashed" if proc.returncode < 0 else "failed"
        match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", text)
        axioms = [x.strip() for x in match[1].split(",") if x.strip()] if match else []
        audited = match is not None or "does not depend on any axioms" in text
        if status == "passed" and (not audited or (mode == "strict" and set(axioms) - STANDARD)):
            status = "axiom-failure"
        events = []
        if replay.exists():
            for line in replay.read_text().splitlines():
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError:
                    pass
        errors = re.findall(r"^.*?:\d+:\d+: error: (.*)$", text, re.M)
        return dict(suite=case["suite"], name=case["name"], mode=mode, status=status,
                    elapsed_ms=round((time.monotonic() - start) * 1000), budget_s=case["budget"],
                    axioms=axioms, source_theorems=case["source_theorems"], errors=errors,
                    replay_calls=len([e for e in events if e.get("kind") == "residual"]),
                    log=str((directory / "lean.log").relative_to(out)))

    jobs = [(c, m) for c in cases for m in modes if (c["suite"], c["name"], m) not in done]
    print(f"{len(cases)} goals, {len(jobs)} attempts remaining", flush=True)
    with resultfile.open("a", buffering=1) as stream, ThreadPoolExecutor(max_workers=args.workers) as pool:
        for future in as_completed([pool.submit(run, c, m) for c, m in jobs]):
            row = future.result()
            rows.append(row)
            stream.write(json.dumps(row) + "\n")
            if len(rows) % 25 == 0 or row["status"] == "crashed":
                print(f'{len(rows)}: {row["suite"]}/{row["name"]} {row["mode"]} {row["status"]}', flush=True)
    summary = {mode: dict(Counter(r["status"] for r in rows if r["mode"] == mode)) for mode in modes}
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
