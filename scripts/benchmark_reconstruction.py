#!/usr/bin/env python3
"""Fresh-process, bounded benchmarks of the actual strict Blaster tactic.

Run `lake build Blaster:shared` first. JSON contains raw repetitions, source revision,
working-tree hash, environment, kernel-accepted proof sizes and replay methods.
The process RSS includes Lean startup and the optional size-measurement traversal.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--limit", type=int, default=120)
    parser.add_argument("--solver-timeout", type=int, default=10)
    parser.add_argument("--backends", default="auto", help="auto or an explicit comma-separated portfolio")
    parser.add_argument("--execution", choices=["native", "interpreted"], default="native")
    parser.add_argument("--certificates", action="store_true", help="enable the experimental encoding contract and Farkas checker")
    parser.add_argument("--cases", nargs="*")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    cases = json.loads((ROOT / "scripts/reconstruction-cases.json").read_text())
    if args.cases:
        unknown = set(args.cases) - {c["name"] for c in cases}
        if unknown:
            parser.error(f"unknown cases: {sorted(unknown)}")
        cases = [c for c in cases if c["name"] in args.cases]
    template = (ROOT / "scripts/ReconstructionBench.lean").read_text()
    env = os.environ.copy()
    for key in list(env):
        if key.startswith("BLASTER_"):
            del env[key]
    env.update(BLASTER_SMTPROOF_SEEDS="1", LEAN_NUM_THREADS="2", BLASTER_SMTPROOF_DEADLINE=str(args.limit))
    if args.backends != "auto":
        env["BLASTER_SMTPROOF_BACKENDS"] = args.backends
    if args.certificates:
        env["BLASTER_SMTPROOF_CERTIFICATES"] = "1"
    native = None
    if args.execution == "native":
        native = next(p for p in (ROOT / ".lake/build/lib").glob("libBlaster.*") if p.suffix in (".dylib", ".so"))
    metadata = dict(head=git("rev-parse", "HEAD").decode().strip(),
                    diff_sha256=hashlib.sha256(git("diff", "HEAD")).hexdigest(),
                    harness_sha256=hashlib.sha256(template.encode()).hexdigest(), cases=cases,
                    platform=platform.platform(), cpus=os.cpu_count(), load_average=os.getloadavg(),
                    solver_timeout_s=args.solver_timeout, execution=args.execution,
                    z3=subprocess.check_output(["z3", "--version"], cwd=ROOT, text=True).strip(),
                    toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                    native_sha256=hashlib.sha256(native.read_bytes()).hexdigest() if native else None,
                    process_limit_s=args.limit,
                    environment={k: v for k, v in env.items() if k.startswith(("BLASTER_", "LEAN_"))})
    (args.out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    results = []
    for case in cases:
        for repetition in range(1, args.repeat + 1):
            stem = f'{case["name"]}-{repetition}'
            metrics = (args.out / f"{stem}.json").resolve()
            replay = (args.out / f"{stem}.jsonl").resolve()
            replay.unlink(missing_ok=True)
            log = args.out / f"{stem}.log"
            source = template.replace("-- BENCHMARK_THEOREM",
                f'#reconstruction_bench ({case["goal"]})').replace("BENCHMARK_TIMEOUT", str(args.solver_timeout))
            source = source.replace("-- BENCHMARK_DEFINITIONS", case.get("definitions", ""))
            with tempfile.TemporaryDirectory(prefix="blaster-bench-") as directory:
                lean = Path(directory) / "Benchmark.lean"
                lean.write_text(source)
                olean = Path(directory) / "Benchmark.olean"
                env.update(BLASTER_BENCH_OUTPUT=str(metrics), BLASTER_SMTPROOF_LOG=str(replay))
                time_args = ["/usr/bin/time", "-l" if platform.system() == "Darwin" else "-v"]
                cmd = time_args + ["lake", "env", "lean", f"--root={directory}", "-o", str(olean), str(lean)]
                if native is not None:
                    cmd.insert(len(time_args) + 3, f"--load-dynlib={native}")
                start = time.monotonic()
                load_average = os.getloadavg()
                with log.open("w") as output:
                    proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=output,
                                            stderr=subprocess.STDOUT, start_new_session=True)
                    timed_out = False
                    try:
                        proc.wait(timeout=args.limit)
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        os.killpg(proc.pid, signal.SIGTERM)
                        try:
                            proc.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL)
                            proc.wait()
                text = log.read_text(errors="replace")
                status = "timeout" if timed_out else "passed" if proc.returncode == 0 else "failed"
                row = dict(case=case["name"], repetition=repetition, status=status,
                           wall_s=round(time.monotonic() - start, 3), returncode=proc.returncode,
                           load_average=load_average)
                if olean.exists():
                    row["olean_bytes"] = olean.stat().st_size
                match = re.search(r"(\d+)\s+maximum resident set size", text)
                if match:
                    row["peak_rss_bytes"] = int(match[1])
                match = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
                if match:
                    row["peak_rss_bytes"] = int(match[1]) * 1024
                if status == "passed":
                    row.update(json.loads(metrics.read_text()))
                else:
                    row["diagnostic"] = "\n".join(text.splitlines()[:8])[:2000]
                events = [json.loads(line) for line in replay.read_text().splitlines()] if replay.exists() else []
                residuals = [e for e in events if e.get("kind") == "residual"]
                row["replay_calls"] = len(residuals)
                row["z3_steps"] = sum(e["steps"] for e in residuals)
                row["replay_ms"] = sum(e.get("elapsed_ms", 0) for e in residuals)
                row["replay_check_ms"] = sum(e.get("check_ms", 0) for e in residuals)
                row["replay"] = residuals
            results.append(row)
            (args.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f'{stem}: {status}, {row["wall_s"]}s, {row.get("expanded_dag_nodes", "?")} nodes, '
                  f'{row["replay_calls"]} replay calls', flush=True)


if __name__ == "__main__":
    main()
