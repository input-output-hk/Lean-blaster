#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Offline, serial finite-field measurements. Never stages or downloads tools.

Linux wait4 reports maximum individual-process RSS including reaped children;
process-tree RSS is sampled separately, not presented as an exact peak. A durable
running record makes worker interruption an incomplete/failed run, not a skip.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import selectors
import shutil
import signal
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PROBE = ["python3", "scripts/finite_fields/probe_solver.py", "--manifest",
         "docs/finite-fields/solver-manifest.json", "--artifact-root",
         ".artifacts/finite-fields", "--profile", "solving", "--offline", "--check"]
UNAVAILABLE = {s: {"status": "not_available", "seconds": None,
                  "reason": "Production M2 stage does not exist at M1"}
               for s in ("proof_reading", "proof_checking", "verified_transport")}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def save(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True, allow_nan=False) + "\n")
    temporary.replace(path)


def hardware():
    def text(path):
        try:
            return Path(path).read_text().strip()
        except OSError:
            return None
    return {"uname": list(platform.uname()), "cpu_count": os.cpu_count(),
            "cpuinfo": text("/proc/cpuinfo"), "meminfo": text("/proc/meminfo"),
            "cgroup_memory_max_bytes": text("/sys/fs/cgroup/memory.max"),
            "cgroup_cpu_max": text("/sys/fs/cgroup/cpu.max"),
            "python": sys.version, "platform": platform.platform()}


def hardware_identity(observed):
    """Pin exposed CPU/platform/quota, not volatile host name or free memory."""
    identifiers = ("CPU implementer", "CPU part", "CPU architecture", "CPU variant", "model name")
    return {"system": observed["uname"][0], "kernel": observed["uname"][2],
            "machine": observed["uname"][4], "exposed_cpu_count": observed["cpu_count"],
            "cpu_quota": observed["cgroup_cpu_max"],
            "memory_ceiling": observed["cgroup_memory_max_bytes"],
            "cpu_identifiers": sorted({line for line in observed["cpuinfo"].splitlines()
                                       if any(key in line for key in identifiers)})}


def validate_config(config):
    if config["schema_version"] != 1 or config["concurrency"] != 1:
        raise ValueError("Only schema 1 and serial measurements are supported")
    if config["warmups"] < 1 or config["repetitions"] < 3:
        raise ValueError("At least one warmup and three measured repetitions required")
    if config["probe_argv"] != PROBE:
        raise ValueError("Parent offline probe interface must remain unchanged")
    for path, expected in config["input_pins"].items():
        if digest(ROOT / path) != expected:
            raise ValueError(f"Input hash mismatch: {path}")
    corpus = load(ROOT / config["corpus_path"])
    if digest(ROOT / config["corpus_path"]) != config["corpus_sha256"]:
        raise ValueError("Corpus identity mismatch")
    for path, expected in corpus["input_pins"].items():
        if config["input_pins"].get(path) != expected:
            raise ValueError(f"Missing parent input pin: {path}")
    runnable = {e["id"]: e for e in corpus["entries"] if e["status"] == "runnable"}
    if set(config["required_corpus_ids"]) != set(runnable):
        raise ValueError("Every parent runnable entry is required")
    if config["catalogue"] != [e for e in corpus["entries"] if e["status"] != "runnable"]:
        raise ValueError("Catalogue limitations must match the parent exactly")
    cases = config["cases"]
    if len({c["id"] for c in cases}) != len(cases):
        raise ValueError("Duplicate case id")
    covered = set()
    for case in cases:
        limits = case["limits"]
        if not (0 < limits["wall_seconds"] <= 120 and
                0 < limits["memory_mib"] <= 4096 and
                0 < limits["tree_memory_mib"] <= 3072 and
                0 < limits["cpu_seconds"] <= 120 and
                0 < limits["output_bytes"] <= 1048576):
            raise ValueError(f"Unsafe resource ceiling: {case['id']}")
        if not case["input_files"] or any(p not in config["input_pins"] for p in case["input_files"]):
            raise ValueError(f"Unpinned case inputs: {case['id']}")
        known_ids = {entry["id"] for entry in corpus["entries"]}
        if any(i not in known_ids for i in case["corpus_ids"]):
            raise ValueError("Unknown corpus provenance")
        for output in case.get("output_files", []):
            target = (ROOT / output).resolve()
            if target.suffix != ".olean" or not target.is_relative_to(ROOT / "benchmarks/finite-fields"):
                raise ValueError("Only benchmark .olean outputs may be replaced")
        if case["category"] == "parent-corpus":
            for entry_id in case["corpus_ids"]:
                entry = runnable[entry_id]
                original = entry["invocation"]
                if case["argv"] != original["argv"] or case["cwd"] != original["cwd"]:
                    raise ValueError("Parent corpus invocation was changed")
                if case["expected"] != entry["expected"]:
                    raise ValueError("Parent expected result was changed")
                covered.add(entry_id)
    if covered != set(runnable):
        raise ValueError("Missing required parent invocation")
    for descriptor in config["case_descriptors"]:
        declared = load(ROOT / descriptor)
        for item in declared:
            matches = [c for c in cases if c["id"] == item["id"]]
            if len(matches) != 1:
                raise ValueError(f"Missing harness case: {item['id']}")
            for key, value in item.items():
                if key != "limits" and matches[0].get(key) != value:
                    raise ValueError(f"Harness descriptor mismatch: {item['id']}/{key}")
            for key, value in item["limits"].items():
                if matches[0]["limits"].get(key) != value:
                    raise ValueError(f"Harness limit mismatch: {item['id']}/{key}")
    for path, expected in config["tool_pins"].items():
        if digest(path) != expected:
            raise ValueError(f"Tool identity mismatch: {path}")
    for name, expected_path in config["resolved_tools"].items():
        actual = shutil.which(name, path=config["environment"]["PATH"])
        if actual is None or str(Path(actual).resolve()) != expected_path:
            raise ValueError(f"Executable resolution mismatch: {name}")
    if platform.machine() != config["setup"]["machine"] or platform.system() != config["setup"]["system"]:
        raise ValueError("Hardware architecture/OS mismatch; create a new exact configuration")
    if Path("/sys/fs/cgroup/memory.max").read_text().strip() != config["setup"]["worker_memory_bytes"]:
        raise ValueError("Worker memory ceiling differs from configured setup")
    if hardware_identity(hardware()) != config["hardware_identity"]:
        raise ValueError("Exposed hardware/kernel/quota differs; record a new configuration")
    return corpus


def environment(config):
    # Start from a recorded allowlist, not ambient solver settings or Lean options.
    return dict(config["environment"])


def tree_rss(group):
    total = 0
    for directory in Path("/proc").iterdir():
        if not directory.name.isdigit():
            continue
        try:
            fields = (directory / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == group:
                total += int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
        except (OSError, ValueError, IndexError):
            pass  # A process may exit between directory enumeration and stat.
    return total


def observe(argv, cwd, env, limits):
    """Bound a process group; preserve diagnostics and wait4 usage without time(1)."""
    streams = {}
    pipes = [os.pipe(), os.pipe()]
    start_ns = time.monotonic_ns()
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            resource.setrlimit(resource.RLIMIT_AS, (limits["memory_mib"] * 1048576,) * 2)
            resource.setrlimit(resource.RLIMIT_CPU, (limits["cpu_seconds"], limits["cpu_seconds"] + 1))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            resource.setrlimit(resource.RLIMIT_FSIZE, (64 * 1048576,) * 2)
            for destination, (reader, writer) in enumerate(pipes, 1):
                os.close(reader)
                os.dup2(writer, destination)
                os.close(writer)
            os.chdir(cwd)
            os.execvpe(argv[0], argv, env)
        except BaseException as error:
            os.write(2, ("FFM20_EXEC_ERROR " + repr(error)).encode())
            os._exit(125)
    selector = selectors.DefaultSelector()
    for name, (reader, writer) in zip(("stdout", "stderr"), pipes):
        os.close(writer)
        os.set_blocking(reader, False)
        selector.register(reader, selectors.EVENT_READ, name)
        streams[name] = bytearray()
    reason = None
    usage = None
    exit_code = None
    peak_tree = 0
    output_bytes = 0
    while selector.get_map() or usage is None:
        elapsed = (time.monotonic_ns() - start_ns) / 1e9
        peak_tree = max(peak_tree, tree_rss(pid))
        if reason is None:
            if elapsed > limits["wall_seconds"]:
                reason = "wall_limit"
            elif peak_tree > limits["tree_memory_mib"] * 1048576:
                reason = "tree_memory_limit"
            elif output_bytes > limits["output_bytes"]:
                reason = "output_limit"
            if reason:
                try:
                    os.killpg(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        for key, _ in selector.select(0.01):
            chunk = os.read(key.fd, 65536)
            if not chunk:
                selector.unregister(key.fd)
                os.close(key.fd)
                continue
            output_bytes += len(chunk)
            remaining = limits["output_bytes"] - len(streams[key.data])
            streams[key.data].extend(chunk[:max(0, remaining)])
        if usage is None:
            reaped, status, observed_usage = os.wait4(pid, os.WNOHANG)
            if reaped:
                usage = observed_usage
                exit_code = os.waitstatus_to_exitcode(status)
    selector.close()
    return {"argv": argv, "cwd": cwd, "limits": limits,
            "elapsed_seconds": (time.monotonic_ns() - start_ns) / 1e9,
            "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
            "wait4_maxrss_kib": usage.ru_maxrss, "sampled_peak_tree_rss_bytes": peak_tree,
            "exit_code": exit_code, "termination_reason": reason,
            "output_bytes": output_bytes,
            **{name: value.decode("utf-8", errors="replace") for name, value in streams.items()}}


def classify(case, run):
    if "FFM20_EXEC_ERROR" in run["stderr"]:
        return "invalid_setup"
    if run["termination_reason"]:
        return run["termination_reason"]
    combined = run["stdout"] + run["stderr"]
    if any(marker in combined for marker in (
            "unknown module prefix", "does not exist", "object file", "FFM20_EXEC_ERROR")):
        if run["exit_code"] != 0:
            return "invalid_setup"
    if run["exit_code"] < 0:
        return "signal_failure"
    if run["exit_code"] != 0:
        if "heartbeats" in combined or "maximum number of heartbeats" in combined:
            return "heartbeat_limit"
        if any(s in combined.lower() for s in ("out of memory", "failed to allocate", "bad_alloc")):
            return "memory_limit"
        return "command_failure"
    expected = case["expected"]
    if any(run.get(k) != value for k, value in expected.items()):
        return "unexpected_result"
    if any(marker not in combined for marker in case.get("required_markers", [])):
        return "unexpected_result"
    if any(marker in combined for marker in case.get("forbidden_markers", [])):
        return "unexpected_result"
    return "success"


def metrics(run):
    found = []
    for line in (run["stdout"] + "\n" + run["stderr"]).splitlines():
        if line.startswith("FFM20_METRIC "):
            found.append(json.loads(line.removeprefix("FFM20_METRIC ")))
    return found


def stage_measurements(run):
    stages = {
        "whole_file_or_process": {"status": "measured", "seconds": run["elapsed_seconds"]},
        "elaboration": {"status": "not_separately_measured", "seconds": None,
                        "reason": "Profiler diagnostics retained raw; not an exclusive elaboration timer."},
        "kernel": {"status": "not_separately_measured", "seconds": None,
                   "reason": "No exclusive kernel timer in this whole-file invocation."}}
    # Lean's profiler option documents exclusive component times. Kernel work
    # here is the `type checking` component for new declarations in this file,
    # not rechecking imports or an isolated theorem's entire proof cost.
    cumulative = (run["stdout"] + "\n" + run["stderr"]).split("cumulative profiling times:\n")
    if len(cumulative) == 2:
        components = {}
        for label, value, unit in re.findall(
                r"^\t(.+?) ([0-9.eE+-]+)(ms|s|us|ns)$", cumulative[1], re.MULTILINE):
            components[label] = float(value) * {"s": 1, "ms": 0.001, "us": 1e-6, "ns": 1e-9}[unit]
        for label, stage in (("elaboration", "elaboration"), ("type checking", "kernel"),
                             ("tactic execution", "tactic_execution"), ("import", "imports")):
            if label in components:
                stages[stage] = {"status": "measured", "seconds": components[label],
                                 "source": f"Lean cumulative exclusive profiler: {label}",
                                 "scope": "whole-file component; not isolated theorem time"}
    labels = {"Optimization": "optimization", "Translation": "translation",
              "Submitting Smt Query": "submission", "Solve": "solve_with_model_extraction"}
    for label, stage in labels.items():
        matches = re.findall(r"^\[End\]: " + re.escape(label) + r" \(([0-9.eE+-]+)s\)$",
                             run["stdout"], re.MULTILINE)
        stages[stage] = ({"status": "measured", "seconds": float(matches[0]),
                          "resolution_seconds": 0.001, "source": "production profileTask"}
                         if len(matches) == 1 else
                         {"status": "not_available", "seconds": None,
                          "reason": "No unique completed production stage trace in this run."})
    for stage in ("value_display", "solver_only", "preflight"):
        stages[stage] = {"status": "not_separately_measured", "seconds": None,
                         "reason": "No exclusive production timer; included in enclosing wall time."}
    return stages


def summaries(runs):
    result = {}
    for case_id in sorted({r["case_id"] for r in runs}):
        selected = [r for r in runs if r["case_id"] == case_id and r["phase"] == "measured"]
        counts = {}
        for row in selected:
            counts[row["status"]] = counts.get(row["status"], 0) + 1
        successful = [r["elapsed_seconds"] for r in selected if r["status"] == "success"]
        all_times = [r["elapsed_seconds"] for r in selected]
        result[case_id] = {"status_counts": counts, "measured_runs": len(selected),
                           "all_elapsed_seconds": distribution(all_times),
                           "success_elapsed_seconds": distribution(successful)}
    return result


def distribution(values):
    if not values:
        return None
    return {"count": len(values), "min": min(values), "max": max(values),
            "median": statistics.median(values), "mean": statistics.mean(values),
            "sample_stdev": statistics.stdev(values) if len(values) > 1 else None}


def execute(config_path, output_path):
    config = load(config_path)
    result = {"schema_version": 1, "config_sha256": digest(config_path),
              "corpus_sha256": config["corpus_sha256"], "status": "invalid_setup",
              "hardware": hardware(), "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "environment": environment(config), "production_m2_stages": UNAVAILABLE,
              "units": config["units"], "runs": [], "setup_observations": []}
    save(output_path, result)
    try:
        validate_config(config)
        env = environment(config)
        for command in [PROBE, *config["setup_commands"]]:
            observation = observe(command, str(ROOT), env, config["setup_limits"])
            result["setup_observations"].append(observation)
            save(output_path, result)
            if observation["exit_code"] != 0 or observation["termination_reason"]:
                raise ValueError(f"Setup command failed: {command}")
        result["status"] = "running"
        for phase, count in (("warmup", config["warmups"]), ("measured", config["repetitions"])):
            # Repeat-major ordering interleaves methods and reduces drift bias.
            for repetition in range(count):
                for case in config["cases"]:
                    row = {"case_id": case["id"], "phase": phase, "repetition": repetition,
                           "status": "running"}
                    result["runs"].append(row)
                    save(output_path, result)
                    for output in case.get("output_files", []):
                        (ROOT / output).unlink(missing_ok=True)
                    observed = observe(case["argv"], str(ROOT / case["cwd"]), env, case["limits"])
                    row.update(observed)
                    row["status"] = classify(case, row)
                    row["metrics"] = metrics(row)
                    row["stages"] = stage_measurements(row)
                    row["compiled_artifacts"] = {
                        path: {"bytes": (ROOT / path).stat().st_size, "sha256": digest(ROOT / path)}
                        for path in case.get("output_files", []) if (ROOT / path).is_file()}
                    row["compiled_artifact_bytes"] = (
                        sum(a["bytes"] for a in row["compiled_artifacts"].values())
                        if row["compiled_artifacts"] else None)
                    save(output_path, result)
                    print(f"{phase} {repetition} {case['id']}: {row['status']} {row['elapsed_seconds']:.6f}s", flush=True)
                    if row["status"] == "invalid_setup":
                        raise ValueError("Executable launch failed during measurement")
        result["summaries"] = summaries(result["runs"])
        result["status"] = "complete"
        result["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        save(output_path, result)
        return 0
    except (OSError, ValueError, KeyError) as error:
        result["status"] = "invalid_setup"
        result["setup_error"] = str(error)
        save(output_path, result)
        print(f"Invalid benchmark setup: {error}", file=sys.stderr)
        return 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    return execute(Path(args.config).resolve(), Path(args.output).resolve())


if __name__ == "__main__":
    sys.exit(main())
