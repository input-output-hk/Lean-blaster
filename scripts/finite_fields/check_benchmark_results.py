#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Validate complete FFM-20 observations, not a cryptographic attestation of execution.

Recomputes outcomes, coverage, trace metrics and summaries. Missing setup, a
worker-killed partial journal, fabricated zero-duration success and omitted
required cases are errors. Measured bounded failures remain valid observations.
"""
import argparse
import copy
import json
import math
from pathlib import Path
import sys

import benchmark as bench


def require(condition, message):
    if not condition:
        raise ValueError(message)


def finite(value, positive=False):
    return (type(value) in (int, float) and math.isfinite(value)
            and (value > 0 if positive else value >= 0))


def check(config, results, config_hash, verify_inputs=True):
    if verify_inputs:
        bench.validate_config(config)
    require(results["schema_version"] == 1 and results["status"] == "complete",
            "Incomplete, interrupted or invalid-setup measurement")
    require(results["config_sha256"] == config_hash, "Config identity mismatch")
    require(results["corpus_sha256"] == config["corpus_sha256"], "Corpus identity mismatch")
    require(results["environment"] == bench.environment(config), "Environment mismatch")
    require(results["units"] == config["units"], "Units mismatch")
    require(results["production_m2_stages"] == bench.UNAVAILABLE, "M2 stages must be unavailable")
    require(results["hardware"]["cgroup_memory_max_bytes"] == config["setup"]["worker_memory_bytes"],
            "Unrecorded worker memory limit")
    require(results["hardware"]["uname"][0] == config["setup"]["system"] and
            results["hardware"]["uname"][4] == config["setup"]["machine"], "Recorded platform mismatch")
    require(results["hardware"]["cpuinfo"] and results["hardware"]["meminfo"], "Missing hardware metadata")
    require(bench.hardware_identity(results["hardware"]) == config["hardware_identity"],
            "Recorded CPU/kernel/quota mismatch")
    commands = [bench.PROBE, *config["setup_commands"]]
    observations = results["setup_observations"]
    require(len(observations) == len(commands), "Missing required setup observations")
    for command, observed in zip(commands, observations):
        require(observed["argv"] == command and observed["exit_code"] == 0 and
                observed["termination_reason"] is None and finite(observed["elapsed_seconds"], True),
                "Invalid setup observation")
        require(observed["limits"] == config["setup_limits"], "Setup resource mismatch")
    probe = json.loads(observations[0]["stdout"])
    require(probe["passed"] is True and not probe["failures"], "Offline parent probe did not pass")
    require(all(probe["capabilities"][key]["passed"] is True for key in ("setup", "solving", "model")),
            "Required staged solver capabilities missing")
    cases = {c["id"]: c for c in config["cases"]}
    expected = {(case, phase, repetition) for case in cases
                for phase, count in (("warmup", config["warmups"]), ("measured", config["repetitions"]))
                for repetition in range(count)}
    seen = set()
    successful_categories = set()
    for row in results["runs"]:
        key = (row["case_id"], row["phase"], row["repetition"])
        require(key in expected and key not in seen, f"Unexpected/duplicate run {key}")
        seen.add(key)
        case = cases[row["case_id"]]
        require(row["argv"] == case["argv"] and row["cwd"] == str(bench.ROOT / case["cwd"]),
                f"Invocation mismatch {key}")
        require(row["limits"] == case["limits"], f"Resource ceiling mismatch {key}")
        require(finite(row["elapsed_seconds"], True), f"Zero/invalid elapsed time {key}")
        require(type(row["exit_code"]) is int, f"Missing process exit {key}")
        for metric in ("user_seconds", "system_seconds", "wait4_maxrss_kib", "sampled_peak_tree_rss_bytes"):
            require(finite(row[metric]), f"Invalid resource observation {key}/{metric}")
        require(row["wait4_maxrss_kib"] > 0, f"Missing peak memory {key}")
        require(row["termination_reason"] in (None, "wall_limit", "tree_memory_limit", "output_limit"),
                f"Unknown termination reason {key}")
        if row["termination_reason"] == "wall_limit":
            require(row["elapsed_seconds"] >= case["limits"]["wall_seconds"], "Unreached wall limit")
        if row["termination_reason"] == "tree_memory_limit":
            require(row["sampled_peak_tree_rss_bytes"] > case["limits"]["tree_memory_mib"] * 1048576,
                    "Unreached tree memory limit")
        if row["termination_reason"] == "output_limit":
            require(row["output_bytes"] > case["limits"]["output_bytes"], "Unreached output limit")
        require(row["status"] == bench.classify(case, row), f"Status inconsistent with evidence {key}")
        require(row["status"] != "invalid_setup", f"Missing setup is not a benchmark failure {key}")
        require(row["metrics"] == bench.metrics(row), f"Metrics differ from raw log {key}")
        for metric in row["metrics"]:
            if "proof_expr_nodes" in metric and metric["proof_expr_nodes"] is not None:
                require(type(metric["proof_expr_nodes"]) is int and metric["proof_expr_nodes"] > 0,
                        "Invalid proof-expression node metric")
                require(set(metric["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"},
                        "Proof metric has an unapproved axiom")
        require(row["stages"] == bench.stage_measurements(row), f"Stage measurements differ from logs {key}")
        artifacts = row["compiled_artifacts"]
        require(set(artifacts) <= set(case.get("output_files", [])), "Unexpected compiled artifact")
        for artifact in artifacts.values():
            require(type(artifact["bytes"]) is int and artifact["bytes"] > 0 and
                    len(artifact["sha256"]) == 64, "Invalid compiled artifact observation")
        total = sum(a["bytes"] for a in artifacts.values()) if artifacts else None
        require(row["compiled_artifact_bytes"] == total, "Compiled artifact byte total mismatch")
        if row["status"] == "success":
            require(set(artifacts) == set(case.get("output_files", [])), "Missing successful compiled output")
        if row["phase"] == "measured" and row["status"] == "success":
            successful_categories.add(case["category"])
    require(seen == expected, f"Missing required case/run coverage: {sorted(expected - seen)}")
    require({c["category"] for c in cases.values()} <= successful_categories,
            "A whole measurement category performed no successful work")
    require(results["summaries"] == bench.summaries(results["runs"]), "Summary calculation mismatch")
    return len(seen)


def self_test(config, results, config_hash):
    """Mutation checks target plausible corruptions of consumer-visible evidence."""
    mutations = []
    def add(name, change):
        data = copy.deepcopy(results)
        change(data)
        mutations.append((name, data))
    add("missing measured case", lambda r: r["runs"].pop())
    add("duplicate observation", lambda r: r["runs"].append(copy.deepcopy(r["runs"][0])))
    add("zero-duration success", lambda r: next(x for x in r["runs"] if x["status"] == "success").update(elapsed_seconds=0))
    add("nonfinite duration", lambda r: r["runs"][0].update(elapsed_seconds=float("nan")))
    add("invented success", lambda r: next(x for x in r["runs"] if x["status"] != "success").update(status="success"))
    add("changed config", lambda r: r.update(config_sha256="0" * 64))
    add("changed corpus", lambda r: r.update(corpus_sha256="0" * 64))
    add("missing staged probe", lambda r: r["setup_observations"].pop(0))
    add("worker interruption", lambda r: r.update(status="running"))
    add("fabricated summary", lambda r: next(iter(r["summaries"].values())).update(measured_runs=999))
    add("false reconstructed proof", lambda r: r["production_m2_stages"]["verified_transport"].update(status="measured", seconds=0.1))
    add("changed resource limit", lambda r: r["runs"][0]["limits"].update(wall_seconds=999))
    for name, mutated in mutations:
        try:
            check(config, mutated, config_hash, verify_inputs=False)
        except (ValueError, KeyError, TypeError):
            print(f"PASS rejection: {name}")
        else:
            raise ValueError(f"Checker accepted mutation: {name}")
    config_mutations = []
    missing_class = copy.deepcopy(config)
    missing_class["required_corpus_ids"].remove("curve25519-circuit")
    config_mutations.append(("missing required circuit class", missing_class))
    missing_input = copy.deepcopy(config)
    del missing_input["input_pins"]["fixtures/finite-fields/audit/Circuits.lean"]
    config_mutations.append(("missing required source pin", missing_input))
    missing_tool = copy.deepcopy(config)
    missing_tool["tool_pins"][str(bench.ROOT / ".artifacts/finite-fields/absent-required-tool")] = "0" * 64
    config_mutations.append(("missing required tool artifact", missing_tool))
    for name, mutated in config_mutations:
        try:
            bench.validate_config(mutated)
        except (OSError, ValueError, KeyError, TypeError):
            print(f"PASS rejection: {name}")
        else:
            raise ValueError(f"Checker accepted configuration mutation: {name}")
    return len(mutations) + len(config_mutations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    parser.add_argument("--results", required=True)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        config, results = bench.load(args.config), bench.load(args.results)
        config_hash = bench.digest(args.config)
        count = check(config, results, config_hash)
        print(f"PASS: {len(config['cases'])} cases, {count} runs; identities, offline setup, statuses, coverage and summaries agree")
        if args.self_test:
            print(f"PASS: {self_test(config, results, config_hash)} evidence-corruption rejection scenarios")
        return 0
    except (OSError, ValueError, KeyError, TypeError, StopIteration) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
