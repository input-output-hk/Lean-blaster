#!/usr/bin/env python3
"""Build the pinned control and two-patch cvc5 pair; never substitute a release."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys


REPOSITORY = "https://github.com/RSoulatIOHK/cvc5.git"
BASE = "67954d09dcc955eba282155766cf452fc0ff1bd6"
HEADS = [
    "6eaca4bf1303a69c2c3aaddc0e50b1bf7d3df6e7",
    "18ed35b885c1655520e2ffe9d1c143017ce907d9",
]
PATCH_HASHES = [
    "66a4ccff45cba6879d7bebbe15e29fd0bd6e0b0c84ca9002a9828edf730193c0",
    "3a6b010f9efa839aaa1b79797f3a81995c3a363be493e75949d72787b9c19dc2",
]
PATCHED_TREE = "05793707126cfbc003fc613d3ff335dc9b103740"
CONFIGURE = [
    "./configure.sh", "unrestricted", "--name=build-parity", "--ninja",
    "--auto-download", "--assertions", "--no-mpfr", "--static", "-DBUILD_GMP=1",
]
DEPENDENCIES = ("GMP", "CaDiCaL", "Poly", "SymFPU")
PYPARSING = "pyparsing==3.3.3 --hash=sha256:ece8c00a69cf01b45d0b1dedabb469c90d8caf996d4fda40f147627a122849a4"


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class Commands:
    def __init__(self, output, environment):
        self.output = output
        self.environment = environment
        self.count = 0
        (output / "logs").mkdir()

    def run(self, args, cwd=None, extra_env=None):
        self.count += 1
        log = self.output / "logs" / f"{self.count:03d}.log"
        command = shlex.join(str(arg) for arg in args)
        print(f"[{cwd or Path.cwd()}] {command}\n  log: {log}", flush=True)
        with (self.output / "commands.log").open("a") as commands:
            commands.write(f"{log.name}: [{cwd or Path.cwd()}] {command}\n")
        with log.open("wb") as stream:
            result = subprocess.run(
                args, cwd=cwd, env={**self.environment, **(extra_env or {})},
                stdout=stream, stderr=subprocess.STDOUT, check=False,
            )
        require(result.returncode == 0,
                f"Command exited {result.returncode}: {command}; see {log}")
        return log.read_text()

    def git(self, directory, *args, extra_env=None):
        return self.run(["git", "-C", str(directory), *args], extra_env=extra_env).strip()


def build_pair(args, output, provenance):
    environment = dict(os.environ)
    # Do not let global Git diff/attribute settings change the pinned patch bytes.
    environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                       LC_ALL="C", TZ="UTC")
    for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_EXTERNAL_DIFF",
                "PYTHONPATH", "PYTHONHOME"):
        environment.pop(key, None)
    commands = Commands(output, environment)
    tools = {}
    for name, executable in {
        "cc": environment.get("CC", "cc"),
        "cxx": environment.get("CXX", "c++"),
        "cmake": "cmake", "ninja": "ninja", "python": sys.executable,
        "git": "git", "make": "make",
    }.items():
        path = shutil.which(executable)
        require(path is not None, f"Missing required tool: {executable}")
        tools[name] = {"path": str(Path(path).absolute()),
                       "version": commands.run([path, "--version"])}
    # Preserve driver names: resolving clang++ symlinks can change link behavior.
    environment["CC"] = tools["cc"]["path"]
    environment["CXX"] = tools["cxx"]["path"]
    provenance["toolchain"] = {
        "platform": platform.platform(), "machine": platform.machine(), "tools": tools,
        "environment": {key: environment[key] for key in (
            "CC", "CXX", "CFLAGS", "CXXFLAGS", "CPPFLAGS", "LDFLAGS", "SDKROOT",
            "MACOSX_DEPLOYMENT_TARGET", "CMAKE_PREFIX_PATH", "SOURCE_DATE_EPOCH",
            "CVC5_CI_IMAGE", "CVC5_DEBIAN_SNAPSHOT",
        ) if key in environment},
    }
    if shutil.which("dpkg-query"):
        provenance["toolchain"]["packages"] = commands.run(
            ["dpkg-query", "-W", "-f=${Package}\t${Version}\n"])
    # cvc5 is the library target; cvc5-bin is required for the executable.
    build = ["cmake", "--build", "build-parity", "--target", "cvc5-bin", "-j", str(args.jobs)]
    configure = [*CONFIGURE, "-DPython_EXECUTABLE=" + tools["python"]["path"]]
    provenance["recipe"] = {
        "path": str(Path(__file__).resolve()), "sha256": sha256(Path(__file__)),
        "configure": configure, "build": build,
    }
    source = str(args.source_repo.resolve()) if args.source_repo else REPOSITORY
    provenance["source"] = {
        "repository": REPOSITORY, "fetch_source": source, "base": BASE,
        "heads": list(HEADS), "patches": [], "patched_tree": PATCHED_TREE,
    }
    control = output / "control"
    patched = output / "patched"
    for directory in (control, patched):
        commands.run(["git", "init", str(directory)])
        commands.git(directory, "fetch", "--no-tags", "--depth=2", source, BASE, *HEADS)
        for revision in (BASE, *HEADS):
            require(commands.git(directory, "rev-parse", revision + "^{commit}") == revision,
                    f"Source revision mismatch: {revision}")
        for head in HEADS:
            require(commands.git(directory, "show", "-s", "--format=%P", head) == BASE,
                    f"Patch {head} is no longer a single commit on the pinned base")
        commands.git(directory, "checkout", "--detach", BASE)
    control_tree = commands.git(control, "rev-parse", BASE + "^{tree}")
    provenance["source"]["control_tree"] = control_tree
    patches = []
    for number, (head, expected) in enumerate(zip(HEADS, PATCH_HASHES), 1):
        # stdout is patch data: keep diagnostics separate rather than using run().
        patch = output / f"pr{number}.patch"
        with patch.open("wb") as stream:
            subprocess.run(
                ["git", "-C", str(control), "diff", "--binary", "--full-index",
                 "--no-ext-diff", "--no-textconv", BASE, head],
                env=environment, stdout=stream, check=True,
            )
        require(sha256(patch) == expected, f"Patch {number} SHA-256 mismatch")
        patches.append(patch)
        provenance["source"]["patches"].append({"head": head, "sha256": expected})
    # A private index prevents any interaction with the caller's repository index.
    index_env = {"GIT_INDEX_FILE": str(output / "composition.index")}
    commands.git(patched, "read-tree", BASE, extra_env=index_env)
    commands.git(patched, "update-index", "--refresh", extra_env=index_env)
    commands.git(patched, "apply", "--index", str(patches[0]), extra_env=index_env)
    commands.git(patched, "apply", "--3way", str(patches[1]), extra_env=index_env)
    require(not commands.git(patched, "ls-files", "--unmerged", extra_env=index_env),
            "Patch composition has unresolved conflicts; manual resolutions are forbidden")
    require(commands.git(patched, "write-tree", extra_env=index_env) == PATCHED_TREE,
            "Composed tree differs from the pinned tree")
    provenance["dependencies"] = {
        name: {"cmake": f"cmake/Find{name}.cmake",
               "sha256": sha256(control / "cmake" / f"Find{name}.cmake")}
        for name in DEPENDENCIES
    }
    requirements = output / "requirements.txt"
    requirements.write_text(PYPARSING + "\n")
    provenance["dependencies"]["pyparsing"] = {"requirement": PYPARSING}
    for role, directory, tree, extra_env in (
        ("control", control, control_tree, None),
        ("patched", patched, PATCHED_TREE, index_env),
    ):
        commands.git(directory, "diff", "--exit-code", extra_env=extra_env)
        require(commands.git(directory, "write-tree", extra_env=extra_env) == tree,
                f"{role} source/index drift")
        build_dir = directory / "build-parity"
        venv = build_dir / ("venv-" + platform.python_version())
        commands.run([tools["python"]["path"], "-m", "venv", str(venv)])
        python = venv / "bin" / "python3"
        commands.run([str(python), "-m", "pip", "install", "--no-deps",
                      "--require-hashes", "-r", str(requirements)])
        configured = commands.run(configure, cwd=directory)
        # All four dependencies must come from the hash-checked source downloads,
        # not an opportunistically discovered system installation.
        for name in DEPENDENCIES:
            require(f"Building {name}" in configured,
                    f"{role}: {name} was not configured as a pinned source dependency")
        shutil.copy2(build_dir / "CMakeCache.txt", output / f"{role}-CMakeCache.txt")
        commands.run(build, cwd=directory)
        commands.git(directory, "diff", "--exit-code", extra_env=extra_env)
        binary = (build_dir / "bin" / "cvc5").resolve()
        require(binary.is_file() and os.access(binary, os.X_OK),
                f"Missing executable from {role} build: {binary}")
        provenance["binaries"][role] = {
            "path": str(binary), "sha256": sha256(binary),
            "version": commands.run([str(binary), "--version"]),
            "show_config": commands.run([str(binary), "--show-config"]),
        }
    provenance["status"] = "complete"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New or empty output directory (existing builds are never trusted)")
    parser.add_argument("--source-repo", type=Path,
                        help="Optional local Git object source; all revision and patch pins still apply")
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    require(sys.version_info >= (3, 11), "Python 3.11+ is required for pinned stdlib TOML parsing")
    require(args.jobs > 0, "--jobs must be positive")
    output = args.output.resolve()
    require(not output.exists() or not any(output.iterdir()),
            f"Output directory must be empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    provenance = {"schema_version": 1, "status": "incomplete", "binaries": {},
                  "reproducibility": "Source inputs pinned; byte reproducibility not established. "
                                     "Binary SHA-256 values identify these local build outputs only."}
    try:
        build_pair(args, output, provenance)
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        provenance["error"] = str(error)
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    finally:
        encoded = json.dumps(provenance, indent=2) + "\n"
        (output / "provenance.json").write_text(encoded)
        print(encoded, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
