#!/usr/bin/env python3
"""Install lean-blaster, its libraries, and pinned Z3 as a normal user command."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import uuid

import fetch_z3


ROOT = Path(__file__).resolve().parent.parent


def replace_link(link, target):
    """Switch an installer-owned symlink atomically; preserve unrelated commands."""
    temporary = link.with_name(f".{link.name}.{uuid.uuid4().hex}.tmp")
    try:
        temporary.symlink_to(target)
        os.replace(temporary, link)
    finally:
        temporary.unlink(missing_ok=True)


def owned_link(link, prefix):
    if not link.exists() and not link.is_symlink():
        return True
    if not link.is_symlink():
        return False
    return link.resolve().is_relative_to(prefix.resolve())


def install(prefix, bin_dir, skip_build=False):
    if os.name == "nt":
        raise SystemExit("This source installer currently supports macOS and Linux")
    prefix = prefix.expanduser().resolve()
    bin_dir = bin_dir.expanduser().resolve()
    command = bin_dir / "lean-blaster"
    private_command = prefix / "bin" / "lean-blaster"
    for link in {command, private_command}:
        if not owned_link(link, prefix):
            raise SystemExit(f"I won't replace the existing command at {link}; choose --bin-dir")
    if prefix.exists() and any(prefix.iterdir()) and not (prefix / "install.json").is_file():
        raise SystemExit(f"{prefix} isn't an existing lean-blaster installation; choose an empty --prefix")
    if not skip_build:
        print("I'm building lean-blaster…", flush=True)
        subprocess.run(["lake", "build", "lean-blaster"], cwd=ROOT, check=True)
    binary = ROOT / ".lake/build/bin/lean-blaster"
    library = ROOT / ".lake/build/lib/lean"
    if not binary.is_file() or not (library / "Blaster.olean").is_file():
        raise SystemExit("Build lean-blaster before installing it")
    sysroot = Path(subprocess.check_output(
        ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    lean_version = (ROOT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
    prefix.mkdir(parents=True, exist_ok=True)
    if not (prefix / "install.json").exists():
        (prefix / "install.json").write_text('{"installationInProgress": true}\n')
    releases = prefix / "releases"
    releases.mkdir(exist_ok=True)
    release_id = uuid.uuid4().hex[:12]
    release = releases / release_id
    with tempfile.TemporaryDirectory(prefix=".staging-", dir=releases) as temporary:
        stage = Path(temporary) / "payload"
        (stage / "bin").mkdir(parents=True)
        shutil.copy2(binary, stage / "bin/lean-blaster")
        installed_lib = stage / "lib/lean"
        installed_lib.mkdir(parents=True)
        # Install runtime module artifacts, excluding Tests and build-system caches.
        for source in library.rglob("*"):
            if not source.is_file():
                continue
            relative = source.relative_to(library)
            if not (relative.parts[0] == "Blaster" or source.name.startswith(("Blaster.", "Blaster_", "libBlaster."))):
                continue
            if not source.name.endswith((".olean", ".olean.private", ".olean.server", ".ilean", ".dylib", ".so", ".dll")):
                continue
            destination = installed_lib / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        solver_dir = stage / "libexec/lean-blaster"
        fetch_z3.install(fetch_z3.host_platform(), solver_dir)
        (solver_dir / "runtime.json").write_text(json.dumps({
            "leanVersion": lean_version, "leanSysroot": str(sysroot)
        }, indent=2) + "\n")
        shutil.copy2(ROOT / "LICENSE", stage / "LICENSE")
        stage.rename(release)
    # Finished releases remain available to processes already running an older executable.
    private_command.parent.mkdir(parents=True, exist_ok=True)
    bin_dir.mkdir(parents=True, exist_ok=True)
    replace_link(private_command, Path("..") / "releases" / release_id / "bin/lean-blaster")
    if command != private_command:
        replace_link(command, private_command)
    (prefix / "install.json").write_text(json.dumps({
        "activeRelease": release_id, "command": str(command), "leanVersion": lean_version,
        "leanSysroot": str(sysroot)
    }, indent=2) + "\n")
    print(f"Installed lean-blaster at {command}")
    if str(bin_dir) not in os.environ.get("PATH", "").split(os.pathsep):
        print(f"Add {bin_dir} to PATH to run 'lean-blaster' from your shell")
    else:
        print("You're ready. Try: lean-blaster doctor")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, help="Private installation directory")
    parser.add_argument("--bin-dir", type=Path, help="Directory for the lean-blaster command")
    parser.add_argument("--skip-build", action="store_true", help="Install an already-built executable")
    args = parser.parse_args()
    default_prefix = Path.home() / ".local/share/lean-blaster"
    destination = args.prefix or default_prefix
    command_dir = args.bin_dir or (destination / "bin" if args.prefix else Path.home() / ".local/bin")
    try:
        install(destination, command_dir, args.skip_build)
    except (OSError, subprocess.CalledProcessError) as error:
        sys.exit(f"I couldn't install lean-blaster: {error}")
