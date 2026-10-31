#!/usr/bin/env python3
"""Fetch the pinned official Z3 release into the executable's private solver directory."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import platform
import shutil
import urllib.request
import zipfile


ROOT = Path(__file__).resolve().parent.parent


def host_platform():
    system = {"Darwin": "macos", "Linux": "linux", "Windows": "windows"}.get(platform.system())
    arch = {"arm64": "arm64", "aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(platform.machine().lower())
    if not system or not arch:
        raise SystemExit("No pinned Z3 archive for this platform; use --platform or --solver instead")
    return f"{system}-{arch}"


def install(target_platform, destination):
    lock = json.loads((ROOT / "scripts" / "z3-release.json").read_text())
    asset = lock["platforms"][target_platform]
    cache = ROOT / ".lake" / "downloads"
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / asset["asset"]
    if not archive.exists() or hashlib.sha256(archive.read_bytes()).hexdigest() != asset["sha256"]:
        url = f'https://github.com/Z3Prover/z3/releases/download/{lock["tag"]}/{asset["asset"]}'
        request = urllib.request.Request(url, headers={"User-Agent": "lean-blaster-release"})
        partial = archive.with_suffix(".partial")
        try:
            with urllib.request.urlopen(request, timeout=60) as response, partial.open("wb") as output:
                shutil.copyfileobj(response, output)
            digest = hashlib.sha256(partial.read_bytes()).hexdigest()
            if digest != asset["sha256"]:
                raise SystemExit(f"Z3 archive checksum mismatch: expected {asset['sha256']}, received {digest}")
            partial.replace(archive)
        finally:
            partial.unlink(missing_ok=True)
    destination.mkdir(parents=True, exist_ok=True)
    executable = "z3.exe" if target_platform.startswith("windows-") else "z3"
    found_executable = False
    found_license = False
    with zipfile.ZipFile(archive) as package:
        for entry in package.infolist():
            path = PurePosixPath(entry.filename)
            if path.is_absolute() or ".." in path.parts:
                raise SystemExit("Unexpected unsafe path in Z3 archive")
            if entry.is_dir():
                continue
            if path.name == "LICENSE.txt":
                (destination / "LICENSE-Z3.txt").write_bytes(package.read(entry))
                found_license = True
            elif len(path.parts) >= 3 and path.parts[-2] == "bin" and (
                path.name == executable or path.name in {"libz3.dylib", "libz3.dll"}
                or path.name.startswith("libz3.so")
            ):
                # Keep bundled runtime libraries beside the executable.
                output = destination / path.name
                output.write_bytes(package.read(entry))
                if path.name == executable:
                    output.chmod(output.stat().st_mode | 0o111)
                    found_executable = True
    if not found_executable or not found_license:
        raise SystemExit("The Z3 archive is missing its executable or license notice")
    (destination / "release.json").write_text(json.dumps({
        "tag": lock["tag"], "platform": target_platform, **asset
    }, indent=2) + "\n")
    print(f"Installed {lock['tag']} ({target_platform}) in {destination}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--platform", default=host_platform())
    parser.add_argument("--destination", type=Path, default=ROOT / ".lake/build/libexec/lean-blaster")
    arguments = parser.parse_args()
    install(arguments.platform, arguments.destination.resolve())
