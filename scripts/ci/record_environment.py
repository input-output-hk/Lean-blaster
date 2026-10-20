#!/usr/bin/env python3
"""Record the tested environment without credentials or arbitrary environment dumps."""
import json
import os
from pathlib import Path
import platform
import subprocess


def output(*args):
    try:
        return subprocess.check_output(args, text=True, stderr=subprocess.STDOUT).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        return f"unavailable: {error}"


def main():
    dest = Path('.ci-results')
    dest.mkdir(exist_ok=True)
    manifest = Path('lake-manifest.json')
    data = {
        'schema_version': 1,
        'source_commit': output('git', 'rev-parse', 'HEAD'),
        'event': os.getenv('GITHUB_EVENT_NAME'),
        'run_id': os.getenv('GITHUB_RUN_ID'),
        'run_attempt': os.getenv('GITHUB_RUN_ATTEMPT'),
        'runner': {'os': platform.system(), 'architecture': platform.machine()},
        'lean_toolchain': Path('lean-toolchain').read_text().strip(),
        'lean': output('lean', '--version'),
        'lake': output('lake', '--version'),
        'z3': output('z3', '--version'),
        'z3_source': json.loads((dest / 'z3-source.json').read_text())
                     if (dest / 'z3-source.json').exists() else None,
        'lake_manifest': json.loads(manifest.read_text()) if manifest.exists() else None,
    }
    (dest / 'environment.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
