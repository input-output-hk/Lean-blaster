#!/usr/bin/env python3
"""Create isolated, pinned Cardano benchmark checkouts from existing local clones.

Source working-tree changes are never copied. Two workload pins are local
investigation commits, so this intentionally accepts local repositories rather
than pretending every pin is fetchable from upstream GitHub.
"""
import argparse
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
NAMES = ['blaster', 'cardano', 'wsc', 'plutuscore', 'plutuscore-wsc']
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, required=True, help='New output directory')
for name in NAMES:
    p.add_argument('--' + name, type=Path, required=True, help='Existing local source repository')
p.add_argument('--blaster-rev', default=None, help='Override the pinned baseline with a candidate commit')
p.add_argument('--no-build', action='store_true', help='Create checkouts only; build dependencies before timing')
a = p.parse_args()
pins = json.loads((HERE / 'pins.json').read_text())
if a.blaster_rev:
    pins['blaster'] = a.blaster_rev
root = a.root.resolve()
if root.exists():
    raise SystemExit('Output directory already exists. Choose a new directory.')
# Validate all inputs before creating anything.
for name in NAMES:
    source = getattr(a, name.replace('-', '_')).resolve()
    subprocess.run(['git', '-C', str(source), 'cat-file', '-e', pins[name] + '^{commit}'], check=True)
root.mkdir(parents=True)
for name in NAMES:
    source = getattr(a, name.replace('-', '_')).resolve()
    target = root / name
    subprocess.run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(source), str(target)], check=True)
    subprocess.run(['git', 'checkout', '--detach', pins[name]], cwd=target, check=True)
    patch = HERE / 'patches' / (name + '.patch')
    if patch.exists():
        subprocess.run(['git', 'apply', str(patch)], cwd=target, check=True)
if not a.no_build:
    subprocess.run(['lake', 'build', 'CardanoLedgerApi.V3', 'PlutusCore.UPLC'], cwd=root/'cardano', check=True)
    subprocess.run(['lake', 'build', 'WSC.Prep.GlobalImport'], cwd=root/'wsc', check=True)
print(root)
