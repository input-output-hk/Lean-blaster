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
import shutil

HERE = Path(__file__).resolve().parent
NAMES = ['blaster', 'cardano', 'wsc', 'plutuscore', 'plutuscore-wsc']
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, required=True, help='New output directory')
for name in NAMES:
    p.add_argument('--' + name, type=Path, required=True, help='Existing local source repository')
p.add_argument('--blaster-rev', default=None, help='Override the pinned baseline with a candidate commit')
p.add_argument('--staged-cek', action='store_true', help='Apply the verified fused CEK prototype to both interpreter pins; requires a specialization-enabled Blaster revision')
p.add_argument('--lifted-search', action='store_true', help='Install certified SellNFT search workers in the named CEK; requires --staged-cek')
p.add_argument('--no-build', action='store_true', help='Create checkouts only; build dependencies before timing')
a = p.parse_args()
if a.lifted_search and not a.staged_cek:
    p.error('--lifted-search requires --staged-cek')
if a.staged_cek and not a.blaster_rev:
    p.error('--staged-cek requires --blaster-rev with the specialization-enabled candidate')
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
if a.staged_cek:
    for name in ['plutuscore', 'plutuscore-wsc']:
        subprocess.run(['git', 'apply', str(HERE / 'patches' / (name + '-staged.patch'))], cwd=root/name, check=True)
        # Include added modules in the runner's tracked-patch hash without committing.
        subprocess.run(['git', 'add', '--intent-to-add', 'PlutusCore/UPLC/StagedCek.lean', 'PlutusCore/UPLC/StagedCekProofs.lean'], cwd=root/name, check=True)
    for name, fixture in [('cardano', 'StagedControl'), ('wsc', 'StagedControlIndexed')]:
        target = root/name/'Tests/Benchmarks'
        target.mkdir(parents=True, exist_ok=True)
        (target/'OptimizeTestUtils.lean').write_text((root/'blaster/Tests/Utils.lean').read_text())
        (target/(fixture + '.lean')).write_text((HERE/'fixtures'/(fixture + '.lean')).read_text())
if a.lifted_search:
    target = root/'plutuscore'
    overlay = HERE/'overlays'/'lifted-search'
    for source in sorted(overlay.rglob('*.lean')):
        relative = source.relative_to(overlay)
        (target/relative).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target/relative)
        subprocess.run(['git', 'add', '--intent-to-add', str(relative)], cwd=target, check=True)
    subprocess.run(['git', 'apply', str(HERE/'patches'/'plutuscore-lifted-search.patch')], cwd=target, check=True)
    for fixture in ['LoopCekControl', 'LiftedTemplateSource']:
        shutil.copyfile(HERE/'fixtures'/(fixture+'.lean'), root/'cardano'/'Tests/Benchmarks'/(fixture+'.lean'))
if not a.no_build:
    subprocess.run(['lake', 'build', 'CardanoLedgerApi.V3', 'PlutusCore.UPLC'], cwd=root/'cardano', check=True)
    subprocess.run(['lake', 'build', 'WSC.Prep.GlobalImport'], cwd=root/'wsc', check=True)
    if a.staged_cek:
        subprocess.run(['lake', 'build', 'Tests.Benchmarks.StagedControl'], cwd=root/'cardano', check=True)
        subprocess.run(['lake', 'build', 'Tests.Benchmarks.StagedControlIndexed'], cwd=root/'wsc', check=True)
    if a.lifted_search:
        subprocess.run(['lake', 'build', 'CardanoLedgerApi.V2', 'Tests.Benchmarks.LoopCekControl',
                        'Tests.Benchmarks.LiftedTemplateSource'], cwd=root/'cardano', check=True)
print(root)
