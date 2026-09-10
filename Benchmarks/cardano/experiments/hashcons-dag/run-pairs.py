#!/usr/bin/env python3
"""Compare already-built workspaces serially, retaining the existing proof controls."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--reference', type=Path, required=True)
parser.add_argument('--candidate', type=Path, required=True)
parser.add_argument('--pairs', type=int, default=3)
parser.add_argument('--label', default='hashcons-dag')
args = parser.parse_args()
runner = Path(__file__).resolve().parents[3] / 'cardano_bench.py'
if args.pairs < 1:
    parser.error('pairs must be positive')

for pair in range(1, args.pairs + 1):
    arms = [('reference', args.reference), ('candidate', args.candidate)]
    if pair % 2 == 0:
        arms.reverse()
    for case, fuel in [('sellnft', 1800), ('governance', 9000)]:
        for arm, root in arms:
            for proof in [False, True]:
                label = f'{args.label}-pair{pair}-{case}-{arm}' + ('-proof' if proof else '')
                cmd = [sys.executable, str(runner), '--root', str(root),
                       '--label', label, '--cases', f'{case}:{fuel}',
                       '--staged-cek', '--timeout', '120', '--max-rss-gib', '12']
                if case == 'sellnft':
                    cmd.append('--lifted-search')
                if proof:
                    cmd.append('--proofs-only')
                print('START', label, flush=True)
                subprocess.run(cmd, check=True)
                row = json.loads((root / 'results' / label / 'results.json').read_text())['runs'][0]
                if proof and case == 'sellnft':
                    verdicts = row.get('verdicts', [])
                    expected = (row['status'] == 'error' and len(verdicts) == 5
                                and '✅ Valid' in verdicts[0] and '✅ Valid' in verdicts[1]
                                and 'Unexpected check-sat result: timeout' in verdicts[2]
                                and '✅ Expected Falsified' in verdicts[3]
                                and '✅ Expected Falsified' in verdicts[4])
                elif proof:
                    expected = (row['status'] == 'completed' and len(row.get('verdicts', [])) == 4
                                and all('✅ Valid' in v for v in row['verdicts']))
                else:
                    expected = row['status'] == 'completed'
                if not expected:
                    raise SystemExit('Unexpected benchmark outcome: ' + json.dumps(row))
            print('ARM_COMPLETE', pair, case, arm, flush=True)
