#!/usr/bin/env python3
"""Alternate reference/fused preparation, each followed by its proof phase.

Use a warmed workspace from prepare_local.py --staged-cek. Expected SellNFT
multisatisfaction timeouts remain error rows; other unexpected outcomes stop
this experiment instead of silently contributing to a speedup summary.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, required=True)
p.add_argument('--cases', nargs='+', default=['sellnft:1800', 'global:1600'])
p.add_argument('--repeat', type=int, default=3)
p.add_argument('--prefix', default='paired')
p.add_argument('--timeout', type=float, default=180)
p.add_argument('--max-rss-gib', type=float, default=12)
a = p.parse_args()
if a.repeat < 1 or not re.fullmatch(r'[A-Za-z0-9_-]+', a.prefix):
    p.error('repeat must be positive and prefix must be a filename-safe label')
root = a.root.resolve()
runner = Path(__file__).resolve().parents[1] / 'cardano_bench.py'

for rep in range(1, a.repeat + 1):
    for case in a.cases:
        for staged in ([False, True] if rep % 2 else [True, False]):
            arm = 'fused' if staged else 'reference'
            base_label = f'{a.prefix}-{case.replace(":", "-")}-{arm}-{rep}'
            for proof in [False, True]:
                label = base_label + ('-proof' if proof else '')
                cmd = [sys.executable, str(runner), '--root', str(root),
                       '--label', label, '--cases', case,
                       '--timeout', str(a.timeout), '--max-rss-gib', str(a.max_rss_gib)]
                if staged:
                    cmd.append('--staged-cek')
                if proof:
                    cmd.append('--proofs-only')
                subprocess.run(cmd, cwd=root/'blaster', check=True)
                row = json.loads((root/'results'/label/'results.json').read_text())['runs'][0]
                if row['status'] == 'completed':
                    continue
                verdicts = row.get('verdicts', [])
                known_timeout = (
                    case == 'sellnft:1800' and proof and row['status'] == 'error'
                    and len(verdicts) == 5
                    and sum('timeout' in v for v in verdicts) == 1
                    and sum('✅ Valid' in v for v in verdicts) == 2
                    and sum('Expected Falsified' in v for v in verdicts) == 2)
                if known_timeout:
                    print(f'{label}: existing SellNFT timeout retained as an error row.', flush=True)
                else:
                    raise SystemExit(f'Unexpected outcome; inspect {root / "results" / label / "results.json"}')
