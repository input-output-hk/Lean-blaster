#!/usr/bin/env python3
"""Summarize normalization profiles saved by cardano_bench.py.

These are exclusive wall times under syntactic normalization heads. A CEK
head's time is not a count of CEK transitions, nor proof that it is static.
"""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('results', type=Path)
p.add_argument('--top', type=int, default=15)
a = p.parse_args()
for run in json.loads(a.results.read_text())['runs']:
    if not run.get('profiles'):
        continue
    profile = run['profiles'][-1]
    elapsed = profile['elapsed_ns']
    accounted = sum(h['self_ns'] for h in profile['heads'])
    if accounted != elapsed:
        raise SystemExit('Profile time does not partition elapsed time')
    if profile['imbalances'] or (profile['status'] == 'complete' and profile['active_frames']):
        raise SystemExit('Unbalanced normalization frames')
    print(f"{run['case']}:{run['budget']} {run['status']} profile={profile['status']} "
          f"seconds={elapsed / 1e9:.3f} active_frames={profile['active_frames']}")
    print(f"cache hits={profile['cache_hits']} misses={profile['cache_misses']} "
          f"mvar bypasses={profile['cache_bypasses']}")
    for head in sorted(profile['heads'], key=lambda h: h['self_ns'], reverse=True)[:a.top]:
        print(f"  {head['self_ns'] / max(elapsed, 1):6.1%} "
              f"{head['self_ns'] / 1e9:8.3f}s {head['calls']:10d}  {head['head']}")
    print('Choice propagation events:')
    for name, count in sorted(profile['events'].items(), key=lambda e: e[1], reverse=True)[:a.top]:
        print(f'  {count:10d}  {name}')
