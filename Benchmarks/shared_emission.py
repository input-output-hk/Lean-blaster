#!/usr/bin/env python3
"""Compare the same build with SMT sharing off/on; emit reproducible JSON.

Run from the repository root after `lake build Blaster`:
  python3 Benchmarks/shared_emission.py --depths 16 20 24 --repeat 3
The wall time includes a fresh Lean process. Phase times exclude startup.
Query sizes come from a separate dump-only run, so dumping is not timed.
"""
import argparse
import json
import os
import signal
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--depths', nargs='+', type=int, default=[16, 20])
parser.add_argument('--repeat', type=int, default=3)
parser.add_argument('--skip-dump', action='store_true', help='Time large queries without generating a separate text dump')
parser.add_argument('--share-smt', nargs='+', type=int, choices=[0, 1], default=[0, 1])
parser.add_argument('--timeout', type=float, default=300)
parser.add_argument('--output', type=Path, default=Path('Benchmarks/shared-emission-results.json'))
args = parser.parse_args()
if args.repeat < 1 or any(d < 1 for d in args.depths):
    parser.error('repeat and depths must be positive')
root = Path(__file__).resolve().parents[1]
prefix = (root / 'Benchmarks/SharedEmission.lean').read_text()
phase_re = re.compile(r'\[End\]: (.+?) \(([0-9.]+)s\)')
def run(command, **kwargs):
    """Bound the whole Lake/Lean/solver process tree, including on timeout."""
    timeout = kwargs.pop('timeout')
    capture = kwargs.pop('capture_output', False)
    if capture:
        kwargs['stdout'] = subprocess.PIPE
        kwargs['stderr'] = subprocess.PIPE
    with subprocess.Popen(command, start_new_session=True, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)

metadata = {
    'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    'lean': subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root, text=True).strip(),
    'z3': subprocess.check_output(['z3', '--version'], text=True).strip(),
    'repeat': args.repeat,
}
rows = []
def checkpoint():
    args.output.write_text(json.dumps({**metadata, 'rows': rows}, indent=2) + '\n')

with tempfile.TemporaryDirectory(prefix='blaster-emission-') as tmp:
    source = Path(tmp) / 'Case.lean'
    for depth in args.depths:
        for shared in args.share_smt:
            samples = []
            row = {'depth': depth, 'share_smt': shared, 'query_dump_bytes': None,
                   'samples': samples}
            rows.append(row)
            for _ in range(args.repeat):
                source.write_text(prefix + f'\n#blaster (verbose: 1) (share-smt: {shared}) (timeout: 10)\n'
                                  f'  [∀ x : Int, 0 ≤ x → emissionChain% {depth} x]\n')
                start = time.monotonic()
                result = run(['lake', 'env', 'lean', str(source)], cwd=root,
                                        capture_output=True, text=True, timeout=args.timeout)
                wall = time.monotonic() - start
                output = result.stdout + result.stderr
                if result.returncode or '✅ Valid' not in output:
                    raise RuntimeError(output)
                phases = {name: float(value) for name, value in phase_re.findall(output)}
                samples.append({'wall_s': wall, **phases})
                row['median'] = {key: statistics.median(sample[key] for sample in samples) for key in samples[0]}
                checkpoint()
            if args.skip_dump:
                print(json.dumps(row), flush=True)
                continue
            source.write_text(prefix + f'\n#blaster (share-smt: {shared}) (only-smt-lib: 1) (dump-smt-lib: 1)\n'
                              f'  [∀ x : Int, 0 ≤ x → emissionChain% {depth} x]\n')
            dump_file = Path(tmp) / 'query.txt'
            with dump_file.open('wb') as output:
                result = run(['lake', 'env', 'lean', str(source)], cwd=root,
                                        stdout=output, stderr=subprocess.PIPE, timeout=args.timeout)
            if result.returncode:
                raise RuntimeError(result.stderr.decode() + dump_file.read_text()[-2000:])
            marker = b'Smt Query:\n'
            with dump_file.open('rb') as dump:
                while (line := dump.readline()) and line != marker:
                    pass
                if line != marker:
                    raise RuntimeError('SMT dump marker missing')
                query_bytes = dump_file.stat().st_size - dump.tell()
            row['query_dump_bytes'] = query_bytes
            checkpoint()
            print(json.dumps(row), flush=True)
