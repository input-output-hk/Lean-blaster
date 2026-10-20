#!/usr/bin/env python3
"""Forward Z3's protocol unchanged, retaining input and enforcing a wall deadline."""
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import threading
import time
import uuid


def main():
    executable = os.environ['Z3_REAL_EXECUTABLE']
    args = sys.argv[1:]
    if '-in' not in args:
        os.execv(executable, [executable, *args])
    limit = float(os.environ.get('Z3_SOLVER_TIMEOUT_SECONDS', '120'))
    if not math.isfinite(limit) or limit <= 0:
        raise ValueError('Z3_SOLVER_TIMEOUT_SECONDS must be finite and positive')
    directory = Path(os.environ.get('Z3_QUERY_LOG_DIR', '.ci-results/solver'))
    directory.mkdir(parents=True, exist_ok=True)
    prefix = directory / f'z3-{uuid.uuid4().hex}'
    query = prefix.with_suffix('.smt2')
    start = time.monotonic()
    errors = []
    with query.open('wb') as evidence:
        process = subprocess.Popen([executable, *args], stdin=subprocess.PIPE)
        def forward():
            try:
                while True:
                    chunk = os.read(sys.stdin.fileno(), 65536)
                    if not chunk:
                        break
                    evidence.write(chunk)
                    evidence.flush()
                    process.stdin.write(chunk)
                    process.stdin.flush()
                process.stdin.close()
            except (BrokenPipeError, OSError, ValueError) as exc:
                errors.append(str(exc))
        worker = threading.Thread(target=forward, daemon=True)
        worker.start()
        timed_out = False
        try:
            code = process.wait(timeout=limit)
        except subprocess.TimeoutExpired:
            timed_out = True
            process.kill()
            process.wait()
            code = 124
            # A hard timeout must produce a protocol error, never an acceptable
            # 'unknown' warning that would let a negative test silently pass.
            message = f'CI Z3 wall deadline ({limit:g}s) exceeded; query: {query}'
            print('(error "' + message.replace('"', '""') + '")', flush=True)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
            prefix.with_suffix('.json').write_text(json.dumps({
                'executable': executable, 'args': args, 'parent_pid': os.getppid(),
                'timeout_seconds': limit, 'timed_out': timed_out, 'exit_code': code,
                'elapsed_seconds': round(time.monotonic() - start, 3),
                'input_file': str(query), 'forward_errors': errors,
            }, indent=2) + '\n')
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
