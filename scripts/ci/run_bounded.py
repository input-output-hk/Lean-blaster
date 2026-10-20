#!/usr/bin/env python3
"""Bound a build's process tree and retain diagnostics before terminating it."""
import argparse
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import time


def snapshot(group):
    try:
        result = subprocess.run(['ps', '-axo', 'pid=,ppid=,pgid=,etime=,args='],
                                capture_output=True, text=True, timeout=5, check=True)
        return [line.strip() for line in result.stdout.splitlines()
                if len(line.split(None, 4)) == 5 and line.split(None, 4)[2] == str(group)]
    except (OSError, subprocess.SubprocessError) as exc:
        return [f'Process snapshot unavailable: {exc}']


def stop(group):
    # Descendants can outlive their parent. Always terminate the private group.
    for sig in [signal.SIGTERM, signal.SIGKILL]:
        try:
            os.killpg(group, sig)
        except ProcessLookupError:
            return
        except PermissionError:
            # Some macOS sandboxes reject negative-pid/group signalling. Only
            # signal positive pids verified to belong to this private group.
            members = snapshot(group)
            if any(line.startswith('Process snapshot unavailable:') for line in members):
                raise
            for line in reversed(members):
                try:
                    os.kill(int(line.split()[0]), sig)
                except ProcessLookupError:
                    pass
        if sig == signal.SIGTERM:
            time.sleep(0.2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--interval', type=float, default=60)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not all(math.isfinite(v) and v > 0 for v in [args.timeout, args.interval]) or not command:
        parser.error('positive timeout/interval and a command are required')
    args.report.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    process = subprocess.Popen(command, start_new_session=True)
    report = {'command': command, 'timeout_seconds': args.timeout, 'timed_out': False}
    code = 1
    def interrupted(signum, _frame):
        raise KeyboardInterrupt(signum)
    for sig in [signal.SIGINT, signal.SIGTERM]:
        signal.signal(sig, interrupted)
    try:
        while True:
            remaining = args.timeout - (time.monotonic() - start)
            if remaining <= 0:
                report['timed_out'] = True
                report['processes'] = snapshot(process.pid)
                print(f'BUILD TIMEOUT after {args.timeout:g}s: {command}', flush=True)
                for line in report['processes']:
                    print(line, flush=True)
                code = 124
                break
            try:
                code = process.wait(timeout=min(args.interval, remaining))
                break
            except subprocess.TimeoutExpired:
                print(f'Build running for {time.monotonic() - start:.0f}s; active processes:', flush=True)
                for line in snapshot(process.pid):
                    print(line, flush=True)
    except KeyboardInterrupt as exc:
        report['interrupted'] = True
        code = 128 + (exc.args[0] if exc.args else signal.SIGINT)
    finally:
        stop(process.pid)
        process.wait()
        report.update(exit_code=code, elapsed_seconds=round(time.monotonic() - start, 3))
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
