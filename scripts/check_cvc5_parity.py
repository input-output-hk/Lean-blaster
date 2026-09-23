#!/usr/bin/env python3
"""Verify pinned paired builds, complete models, and observed negative controls."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time

import build_patched_cvc5 as pin

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'Tests/Smt/ModelCorpus'


def digest(path):
    return pin.sha256(Path(path))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def verify_provenance(args):
    data = json.loads(args.provenance.read_text())
    source = data['source']
    require(data['status'] == 'complete', 'incomplete patched build')
    require(source['base'] == pin.BASE and source['heads'] == list(pin.HEADS), 'source pin mismatch')
    require([p['sha256'] for p in source['patches']] == list(pin.PATCH_HASHES), 'patch pin mismatch')
    require(source['patched_tree'] == pin.PATCHED_TREE, 'composed tree mismatch')
    require(data['recipe']['sha256'] == digest(pin.__file__), 'build recipe mismatch; rebuild required')
    for name in ('control', 'patched'):
        binary = getattr(args, name).resolve(strict=True)
        identity = data['binaries'][name]
        require(binary == Path(identity['path']).resolve(strict=True), name + ' resolved path mismatch')
        require(digest(binary) == identity['sha256'], name + ' binary checksum mismatch')
        version = subprocess.check_output([str(binary), '--version'], text=True)
        require(version == identity['version'], name + ' version mismatch')
        print(json.dumps(dict(backend=name, path=str(binary), sha256=digest(binary), version=version)), flush=True)
    print(json.dumps(data, indent=2), flush=True)
    return data


def semantic_check(expected, actual, directory, lean_root):
    expected_path = directory / 'expected.out'
    actual_path = directory / 'actual.out'
    expected_path.write_text(expected)
    actual_path.write_text(actual)
    argv = ['lake', 'env', 'lean', '--run', str(ROOT / 'Tests/Smt/ModelParity.lean'), str(expected_path), str(actual_path)]
    with (directory / 'semantic.log').open('w') as log:
        result = subprocess.run(argv, cwd=lean_root, stdout=log, stderr=subprocess.STDOUT)
    return result.returncode


def solver_case(binary, backend, fixture, directory, lean_root):
    directory.mkdir(parents=True, exist_ok=True)
    query = fixture.read_text()
    capture = json.loads((FIXTURES / 'captured.json').read_text())['cases'][fixture.stem]
    require(digest(fixture) == capture['query_sha256'], 'captured query changed: ' + fixture.stem)
    expected = capture['patched_stdout']
    flags = re.search(r'^; COMMAND-LINE: (.*)$', query, re.M).group(1).split()
    argv = ([str(binary), *flags, '--tlimit-per=120000'] if backend != 'z3'
            else [str(binary), '-in', '-smt2', '-t:120000'])
    # Echo timestamps bound the model retrieval itself, excluding search time.
    instrumented = re.sub(r'^(\(get-value .*\))$',
                          '(echo "blaster-evidence-start")\n\\1\n(echo "blaster-evidence-end")', query, flags=re.M)
    (directory / 'query.smt2').write_text(instrumented)
    lines, evidence_seconds = [], []
    begin = time.monotonic()
    with (directory / 'stderr').open('w') as err:
        process = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err, text=True)
        def collect():
            started = None
            for line in process.stdout:
                if line.strip().strip('"') == 'blaster-evidence-start':
                    started = time.monotonic()
                elif line.strip().strip('"') == 'blaster-evidence-end':
                    if started is not None:
                        evidence_seconds.append(time.monotonic() - started)
                        started = None
                else:
                    lines.append(line)
        reader = threading.Thread(target=collect)
        reader.start()
        process.stdin.write(instrumented + '\n(exit)\n')
        process.stdin.close()
        timed_out = False
        try:
            process.wait(timeout=400)
        except subprocess.TimeoutExpired:
            timed_out = True
            process.kill()
            process.wait()
        reader.join()
        process.stdout.close()
    stdout = ''.join(lines)
    check_exit = semantic_check(expected, stdout, directory, lean_root)
    result = dict(argv=argv, solver_exit=process.returncode, validation_exit=check_exit,
                  wall_seconds=time.monotonic()-begin, evidence_seconds=evidence_seconds, timed_out=timed_out,
                  complete=process.returncode == 0 and check_exit == 0 and not timed_out)
    (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result, stdout


def trace_solver(binary, directory):
    if any(arg in ('--version', '-version') for arg in sys.argv[1:]):
        os.execv(binary, [binary, *sys.argv[1:]])
    trace = dict(argv=[binary, *sys.argv[1:]], started=time.monotonic(),
                 commands=[], responses=[], evidence_upper_bound_seconds=[])
    process = subprocess.Popen(trace['argv'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    def forward():
        for line in process.stdout:
            trace['responses'].append(line)
            sys.stdout.write(line)
            sys.stdout.flush()
    reader = threading.Thread(target=forward)
    reader.start()
    started = None
    try:
        for line in sys.stdin:
            trace['commands'].append(line)
            if line.startswith(('(get-value', '(get-model')):
                if started is None:
                    started = time.monotonic()
            elif started is not None:
                trace['evidence_upper_bound_seconds'].append(time.monotonic() - started)
                started = None
            process.stdin.write(line)
            process.stdin.flush()
            if line.strip() == '(exit)':
                break
        process.stdin.close()
        process.wait(timeout=5)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        reader.join()
        process.stdout.close()
        trace['exit'] = process.returncode
        (Path(directory) / f'transcript-{os.getpid()}.json').write_text(json.dumps(trace, indent=2) + '\n')
    sys.exit(process.returncode)


def corpus(binary, backend, directory, lean_root, profile='patched'):
    directory.mkdir(parents=True, exist_ok=True)
    bindir = directory / 'bin'
    bindir.mkdir(exist_ok=True)
    # PATH selection is explicit. A missing chosen binary cannot fall back to stock.
    link = bindir / backend
    if link.is_symlink():
        link.unlink()
    link.write_text(f'#!{sys.executable}\nimport sys\nsys.path.insert(0, {str(ROOT / "scripts")!r})\n'
                    f'from check_cvc5_parity import trace_solver\ntrace_solver({str(binary.resolve(strict=True))!r}, {str(directory)!r})\n')
    link.chmod(0o755)
    env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'],
               BLASTER_SOLVER=backend, BLASTER_CVC5_BUILD=profile, BLASTER_TIMEOUT='120',
               BLASTER_STRICT_CVC5_RESULTS='1', LEAN_NUM_THREADS='5')
    argv = ['lake', 'lean', str(ROOT / 'Tests/Smt/ModelCorpus.lean')]
    start = time.monotonic()
    with (directory / 'corpus.log').open('w') as log:
        result = subprocess.run(argv, cwd=lean_root, env=env, stdout=log, stderr=subprocess.STDOUT)
    cases = [json.loads(line.removeprefix('MODEL_CASE:')) for line in (directory / 'corpus.log').read_text().splitlines()
             if line.startswith('MODEL_CASE:')]
    names = {'none', 'int', 'structure', 'some', 'tuple', 'list', 'string', 'nat',
             'quoted-constructor', 'escaped-quoted-identifier'}
    if profile == 'patched':
        names.update(('natgroup-first', 'natgroup-second'))
    negative_cases = {'list', 'natgroup-first', 'natgroup-second'}
    complete_inventory = len(cases) == len(names) and {case['case'] for case in cases} == names
    traces = sorted((json.loads(path.read_text()) for path in directory.glob('transcript-*.json')),
                    key=lambda trace: trace['started'])
    complete_inventory = (complete_inventory and len(traces) == len(cases)
                          and all(trace['exit'] == 0 for trace in traces))
    for index, case in enumerate(cases):
        trace = traces[index] if index < len(traces) else None
        case['evidence_upper_bound_seconds'] = trace['evidence_upper_bound_seconds'] if trace else []
        case['complete'] = (case['complete'] and trace is not None
                            and bool(trace['evidence_upper_bound_seconds']) and trace['exit'] == 0)
        case['negative_verdict'] = (case['case'] in negative_cases and case['verdict'] == 'unknown'
                                    and trace is not None
                                    and any(line.strip() == 'unknown' for line in trace['responses']))
    complete = result.returncode == 0 and complete_inventory and all(case['complete'] for case in cases)
    negative = (result.returncode == 1 and complete_inventory
                and any(case['negative_verdict'] for case in cases)
                and all(case['complete'] or case['negative_verdict'] for case in cases))
    row = dict(argv=argv, exit=result.returncode, wall_seconds=time.monotonic()-start, binary=str(binary),
               profile=profile, cases=cases, complete=complete, expected_corpus_negative=negative)
    (directory / 'result.json').write_text(json.dumps(row, indent=2) + '\n')
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--control', type=Path, required=True)
    parser.add_argument('--patched', type=Path, required=True)
    parser.add_argument('--provenance', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-root', type=Path, default=ROOT)
    parser.add_argument('--z3', type=Path)
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    require(not any(args.output.iterdir()), 'parity output directory must be empty')
    verify_provenance(args)
    results = {}
    failures = []
    captures = json.loads((FIXTURES / 'captured.json').read_text())['cases']
    fixtures = sorted(FIXTURES.glob('*.smt2'))
    require({path.stem for path in fixtures} == set(captures), 'required fixture inventory is incomplete')
    for backend in ('control', 'patched', 'z3'):
        binary = getattr(args, backend)
        if binary is None:
            continue
        binary = binary.resolve(strict=True)
        rows = {}
        for fixture in fixtures:
            row, stdout = solver_case(binary, backend, fixture, args.output / backend / fixture.stem, args.lean_root)
            if backend == 'control':
                negative_dir = args.output / backend / fixture.stem / 'negative-control'
                negative_dir.mkdir()
                row['negative_validation_exit'] = semantic_check(
                    captures[fixture.stem]['control_stdout'], stdout, negative_dir, args.lean_root)
                negative = (row['solver_exit'] == 0 and row['validation_exit'] == 1
                            and row['negative_validation_exit'] == 0 and not row['timed_out'])
                row['patch_effect'] = ('NOT REPRODUCED' if row['complete'] else
                                      'EXPECTED NEGATIVE CONTROL' if negative else 'VALIDATION FAILURE')
                if row['patch_effect'] == 'VALIDATION FAILURE':
                    failures.append(backend + '/' + fixture.stem)
            elif not row['complete']:
                failures.append(backend + '/' + fixture.stem)
            rows[fixture.stem] = row
        rows['supported-corpus'] = corpus(binary, 'z3' if backend == 'z3' else 'cvc5', args.output / backend / 'supported-corpus', args.lean_root)
        if backend == 'control':
            for case in rows['supported-corpus']['cases']:
                case['patch_effect'] = ('NOT REPRODUCED' if case['complete'] else
                                        'EXPECTED NEGATIVE CONTROL' if case['negative_verdict'] else 'VALIDATION FAILURE')
            rows['baseline-corpus'] = corpus(binary, 'cvc5', args.output / backend / 'baseline-corpus', args.lean_root, 'stock')
            if not rows['baseline-corpus']['complete']:
                failures.append('control/baseline-corpus')
            if not (rows['supported-corpus']['complete'] or rows['supported-corpus']['expected_corpus_negative']):
                failures.append('control/supported-corpus')
        elif not rows['supported-corpus']['complete']:
            failures.append(backend + '/supported-corpus')
        results[backend] = rows
    for family in ('rec-alias-', 'macros-ground-'):
        if not any(name.startswith(family) and row.get('patch_effect') == 'EXPECTED NEGATIVE CONTROL'
                   for name, row in results['control'].items()):
            failures.append('no documented negative control observed: ' + family)
    (args.output / 'matrix.json').write_text(json.dumps(dict(results=results, failures=failures), indent=2) + '\n')
    require(not failures, 'Parity validation failed: ' + ', '.join(failures))
    print('PASS: complete patched evidence and observed unpatched negative controls; original six-case recovery remains separate')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        sys.exit('ERROR: ' + str(error))
