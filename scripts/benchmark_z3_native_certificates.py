#!/usr/bin/env python3
"""Compare the official Z3 Lean exporter with a reflected Farkas identity.

Run with a Python environment containing z3-solver. --upstream is an unmodified
Z3 source checkout. Its Python exporter is imported read-only; a separate Lean
workspace and all certificates/proofs are written under --out. One saved native
certificate is reused by both variants. Every proposed reflected lemma must
actually reference the soundness theorem in its kernel-accepted proof.
"""
import argparse
from fractions import Fraction
import functools
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def reflected(exporter, original, selected, graph, node):
    # Preserve the official heuristic selecting the large conflicts. This
    # experiment replaces only their identity proof, not their bound evidence.
    lines = original(graph, node)
    if lines is None:
        return None
    premises, bounds = exporter._lemma_bounds(graph, node)
    coefficients = [Fraction(c) for c in graph.decl(node).parameters[1:]]
    multipliers = exporter._farkas_multipliers(
        [b[5] for b in bounds], coefficients, [b[4] for b in bounds])
    combination, _, total, _ = exporter._combination_sum(bounds, multipliers)
    scale = functools.reduce(math.lcm, (m.denominator for m in multipliers), 1)
    atoms = {}

    def expr(n):
        kind, args = graph.kind(n), graph.arguments(n)
        z3 = exporter.z3
        if kind == z3.Z3_OP_ANUM:
            k = Fraction(graph.decl(n).name)
            if k.denominator != 1:
                raise ValueError("non-integer Int numeral")
            return f"(.num ({int(k)}))"
        if kind in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL):
            op = {z3.Z3_OP_ADD: 'add', z3.Z3_OP_SUB: 'sub', z3.Z3_OP_MUL: 'mul'}[kind]
            return functools.reduce(lambda a, b: f"(.{op} {a} {b})", map(expr, args))
        if kind == z3.Z3_OP_UMINUS:
            return f"(.neg {expr(args[0])})"
        index = atoms.setdefault(n, len(atoms))
        return f"(.var {index})"

    def term_id(text):
        match = re.fullmatch(r"\(term_(\d+) _atoms _vars\)", text)
        if not match:
            raise ValueError("prototype supports the pure Int fragment only")
        return int(match[1])

    summands = []
    for bound, multiplier in zip(bounds, multipliers):
        if not multiplier:
            continue
        lower, upper, tightened = bound[:3]
        if multiplier < 0:
            lower, upper, multiplier = upper, lower, -multiplier
        lower, upper = expr(term_id(lower)), expr(term_id(upper))
        if tightened:
            lower = f"(.add {lower} (.num 1))"
        summands.append(f"(.mul (.num {int(multiplier * scale)}) (.sub {upper} {lower}))")

    def balanced(items):
        if len(items) == 1:
            return items[0]
        middle = (len(items) + 1) // 2
        return f"(.add {balanced(items[:middle])} {balanced(items[middle:])})"

    data = balanced(summands)
    values = [exporter._term(graph, atom) for atom in atoms]

    def context(items, offset=0):
        if len(items) == 1:
            return f"(Lean.RArray.leaf {items[0]})"
        if not items:
            return "(Lean.RArray.leaf (0 : Int))"
        middle = (len(items) + 1) // 2
        return f"(Lean.RArray.branch {offset + middle} {context(items[:middle], offset)} {context(items[middle:], offset + middle)})"

    lines[0] = (f"have _sum : {combination} = (({total} : Int)) := by "
                f"exact Z3Certificate.IntFarkas.constant_eq {context(values)} {data} ({total}) rfl")
    selected.append(node)
    return lines


AUDIT = r'''
open Lean Elab Command in
elab "#uses_reflected_identity " n:ident : command => do
  let root ← resolveGlobalConstNoOverload n
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let next ← liftTermElabM do
      let info ← getConstInfo name
      return (info.value? (allowOpaque := true)).map (·.getUsedConstants)
    if let some next := next then todo := todo ++ next
  unless seen.contains ``Z3Certificate.IntFarkas.constant_eq do
    throwError "reflected identity fell back to a tactic: {root}"
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--repeat', type=int, default=3)
    p.add_argument('--limit', type=int, default=120)
    p.add_argument('inputs', type=Path, nargs='+')
    a = p.parse_args()
    upstream, out = a.upstream.resolve(), a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(upstream / 'examples/python'))
    import proof_certificate as producer
    import proof_to_lean as exporter
    project = out / 'lean'
    (project / 'Z3Certificate').mkdir(parents=True, exist_ok=True)
    core = ROOT / 'Blaster/Reconstruct/Certificate/IntFarkas.lean'
    shutil.copyfile(core, project / 'Z3Certificate/IntFarkas.lean')
    shutil.copyfile(upstream / 'lean/lean-toolchain', project / 'lean-toolchain')
    (project / 'lakefile.toml').write_text('name = "certificate_experiment"\ndefaultTargets = ["Z3Certificate"]\n[[lean_lib]]\nname = "Z3Certificate"\n')
    (project / 'Z3Certificate.lean').write_text('import Z3Certificate.IntFarkas\n')
    subprocess.run(['lake', 'build', 'Z3Certificate'], cwd=project, check=True)
    metadata = dict(z3=producer.z3.get_full_version(),
        toolchain=(project / 'lean-toolchain').read_text().strip(),
        core_sha256=hashlib.sha256(core.read_bytes()).hexdigest(),
        exporter_sha256=hashlib.sha256((upstream / 'examples/python/proof_to_lean.py').read_bytes()).hexdigest(),
        reference_upstream='708879ef23599153d4f0adb3af58fb514e2c8942',
        producer_sha256=hashlib.sha256((upstream / 'examples/python/proof_certificate.py').read_bytes()).hexdigest(),
        process_limit_s=a.limit, repeat=a.repeat, platform=platform.platform())
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    original = exporter._farkas_combination
    rows = []
    for path in a.inputs:
        source = path.read_text()
        certificate = producer.export_certificate(source, timeout=30, memory=8192)
        (out / (path.stem + '.json')).write_text(json.dumps(certificate, indent=2) + '\n')
        variants = {}
        for variant in ['official', 'reflected']:
            selected = []
            exporter._farkas_combination = (original if variant == 'official' else
                lambda graph, node: reflected(exporter, original, selected, graph, node))
            text = exporter.reconstruct(source, certificate)
            namespace = re.search(r'^namespace (\S+)', text, re.M)[1]
            theorem = re.findall(r'^theorem (\S+)', text, re.M)[-1]
            text = text.replace('import Init', 'import Lean\nimport Z3Certificate.IntFarkas', 1)
            text += AUDIT
            text += ''.join(f'\n#uses_reflected_identity {namespace}.th_lemma_{n}\n' for n in selected)
            text += f'\n#print axioms {namespace}.{theorem}\n'
            file = project / f'{path.stem}_{variant}.lean'
            file.write_text(text)
            variants[variant] = (file, len(selected))
        for repetition in range(1, a.repeat + 1):
            order = ['official', 'reflected'] if repetition % 2 else ['reflected', 'official']
            for variant in order:
                file, count = variants[variant]
                log = out / f'{file.stem}-{repetition}.log'
                olean = file.with_suffix('.olean')
                cmd = ['/usr/bin/time', '-l' if platform.system() == 'Darwin' else '-v',
                       'lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true',
                       '--memory=8192', '-o', str(olean), str(file)]
                env = dict(os.environ, LEAN_NUM_THREADS='2')
                start = time.monotonic()
                with log.open('w') as stream:
                    proc = subprocess.Popen(cmd, cwd=project, env=env, stdout=stream,
                        stderr=subprocess.STDOUT, start_new_session=True)
                    timed_out = False
                    try:
                        proc.wait(timeout=a.limit)
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                text = log.read_text(errors='replace')
                match = re.search(r'depends on axioms:\s*\[([^\]]*)\]', text)
                audited = match is not None or 'does not depend on any axioms' in text
                axioms = {x.strip() for x in match[1].split(',') if x.strip()} if match else set()
                passed = proc.returncode == 0 and audited and axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
                rss = re.search(r'(\d+)\s+maximum resident set size', text)
                row = dict(case=path.stem, variant=variant, repetition=repetition,
                    status='timeout' if timed_out else 'passed' if passed else 'failed',
                    wall_s=round(time.monotonic()-start, 3), reflected_steps=count,
                    peak_rss_bytes=int(rss[1]) if rss else None,
                    source_bytes=file.stat().st_size, olean_bytes=olean.stat().st_size if passed else None)
                rows.append(row)
                (out / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
                print(row, flush=True)


if __name__ == '__main__':
    main()
