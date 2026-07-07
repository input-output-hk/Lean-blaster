#!/usr/bin/env python3
"""Merge adjacent z3/cvc5 test invocation pairs into single (solver: all) calls.

For each `#blaster`/`#bmc`/`#kind` invocation without a `solver:` option that
is immediately followed by its `(solver: cvc5)` sibling on the same term:
  - replace both with one invocation carrying `(solver: all)`;
  - a differing `solve-result` resolves to the definitive expectation
    (0/1 win over 2);
  - a sibling-only `(timeout: n)` is kept on the merged invocation;
  - `#guard_msgs`-wrapped blocks are skipped (separate per-solver baselines).

Usage: python3 scripts/merge_solver_all.py [--dry-run] [roots...]
"""
import re
import sys
import pathlib

CMD = re.compile(r'^(\s*)#(blaster|bmc|kind)\b')
OPT = re.compile(r'\((\w[\w-]*):\s*([^)]*)\)')

SKIP_FILES = {"SmtSolverSelection.lean"}


def find_invocation_end(lines, i):
    depth = 0
    seen_open = False
    for j in range(i, len(lines)):
        for ch in lines[j]:
            if ch == '[':
                depth += 1
                seen_open = True
            elif ch == ']':
                depth -= 1
        if seen_open and depth <= 0:
            return j
    raise ValueError(f"unbalanced brackets from line {i + 1}")


def parse_invocation(text, cmd):
    """Split an invocation into (options dict/order, term text)."""
    head, _, _ = text.partition('[')
    opts = OPT.findall(head)
    term_start = text.index('[')
    term = text[term_start:]
    return opts, term.strip()


def merged_invocation(a_text, cmd, a_opts, b_opts):
    """Build the merged (solver: all) invocation from the z3 original text."""
    new = a_text.replace(f'#{cmd}', f'#{cmd} (solver: all)', 1)
    a_d = dict(a_opts)
    b_d = {k: v for k, v in b_opts if k != 'solver'}
    # resolve solve-result: definitive expectation wins over 2
    a_sr, b_sr = a_d.get('solve-result', '0').strip(), b_d.get('solve-result', '0').strip()
    if a_sr != b_sr:
        resolved = a_sr if a_sr in ('0', '1') else b_sr
        if a_d.get('solve-result') is not None:
            new = re.sub(r'\(solve-result:\s*[^)]*\)', f'(solve-result: {resolved})', new, count=1)
        elif resolved != '0':
            new = new.replace('(solver: all)', f'(solver: all) (solve-result: {resolved})', 1)
    # keep the sibling's timeout (it exists to cap cvc5)
    if 'timeout' in b_d:
        if 'timeout' in a_d:
            if a_d['timeout'].strip() != b_d['timeout'].strip():
                new = re.sub(r'\(timeout:\s*[^)]*\)', f"(timeout: {b_d['timeout'].strip()})", new, count=1)
        else:
            new = new.replace('(solver: all)', f"(solver: all) (timeout: {b_d['timeout'].strip()})", 1)
    return new


def process(path, dry):
    lines = path.read_text(encoding='utf-8').splitlines(keepends=True)
    out, i, merged, flagged = [], 0, 0, []
    while i < len(lines):
        m = CMD.match(lines[i])
        prev = out[-1].strip() if out else ''
        if not m or prev.startswith('#guard_msgs'):
            out.append(lines[i])
            i += 1
            continue
        j = find_invocation_end(lines, i)
        a_text = ''.join(lines[i:j + 1])
        cmd = m.group(2)
        a_opts, a_term = parse_invocation(a_text, cmd)
        # a merge candidate must not already select a solver
        if any(k == 'solver' for k, _ in a_opts) or j + 1 >= len(lines):
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        # look at the immediately following invocation
        k = j + 1
        m2 = CMD.match(lines[k]) if k < len(lines) else None
        if not m2 or m2.group(2) != cmd:
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        j2 = find_invocation_end(lines, k)
        b_text = ''.join(lines[k:j2 + 1])
        b_opts, b_term = parse_invocation(b_text, cmd)
        b_d = dict(b_opts)
        if b_d.get('solver', '').strip() != 'cvc5' or b_term != a_term:
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        # sanity: conflicting definitive expectations are never auto-merged
        a_sr = dict(a_opts).get('solve-result', '0').strip()
        b_sr = b_d.get('solve-result', '0').strip()
        if a_sr in ('0', '1') and b_sr in ('0', '1') and a_sr != b_sr:
            flagged.append(f'{path}:{i + 1} conflicting expectations {a_sr} vs {b_sr}')
            out.extend(lines[i:j2 + 1])
            i = j2 + 1
            continue
        new = merged_invocation(a_text, cmd, a_opts, b_opts)
        if not new.endswith('\n'):
            new += '\n'
        out.append(new)
        merged += 1
        i = j2 + 1
    if merged and not dry:
        path.write_text(''.join(out), encoding='utf-8')
    return merged, flagged


def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    roots = [a for a in args if not a.startswith('--')] or ['Tests']
    total = 0
    all_flags = []
    for root in roots:
        for p in sorted(pathlib.Path(root).rglob('*.lean')):
            if p.name in SKIP_FILES:
                continue
            n, flags = process(p, dry)
            all_flags.extend(flags)
            if n:
                print(f'{p}: {n} pair(s) merged')
                total += n
    for f in all_flags:
        print(f'FLAGGED (not merged): {f}')
    print(f'total: {total} pair(s) merged{" (dry run)" if dry else ""}')


if __name__ == '__main__':
    main()
