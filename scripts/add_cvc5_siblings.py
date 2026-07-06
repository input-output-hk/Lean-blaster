#!/usr/bin/env python3
"""Add a `(solver: cvc5)` sibling after every backend-reaching test invocation.

For each `#blaster` / `#bmc` / `#kind` invocation under the given roots:
  - skip when its options contain `only-smt-lib: 1`, `only-optimize: 1`,
    or an explicit `solver:` (no backend reached / already covered);
  - skip when the invocation is wrapped in `#guard_msgs` (its expected
    messages are Z3 baselines — handled manually);
  - otherwise, duplicate the whole invocation right below it, inserting
    `(solver: cvc5)` after the command keyword.

Usage: python3 scripts/add_cvc5_siblings.py [--dry-run] [roots...]
"""
import re
import sys
import pathlib

CMD = re.compile(r'^(\s*)#(blaster|bmc|kind)\b')


def find_invocation_end(lines, i):
    """Index (inclusive) of the line closing the invocation's `[...]` term."""
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


def process(path, dry):
    lines = path.read_text(encoding='utf-8').splitlines(keepends=True)
    out, i, changed = [], 0, 0
    while i < len(lines):
        line = lines[i]
        m = CMD.match(line)
        prev = out[-1].strip() if out else ''
        if not m or prev.startswith('#guard_msgs'):
            out.append(line)
            i += 1
            continue
        j = find_invocation_end(lines, i)
        block = lines[i:j + 1]
        text = ''.join(block)
        out.extend(block)
        if ('only-smt-lib: 1' not in text and 'only-optimize: 1' not in text
                and 'solver:' not in text):
            sib = text.replace(f'#{m.group(2)}', f'#{m.group(2)} (solver: cvc5)', 1)
            if not sib.endswith('\n'):
                sib += '\n'
            out.append(sib)
            changed += 1
        i = j + 1
    if changed and not dry:
        path.write_text(''.join(out), encoding='utf-8')
    return changed


def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    roots = [a for a in args if not a.startswith('--')] or ['Tests']
    total = 0
    for root in roots:
        for p in sorted(pathlib.Path(root).rglob('*.lean')):
            n = process(p, dry)
            if n:
                print(f'{p}: {n} sibling(s)')
                total += n
    print(f'total: {total} sibling(s){" (dry run)" if dry else ""}')


if __name__ == '__main__':
    main()
