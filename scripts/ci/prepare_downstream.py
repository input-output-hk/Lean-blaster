#!/usr/bin/env python3
"""Overlay exact dependency revisions in a disposable downstream checkout."""
import argparse
import json
from pathlib import Path
import re


def full_sha(value):
    if not re.fullmatch(r'[0-9a-fA-F]{40}', value):
        raise ValueError('A full 40-character commit SHA is required')
    return value.lower()


def replace_dependency(source, package, repository, revision):
    # Match the exact known Git dependency, not comments or similarly named packages.
    pattern = (r'(?m)^(\s*require ' + re.escape(package) + r' from git "https://github\.com/'
               + re.escape(repository) + r'(?:\.git)?" @ )"[^"]+"')
    changed, count = re.subn(pattern, lambda match: match[1] + '"' + full_sha(revision) + '"', source)
    if count != 1:
        raise ValueError(f'Expected one explicit {package} dependency; found {count}')
    return changed


def verify_manifest(manifest, expected):
    packages = {p['name']: p for p in manifest['packages']}
    for name, sha in expected.items():
        if packages.get(name, {}).get('rev') != full_sha(sha):
            raise ValueError(f'{name} did not resolve to the requested commit')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blaster', required=True, type=full_sha)
    parser.add_argument('--plutus', type=full_sha)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    expected = {'Blaster': args.blaster}
    if args.plutus:
        expected['PlutusCore'] = args.plutus
    if args.verify:
        verify_manifest(json.loads(Path('lake-manifest.json').read_text()), expected)
    else:
        path = Path('lakefile.lean')
        source = replace_dependency(path.read_text(), 'Blaster', 'input-output-hk/Lean-blaster', args.blaster)
        if args.plutus:
            source = replace_dependency(source, 'PlutusCore', 'input-output-hk/PlutusCoreBlaster', args.plutus)
        path.write_text(source)


if __name__ == '__main__':
    main()
