#!/usr/bin/env python3
"""Install a selected tc-solvers adapter set into a Goblint checkout."""
import argparse
from datetime import datetime, timezone
from pathlib import Path
import shutil
import subprocess

FILES = ('slrtc_simple.ml', 'slrtc_restarting.ml', 'slrtc_narrowing_fixed_point.ml',
         'slrtc_update.ml', 'slrtc_nfp_update.ml', 'slrtc_register.ml')


def install(analyzer, generated):
    analyzer = analyzer.resolve()
    target = analyzer / 'src/solver'
    if not (target / 'selector.ml').is_file():
        raise ValueError('Expected a Goblint checkout with src/solver/selector.ml')
    for name in FILES:
        if not (generated / name).is_file():
            raise ValueError(f'Missing {name}; run make goblint-solvers')
    for name in FILES[:3]:
        header = (generated / name).read_text().splitlines()[:8]
        if not any('Rank worklist: bitmap' in x or 'bitmap worklist' in x for x in header):
            raise ValueError(f'{name} must use the bitmap backend for the paper registrations')
    git_dir = Path(subprocess.check_output(
        ['git', '-C', str(analyzer), 'rev-parse', '--absolute-git-dir'], text=True).strip())
    backup = git_dir / 'tc-solvers-backups' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    backup.mkdir(parents=True)
    for name in FILES:
        dest = target / name
        if dest.exists():
            shutil.copy2(dest, backup / name)
        shutil.copy2(generated / name, dest)
    return backup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('analyzer', type=Path)
    parser.add_argument('--set', choices=['slr-paper'], default='slr-paper',
                        help='Registration set to install (default: slr-paper)')
    args = parser.parse_args()
    try:
        backup = install(args.analyzer, Path(__file__).resolve().parent / 'generated')
    except ValueError as error:
        parser.error(str(error))
    print('Installed slrtc_s, slrtc_r, slrtc_rs, slrtc_rd, slrtc_rds, slrtc_n')
    print(f'Previous files: {backup}')
    print('Rebuild Goblint with make release in its checkout.')


if __name__ == '__main__':
    main()
