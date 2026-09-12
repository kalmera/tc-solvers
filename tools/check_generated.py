"""Fail if regeneration differs from the committed generated sources."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
paths = ['ocaml/extracted', 'ocaml/adapters/goblint/generated', 'ocaml/library/generated']
status = subprocess.check_output(
    ['git', 'status', '--porcelain', '--untracked-files=all', '--', *paths], cwd=root, text=True)
if status:
    raise SystemExit('Generated sources differ; run make regenerate and commit them:\n' + status)
print('Generated sources match the committed snapshot.')
