#!/usr/bin/env python3
"""Typprüft die drei `Suggested.lean` des Worktrees gegen das fertig gebaute
Mathlib v4.33.1 des Hauptcheckouts und zählt Fehler und `sorry`.

Der Hauptcheckout wird nur gelesen: `lake env lean` baut nichts und legt dort
nichts an.  Statt `cd` wird `lake --dir=…` benutzt — das ist die Form, die ohne
Unterschale auskommt.

    python3 scripts/check_suggested.py   -> scripts/_citations/lean_check.md
"""
import os, subprocess

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

JOURNAL = '/home/pfaffelh/Code/lean/journal'
BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
OUT = 'scripts/_citations'
FILES = ['MartingaleProblems', 'SkorokhodSpace', 'WeakConvergence']

os.makedirs(OUT, exist_ok=True)
ver = subprocess.run(['lean', '--version'], capture_output=True, text=True).stdout.strip()
rows = [f'# `lake env lean` gegen {ver}', '', '| Datei | rc | Fehler | `sorry` |', '| --- | --- | --- | --- |']
detail = []
for f in FILES:
    path = os.path.abspath(f'{BASE}/{f}/Suggested.lean')
    r = subprocess.run(['lake', f'--dir={JOURNAL}', 'env', 'lean', path],
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    # Lean meldet auch getaggte Fehler, `error(lean.dependsOnNoncomputable):`
    # etwa; ein Filter auf `error:` allein übersieht sie.
    errs = [l for l in out.splitlines() if 'error:' in l or 'error(' in l]
    sorries = [l for l in out.splitlines() if 'declaration uses' in l and 'sorry' in l]
    rows.append(f'| `{f}/Suggested.lean` | {r.returncode} | {len(errs)} | {len(sorries)} |')
    if errs:
        detail += [f'', f'## Fehler in `{f}/Suggested.lean`', ''] + [f'* `{e}`' for e in errs]

open(f'{OUT}/lean_check.md', 'w').write('\n'.join(rows + detail) + '\n')
print('\n'.join(rows + detail))
