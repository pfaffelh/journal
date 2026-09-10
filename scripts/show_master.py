#!/usr/bin/env python3
"""Zeigt Kontextzeilen aus `upstream/master` (oder aus dem v4.33.1-Release),
ohne etwas auszuchecken.

    python3 scripts/show_master.py Mathlib/Foo/Bar.lean:120 [±n] [--v4331]
"""
import subprocess, sys, os

MATHLIB4 = '/home/pfaffelh/Code/lean/mathlib4'
V4331 = '/home/pfaffelh/Code/lean/journal/.lake/packages/mathlib'

args = [a for a in sys.argv[1:] if a != '--v4331']
use_v = '--v4331' in sys.argv
ctx = 5
specs = []
for a in args:
    if a.isdigit():
        ctx = int(a)
    else:
        specs.append(a)

for spec in specs:
    path, _, no = spec.partition(':')
    no = int(no or 1)
    if use_v:
        text = open(os.path.join(V4331, path)).read()
    else:
        text = subprocess.run(['git', '-C', MATHLIB4, 'show', f'upstream/master:{path}'],
                              capture_output=True, text=True).stdout
    lines = text.splitlines()
    print(f'=== {"v4.33.1" if use_v else "master"} {path}:{no}')
    for i in range(max(0, no - 1 - ctx), min(len(lines), no + ctx)):
        print(f'{i+1:6d}  {lines[i]}')
    print()
