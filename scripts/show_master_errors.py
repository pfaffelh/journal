#!/usr/bin/env python3
"""Zeigt die Fehlermeldungen eines `check_master.py`-Durchlaufs ungekürzt.

    python3 scripts/show_master_errors.py <Datei> [erste] [letzte]

`<Datei>` ist einer der drei Namen `WeakConvergence`, `SkorokhodSpace`,
`MartingaleProblems`; die Ausgabe liest `scripts/_citations/master_<Datei>.out`.
Mit `erste`/`letzte` wird auf die Meldungen in diesem Zeilenbereich der
`Suggested.lean` eingeschränkt -- nützlich, um eine Fehlerfamilie einzeln
anzusehen, ohne die Meldung zu beschneiden.
"""
import os, re, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
name = sys.argv[1] if len(sys.argv) > 1 else 'WeakConvergence'
lo = int(sys.argv[2]) if len(sys.argv) > 2 else 0
hi = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9

path = os.path.join(HERE, 'scripts/_citations', f'master_{name}.out')
text = open(path).read()
parts = re.split(r'(?m)^(?=\S*Suggested\.lean:\d+:\d+: )', text)
for p in parts:
    head = p.split('\n', 1)[0]
    m = re.match(r'\S*Suggested\.lean:(\d+):\d+: (\w+)', head)
    if not m or not m.group(2).startswith('error'):
        continue
    if lo <= int(m.group(1)) <= hi:
        print(p.rstrip())
        print('-' * 70)
