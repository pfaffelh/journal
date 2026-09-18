#!/usr/bin/env python3
"""Gruppiert die Fehlermeldungen eines `check_master.py`-Durchlaufs nach dem
Kopf der Anwendung, in der sie auftreten -- also nach dem Mathlib-Namen, dessen
Signatur sich geändert hat.

    python3 scripts/master_error_families.py <Datei>

Das ist eine Lesehilfe und keine Prüfung: maßgeblich bleibt
`scripts/_citations/lean_check_master.md`.
"""
import collections, os, re, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
name = sys.argv[1] if len(sys.argv) > 1 else 'MartingaleProblems'
text = open(os.path.join(HERE, 'scripts/_citations', f'master_{name}.out')).read()

fam = collections.defaultdict(list)
for p in re.split(r'(?m)^(?=\S*Suggested\.lean:\d+:\d+: )', text):
    head = p.split('\n', 1)[0]
    m = re.match(r'\S*Suggested\.lean:(\d+):\d+: (\w+)', head)
    if not m or not m.group(2).startswith('error'):
        continue
    line = int(m.group(1))
    app = re.search(r'(?m)^in the application\n\s*(\S+)', p)
    if app:
        key = app.group(1)
    else:
        key = re.sub(r'`[^`]*`', '`…`', head.split('error', 1)[1])[:70]
    fam[key].append(line)

for k, v in sorted(fam.items(), key=lambda kv: -len(kv[1])):
    print(f'{len(v):3d}  {k}')
    print(f'     {v}')
