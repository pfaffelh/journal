#!/usr/bin/env python3
"""Extrahiert aus den vier Tau-Ceti-Roadmaps und den drei `Suggested.lean` alle
zitierten Mathlib-Dateipfade und alle in Backticks stehenden Bezeichner, die
nicht in den `Suggested.lean` selbst deklariert sind.

Ausgabe: `scripts/_citations/{own,cands,paths}.json`.  Das Skript ist allein
lauffähig und schreibt nur unter `scripts/_citations/`.
"""
import re, os, json

# Alle Pfade relativ zur Wurzel des Worktrees, damit das Skript aus jedem
# Verzeichnis heraus lauffähig ist.
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
OUT = 'scripts/_citations'
DIRS = ['KolmogorovExtension', 'MartingaleProblems', 'SkorokhodSpace', 'WeakConvergence']

files = []
for d in DIRS:
    for f in ['README.md', 'Suggested.lean']:
        p = os.path.join(BASE, d, f)
        if os.path.exists(p):
            files.append(p)

declkw = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)")

own = set()
for p in files:
    if not p.endswith('.lean'):
        continue
    for line in open(p):
        m = declkw.match(line)
        if m:
            own.add(m.group(2))
            own.add(m.group(2).split('.')[-1])

tok = re.compile(r'`([^`\n]+)`')
ident = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_'][A-Za-z0-9_'!?]*)*$")

cands, paths = {}, {}
for p in files:
    for i, line in enumerate(open(p), 1):
        for fp in re.findall(r'Mathlib/[A-Za-z0-9_/]+\.lean', line):
            paths.setdefault(fp, []).append(f'{p}:{i}')
        for t in tok.findall(line):
            t = t.strip()
            if t.startswith('Mathlib/') or not ident.match(t):
                continue
            if t in own or t.split('.')[-1] in own:
                continue
            cands.setdefault(t, []).append(f'{p}:{i}')

os.makedirs(OUT, exist_ok=True)
json.dump(sorted(own), open(f'{OUT}/own.json', 'w'), indent=0)
json.dump(cands, open(f'{OUT}/cands.json', 'w'), indent=0)
json.dump(paths, open(f'{OUT}/paths.json', 'w'), indent=0)
print('own decls:', len(own), '| cand tokens:', len(cands), '| paths:', len(paths))
