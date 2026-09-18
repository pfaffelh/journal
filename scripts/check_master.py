#!/usr/bin/env python3
"""Typprüft die drei `Suggested.lean` gegen Mathlib **`upstream/master`**, in
Abhängigkeitsordnung, und zählt Fehler, `sorry`, Warnungen und darunter eigens
die **veralteten Namen**.

## Warum die Veraltungen eine eigene Spalte haben

Am 2026-09-17 standen 37 Aufrufe von `Set.mem_setOf_eq` in den Dateien, das seit
dem 2026-07-09 **auch auf v4.33.1** veraltet ist; `check_suggested.py` zählt nur
Fehler und war dafür blind.  Bei 514 Warnungen findet niemand die eine, die
zählt.  Die Spalte macht die Zahl sichtbar, und der Anhang nennt die Namen.

    python3 scripts/check_master.py [pfad-zum-master-worktree]

Voreinstellung ist `~/Code/lean/mathlib-master`, ein Worktree von
`~/Code/lean/mathlib4` auf `upstream/master`, mit gezogenem Mathlib-Cache
(`lake exe cache get`, rund 6,7 GB).  Frischer Stand:

    git -C ~/Code/lean/mathlib4 fetch upstream master
    git -C ~/Code/lean/mathlib-master checkout --detach upstream/master
    cd ~/Code/lean/mathlib-master && lake exe cache get

## Warum die Quellen kopiert werden

`lean` verlangt, daß die Eingabedatei unterhalb des Wurzelverzeichnisses liegt.
Die drei Dateien werden deshalb nach `<worktree>/TauCetiRoadmap/<Name>/` kopiert
-- was zugleich die Lage im Zielrepositorium ist.  Und der Unterprozeß läuft mit
`cwd` im Worktree, weil `elan` die Lean-Version am Arbeitsverzeichnis wählt: von
woanders aus nimmt es v4.33.1 und meldet `incompatible header`.

## Was die Prüfung nicht tut

Sie filtert nicht und schneidet nicht ab.  `| head -N` ist verboten: ein
abgeschnittener Durchlauf sieht wie ein fehlerfreier aus.
"""
import collections, os, re, shutil, subprocess, sys, time

MW = os.path.abspath(sys.argv[1] if len(sys.argv) > 1
                     else os.path.expanduser('~/Code/lean/mathlib-master'))
# Das Repositorium, in dem *dieses Skript* liegt -- nicht der Hauptcheckout.
# Ein Lauf arbeitet in einem Worktree, und geprüft gehören seine Quellen, nicht
# die von `master`; ebenso wird der Bericht dorthin geschrieben, wo er committet
# wird.
JOURNAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASE = os.path.join(JOURNAL, 'Journal/Blog/MartingaleProblem/TauCeti')
OUT = os.path.join(JOURNAL, 'scripts/_citations')
PREFIX = 'TauCetiRoadmap'
SRCDIR = os.path.join(MW, PREFIX)
BUILD = os.path.join(MW, '_lean_master')
FILES = ['WeakConvergence', 'SkorokhodSpace', 'MartingaleProblems']

os.makedirs(OUT, exist_ok=True)
shutil.rmtree(BUILD, ignore_errors=True)
shutil.rmtree(SRCDIR, ignore_errors=True)
for f in FILES:
    os.makedirs(os.path.join(SRCDIR, f), exist_ok=True)
    shutil.copy(os.path.join(BASE, f, 'Suggested.lean'),
                os.path.join(SRCDIR, f, 'Suggested.lean'))

ver = subprocess.run(['lean', '--version'], capture_output=True, text=True,
                     cwd=MW).stdout.strip()
commit = subprocess.run(['git', '-C', MW, 'log', '-1', '--format=%H %ad',
                         '--date=short'], capture_output=True, text=True).stdout.strip()
rows = [f'# `lake env lean` gegen Mathlib `upstream/master`', '',
        f'* Mathlib: `{commit}`', f'* {ver}', '',
        '| Datei | rc | Fehler | `sorry` | Warnungen | davon veraltet | Sekunden |',
        '| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
detail = []
deprecated = {}

# Eine Warnung ist eine Zeile der Gestalt `<datei>:<zeile>:<spalte>: warning: …`.
# Auf das bloße Vorkommen von `warning:` zu prüfen, zählt zu viel: der Hinweis
# des Linters für ungenutzte Bindungen endet mit den Worten „to silence this
# warning:" und wurde bis zum 2026-09-18 als eigene Warnung mitgezählt -- 22 von
# den 536 des ersten master-Durchlaufs waren solche Fortsetzungszeilen.
WARN = re.compile(r':\d+:\d+: warning: (.*)$')

for f in FILES:
    src = os.path.join(SRCDIR, f, 'Suggested.lean')
    olean = os.path.join(BUILD, PREFIX, f, 'Suggested.olean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
             f'-DautoImplicit=false -DrelaxedAutoImplicit=false -o {olean} {src}')
    t0 = time.time()
    r = subprocess.run(['lake', 'env', 'sh', '-c', shell],
                       capture_output=True, text=True, cwd=MW)
    secs = round(time.time() - t0)
    out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if 'error:' in l or 'error(' in l]
    sorries = [l for l in out.splitlines() if 'declaration uses' in l and 'sorry' in l]
    warns = [m.group(1) for m in map(WARN.search, out.splitlines()) if m]
    deps = [w for w in warns if 'has been deprecated' in w]
    deprecated[f] = deps
    rows.append(f'| `{f}` | {r.returncode} | {len(errs)} | {len(sorries)} | '
                f'{len(warns)} | {len(deps)} | {secs} |')
    if errs:
        detail += ['', f'## Fehler in `{f}`', ''] + [f'* `{e.split("Suggested.lean:")[-1][:200]}`'
                                                     for e in errs]
    if not os.path.exists(olean):
        detail += ['', f'## Keine `.olean` für `{f}`', '',
                   '* die folgenden Dateien der Kette sind damit **nicht geprüft**']
    with open(os.path.join(OUT, f'master_{f}.out'), 'w') as fh:
        fh.write(out)

flat = [w for f in FILES for w in deprecated.get(f, [])]
if flat:
    detail += ['', '## Veraltete Namen, nach Häufigkeit', '']
    for w, n in collections.Counter(flat).most_common():
        detail.append(f'* {n}× {w}')

text = '\n'.join(rows + detail) + '\n'
with open(os.path.join(OUT, 'lean_check_master.md'), 'w') as fh:
    fh.write(text)
print(text)
