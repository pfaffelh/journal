#!/usr/bin/env python3
"""Typprüft eine **Arbeitsdatei** gegen die von `check_master.py` schon
gebauten `.olean` im master-Worktree.

Das ist zu `check_master.py`, was `dev_check.py` zu `check_suggested.py` ist:
ein Entwicklungswerkzeug, kein Ersatz.  Eine Datei, die
`TauCetiRoadmap.SkorokhodSpace.Suggested` importiert, übersetzt in Sekunden,
während der ganze Durchlauf der Kette rund zwei Minuten braucht; wer eine neue
Deklaration schreibt, probiert sie hier und hängt sie erst danach in die
Roadmap.  **Verbindlich bleibt `check_master.py`**, ungefiltert und über die
ganze Datei.

    python3 scripts/dev_check_master.py <datei.lean> [pfad-zum-master-worktree]

Voraussetzung: `check_master.py` ist in diesem Lauf schon einmal gelaufen, so
daß `<worktree>/_lean_master/TauCetiRoadmap/*/Suggested.olean` existieren.
Fehlen sie, so scheitert `lean` an einem unbekannten Modul und sagt das --- das
Skript rät nicht und baut nichts nach.

Die Quelle wird nach `<worktree>/TauCetiRoadmap/_Dev.lean` kopiert, weil `lean`
verlangt, daß die Eingabedatei unterhalb des Wurzelverzeichnisses liegt, und
der Unterprozeß läuft mit `cwd` im Worktree, weil `elan` die Lean-Version am
Arbeitsverzeichnis wählt.
"""
import os, shutil, subprocess, sys

if len(sys.argv) not in (2, 3):
    raise SystemExit('Aufruf: python3 scripts/dev_check_master.py <datei.lean> '
                     '[pfad-zum-master-worktree]')

SRC = os.path.abspath(sys.argv[1])
MW = os.path.abspath(sys.argv[2] if len(sys.argv) > 2
                     else os.path.expanduser('~/Code/lean/mathlib-master'))
BUILD = os.path.join(MW, '_lean_master')
DEST = os.path.join(MW, 'TauCetiRoadmap', '_Dev.lean')

if not os.path.isdir(BUILD):
    raise SystemExit(f'{BUILD} fehlt -- erst `python3 scripts/check_master.py` laufen lassen.')

os.makedirs(os.path.dirname(DEST), exist_ok=True)
if os.path.abspath(SRC) != os.path.abspath(DEST):
    shutil.copy(SRC, DEST)

shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
         f'-DautoImplicit=false -DrelaxedAutoImplicit=false {DEST}')
r = subprocess.run(['lake', 'env', 'sh', '-c', shell],
                   capture_output=True, text=True, cwd=MW)
print(r.stdout + r.stderr)
print(f'rc={r.returncode}')
sys.exit(r.returncode)
