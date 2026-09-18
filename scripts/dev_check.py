#!/usr/bin/env python3
"""Typprüft `scratch/dev.lean` gegen die bereits von `check_suggested.py`
gebauten `.olean` unter `scratch/_lean`.

Das ist ein **Entwicklungswerkzeug**, kein Ersatz für `check_suggested.py`:
es prüft eine Arbeitsdatei, die die drei Roadmaps importiert, damit ein Lauf
nicht für jede Zwischenfassung die ganze `MartingaleProblems/Suggested.lean`
neu übersetzen muß.  Die verbindliche Prüfung bleibt `check_suggested.py`,
und sie übersetzt weiterhin jede Datei ganz und ungefiltert.

Aufruf: `python3 scripts/dev_check.py <datei.lean>`.  Die Datei wird verlangt
und nicht erraten, damit das Skript auf nichts Ungeschriebenes zeigt.

Voraussetzung: `check_suggested.py` ist in diesem Lauf schon einmal gelaufen,
so daß `scratch/_lean/TauCetiRoadmap/*/Suggested.olean` existieren; sonst
scheitert `lean` an einem unbekannten Modul und sagt das.
"""
import os, subprocess, sys

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

JOURNAL = '/home/pfaffelh/Code/lean/journal'
BUILD = os.path.abspath('scratch/_lean')
if len(sys.argv) != 2:
    raise SystemExit('Aufruf: python3 scripts/dev_check.py <datei.lean>')
SRC = os.path.abspath(sys.argv[1])

shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
         f'-DautoImplicit=false -DrelaxedAutoImplicit=false {SRC}')
r = subprocess.run(['lake', f'--dir={JOURNAL}', 'env', 'sh', '-c', shell],
                   capture_output=True, text=True)
out = r.stdout + r.stderr
print(out)
print(f'rc={r.returncode}')
