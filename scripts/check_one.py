#!/usr/bin/env python3
"""Typprüft **eine** `Suggested.lean` gegen Mathlib `upstream/master`, ohne die
Kette davor neu zu bauen.

    python3 scripts/check_one.py SkorokhodSpace [pfad-zum-master-worktree]

Das ist das Werkzeug für das Arbeiten *an* einer Datei: `check_master.py` baut
alle drei in Abhängigkeitsordnung und braucht dafür rund zwei Minuten, während
eine einzelne Datei in Sekunden übersetzt.  Es setzt voraus, daß die `.olean`
der Abhängigkeiten aus einem früheren Lauf von `check_master.py` noch unter
`<worktree>/_lean_master` liegen; fehlen sie, so sagt es das und bricht ab,
statt eine ungeprüfte Datei für geprüft auszugeben.

**Es ersetzt `check_master.py` nicht.**  Es schreibt keine `.olean`, also sieht
der Verbraucher einer Datei die Änderung nicht, und es schreibt keinen Bericht.
Am Ende eines Laufs steht `check_master.py`, ungefiltert und über alle drei.

Wie dort gilt: nicht filtern, nicht abschneiden, kein `| head -N`.
"""
import os, re, shutil, subprocess, sys, time

FILES = ['WeakConvergence', 'SkorokhodSpace', 'MartingaleProblems']

if len(sys.argv) < 2 or sys.argv[1] not in FILES:
    print(f'Aufruf: check_one.py {{{"|".join(FILES)}}} [worktree]', file=sys.stderr)
    sys.exit(2)

NAME = sys.argv[1]
MW = os.path.abspath(sys.argv[2] if len(sys.argv) > 2
                     else os.path.expanduser('~/Code/lean/mathlib-master'))
JOURNAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASE = os.path.join(JOURNAL, 'Journal/Blog/MartingaleProblem/TauCeti')
PREFIX = 'TauCetiRoadmap'
SRCDIR = os.path.join(MW, PREFIX)
BUILD = os.path.join(MW, '_lean_master')

for dep in FILES[:FILES.index(NAME)]:
    olean = os.path.join(BUILD, PREFIX, dep, 'Suggested.olean')
    if not os.path.exists(olean):
        print(f'FEHLSCHLAG: die `.olean` von `{dep}` fehlt unter {olean}.\n'
              f'Erst `python3 scripts/check_master.py` laufen lassen.', file=sys.stderr)
        sys.exit(2)

os.makedirs(os.path.join(SRCDIR, NAME), exist_ok=True)
src = os.path.join(SRCDIR, NAME, 'Suggested.lean')
shutil.copy(os.path.join(BASE, NAME, 'Suggested.lean'), src)

shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
         f'-DautoImplicit=false -DrelaxedAutoImplicit=false {src}')
t0 = time.time()
r = subprocess.run(['lake', 'env', 'sh', '-c', shell],
                   capture_output=True, text=True, cwd=MW)
secs = round(time.time() - t0)
out = r.stdout + r.stderr
lines = out.splitlines()
errs = [l for l in lines if 'error:' in l or 'error(' in l]
sorries = [l for l in lines if 'declaration uses' in l and 'sorry' in l]
WARN = re.compile(r':\d+:\d+: warning: (.*)$')
warns = [m.group(1) for m in map(WARN.search, lines) if m]
deps = [w for w in warns if 'has been deprecated' in w]

print(out)
print(f'--- `{NAME}`: rc {r.returncode}, {len(errs)} Fehler, {len(sorries)} `sorry`, '
      f'{len(warns)} Warnungen, davon {len(deps)} veraltet, {secs} s')
sys.exit(1 if (errs or deps) else 0)
