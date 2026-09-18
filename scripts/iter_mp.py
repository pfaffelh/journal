#!/usr/bin/env python3
"""Schnelle Iteration an einer einzelnen `Suggested.lean` während eines Laufs.

`scripts/check_suggested.py` löscht seinen `.olean`-Baum bei jedem Lauf und baut
alle drei Dateien neu; das ist richtig für die **Prüfung** und zu langsam für das
Schreiben.  Dieses Skript baut in einen eigenen, bleibenden Baum `scratch/_iter/`
und übersetzt nur, was verlangt ist.

    python3 scripts/iter_mp.py WeakConvergence SkorokhodSpace   # einmal
    python3 scripts/iter_mp.py MartingaleProblems               # je Durchgang

Es gibt die Fehlerzeilen ungefiltert aus und **ersetzt `check_suggested.py`
nicht**: der Abschlußbefund eines Laufs wird mit jenem Skript erhoben, das ohne
Zwischenspeicher arbeitet und damit keine veraltete `.olean` durchgehen läßt.
"""
import os, subprocess, sys, time

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

JOURNAL = '/home/pfaffelh/Code/lean/journal'
BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
BUILD = os.path.abspath('scratch/_iter')
PREFIX = 'TauCetiRoadmap'

rc_all = 0
for f in sys.argv[1:]:
    src = os.path.abspath(f'{BASE}/{f}/Suggested.lean')
    olean = os.path.join(BUILD, PREFIX, f, 'Suggested.olean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
             f'-DautoImplicit=false -DrelaxedAutoImplicit=false -o {olean} {src}')
    t0 = time.time()
    r = subprocess.run(['lake', f'--dir={JOURNAL}', 'env', 'sh', '-c', shell],
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if 'error:' in l or 'error(' in l]
    sorries = [l for l in out.splitlines() if 'declaration uses' in l and 'sorry' in l]
    print(f'== {f}: rc={r.returncode} Fehler={len(errs)} sorry={len(sorries)} '
          f'{round(time.time() - t0)}s')
    # Nur die Fehlerblöcke ausgeben: ein Fehler reicht bis zur nächsten
    # Meldungszeile `<datei>:<zeile>:<spalte>:`.  Warnungen werden übergangen,
    # Fehler **nicht** gefiltert -- jede Fehlerzeile steht vollständig da.
    if errs:
        import re
        head = re.compile(r'^\S+\.lean:\d+:\d+: ')
        show, on = [], False
        for l in out.splitlines():
            if head.match(l):
                on = 'error:' in l or 'error(' in l
            if on:
                show.append(l)
        print('\n'.join(show))
    rc_all |= r.returncode
sys.exit(rc_all)
