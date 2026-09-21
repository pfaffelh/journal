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

## Der Rückgabewert

Seit dem 2026-09-18, vierundzwanzigster Lauf, ist er **nicht mehr immer 0**: das
Skript scheitert, wenn die Spalte „davon veraltet" nicht 0 ist, und ebenso bei
einem Fehler.  Die übrigen Warnungen bleiben draußen -- es sind 160, und sie sind
Stilfragen.

## Was die Prüfung nicht tut

Sie filtert nicht und schneidet nicht ab.  `| head -N` ist verboten: ein
abgeschnittener Durchlauf sieht wie ein fehlerfreier aus.
"""
import atexit, collections, os, re, shutil, subprocess, sys, time

# `--keep` tut dasselbe wie `CHECK_MASTER_KEEP=1`.  Der Grund für die zweite
# Schreibweise ist nicht Bequemlichkeit: eine Umgebung läßt sich nicht in jedem
# Aufrufkontext setzen (ein Lauf vom 2026-09-19 konnte Kommandos nur ohne
# vorangestellte Zuweisung absetzen), und dann ist der schnelle Entwicklungsweg
# ohne eine Flagge gar nicht erreichbar.
ARGV = [a for a in sys.argv[1:] if a != '--keep']
MW = os.path.abspath(ARGV[0] if ARGV
                     else os.path.expanduser('~/Code/lean/mathlib-master'))
# Das Repositorium, in dem *dieses Skript* liegt -- nicht der Hauptcheckout.
# Ein Lauf arbeitet in einem Worktree, und geprüft gehören seine Quellen, nicht
# die von `master`; ebenso wird der Bericht dorthin geschrieben, wo er committet
# wird.
JOURNAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASE = os.path.join(JOURNAL, 'Journal/Blog/MartingaleProblem/TauCeti')
OUT = os.path.join(JOURNAL, 'scripts/_citations')
PREFIX = 'TauCetiRoadmap'
# Jeder Aufruf bekommt seinen eigenen Baum unterhalb des Worktrees.  Der Grund
# ist gemessen, nicht vorsorglich: am 2026-09-19 liefen der Cron-Lauf und der
# Hauptcheckout in derselben Minute, beide kopierten nach `<MW>/TauCetiRoadmap/`
# und ueberschrieben einander Quellen und `.olean`.  Die Zahlen mussten allein
# nachgemessen werden.  `lean` verlangt nur, dass die Eingabedatei *unterhalb*
# des Wurzelverzeichnisses liegt, nicht unmittelbar darin -- eine Ebene mehr
# kostet also nichts und erlaubt parallele Aufrufe.
RUNDIR = os.path.join(MW, f'_check_{os.getpid()}')
SRCDIR = os.path.join(RUNDIR, PREFIX)
BUILD = os.path.join(RUNDIR, '_lean_master')
FILES = ['WeakConvergence', 'SkorokhodSpace', 'MartingaleProblems']

os.makedirs(OUT, exist_ok=True)
shutil.rmtree(RUNDIR, ignore_errors=True)
# Der eigene Baum wird am Ende geräumt -- außer ein Entwicklungslauf verlangt ihn
# zurück.  `check_axioms_master.py` und `dev_check_master.py` brauchen die
# gebauten `.olean`, und seit der Baum je Aufruf angelegt wird, finden sie ihn
# nur, wenn er stehenbleibt und sein Pfad genannt wird.
KEEP = os.environ.get('CHECK_MASTER_KEEP') == '1' or '--keep' in sys.argv[1:]
if not KEEP:
    atexit.register(shutil.rmtree, RUNDIR, True)

# Verwaiste Baeume raeumen.  `atexit` greift nicht, wenn der Aufrufer abgebrochen
# wird, und mit `--keep` greift es gar nicht: am 2026-09-21 standen **93** Baeume
# zu je 30-64 MB unter dem Worktree, mehrere Gigabyte.  Beim Start deshalb alles
# entfernen, dessen PID nicht mehr laeuft -- der eigene und die fremder laufender
# Aufrufe bleiben stehen, sodass parallele Laeufe sich weiterhin nicht stoeren.
for _d in os.listdir(MW):
    if not _d.startswith('_check_'):
        continue
    try:
        _pid = int(_d[len('_check_'):])
    except ValueError:
        continue
    if _pid == os.getpid():
        continue
    try:
        os.kill(_pid, 0)
    except ProcessLookupError:
        shutil.rmtree(os.path.join(MW, _d), ignore_errors=True)
    except PermissionError:
        pass
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
errcount = 0

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
    errcount += len(errs)
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

# Die Schranke, und sie gilt nur für die Veraltungen.
#
# Am 2026-09-18 waren 78 der 354 abgetragenen Veraltungen schon gegen v4.33.1
# veraltet, eine davon seit zehn Monaten; unbemerkt geblieben sind sie, weil
# `check_suggested.py` nur Fehler zählt.  Ein Nullstand ohne Schranke hält bis
# zur nächsten Deklaration, deshalb bricht der Lauf hier ab.
#
# Die übrigen Warnungen bleiben ausdrücklich draußen.  Es sind 160, und sie sind
# Stilfragen -- `unusedSectionVars` zu befolgen hieße Signaturen ändern.  Eine
# Schranke darüber machte die Prüfung unbrauchbar.
#
# Fehler lassen den Lauf ebenfalls scheitern.  Das steht nicht im Auftrag, der
# nur die Veraltungen verlangte, ist aber dieselbe Falle: ein Prüfskript, das
# bei Fehlern rc 0 zurückgibt, sieht von außen wie ein sauberer Durchlauf aus.
if KEEP:
    print(f'CHECK_TREE={RUNDIR}/_lean_master')
bad = sum(len(v) for v in deprecated.values())
if bad:
    print(f'FEHLSCHLAG: {bad} veraltete Namen in der Kette. '
          f'Die Namen stehen im Anhang von `_citations/lean_check_master.md`.',
          file=sys.stderr)
if errcount:
    print(f'FEHLSCHLAG: {errcount} Fehler in der Kette.', file=sys.stderr)
sys.exit(1 if (bad or errcount) else 0)
