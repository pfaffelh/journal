#!/usr/bin/env python3
"""Typprüft die `Suggested.lean` des Worktrees gegen das fertig gebaute
Mathlib v4.33.1 des Hauptcheckouts, **in Abhängigkeitsordnung**, und zählt
Fehler und `sorry`.

    python3 scripts/check_suggested.py   -> scripts/_citations/lean_check.md

## Warum die Reihenfolge

Seit der Entscheidung des Nutzers vom 2026-09-17 dürfen die Roadmap-Dateien
aufeinander aufbauen, in der Kette

    WeakConvergence -> SkorokhodSpace -> MartingaleProblems

(`KolmogorovExtension` hat keine `Suggested.lean` und ist ohnehin unabhängig).
Ein `import` zwischen ihnen setzt eine gebaute `.olean` der Abhängigkeit voraus.
Dieses Skript baut sie deshalb der Reihe nach und legt jede `.olean` in einen
eigenen Baum, der beim Übersetzen der nächsten Datei an `LEAN_PATH` gehängt
wird.

## Warum der Baum `TauCetiRoadmap/` heißt und das Quellverzeichnis `TauCeti/`

Der Modulname einer importierten Datei kommt **aus der Lage ihrer `.olean` in
`LEAN_PATH`**, nicht aus der Lage ihres Quelltextes; am 2026-09-17 mit einem
Zeugen geprüft.  Das Zielrepositorium `TauCetiProject/TauCetiRoadmap` baut die
Roadmaps unter dem Präfix `TauCetiRoadmap.` -- seine `lakefile.toml` erklärt
`lean_lib TauCetiRoadmap` mit `globs = ["TauCetiRoadmap.*"]` über dem
Verzeichnis `TauCetiRoadmap/`, und eine eingereichte Datei heißt dort also
`TauCetiRoadmap.WeakConvergence.Suggested`.  Genau diese Importzeile muß in
unseren Dateien stehen, sonst baut es hier und nicht dort.  Der `.olean`-Baum
trägt deshalb das Präfix, während das Quellverzeichnis `TauCeti/` heißen darf,
wie es heißt.

## Was die Prüfung nicht tut

Sie filtert nicht, sie schneidet nicht ab und sie übersetzt jede Datei ganz.
`| head -N` ist verboten: ein abgeschnittener Durchlauf sieht wie ein
fehlerfreier aus.  Es wird auch nichts zwischengespeichert -- jeder Lauf
übersetzt alle Dateien neu, damit eine veraltete `.olean` keine Prüfung
vortäuscht.

Der Hauptcheckout wird nur gelesen: `lake env lean` baut dort nichts und legt
dort nichts an.  Statt `cd` wird `lake --dir=…` benutzt.

## Warum `autoImplicit` ausgeschaltet wird

Ohne Lakefile hat `lean` `autoImplicit` **an**, Mathlib schaltet es aus.  Der
Unterschied ist nicht stilistisch: ein unbekannter großgeschriebener Name wird
unter `autoImplicit` stillschweigend zu einer automatisch gebundenen impliziten
Variablen statt zu `unknown identifier`.  Am 2026-09-17, zweiundzwanzigster
Lauf, hat genau das verdeckt, daß `MartingaleProblems/Suggested.lean` die
`SkorokhodSpace`-Roadmap gar nicht importierte -- der Name `IsCadlag` war frei
und die Prüfung fand nichts.  Eine Aussage über einem verschriebenen Namen wäre
so wahr und leer geworden.

Die Abschaltung kostet in allen drei Dateien **null Fehler**; am selben Tag
gemessen.  Das Zielrepositorium baut mit Mathlibs Einstellungen, also prüft
dieses Skript gegen die schärfere und nicht gegen die bequemere.
"""
import os, shutil, subprocess, time

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

JOURNAL = '/home/pfaffelh/Code/lean/journal'
BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
OUT = 'scripts/_citations'
BUILD = os.path.abspath('scratch/_lean')
PREFIX = 'TauCetiRoadmap'

# In Abhängigkeitsordnung.  Der Modulname ist der, unter dem die Datei im
# Zielrepositorium gebaut wird.
FILES = ['WeakConvergence', 'SkorokhodSpace', 'MartingaleProblems']

os.makedirs(OUT, exist_ok=True)
shutil.rmtree(BUILD, ignore_errors=True)

ver = subprocess.run(['lean', '--version'], capture_output=True, text=True).stdout.strip()
rows = [f'# `lake env lean` gegen {ver}', '',
        'In Abhängigkeitsordnung gebaut; jede Datei sieht die `.olean` der vorigen '
        f'unter dem Modulpräfix `{PREFIX}.`.', '',
        'Übersetzt mit `autoImplicit=false` und `relaxedAutoImplicit=false`, wie '
        'Mathlib und wie das Zielrepositorium: ein unbekannter großgeschriebener '
        'Name ist dann ein Fehler und keine freie Variable.', '',
        '| Datei | Modul | rc | Fehler | `sorry` | Sekunden |',
        '| --- | --- | --- | --- | --- | --- |']
detail = []
missing = []

for f in FILES:
    src = os.path.abspath(f'{BASE}/{f}/Suggested.lean')
    mod = f'{PREFIX}.{f}.Suggested'
    olean = os.path.join(BUILD, PREFIX, f, 'Suggested.olean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)

    if not os.path.exists(src):
        rows.append(f'| `{f}/Suggested.lean` | `{mod}` | — | — | — | — |')
        detail += ['', f'## `{f}/Suggested.lean` fehlt', '',
                   f'* keine Datei unter `{src}`']
        continue

    # `lake env` setzt LEAN_PATH auf Mathlib; unser Baum kommt hinten dran.
    shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
             f'-DautoImplicit=false -DrelaxedAutoImplicit=false '
             f'-o {olean} {src}')
    t0 = time.time()
    r = subprocess.run(['lake', f'--dir={JOURNAL}', 'env', 'sh', '-c', shell],
                       capture_output=True, text=True)
    secs = round(time.time() - t0)
    out = r.stdout + r.stderr
    # Lean meldet auch getaggte Fehler, `error(lean.dependsOnNoncomputable):`
    # etwa; ein Filter auf `error:` allein übersieht sie.
    errs = [l for l in out.splitlines() if 'error:' in l or 'error(' in l]
    sorries = [l for l in out.splitlines() if 'declaration uses' in l and 'sorry' in l]
    rows.append(f'| `{f}/Suggested.lean` | `{mod}` | {r.returncode} | '
                f'{len(errs)} | {len(sorries)} | {secs} |')
    if errs:
        detail += ['', f'## Fehler in `{f}/Suggested.lean`', ''] + [f'* `{e}`' for e in errs]
    if not os.path.exists(olean):
        missing.append(f)
        detail += ['', f'## Keine `.olean` für `{f}`', '',
                   f'* `{mod}` ist nicht gebaut; jede spätere Datei, die es '
                   'importiert, scheitert an einem unbekannten Modul und ihr '
                   'Ergebnis unten sagt nichts über ihren Inhalt.']

open(f'{OUT}/lean_check.md', 'w').write('\n'.join(rows + detail) + '\n')
print('\n'.join(rows + detail))
