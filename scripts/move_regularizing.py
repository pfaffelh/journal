#!/usr/bin/env python3
"""Holt den Abschnitt `Regularizing` aus `JumpProcesses` nach `MartingaleProblems`.

Der Schnitt vom 2026-09-22 hat den Abschnitt `Regularizing` **mitten
durchgeschnitten**: die Sätze, die `IsCompensatorFor` lesen, sind nach
`JumpProcesses` gewandert, alles übrige blieb.  Beide Dateien tragen seither
denselben Abschnittskopf, dieselben zwei Vorbemerkungen und dieselben
`variable`-Zeilen; zwei Zeugenräume (`LiftWitness`, `AtomWitness`) stehen zur
Hälfte hier und zur Hälfte dort.

Das Skript macht den Schnitt rückgängig, und zwar allein durch Verschieben:
kein Text wird geändert.

    python3 scripts/_dev_move_regularizing.py

Es ist **einmal** zu laufen und danach gegenstandslos; es bleibt stehen, damit
nachprüfbar ist, daß der Umzug ein Verschieben war und keine Neufassung.
"""
import os

BASE = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    'Journal/Blog/MartingaleProblem/TauCeti')
JP = os.path.join(BASE, 'JumpProcesses/Suggested.lean')
MP = os.path.join(BASE, 'MartingaleProblems/Suggested.lean')

jp = open(JP).read().split('\n')
mp = open(MP).read().split('\n')

# 1-basierte Zeilen, am Quelltext abgelesen und hier geprüft statt geraten.
JP_HEAD = 362        # `/-! ## Milestone 9: the regularizing class ...`
JP_BODY_FROM = 403   # `/-- The decomposition attached to one `f` ...`
JP_BODY_TO = 1607    # letzte Zeile vor `end Regularizing` (leer)
JP_END = 1609        # Leerzeile nach `end Regularizing`
MP_END = 5926        # `end Regularizing`

# Der Umzug ist einmal gelaufen.  Ein zweiter Aufruf soll das sagen und nicht an
# einer Zusicherung zerbrechen -- ein Skript, das mit einer Stapelspur abbricht,
# sieht wie ein Fehler aus, wo es bloß gegenstandslos ist.
if len(jp) <= JP_END or not jp[JP_HEAD - 1].startswith('/-! ## Milestone 9'):
    raise SystemExit('Der Abschnitt `Regularizing` steht nicht mehr in '
                     '`JumpProcesses` -- der Umzug ist am 2026-09-24 gelaufen '
                     'und dieses Skript ist gegenstandslos.')

assert jp[JP_HEAD - 1].startswith('/-! ## Milestone 9: the regularizing class'), jp[JP_HEAD - 1]
assert jp[JP_BODY_FROM - 1].startswith('/-- The decomposition attached'), jp[JP_BODY_FROM - 1]
assert jp[JP_BODY_TO - 1] == '', repr(jp[JP_BODY_TO - 1])
assert jp[JP_BODY_TO] == 'end Regularizing', jp[JP_BODY_TO]
assert jp[JP_END - 1] == '', repr(jp[JP_END - 1])
assert mp[MP_END - 1] == 'end Regularizing', mp[MP_END - 1]

body = jp[JP_BODY_FROM - 1:JP_BODY_TO]

out_mp = mp[:MP_END - 1] + body + mp[MP_END - 1:]
out_jp = jp[:JP_HEAD - 1] + jp[JP_END:]

open(MP, 'w').write('\n'.join(out_mp))
open(JP, 'w').write('\n'.join(out_jp))

print(f'verschoben: {len(body)} Zeilen')
print(f'JumpProcesses: {len(jp)} -> {len(out_jp)} Zeilen')
print(f'MartingaleProblems: {len(mp)} -> {len(out_mp)} Zeilen')
