#!/usr/bin/env python3
"""Welche Namen liest der Beweis einer Deklaration, und wo stehen sie?

Ein Hilfsskript für die Aufgabe vom 2026-09-24, Punkt 1: fünf allgemeine
Aussagen stehen in `JumpProcesses/Suggested.lean`, weil ihre *Beweise*
Sprungmaterial lesen sollen.  Das Skript prüft, ob das stimmt -- je
Deklaration und Name, nicht pauschal.

    python3 scripts/_dev_deps.py <name> [<name> ...]

Ausgegeben wird je Name die Liste der Bezeichner, die im Rumpf vorkommen und
in `JumpProcesses/Suggested.lean` **definiert** sind.  Ist sie leer, so liest
der Beweis kein Sprungmaterial und die Deklaration kann zurück.

Die Erkennung ist syntaktisch und damit nach oben grob: sie zählt jeden
Bezeichner, auch einen, der bloß im Doc-Kommentar steht.  Doc-Kommentare
werden deshalb abgeschnitten.  Ein leerer Befund ist daher belastbar, ein
nichtleerer ist eine Liste von Verdächtigen und keine Entscheidung.
"""
import json
import os
import re
import sys

BASE = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    'Journal/Blog/MartingaleProblem/TauCeti')
DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*'
    r'(?:theorem|lemma|def|structure|abbrev|instance|class|inductive)\s+'
    r"([A-Za-z_][A-Za-z0-9_'\.]*)")
STOP = re.compile(
    r"^(?:/-|@\[|section\b|end\b|namespace\b|open\b|variable\b|omit\b|"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(?:theorem|lemma|def|structure|abbrev|instance|class|inductive)\b)")


def declarations(path):
    """Name -> Zeile der ersten Zeile der Deklaration."""
    out = {}
    with open(path) as fh:
        for i, line in enumerate(fh, 1):
            m = DECL.match(line)
            if m:
                out.setdefault(m.group(1), i)
    return out


def body(path, name):
    """Der Rumpf einer Deklaration, ohne Doc-Kommentar davor."""
    lines = open(path).read().split('\n')
    start = None
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if m and m.group(1) == name:
            start = i
            break
    if start is None:
        return None
    end = start + 1
    while end < len(lines) and not STOP.match(lines[end]):
        end += 1
    return '\n'.join(lines[start:end])


def main(argv):
    jp = declarations(os.path.join(BASE, 'JumpProcesses/Suggested.lean'))
    mp = declarations(os.path.join(BASE, 'MartingaleProblems/Suggested.lean'))
    sys.stderr.write(f'JumpProcesses: {len(jp)} Deklarationen, '
                     f'MartingaleProblems: {len(mp)}\n')
    for name in argv:
        src = os.path.join(BASE, 'JumpProcesses/Suggested.lean')
        txt = body(src, name)
        if txt is None:
            print(f'{name}: nicht in JumpProcesses gefunden')
            continue
        # Bezeichner des Rumpfes, ohne den eigenen Namen
        used = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'\.]*", txt)) - {name}
        local = sorted(n for n in used if n in jp and n not in mp)
        nloc = len(txt.split('\n'))
        print(f'{name}  ({nloc} Zeilen Rumpf)')
        if local:
            for n in local:
                print(f'    JumpProcesses-eigen: {n}  (Zeile {jp[n]})')
        else:
            print('    kein JumpProcesses-eigener Name im Rumpf')


if __name__ == '__main__':
    main(sys.argv[1:])
