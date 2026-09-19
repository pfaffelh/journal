#!/usr/bin/env python3
"""Sucht Deklarationen der Roadmaps, die es auf Mathlib `master` schon gibt.

    python3 scripts/check_duplicates.py [REV]
    -> scripts/_citations/duplicates.md

**Warum.**  `TauCetiRoadmap/CONTRIBUTING.md` verlangt, daß eine Roadmap der
Bibliothek nichts anbietet, was sie hat.  Der vierundzwanzigste Lauf des
2026-09-18 fand fünf solche Doppelungen — aber nicht durch eine Prüfung, sondern
weil in `SkorokhodSpace/Suggested.lean` eine Bemerkung stand, die ein Lauf
irgendwann hineingeschrieben hatte.  Das ist Zufall und keine Methode, und
dieses Skript ersetzt ihn.

**Wonach es sucht.**  Nach dem **letzten Namensbestandteil**.  Mathlib benennt
systematisch; wer `isCompact_iff_foo` beweist und die Bibliothek hat
`Bar.isCompact_iff_foo`, hat sehr wahrscheinlich denselben Satz.  Das ist ein
Anhaltspunkt und kein Beweis: das Skript **entscheidet nichts**, es legt die
Paare nebeneinander, und ein Lauf sieht sie am Quelltext an.

**Was es nicht findet:** dieselbe Aussage unter einem anderen Namen.  Dafür gibt
es keine mechanische Prüfung, und das Skript behauptet auch nicht, sie zu
ersetzen — es räumt nur den Teil ab, der mechanisch geht.
"""
import json
import os
import re
import subprocess
import sys

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
OUT = 'scripts/_citations'
PINNED = '94ef6b89544e58e90f119da869f3fb48d1da0f4c'
DIRS = ['KolmogorovExtension', 'MartingaleProblems', 'SkorokhodSpace', 'WeakConvergence']

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+)*"
    r"(theorem|lemma|irreducible_def|def|abbrev|structure|class|instance|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)")

#  Namensbestandteile, die in Mathlib tausendfach vorkommen und über eine
#  Doppelung nichts aussagen.  Sie werden gezählt und nicht aufgeführt.
GENERIC = {'ext', 'map', 'apply', 'mk', 'coe', 'val', 'id', 'comp', 'symm',
           'trans', 'refl', 'le', 'lt', 'eq', 'ne', 'add', 'mul', 'sub', 'neg',
           'zero', 'one', 'top', 'bot', 'sup', 'inf', 'min', 'max', 'fst',
           'snd', 'left', 'right', 'up', 'down', 'toFun', 'invFun', 'congr',
           'cast', 'lift', 'bind', 'pure', 'seq', 'join', 'range', 'dom'}


def index_for(rev):
    path = f'{OUT}/index_{rev}.json'
    if not os.path.exists(path):
        subprocess.run([sys.executable, 'scripts/mathlib_index.py', rev], check=True)
    return json.load(open(path))


#  `namespace X` / `section` / `section X` / `end` / `end X`.  Gebraucht wird
#  beides: der Namensraum, um den vollen Namen zu bilden, und die Klammer, um
#  ihn wieder abzuräumen.  `end` schließt in Lean beides, deshalb ein Stapel
#  aus Paaren und nicht zwei Zähler.
SCOPE = re.compile(r"^(namespace|section|end)(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


def ours():
    """(Datei, Zeile, voller Name) für jede Deklaration der Roadmap-Dateien.

    Zwei Dinge, die eine reine Zeilensuche falsch macht und die der dritte Lauf
    des 2026-09-19 an zwei Fundstellen nachgewiesen hat:

    * **Blockkommentare.**  `MartingaleProblems/Suggested.lean:32443` beginnt im
      Fließtext eines Doc-Kommentars mit den Worten „instance arguments with …",
      und das las der Prüfer als eine Deklaration namens `arguments`.  Sie stand
      als Treffer gegen `Mathlib/Algebra/HierarchyDesign.lean:223` im Bericht.
      `/-` bis `-/` wird daher übersprungen; Zeilenkommentare `--` können keine
      Deklaration beginnen und bleiben unbeachtet.

    * **Namensräume.**  Der Prüfer nahm den Namen, wie er dasteht, und
      `RightContinuousPath.coordinate` stand deshalb als `coordinate` im
      Bericht — ein Name, den es bei uns nicht gibt.  Für den *letzten*
      Bestandteil, nach dem gesucht wird, ist das gleichgültig; für den Leser,
      der das Paar beurteilen soll, ist es der Unterschied zwischen einer
      Kollision im Wurzelnamensraum und keiner.  Der volle Name wird daher aus
      dem Stapel der offenen `namespace` gebildet.
    """
    for d in DIRS:
        p = os.path.join(BASE, d, 'Suggested.lean')
        if not os.path.exists(p):
            continue
        stack, depth = [], 0
        for i, line in enumerate(open(p, encoding='utf-8'), 1):
            if depth:
                depth -= line.count('-/')
                depth += line.count('/-')
                continue
            stripped = line.strip()
            #  Ein einzeiliger Blockkommentar `/-- … -/` öffnet nichts.
            opens = line.count('/-') - line.count('-/')
            if opens > 0:
                #  Beginnt der Kommentar am Zeilenanfang, so kann in dieser
                #  Zeile keine Deklaration mehr stehen.
                depth = opens
                if stripped.startswith('/-'):
                    continue
            m = SCOPE.match(stripped)
            if m:
                kind, nm = m.group(1), m.group(2)
                if kind == 'end':
                    if stack:
                        stack.pop()
                else:
                    stack.append(nm if kind == 'namespace' else None)
                continue
            m = DECL.match(line)
            if m:
                prefix = '.'.join(s for s in stack if s)
                name = m.group(2)
                yield p, i, f'{prefix}.{name}' if prefix else name


def main():
    rev = sys.argv[1] if len(sys.argv) > 1 else PINNED
    index = index_for(rev)

    #  letzter Namensbestandteil -> volle Mathlib-Namen
    by_last = {}
    for q, loc in index.items():
        by_last.setdefault(q.split('.')[-1], []).append((q, loc))

    hits, generic, total = [], 0, 0
    for src, line, name in ours():
        total += 1
        last = name.split('.')[-1]
        if last not in by_last:
            continue
        if last in GENERIC or len(last) < 8:
            generic += 1
            continue
        #  Ein Treffer, der selbst `deprecated` ist, ist keine Doppelung: die
        #  Bibliothek gibt den Namen gerade auf.
        live = [(q, loc) for q, loc in by_last[last] if not loc.startswith('!')]
        if not live:
            continue
        hits.append((src, line, name, live))

    hits.sort(key=lambda h: (-len(h[2].split('_')), h[2]))

    lines = [f'# Deklarationen, die es auf `{rev}` schon geben könnte', '',
             f'* geprüfte eigene Deklarationen: **{total}**',
             f'* Treffer auf dem letzten Namensbestandteil: **{len(hits)}**',
             f'* als zu allgemein übergangen (kurz oder generisch): {generic}', '',
             'Ein Treffer ist ein **Anhaltspunkt**, keine Doppelung. Er sagt, daß '
             'Mathlib einen Satz mit demselben letzten Namensbestandteil hat — '
             'nachzusehen ist, ob es dieselbe Aussage ist.', '',
             '| unsere Deklaration | Stelle | gleichnamig auf `master` |',
             '| --- | --- | --- |']
    for src, line, name, live in hits:
        where = f'{os.path.relpath(src, BASE)}:{line}'
        cand = '; '.join(f'`{q}` (`{loc}`)' for q, loc in live[:3])
        lines.append(f'| `{name}` | `{where}` | {cand} |')
    lines.append('')

    os.makedirs(OUT, exist_ok=True)
    open(f'{OUT}/duplicates.md', 'w', encoding='utf-8').write('\n'.join(lines))
    print('\n'.join(lines[:6]))
    print(f'-> {OUT}/duplicates.md')
    return 0


if __name__ == '__main__':
    sys.exit(main())
