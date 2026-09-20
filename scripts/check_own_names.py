#!/usr/bin/env python3
"""Prüft die in den Roadmaps zitierten **eigenen** Deklarationsnamen.

    python3 scripts/check_own_names.py [REV]
    -> scripts/_citations/own_names.md

**Warum es dieses Skript gibt, und was es von `check_cited_names.py`
unterscheidet.**  Jenes prüft die zitierten **Mathlib**-Namen gegen
`upstream/master`; es sagt ausdrücklich, ein Fehlschlag heiße nicht, daß der
Name verschwunden sei — „er kann auch unsere eigene Roadmap-Vokabel sein".
Genau darin lag ein blinder Fleck: eine Roadmap, die eine Aussage **unter Namen
verspricht**, die in keiner unserer `Suggested.lean` steht, fällt dort in den
Topf der nicht beurteilbaren Namen und wird nicht bemerkt.

Am 2026-09-20 stand so `Martingale.eLpNorm_iSup_norm_le` seit Wochen als
Akzeptanzbeispiel in `MartingaleProblems/README.md`, Meilenstein 9 — ein Satz,
den ein Leser aufschlagen soll und den es nicht gibt.  Gefunden wurde er von
Hand, beim Lesen.  Das ist Zufall und keine Methode.

**Was ein Treffer heißt, und was er nicht heißt.**  Eine Tau-Ceti-Roadmap
*benennt* Aussagen, die noch zu beweisen sind; ein Name in der `README.md`
ohne Deklaration in der `Suggested.lean` ist deshalb der **Regelfall** eines
offenen Punktes und kein Fehler.  Das Skript entscheidet darüber nichts.  Was
es liefert, ist die Liste dieser **offenen Zusagen** — und damit die Stelle,
an der ein Lauf nachsieht, ob eine davon inzwischen unter einem *anderen*
Namen dasteht.  Genau das war der Fall vom 2026-09-20:
`Martingale.lintegral_biSup_enorm_rpow_le` war bewiesen, die `README.md`
verwies daneben auf einen Namen, den kein Lauf je geschrieben hat.

Der Rückgabewert ist deshalb **immer 0**.  Eine Zahl, die im Normalbetrieb
nicht null ist, taugt nicht als Abbruchbedingung.

**Wonach gesucht wird.**  Nach jedem in Rückwärtsanführungszeichen gesetzten
Bezeichner in den vier `README.md`, der

* **weder** eine Deklaration einer unserer vier `Suggested.lean` ist (voller
  Name oder, nachsichtiger, letzter Namensbestandteil),
* **noch** auf Mathlib `REV` existiert (voller Name oder letzter Bestandteil).

Die Deckung wird **nachsichtig** geprüft: es genügt der letzte
Namensbestandteil.  `Foo.bar_baz` gilt als gedeckt, sobald irgendwo ein
`bar_baz` steht.  Die gemeldete Zahl ist damit eine **untere Schranke** für
die offenen Zusagen, und das ist die gewollte Richtung: was hier steht, steht
wirklich nirgends.

Die Ausgabe ist in zwei Abschnitte geteilt:

1. **Qualifizierte Namen ohne Deckung** — sie enthalten einen Punkt und ihr
   Präfix ist ein bei uns oder in Mathlib vorhandener Namensraum.  Das sind
   die offenen Zusagen im engeren Sinn: sie sehen für einen Leser wie eine
   Fundstelle aus.
2. **Alles übrige ohne Deckung** — die grobe Restliste aus Notationen,
   Feldnamen und Hilfsvariablen des Fließtexts.

Gelesen wird nur.
"""
import json
import os
import re
import subprocess
import sys

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

sys.path.insert(0, os.path.join(os.getcwd(), 'scripts'))
from check_duplicates import ours, index_for, PINNED, DIRS, BASE  # noqa: E402

OUT = 'scripts/_citations'

#  Ein Zitat ist ein Bezeichner in Backticks, ohne Leerzeichen, mit einem
#  Buchstaben am Anfang.  Notationen (`ℝ≥0`, `→ᵇ`) fallen dadurch heraus.
#  Dieselbe Regel wie in `check_cited_names.py`, damit die beiden Prüflisten
#  vergleichbar bleiben.
CITE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)`")

#  Wörter, die in den Roadmaps als Fließtext in Backticks stehen und keine
#  Deklaration sind.  Sie werden gezählt und nicht aufgeführt; die Liste wächst
#  nur, wenn ein Lauf einen Namen als Fließtext *belegt* hat.
PROSE = {
    'sorry', 'rfl', 'simp', 'rw', 'exact', 'ext', 'omega', 'fun_prop',
    'positivity', 'calc', 'have', 'show', 'obtain', 'refine', 'intro',
    'filter_upwards', 'push_neg', 'norm_num', 'ring', 'linarith', 'gcongr',
    'classical', 'convert', 'apply', 'induction', 'cases', 'rcases',
    'namespace', 'section', 'variable', 'theorem', 'lemma', 'def', 'instance',
    'structure', 'class', 'import', 'open', 'deprecated', 'master', 'main',
    'true', 'false', 'if', 'then', 'else', 'let', 'do', 'where', 'with',
    'at', 'in', 'by', 'and', 'or', 'not', 'iff',
}


def citations():
    """(Datei, Zeile, Name) für jedes Zitat in den vier `README.md`."""
    for d in DIRS:
        p = os.path.join(BASE, d, 'README.md')
        if not os.path.exists(p):
            continue
        for i, line in enumerate(open(p, encoding='utf-8'), 1):
            for name in CITE.findall(line):
                yield p, i, name


def main():
    rev = sys.argv[1] if len(sys.argv) > 1 else PINNED
    index = index_for(rev)
    mathlib_full = set(index)
    mathlib_last = {q.split('.')[-1] for q in index}

    own_full, own_last, own_ns = set(), set(), set()
    for _, _, q in ours():
        own_full.add(q)
        own_last.add(q.split('.')[-1])
        parts = q.split('.')
        for k in range(1, len(parts)):
            own_ns.add('.'.join(parts[:k]))

    mathlib_ns = set()
    for q in mathlib_full:
        parts = q.split('.')
        for k in range(1, len(parts)):
            mathlib_ns.add('.'.join(parts[:k]))
    namespaces = own_ns | mathlib_ns

    #  Name -> Fundstellen, für die Namen ohne jede Deckung.
    uncovered = {}
    seen = 0
    prose = 0
    for path, line, name in citations():
        seen += 1
        if name in PROSE:
            prose += 1
            continue
        last = name.split('.')[-1]
        if (name in own_full or name in mathlib_full
                or last in own_last or last in mathlib_last):
            continue
        uncovered.setdefault(name, []).append(f'{path}:{line}')

    def looks_like_decl(n):
        last = n.rsplit('.', 1)[-1]
        #  `p.1`, `p.2` sind Projektionen, `Cauchy.lean` ist ein Dateiname.
        return not last.isdigit() and last not in {'lean', 'md', 'py', 'tex'}

    qualified = {n: v for n, v in uncovered.items()
                 if '.' in n and n.rsplit('.', 1)[0] in namespaces
                 and looks_like_decl(n)}
    rest = {n: v for n, v in uncovered.items() if n not in qualified}

    lines = ['# Zitierte eigene Namen ohne Deckung', '',
             f'* Mathlib-Index: `{rev}`',
             f'* Zitate in den vier `README.md`: {seen}',
             f'* davon Fließtext (Taktiken, Schlüsselwörter): {prose}',
             f'* ohne Deckung in Mathlib **und** in unseren `Suggested.lean`: '
             f'{len(uncovered)}',
             '',
             '## 1. Qualifizierte Namen ohne Deckung',
             '',
             'Der Namensraum existiert, der Name nicht.  Das ist im Regelfall '
             'ein **offener Punkt** der Roadmap und kein Fehler; zu prüfen ist '
             'je Zeile, ob die Aussage inzwischen unter einem anderen Namen '
             'dasteht.',
             '']
    if qualified:
        lines += ['| Name | Fundstellen |', '| --- | --- |']
        for n in sorted(qualified):
            locs = ', '.join(f'`{x}`' for x in qualified[n])
            lines.append(f'| `{n}` | {locs} |')
    else:
        lines.append('Keine.')
    lines += ['', '## 2. Alles übrige ohne Deckung', '',
              'Prüfliste, von Hand durchzugehen: Notationen, Feldnamen, '
              'Hilfsvariablen aus dem Fließtext — und was davon keines ist.',
              '']
    if rest:
        lines += ['| Name | Fundstellen |', '| --- | --- |']
        for n in sorted(rest):
            locs = ', '.join(f'`{x}`' for x in rest[n][:4])
            if len(rest[n]) > 4:
                locs += f', … ({len(rest[n])} insgesamt)'
            lines.append(f'| `{n}` | {locs} |')
    else:
        lines.append('Keine.')

    os.makedirs(OUT, exist_ok=True)
    with open(f'{OUT}/own_names.md', 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines) + '\n')
    print('\n'.join(lines[:12]))
    print(f'\n-> {OUT}/own_names.md '
          f'({len(qualified)} qualifiziert, {len(rest)} übrige)')
    #  Kein Fehlschlag: offene Zusagen sind der Normalzustand einer Roadmap.
    return 0


if __name__ == '__main__':
    sys.exit(main())
