#!/usr/bin/env python3
"""Zaehlt Zeilen und Deklarationen in Zeilenbereichen einer Lean-Datei.

Allein lauffaehig, liest nur.  Aufruf:

    python3 scripts/count_range.py <datei.lean> <von>-<bis> [<von>-<bis> ...]

Gezaehlt wird als Deklaration jede Zeile, die in Spalte 0 mit
`theorem`, `lemma`, `def`, `noncomputable def`, `instance` oder
`structure` beginnt.  Die Namen der gefundenen Deklarationen werden
mitgedruckt, damit ein Leser die Zuordnung zu einem Weg nachpruefen
kann, statt der Zahl glauben zu muessen.
"""

import re
import sys

DECL = re.compile(
    r"^(?:noncomputable\s+)?(theorem|lemma|def|instance|structure)\s+([^\s({\[:]+)"
)


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    path = sys.argv[1]
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()

    grand_lines = 0
    grand_decls = 0
    for spec in sys.argv[2:]:
        lo, hi = (int(x) for x in spec.split("-"))
        names = [
            m.group(2)
            for m in (DECL.match(b) for b in lines[lo - 1 : hi])
            if m is not None
        ]
        span = hi - lo + 1
        grand_lines += span
        grand_decls += len(names)
        print(f"{spec}: Zeilen {span}, Deklarationen {len(names)}")
        for n in names:
            print(f"    {n}")
    print(f"SUMME: Zeilen {grand_lines}, Deklarationen {grand_decls}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
