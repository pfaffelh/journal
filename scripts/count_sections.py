#!/usr/bin/env python3
"""Zaehlt Zeilen und Deklarationen je `section` einer Lean-Datei.

Allein lauffaehig, liest nur.  Aufruf:

    python3 scripts/count_sections.py <datei.lean> [name ...]

Ohne Namen werden alle Abschnitte gezaehlt, sonst nur die genannten.
Gezaehlt wird als Deklaration jede Zeile, die in Spalte 0 mit
`theorem`, `lemma`, `def`, `noncomputable def`, `instance` oder
`structure` beginnt; Doc-Kommentare und Beweiszeilen zaehlen als Zeilen.

Was das Skript **nicht** leistet: es kennt keine verschachtelten
`section`-Namen ohne Bezeichner und keine `namespace`-Bloecke.  Es ist
ein Zeilenzaehler und kein Parser.
"""

import re
import sys

DECL = re.compile(r"^(theorem|lemma|def|noncomputable def|instance|structure)\b")
SEC = re.compile(r"^section\s+(\S+)")
END = re.compile(r"^end\s+(\S+)")


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    path = sys.argv[1]
    wanted = set(sys.argv[2:])
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()

    open_sections: list[tuple[str, int]] = []
    results: list[tuple[str, int, int, int]] = []
    for i, line in enumerate(lines, start=1):
        m = SEC.match(line)
        if m:
            open_sections.append((m.group(1), i))
            continue
        m = END.match(line)
        if m:
            name = m.group(1)
            for k in range(len(open_sections) - 1, -1, -1):
                if open_sections[k][0] == name:
                    start = open_sections.pop(k)[1]
                    body = lines[start : i - 1]
                    decls = sum(1 for b in body if DECL.match(b))
                    results.append((name, start, i, decls))
                    break

    total_lines = 0
    total_decls = 0
    for name, start, end, decls in sorted(results, key=lambda r: r[1]):
        if wanted and name not in wanted:
            continue
        span = end - start + 1
        total_lines += span
        total_decls += decls
        print(f"{name}: Zeilen {start}-{end} ({span}), Deklarationen {decls}")
    print(f"SUMME: Zeilen {total_lines}, Deklarationen {total_decls}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
