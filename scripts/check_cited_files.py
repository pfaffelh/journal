#!/usr/bin/env python3
"""Prüft, ob die in den Roadmaps zitierten Mathlib-Dateipfade auf
`upstream/master` noch existieren.

Aufruf (aus dem Worktree-Wurzelverzeichnis):

    python3 scripts/check_cited_files.py

Es wird nur gelesen: `git -C ~/Code/lean/mathlib4 ls-tree` gegen
`upstream/master`, ohne Auschecken.  Ausgabe auf stdout: je Zeile ein
zitierter Pfad mit `OK` oder `FEHLT`, danach eine Zusammenfassung.
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAUCETI = ROOT / "Journal" / "Blog" / "MartingaleProblem" / "TauCeti"
MATHLIB = pathlib.Path.home() / "Code" / "lean" / "mathlib4"
REF = "upstream/master"

#  Nur Pfade mit mindestens einem `/`: ein bloßes `Basic.lean` ist kein Zitat,
#  sondern eine Abkürzung im Fließtext und in Mathlib hundertfach vorhanden.
PATH_RE = re.compile(r"[A-Z][A-Za-z0-9_]*(?:/[A-Za-z0-9_]+)+\.lean")


def tracked_files() -> set[str]:
    out = subprocess.run(
        ["git", "-C", str(MATHLIB), "ls-tree", "-r", "--name-only", REF, "Mathlib/"],
        capture_output=True, text=True, check=True).stdout
    return set(out.split())


def main() -> int:
    tracked = tracked_files()
    suffixes: dict[str, list[str]] = {}
    for f in tracked:
        suffixes.setdefault(f.split("/")[-1], []).append(f)

    cited: dict[str, list[str]] = {}
    for src in sorted(TAUCETI.glob("*/README.md")) + sorted(TAUCETI.glob("*/Suggested.lean")):
        for m in PATH_RE.finditer(src.read_text(encoding="utf-8")):
            cited.setdefault(m.group(0), []).append(src.name)

    missing = []
    for path in sorted(cited):
        full = path if path.startswith("Mathlib/") else "Mathlib/" + path
        #  Die Roadmaps kürzen Pfade oft ab (`Measure/Tight.lean` für
        #  `Mathlib/MeasureTheory/Measure/Tight.lean`).  Ein Zitat gilt als
        #  eingelöst, wenn eine getrackte Datei auf genau diesen Pfad endet.
        tails = [f for f in suffixes.get(path.split("/")[-1], [])
                 if f == full or f.endswith("/" + path)]
        if full in tracked:
            status = "OK"
        elif len(tails) == 1:
            status = "OK(kurz)"
        elif len(tails) > 1:
            status = "MEHRDEUTIG"
            missing.append((path, status + " -> " + ", ".join(sorted(tails)[:4])))
        else:
            status = "FEHLT"
            missing.append((path, status))
        print(f"{status:<12} {path}")

    print()
    for path, status in missing:
        print(f"BEFUND {path}: {status}  (zitiert in "
              f"{', '.join(sorted(set(cited[path])))})")
    print()
    print(f"{len(cited)} zitierte Pfade, {len(missing)} nicht als "
          f"Mathlib/<Pfad> auf {REF} gefunden.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
