#!/usr/bin/env python3
"""Wie `check_axioms.py`, aber gegen Mathlib **`upstream/master`**.

    python3 scripts/check_axioms_master.py MartingaleProblems name [name ...]

Seit dem 2026-09-18 ist `master` der maßgebliche Stand, und gegen v4.33.1
übersetzt die Kette nicht mehr; `check_axioms.py` hängt aber am dortigen Baum
`scratch/_lean` und läuft deshalb ins Leere.  Dieses Skript benutzt den Baum,
den `scripts/check_master.py` anlegt (`<worktree>/_lean_master`), und läuft mit
`cwd` im Worktree, weil `elan` die Lean-Version am Arbeitsverzeichnis wählt.

`scripts/check_master.py` ist also **zuerst** zu laufen: ohne die `.olean` der
Vorgängerdateien scheitert schon die Importzeile, und die Axiomprüfung sagt
dann nichts.

Wie beim Original wird auf einer **Kopie** neben der Quelle gearbeitet, damit
ein Abbruch die Quelle unverändert läßt; und Fortsetzungszeilen werden erst
angehängt und dann gefiltert, weil Lean lange Axiomlisten umbricht und ein
`sorryAx` sonst in der zweiten Zeile verschwindet.
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MW = pathlib.Path(os.environ.get('MATHLIB_MASTER',
                                 os.path.expanduser('~/Code/lean/mathlib-master')))
# Seit `check_master.py` je Aufruf einen eigenen Baum anlegt (2026-09-19), liegt
# der gebaute Baum nicht mehr fest unter `<worktree>/_lean_master`.  `CHECK_TREE`
# nimmt den Pfad auf, den ein Lauf mit `CHECK_MASTER_KEEP=1` stehenläßt.
BUILD = pathlib.Path(os.environ.get('CHECK_TREE', str(MW / '_lean_master')))


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    roadmap, names = argv[0], argv[1:]
    src = ROOT / "Journal/Blog/MartingaleProblem/TauCeti" / roadmap / "Suggested.lean"
    if not src.exists():
        print(f"no such file: {src}")
        return 2
    if not BUILD.is_dir():
        print(f"kein gebauter Baum unter {BUILD}; "
              "erst `python3 scripts/check_master.py` laufen lassen")
        return 2
    # Die Datei muß unterhalb des Wurzelverzeichnisses von `lean` liegen, und
    # ihre Lage bestimmt ihren Modulnamen; also dieselbe Lage wie in
    # `check_master.py`.
    tmp = MW / "TauCetiRoadmap" / roadmap / "Suggested.axioms.tmp.lean"
    tmp.parent.mkdir(parents=True, exist_ok=True)
    tmp.write_text(
        src.read_text() + "\n" + "".join(f"#print axioms {n}\n" for n in names))
    try:
        shell = (f'LEAN_PATH="$LEAN_PATH:{BUILD}" exec lean '
                 f'-DautoImplicit=false -DrelaxedAutoImplicit=false {tmp}')
        proc = subprocess.run(["lake", "env", "sh", "-c", shell],
                              cwd=MW, capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        joined: list[str] = []
        for line in out.splitlines():
            if joined and line[:1].isspace() and line.strip():
                joined[-1] = joined[-1].rstrip() + " " + line.strip()
            else:
                joined.append(line)
        for line in joined:
            if "depends on axioms" in line or "error" in line:
                print(line)
        return proc.returncode
    finally:
        tmp.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
