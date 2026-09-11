#!/usr/bin/env python3
"""Print the axiom dependencies of named declarations of a `Suggested.lean`.

Every run of this branch checks its new declarations with `#print axioms` and
reports the result.  Until now that was done by hand, by appending the lines to
the file, translating it, and removing them again -- a step that leaves the
source in a modified state if the run is cut off in the middle.  This script
does it on a **copy** next to the source, so an interruption leaves nothing
behind but a stray file that no other file refers to.

The copy has to sit in the same directory as the original: `lake env lean`
resolves nothing relative to the file, but the temporary name is kept next to
the source so that a reader who finds it knows what it came from.

Usage:

    python3 scripts/check_axioms.py MartingaleProblems name [name ...]

where the first argument is the roadmap directory under `TauCeti/` and the rest
are declaration names.  Exit code is that of `lake env lean`; a declaration that
does not exist is reported by Lean as an error and shows up in the output.
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MAIN = pathlib.Path("/home/pfaffelh/Code/lean/journal")


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    roadmap, names = argv[0], argv[1:]
    src = ROOT / "Journal/Blog/MartingaleProblem/TauCeti" / roadmap / "Suggested.lean"
    if not src.exists():
        print(f"no such file: {src}")
        return 2
    tmp = src.with_name("Suggested.axioms.tmp.lean")
    tmp.write_text(
        src.read_text() + "\n" + "".join(f"#print axioms {n}\n" for n in names))
    try:
        proc = subprocess.run(["lake", "env", "lean", str(tmp)],
                              cwd=MAIN, capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        for line in out.splitlines():
            if "depends on axioms" in line or "error" in line:
                print(line.replace(str(tmp), str(src)))
        print(f"rc {proc.returncode}")
        return proc.returncode
    finally:
        tmp.unlink(missing_ok=True)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
