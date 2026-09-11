#!/usr/bin/env python3
"""Count declarations and code lines of the transfer of non explosion across
`posRate`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py`, `count_yule.py`, `count_yule_master.py`,
`count_yule_law.py` and `count_coupling.py`.

Unlike those, the statements counted here do **not** form a section of their
own: they sit inside `AbsorbingRate` and `LinearBirthDeath`, next to the
statements they are about.  So they are located by name, and a name that is not
found is reported rather than silently counted as zero -- an absent declaration
must not look like a cheap one.

A declaration is counted from its `theorem` line to the line before the next
top level opener (a doc comment, another declaration, a section marker).  Doc
comments are therefore excluded from the code line count and included in the
"with docs" count, as in the sibling scripts.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 the transfer at one sample point": [
        "mem_nonExplosiveE_posRate_of_mem",
    ],
    "G2 the almost sure form": [
        "ae_mem_nonExplosiveE_posRate",
    ],
    "G3 the linear birth and death instance": [
        "ae_mem_nonExplosiveE_posRate_linearBirthDeath",
    ],
}

OPENER = re.compile(
    r"^(/-|theorem |lemma |def |noncomputable |instance |section |end |variable )"
)
DECL = re.compile(r"^(?:theorem|lemma|noncomputable def|def) (\S+)")


def span(lines: list[str], name: str) -> tuple[int, int] | None:
    """The half open line range of the declaration `name`, or `None`."""
    start = None
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m and m.group(1) == name:
            start = i
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if OPENER.match(lines[j]):
            end = j
            break
    return (start, end)


def code_lines(seg: list[str]) -> int:
    n = 0
    indoc = False
    for l in seg:
        s = l.strip()
        if s.startswith("/-"):
            indoc = True
        if indoc:
            if s.endswith("-/"):
                indoc = False
            continue
        if s.startswith("--") or s == "":
            continue
        n += 1
    return n


def main() -> None:
    lines = SRC.read_text().split("\n")
    missing = []
    total_code = 0
    total_decl = 0
    for key, names in GROUPS.items():
        ncode = 0
        ndecl = 0
        for name in names:
            sp = span(lines, name)
            if sp is None:
                missing.append(name)
                continue
            ncode += code_lines(lines[sp[0] : sp[1]])
            ndecl += 1
        print(f"{key}: {ndecl} declarations, {ncode} code lines")
        total_code += ncode
        total_decl += ndecl
    print(f"total: {total_decl} declarations, {total_code} code lines")
    if missing:
        print("declarations not found (fix this script or the source): "
              + ", ".join(missing))


if __name__ == "__main__":
    main()
