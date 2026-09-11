#!/usr/bin/env python3
"""Count declarations and code lines of `section LinearBirthDeathMasterEquation`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py`, `count_yule.py`, `count_yule_master.py`,
`count_yule_law.py` and `count_coupling.py`.

The three groups answer three different questions.  The *generator* is a
computation on the data and says what the equation is; the *integration step* is
the passage from an integral along the process to an expression in the one
dimensional laws, and is free of the birth and death data; the *equation* is the
assembly.  Counting them apart is what makes the comparison with
`count_yule_master.py` -- the same three groups for the pure birth case -- read
as a comparison and not as a total.

A declaration in neither set is a mistake in this script, not in the source, so
it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 the generator at a state indicator": {
        "jumpApply_linearBirthDeath_indicator",
        "jumpApply_linearBirthDeath_indicator_zero",
        "jumpApply_yule_indicator_of_linearBirthDeath",
    },
    "G2 the integration step, free of the data": {
        "integral_comp_jumpProcess_eq_add_sub",
    },
    "G3 the equation": {
        "linearBirthDeath_masterEquation",
    },
}


def group_of(name: str) -> str | None:
    for key, names in GROUPS.items():
        if name in names:
            return key
    return None


def main() -> None:
    lines = SRC.read_text().split("\n")
    start = next(i for i, l in enumerate(lines, 1)
                 if l.strip() == "section LinearBirthDeathMasterEquation")
    end = next(i for i, l in enumerate(lines, 1)
               if l.strip() == "end LinearBirthDeathMasterEquation")
    seg = lines[start - 1 : end]

    code = []
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
        code.append(l)

    counts = {k: [0, 0] for k in GROUPS}
    unclassified = []
    cur = None
    for l in code:
        m = re.match(r"^(?:theorem|lemma|noncomputable def|def) (\S+)", l)
        if m:
            cur = group_of(m.group(1))
            if cur is None:
                unclassified.append(m.group(1))
            else:
                counts[cur][1] += 1
        if cur:
            counts[cur][0] += 1

    for k in GROUPS:
        nlines, ndecl = counts[k]
        print(f"{k}: {ndecl} declarations, {nlines} code lines")
    print(f"section total: {len(code)} code lines, {end - start + 1} lines with docs")
    if unclassified:
        print("unclassified declarations (fix this script): " + ", ".join(unclassified))


if __name__ == "__main__":
    main()
