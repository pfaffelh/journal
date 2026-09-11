#!/usr/bin/env python3
"""Count declarations and code lines of `section YuleMasterEquation`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py` and `count_yule.py`.

The section is the third measurement of the comparison of routes to the one
dimensional laws of the Yule process.  Two groups are counted separately because
they answer different questions.  The *bridge* is what it costs to make the
master equation speak about the process of the rate itself rather than about the
lifted rate it is written in; the *equation* is the master equation on the Yule
data.  A declaration in neither set is a mistake in this script, not in the
source, so it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 bridge from the lifted rate to the process": {
        "integrable_stateIndicator_jumpProcess",
        "integral_comp_jumpProcess_eq_sub",
        "jumpLaw_posRate_eq",
    },
    "G2 the master equation on the Yule data": {
        "yule_masterEquation",
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
                 if l.strip() == "section YuleMasterEquation")
    end = next(i for i, l in enumerate(lines, 1)
               if l.strip() == "end YuleMasterEquation")
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
