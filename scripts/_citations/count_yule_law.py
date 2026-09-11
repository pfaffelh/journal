#!/usr/bin/env python3
"""Count declarations and code lines of `section YuleLaw`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py`, `count_yule.py` and `count_yule_master.py`.

The section solves the master equation of the Yule process and reads off the one
dimensional law.  Five groups are counted separately because they answer
different questions and only some of them are specific to the Yule data:

* the *law in time* is what has to be known about `jumpLaw` as a function of the
  time argument before any calculus applies to it;
* the *uniqueness* is the scalar linear equation and is about nothing else;
* the *candidate* is the closed formula and its derivative;
* the *solution* is the induction over the level, stated for an arbitrary family
  satisfying the equation and therefore free of the jump construction;
* the *Yule instance* is the substitution of the data.

A declaration in none of the sets is a mistake in this script, not in the
source, so it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 the one dimensional law as a function of time": {
        "measurable_jumpLaw",
        "abs_jumpLaw_le_one",
        "intervalIntegrable_jumpLaw",
        "abs_sub_mul_jumpLaw_le",
    },
    "G2 uniqueness for the scalar linear equation": {
        "eq_of_masterEquation",
    },
    "G3 the candidate and its derivative": {
        "hasDerivAt_expNeg",
        "hasDerivAt_yuleDensity_succ",
    },
    "G4 the solution of the equation, free of the construction": {
        "eq_yuleDensity_of_masterEquation",
    },
    "G5 the Yule instance": {
        "yule_masterEquation_zero",
        "jumpLaw_yule_init",
        "jumpLaw_yule_zero",
        "jumpLaw_yule_succ",
        "tsum_jumpLaw_yule_succ",
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
                 if l.strip() == "section YuleLaw")
    end = next(i for i, l in enumerate(lines, 1)
               if l.strip() == "end YuleLaw")
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
