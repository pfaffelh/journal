#!/usr/bin/env python3
"""Count the two step path processes against each other: the state dependent
`jumpProcess` and the path dependent `jumpProcessF`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_pathdep.py`.

The question this answers is the one the path dependent variant raises.  Its
ground floor -- the existence of the inverse of the cumulated rate -- costs
thirty times what the state dependent jump times cost, and `count_pathdep.py`
measures that.  The question left over is whether the surcharge is *once* or
*per statement*, and the first statement that builds on the jump times rather
than supplying them is the process itself.  So the two groups here are the same
five statements twice: the definition, the step path property, the càdlàg
property, the value before the first jump, and the value at the origin.

A declaration named in neither group but matched by the pattern is ignored; a
declaration named in a group and not found in the source is reported, since that
would make the comparison silently wrong.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "the state dependent process (a division)": [
        "jumpProcess",
        "isStepPath_jumpProcess",
        "isCadlagPath_jumpProcess",
        "jumpProcess_of_lt_jumpTime_one",
        "jumpProcess_zero",
    ],
    "the path dependent process (an inverse)": [
        "jumpProcessF",
        "isStepPath_jumpProcessF",
        "isCadlagPath_jumpProcessF",
        "jumpProcessF_of_lt_jumpTimeF_one",
        "jumpProcessF_zero",
    ],
}

DECL = re.compile(r"^(?:@\[[^\]]*\] )?(?:theorem|lemma|noncomputable def|def) (\S+)")


def code_lines(lines: list[str]) -> dict[str, int]:
    """Code lines per declaration: doc comments, `--` comments and blank lines out."""
    counts: dict[str, int] = {}
    cur = None
    indoc = False
    for line in lines:
        s = line.strip()
        if s.startswith("/-"):
            indoc = True
        if indoc:
            if s.endswith("-/"):
                indoc = False
            continue
        if s.startswith("--") or s == "":
            continue
        m = DECL.match(line)
        if m:
            cur = m.group(1)
            counts.setdefault(cur, 0)
        elif line[:1] not in (" ", "\t"):
            # a top level line that is not a declaration ends the previous one
            cur = None
        if cur is not None:
            counts[cur] += 1
    return counts


def main() -> None:
    counts = code_lines(SRC.read_text().split("\n"))
    missing = []
    for title, names in GROUPS.items():
        total = 0
        for n in names:
            if n not in counts:
                missing.append(n)
                continue
            total += counts[n]
        print(f"{title}: {len(names)} declarations, {total} code lines")
        for n in names:
            if n in counts:
                print(f"    {n}: {counts[n]}")
    if missing:
        print("not found in the source (fix this script): " + ", ".join(missing))


if __name__ == "__main__":
    main()
