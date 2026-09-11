#!/usr/bin/env python3
"""Count declarations and code lines of `section RateMonotone`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py`, `count_yule.py`, `count_yule_master.py` and
`count_yule_law.py`.

The section is the beginning of the coupling route, the third of the routes to
non explosion named for the Yule process.  Two groups are counted separately
because they answer different questions: the *domination* is the general
statement that non explosion is antitone in the rate, the *instance* is what
that statement does and does not give on the linear birth and death data.

A declaration in neither set is a mistake in this script, not in the source, so
it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 non explosion is antitone in the rate": {
        "mem_nonExplosiveE_of_rate_le",
        "nonExplosiveE_subset_of_rate_le",
    },
    "G2 the linear birth and death instance": {
        "mem_nonExplosiveE_yule_of_linearBirthDeath",
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
                 if l.strip() == "section RateMonotone")
    end = next(i for i, l in enumerate(lines, 1)
               if l.strip() == "end RateMonotone")
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
