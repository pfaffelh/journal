#!/usr/bin/env python3
"""Count declarations and code lines of the Lyapunov route in MartingaleProblems/Suggested.lean.

Standalone: anchors its path at the worktree root and needs no arguments.  The
criterion and its birth and death instances are counted separately, since the
first is general and the second is the part that replaces the trajectory
argument of `section LinearBirthDeath`.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

INSTANCES = {
    "ae_mem_nonExplosiveE_birthDeath_of_rate_le",
    "ae_mem_nonExplosiveE_linearBirthDeath_of_lyapunov",
    "ae_mem_nonExplosiveE_yule_of_lyapunov",
}


def main() -> None:
    lines = SRC.read_text().split("\n")
    start = next(i for i, l in enumerate(lines, 1) if l.strip() == "section Lyapunov")
    end = next(i for i, l in enumerate(lines, 1) if l.strip() == "end Lyapunov")
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

    counts = {"G1 criterion": [0, 0], "G2 birth and death instances": [0, 0]}
    cur = None
    for l in code:
        m = re.match(r"^(?:theorem|lemma|noncomputable def|def) (\S+)", l)
        if m:
            cur = "G2 birth and death instances" if m.group(1) in INSTANCES else "G1 criterion"
            counts[cur][1] += 1
        if cur:
            counts[cur][0] += 1

    for k, (nlines, ndecl) in counts.items():
        print(f"{k}: {ndecl} declarations, {nlines} code lines")
    print(f"section total: {len(code)} code lines, {end - start + 1} lines with docs")


if __name__ == "__main__":
    main()
