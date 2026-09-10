#!/usr/bin/env python3
"""Count code lines per route in the YuleProcess section of MartingaleProblems/Suggested.lean.

Standalone: anchors its path at the worktree root and needs no arguments.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

G1 = {
    "linearDeath_zero",
    "birthDeathRate_yule_apply",
    "isMarkovKernel_yuleKernel",
    "yuleKernel_apply",
    "jumpApply_yule",
    "ae_mem_nonExplosiveE_yule",
    "yule_isLocalMPSolution",
}


def main() -> None:
    lines = SRC.read_text().split("\n")
    start = next(i for i, l in enumerate(lines, 1) if l.strip() == "section YuleProcess")
    end = next(i for i, l in enumerate(lines, 1) if l.strip() == "end YuleProcess")
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

    counts = {"G1 Yule instance": [0, 0], "G2 master equation": [0, 0]}
    cur = None
    for l in code:
        m = re.match(r"^(?:theorem|lemma|noncomputable def|def) (\S+)", l)
        if m:
            cur = "G1 Yule instance" if m.group(1) in G1 else "G2 master equation"
            counts[cur][1] += 1
        if cur:
            counts[cur][0] += 1

    for k, (nlines, ndecl) in counts.items():
        print(f"{k}: {ndecl} declarations, {nlines} code lines")
    print(f"section total: {len(code)} code lines, {end - start + 1} lines with docs")


if __name__ == "__main__":
    main()
