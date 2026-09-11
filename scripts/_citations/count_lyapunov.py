#!/usr/bin/env python3
"""Count declarations and code lines of the Lyapunov route in MartingaleProblems/Suggested.lean.

Standalone: anchors its path at the worktree root and needs no arguments.  Four
groups are counted separately, because they answer different questions.  The
*pathwise* criterion asks the Lyapunov inequality at every point the kernel can
reach; the *generator* criterion asks it of the average only, which is what the
literature asks and what carries `b x ≤ C (x+1)` with a free death rate.  Each
comes with its birth and death instances, which is the part that replaces the
trajectory argument of `section LinearBirthDeath`.

A declaration whose name is in none of the four sets is a mistake in this
script, not in the source, so it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 pathwise criterion": {
        "le_mul_exp_sum_of_lyapunov",
        "not_summable_inv_of_lyapunov",
        "ae_mem_nonExplosiveE_jumpMeasure_of_lyapunov",
        "jumpApply_le_of_lyapunov",
    },
    "G2 pathwise birth and death instances": {
        "ae_mem_nonExplosiveE_birthDeath_of_rate_le",
        "ae_mem_nonExplosiveE_linearBirthDeath_of_lyapunov",
        "ae_mem_nonExplosiveE_yule_of_lyapunov",
    },
    "G3 generator criterion": {
        "lyapunovWeight",
        "measurable_lyapunovWeight",
        "prod_lyapunovWeight_of_pos",
        "lintegral_chainKernel_lyapunov_le",
        "ae_absorb_or_not_summable_of_lintegral_le",
        "summable_iff_tsum_ofReal_ne_top",
        "measurableSet_summable_inv_comp",
        "measurableSet_absorb_or_not_summable",
        "ae_mem_nonExplosiveE_jumpMeasure_of_lintegral_le",
        "ae_mem_nonExplosiveE_jumpMeasure_of_lintegral_le_of_ne_top",
        "lintegral_ofReal_le_of_jumpApply_le",
        "ae_mem_nonExplosiveE_jumpMeasure_of_jumpApply_le",
    },
    "G4 generator birth and death instances": {
        "exists_bound_of_le_nat",
        "integrable_birthDeathKernel",
        "ae_mem_nonExplosiveE_birthDeath_of_birth_le",
        "ae_mem_nonExplosiveE_yule_of_jumpApply_le",
    },
    "G5 the criterion across the lift of the rate": {
        "ae_mem_nonExplosiveE_posRate_of_jumpApply_le",
        "ae_mem_nonExplosiveE_posRate_birthDeath_of_birth_le",
        "ae_mem_nonExplosiveE_posRate_yule",
    },
}


def group_of(name: str) -> str | None:
    for key, names in GROUPS.items():
        if name in names:
            return key
    return None


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
    pathwise = sum(counts[k][0] for k in ("G1 pathwise criterion",
                                          "G2 pathwise birth and death instances"))
    generator = sum(counts[k][0] for k in ("G3 generator criterion",
                                           "G4 generator birth and death instances"))
    print(f"pathwise route: {pathwise} code lines")
    print(f"generator route: {generator} code lines")
    print(f"section total: {len(code)} code lines, {end - start + 1} lines with docs")
    if unclassified:
        print("unclassified declarations (fix this script): " + ", ".join(unclassified))


if __name__ == "__main__":
    main()
