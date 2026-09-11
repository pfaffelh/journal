#!/usr/bin/env python3
"""Count declarations and code lines of `section PathDependent`.

Standalone: anchors its path at the worktree root and needs no arguments, after
the pattern of `count_lyapunov.py`, `count_yule.py`, `count_yule_master.py`,
`count_yule_law.py`, `count_coupling.py`, `count_posrate_transfer.py` and
`count_bd_master.py`.

The four groups answer four different questions.  The *cumulated rate* is the
compensator along one sample point and carries the three analytic properties on
which everything rests; the *inversion* is the passage from those properties to
a time at which a given level is attained; the *jump times* are the definition
the whole variant is about, together with its defining equation; and the *probe*
is the specialisation back to the state dependent construction at a constant
rate.  Counting them apart is what makes the price of "an inverse instead of a
division" readable -- the state dependent jump times cost three declarations
(`jumpTime`, `jumpTime_zero`, `jumpTime_succ`) and no analysis at all.

A declaration in neither set is a mistake in this script, not in the source, so
it is reported rather than silently dropped.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean"

GROUPS = {
    "G1 the cumulated rate and its three properties": {
        "cumulativeRateF",
        "cumulativeRateF_zero",
        "cumulativeRateF_eq_intervalIntegral",
        "integrableOn_Ioc_of_rate",
        "cumulativeRateF_sub",
        "strictMonoOn_cumulativeRateF",
        "monotoneOn_cumulativeRateF",
        "continuousOn_cumulativeRateF",
        "tendsto_cumulativeRateF_atTop_of_le",
    },
    "G2 the inversion": {
        "rateInverse",
        "rateInverse_nonneg",
        "rateInverse_zero",
        "cumulativeRateF_rateInverse",
        "rateInverse_mono",
    },
    "G3 the jump times and their defining equation": {
        "jumpTimeF",
        "jumpTimeF_zero",
        "jumpTimeF_nonneg",
        "monotone_jumpTimeF",
        "jumpTimeF_succ_spec",
        "strictMono_jumpTimeF",
        "tendsto_jumpTimeF_atTop",
    },
    "G4 the probe against emptiness, a constant rate": {
        "cumulativeRateF_const",
        "intervalIntegrable_const_rate",
        "tendsto_cumulativeRateF_const",
        "rateInverse_const",
        "jumpTimeF_const",
        "jumpTimeF_const_eq_jumpTime",
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
                 if l.strip() == "section PathDependent")
    end = next(i for i, l in enumerate(lines, 1)
               if l.strip() == "end PathDependent")
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
        # the attribute prefix is optional: `@[simp] theorem ...` is a declaration too,
        # and the scripts this one is modelled on have no `@[simp]` in their sections.
        m = re.match(r"^(?:@\[[^\]]*\] )?(?:theorem|lemma|noncomputable def|def) (\S+)", l)
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
