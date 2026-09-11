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
        "rateInverse_eq_of_cumulativeRateF",
        "rateInverse_le_iff",
        "setOf_rateInverse_le",
        "rateInverse_mono",
        "cumulativeRateF_congr",
        "rateInverse_congr",
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
    "G5 the junk value of the inverse": {
        "rateInverse_eq_zero_of_forall_lt",
        "cumulativeRateF_le_of_integrableOn",
        "rateInverse_eq_zero_of_integrableOn",
        "cumulativeRateF_rateInverse_ne",
        "jumpTimeF_eq_zero_of_integrableOn",
    },
    "G5' the witness of a finite total mass": {
        "expRate",
        "expRate_pos",
        "intervalIntegrable_expRate",
        "integrableOn_expRate",
        "integral_expRate",
        "not_tendsto_cumulativeRateF_expRate",
        "jumpTimeF_expRate_eq_zero",
    },
    "G6 the path dependent jump process": {
        "jumpProcessF",
        "isStepPath_jumpProcessF",
        "isCadlagPath_jumpProcessF",
        "jumpProcessF_of_lt_jumpTimeF_one",
        "jumpProcessF_zero",
        "jumpProcessF_const_eq_jumpProcess",
    },
    "G7 the Hawkes rate": {
        "hawkesRate",
        "le_hawkesRate",
        "hawkesRate_pos",
        "tendsto_cumulativeRateF_hawkes",
        "hawkesRate_zero_kernel",
    },
    "G8 the Hawkes fixed point, resolved by recursion": {
        "hawkesFrozen",
        "hawkesFrozen_congr",
        "le_hawkesFrozen",
        "hawkesFrozen_succ_of_lt",
        "hawkesStep",
        "hawkesJumpTime",
        "hawkesJumpTime_zero",
        "hawkesStep_succ_of_le",
        "hawkesStep_eq_of_le",
        "hawkesStep_eq_hawkesJumpTime",
        "hawkesJumpTime_succ",
        "cumulativeRateF_hawkesJumpTime",
        "hawkesFrozen_one",
        "hawkesFrozen_succ_of_le",
    },
    "G9 the frozen rate is the Hawkes rate of a counting measure": {
        "countingMeasure",
        "restrict_countingMeasure",
        "integral_countingMeasure_Ico",
        "hawkesFrozen_succ_eq_sum_range",
        "hawkesRate_countingMeasure_of_lt",
        "hawkesRate_countingMeasure",
    },
    "G10 the Hawkes jump times increase": {
        "hawkesJumpTime_nonneg",
        "hawkesJumpTime_one",
        "cumulativeRateF_hawkesFrozen_succ_of_le",
        "hawkesJumpTime_le_succ",
        "monotone_hawkesJumpTime",
        "strictMono_hawkesJumpTime",
    },
    "G11 the fixed point closed": {
        "hawkesJumpTime_succ_eq_rateInverse_hawkesRate",
        "jumpTimeF_hawkesRate_eq_hawkesJumpTime",
    },
    "G12 the Hawkes process": {
        "hawkesSelfRate",
        "hawkesSelfRate_apply",
        "hawkesProcess",
        "le_hawkesSelfRate",
        "hawkesSelfRate_pos",
        "tendsto_cumulativeRateF_hawkesSelfRate",
        "isStepPath_hawkesProcess",
        "isCadlagPath_hawkesProcess",
        "jumpTimeF_hawkesSelfRate",
        "hawkesProcess_eq_stepPath",
        "hawkesProcess_of_lt_first",
    },
    "G13 the integrability of the frozen rate, discharged on the kernel": {
        "intervalIntegrable_hawkesFrozen",
        "strictMono_hawkesJumpTime_of_kernel",
    },
    "G14 the inverse is measurable in a parameter": {
        "cumulativeRateF_nonneg",
        "measurable_cumulativeRateF",
        "measurable_rateInverse",
    },
    "G15 the Hawkes jump times are measurable": {
        "rateInverse_hawkesFrozen_sample",
        "hawkesStep_sample_congr",
        "hawkesJumpTime_sample_congr",
        "measurable_hawkesJumpTime",
        "measurable_uncurry_hawkesStepPath",
    },
    "G16 the filtration of a point process": {
        "jumpRecord",
        "measurable_jumpRecord",
        "jumpState",
        "measurable_jumpState",
        "pointFiltration",
        "measurableSet_record",
        "isStoppingTime_jumpTime",
        "measurable_stepPath_pointFiltration",
    },
    "G17 the Hawkes filtration, and the path filtration it replaces": {
        "measurable_hawkesJumpTime_apply",
        "hawkesFiltration",
        "isStoppingTime_hawkesJumpTime",
        "measurable_hawkesStepPath_hawkesFiltration",
        "hawkesPathFiltration",
        "hawkesPathFiltration_le_hawkesFiltration",
        "not_isStoppingTime_hawkesJumpTime_pathFiltration",
    },
    "G18 progressive measurability, and the compensating window": {
        "measurable_uncurry_stepPath_pointFiltration",
        "measurable_compensator_pointFiltration",
        "measurable_uncurry_hawkesStepPath_hawkesFiltration",
        "measurable_compensator_hawkesFiltration",
    },
    "G19 the generator of eq:pathgen, and the probe that it generalises": {
        "jumpApplyF",
        "jumpOperatorF",
        "jumpApplyF_state",
        "jumpOperatorF_state",
        "mpFamilyF_jumpOperatorF_state",
    },
    "G20 the rate that reads its own past, and its measurability": {
        "countingMeasure_eq_map_count",
        "integral_countingMeasure_eq_integral_count",
        "indicator_Ico_min_right",
        "measurable_min_jumpTime_pointFiltration",
        "measurable_uncurry_pointRate_pointFiltration",
        "measurable_uncurry_hawkesSelfRate_hawkesFiltration",
        "measurable_uncurry_hawkesJumpApplyF_hawkesFiltration",
        "measurable_compensator_of_uncurry_min",
        "measurable_compensator_hawkesJumpApplyF_hawkesFiltration",
    },
    "G21 the test process is progressively measurable": {
        "measurable_uncurry_compensator_of_uncurry_min",
        "isStronglyProgressive_of_measurable_uncurry_mpFamilyF",
        "isStronglyProgressive_mpFamilyF_hawkesStepPath",
    },
    "G22 the paths of the test process are right continuous": {
        "measurable_pointRate",
        "measurable_hawkesSelfRate_time",
        "compensator_eq_intervalIntegral",
        "intervalIntegrable_mul_bdd",
        "tendsto_nhdsGE_of_intervalIntegrable_mpFamilyF",
        "tendsto_nhdsGE_mpFamilyF_hawkesStepPath",
    },
    "G23 the window bound, and the third input it does not reach": {
        "abs_setIntegral_compensatorF_le",
        "bdd_mpFamilyF_of_bdd",
    },
    "G24 the truncated rate, and the mass it may still spend": {
        "truncRateF",
        "truncRateF_eq_indicator",
        "truncRateF_apply",
        "truncRateF_of_lt",
        "truncRateF_of_le",
        "truncRateF_nonneg",
        "intervalIntegrable_truncRateF",
        "cumulativeRateF_truncRateF",
        "cumulativeRateF_truncRateF_of_le",
        "cumulativeRateF_truncRateF_le",
        "rateInverse_truncRateF_of_le",
        "rateInverse_truncRateF_eq_zero_of_lt",
    },
    "G25 the window bound from a bound on the mass": {
        "abs_setIntegral_compensatorF_le_of_cumulated",
        "bdd_mpFamilyF_of_cumulated",
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
