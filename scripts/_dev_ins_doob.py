dev = open('scripts/_dev_A5doob.lean').read()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')
docs = {
'theorem lintegral_enorm_sq_eq_of_isPreBrownianReal':
"""/-- **The second moment of a pre-Brownian motion, as a lower integral**: for
`ProbabilityTheory.IsPreBrownianReal X Q` with measurable coordinates,
`∫⁻ ‖X T‖ₑ ^ 2 = T`.  The variance of `gaussianReal 0 T` is `T`
(`ProbabilityTheory.IsPreBrownianReal.hasLaw_eval`, `ProbabilityTheory.variance_id_gaussianReal`),
the mean is `0`, and `‖x‖ₑ ^ 2 = ofReal (x ^ 2)` carries it to the lower integral
(`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`).  It is the right hand side of Doob's
`L²` inequality computed below, in the form that inequality is stated in. -/
""",
'theorem lintegral_biSup_enorm_sq_le_of_isBrownianReal':
"""/-- **Acceptance: Doob's `L²` inequality, computed for Brownian motion.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates and **every** path continuous,
`∫⁻ (⨆ t ≤ T, ‖X t‖ₑ) ^ 2 ≤ 4 T`.  It is `Martingale.lintegral_biSup_enorm_rpow_le` at `r = 2`,
whose constant `(r / (r - 1)) ^ r` is `4`, for the martingale `martingale_of_isPreBrownianReal`
and a countable dense subset of `ℝ≥0`, with the right hand side `4 ∫⁻ ‖X T‖ₑ ^ 2 = 4 T` from
`lintegral_enorm_sq_eq_of_isPreBrownianReal`.  The `L²` hypothesis of the general statement is
discharged by the same computation.  Continuity of **every** path, and not only of almost every
one, is asked because the general statement reads right continuity at every sample point. -/
""",
'theorem integral_norm_le_sqrt_of_isPreBrownianReal':
"""/-- **`E|X T| ≤ √T` for a pre-Brownian motion**, from `Var |X T| ≥ 0` and `E[X T ^ 2] = T`
(`ProbabilityTheory.variance_eq_sub`).  The exact value is `√(2T/π)`; it is not needed for the
acceptance example below and not proved here. -/
""",
'theorem measure_biSup_enorm_le_of_isBrownianReal':
"""/-- **Acceptance: Doob's maximal inequality, computed for Brownian motion, with the constant
`1`.**  Under the hypotheses of `lintegral_biSup_enorm_sq_le_of_isBrownianReal`,
`ε · Q {ε ≤ ⨆ t ≤ T, ‖X t‖ₑ} ≤ √T`.  It is `Martingale.measure_iSup_norm_le` followed by
`integral_norm_le_sqrt_of_isPreBrownianReal`.  The two sided window bound
`Submartingale.mul_measReal_le_biSup_enorm_le` would give `2 E|X T| - E[X 0] = 2 E|X T|` on these
data, which is the bound this example distinguishes from the classical one. -/
""",
}
for k, v in docs.items():
    assert k in body, k
    body = body.replace(k, v + k, 1)
p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = open(p).read()
anchor = "  rw [integral_congr_ae hval]\n  simp\n\nend ContinuousTimeMartingales"
assert s.count(anchor) == 1
s = s.replace(anchor, "  rw [integral_congr_ae hval]\n  simp\n\n" + body + "\n\nend ContinuousTimeMartingales")
open(p, 'w').write(s)
print("ok")
