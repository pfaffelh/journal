#!/usr/bin/env python3
"""Hängt die Aussagen aus `scripts/_dev_cosh.lean` in `MartingaleProblems/Suggested.lean`
ein: das Erwartungslemma hinter `martingale_exp_of_isPreBrownianReal`, die beiden
cosh-Aussagen ans Ende des Abschnitts `FirstPassageLaplace`; und kürzt den
`hint`-Schritt der Laplace-Aussage auf das Erwartungslemma.  Nur Entwicklungswerkzeug."""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
P = ROOT / 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = P.read_text()
dev = (ROOT / 'scripts/_dev_cosh.lean').read_text()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')
d1, d2 = body.split('\n\ntheorem ')
d2 = 'theorem ' + d2

doc1 = """/-- **The exponential martingale has expectation `1`.**  For
`ProbabilityTheory.IsPreBrownianReal X Q`, every real `θ` and every `t`,
`E[exp (θ X t - θ ^ 2 t / 2)] = 1`: this is the moment generating function of
`gaussianReal 0 t` at `θ` (`ProbabilityTheory.mgf_gaussianReal`) times `exp (-θ ^ 2 t / 2)`. -/
"""
doc2 = """/-- **The Laplace transform of the exit time of Brownian motion from `(-a, a)`, for every path
continuous.**  For `ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates and **every**
path continuous, `0 < a` and `0 < r`, the exit time `τ = hittingAfter X ((-∞, -a] ∪ [a, ∞)) 0`
satisfies `E[exp (-r τ)] = 1 / cosh (a √(2 r))`.

With `θ = √(2 r)`, the sum of the two exponential martingales at `θ` and `-θ`
(`MeasureTheory.martingale_exp_of_isPreBrownianReal`) is `exp (-r t) (exp (θ X t) + exp (-θ X t))`.
Up to `τ` the path is in `[-a, a]` (`MeasureTheory.mem_Icc_of_le_hittingAfter_of_continuous`), so
the stopped sum is at most `2 exp (θ a)`; at `τ` the path is at `-a` or at `a`
(`MeasureTheory.ae_stoppedValue_hittingAfter_eq_or_eq_of_continuous`), and in either case the sum
is `2 cosh (θ a) exp (-r τ)` — the symmetry of the interval is what makes the value at `τ`
independent of the side of exit.  Optional sampling at `τ ∧ n` and bounded convergence give
`2 cosh (θ a) E[exp (-r τ)] = 2`.  **Not an existence statement**: `X` is a hypothesis. -/
"""
doc3 = """/-- **The Laplace transform of the exit time of Brownian motion from `(-a, a)`.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, `0 < a` and `0 < r`,
`E[exp (-r τ)] = 1 / cosh (a √(2 r))` for `τ = hittingAfter X ((-∞, -a] ∪ [a, ∞)) 0`, with no
hypothesis on every path; through the same modification as
`MeasureTheory.integral_exp_neg_hittingAfter_Ici_of_isBrownianReal`.  **Not an existence
statement**: `X` is a hypothesis. -/
"""
d3 = """theorem integral_exp_neg_hittingAfter_abs_of_isBrownianReal
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'}
    {X : ℝ≥0 → Ω' → ℝ} (hX : IsBrownianReal X Q) (hm : ∀ t, Measurable (X t))
    {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 < r) :
    ∫ ω, Real.exp (-r * ((hittingAfter X (Iic (-a) ∪ Ici a) 0 ω).untopA : ℝ)) ∂Q
      = (Real.cosh (a * Real.sqrt (2 * r)))⁻¹ := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hX.cont)
  classical
  set X' : ℝ≥0 → Ω' → ℝ := fun t ω ↦ if ω ∈ N then 0 else X t ω
  have hcont : ∀ ω, Continuous (X' · ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [X', ite_eq_left hω]
      exact continuous_const
    · simp only [X', ite_eq_right hω]
      exact not_not.1 fun h ↦ hω (hsub h)
  have hm' : ∀ t, Measurable (X' t) := fun t ↦ Measurable.ite hNm measurable_const (hm t)
  have hae : ∀ᵐ ω ∂Q, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hX' : IsBrownianReal X' Q :=
    { toIsPreBrownianReal := hX.toIsPreBrownianReal.congr fun t ↦ by
        filter_upwards [hae] with ω hω
        simp only [X', hω, ite_false]
      cont := ae_of_all _ hcont }
  rw [← integral_exp_neg_hittingAfter_abs_of_continuous hX' hm' hcont ha hr]
  refine integral_congr_ae ?_
  filter_upwards [hae] with ω hω
  have h : hittingAfter X' (Iic (-a) ∪ Ici a) 0 ω = hittingAfter X (Iic (-a) ∪ Ici a) 0 ω := by
    simp only [hittingAfter, X', hω, ite_false]
  rw [h]
"""
a1 = '\nend BrownianMartingale\n'
assert s.count(a1) == 1
s = s.replace(a1, '\n' + doc1 + d1 + '\n' + a1)
a2 = '\nend FirstPassageLaplace\n'
assert s.count(a2) == 1
s = s.replace(a2, '\n' + doc2 + d2 + '\n\n' + doc3 + d3 + a2)

old_hint = """  have hint : ∀ n, ∫ ω, stoppedValue M (ρ n) ω ∂Q = 1 := fun n ↦ by
    rw [integral_stoppedValue_eq_of_rightContinuous hM hrc (hρ n) (hρj n)]
    have hmgf := mgf_gaussianReal (hX.toIsPreBrownianReal.hasLaw_eval ((n : ℕ) : ℝ≥0)) θ
    rw [mgf] at hmgf
    have hsplit : (fun ω ↦ M ((n : ℕ) : ℝ≥0) ω)
        = fun ω ↦ Real.exp (-(θ ^ 2 * ((n : ℕ) : ℝ≥0) / 2)) * Real.exp (θ * X (n : ℝ≥0) ω) := by
      funext ω
      simp only [hM_def, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit, integral_const_mul, hmgf, ← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
"""
new_hint = """  have hint : ∀ n, ∫ ω, stoppedValue M (ρ n) ω ∂Q = 1 := fun n ↦ by
    rw [integral_stoppedValue_eq_of_rightContinuous hM hrc (hρ n) (hρj n)]
    exact integral_exp_sub_eq_one_of_isPreBrownianReal hX.toIsPreBrownianReal θ _
"""
assert s.count(old_hint) == 1
s = s.replace(old_hint, new_hint)
P.write_text(s)
print('ok')
