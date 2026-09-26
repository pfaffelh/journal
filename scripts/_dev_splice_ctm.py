#!/usr/bin/env python3
"""Hängt den Abschnitt `ContinuousTimeMartingales` (Aufgabe A, Schritte A1 und A2, Lauf vom
2026-09-26 07:03 UTC) aus `scripts/_dev_ctm1.lean` an `MartingaleProblems/Suggested.lean` an.
Läuft nur einmal: steht der Abschnitt schon da, bricht es ab."""
import os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, 'scripts/_dev_ctm1.lean')
DST = os.path.join(ROOT, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')

dst = open(DST).read()
if 'section ContinuousTimeMartingales' in dst:
    sys.exit('Abschnitt steht schon da')
dev = open(DEV).read()
body = dev[dev.index('section ContinuousTimeMartingales'):]
body = body.replace('variable {Ω : Type*} {m : MeasurableSpace Ω}\n\n', '', 1)

DOC = '''/-! ## Continuous time martingales: optional sampling for submartingales

Milestone 8.  The martingale half of optional sampling in continuous time stands above
(`stoppedValue_ae_eq_condExp`, `martingale_stoppedProcess`); this section is the submartingale
half, `Submartingale.stoppedValue_min_le_condExp`, for a bounded stopping time, almost everywhere
right continuous paths, and **no bound on the paths**.

The route:

* **the dyadic grid as an `ℕ`-indexed process.**  `dyadStop j ρ n` takes its values in the grid
  `dyadGrid j n`, a monotone sequence of times, and its index on the grid, `dyadIndex`, is a
  stopping time for the reindexed filtration `Filtration.comp`.  Mathlib's discrete optional
  stopping, `Submartingale.expected_stoppedValue_mono`, then applies verbatim
  (`Submartingale.integral_stoppedValue_dyadStop_mono`), and its set form gives the conditional
  bound `Y_{ρ_n} ≤ E[Y_j | ·]` on the grid (`Submartingale.stoppedValue_dyadStop_ae_le_condExp`).
* **integrability without a bound on the paths**, by Fatou along the approximations, whose `L¹`
  norms are at most `2 E[(Y j)⁺] - E[Y 0]`
  (`Submartingale.integrable_stoppedValue_of_rightContinuous`).
* **the passage to the limit.**  For a martingale the approximations are conditional expectations
  of one function and uniformly integrable for free; for a submartingale the conditional bound
  controls them only from above.  Cutting at `-K` supplies the missing side: `Y ⊔ -K` is a
  submartingale bounded below, so its approximations are uniformly integrable
  (`uniformIntegrable_of_le_condExp`) and Vitali applies
  (`Submartingale.integral_stoppedValue_mono_of_ge`); `K → ∞` is dominated convergence against
  `|Y_ρ|` (`Submartingale.integral_stoppedValue_mono`).  No backward submartingale and no Doob
  decomposition in continuous time are needed.
* **the conditional form** from the expectation form at the auxiliary time equal to `τ ∧ σ` on the
  test set and to `τ` off it.

The filtration is the raw one: no `[𝓕.IsRightContinuous]`, no completeness. -/

'''

A2 = '''
/-- **`Martingale.stoppedProcess_of_rightContinuous`**, the name the roadmap gives to
`martingale_stoppedProcess`: the stopped process of a progressive, almost everywhere right
continuous martingale is a martingale, for an arbitrary stopping time and the raw filtration. -/
theorem MeasureTheory.Martingale.stoppedProcess_of_rightContinuous (hY : Martingale Y 𝓕 P)
    (hprog : IsStronglyProgressive 𝓕 Y)
    (hrc : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Tendsto (fun r ↦ Y r ω) (𝓝[≥] s) (𝓝 (Y s ω)))
    {τ : Ω → ENNReal} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess Y τ) 𝓕 P :=
  martingale_stoppedProcess hY hprog hrc hτ

/-- **Emptiness check for `Submartingale.stoppedValue_min_le_condExp`**: the zero process meets
every hypothesis. -/
theorem Submartingale.stoppedValue_min_le_condExp_zero {j : ℝ≥0} {τ σ : Ω → ENNReal}
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) (hτj : ∀ ω, τ ω ≤ (j : ENNReal)) :
    stoppedValue (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) (τ ⊓ σ)
      ≤ᵐ[P] P[stoppedValue (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) τ | hσ.measurableSpace] :=
  (martingale_zero ℝ 𝓕 P).submartingale.stoppedValue_min_le_condExp
    (isStronglyProgressive_const 𝓕 0) (Filter.Eventually.of_forall fun _ _ ↦ tendsto_const_nhds)
    hτ hσ hτj

end ContinuousTimeMartingales
'''
body = body.replace('\nend ContinuousTimeMartingales\n', A2, 1)
body = body.replace('section ContinuousTimeMartingales\n', 'section ContinuousTimeMartingales\n\n' + DOC, 1)
for name in ['theorem aestronglyMeasurable_stoppedValue_dyadStop',
             'theorem MeasureTheory.Submartingale.integrable_stoppedValue_dyadStop ']:
    i = body.index(name)
    j = body.rfind('\n/--', 0, i)
    if j != -1 and body.count('\n', j, i) < 6:
        body = body[:j] + '\nomit [IsFiniteMeasure P] in' + body[j:]
    else:
        body = body[:i] + 'omit [IsFiniteMeasure P] in\n' + body[i:]
with open(DST, 'a') as fh:
    fh.write('\n' + body)
print('angehängt:', body.count('\ntheorem '), 'Sätze,', body.count('\nnoncomputable def '), 'Definitionen')
