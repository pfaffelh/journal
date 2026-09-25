#!/usr/bin/env python3
"""Ersetzt in `MartingaleProblems/Suggested.lean`, Abschnitt `ContinuousHittingTime`, den Beweis
von `measure_hittingAfter_le_eq_two_mul_of_isBrownianReal` durch einen über den pfadweisen
Hilfssatz `hittingAfter_Ici_le_iff_le_iSup` und hängt die Rekurrenz aus
`scripts/_dev_recurrence.lean` an.  Einmalig; bricht ab, wenn die Rekurrenz schon steht."""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, 'scripts/_dev_recurrence.lean')
TGT = os.path.join(ROOT, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')

dev = open(DEV).read()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')


def decl(name):
    """Der Text einer Deklaration aus der Arbeitsdatei, ohne ihren Kurzkommentar."""
    i = min(k for k in (body.find('theorem ' + name + ' '), body.find('theorem ' + name + '\n'))
            if k >= 0)
    j = body.find('\n\n', i)
    txt = body[i:] if j < 0 else body[i:j]
    return txt


LEMMA_DOC = '''/-- **At a continuous real path, the first passage time at `a` is at most `T` exactly when the
running maximum up to `T` reaches `a`.**  `MeasureTheory.hittingAfter_le_iff_of_isClosed` turns
`τ_a ≤ T` into `∃ t ≤ T, a ≤ X t`, and a continuous path attains its maximum on the compact
`[0, T]` (`IsCompact.exists_isMaxOn`), so this is `a ≤ ⨆ t ≤ T, X t`.  The supremum is over a set
bounded above, because the path is continuous on a compact set, and is not a junk value. -/
'''

PASSAGE_DOC = '''/-- **The law of the first passage time of Brownian motion.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, `0 < T` and `0 < a`, the
first time `τ_a = hittingAfter X [a, ∞) 0` at which `X` reaches `a` satisfies
`Q (τ_a ≤ T) = 2 Q (a ≤ X T)`.

At every continuous path `{τ_a ≤ T} = {a ≤ sup_{t ≤ T} X t}`
(`MeasureTheory.hittingAfter_Ici_le_iff_le_iSup`).  The paths are continuous off one null set
(`cont`), and `MeasureTheory.measure_le_iSup_eq_two_mul_of_isBrownianReal` gives the value.  `τ_a`
is valued in `WithTop ℝ≥0` and is `⊤` on paths that never reach `a`; that value is the truth and
not a junk value, and `{τ_a ≤ T}` does not contain those paths.  The event need not be
measurable; `Q` is evaluated as an outer measure.  **Not an existence statement**: `X` is a
hypothesis. -/
'''

PASSAGE = '''theorem measure_hittingAfter_le_eq_two_mul_of_isBrownianReal
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'}
    {X : ℝ≥0 → Ω' → ℝ} (hX : IsBrownianReal X Q) (hm : ∀ t, Measurable (X t))
    {T : ℝ≥0} (hT : 0 < T) {a : ℝ} (ha : 0 < a) :
    Q {ω | hittingAfter X (Ici a) 0 ω ≤ T} = 2 * Q {ω | a ≤ X T ω} := by
  rw [← measure_le_iSup_eq_two_mul_of_isBrownianReal hX hm hT ha]
  refine measure_congr ?_
  filter_upwards [hX.cont] with ω hω
  change (hittingAfter X (Ici a) 0 ω ≤ T) = (a ≤ ⨆ t : Iic T, X t ω)
  exact propext (hittingAfter_Ici_le_iff_le_iSup hω a T)'''

GAUSS_DOC = '''/-- **The standard Gaussian gives mass `1/2` to `(0, ∞)`**, in the form `2 * N (0, ∞) = 1`.
`N (0, ∞) = N (-∞, 0)` by `ProbabilityTheory.gaussianReal_map_neg`, `N {0} = 0` by
`ProbabilityTheory.gaussianReal_absolutelyContinuous`, and the two half-lines with the point
cover `ℝ`.  Mathlib states no mass of a half-line under `gaussianReal`. -/
'''

REC_DOC = '''/-- **Brownian motion reaches every level: the first passage time is finite almost surely.**
For `ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates and every real `a`,
`hittingAfter X [a, ∞) 0 ≠ ⊤` for `Q`-almost every `ω`.

For `a ≤ 0` this is `X 0 = 0` almost surely
(`ProbabilityTheory.IsPreBrownianReal.eval_zero_ae_eq_zero`).  For `0 < a`,
`Q (τ_a ≤ k + 1) = 2 Q (a ≤ X (k+1))` by
`MeasureTheory.measure_hittingAfter_le_eq_two_mul_of_isBrownianReal`, and
`Q (a ≤ X t) = N [a / √t, ∞)` for the standard Gaussian `N`
(`ProbabilityTheory.gaussianReal_div_const`), which increases to `N (0, ∞) = 1/2`
(`MeasureTheory.two_mul_gaussianReal_Ioi_zero`).  So `Q (τ_a = ⊤) + 2 Q (a ≤ X (k+1)) ≤ 1` for
every `k`, and in the limit `Q (τ_a = ⊤) = 0`.

The one step that needs care is the complement: `{τ_a = ⊤}` lies in the complement of
`{τ_a ≤ k + 1}`, and `Q (A) + Q (Aᶜ) = 1` asks `A` to be null measurable
(`MeasureTheory.measure_add_measure_compl₀`).  `{τ_a ≤ T}` is almost surely equal to the preimage
of `[a, ∞)` under `SkorokhodSpace.supOn T` and the path map of the càdlàg modification of
`MeasureTheory.isCadlagMPSolution_of_isBrownianReal`, which is measurable
(`SkorokhodSpace.measurable_supOn`).  **Not an existence statement**: `X` is a hypothesis. -/
'''

s = open(TGT).read()
if 'theorem ae_hittingAfter_ne_top_of_isBrownianReal' in s:
    raise SystemExit('Rekurrenz steht schon')
start = s.index('/-- **The law of the first passage time of Brownian motion.**')
end = s.index('\nend ContinuousHittingTime\n')
new = (LEMMA_DOC + decl('hittingAfter_Ici_le_iff_le_iSup') + '\n\n'
       + PASSAGE_DOC + PASSAGE + '\n\n'
       + GAUSS_DOC + decl('two_mul_gaussianReal_Ioi_zero') + '\n\n'
       + REC_DOC + decl('ae_hittingAfter_ne_top_of_isBrownianReal') + '\n')
s = s[:start] + new + s[end:]
open(TGT, 'w').write(s)
print('eingefügt')
