#!/usr/bin/env python3
"""Hängt den Abschnitt `ReflectionPrinciple` aus `scripts/_dev_onedimwalk.lean` hinter
`end RademacherData` in `MartingaleProblems/Suggested.lean` ein, mit Doc-Kommentaren.
Einmalig; bricht ab, wenn der Abschnitt schon steht."""
import os, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, 'scripts/_dev_onedimwalk.lean')
TGT = os.path.join(ROOT, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')

dev = open(DEV).read()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')
body = body.replace('variable {Ω : Type*}\n\n', '')

DOCS = {
'theorem ProbabilityMeasure.tendsto_measure_Ici_of_tendsto': '''/-- **Portmanteau with a moving boundary.**  If `μs → μ` weakly on `ℝ`, `μ` has no atom at `a`,
and `c i → a`, then `μs i [c i, ∞) → μ [a, ∞)`.

`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` covers a fixed set; here the
boundary moves with `i`.  The proof sandwiches `[c i, ∞)` between `(s, ∞)` and `[s', ∞)` for
fixed `s' < a < s`, reads the two halves of the portmanteau theorem there
(`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`,
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), and lets `s ↓ a`, `s' ↑ a` by
continuity of `μ` along `⋃ (a + 1/(k+1), ∞) = (a, ∞)` and `⋂ [a - 1/(k+1), ∞) = [a, ∞)`.  The atom
condition is read once, to identify `μ (a, ∞)` with `μ [a, ∞)` (`Ioi_ae_eq_Ici'`); no atom
condition is asked at `s` or `s'`, because the portmanteau halves are inequalities. -/
''',
'theorem tendsto_measure_le_eval_rescaledWalk_of_isBrownianReal': '''/-- **The one-dimensional central limit theorem along Donsker's theorem, with a moving level.**
For Donsker's data, `ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, a
horizon `0 < T` and levels `c n → a`,
`P (c n ≤ Φ n T) → Q (a ≤ √v · X T)`.

The law of `Φ n T` converges to that of `√v · X' T` by the continuous mapping theorem with a
null discontinuity set, `MeasureTheory.tendsto_of_measure_setOf_not_continuousAt_eq_zero`,
applied to the evaluation at `T`, which is continuous at every continuous path
(`SkorokhodSpace.continuousAt_eval_of_notMem_leftJumpSet`); `X'` is the modification of
`MeasureTheory.tendsto_map_rescaledWalk_of_isBrownianReal`, and `cont` puts almost every limit path
there.  The limit law is `gaussianReal 0 T` scaled by `√v`, absolutely continuous
(`ProbabilityTheory.gaussianReal_absolutelyContinuous`), so it has no atom at `a` and
`MeasureTheory.ProbabilityMeasure.tendsto_measure_Ici_of_tendsto` applies.  `0 < T` is where the
atom condition comes from: at `T = 0` the limit is `dirac 0`.  **Not an existence statement**:
`X` is a hypothesis. -/
''',
'theorem tendsto_rademacherSeq_le_sum_div_sqrt': '''/-- **The walk of fair signs at a moving level.**  For `ProbabilityTheory.IsBrownianReal X Q` with
measurable coordinates, `0 < T` and `c n → a`,
`P (c n √(n+1) ≤ S_{⌊T (n+1)⌋}) → Q (a ≤ X T)` under `rademacherSeq`.  This is
`MeasureTheory.tendsto_measure_le_eval_rescaledWalk_of_isBrownianReal` on the data of
`MeasureTheory.rademacherSeq`, with `v = 1`, the event rewritten from `Φ n T` to the partial sum.
It is the form in which the two summands of
`MeasureTheory.rademacherSeq_le_supOn_rescaledWalkPath` are passed to the limit. -/
''',
'theorem measure_le_iSup_eq_two_mul_of_isBrownianReal': '''/-- **The reflection principle for Mathlib's Brownian motion.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, `0 < T` and `0 < a`,
`Q (a ≤ ⨆ t ≤ T, X t) = 2 Q (a ≤ X T)`.

The proof is Billingsley's (*Convergence of Probability Measures*, §9): exact for the fair-sign
walk, then Donsker.  For the walk,
`P (a ≤ sup_{t ≤ T} Φ n) = P (S_N ≥ m) + P (S_N > m)` with `m = ⌈a √(n+1)⌉`
(`MeasureTheory.rademacherSeq_le_supOn_rescaledWalkPath`); both summands tend to `Q (a ≤ X T)` by
`MeasureTheory.tendsto_rademacherSeq_le_sum_div_sqrt`, the second squeezed between the levels
`m + 1` and `m`, so no integrality of `S_N` is read.  The laws of `sup_{t ≤ T} Φ n` converge to
that of `sup_{t ≤ T} X'` (`SkorokhodSpace.continuousAt_supOn` and the continuous mapping theorem
with a null discontinuity set), and the two halves of the portmanteau theorem give
`Q (a < sup) ≤ 2 Q (s ≤ X T)` for every `0 < s` and `2 Q (a ≤ X T) ≤ Q (a ≤ sup)`.  Letting
`s ↑ a` along `a - 1/(k+1)` closes the gap, by continuity of `s ↦ Q (s ≤ X T)` from the left,
which is continuity of a measure from above and asks for **no** atom condition.  In particular
it is **not** shown beforehand that `sup_{t ≤ T} X t` has no atoms; that falls out.

The supremum `⨆ t : Set.Iic T, X t ω` is Lean's `iSup` of reals and is the junk value `0` on an
unbounded family.  It is not read there: off one null set the path is continuous, hence bounded
on `[0, T]`, and the measure only sees the almost sure class of the event.  The event itself
need not be measurable; `Q` is evaluated as an outer measure.

**Not an existence statement**: `X` is a hypothesis, and `ProbabilityTheory.IsBrownianReal`
carries no existence statement. -/
''',
}

for k, d in DOCS.items():
    assert body.count(k + '\n') + body.count(k + ' ') >= 1, k
    body = body.replace(k, d + k, 1)

HEAD = '''/-! ### The reflection principle for Brownian motion

`MeasureTheory.measure_le_iSup_eq_two_mul_of_isBrownianReal`: for Mathlib's
`ProbabilityTheory.IsBrownianReal X Q`, `Q (a ≤ ⨆ t ≤ T, X t) = 2 Q (a ≤ X T)`, by the exact
reflection identity for the fair-sign walk and Donsker's theorem.  The inputs are a portmanteau
statement with a moving boundary on `ℝ`, the one-dimensional limit along Donsker's theorem, and
its instance on `MeasureTheory.rademacherSeq`.  `X` is a hypothesis throughout. -/

section ReflectionPrinciple

variable {Ω : Type*}

'''

src = open(TGT).read()
if 'section ReflectionPrinciple' in src:
    raise SystemExit('Abschnitt steht schon')
anchor = 'end RademacherData\n'
assert src.count(anchor) == 1
src = src.replace(anchor, anchor + '\n' + HEAD + body + '\n\nend ReflectionPrinciple\n', 1)
open(TGT, 'w').write(src)
print('eingefügt')
