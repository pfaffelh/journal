#!/usr/bin/env python3
"""Hängt den Abschnitt `ContinuousHittingTime` aus `scripts/_dev_hitting.lean` hinter
`end ReflectionPrinciple` in `MartingaleProblems/Suggested.lean` ein, mit Doc-Kommentaren.
Einmalig; bricht ab, wenn der Abschnitt schon steht."""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, 'scripts/_dev_hitting.lean')
TGT = os.path.join(ROOT, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')

dev = open(DEV).read()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')

DOCS = [
('theorem hittingAfter_mem_set_of_isClosed', '''/-- **A right-continuous path attains its hitting time of a closed set.**  If `t ↦ u t ω` is
continuous from the right at every time, `s` is closed, and the path enters `s` after `n`,
then `hittingAfter u s n ω` is a time `i ≥ n` with `u i ω ∈ s`.

Mathlib's `MeasureTheory.hittingAfter_mem_set` asks for `[WellFoundedLT ι]` instead, which
excludes `ℝ≥0`.  Here the infimum `i` of the entrance set `S` lies in the closure of `S`
(`csInf_mem_closure`) and `S ⊆ [i, ∞)`, so right continuity at `i` puts `u i ω` into the closure
of `u '' S ⊆ s` (`ContinuousWithinAt.mem_closure_image`), and `s` is closed. -/
'''),
('theorem hittingAfter_le_iff_of_isClosed', '''/-- **The hitting time of a closed set by a right-continuous path is at most `i` exactly when the
path is in `s` at some time of `[n, i]`.**  The continuous-time counterpart of
`MeasureTheory.hittingAfter_le_iff`, which carries `[WellFoundedLT ι]` and reads it only through
`MeasureTheory.hittingAfter_mem_set`; `MeasureTheory.hittingAfter_mem_set_of_isClosed` replaces
that input.  Without closedness the statement fails: the path `t ↦ t` hits `(1, ∞)` at time `1`
and is not in it at any time of `[0, 1]`. -/
'''),
('theorem measure_hittingAfter_le_eq_two_mul_of_isBrownianReal', '''/-- **The law of the first passage time of Brownian motion.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, `0 < T` and `0 < a`, the
first time `τ_a = hittingAfter X [a, ∞) 0` at which `X` reaches `a` satisfies
`Q (τ_a ≤ T) = 2 Q (a ≤ X T)`.

At every continuous path `{τ_a ≤ T} = {∃ t ≤ T, a ≤ X t} = {a ≤ sup_{t ≤ T} X t}`: the first
equality is `MeasureTheory.hittingAfter_le_iff_of_isClosed`, the second holds because a continuous
path attains its maximum on the compact `[0, T]` (`IsCompact.exists_isMaxOn`).  The paths are
continuous off one null set (`cont`), and
`MeasureTheory.measure_le_iSup_eq_two_mul_of_isBrownianReal` gives the value.  `τ_a` is valued in
`WithTop ℝ≥0` and is `⊤` on paths that never reach `a`; that value is the truth and not a junk
value, and `{τ_a ≤ T}` does not contain those paths.  The event need not be measurable; `Q` is
evaluated as an outer measure.  **Not an existence statement**: `X` is a hypothesis. -/
'''),
]
for k, v in DOCS:
    assert body.count(k) == 1, k
    body = body.replace(k, v + k, 1)

HEAD = '''/-! ### Hitting times in continuous time, and the first passage time of Brownian motion

Mathlib's results about `MeasureTheory.hittingAfter` that locate the hitting time carry
`[WellFoundedLT ι]`, so none of them applies over `ℝ≥0`.  For a closed set and a right-continuous
path the infimum is attained (`MeasureTheory.hittingAfter_mem_set_of_isClosed`), which gives the
characterisation `MeasureTheory.hittingAfter_le_iff_of_isClosed`, and with it the law of the first
passage time of Brownian motion from the reflection principle. -/

section ContinuousHittingTime

'''

s = open(TGT).read()
if 'section ContinuousHittingTime' in s:
    raise SystemExit('Abschnitt steht schon')
anchor = '\nend ReflectionPrinciple\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + HEAD + body + '\n\nend ContinuousHittingTime\n', 1)
open(TGT, 'w').write(s)
print('eingefügt')
