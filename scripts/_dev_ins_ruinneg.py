#!/usr/bin/env python3
"""Hängt die beiden Aussagen aus `scripts/_dev_ruinneg.lean` vor Walds Identität
in `MartingaleProblems/Suggested.lean` ein.  Nur Entwicklungswerkzeug."""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
P = ROOT / 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = P.read_text()
dev = (ROOT / 'scripts/_dev_ruinneg.lean').read_text()
body = dev.split('namespace MeasureTheory\n', 1)[1].rsplit('end MeasureTheory', 1)[0].strip('\n')
d1, d2 = body.split('\n\ntheorem ')
d2 = 'theorem ' + d2
doc1 = """/-- **The other exit of the gambler's ruin, for every path continuous.**  Under the hypotheses
of `MeasureTheory.measure_stoppedValue_hittingAfter_eq_of_continuous`, `Q (X τ = -b) = a / (a + b)`.
The same computation with the indicator of `B = {X τ = -b}`: `X τ = a - (a + b) 1_B` almost
surely, and `E[X τ] = 0`.  It is not read off as `1 - b / (a + b)`: that would ask the two events
to be measurable as written, and the proof avoids that by working with a measurable version of
`X τ`.  **Not an existence statement**: `X` is a hypothesis. -/
"""
doc2 = """/-- **The other exit of the gambler's ruin for Brownian motion.**  For
`ProbabilityTheory.IsBrownianReal X Q` with measurable coordinates, `0 < a` and `0 < b`,
`Q (X τ = -b) = a / (a + b)` for `τ = hittingAfter X ((-∞, -b] ∪ [a, ∞)) 0`, with no hypothesis
on every path; through the same modification as
`MeasureTheory.measure_stoppedValue_hittingAfter_eq_of_isBrownianReal`.  **Not an existence
statement**: `X` is a hypothesis. -/
"""
anchor = "open scoped ENNReal in\n/-- **Wald's identity for Brownian motion with every path"
assert s.count(anchor) == 1
s = s.replace(anchor, doc1 + d1 + '\n\n' + doc2 + d2 + '\n\n' + anchor)
P.write_text(s)
print('ok')
