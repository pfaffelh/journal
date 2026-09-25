#!/usr/bin/env python3
"""Einmaliges Einbauskript des achtzehnten Laufs vom 2026-09-25, vierter Teil: hängt
`section ClockQuantile` aus `scripts/_dev_quantile.lean` hinter `end DualityBridge` in
`MartingaleProblems/Suggested.lean` an.  Bricht ab, statt halb zu schreiben, wenn eine erwartete
Stelle fehlt."""
import os
J = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = os.path.join(J, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
s = open(R).read()
if 'def clockQuantile' in s:
    raise SystemExit('schon eingebaut')
w = open(os.path.join(J, 'scripts/_dev_quantile.lean')).read()
w = w[w.index('section ClockQuantile'):w.index('end ClockQuantile') + len('end ClockQuantile')]
w = w.replace('ℝ≥0∞', 'ENNReal')
HEAD = '''/-! ### Toward `cor:atomless`: the time change and the quantile of a clock on `ℝ≥0`

`Q s = q [0, s)` and its quantile `Q^←`, capped at a horizon `b` so that the supremum is honest.
The substitution formula `eq:quantile` holds for **every** clock finite on `[0, s)`, in the
predictable convention (`restrict_Iio_eq_map_clockQuantile`,
`setIntegral_interval_eq_clockQuantile`): the quantile is constant on the gap an atom leaves in
the range of `Q`, and the gap carries exactly the atom's mass.  Atomlessness is spent in one
place only, `clockTime_clockQuantile`: `Q (Q^← z) = z`, which is what turns the increments of
`Φ (Q^← ·, Q^← ·)` into Lebesgue integrals over arbitrary intervals. -/

'''
anchor = 'end DualityBridge\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + HEAD + w + '\n', 1)
open(R, 'w').write(s)
print('eingebaut')
