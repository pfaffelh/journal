#!/usr/bin/env python3
"""Haengt den Abschnitt `RunningSupremum` aus `_dev_l1auto.lean` an
`MartingaleProblems/Suggested.lean` an, mit Doc-Kommentaren (Lauf 2026-09-25, 21:03 UTC)."""
d = open('scripts/_dev_l1auto.lean').read()
body = d[d.index("section RunningSupremum"):]
docs = [
("noncomputable def runningSup", """/-- **The running supremum of the norm**, `S_t = sup_{s ≤ t} ‖Y_s‖` of `lem:L1auto`, in `ℝ≥0∞`
so that no boundedness has to be proved before it can be written. -/
"""),
("theorem monotone_runningSup", "/-- The running supremum is nondecreasing, Step 1 of the proof of `lem:L1auto`. -/\n"),
("theorem runningSup_eq_of_dense", """/-- **For right continuous paths the running supremum is a supremum over a countable set**,
`eq:supcountable` of the manuscript: any dense `D` together with the endpoint `t` will do.  A
value `‖Y s‖` above the countable supremum would, by right continuity at `s`, persist on some
`[s, u)`, and `D` meets `(s, min u t)`. -/
"""),
("theorem measurable_runningSup", """/-- **The running supremum is adapted**, Step 1 of the proof of `lem:L1auto`, through the
countable supremum `runningSup_eq_of_dense` and `Measurable.biSup`.  Only right continuity of
the paths and adaptedness enter (`T2b`); no completeness. -/
"""),
("theorem exists_gt_runningSup_le", """/-- A strict upper bound of the running supremum at `t` survives a little beyond `t`.  This is
right continuity of the running supremum, in the one form in which it is used. -/
"""),
("noncomputable def supHittingTime", """/-- **The hitting time of the level `n` by the running supremum**, `τ^Y_n` of `lem:L1auto`.  The
infimum is taken in `ℝ≥0∞`, so that `sInf ∅ = ⊤`: a path whose running supremum stays below `n`
is never stopped. -/
"""),
("theorem supHittingTime_le_iff", """/-- **`{τ_n ≤ t} = {S_t ≥ n}`**, `eq:debutclosed`, Step 2 of the proof of `lem:L1auto`.  The
level set of the running supremum is closed from the right because the running supremum is right
continuous (`exists_gt_runningSup_le`), so the infimum is attained. -/
"""),
("theorem isStoppingTime_supHittingTime", """/-- **`τ^Y_n` is a strict stopping time**, i.e. one for the raw filtration `𝓕`.

This is where the construction differs from BrownianMotion's `isLocalizingSequence_leastGE`
(`BrownianMotion/StochasticIntegral/LocalizingLeastGE.lean:24`, `0d5b6eb`), which hits the level
by `‖Y‖` itself and gets the stopping time property from the début theorem, under
`[𝓕.IsComplete P] [𝓕.IsRightContinuous]`.  Hitting by the **running supremum** makes the event
`{τ_n ≤ t}` equal to `{n ≤ S_t}` (`supHittingTime_le_iff`), and `S_t` is `𝓕 t`-measurable by the
countable supremum (`measurable_runningSup`); neither completion nor right continuity of the
filtration is used. -/
"""),
]
for k, v in docs:
    assert k in body, k
    body = body.replace(k, v + k, 1)
body = body.replace("section RunningSupremum", """/-! ### The running supremum and its hitting times, `lem:L1auto`

Steps 1 and 2 of the proof of `lem:L1auto`: the running supremum of a right continuous adapted
process is adapted, and its hitting times are strict stopping times. -/

open scoped ENNReal

section RunningSupremum""", 1)
p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = open(p).read()
assert 'section RunningSupremum' not in s
s = s.rstrip('\n') + "\n\n" + body
open(p, 'w').write(s)
print('ok')
