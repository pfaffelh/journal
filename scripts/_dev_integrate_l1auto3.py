#!/usr/bin/env python3
"""Fuegt die Sprungschranke (Schritt 3 von `lem:L1auto`) aus `_dev_l1auto3.lean` vor
`end RunningSupremum` in `MartingaleProblems/Suggested.lean` ein (Lauf 2026-09-25, 21:03 UTC)."""
d = open('scripts/_dev_l1auto3.lean').read()
body = d[d.index("theorem norm_lt_of_lt_supHittingTime"):d.index("end RunningSupremum3")]
body = body.replace("theorem norm_lt_of_lt_supHittingTime", """/-- Before the hitting time the norm is below the level. -/
theorem norm_lt_of_lt_supHittingTime""", 1)
body = body.replace("theorem norm_stoppedProcess_supHittingTime_le", """/-- **`‖Y^{τ_n}‖ ≤ n + c`**, Step 3 of the proof of `lem:L1auto`, for a path with `Y 0 = 0`, left
limits, and jumps bounded by `c`.  Before `τ_n` the norm is below `n`; at `τ_n > 0` the left limit
has norm at most `n`, and the jump adds at most `c`.

-- nach BrownianMotion, StochasticIntegral/LocalizingLeastGE.lean:107 (0d5b6eb),
-- `stoppedAtNorm_le_add_jump`, mit dem laufenden Supremum statt `‖Y‖`.

The jump bound is stated through the left limit and only at `t > 0`: at `0` the left
neighbourhood filter of `ℝ≥0` is `⊥`, every `l` is a limit along it, and the bound would say
nothing true; `Y 0 = 0` takes its place.  The indicator of `{⊥ < τ_n}` that `Locally` adds is not
in the statement; it only lowers the norm. -/
theorem norm_stoppedProcess_supHittingTime_le""", 1)
p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = open(p).read()
assert 'norm_stoppedProcess_supHittingTime_le' not in s
k = s.rindex("end RunningSupremum")
s = s[:k] + body.lstrip('\n') + s[k:]
open(p, 'w').write(s)
print('ok')
