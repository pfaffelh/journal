#!/usr/bin/env python3
"""Einmaliges Einbauskript des achtzehnten Laufs vom 2026-09-25: hängt `section Weighted` aus
`scripts/_dev_weighted.lean` (ohne die Stubs) und den Zeugen aus `scripts/_dev_witness.lean`
hinter `end AlphaBeta` in `MartingaleProblems/Suggested.lean` an.  Bricht ab, statt halb zu
schreiben, wenn eine erwartete Stelle fehlt."""
import os
J = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = os.path.join(J, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
s = open(R).read()
if 'duality_weighted' in s:
    raise SystemExit('schon eingebaut')
w = open(os.path.join(J, 'scripts/_dev_weighted.lean')).read()
w = w[w.index('section Weighted'):w.index('end Weighted') + len('end Weighted')]
z = open(os.path.join(J, 'scripts/_dev_witness.lean')).read()
z = z[z.index('/-- **The weight must sit on the first factor**'):].rstrip() + '\n'
HEAD = '''/-! ### The weighted duality of `rem:dualnonmarkov`

`Φ^Z (s, t) = E[Z f (X (s₀ + s), Y t)]` for a bounded weight `Z` measurable for the past of `X` at
`s₀`.  The reduction is the one of `duality`: the weight is carried by an extra coordinate,
`X' r = (Z, X (s₀ + r))`, and `duality_zero_of_mean` applies to `v f (x, y)`.  What is new is
the mean hypothesis in the first variable, which now consumes the whole martingale property
(`integral_weight_sub_eq_zero`); and the witness `not_secondIncrement_of_weight_on_dual` shows
that the weight cannot be moved to the dual side. -/

'''
anchor = 'end AlphaBeta\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + HEAD + w + '\n\n' + z, 1)
open(R, 'w').write(s)
print('eingebaut')
