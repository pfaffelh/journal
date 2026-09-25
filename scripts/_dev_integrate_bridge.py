#!/usr/bin/env python3
"""Einmaliges Einbauskript des achtzehnten Laufs vom 2026-09-25, dritter Teil: hängt
`section DualityBridge` aus `scripts/_dev_bridge_dual.lean` (ohne die Stubs) hinter
`end Stopped` in `MartingaleProblems/Suggested.lean` an.  Bricht ab, statt halb zu schreiben,
wenn eine erwartete Stelle fehlt."""
import os
J = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = os.path.join(J, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
s = open(R).read()
if 'propagatesAgreement_of_duality' in s and 'theorem propagatesAgreement_of_duality' in s:
    raise SystemExit('schon eingebaut')
w = open(os.path.join(J, 'scripts/_dev_bridge_dual.lean')).read()
w = w[w.index('section DualityBridge'):w.index('end DualityBridge') + len('end DualityBridge')]
w = w.replace('ℝ≥0∞', 'ENNReal')
HEAD = '''/-! ### The bridge to uniqueness: `propagatesAgreement_of_duality`

The route of `rem:dualnonmarkov` and not the one of the proof of `cor:uniqviadual`: the weighted
duality relation is `htransfer` of `propagatesAgreement_of_transfer`, and
`eq_of_propagatesAgreement` gives uniqueness for every initial law.  The solution `π` lives under
`P` on the path space, the dual `Y y` under `Q` on its own space, and the two are made
independent on the product `P ⊗ Q` (`indepFun_prod`); the mean hypotheses of
`duality_relation_zero_of_mean` are then read off the factors (`integral_fun_fst`,
`integral_fun_snd`), so that no martingale on the product is ever formed.

`isMarkov_of_duality` is not stated.  With `Z = 1_A`, `A ∈ 𝓕₀ s`, the weighted relation gives
`E[f (π t, y) | 𝓕₀ s] = Λ (π s)` for the functions `f (·, y)` only; the Markov property for every
bounded `f` needs an extension from the separating family, which is a proof of its own and not a
corollary of the statements below. -/

'''
anchor = 'end Stopped\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + HEAD + w + '\n', 1)
open(R, 'w').write(s)
print('eingebaut')
