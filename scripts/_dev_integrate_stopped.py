#!/usr/bin/env python3
"""Einmaliges Einbauskript des achtzehnten Laufs vom 2026-09-25, zweiter Teil: hängt
`section Stopped` aus `scripts/_dev_stopped.lean` (ohne die Stubs) hinter den Zeugen
`not_secondIncrement_of_weight_on_dual` in `MartingaleProblems/Suggested.lean` an.  Bricht ab,
statt halb zu schreiben, wenn eine erwartete Stelle fehlt."""
import os
J = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = os.path.join(J, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
s = open(R).read()
if 'duality_stopped' in s:
    raise SystemExit('schon eingebaut')
w = open(os.path.join(J, 'scripts/_dev_stopped.lean')).read()
w = w[w.index('section Stopped'):w.index('end Stopped') + len('end Stopped')].replace('ℝ≥0∞', 'ENNReal')
HEAD = '''/-! ### `cor:dualstopped`: the stopped duality

A corollary of `duality_zero_of_mean` by the same device as `duality` and `duality_weighted`:
the indicator `1_{s ≤ τ}` of the manuscript's proof is carried by a second coordinate of the
process, so that the compensator up to `t ∧ τ` becomes a compensator up to `t` with a cut off
integrand (`intervalIntegral_min_eq_indicator`), and nothing of the proof of `thm:duality` is
repeated. -/

'''
anchor = '\n/-! ## Causal convolution and the Volterra resolvent'
assert s.count(anchor) == 1
s = s.replace(anchor, '\n' + HEAD + w + '\n' + anchor, 1)
open(R, 'w').write(s)
print('eingebaut')
