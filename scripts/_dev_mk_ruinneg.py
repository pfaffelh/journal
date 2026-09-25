#!/usr/bin/env python3
"""Erzeugt `scripts/_dev_ruinneg.lean` aus den beiden Ruin-Aussagen in
`MartingaleProblems/Suggested.lean`: dieselben Beweise für das Ereignis
`{X τ = -b}` statt `{X τ = a}`.  Nur Entwicklungswerkzeug."""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
P = ROOT / 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = P.read_text()
i = s.index('theorem measure_stoppedValue_hittingAfter_eq_of_continuous')
j = s.index("/-- **The gambler's ruin for Brownian motion.**")
k = s.index("open scoped ENNReal in\n/-- **Wald's identity for Brownian motion with every path")
cont = s[i:j].rstrip() + '\n'
bm = s[j:k]
bm = bm[bm.index('theorem '):].rstrip() + '\n'


def neg(t):
    t = t.replace('measure_stoppedValue_hittingAfter_eq_of_continuous',
                  'measure_stoppedValue_hittingAfter_eq_neg_of_continuous')
    t = t.replace('measure_stoppedValue_hittingAfter_eq_of_isBrownianReal',
                  'measure_stoppedValue_hittingAfter_eq_neg_of_isBrownianReal')
    t = t.replace('ω = a}\n      = ENNReal.ofReal (b / (a + b))',
                  'ω = -b}\n      = ENNReal.ofReal (a / (a + b))')
    return t


cont = neg(cont)
old_tail = cont[cont.index("  set A := {ω | Y' ω = a} with hA"):]
new_tail = """  set A := {ω | Y' ω = -b} with hA
  have hAm : MeasurableSet A := hY'm (measurableSet_singleton (-b))
  have hQA : Q {ω | stoppedValue X τ ω = -b} = Q A := by
    refine measure_congr ?_
    filter_upwards [hYY] with ω hω
    change (stoppedValue X τ ω = -b) = (Y' ω = -b)
    rw [hω]
  have hYA : Y' =ᵐ[Q] fun ω ↦ a - A.indicator (fun _ ↦ a + b) ω := by
    filter_upwards [hYY, htwo] with ω hω h2
    rw [← hω]
    rcases h2 with h2 | h2
    · have : ω ∈ A := by
        change Y' ω = -b
        rw [← hω, h2]
      rw [indicator_of_mem this, h2]
      ring
    · have : ω ∉ A := by
        change ¬ Y' ω = -b
        rw [← hω, h2]
        intro h; linarith
      rw [indicator_of_notMem this, h2]
      ring
  have hcalc : 0 = a - Q.real A * (a + b) := by
    rw [← hEτ, integral_congr_ae hYY, integral_congr_ae hYA,
      integral_sub (integrable_const _) ((integrable_const _).indicator hAm),
      integral_indicator_const _ hAm, integral_const]
    simp [smul_eq_mul]
  have hreal : Q.real A = a / (a + b) := by
    field_simp
    linarith
  rw [hQA, ← ofReal_measureReal, hreal]
"""
cont = cont.replace(old_tail, new_tail)
bm = neg(bm)
head = """import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory

"""
(ROOT / 'scripts/_dev_ruinneg.lean').write_text(head + cont + '\n' + bm + '\nend MeasureTheory\n')
print('ok')
