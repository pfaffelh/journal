#!/usr/bin/env python3
"""Einmaliges Einbauskript des siebzehnten Laufs vom 2026-09-25: stellt die vier Sätze von
`section ContinuousDuality` auf die Mittelwerthypothese um (`_of_mean`), läßt die
Martingalfassungen als Einzeiler stehen und hängt die Abschnitte aus
`scripts/_dev_expmart.lean` hinter `end ContinuousDuality` an.  Bricht ab, statt halb zu
schreiben, wenn eine erwartete Stelle fehlt."""
import os
J = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = os.path.join(J, 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
D = os.path.join(J, 'scripts/_dev_expmart.lean')
s = open(R).read()
if 'duality_zero_of_mean' in s:
    raise SystemExit('schon eingebaut')
a = s.index('/-- **The first increment representation `eq:Fpartial1` at `α = β = 0`.**')
b = s.index('end ContinuousDuality\n')
reg = s[a:b]


def rep(old, new, count=1):
    global reg
    assert reg.count(old) == count, (old[:60], reg.count(old))
    reg = reg.replace(old, new)


rep("""    {𝓕 : Filtration ℝ≥0 mΩ}
    (hXmg : ∀ y, Martingale (fun t ω ↦ f (X t ω, y) - ∫ r in (0 : ℝ)..t, g (X r.toNNReal ω, y))
      𝓕 P) (s t : ℝ) (hs : 0 ≤ s) :""",
    """    (hXm : ∀ y (s : ℝ≥0), ∫ ω, (f (X s ω, y) - f (X 0 ω, y) -
      ∫ r in (0 : ℝ)..s, g (X r.toNNReal ω, y)) ∂P = 0) (s t : ℝ) (hs : 0 ≤ s) :""")
rep("""  have h := integral_sub_eq_zero_of_martingale (hXmg y) (zero_le : (0 : ℝ≥0) ≤ s.toNNReal)
  refine (integral_congr_ae (ae_of_all _ fun ω ↦ ?_)).trans h
  simp only [Real.coe_toNNReal s hs, NNReal.coe_zero, intervalIntegral.integral_same,
    Real.toNNReal_zero]
  ring""",
    """  have h := hXm y s.toNNReal
  refine (integral_congr_ae (ae_of_all _ fun ω ↦ ?_)).trans h
  simp only [Real.coe_toNNReal s hs, Real.toNNReal_zero]""")

NAMES = ['duality_increment_fst', 'duality_zero_hypotheses', 'duality_zero',
         'duality_relation_zero']


def sig(name):
    i = reg.index('theorem ' + name + ' ')
    j = reg.index(':= by', i)
    return reg[i:j]


# the original signatures, for the wrappers (read before the renaming, but the first one
# already carries the mean hypothesis, so it is restored below)
orig = {n: sig(n) for n in NAMES}
MG1 = """    {𝓕 : Filtration ℝ≥0 mΩ}
    (hXmg : ∀ y, Martingale (fun t ω ↦ f (X t ω, y) - ∫ r in (0 : ℝ)..t, g (X r.toNNReal ω, y))
      𝓕 P) (s t : ℝ) (hs : 0 ≤ s) :"""
orig['duality_increment_fst'] = orig['duality_increment_fst'].replace(
    """    (hXm : ∀ y (s : ℝ≥0), ∫ ω, (f (X s ω, y) - f (X 0 ω, y) -
      ∫ r in (0 : ℝ)..s, g (X r.toNNReal ω, y)) ∂P = 0) (s t : ℝ) (hs : 0 ≤ s) :""", MG1)
rep("""    {𝓕 𝓖 : Filtration ℝ≥0 mΩ}
    (hXmg : ∀ y, Martingale (fun t ω ↦ f (X t ω, y) - ∫ r in (0 : ℝ)..t, g (X r.toNNReal ω, y))
      𝓕 P)
    (hYmg : ∀ x, Martingale (fun t ω ↦ f (x, Y t ω) - ∫ r in (0 : ℝ)..t, h (x, Y r.toNNReal ω))
      𝓖 P)""",
    """    (hXm : ∀ y (s : ℝ≥0), ∫ ω, (f (X s ω, y) - f (X 0 ω, y) -
      ∫ r in (0 : ℝ)..s, g (X r.toNNReal ω, y)) ∂P = 0)
    (hYm : ∀ x (t : ℝ≥0), ∫ ω, (f (x, Y t ω) - f (x, Y 0 ω) -
      ∫ r in (0 : ℝ)..t, h (x, Y r.toNNReal ω)) ∂P = 0)""", 3)
for n in NAMES:
    rep('theorem ' + n + ' ', 'theorem ' + n + '_of_mean ')
rep("duality_increment_fst hX hYt hind hf hg hΓ hfΓ hgΓ hXmg s t hs",
    "duality_increment_fst_of_mean hX hYt hind hf hg hΓ hfΓ hgΓ hXm s t hs")
rep("      (Γ := Γ) (𝓕 := 𝓖) hY hXt (fun s t ↦ (hind t s).symm)",
    "      (Γ := Γ) hY hXt (fun s t ↦ (hind t s).symm)")
rep("have := duality_increment_fst (f :=", "have := duality_increment_fst_of_mean (f :=")
rep("(fun T s t hs ht ω ↦ hhΓ T t s ht hs ω) hYmg t s ht",
    "(fun T s t hs ht ω ↦ hhΓ T t s ht hs ω) hYm t s ht")
rep("duality_zero_hypotheses hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ hXmg hYmg",
    "duality_zero_hypotheses_of_mean hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ hXm hYm", 2)
rep("duality_zero hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ hXmg hYmg",
    "duality_zero_of_mean hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ hXm hYm")
assert 'hXmg' not in reg and 'hYmg' not in reg

LEMMA = '''/-- **The mean hypothesis from a martingale.**  Of the martingale hypotheses
`eq:dualmg1`/`eq:dualmg2`, the `_of_mean` statements above consume only this: the compensated
increment between `0` and `s` has mean zero, at every frozen value of the other process.  The
exponential weights of `duality` produce exactly this form, and no martingale. -/
theorem integral_compensated_sub_eq_zero_of_martingale {X : ℝ≥0 → Ω → E₁} {f g : E₁ × E₂ → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (hXmg : ∀ y, Martingale (fun t ω ↦ f (X t ω, y) - ∫ r in (0 : ℝ)..t, g (X r.toNNReal ω, y))
      𝓕 P) (y : E₂) (s : ℝ≥0) :
    ∫ ω, (f (X s ω, y) - f (X 0 ω, y) - ∫ r in (0 : ℝ)..s, g (X r.toNNReal ω, y)) ∂P = 0 := by
  have h := integral_sub_eq_zero_of_martingale (hXmg y) (zero_le : (0 : ℝ≥0) ≤ s)
  refine (integral_congr_ae (ae_of_all _ fun ω ↦ ?_)).trans h
  simp only [NNReal.coe_zero, intervalIntegral.integral_same]
  ring

'''
HY = ("(fun x t ↦ integral_compensated_sub_eq_zero_of_martingale (f := fun z ↦ f (z.2, z.1))\n"
      "      (g := fun z ↦ h (z.2, z.1)) hYmg x t)")
DOC = '/-- `{0}_of_mean` under the martingale hypotheses `eq:dualmg1`/`eq:dualmg2`. -/\n'
BODY = {
    'duality_increment_fst': ":=\n  duality_increment_fst_of_mean hX hY hind hf hg hΓ hfΓ hgΓ\n"
    "    (integral_compensated_sub_eq_zero_of_martingale hXmg) s t hs\n",
    'duality_zero_hypotheses': ":=\n  duality_zero_hypotheses_of_mean hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ\n"
    "    (integral_compensated_sub_eq_zero_of_martingale hXmg)\n    " + HY + "\n",
    'duality_zero': ":=\n  duality_zero_of_mean hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ\n"
    "    (integral_compensated_sub_eq_zero_of_martingale hXmg)\n    " + HY + "\n",
    'duality_relation_zero': ":=\n  duality_relation_zero_of_mean hX hY hind hf hg hh hΓ hfΓ hgΓ hhΓ\n"
    "    (integral_compensated_sub_eq_zero_of_martingale hXmg)\n    " + HY + " hbal t\n",
}
wr = LEMMA
for n in NAMES:
    wr += DOC.format(n) + orig[n].rstrip() + ' ' + BODY[n] + '\n'
reg = reg + wr
s = s[:a] + reg + s[b:]

d = open(D).read()
ds = d[d.index('section ExpCalculus'):]
i = ds.index('-- dev copy of the roadmap')
j = ds.index('/-- **The exponential martingale, in mean.**')
ds = ds[:i] + ds[j:]
i = ds.index('-- dev stubs')
j = ds.index('/-- **The exponential martingale as the mean hypothesis')
ds = ds[:i] + ds[j:]
ds = ds.replace('intervalIntegrable_of_abs_le', 'intervalIntegrable_of_abs_le_Icc')
HEAD = '''
/-! ### `thm:duality` and `cor:dualrel` with `α` and `β`

The reduction of `thm:duality` to its case `α = β = 0`: the exponential weights are carried by
an extra coordinate, `X̃ s = (X s, ∫_0^s α (X w) dw)` and `Ỹ t = (Y t, ∫_0^t β (Y w) dw)`, and
`f̃ ((x, a), (y, b)) = f (x, y) e^a e^b`.  Then `eq:Phidual` is the `Φ` of `duality_zero` for
`X̃`, `Ỹ`, `f̃`, and `eq:dualbalance` is the balance `g̃ = h̃`.  What is new is one statement about
one process, `integral_mul_exp_sub_eq_zero_of_martingale`: the exponentially weighted
compensated increment has mean zero.  It is proved without a partition, from the chain rule and
the product rule for absolutely continuous functions (Mathlib's
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` and `integral_deriv_mul_eq_sub`), so that
the terms `T₂`, `T₄` of the manuscript's proof do not occur instead of being `O(h²)`. -/

'''
s = s.replace('end ContinuousDuality\n', 'end ContinuousDuality\n' + HEAD + ds.rstrip() + '\n', 1)
open(R, 'w').write(s)
print('eingebaut')
