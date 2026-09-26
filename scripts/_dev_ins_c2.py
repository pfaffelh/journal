dev = open('scripts/_dev_C2poisson.lean').read()
body = 'theorem integrable_natCast_poissonMeasure' + dev.split('theorem integrable_natCast_poissonMeasure', 1)[1]
doc1 = """/-- **The Poisson law has a first moment**: `n ↦ (n : ℝ)` is integrable against
`ProbabilityTheory.poissonMeasure r`.  `integrable_poissonMeasure_iff` reduces it to the
summability of `e^{-r} r^n n / n!`, which is dominated by `e^{-r} (2r)^n / n!` because `n ≤ 2^n`
(`Real.summable_pow_div_factorial`).  Mathlib states no moment of the Poisson law. -/
"""
doc3 = """/-- **Acceptance of Milestone 2: the Poisson process by hand, with the unbounded `f = id`.**
The constructed Poisson process solves the martingale problem for its operator **together with the
pair `(id, 1)`**, that is, `N t - t` is a martingale, and this is obtained from the bounded pairs
alone through `IsMPSolutionFor.insert_of_tendsto`, with the truncations `f n = min · n`.

On them the generator is `1_{x < n}` (`jumpApply_poisson_min`), so the test processes are
`min (N t) n - ∫_0^t 1_{N s < n} ds`.  They converge pointwise (for fixed `ω` the first term is
eventually `N t`, the second converges by dominated convergence on the window), are dominated by
`2 N t + 2 t`, and `N t` is integrable because its law is `Po(t)`
(`jumpMeasure_map_jumpProcess_poisson`, `integrable_natCast_poissonMeasure`).  Adaptedness of
`N t - t` is read off the pointwise limit of adapted processes, so no statement about the
filtration of the construction is needed.  The bounded form
`IsMPSolutionFor.insert_of_forall_norm_le` does **not** apply here, `id` being unbounded; that is
the point of the example. -/
"""
body = body.replace('theorem integrable_natCast_poissonMeasure', doc1 + 'theorem integrable_natCast_poissonMeasure', 1)
body = body.replace('theorem poissonProcess_isMPSolutionFor_insert_id', doc3 + 'theorem poissonProcess_isMPSolutionFor_insert_id', 1)
body = body.rstrip('\n')
p = 'Journal/Blog/MartingaleProblem/TauCeti/JumpProcesses/Suggested.lean'
s = open(p).read()
anchor = "\nend PoissonExample\n"
assert s.count(anchor) == 1
s = s.replace(anchor, "\n" + body + "\n" + anchor)
open(p, 'w').write(s)
print('ok')
