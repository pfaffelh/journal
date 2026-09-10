/-
Development harness of 2026-09-10, first run: the Markov property with a factor from the past,
i.e. the measure theoretic core of the conditional expectation of the jump martingale problem.
It was a harness -- the prerequisites of `Suggested.lean` copied in as `axiom`s so that a run took
seconds instead of minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`jumpKernel_map_snd`, `ae_mem_nonExplosive_jumpKernel`,
`abs_integral_jumpMeasure_add_sub_le_past`, `jumpMeasure_integral_jumpProcess_add_past` and
`setIntegral_jumpProcess_sub_eq_intervalIntegral`, all five in the new section
`ConditionalMarkov` at the end of `section Space`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
