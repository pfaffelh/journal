/-
Development file of 2026-09-09, twenty fourth run: the backward equation in differential form.
It was a harness -- the prerequisites of `Suggested.lean` copied in as `axiom`s so that iteration
took seconds instead of minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`expMeasure_one_real_Iic`, `integral_chain_zero_eq`, `one_sub_exp_neg_le_self`,
`exp_neg_le_one_of_nonneg`, `measureReal_jumpTime_one_le`, `abs_integral_jumpProcess_sub_le`,
`measurable_integral_kernel_apply`, `jumpApply_eq`, `abs_integral_jumpProcess_sub_sub_le`,
`integral_jumpProcess_of_nonpos`, `jumpMeasure_hasDerivWithinAt_integral` and
`eq_zero_of_hasDerivAt_integral_jumpProcess`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
