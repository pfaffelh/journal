/-
Development harness of 2026-09-09, twenty sixth run: the induction over the number of jumps, and
with it the Markov property of the jump process at a fixed time.  It was a harness -- the
prerequisites of `Suggested.lean` copied in as `axiom`s so that a run took seconds instead of
minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`jumpMeasure_step_eq_comp`, `measurable_integral_jumpMeasure_step`,
`integral_jumpMeasure_eq_of_split_prod`, `setIntegral_jumpMeasure_eq_integral_jumpKernel`,
`abs_sub_le_add`, `abs_integral_jumpMeasure_add_sub_le`, `tendsto_measureReal_jumpTime_le`,
`jumpMeasure_integral_jumpProcess_add` and `jumpMeasure_integral_jumpProcess_add'`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
