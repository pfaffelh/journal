/-
Development harness of 2026-09-09, twenty fifth run: the jump construction as a kernel in the
initial state, and the base case of the Markov property at a fixed time.  It was a harness -- the
prerequisites of `Suggested.lean` copied in as `axiom`s so that a run took seconds instead of
minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`jumpKernel`, `instIsMarkovKernelJumpKernel`, `jumpKernel_apply`, `jumpMeasure_eq_comp`,
`integral_jumpMeasure_eq_integral_jumpKernel`, `measurable_integral_jumpKernel`,
`integral_chainKernel_zero_eq`, `integral_jumpKernel_zero_eq`, `jumpSemigroup`,
`measurable_uncurry_jumpSemigroup`, `measurable_jumpSemigroup`, `abs_jumpSemigroup_le`,
`integral_jumpSemigroup_eq`, `waitShift`, `measurable_waitShift`, `jumpTime_waitShift`,
`jumpProcess_waitShift`, `waitingMeasure_map_natCons`, `integral_waitingMeasure_waitShift`,
`integral_jumpKernel_waitShift` and `integral_jumpKernel_add_of_lt_jumpTime_one`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
