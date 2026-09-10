/-
Development harness of 2026-09-09, twenty seventh run: the structure of the past, i.e. what a
`jumpFiltration`-measurable functional is allowed to depend on.  It was a harness -- the
prerequisites of `Suggested.lean` copied in as `axiom`s so that a run took seconds instead of
minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`eq_of_measurable_naturalFiltration`, `measurable_comp_of_measurable_naturalFiltration`,
`NonExplosive`, `measurableSet_nonExplosive`, `ae_mem_nonExplosive`,
`indicator_nonExplosive_ae_eq`, `jumpConst` with `measurable_jumpConst`, `jumpTime_jumpConst`,
`lt_jumpTime_one_jumpConst`, `jumpConst_mem_nonExplosive` and `jumpProcess_jumpConst`,
`jumpPrepend` with `measurable_jumpPrepend`, `jumpShift_jumpPrepend`, `jumpPrepend_self`,
`jumpTime_jumpPrepend`, `jumpTime_one_jumpPrepend`, `jumpPrepend_mem_nonExplosive_iff` and
`jumpProcess_jumpPrepend`, and finally `IsPastFunctional` with `isPastFunctional_indicator`,
`eq_jumpConst_of_isPastFunctional`, `IsPastFunctional.comp_jumpPrepend` and
`measurable_comp_jumpConst`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
