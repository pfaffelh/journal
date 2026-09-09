/-
Development file of 2026-09-09, twenty second run: the jump-construction half of the splitting
of the driving data at the first jump.  It was a harness -- the definitions of `Suggested.lean`
copied in, with the already-proved facts stubbed by `sorry` so that iteration was fast.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`measurable_natSplit`, `chainKernel_map_split`, `comp_chainKernel_map_split`,
`waitingMeasure_map_split`, `jumpMeasure_map_split`, `prod_comp_chainKernel_eq_jumpMeasure` and
`jumpShift_eq_split`.

Nothing is left here on purpose: a harness with `sorry` stubs for statements that are proved in
`Suggested.lean` would be a second, misleading source of truth.
-/
