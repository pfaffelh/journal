/-
Development file of 2026-09-09, twenty third run: the renewal equation of the jump construction.
It was a harness -- the definitions of `Suggested.lean` copied in, with the already-proved facts
stubbed by `sorry` so that iteration was fast.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`integrable_of_abs_le`, `abs_integral_le_of_abs_le`, `expMeasure_eq_withDensity`,
`toReal_exponentialPDF_one`, `integral_expMeasure_one`, `ae_exists_lt_jumpTime`,
`integral_jumpMeasure_eq_of_split` and `jumpMeasure_integral_eq_renewal`.

Nothing is left here on purpose: a harness with `sorry` stubs for statements that are proved in
`Suggested.lean` would be a second, misleading source of truth.
-/
