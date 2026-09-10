/-
Development file of 2026-09-10, fifth run: the Gregory--Newton summation of the exponential
series of the forward difference operator.  It was a harness -- a standalone file over Mathlib
alone, so that the Cauchy product and the antidiagonal bookkeeping could be iterated in seconds
instead of in a full pass over `Suggested.lean`.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where they are
type-checked in place against Mathlib v4.33.1 and checked with `#print axioms`:
`abs_fwdDiff_iter_le` and `tsum_fwdDiff_iter_eq`, in `section PoissonExample`.

Nothing is left here on purpose: a second copy of a proved statement would be a second,
misleading source of truth.
-/
