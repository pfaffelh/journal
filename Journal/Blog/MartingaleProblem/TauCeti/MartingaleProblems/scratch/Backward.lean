/-
Development harness of 2026-09-09, twenty sixth run, second part: the expectation identity of the
backward equation.  It was a harness -- the prerequisites of `Suggested.lean` copied in as
`axiom`s so that a run took seconds instead of minutes.

Its contents have moved into `TauCeti/MartingaleProblems/Suggested.lean`, where
`jumpMeasure_integral_sub_eq_intervalIntegral` is type-checked in place against Mathlib v4.33.1
and checked with `#print axioms`.

Nothing is left here on purpose: a harness whose `axiom`s duplicate statements that are proved in
`Suggested.lean` would be a second, misleading source of truth -- and an `axiom` is worse than a
`sorry`, because it carries no warning.
-/
