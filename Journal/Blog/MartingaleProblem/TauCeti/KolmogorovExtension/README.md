# The Kolmogorov extension theorem

Given a family of finite measures `P J` on `Π j : J, α j`, indexed by the finite
subsets `J` of an arbitrary index type `ι` and consistent under restriction,
produce a measure on `Π i, α i` whose finite dimensional marginals are the
`P J`.

Mathlib has the scaffolding and the two special cases. Present are
`MeasureTheory.IsProjectiveMeasureFamily` and `MeasureTheory.IsProjectiveLimit`
in `Mathlib/MeasureTheory/Constructions/Projective.lean`, the cylinder sets
`MeasureTheory.measurableCylinders` with
`MeasureTheory.generateFrom_measurableCylinders`, the semiring structure on
them, `MeasureTheory.AddContent` with its extension to a measure, the
sequential Ionescu–Tulcea construction in
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`, and the product measure
for an arbitrary index in `Mathlib/Probability/ProductMeasure.lean`
(`MeasureTheory.isProjectiveLimit_infinitePi`). Absent is the theorem itself
for a general projective family.

Prior art whose code may be reused: the repository
`RemyDegenne/kolmogorov_extension4`, Apache License 2.0, files
`KolmogorovExtension4/Semiring.lean`, `RegularContent.lean`, `CompactSystem.lean`
and `KolmogorovExtension.lean`. Its `projectiveLimit` and
`isProjectiveLimit_projectiveLimit` are Milestone 3 below. Copyright headers and
author attribution are to be preserved, as the Apache licence requires. Parts of
that development have since been absorbed into Mathlib; what is taken over is to
be reduced to what Mathlib does not already provide.

## Milestone 1: compact systems

* `MeasureTheory.IsCompactSystem (C : Set (Set α))`: every countable subfamily
  with the finite intersection property has nonempty intersection.
* The compact sets of a topological space form a compact system.
* A compact system is stable under finite unions and finite intersections when
  the underlying family is; the closed compact sets of a Hausdorff space form a
  compact system stable under both.
* `IsCompactSystem.exists_of_iUnion`: if `C` is a compact system, `s n` is a
  decreasing sequence of sets each containing a member of `C` of almost the same
  content, then the intersection is nonempty. This is the combinatorial core of
  the σ-additivity argument.

## Milestone 2: inner regular contents

* `MeasureTheory.AddContent.IsInnerRegular` for a content on a set semiring,
  with respect to a compact system.
* `MeasureTheory.AddContent.sigma_additive_of_isInnerRegular`: an inner regular
  additive content on a set semiring is σ-additive, hence extends to a measure
  by the existing `MeasureTheory.AddContent.measure`.
* `MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite`: a
  finite measure on a Polish space is inner regular with respect to the compact
  closed sets. Mathlib has inner regularity results in
  `Mathlib/MeasureTheory/Measure/Regular.lean`; this states the form the
  extension needs.

## Milestone 3: the theorem

* `MeasureTheory.projectiveFamilyContent`: the additive content on
  `measurableCylinders α` determined by a projective family, together with
  `projectiveFamilyContent_congr` expressing that it does not depend on the
  chosen finite index set.
* `MeasureTheory.projectiveFamilyContent_sigma_additive`, under
  `[∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)] [∀ i, PolishSpace (α i)]`
  and `[∀ J, IsFiniteMeasure (P J)]`.
* `MeasureTheory.projectiveLimit P hP` and
  `MeasureTheory.isProjectiveLimit_projectiveLimit`: the Kolmogorov extension
  theorem for an arbitrary index type and Polish factors.
* `MeasureTheory.IsProjectiveLimit.unique`: two projective limits of the same
  family agree. Mathlib has this for cylinder-generated σ-algebras; state it
  here in the form used with `projectiveLimit`.
* `IsProbabilityMeasure (projectiveLimit P hP)` when every `P J` is a
  probability measure.

## Milestone 4: the standard applications

* The construction of a stochastic process with prescribed consistent finite
  dimensional distributions: for `α : ι → Type*` Polish and a projective family,
  a probability space carrying a process whose finite dimensional laws are the
  given ones. State it for the canonical space `Π i, α i` with the coordinate
  process.
* The law of a family of independent random variables with prescribed marginals,
  recovering `MeasureTheory.isProjectiveLimit_infinitePi` as a special case.
* The extension of a consistent family of transition kernels along an arbitrary
  totally ordered index, generalizing the sequential
  `ProbabilityTheory.Kernel.traj`.
