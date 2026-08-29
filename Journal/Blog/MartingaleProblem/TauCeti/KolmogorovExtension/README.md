# The Kolmogorov extension theorem

Given a family of finite measures `P J` on `Π j : J, α j`, indexed by the finite
subsets `J` of an arbitrary index type `ι` and consistent under restriction,
produce a measure on `Π i, α i` whose finite dimensional marginals are the
`P J`.

## What Mathlib already has

Nearly all the scaffolding, and it is **not** to be rebuilt.

* `MeasureTheory.IsProjectiveMeasureFamily` and
  `MeasureTheory.IsProjectiveLimit` in
  `Mathlib/MeasureTheory/Constructions/Projective.lean`.
* The cylinder sets in `Mathlib/MeasureTheory/Constructions/Cylinders.lean`,
  with `measurableCylinders` and `generateFrom_measurableCylinders`.
* `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean`: the whole
  content already exists — `isSetSemiring_measurableCylinders`,
  `isSetRing_measurableCylinders`, `isSetAlgebra_measurableCylinders`,
  `projectiveFamilyContent` with `projectiveFamilyContent_eq`, `_congr`,
  `_cylinder`, `_mono`, `_iUnion_le`, `_ne_top`, `_sdiff` and
  `_sdiff_of_subset`.
* `Mathlib/MeasureTheory/Measure/AddContent.lean` with
  `MeasureTheory.AddContent.IsSigmaSubadditive`, and
  `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean` with
  `MeasureTheory.AddContent.measure`, which turns a σ-subadditive content on a
  set semiring into a measure, together with `AddContent.measure_eq`.
* `Mathlib/Topology/Compactness/CompactSystem.lean`:
  `IsCompactSystem` with `IsCompactSystem.nonempty_iInter`, `mono`,
  `insert_empty`, `insert_univ` and `isCompactSystem_insert_univ_iff`.
* `MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite` and
  `MeasureTheory.innerRegularWRT_isCompact_isClosed` in
  `Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`: a finite measure on a
  completely pseudometrizable space is inner regular with respect to the compact
  closed sets.
* The two special cases of the theorem: the sequential Ionescu–Tulcea
  construction `ProbabilityTheory.Kernel.traj` in
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`, and the product measure
  for an arbitrary index, `MeasureTheory.isProjectiveLimit_infinitePi` in
  `Mathlib/Probability/ProductMeasure.lean`.

What is missing is the bridge between the compact system and the content, and
the theorem itself. That is one milestone of real work and one of assembly.

Prior art whose code may be reused: the repository
`RemyDegenne/kolmogorov_extension4`, Apache License 2.0, file
`KolmogorovExtension4/KolmogorovExtension.lean`. Much of what it contains has
since landed in Mathlib under the names above, so what is taken over is only the
two items below. Copyright headers and author attribution are to be preserved,
as the Apache licence requires.

## Milestone 1: inner regularity makes a content σ-subadditive

* `MeasureTheory.AddContent.isSigmaSubadditive_of_innerRegular`: let `C` be a set
  semiring, `m` an additive content on `C` that is finite, and `K` a compact
  system such that every `s ∈ C` is approximated from inside by members of `K`
  contained in `s`, in the sense that for every `ε > 0` there is `k ∈ K` and
  `t ∈ C` with `t ⊆ k ⊆ s` and `m s ≤ m t + ε`. Then `m.IsSigmaSubadditive`.
  The proof is `IsCompactSystem.nonempty_iInter` applied to a decreasing
  sequence of approximants, and it is the only place where compactness enters
  the extension theorem.
* The consequence, packaged for use with the existing
  `MeasureTheory.AddContent.measure`: such an `m` extends to a measure on
  `MeasurableSpace.generateFrom C` agreeing with `m` on `C`.
* The instance of the hypothesis that the next milestone needs: for
  `[∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]` and every `α i` Polish,
  the closed compact cylinders form a compact system in `Π i, α i`, and
  `projectiveFamilyContent` is approximated from inside by them. This is
  `innerRegular_isCompact_isClosed_measurableSet_of_finite` applied in each
  finite coordinate block, together with the fact that a product of compact sets
  is compact.

## Milestone 2: the theorem

* `MeasureTheory.projectiveFamilyContent_isSigmaSubadditive`, under
  `[∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)] [∀ i, PolishSpace (α i)]`
  and `[∀ J, IsFiniteMeasure (P J)]`, from Milestone 1.
* `MeasureTheory.projectiveLimit P hP`, defined as
  `(projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
  generateFrom_measurableCylinders.symm.le` with the σ-subadditivity above.
* `MeasureTheory.isProjectiveLimit_projectiveLimit`: the Kolmogorov extension
  theorem. Its marginals are the `P J`.
* `IsProbabilityMeasure (projectiveLimit P hP)` when every `P J` is a probability
  measure, and `IsFiniteMeasure` in general.
* `MeasureTheory.IsProjectiveLimit.unique`: two projective limits of the same
  family agree, from `generateFrom_measurableCylinders` and the π-system
  uniqueness lemma `MeasureTheory.ext_of_generate_finite`.

## Milestone 3: the standard applications

* `exists_process_of_isProjectiveMeasureFamily`: for Polish `α i` and a
  projective family, the coordinate process on `Π i, α i` under
  `projectiveLimit` has the prescribed finite dimensional distributions. State
  it through `MeasureTheory.isProjectiveLimit_map` of
  `Mathlib/Probability/Process/FiniteDimensionalLaws.lean`, so that it composes
  with the existing process API.
* `MeasureTheory.isProjectiveLimit_infinitePi` recovered as the special case of
  independent coordinates.
* The extension of a consistent family of transition kernels along an arbitrary
  totally ordered index, generalizing the sequential
  `ProbabilityTheory.Kernel.traj`.
