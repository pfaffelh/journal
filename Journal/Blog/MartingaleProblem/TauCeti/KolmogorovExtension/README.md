# The Kolmogorov extension theorem

Given a family of finite measures `P J` on `Π j : J, α j`, indexed by the finite
subsets `J` of an arbitrary index type `ι` and consistent under restriction,
produce a measure on `Π i, α i` whose finite dimensional marginals are the
`P J`.

## What Mathlib already has

Nearly all the scaffolding, and it is **not** to be rebuilt.

* `MeasureTheory.IsProjectiveMeasureFamily` and
  `MeasureTheory.IsProjectiveLimit` in
  `Mathlib/MeasureTheory/Constructions/Projective.lean`, together with the whole
  uniqueness layer: `MeasureTheory.IsProjectiveLimit.measure_cylinder`,
  `measure_univ_eq`, `isFiniteMeasure`, `isProbabilityMeasure`,
  `measure_univ_unique` and `MeasureTheory.IsProjectiveLimit.unique`, which is
  the statement that two projective limits of the same family of finite measures
  agree.
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
  `IsCompactSystem` with `IsCompactSystem.nonempty_iInter`,
  `IsCompactSystem.of_nonempty_iInter`, `IsCompactSystem.iff_nonempty_iInter`,
  `mono`, `insert_empty`, `insert_univ`, `isCompactSystem_insert_empty_iff`,
  `isCompactSystem_insert_univ_iff` and `isCompactSystem_iff_of_directed`. It
  also supplies the compact system that Milestone 1 needs in each coordinate
  block: `isCompactSystem_isCompact_isClosed`, the closed compact sets of a
  topological space, with `isCompactSystem_isCompact` for a `T2Space` and
  `isCompactSystem_insert_univ_isCompact_isClosed`.
* `MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite` and
  `MeasureTheory.innerRegularWRT_isCompact_isClosed` in
  `Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`: a finite measure on a
  second countable completely pseudometrizable space is inner regular with
  respect to the compact closed sets. Both carry
  `[SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]`, the first
  `[BorelSpace α]` and the second `[OpensMeasurableSpace α]`; a Polish `α i`
  supplies all four.
* The two special cases of the theorem: the sequential Ionescu–Tulcea
  construction `ProbabilityTheory.Kernel.traj` in
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`, and the product measure
  for an arbitrary index, `MeasureTheory.Measure.isProjectiveLimit_infinitePi`
  in `Mathlib/Probability/ProductMeasure.lean` — in the namespace
  `MeasureTheory.Measure`, with `MeasureTheory.Measure.isProjectiveLimit_infinitePiNat`
  for the index `ℕ`.

What is missing is the bridge between the compact system and the content, and
the theorem itself. That is one milestone of real work and one of assembly.

**Prior art, cited and not presupposed.** The repository
`RemyDegenne/kolmogorov_extension4` (Apache-2.0) carries a development of the
same theorem, most of which has since landed in Mathlib under the names above.
It is named here as a source an implementer may consult and, the licence
permitting, draw on with its copyright header preserved — **not** as the
specification. The two milestones below state what is wanted in full and are to
be reviewed on their own terms.

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
  is compact. That the closed compact sets are a compact system to begin with is
  `isCompactSystem_isCompact_isClosed`, and the passage to the cylinders over
  them is what this item adds.

**Acceptance examples.**

* **The decreasing cylinders that do not close up.** `ι = ℕ`, `α i = ℝ`,
  `P J` the standard Gaussian on `Π j : J, ℝ`, and
  `C n = {x | ∀ k ≤ n, |x k| ≤ a k}` with `a k` chosen so that
  `∏ k, P {|y| ≤ a k} = 1/2`. The `C n` decrease, each is a cylinder of content
  at least `1/2`, and `⋂ n, C n` is nonempty — it contains the zero sequence.
  `AddContent.isSigmaSubadditive_of_innerRegular` must produce exactly this
  conclusion from `IsCompactSystem.nonempty_iInter`, applied to the compact
  boxes `Π k ≤ n, Set.Icc (-a k) (a k)` inside the `C n`. Replacing the boxes by
  the open sets `{|x k| < a k}` breaks it: the intersection of a decreasing
  sequence of nonempty open cylinders can be empty, which is why the compact
  system and not mere nonemptiness is the hypothesis.
* **The inner regularity hypothesis is sufficient and not necessary.** Let
  `α i = ℝ` carry the countable–cocountable σ-algebra and `μ A = 0` for `A`
  countable, `1` for `A` cocountable — a probability measure. Its measurable
  compact sets are the countable compacts, of measure `0`, there being no
  cocountable compact subset of `ℝ`; so inner regularity by compact sets fails
  as badly as possible, and Milestone 1 does not apply. The projective limit of
  the product family nevertheless exists, being
  `MeasureTheory.Measure.infinitePi`. The milestone must therefore be stated as
  a sufficient condition, and no later item may read the failure of inner
  regularity as the failure of extension.

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
  measure, and `IsFiniteMeasure` in general. Both are
  `MeasureTheory.isProjectiveLimit_projectiveLimit` fed to
  `MeasureTheory.IsProjectiveLimit.isProbabilityMeasure` and
  `MeasureTheory.IsProjectiveLimit.isFiniteMeasure`, and are stated as instances.
  Uniqueness of the limit needs nothing from this milestone: it is
  `MeasureTheory.IsProjectiveLimit.unique` of the head list, applied to
  `isProjectiveLimit_projectiveLimit`.

**Acceptance examples.**

* **Against the product measure, which Mathlib builds independently.**
  `α i = ℝ` and `P J = Measure.pi (fun j : J ↦ μ j)` for probability measures
  `μ i`. This family is projective by
  `MeasureTheory.isProjectiveMeasureFamily_pi`, so `projectiveLimit P hP` is
  defined; and `MeasureTheory.Measure.isProjectiveLimit_infinitePi` says
  `Measure.infinitePi μ` is a projective limit of the same family. By
  `IsProjectiveLimit.unique` the two must be **equal**. This is the sharpest
  acceptance test the milestone admits, because `Measure.infinitePi` is built
  along a completely different route — through `piContent_tendsto_zero` and a
  countable set of coordinates — and under no topological hypothesis at all.
* **Against Ionescu–Tulcea on `ℕ`.** `ι = ℕ`, `α n` Polish, and `P J` the
  marginals of a family of kernels. Then `projectiveLimit P hP` and
  `ProbabilityTheory.Kernel.traj` are projective limits of the same family, so
  they agree, again by `IsProjectiveLimit.unique`. The manuscript records the
  same collapse in `fact:kolmogorov`: for a countable `𝕋` that can be
  enumerated, Ionescu–Tulcea suffices and the theorem of this milestone is not
  needed.
* **Wiener measure on an uncountable index.** `ι = Set.Ici (0:ℝ)`, `α i = ℝ`,
  and `P J` the centred Gaussian on `Π j : J, ℝ` with covariance
  `fun s t ↦ min s t`. Consistency is the marginal property of Gaussian
  vectors, `ℝ` is Polish, so `isProjectiveLimit_projectiveLimit` yields a
  probability measure on `Π t : Set.Ici (0:ℝ), ℝ` with the Brownian finite
  dimensional distributions. Neither `Kernel.traj` nor `infinitePi` reaches it:
  the index is uncountable and the coordinates are dependent. This is the
  instance for which the milestone exists.

## Milestone 3: the standard applications

* `exists_process_of_isProjectiveMeasureFamily`: for Polish `α i` and a
  projective family, the coordinate process on `Π i, α i` under
  `projectiveLimit` has the prescribed finite dimensional distributions. State
  it through `ProbabilityTheory.isProjectiveLimit_map` of
  `Mathlib/Probability/Process/FiniteDimensionalLaws.lean` — that file is in the
  namespace `ProbabilityTheory`, unlike the rest of the projective-limit
  material — so that it composes with the existing process API.
* `MeasureTheory.Measure.isProjectiveLimit_infinitePi` recovered as the special
  case of independent coordinates.
* The extension of a consistent family of transition kernels along an arbitrary
  totally ordered index, generalizing the sequential
  `ProbabilityTheory.Kernel.traj`.

**Acceptance examples.**

* **Brownian motion as a process.** With the family of the previous milestone,
  `exists_process_of_isProjectiveMeasureFamily` must return the coordinate
  process `W t ω = ω t` on `Π t : Set.Ici (0:ℝ), ℝ` together with the statement
  that its finite dimensional laws are the prescribed Gaussians, stated through
  `ProbabilityTheory.isProjectiveLimit_map`. The paths of that process are not
  continuous and no statement of this roadmap says they are: continuity is a
  modification theorem and belongs to **SkorokhodSpace**. An item that promised
  a process on `C(ι, E)` here would be false, `Π t, ℝ` carrying the product
  σ-algebra in which `{ω | Continuous ω}` is not measurable.
* **A Markov semigroup along `[0,∞)`.** `E` Polish, `μ t (x, ·)` a family of
  kernels with `μ 0 (x, ·) = δ x` and Chapman–Kolmogorov, `ν` an initial law.
  This is the manuscript's `fact:kolmogorov` verbatim, and the third item must
  produce from it the law on `E^[0,∞)` under which the coordinate process is
  Markov with those transitions. Instantiating `μ t (x, ·)` as the Gaussian
  `N(x, t)` recovers the previous example, so the two items overlap on one
  instance, and that they agree on it is the acceptance test.
* **Independent coordinates, and the boundary of the Markov form.** A family of
  kernels ignoring its state argument, `μ t (x, ·) = ν t` for all `x`, gives the
  product family, and the second item — `isProjectiveLimit_infinitePi` recovered
  as a special case — must return `Measure.infinitePi` on it. It is **not** an
  instance of the Markov form of the previous example: `μ 0 (x, ·) = δ x` fails
  unless `E` is a single point. So the roadmap needs both the projective-family
  statement and the kernel statement, and neither subsumes the other; an item
  that offered only the kernel form would not cover the product measure.
