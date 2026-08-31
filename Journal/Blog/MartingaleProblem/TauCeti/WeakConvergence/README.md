# Weak convergence: separating classes, the continuous mapping theorem, and Skorokhod representation

Weak convergence of measures on a metric space is well developed in Mathlib,
and the next section says how far. Five things are wanted beyond it, each used
pervasively downstream: the two classes of functions that determine a measure or
its convergence, as predicates and with the instances Mathlib does not prove;
the continuous mapping theorem for maps continuous only almost everywhere; the
separability and the completeness of the space of laws itself, of which Mathlib
has only the metrizability; the Skorokhod representation theorem; and the link
between uniform integrability and convergence in distribution.

Throughout, `E` is a metric space, `Ω` a measurable space, and measures are
Borel probability measures. Weak convergence is
`Filter.Tendsto μ l (𝓝 μ₀)` in `MeasureTheory.ProbabilityMeasure E`.

## What Mathlib already has

Most of the elementary theory is present and is **not** to be rebuilt. In
`Mathlib/MeasureTheory/Measure/`:

* `ext_of_forall_integral_eq_of_IsFiniteMeasure` and
  `ext_of_forall_lintegral_eq_of_IsFiniteMeasure` in `HasOuterApproxClosed.lean`,
  with the bundled `FiniteMeasure.ext_of_forall_integral_eq` and
  `FiniteMeasure.ext_of_forall_lintegral_eq` in `FiniteMeasure.lean`: the bounded
  continuous functions separate finite Borel measures.
* `ext_of_forall_mem_subalgebra_integral_eq_of_polish` and
  `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
  in `FiniteMeasureExt.lean`: a `StarSubalgebra` of `E →ᵇ 𝕜` separating points
  separates finite measures, for `[RCLike 𝕜]`.
* `FiniteMeasure.tendsto_iff_forall_integral_tendsto`,
  `FiniteMeasure.tendsto_of_forall_integral_tendsto`, the `lintegral`,
  `testAgainstNN` and `weakDual` variants, and the same for
  `ProbabilityMeasure` together with
  `ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto`: the bounded
  continuous functions are convergence determining, in both directions.
* `ProbabilityMeasure.tendsto_iff_tendsto_charFun` in `LevyConvergence.lean`:
  Lévy's theorem, so the characteristic functions are a convergence determining
  class on a finite dimensional inner product space.
* `FiniteMeasure.tendsto_map_of_tendsto_of_continuous`,
  `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` and
  `FiniteMeasure.continuous_map`: the continuous mapping theorem for maps that
  are continuous everywhere.
* Portmanteau, the Lévy–Prokhorov metric, `IsTightMeasureSet` and Prokhorov's
  theorem; and in `Mathlib/MeasureTheory/Function/UniformIntegrable.lean` the
  `UniformIntegrable` and `UnifIntegrable` theory with `uniformIntegrable_iff`
  and the Vitali convergence theorems for convergence in measure.

What follows is what that leaves.

## Milestone 1: the two classes as predicates, and the missing instances

Mathlib states the results above as `ext_of_…` and `tendsto_…` theorems and has
no predicate for a class of functions. Downstream a predicate is needed, because
"`Φ` is separating" occurs as a **hypothesis** of the càdlàg modification
theorem in the roadmap **MartingaleProblems**. So introduce the two predicates,
tie them to the existing theorems, and prove the instances Mathlib lacks.

* `MeasureTheory.IsSeparating Γ` for `Γ : Set (E → ℝ)`: two finite Borel
  measures integrating every member of `Γ` alike are equal. Monotone in `Γ`.
* `MeasureTheory.IsConvergenceDetermining Γ` for `Γ : Set (E → ℝ)`: pointwise
  convergence of the integrals along `Γ` implies weak convergence. Monotone in
  `Γ`, and `IsConvergenceDetermining.isSeparating`.
* The two bridging lemmas: `isSeparating_setOf_boundedContinuous` from
  `ext_of_forall_integral_eq_of_IsFiniteMeasure`, and
  `isConvergenceDetermining_setOf_boundedContinuous` from
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. These are one line
  each and exist so that no later proof reaches past the predicate.
* `IsSeparating.of_subalgebra`, from
  `ext_of_forall_mem_subalgebra_integral_eq_of_polish`.
* **Missing, and the reason this milestone exists.** The Stone–Weierstrass step
  for the *convergence* notion: on a Polish space, a subalgebra of `E →ᵇ ℝ` that
  separates points and vanishes nowhere is convergence determining. Mathlib
  proves the separating half only. The extra content is that density in the
  topology of uniform convergence on compact sets suffices, which is where
  tightness enters — `IsTightMeasureSet` and
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure` reduce the estimate to
  a compact set.
* **Missing.** Stability under uniformly bounded pointwise limits: if `Γ` is
  separating and every member of `Γ` is the pointwise limit of a uniformly
  bounded sequence from `Γ'`, then `Γ'` is separating. Dominated convergence;
  the same for the convergence determining notion.
* **Missing.** Products, for an **arbitrary index** `ι`, not only a finite one.
  For measurable spaces `S i`, `i : ι`, with `Γ i` separating on `S i`, the
  functions `fun x ↦ ∏ i ∈ J, f i (x i)` with `J : Finset ι` and `f i ∈ Γ i` are
  separating on `Π i, S i`; and the same statement for convergence determining
  classes when `ι` is countable and the `S i` are Polish. `FiniteMeasurePi.lean`
  has the product measure and the continuity of the product map, but not this.
  It is the statement that makes finite dimensional distributions determine a
  law — for a process the index is the time set, so the finite case does not
  suffice. The determining sets of **MartingaleProblems** Milestone 3 are its
  special case `Γ i` all bounded measurable, where the separating hypothesis is
  vacuous, and `isDetermining_products` is proved there directly from
  `induction_on_mulSystem`; what this point adds is that a *separating* `Γ i` —
  the bounded continuous functions, or a countable subfamily of them — already
  suffices at each factor. The proof is the functional monotone class theorem of
  Milestone 5 applied to those products, which form a multiplicative system
  generating the product σ-algebra. The convergence determining half is the
  weaker of the two in reach: the one place in Ethier–Kurtz where it does the
  work is the last step of Corollary 3.9.2, which passes from the convergence of
  `(g 1, ..., g k) ∘ X n` for finite families out of a dense subalgebra to the
  convergence of the finite dimensional distributions. The route through
  Theorem 3.9.1 and Theorem 3.9.4, which is the one **SkorokhodSpace**
  Milestone 8 and **MartingaleProblems** Milestone 11 take, reaches the same
  conclusion by relative compactness and identification of the limit, and does
  not pass through it.
* **Missing.** On a Polish space there is a countable convergence determining
  set of bounded uniformly continuous functions, and a countable separating set.
* **Missing.** The conditional form, `IsSeparating.ae_eq_of_forall_condExp_eq`.
  Let `E` be standard Borel, `m ≤ mΩ` a sub-σ-algebra, `Γ ⊆ E →ᵇ ℝ` separating,
  and `U V : Ω → E` measurable with `V` `m`-measurable. If
  `P[f ∘ U | m] =ᵐ[P] f ∘ V` for every `f ∈ Γ`, then `U =ᵐ[P] V`. This is the
  last step of the absolute continuity theorem in **MartingaleProblems**, and it
  is the one place where a separating class is used against a σ-algebra rather
  than against a second measure. Two steps.
  * Conditional equality in law: for `G` with `MeasurableSet[m] G`, the two
    finite measures `(P.restrict G).map U` and `(P.restrict G).map V` integrate
    every `f ∈ Γ` alike, by the defining property of `condExp` against the
    bounded `m`-measurable indicator of `G`; so `IsSeparating` gives
    `P (U ⁻¹' B ∩ G) = P (V ⁻¹' B ∩ G)` for every Borel `B`. No normalization
    and no case `P G = 0`, because `IsSeparating` is stated for finite measures.
  * `U ⁻¹' B =ᵐ[P] V ⁻¹' B` for each Borel `B`: take `G = V ⁻¹' B`, which is in
    `m` because `V` is `m`-measurable, and then its complement. Conclude with
    `Filter.EventuallyEq.of_forall_separating_preimage` of
    `Mathlib/Order/Filter/CountableSeparatingOn.lean`, whose hypothesis
    `HasCountableSeparatingOn E MeasurableSet Set.univ` is
    `MeasurableSpace.CountablySeparated E`, supplied for a standard Borel `E` by
    `MeasurableSpace.CountablyGenerated` and `MeasurableSpace.SeparatesPoints`
    (`Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean`, and
    `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean` for the instance
    from `BorelSpace` and `SecondCountableTopology`).

  The countability is thus the state space's, not `Γ`'s: no countable subfamily
  of `Γ` is chosen, and none exists in general. The separability of `E` is used
  only through `CountablySeparated`, and a regular conditional distribution of
  `U` given `m` is not needed — `condDistrib` of
  `Mathlib/Probability/Kernel/CondDistrib.lean` conditions on a map and
  `condExpKernel` of `Mathlib/Probability/Kernel/Condexp.lean` needs `Ω` itself
  standard Borel, and neither hypothesis holds here.

## Milestone 2: the continuous mapping theorem for almost everywhere continuous maps

Mathlib has the theorem for continuous `f`. What the convergence theory needs is
the version where `f` is merely Borel and continuous off a null set of the
limit; the set of continuity points is Borel, so the hypothesis is meaningful.

* `MeasureTheory.ProbabilityMeasure.tendsto_map_of_measure_setOf_continuousAt_eq_one`:
  for `E`, `E'` separable metric, `h : E → E'` Borel, `μ n → μ` weakly and
  `μ {x | ContinuousAt h x} = 1`, one has `(μ n).map h → μ.map h` weakly.
  Recover `tendsto_map_of_tendsto_of_continuous` as the case where the set is
  everything.
* `measurableSet_setOf_continuousAt`, if Mathlib does not already have the
  continuity set as a `MeasurableSet`; it is a countable intersection of open
  sets.
* The random variable form, for `E`-valued random variables `X n`, `X` with
  `X n → X` in distribution and `ℙ {ω | ContinuousAt h (X ω)} = 1`.
* The Slutsky form: `X n → X` in distribution and `dist (X n) (Y n) → 0` in
  probability imply `Y n → X` in distribution.

## Milestone 3: the space of laws, and the Skorokhod representation theorem

Let `E` be a separable metric space.

Mathlib metrizes the topology of convergence in distribution — the instance is
`MeasureTheory.instMetrizableSpaceProbabilityMeasure`
(`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean:695`), for `E`
pseudometrizable separable and Borel — and stops there. The two properties that
make `ProbabilityMeasure E` a space one can run a subsequence argument in are
absent: neither `SeparableSpace (ProbabilityMeasure E)` nor complete
metrizability of it occurs anywhere in Mathlib. They come first, because the
Skorokhod representation below and every relative compactness argument
downstream live in this space.

Where each statement lives is fixed by Mathlib's design. `LevyProkhorov` is a
one-field structure wrapping a measure (`LevyProkhorovMetric.lean:259`), and the
distance instances sit on it: `LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure`
(`:311`) and, for `E` Borel, `LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure`
(`:336`). `ProbabilityMeasure E` itself carries the topology of convergence in
distribution and no uniformity, so `CompleteSpace (ProbabilityMeasure E)` is not
a statement one can write down. Completeness is stated on the synonym, and what
crosses back along `LevyProkhorov.probabilityMeasureHomeomorph` (`:676`) is
`IsCompletelyMetrizableSpace`, which is what `PolishSpace` is defined from. The
rule for the whole milestone: a **uniform** statement about the space of laws is
made on `LevyProkhorov (ProbabilityMeasure E)`, a **topological** one on
`ProbabilityMeasure E`, and the homeomorphism carries the second kind across.

* `MeasureTheory.ProbabilityMeasure.separableSpace`: for `E` a separable
  pseudometric space with `[OpensMeasurableSpace E]`, `ProbabilityMeasure E` is
  separable. The countable dense set is the finitely supported measures with
  rational masses at points of a countable dense sequence of `E`
  (`TopologicalSpace.exists_dense_seq`); the estimate is run in the
  Lévy–Prokhorov pseudometric through `probabilityMeasureHomeomorph`, and the
  partition of `E` into countably many measurable sets of diameter at most `ε`
  that it needs is `MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le`
  (`LevyProkhorovMetric.lean:540`). Completeness of `E` is nowhere used.
* `MeasureTheory.ProbabilityMeasure.secondCountableTopology`: the item above,
  read on the synonym, where there is a uniformity to argue with —
  `UniformSpace.secondCountable_of_separable`
  (`Mathlib/Topology/UniformSpace/Cauchy.lean:932`) asks for a uniform space with
  countably generated uniformity and does not apply to `ProbabilityMeasure E`
  itself — and carried back by `Homeomorph.secondCountableTopology`
  (`Mathlib/Topology/Homeomorph/Lemmas.lean:37`).
* `MeasureTheory.isTightMeasureSet_of_forall_exists_finite_iUnion_ball`: on a
  complete second countable metric space, a set `S` of probability measures is
  tight as soon as for every `ε > 0` and every `r > 0` there is a finite
  `F ⊆ E` with `μ (⋃ x ∈ F, ball x r)ᶜ ≤ ε` for every `μ ∈ S` — uniform total
  boundedness in measure. This is the skeleton of the proof of
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure`
  (`Mathlib/MeasureTheory/Measure/Prokhorov.lean:634`), where it is inlined:
  the compact set `⋂ m, ⋃ i ≤ k m, closure (ball (D i) (u m))`, the summation of
  the errors over `m`, and `TotallyBounded.isCompact_of_isClosed` are lines
  640–704 of that file and use the compactness hypothesis only through the one
  step `exists_measure_iUnion_gt_of_isCompact_closure` (`:573`). Factoring it out
  costs nothing there — that theorem becomes its corollary — and it is what the
  completeness below needs, since a Cauchy sequence has no compact closure to
  start from.
* `MeasureTheory.LevyProkhorov.completeSpace_probabilityMeasure`: for `E` a
  complete separable metric space, `CompleteSpace (LevyProkhorov (ProbabilityMeasure E))`.
  Three steps.
  * A Cauchy sequence `μ` is tight. Fix `ε` and `r` and take `N` with
    `dist (μ n) (μ N) < min (r/2) (ε/2)` for `n ≥ N`. Each single measure is
    tight by Ulam's theorem, which Mathlib has as
    `MeasureTheory.isTightMeasureSet_singleton`
    (`Mathlib/MeasureTheory/Measure/Tight.lean:99`, under
    `[IsCompletelyPseudoMetrizableSpace E] [SecondCountableTopology E] [BorelSpace E]`),
    and the finite head `μ 0, …, μ N` is tight by
    `MeasureTheory.IsTightMeasureSet.union` (`Tight.lean:119`); covering its
    compact set by finitely many `r/2`-balls gives `F`, and for `n > N` the
    Lévy–Prokhorov inequality applied to `B = ⋃ x ∈ F, ball x (r/2)` with
    `B` thickened by `r/2` inside `⋃ x ∈ F, ball x r` gives the same bound.
    The previous item then applies.
  * `isCompact_closure_of_isTightMeasureSet` (`Measure/Prokhorov.lean:530`) turns
    the tightness into a compact closure, and since `ProbabilityMeasure E` is
    metrizable a compact set in it is sequentially compact, so a subsequence
    converges.
  * A Cauchy sequence with a convergent subsequence converges.
* `MeasureTheory.ProbabilityMeasure.isCompletelyMetrizableSpace`: for `E` Polish
  and Borel, transport the previous item along `probabilityMeasureHomeomorph`
  with `Homeomorph.isClosedEmbedding`
  (`Mathlib/Topology/Homeomorph/Defs.lean:297`) and
  `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
  (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean:249`).
* `MeasureTheory.ProbabilityMeasure.polishSpace`: for `E` Polish,
  `ProbabilityMeasure E` is Polish. Nothing is left to prove: `PolishSpace` is
  `SecondCountableTopology` together with `IsCompletelyMetrizableSpace`
  (`Mathlib/Topology/MetricSpace/Polish.lean:62`) and the instance at `:65`
  builds it from separability and complete metrizability, so this is the first
  and the fourth item. Here the completeness of `E` is used; separability alone
  gives the first two items and the whole of the rest of this milestone.

The representation theorem itself:

* `MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le_null_frontier`:
  for a finite measure `μ` on a separable metric space `E` and `ε > 0`, a
  countable measurable partition of `E` into sets of diameter at most `ε` all of
  whose frontiers are `μ`-null. Mathlib's partition
  (`LevyProkhorovMetric.lean:540`) is built from balls of one fixed radius and
  says nothing about frontiers. The radii are chosen one per point of a countable
  dense sequence by `MeasureTheory.exists_null_frontier_thickening`
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean:401`, which is
  `MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion`,
  `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:305`, applied to the
  spheres) together with `Metric.thickening_singleton`
  (`Mathlib/Topology/MetricSpace/Thickening.lean:157`) to read a thickening of a
  point as a ball; `disjointed` then keeps the frontiers null, because
  `frontier_inter_subset`, `frontier_union_subset` and `frontier_compl`
  (`Mathlib/Topology/Closure.lean:537,544,528`) bound the frontier of a finite
  Boolean combination by the union of the frontiers. This is the step that
  carries the whole Skorokhod approximation.
* `MeasureTheory.ProbabilityMeasure.exists_ae_tendsto_of_tendsto`: if
  `μ n → μ` weakly, there is a probability space and `E`-valued random
  variables `X n`, `X` on it with laws `μ n`, `μ` and `X n → X` almost surely.
  Separability is the only hypothesis; the construction uses the partition of
  the previous item, so that `Portmanteau`'s
  `MeasureTheory.tendsto_measure_of_null_frontier` (`Portmanteau.lean:243`)
  applies to each piece, and the unit interval with Lebesgue measure as the
  common space.
* The version for a single limit along a filter with a countable basis.
* The converse direction, almost sure convergence implies weak convergence of
  the laws, from `MeasureTheory.tendsto_of_ae_tendsto` or directly.

## Milestone 4: uniform integrability against convergence in distribution

Mathlib's uniform integrability theory is about a single measure: it gives
`uniformIntegrable_iff` and the Vitali convergence theorems for convergence in
measure. Absent is the link to convergence in distribution, where the random
variables live on different spaces and only their laws are comparable. That link
is what the convergence theorem of **MartingaleProblems** consumes, three times.

* `tendsto_integral_of_tendsto_of_uniformIntegrable`: if the real random
  variables `X n` converge in distribution to `X` and `{X n}` is uniformly
  integrable, then `X` is integrable and `𝔼[X n] → 𝔼[X]`. Prove it through the
  Skorokhod representation of Milestone 3, which puts everything on one space
  and reduces the statement to Mathlib's Vitali theorem.
* The truncation characterization for a family of real random variables on
  varying spaces: uniform integrability is equivalent to
  `lim_{N→∞} sup_n 𝔼[|X n| - min |X n| N] = 0`. State it in that form, since it
  is the form the convergence proof uses; relate it to `uniformIntegrable_iff`.
* The de la Vallée-Poussin form: uniform integrability holds if and only if
  there is a convex increasing `φ` on `[0,∞)` with `φ x / x → ∞` and
  `sup_n 𝔼[φ (|X n|)] < ∞`.
* Stability, each as a separate lemma: a family dominated by a uniformly
  integrable family is uniformly integrable; a uniformly bounded family is;
  the product of a uniformly integrable family with a uniformly bounded family
  is; and a finite union of uniformly integrable families is.

## Milestone 5: the functional monotone class theorem

Mathlib has Dynkin's π–λ theorem for **sets**, as the induction principle
`induction_on_inter` in `Mathlib/MeasureTheory/PiSystem.lean`. The functional
form — a linear space of bounded functions containing the constants and a
multiplicative class `K`, closed under bounded monotone limits, contains every
bounded `σ K`-measurable function — is absent; `docs/1000.yaml`
carries the monotone class theorem as `Q242045` with no declaration. It is the
tool the products of Milestone 1 rest on, and the determining sets of the
roadmap **MartingaleProblems** are built with it. `Ω` here is a bare measurable
space; no topology is involved.

* `MeasureTheory.IsMulSystem K` for `K : Set (Ω → ℝ)`, defined as
  `∀ f ∈ K, ∀ g ∈ K, f * g ∈ K`, the multiplicative counterpart of
  `IsPiSystem`. With it `isMulSystem_indicator_of_isPiSystem`: for a π-system
  `𝒞` the indicators `Set.indicator s 1` with `s ∈ 𝒞` form a multiplicative
  system.
* `MeasureTheory.generateFromFuns K`, defined as
  `⨆ f ∈ K, MeasurableSpace.comap f (borel ℝ)` with `MeasurableSpace.comap` of
  `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`, together with
  `measurable_generateFromFuns_of_mem` for `f ∈ K`, monotonicity in `K`, and the
  identity `generateFromFuns (indicators of 𝒞) = MeasurableSpace.generateFrom 𝒞`
  that connects the functional form to `induction_on_inter`.
* `MeasureTheory.induction_on_mulSystem`: let `K : Set (Ω → ℝ)` be a
  multiplicative system of bounded functions and `P : (Ω → ℝ) → Prop` with
  `P f` for every `f ∈ K`; `P (fun _ ↦ c)` for every constant `c`; `P` preserved
  by addition and by scalar multiplication; and `P` preserved by bounded
  monotone limits, that is `P g` whenever `f : ℕ → Ω → ℝ` is pointwise monotone,
  satisfies `P (f n)` for every `n`, is uniformly bounded and tends to `g`
  pointwise. Then `P f` for every bounded `generateFromFuns K`-measurable `f`.
  State it `@[elab_as_elim]`, as `induction_on_inter` is.
* `MeasureTheory.ext_of_forall_integral_eq_of_isMulSystem`: two finite measures
  agreeing on `∫ f` for every `f` in a multiplicative system of bounded
  functions, and on the total mass, agree on `generateFromFuns K`.
* `MeasureTheory.integral_mul_eq_zero_of_isMulSystem`: for `μ` finite and `g`
  integrable, `∫ g * f ∂μ = 0` for every `f ∈ K` implies `∫ g * f ∂μ = 0` for
  every bounded `generateFromFuns K`-measurable `f`; and the conditional form,
  `∫ X * f ∂μ = ∫ Y * f ∂μ` for every `f ∈ K` implies
  `μ[X | generateFromFuns K] =ᵐ[μ] μ[Y | generateFromFuns K]`. This is the form
  in which the martingale property is verified.
* The `RCLike` variants of all of the above, obtained from the real ones by
  splitting into real and imaginary part.
