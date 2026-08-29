# Weak convergence: separating classes, the continuous mapping theorem, and Skorokhod representation

Weak convergence of measures on a metric space is well developed in Mathlib,
and the next section says how far. Four things are wanted beyond it, each used
pervasively downstream: the two classes of functions that determine a measure or
its convergence, as predicates and with the instances Mathlib does not prove;
the continuous mapping theorem for maps continuous only almost everywhere; the
Skorokhod representation theorem; and the link between uniform integrability and
convergence in distribution.

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
  `isTightMeasureSet_of_isCompact_closure` reduce the estimate to a compact set.
* **Missing.** Stability under uniformly bounded pointwise limits: if `Γ` is
  separating and every member of `Γ` is the pointwise limit of a uniformly
  bounded sequence from `Γ'`, then `Γ'` is separating. Dominated convergence;
  the same for the convergence determining notion.
* **Missing.** Products. For measurable spaces `S 1, …, S k` with `Γ i`
  separating on `S i`, the products `fun x ↦ ∏ i, f i (x i)` with `f i ∈ Γ i`
  are separating on `Π i, S i`; and the same statement for convergence
  determining classes when the `S i` are Polish. `FiniteMeasurePi.lean` has the
  product measure and the continuity of the product map, but not this. It is the
  statement that makes finite dimensional distributions determine a law, and
  every determining set in **MartingaleProblems** is built from it.
* **Missing.** On a Polish space there is a countable convergence determining
  set of bounded uniformly continuous functions, and a countable separating set.

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

## Milestone 3: the Skorokhod representation theorem

Let `E` be a separable metric space.

* `MeasureTheory.ProbabilityMeasure.exists_ae_tendsto_of_tendsto`: if
  `μ n → μ` weakly, there is a probability space and `E`-valued random
  variables `X n`, `X` on it with laws `μ n`, `μ` and `X n → X` almost surely.
  Separability is the only hypothesis; the standard construction uses a
  countable partition of `E` into sets of small diameter whose boundaries are
  `μ`-null, and the unit interval with Lebesgue measure as the common space.
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
