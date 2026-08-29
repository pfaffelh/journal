# Weak convergence: separating classes, the continuous mapping theorem, and Skorokhod representation

Mathlib has weak convergence of measures on a metric space (portmanteau in
`Mathlib/MeasureTheory/Measure/Portmanteau.lean`, the Lévy–Prokhorov metric
`MeasureTheory.levyProkhorovDist`, tightness `MeasureTheory.IsTightMeasureSet`
and Prokhorov's theorem in `Mathlib/MeasureTheory/Measure/Prokhorov.lean`).
Three further pieces of the standard theory are wanted, all of them used
pervasively downstream: classes of functions that determine a measure or its
convergence, the continuous mapping theorem for maps that are continuous only
almost everywhere, and the Skorokhod representation theorem.

Throughout, `E` is a metric space, `Ω` a measurable space, and measures are
Borel probability measures. Weak convergence is
`Filter.Tendsto μ l (𝓝 μ₀)` in `MeasureTheory.ProbabilityMeasure E`.

## Milestone 1: separating classes

A set `Γ ⊆ (E → ℝ)` of bounded measurable functions is *separating* when two
Borel probability measures that integrate every member of `Γ` to the same value
are equal. Mathlib has one instance of this pattern,
`MeasureTheory.FiniteMeasure.ext_of_forall_mem_subalgebra_integral_eq_of_polish`
in `Mathlib/MeasureTheory/Measure/FiniteMeasureExt.lean`, for a subalgebra of
`C(E, ℝ)` that separates points on a Polish space. Wanted is the notion itself,
with its basic theory.

* `MeasureTheory.IsSeparating Γ` for `Γ : Set (E → ℝ)`, defined as above.
* Monotonicity in `Γ`, and stability under passing to a superset inside the
  bounded measurable functions.
* `C(E, ℝ) ∩ bounded` is separating on a metric space; `Cb(E, ℝ)` is separating.
* A subalgebra of `C(E, ℝ)` that separates points and contains the constants is
  separating on a Polish space. This restates the existing Mathlib lemma in the
  new vocabulary and is proved from it.
* Uniformly bounded pointwise limits: if `Γ` is separating and every member of
  `Γ` is a pointwise limit of a uniformly bounded sequence from `Γ'`, then `Γ'`
  is separating.
* On a Polish space, a countable separating set exists.

A set `Γ` is *convergence determining* when, for probability measures `μ n` and
`μ` on `E`, `∀ f ∈ Γ, Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂μ))`
implies `μ n → μ` weakly.

* `MeasureTheory.IsConvergenceDetermining Γ`.
* Every convergence determining set is separating.
* `Cb(E, ℝ)` is convergence determining, immediately from the definition of the
  weak topology.
* On a Polish space, a countable convergence determining set of bounded
  uniformly continuous functions exists. Deduce it from the separability of
  `C(E,ℝ)` on compacts together with tightness.
* The Stone–Weierstrass criterion: on a Polish space, a subalgebra of `Cb(E, ℝ)`
  that separates points, vanishes nowhere and is closed under complex
  conjugation is convergence determining. Mathlib's
  `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`
  supplies the density statement; the content here is that density in the
  topology of uniform convergence on compact sets suffices, using tightness to
  reduce to a compact set.

## Milestone 2: the continuous mapping theorem

Let `E`, `E'` be separable metric spaces, `h : E → E'` Borel measurable, and
`C h` the set of points at which `h` is continuous.

* `MeasureTheory.ProbabilityMeasure.tendsto_map_of_measure_continuousAt_eq_one`:
  if `μ n → μ` weakly and `μ (C h) = 1`, then `(μ n).map h → μ.map h` weakly.
  `C h` is Borel — prove `isGO_setOf_continuousAt` or reuse
  `Mathlib/Topology/ContinuousOn.lean` — so the hypothesis is meaningful.
* The random-variable form: for `E`-valued random variables `X n`, `X` with
  `X n → X` in distribution and `ℙ {ω | ContinuousAt h (X ω)} = 1`, one has
  `h ∘ X n → h ∘ X` in distribution.
* The Slutsky form: if `X n → X` in distribution and `dist (X n) (Y n) → 0` in
  probability, then `Y n → X` in distribution.
* Corollaries for the two standard cases: `h` continuous everywhere, and `h`
  the restriction of a continuous map to a Borel set of full measure.

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

## Milestone 4: Vitali's theorem in the form used downstream

Mathlib has `MeasureTheory.UniformIntegrable` and
`MeasureTheory.uniformIntegrable_iff`. Wanted is the statement that links it to
weak convergence.

* If `X n → X` in distribution as real random variables and `{X n}` is uniformly
  integrable, then `X` is integrable and `𝔼[X n] → 𝔼[X]`.
* The characterization `lim_{N→∞} sup_n 𝔼[|X n| - min |X n| N] = 0` as an
  equivalent of uniform integrability for a family of real random variables, and
  the de la Vallée-Poussin form: uniform integrability holds if and only if
  there is a convex increasing `φ` with `φ x / x → ∞` and `sup_n 𝔼[φ (|X n|)] < ∞`.
* Stability: a family dominated by a uniformly integrable family is uniformly
  integrable; a uniformly bounded family is uniformly integrable; the product of
  a uniformly integrable family with a uniformly bounded family is uniformly
  integrable.
