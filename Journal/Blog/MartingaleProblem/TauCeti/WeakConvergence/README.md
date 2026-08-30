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
* **Missing.** Products, for an **arbitrary index** `ι`, not only a finite one.
  For measurable spaces `S i`, `i : ι`, with `Γ i` separating on `S i`, the
  functions `fun x ↦ ∏ i ∈ J, f i (x i)` with `J : Finset ι` and `f i ∈ Γ i` are
  separating on `Π i, S i`; and the same statement for convergence determining
  classes when `ι` is countable and the `S i` are Polish. `FiniteMeasurePi.lean`
  has the product measure and the continuity of the product map, but not this.
  It is the statement that makes finite dimensional distributions determine a
  law — for a process the index is the time set, so the finite case does not
  suffice — and every determining set in **MartingaleProblems** is built from
  it. The proof is the functional monotone class theorem of Milestone 5 applied
  to those products, which form a multiplicative system generating the product
  σ-algebra.
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
