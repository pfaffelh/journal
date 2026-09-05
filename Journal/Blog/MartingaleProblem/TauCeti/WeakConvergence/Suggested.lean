/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Topology.MetricSpace.Polish

/-!
# Suggested signatures for the weak convergence roadmap

Prototypes only.

**Status: not type-checked.**  The run of 2026-09-05 that revised this file had
no permission to execute `lean` or `lake`, so every declaration below is checked
only against the Mathlib sources (`upstream/master`, `251e86bd1fa`): each cited
name exists, is not `deprecated`, and its instance arguments are read off the
surrounding `variable` block.  That is weaker than a type check and is meant to
be replaced by one.
-/

open Filter Topology MeasureTheory Set ENNReal
open scoped BoundedContinuousFunction

namespace MeasureTheory

variable {E E' : Type*} [MeasurableSpace E] [MeasurableSpace E']

/-! ## Milestone 1: the two predicates, and the instances Mathlib lacks

Mathlib proves that the bounded continuous functions separate finite measures
(`ext_of_forall_integral_eq_of_IsFiniteMeasure`,
`MeasureTheory/Measure/HasOuterApproxClosed.lean:269`) and are convergence
determining (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`,
`MeasureTheory/Measure/ProbabilityMeasure.lean:364`), and that a
`StarSubalgebra` separating points separates finite measures
(`ext_of_forall_mem_subalgebra_integral_eq_of_polish`,
`MeasureTheory/Measure/FiniteMeasureExt.lean:72`).  The predicates exist
because `IsSeparating` occurs as a hypothesis downstream. -/

/-- A set of bounded measurable functions that separates finite Borel measures. -/
def IsSeparating (Γ : Set (E → ℝ)) : Prop :=
  ∀ (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
    (∀ f ∈ Γ, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν

/-- A set of functions along which weak convergence can be tested.

The topology on `ProbabilityMeasure E` is the one induced from `FiniteMeasure E`
(`MeasureTheory/Measure/ProbabilityMeasure.lean:307`); it is an instance exactly
under `[TopologicalSpace E]` and `[OpensMeasurableSpace E]`, so both are
hypotheses here. -/
def IsConvergenceDetermining [TopologicalSpace E] [OpensMeasurableSpace E]
    (Γ : Set (E → ℝ)) : Prop :=
  ∀ (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E),
    (∀ f ∈ Γ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E)))) → Tendsto μ atTop (𝓝 ν)

theorem IsSeparating.mono {Γ Γ' : Set (E → ℝ)} (h : IsSeparating Γ) (hsub : Γ ⊆ Γ') :
    IsSeparating Γ' := sorry

theorem IsConvergenceDetermining.mono [TopologicalSpace E] [OpensMeasurableSpace E]
    {Γ Γ' : Set (E → ℝ)} (h : IsConvergenceDetermining Γ) (hsub : Γ ⊆ Γ') :
    IsConvergenceDetermining Γ' := sorry

/-- A convergence determining class separates **probability** measures: apply the
hypothesis to the constant sequence and use that `ProbabilityMeasure E` is
Hausdorff (`ProbabilityMeasure.t2Space`,
`MeasureTheory/Measure/ProbabilityMeasure.lean:440`, which is where
`HasOuterApproxClosed` is needed).

It does **not** separate finite measures, so there is no
`IsConvergenceDetermining.isSeparating`: on a one-point space every set of
functions, `∅` included, is convergence determining, while `∅` does not tell the
Dirac measure from twice the Dirac measure.  A convergence determining class
never has to see the total mass. -/
theorem IsConvergenceDetermining.eq_of_forall_integral_eq [TopologicalSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] {Γ : Set (E → ℝ)}
    (h : IsConvergenceDetermining Γ) {μ ν : ProbabilityMeasure E}
    (heq : ∀ f ∈ Γ, ∫ x, f x ∂(μ : Measure E) = ∫ x, f x ∂(ν : Measure E)) :
    μ = ν := sorry

/-- One line from `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`. -/
theorem isSeparating_setOf_boundedContinuous [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] :
    IsSeparating {f : E → ℝ | ∃ g : E →ᵇ ℝ, ⇑g = f} := sorry

/-- One line from `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. -/
theorem isConvergenceDetermining_setOf_boundedContinuous [TopologicalSpace E]
    [OpensMeasurableSpace E] :
    IsConvergenceDetermining {f : E → ℝ | ∃ g : E →ᵇ ℝ, ⇑g = f} := sorry

/-- From `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish`.  That
theorem is stated for a `StarSubalgebra 𝕜 (E →ᵇ 𝕜)` with `[RCLike 𝕜]` and the
hypothesis `(A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints`; over `ℝ` the star
operation is trivial, and the real form of the separation hypothesis is the one
that occurs inside its proof
(`Analysis/SpecialFunctions/MulExpNegMulSqIntegral.lean:161`). -/
theorem IsSeparating.of_subalgebra [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hsep : (A.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints) :
    IsSeparating {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := sorry

/-- Missing from Mathlib: the Stone-Weierstrass step for the *convergence*
notion.  Mathlib proves the separating half only. -/
theorem isConvergenceDetermining_of_separatesPoints [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hsep : (A.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints)
    (hvan : ∀ x : E, ∃ g ∈ A, g x ≠ 0) :
    IsConvergenceDetermining {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := sorry

/-- Missing from Mathlib: products, for an **arbitrary** index type.  This is what
makes finite dimensional distributions determine a law; for a process the index
is the time set, so the finite case does not suffice. -/
theorem isSeparating_pi {ι : Type*} {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (Γ : ∀ i, Set (S i → ℝ)) (h : ∀ i, IsSeparating (Γ i)) :
    IsSeparating {f : (∀ i, S i) → ℝ |
      ∃ (J : Finset ι) (g : ∀ i, S i → ℝ), (∀ i ∈ J, g i ∈ Γ i) ∧
        f = fun x => ∏ i ∈ J, g i (x i)} := sorry

/-- The conditional form, and the one place where a separating class is used
against a σ-algebra rather than against a second measure.  It is the last step of
the absolute continuity theorem in the roadmap **MartingaleProblems**.

Two steps, neither of which needs a regular conditional distribution.  First,
conditional equality in law: for `G` with `MeasurableSet[m] G`, the two finite
measures `(P.restrict G).map U` and `(P.restrict G).map V` integrate every
`f ∈ Γ` alike, by `setIntegral_condExp`
(`MeasureTheory/Function/ConditionalExpectation/Basic.lean:232`), so
`IsSeparating` gives `P (U ⁻¹' B ∩ G) = P (V ⁻¹' B ∩ G)` for Borel `B`.  Second,
`U ⁻¹' B =ᵐ[P] V ⁻¹' B` for each Borel `B`, by taking `G = V ⁻¹' B` and then its
complement, and `Filter.EventuallyEq.of_forall_separating_preimage`
(`Order/Filter/CountableSeparatingOn.lean:257`) concludes.  Its hypothesis
`HasCountableSeparatingOn E MeasurableSet Set.univ` is
`MeasurableSpace.CountablySeparated E`
(`MeasureTheory/MeasurableSpace/CountablyGenerated.lean:322`, with the instance
in both directions at `:326` and `:329`).

The countability is the state space's, not `Γ`'s: no countable subfamily of `Γ`
is chosen, and none exists in general. -/
theorem IsSeparating.ae_eq_of_forall_condExp_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    [MeasurableSpace.CountablySeparated E]
    {Γ : Set (E → ℝ)} (hΓ : IsSeparating Γ)
    (hΓb : ∀ f ∈ Γ, ∃ g : E →ᵇ ℝ, ⇑g = f)
    {U V : Ω → E} (hU : Measurable U) (hV : Measurable[m] V)
    (h : ∀ f ∈ Γ, P[fun ω => f (U ω) | m] =ᵐ[P] fun ω => f (V ω)) :
    U =ᵐ[P] V := sorry

/-! ## Milestone 2: the continuous mapping theorem for almost everywhere continuous maps

Mathlib has `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`
(`MeasureTheory/Measure/ProbabilityMeasure.lean:657`) for continuous maps; this
is the version the convergence theory needs.  Note that
`ProbabilityMeasure.map` (`ibid.:626`) takes the *function*, not a measurability
proof. -/

theorem tendsto_map_of_measure_setOf_continuousAt_eq_one [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] [MetricSpace E'] [BorelSpace E']
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} {h : E → E'}
    (hh : Measurable h) (hconv : Tendsto μ atTop (𝓝 ν))
    (hcont : (ν : Measure E) {x | ContinuousAt h x} = 1) :
    Tendsto (fun n => (μ n).map h) atTop (𝓝 (ν.map h)) := sorry

/-! ## Milestone 3: the space of laws, and the Skorokhod representation theorem

Mathlib metrizes the topology of convergence in distribution
(`instMetrizableSpaceProbabilityMeasure`,
`MeasureTheory/Measure/LevyProkhorovMetric.lean:695`) and stops there.  Note
where the statements have to live: the distance sits on the structure
`LevyProkhorov (ProbabilityMeasure E)`, while `ProbabilityMeasure E` carries no
uniformity, so completeness is stated on the synonym and crosses back as
`IsCompletelyMetrizableSpace` (`Topology/Metrizable/CompletelyMetrizable.lean:154`,
in namespace `TopologicalSpace`) along
`LevyProkhorov.probabilityMeasureHomeomorph` (`ibid.:676`). -/

theorem separableSpace_probabilityMeasure [PseudoMetricSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (ProbabilityMeasure E) := sorry

/-- The skeleton of the proof of `isTightMeasureSet_of_isCompact_closure`, which
Mathlib inlines there: uniform total boundedness in measure already gives
tightness.  A Cauchy sequence has no compact closure to start from, so the
completeness below needs this form.  `IsTightMeasureSet`
(`MeasureTheory/Measure/Tight.lean:55`) is a predicate on `Set (Measure E)`, and
`isCompact_closure_of_isTightMeasureSet` (`Measure/Prokhorov.lean:530`) takes it
in exactly the image form written here. -/
theorem isTightMeasureSet_of_forall_exists_finite_iUnion_ball [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {S : Set (ProbabilityMeasure E)}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∀ r : ℝ, 0 < r →
      ∃ F : Finset E, ∀ μ ∈ S, (μ : Measure E) (⋃ x ∈ F, Metric.ball x r)ᶜ ≤ ε) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := sorry

/-- Tightness of a Cauchy sequence comes from `isTightMeasureSet_singleton`
(Ulam, `MeasureTheory/Measure/Tight.lean:99`) for the finite head and from the
Lévy-Prokhorov estimate for the tail; `isCompact_closure_of_isTightMeasureSet`
then gives a convergent subsequence. -/
theorem completeSpace_levyProkhorov_probabilityMeasure [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] :
    CompleteSpace (LevyProkhorov (ProbabilityMeasure E)) := sorry

theorem isCompletelyMetrizableSpace_probabilityMeasure [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (ProbabilityMeasure E) := sorry

theorem polishSpace_probabilityMeasure [MetricSpace E] [BorelSpace E] [PolishSpace E] :
    PolishSpace (ProbabilityMeasure E) := sorry

/-- Mathlib's `SeparableSpace.exists_measurable_partition_diam_le`
(`MeasureTheory/Measure/LevyProkhorovMetric.lean:540`, in namespace
`MeasureTheory`, with `Ω` explicit) uses balls of one fixed radius and says
nothing about frontiers; the Skorokhod construction needs the radii chosen so
that the frontiers are null.  Its boundedness clause is kept here, because the
proof is the same disjointification of balls. -/
theorem exists_measurable_partition_diam_le_null_frontier [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ As : ℕ → Set E, (∀ n, MeasurableSet (As n)) ∧ (∀ n, Bornology.IsBounded (As n)) ∧
      (∀ n, Metric.diam (As n) ≤ ε) ∧ (∀ n, μ (frontier (As n)) = 0) ∧
      (⋃ n, As n = univ) ∧ Pairwise (fun n m : ℕ => Disjoint (As n) (As m)) := sorry

theorem exists_ae_tendsto_of_tendsto [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {μ : ℕ → ProbabilityMeasure E}
    {ν : ProbabilityMeasure E} (h : Tendsto μ atTop (𝓝 ν)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → E) (Y : Ω → E),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, P.map (X n) = (μ n : Measure E)) ∧ P.map Y = (ν : Measure E) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := sorry

/-! ## Milestone 4: uniform integrability against convergence in distribution

Mathlib's uniform integrability theory (`uniformIntegrable_iff`, the Vitali
theorems in `MeasureTheory/Function/UniformIntegrable.lean`) is about a single
measure.  This is the statement for laws on varying spaces; the Skorokhod
representation above reduces it to Mathlib's. -/

/-- Uniform integrability of a family of real random variables living on
different spaces, stated by truncation because that is the form the convergence
proof uses. -/
def IsUniformlyIntegrableLaws (μ : ℕ → ProbabilityMeasure ℝ) : Prop :=
  Tendsto (fun N : ℕ => ⨆ n, ∫ x, (|x| - min |x| N) ∂(μ n : Measure ℝ)) atTop (𝓝 0)

theorem tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto μ atTop (𝓝 ν)) (hui : IsUniformlyIntegrableLaws μ) :
    Integrable id (ν : Measure ℝ) ∧
      Tendsto (fun n => ∫ x, x ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, x ∂(ν : Measure ℝ))) :=
  sorry

end MeasureTheory
