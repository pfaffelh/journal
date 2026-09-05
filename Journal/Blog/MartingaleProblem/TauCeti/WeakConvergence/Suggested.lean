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

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1` on
2026-09-05.  Every declaration elaborates; the remaining `sorry`s are the
statements' own proofs, which is what this file is for.

Five of Milestone 1 are no longer `sorry` but proved: `IsSeparating.mono`,
`IsConvergenceDetermining.mono`, `IsConvergenceDetermining.isSeparating`,
`isSeparating_setOf_boundedContinuous` and
`isConvergenceDetermining_setOf_boundedContinuous`.

One statement is deliberately written for `upstream/master` rather than for
`v4.33.1`, and so does not elaborate here:
`tendsto_map_of_measure_setOf_continuousAt_eq_one` uses
`ProbabilityMeasure.map`, which on master takes the *function*
(`MeasureTheory/Measure/ProbabilityMeasure.lean:626`) and in `v4.33.1` takes an
`AEMeasurable` proof as well.  Master is what Tau Ceti builds on, so the
statement follows master.
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

/-- A set of bounded measurable functions that separates Borel measures.

Separating, over PROBABILITY measures, as in the manuscript's
`def:separating` (Ethier-Kurtz, Section 3.4).  Quantifying over finite measures
instead gives a strictly stronger notion under which
`IsConvergenceDetermining.isSeparating` is false -- on a one-point space the
empty set is convergence determining, there being only one probability measure,
but does not separate `δ` from `2δ`. -/
def IsSeparating (Γ : Set (E → ℝ)) : Prop :=
  ∀ (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
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
    IsSeparating Γ' := by
  intro μ ν _ _ hμν
  exact h μ ν fun f hf => hμν f (hsub hf)

theorem IsConvergenceDetermining.mono [TopologicalSpace E] [OpensMeasurableSpace E]
    {Γ Γ' : Set (E → ℝ)} (h : IsConvergenceDetermining Γ) (hsub : Γ ⊆ Γ') :
    IsConvergenceDetermining Γ' := by
  intro μ ν hμν
  exact h μ ν fun f hf => hμν f (hsub hf)

/-- A convergence determining class separates **probability** measures: apply the
hypothesis to the constant sequence and use that `ProbabilityMeasure E` is
Hausdorff (`ProbabilityMeasure.t2Space`,
`MeasureTheory/Measure/ProbabilityMeasure.lean:440`, which is where
`HasOuterApproxClosed` is needed).

It does **not** separate finite measures, so there is no
`IsConvergenceDetermining.isSeparating`: on a one-point space every set of
functions, `∅` included, is convergence determining, while `∅` does not tell the
Dirac measure from twice the Dirac measure.  A convergence determining class
never has to see the total mass.

With `IsSeparating` over probability measures this is the manuscript's
`def:separating`, last sentence.  Proof: test with the constant sequence
`μ_n = μ`, so `μ_n → ν` weakly, and conclude by `ProbabilityMeasure.t2Space`. -/
theorem IsConvergenceDetermining.isSeparating [TopologicalSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] {Γ : Set (E → ℝ)}
    (h : IsConvergenceDetermining Γ) : IsSeparating Γ := by
  intro μ ν _ _ hμν
  let μ' : ProbabilityMeasure E := ⟨μ, ‹_›⟩
  let ν' : ProbabilityMeasure E := ⟨ν, ‹_›⟩
  have key : Tendsto (fun _ : ℕ => μ') atTop (𝓝 ν') :=
    h _ _ fun f hf => by simp [μ', ν', hμν f hf]
  exact congrArg (fun p : ProbabilityMeasure E => (p : Measure E))
    (tendsto_nhds_unique tendsto_const_nhds key)

/-- One line from `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`,
which proves the stronger, finite measure statement. -/
theorem isSeparating_setOf_boundedContinuous [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] :
    IsSeparating {f : E → ℝ | ∃ g : E →ᵇ ℝ, ⇑g = f} := by
  intro μ ν _ _ hμν
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => hμν g ⟨g, rfl⟩

/-- One line from `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. -/
theorem isConvergenceDetermining_setOf_boundedContinuous [TopologicalSpace E]
    [OpensMeasurableSpace E] :
    IsConvergenceDetermining {f : E → ℝ | ∃ g : E →ᵇ ℝ, ⇑g = f} := by
  intro μ ν hμν
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
    fun g => hμν g ⟨g, rfl⟩

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

/-! ### The Stone-Weierstrass step for the convergence notion

Mathlib has this step **under a tightness hypothesis**:
`MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`MeasureTheory/Measure/LevyConvergence.lean:154`) says that for `E` Polish, a
`StarSubalgebra 𝕜 (E →ᵇ 𝕜)` whose image separates points, and a family
`μ : ι → ProbabilityMeasure E` with `IsTightMeasureSet {(μ n : Measure E) | n}`,
convergence of the integrals over the algebra gives `Tendsto μ 𝓕 (𝓝 μ₀)`.

The tightness hypothesis is not removable at the price of mere separation of
points, and the manuscript's `fact:stoneweierstrass` does not ask it to be: it
asks for *strong* separation.  Witness that plain separation is too weak, with
`E = ℝ` and

  `A = {f : ℝ →ᵇ ℝ | Tendsto f atTop (𝓝 (f 0))}`,

an `ℝ`-subalgebra (limits add and multiply, and so do the values at `0`)
containing the constants and separating points (for `x ≠ y` pick a continuous
function supported in a large ball with the prescribed two values, taking the
value `0` at whichever of `x`, `y` is not `0`).  For `μ n = δ n` and `μ₀ = δ 0`
every `f ∈ A` has `∫ f ∂δ n = f n → f 0 = ∫ f ∂δ 0`, while `δ n` does not
converge weakly to `δ 0`.  The family `{δ n}` is not tight, and `A` does not
strongly separate points at `0`, since `max i |h i n - h i 0| → 0` for every
finite family from `A`.

So what is missing is the passage from strong separation to tightness; the two
declarations below are that passage and the theorem it yields. -/

/-- Strong separation of points, as in the manuscript's `def:separating`: for
every `x` and every `δ > 0` some finite family from `Γ` keeps all points at
distance at least `δ` from `x` a fixed amount away from `x`.  Mathlib has
`Set.SeparatesPoints` (`Logic/Function/Basic.lean:1225`) and no strong form. -/
def StronglySeparatesPoints [PseudoMetricSpace E] (Γ : Set (E → ℝ)) : Prop :=
  ∀ (x : E) (δ : ℝ), 0 < δ → ∃ (s : Finset (E → ℝ)) (ε : ℝ), ↑s ⊆ Γ ∧ 0 < ε ∧
    ∀ y : E, δ ≤ dist y x → ∃ f ∈ s, ε ≤ |f y - f x|

/-- Take `δ = dist y x`. -/
theorem StronglySeparatesPoints.separatesPoints [MetricSpace E] {Γ : Set (E → ℝ)}
    (h : StronglySeparatesPoints Γ) : Γ.SeparatesPoints := sorry

/-- Missing from Mathlib, and the whole of what `fact:stoneweierstrass` still
owes: a strongly separating subalgebra forces tightness of any family whose
integrals over it converge.  Given this,
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` supplies the rest.

That strong separation is what does the work is visible on `E = ℝ` with the
algebra generated by `arctan`, which is strongly separating: `∫ arctan ∂δ n`
converges, to `π / 2`, and no probability measure has `∫ arctan = π / 2`, so the
hypothesis below is vacuous there rather than false. -/
theorem isTightMeasureSet_of_stronglySeparatesPoints [MetricSpace E]
    [PolishSpace E] [BorelSpace E] {ι : Type*} {𝓕 : Filter ι} [𝓕.NeBot]
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : StronglySeparatesPoints {f : E → ℝ | ∃ g ∈ A, ⇑g = f})
    {μ : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, g x ∂(μ₀ : Measure E)))) :
    IsTightMeasureSet {((μ n : ProbabilityMeasure E) : Measure E) | n} := sorry

/-- `fact:stoneweierstrass`, convergence half.  From
`isTightMeasureSet_of_stronglySeparatesPoints` and
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, whose separation
hypothesis comes from `StronglySeparatesPoints.separatesPoints`. -/
theorem isConvergenceDetermining_of_stronglySeparatesPoints [MetricSpace E]
    [PolishSpace E] [BorelSpace E] (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : StronglySeparatesPoints {f : E → ℝ | ∃ g ∈ A, ⇑g = f}) :
    IsConvergenceDetermining {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := sorry

/-- `fact:convdet` (Ethier-Kurtz, Proposition 3.4.4), first half.  Separability
alone: no completeness, and no local compactness. -/
theorem isConvergenceDetermining_setOf_uniformContinuous_isBounded_support
    [MetricSpace E] [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E] :
    IsConvergenceDetermining {f : E → ℝ | UniformContinuous f ∧
      (∃ C, ∀ x, |f x| ≤ C) ∧ Bornology.IsBounded (Function.support f)} := sorry

/-- `fact:convdet`, second half: on a locally compact separable metric space the
continuous functions of compact support are convergence determining.  The total
mass is not seen by them, and does not have to be: the measures are probability
measures on both sides. -/
theorem isConvergenceDetermining_setOf_hasCompactSupport
    [MetricSpace E] [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    [LocallyCompactSpace E] :
    IsConvergenceDetermining {f : E → ℝ | Continuous f ∧ HasCompactSupport f} := sorry

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
`IsSeparating` gives `P (U ⁻¹' B ∩ G) = P (V ⁻¹' B ∩ G)` for Borel `B` -- but
`IsSeparating` quantifies over *probability* measures, so this splits: for
`P G = 0` both sides are at most `P G`, and for `P G ≠ 0` one applies it to
`((P G)⁻¹ • P.restrict G).map U` and the same for `V`, the scaling passing
through the integrals in both directions.  Second,
`U ⁻¹' B =ᵐ[P] V ⁻¹' B` for each Borel `B`, by taking `G = V ⁻¹' B` and then its
complement, and `Filter.EventuallyEq.of_forall_separating_preimage`
(`Order/Filter/CountableSeparatingOn.lean:257`) concludes.  Its hypothesis
`HasCountableSeparatingOn E MeasurableSet Set.univ` is
`MeasurableSpace.CountablySeparated E`
(`MeasureTheory/MeasurableSpace/CountablyGenerated.lean:322`, with the instance
in both directions at `:326` and `:329`).

The countability is the state space's, not `Γ`'s: no countable subfamily of `Γ`
is chosen, and none exists in general. -/
theorem IsSeparating.ae_eq_of_forall_condExp_eq [TopologicalSpace E]
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
