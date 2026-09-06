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
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Topology.MetricSpace.Polish

/-!
# Suggested signatures for the weak convergence roadmap

Prototypes only.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1` on
2026-09-06.  Every declaration elaborates, and the only warnings are
`declaration uses 'sorry'`; those `sorry`s are the statements' own proofs, which
is what this file is for.

Twenty declarations are no longer `sorry` but proved.  Of Milestone 1:
`IsSeparating.mono`, `IsConvergenceDetermining.mono`,
`IsConvergenceDetermining.isSeparating`, `isSeparating_setOf_boundedContinuous`,
`isConvergenceDetermining_setOf_boundedContinuous` and, since 2026-09-06,
`IsSeparating.ae_eq_of_forall_condExp_eq`,
`StronglySeparatesPoints.separatesPoints` and `IsSeparating.of_subalgebra`.  Of Milestone 5, since 2026-09-06:
`indicatorFuns_mono`, `isMulSystem_indicator_of_isPiSystem`,
`measurable_generateFromFuns_of_mem`, `generateFromFuns_le_iff`,
`generateFromFuns_mono` and `generateFromFuns_indicatorFuns` -- the bridge from
`IsPiSystem` to `IsMulSystem` and from `MeasurableSpace.generateFrom` to
`generateFromFuns`, which is what the functional monotone class theorem will be
proved against -- `isPiSystem_ioiCells` and
`generateFromFuns_eq_generateFrom_ioiCells`, the π-system the induction runs
along, `of_tendstoUniformly_of_mono_lim`, its first step, and the algebraic half
of its second step: `mul_mem_span_insert_one_of_isMulSystem`,
`of_mem_span_insert_one` and `exists_bound_of_mem_span_insert_one`.

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
    IsSeparating {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := by
  intro μ ν _ _ hμν
  -- Over `ℝ` the star operation is the identity, so `A` is a `StarSubalgebra` as it stands.
  let A' : StarSubalgebra ℝ (E →ᵇ ℝ) :=
    { toSubalgebra := A
      star_mem' := fun {g} hg => by
        have hstar : star g = g := by ext a; simp
        rwa [hstar] }
  -- `toContinuousMapStarₐ ℝ` and `toContinuousMapₐ ℝ` have the same underlying function,
  -- so the images of `A'` and of `A` in `C(E, ℝ)` are the same set of functions.
  have hsep' : (A'.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨F, ⟨g, hg, rfl⟩, rfl⟩, hne⟩ := hsep hxy
    exact ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ g, ⟨g, hg, rfl⟩, rfl⟩, hne⟩
  exact ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℝ) hsep'
    fun g hg => hμν g ⟨g, hg, rfl⟩

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

omit [MeasurableSpace E] in
/-- Take `δ = dist y x`.  No measurable structure enters, hence the `omit`. -/
theorem StronglySeparatesPoints.separatesPoints [MetricSpace E] {Γ : Set (E → ℝ)}
    (h : StronglySeparatesPoints Γ) : Γ.SeparatesPoints := by
  intro x y hxy
  obtain ⟨s, ε, hsΓ, hε, hs⟩ := h x (dist y x) (dist_pos.2 (Ne.symm hxy))
  obtain ⟨f, hfs, hf⟩ := hs y le_rfl
  refine ⟨f, hsΓ (Finset.mem_coe.2 hfs), fun hcontra => ?_⟩
  rw [hcontra, sub_self, abs_zero] at hf
  exact absurd hf (not_le.2 hε)

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
is chosen, and none exists in general.

`[OpensMeasurableSpace E]` is what makes the members of `Γ` integrable: it is the
hypothesis of `Continuous.stronglyMeasurable`
(`MeasureTheory/Function/StronglyMeasurable/Basic.lean:718`, the second-countable
side of `SecondCountableTopologyEither` being `ℝ`) and of
`BoundedContinuousFunction.integrable`
(`MeasureTheory/Integral/BoundedContinuousFunction.lean:99`).  Without it the
statement is unprovable, `∫ f ∂μ` being `0` for every non-measurable `f`.

The order of the two σ-algebras is not cosmetic.  Both `m` and `mΩ` are local
instances of `MeasurableSpace Ω`, and instance search takes the **last** one, so
with `mΩ` declared first the unannotated `Measurable U` reads `Measurable[m] U`
-- the wrong, strictly stronger hypothesis, and one that makes the theorem say
much less than it should.  Mathlib's own convention (`{m m0 : MeasurableSpace α}`
throughout `ConditionalExpectation`) puts the ambient σ-algebra last for exactly
this reason; that is what is done here. -/
theorem IsSeparating.ae_eq_of_forall_condExp_eq [TopologicalSpace E]
    [OpensMeasurableSpace E]
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    [MeasurableSpace.CountablySeparated E]
    {Γ : Set (E → ℝ)} (hΓ : IsSeparating Γ)
    (hΓb : ∀ f ∈ Γ, ∃ g : E →ᵇ ℝ, ⇑g = f)
    {U V : Ω → E} (hU : Measurable U) (hV : Measurable[m] V)
    (h : ∀ f ∈ Γ, P[fun ω => f (U ω) | m] =ᵐ[P] fun ω => f (V ω)) :
    U =ᵐ[P] V := by
  have hV' : Measurable V := hV.mono hm le_rfl
  -- Step one: on every `m`-measurable set the two conditional laws agree.
  have key : ∀ G : Set Ω, MeasurableSet[m] G →
      (P.restrict G).map U = (P.restrict G).map V := by
    intro G hG
    have hmassU : ((P.restrict G).map U) univ = P G := by
      rw [Measure.map_apply hU MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ]
    have hmassV : ((P.restrict G).map V) univ = P G := by
      rw [Measure.map_apply hV' MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ]
    have hint : ∀ f ∈ Γ,
        ∫ x, f x ∂((P.restrict G).map U) = ∫ x, f x ∂((P.restrict G).map V) := by
      intro f hf
      obtain ⟨g, rfl⟩ := hΓb f hf
      have hUint : Integrable (fun ω => g (U ω)) P := by
        have : IsFiniteMeasure (P.map U) := Measure.isFiniteMeasure_map P U
        exact (g.integrable (P.map U)).comp_measurable hU
      rw [integral_map hU.aemeasurable
          g.continuous.stronglyMeasurable.aestronglyMeasurable,
        integral_map hV'.aemeasurable
          g.continuous.stronglyMeasurable.aestronglyMeasurable]
      calc ∫ ω in G, g (U ω) ∂P
          = ∫ ω in G, (P[fun ω => g (U ω) | m]) ω ∂P :=
            (setIntegral_condExp hm hUint hG).symm
        _ = ∫ ω in G, g (V ω) ∂P :=
            integral_congr_ae (ae_restrict_of_ae (h _ hf))
    rcases eq_or_ne (P G) 0 with hPG | hPG
    · have h0 : P.restrict G = 0 := Measure.restrict_eq_zero.2 hPG
      rw [h0]
      simp
    · have hPGtop : P G ≠ ⊤ := measure_ne_top P G
      have : IsProbabilityMeasure ((P G)⁻¹ • ((P.restrict G).map U)) := by
        refine ⟨?_⟩
        rw [Measure.smul_apply, smul_eq_mul, hmassU,
          ENNReal.inv_mul_cancel hPG hPGtop]
      have : IsProbabilityMeasure ((P G)⁻¹ • ((P.restrict G).map V)) := by
        refine ⟨?_⟩
        rw [Measure.smul_apply, smul_eq_mul, hmassV,
          ENNReal.inv_mul_cancel hPG hPGtop]
      have heq : (P G)⁻¹ • ((P.restrict G).map U) = (P G)⁻¹ • ((P.restrict G).map V) :=
        hΓ _ _ fun f hf => by
          rw [integral_smul_measure, integral_smul_measure, hint f hf]
      have hscale := congrArg (fun μ : Measure E => (P G) • μ) heq
      simpa only [smul_smul, ENNReal.mul_inv_cancel hPG hPGtop, one_smul] using hscale
  -- Step two: the preimages of Borel sets agree almost everywhere.
  refine EventuallyEq.of_forall_separating_preimage (l := ae P) MeasurableSet ?_
  intro B hB
  have hUB : MeasurableSet (U ⁻¹' B) := hU hB
  have hVB : MeasurableSet[m] (V ⁻¹' B) := hV hB
  have e1 : P (U ⁻¹' B ∩ V ⁻¹' B) = P (V ⁻¹' B) := by
    have h1 : ((P.restrict (V ⁻¹' B)).map U) B = ((P.restrict (V ⁻¹' B)).map V) B := by
      rw [key _ hVB]
    rwa [Measure.map_apply hU hB, Measure.map_apply hV' hB,
      Measure.restrict_apply hUB, Measure.restrict_apply (hV' hB),
      Set.inter_self] at h1
  have e2 : P (U ⁻¹' B \ V ⁻¹' B) = 0 := by
    have h1 : ((P.restrict (V ⁻¹' B)ᶜ).map U) B = ((P.restrict (V ⁻¹' B)ᶜ).map V) B := by
      rw [key _ hVB.compl]
    rw [Measure.map_apply hU hB, Measure.map_apply hV' hB,
      Measure.restrict_apply hUB, Measure.restrict_apply (hV' hB),
      Set.inter_compl_self, measure_empty] at h1
    rwa [Set.sdiff_eq]
  rw [MeasureTheory.ae_eq_set]
  refine ⟨e2, ?_⟩
  have hadd := measure_inter_add_sdiff (μ := P) (V ⁻¹' B) hUB
  rw [Set.inter_comm, e1] at hadd
  exact (ENNReal.add_right_inj (measure_ne_top P _)).1 (by rw [add_zero]; exact hadd)

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

/-! ## Milestone 5: the functional monotone class theorem

Mathlib has Dynkin's π-λ theorem for **sets**, as `MeasurableSpace.induction_on_inter`
(`MeasureTheory/PiSystem.lean:713`; the roadmap's bare `induction_on_inter` is
that declaration under `open MeasurableSpace`).  The functional form is absent.
Searched on `upstream/master` at `810b3888` on 2026-09-06, in Mathlib's own
vocabulary rather than ours: `monotone class` (no hit anywhere in `Mathlib/`),
`MulSystem`, `generateFromFuns`, `multiplicative system`, `monotone limits`,
`bounded monotone convergence`, `functional monotone`, `multiplicative family of
functions` -- all without a single hit.  `docs/1000.yaml` carries the monotone
class theorem as `Q242045` with no declaration.

`Ω` carries no `MeasurableSpace` instance in this section: the σ-algebra
generated by the function class is the object of study, and the statements that
do need an ambient one carry it as a binder. -/

section MulSystem

variable {Ω : Type*}

/-- A set of real functions closed under multiplication, the multiplicative
counterpart of `IsPiSystem`.  There is no nonemptiness side condition here, and
none is possible: `IsPiSystem` needs one because `s ∩ t` can leave the class,
while `f * g` is defined whatever `f` and `g` are. -/
def IsMulSystem (K : Set (Ω → ℝ)) : Prop := ∀ f ∈ K, ∀ g ∈ K, f * g ∈ K

/-- The indicators of a family of sets: the bridge from `IsPiSystem` to
`IsMulSystem`, and from `MeasurableSpace.generateFrom` to `generateFromFuns`. -/
def indicatorFuns (𝒞 : Set (Set Ω)) : Set (Ω → ℝ) :=
  {f | ∃ s ∈ 𝒞, Set.indicator s (1 : Ω → ℝ) = f}

theorem indicatorFuns_mono {𝒞 𝒟 : Set (Set Ω)} (h : 𝒞 ⊆ 𝒟) :
    indicatorFuns 𝒞 ⊆ indicatorFuns 𝒟 := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, h hs, rfl⟩

/-- The indicators of a π-system, **with `∅` adjoined**, form a multiplicative
system.

The `insert ∅` is not decoration.  Without it the statement is false: on
`Ω = ℕ` the family `𝒞 = {{0}, {1}}` is a π-system (no two distinct members
meet, so the condition is vacuous), and the product of its two indicators is the
constant `0`, which is the indicator of `∅` and of nothing else in `𝒞`.  This is
the form the roadmap asked for, corrected.  Adjoining `∅` costs nothing
downstream, by `MeasurableSpace.generateFrom_insert_empty`
(`MeasurableSpace/Defs.lean:426`) and `generateFromFuns_indicatorFuns` below. -/
theorem isMulSystem_indicator_of_isPiSystem {𝒞 : Set (Set Ω)} (h𝒞 : IsPiSystem 𝒞) :
    IsMulSystem (indicatorFuns (insert ∅ 𝒞)) := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  refine ⟨s ∩ t, ?_, Set.inter_indicator_one⟩
  rcases Set.eq_empty_or_nonempty (s ∩ t) with hst | hst
  · rw [hst]
    exact Set.mem_insert _ _
  · simp only [Set.mem_insert_iff] at hs ht
    have hs' : s ∈ 𝒞 := by
      rcases hs with rfl | hs
      · simp at hst
      · exact hs
    have ht' : t ∈ 𝒞 := by
      rcases ht with rfl | ht
      · simp at hst
      · exact ht
    exact Set.mem_insert_of_mem _ (h𝒞 s hs' t ht' hst)

/-- The σ-algebra generated by a family of real functions.  `borel ℝ` is
`Real.measurableSpace` on the nose (`Real.borelSpace` is `⟨rfl⟩`,
`Constructions/BorelSpace/Basic.lean:715`), so no transport is needed.

`@[instance_reducible]` as on `MeasurableSpace.generateFrom`
(`MeasurableSpace/Defs.lean:329`); without it the class-definition-reducibility
linter objects. -/
@[instance_reducible]
def generateFromFuns (K : Set (Ω → ℝ)) : MeasurableSpace Ω :=
  ⨆ f ∈ K, MeasurableSpace.comap f (borel ℝ)

theorem measurable_generateFromFuns_of_mem {K : Set (Ω → ℝ)} {f : Ω → ℝ} (hf : f ∈ K) :
    Measurable[generateFromFuns K] f := by
  refine measurable_iff_comap_le.2 ?_
  exact le_iSup₂ (f := fun g (_ : g ∈ K) => MeasurableSpace.comap g (borel ℝ)) f hf

theorem generateFromFuns_le_iff {K : Set (Ω → ℝ)} {m : MeasurableSpace Ω} :
    generateFromFuns K ≤ m ↔ ∀ f ∈ K, Measurable[m] f :=
  ⟨fun h _ hf => (measurable_generateFromFuns_of_mem hf).mono h le_rfl,
    fun h => iSup₂_le fun f hf => measurable_iff_comap_le.1 (h f hf)⟩

theorem generateFromFuns_mono {K K' : Set (Ω → ℝ)} (h : K ⊆ K') :
    generateFromFuns K ≤ generateFromFuns K' :=
  generateFromFuns_le_iff.2 fun _ hf => measurable_generateFromFuns_of_mem (h hf)

/-- The identity that connects the functional form to `induction_on_inter`: the
σ-algebra generated by the indicators of a family is the σ-algebra generated by
the family.  Adding `∅` on the left changes nothing, which is why the `insert ∅`
of `isMulSystem_indicator_of_isPiSystem` is free. -/
theorem generateFromFuns_indicatorFuns (𝒞 : Set (Set Ω)) :
    generateFromFuns (indicatorFuns (insert ∅ 𝒞)) = MeasurableSpace.generateFrom 𝒞 := by
  refine le_antisymm (generateFromFuns_le_iff.2 ?_) (MeasurableSpace.generateFrom_le fun s hs => ?_)
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : MeasurableSet[MeasurableSpace.generateFrom 𝒞] s := by
      simp only [Set.mem_insert_iff] at hs
      rcases hs with rfl | hs
      · exact MeasurableSpace.measurableSet_empty _
      · exact MeasurableSpace.measurableSet_generateFrom hs
    exact Measurable.indicator measurable_const hs'
  · have hmem : Set.indicator s (1 : Ω → ℝ) ∈ indicatorFuns (insert ∅ 𝒞) :=
      ⟨s, Set.mem_insert_of_mem _ hs, rfl⟩
    have hpre : Set.indicator s (1 : Ω → ℝ) ⁻¹' {1} = s := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    exact hpre ▸ measurable_generateFromFuns_of_mem hmem (measurableSet_singleton (1 : ℝ))

/-- The cells cut out of `Ω` by finitely many members of `K`: finite
intersections of the sets `f ⁻¹' Ioi c` with `f ∈ K`.

The finite intersection is what makes this a π-system, and a π-system is what
`MeasurableSpace.induction_on_inter` needs; the sets `f ⁻¹' Ioi c` alone are not
closed under intersection.  The family is indexed by a `List` rather than by a
`Finset` because two members may name the same `f` with different `c`, which a
`Finset` of pairs would allow but a `Finset` of functions with a choice of
levels would not; and appending lists is exactly the closure under
intersection. -/
def ioiCells (K : Set (Ω → ℝ)) : Set (Set Ω) :=
  {s | ∃ l : List ((Ω → ℝ) × ℝ), (∀ p ∈ l, p.1 ∈ K) ∧
    s = ⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2}

theorem isPiSystem_ioiCells (K : Set (Ω → ℝ)) : IsPiSystem (ioiCells K) := by
  rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩ -
  refine ⟨l₁ ++ l₂, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, List.mem_append]
    constructor
    · rintro ⟨ha, hb⟩ i (hi | hi)
      · exact ha i hi
      · exact hb i hi
    · intro hx
      exact ⟨fun i hi => hx i (Or.inl hi), fun i hi => hx i (Or.inr hi)⟩

/-- The σ-algebra generated by `K` is generated by the cells: this is where the
functional form meets `MeasurableSpace.induction_on_inter`.

One direction is `measurable_of_Ioi` (`Constructions/BorelSpace/Order.lean:653`),
the other an induction along the list. -/
theorem generateFromFuns_eq_generateFrom_ioiCells (K : Set (Ω → ℝ)) :
    generateFromFuns K = MeasurableSpace.generateFrom (ioiCells K) := by
  have hmeas : ∀ l : List ((Ω → ℝ) × ℝ), (∀ p ∈ l, p.1 ∈ K) →
      MeasurableSet[generateFromFuns K] (⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2) := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.not_mem_nil, Set.iInter_of_empty, Set.iInter_univ]
      exact MeasurableSet.univ
    | cons p l ih =>
      intro hl
      have he : (⋂ q ∈ p :: l, q.1 ⁻¹' Set.Ioi q.2)
          = (p.1 ⁻¹' Set.Ioi p.2) ∩ ⋂ q ∈ l, q.1 ⁻¹' Set.Ioi q.2 := by
        ext x
        simp only [Set.mem_iInter, Set.mem_inter_iff, List.mem_cons]
        constructor
        · intro hx
          exact ⟨hx p (Or.inl rfl), fun q hq => hx q (Or.inr hq)⟩
        · rintro ⟨hx, hx'⟩ q (rfl | hq)
          · exact hx
          · exact hx' q hq
      rw [he]
      refine MeasurableSet.inter ?_ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
      exact measurable_generateFromFuns_of_mem (hl p List.mem_cons_self)
        measurableSet_Ioi
  refine le_antisymm (generateFromFuns_le_iff.2 fun f hf => ?_)
    (MeasurableSpace.generateFrom_le ?_)
  · refine measurable_of_Ioi fun c => ?_
    refine MeasurableSpace.measurableSet_generateFrom ⟨[(f, c)], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hf
    · ext x
      simp
  · rintro _ ⟨l, hl, rfl⟩
    exact hmeas l hl

/-- A linear class containing the constants and closed under bounded monotone
limits is closed under uniform limits.

This is the standard subsequence trick, and it is the first step of
`induction_on_mulSystem`: shift the `k`-th member of a subsequence that is
`(1/2)^(k+2)`-close down by `(1/2)^k`, which makes it increase, converge to the
same limit, and stay bounded.  Multiplicativity is not used, so this holds of
any linear class -- which is why it is a lemma and not part of the induction. -/
theorem of_tendstoUniformly_of_mono_lim {P : (Ω → ℝ) → Prop}
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hP : ∀ n, P (f n))
    (hgbdd : ∃ C, ∀ x, |g x| ≤ C) (hu : TendstoUniformly f g atTop) :
    P g := by
  obtain ⟨C, hC⟩ := hgbdd
  have hstep : ∀ k : ℕ, ∃ m : ℕ, ∀ x, |f m x - g x| ≤ (1 / 2 : ℝ) ^ (k + 2) := by
    intro k
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 2) := by positivity
    obtain ⟨m, hm⟩ := (Metric.tendstoUniformly_iff.1 hu _ hpos).exists
    refine ⟨m, fun x => ?_⟩
    have hx := hm x
    rw [Real.dist_eq, abs_sub_comm] at hx
    exact hx.le
  choose m hm using hstep
  set h : ℕ → Ω → ℝ := fun k x => f (m k) x - (1 / 2 : ℝ) ^ k with hh
  have hpow : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hpow1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsucc : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by
    intro k; rw [pow_succ]; ring
  have hsucc2 : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ k / 4 := by
    intro k; rw [pow_add]; ring
  have hsucc3 : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 3) = (1 / 2 : ℝ) ^ k / 8 := by
    intro k; rw [pow_add]; ring
  have hmono : ∀ x, Monotone fun k => h k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    have e1 := (abs_le.1 (hm k x)).2
    have e2 := (abs_le.1 (hm (k + 1) x)).1
    have hk3 : k + 1 + 2 = k + 3 := by omega
    rw [hk3, hsucc3] at e2
    rw [hsucc2] at e1
    have hp := hpow k
    simp only [hh, hsucc]
    linarith
  refine mono_lim h g hmono (fun k => ?_) ⟨C + 2, fun k x => ?_⟩ ?_
  · have hfun : h k = f (m k) + fun _ => -(1 / 2 : ℝ) ^ k := by
      funext x; simp [hh, sub_eq_add_neg]
    rw [hfun]
    exact add _ _ (hP (m k)) (const _)
  · have e1 := abs_le.1 (hm k x)
    have e2 := abs_le.1 (hC x)
    have h4 := hpow1 (k + 2)
    have h5 := hpow1 k
    have h6 := hpow k
    rw [abs_le]
    constructor <;> · simp only [hh]; linarith
  · intro x
    have hhalf : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hhalf2 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 2)) atTop (𝓝 0) :=
      hhalf.comp (tendsto_add_atTop_nat 2)
    have hdiff : Tendsto (fun k => f (m k) x - g x) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by simpa [Real.norm_eq_abs] using hm k x) hhalf2
    have hsub : Tendsto (fun k => h k x - g x) atTop (𝓝 0) := by
      simpa [hh, sub_right_comm] using hdiff.sub hhalf
    simpa using hsub.add_const (g x)

/-! ### The algebra generated by a multiplicative system

Step (ii) of `induction_on_mulSystem` approximates a continuous `φ` composed with
finitely many members of `K` by polynomials in those members, and needs to know
that those polynomials are still in `P`.  `P` itself is **not** closed under
multiplication -- it is linear, contains the constants, and is closed under
bounded monotone limits, and nothing more -- so the multiplicativity has to be
kept inside `K`.  The vehicle is `Submodule.span ℝ (insert 1 K)`: it is closed
under multiplication because `K` is (`K * K ⊆ K`, and the extra `1` is a unit),
and `P` holds on all of it by linearity.  So it is the subalgebra generated by
`K`, and it sits between `K` and `P`. -/

/-- The `ℝ`-span of `insert 1 K` is closed under multiplication when `K` is: it
is the subalgebra generated by a multiplicative system. -/
theorem mul_mem_span_insert_one_of_isMulSystem {K : Set (Ω → ℝ)} (hK : IsMulSystem K)
    {u v : Ω → ℝ} (hu : u ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K))
    (hv : v ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K)) :
    u * v ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K) := by
  induction hu using Submodule.span_induction with
  | mem a ha =>
    induction hv using Submodule.span_induction with
    | mem b hb =>
      rcases ha with rfl | ha
      · rw [one_mul]
        exact Submodule.subset_span hb
      · rcases hb with rfl | hb
        · rw [mul_one]
          exact Submodule.subset_span (Set.mem_insert_of_mem _ ha)
        · exact Submodule.subset_span (Set.mem_insert_of_mem _ (hK a ha b hb))
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- A class that contains `K` and the constants and is closed under addition and
scalar multiplication contains the whole subalgebra generated by `K`. -/
theorem of_mem_span_insert_one {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    {g : Ω → ℝ} (hg : g ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K)) : P g := by
  induction hg using Submodule.span_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact const 1
    · exact basic a ha
  | zero => exact const 0
  | add x y _ _ hx hy => exact add x y hx hy
  | smul c x _ hx => exact smul c x hx

/-- Every member of the subalgebra generated by a multiplicative system of
bounded functions is bounded. -/
theorem exists_bound_of_mem_span_insert_one {K : Set (Ω → ℝ)}
    (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    {g : Ω → ℝ} (hg : g ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K)) :
    ∃ C, ∀ x, |g x| ≤ C := by
  induction hg using Submodule.span_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact ⟨1, fun x => by simp⟩
    · exact hKbdd a ha
  | zero => exact ⟨0, fun x => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC⟩ := hx
    obtain ⟨D, hD⟩ := hy
    refine ⟨C + D, fun z => ?_⟩
    calc |(x + y) z| ≤ |x z| + |y z| := abs_add_le _ _
      _ ≤ C + D := add_le_add (hC z) (hD z)
  | smul c x _ hx =>
    obtain ⟨C, hC⟩ := hx
    refine ⟨|c| * C, fun z => ?_⟩
    calc |(c • x) z| = |c| * |x z| := by simp [abs_mul]
      _ ≤ |c| * C := by
          exact mul_le_mul_of_nonneg_left (hC z) (abs_nonneg c)

/-- Step (ii) of `induction_on_mulSystem`: a continuous function of finitely many
members of `K` is in `P`.

`φ` is only ever evaluated on the range of `x ↦ (f 1 x, …, f n x)`, which lies in
a closed box because the members of `K` are bounded; the box is compact, so
Stone-Weierstrass applies to the subalgebra of `C(box, ℝ)` generated by the
coordinate maps, which separates points and contains the constants.  The anchor
is `ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`
(`Topology/ContinuousMap/StoneWeierstrass.lean:313`), the unbundled ε-form,
which takes `φ` as a plain function with a `Continuous` proof rather than as a
`C(X, ℝ)`; the bundled form is `:297`.
Pulling an approximant back along `x ↦ (f 1 x, …, f n x)` lands in
`Submodule.span ℝ (insert 1 K)` -- that is what
`mul_mem_span_insert_one_of_isMulSystem` is for, the pullback of a subalgebra
being a subalgebra -- hence in `P` by `of_mem_span_insert_one`, and the uniform
limit is in `P` by `of_tendstoUniformly_of_mono_lim`, whose boundedness
hypothesis is `exists_bound_of_mem_span_insert_one`. -/
theorem of_continuous_comp_of_isMulSystem {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    {n : ℕ} (f : Fin n → Ω → ℝ) (hf : ∀ i, f i ∈ K)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    P (fun x => φ (fun i => f i x)) := sorry

/-- `fact:monotoneclass` (Ethier-Kurtz, Appendix 4), the functional monotone
class theorem.  Stated `@[elab_as_elim]`, as `MeasurableSpace.induction_on_inter`
is.

The proof, in the four steps the auxiliary declarations above and below cut it
into.  (i) `P` is closed under uniform limits, by
`of_tendstoUniformly_of_mono_lim`.  (ii) Hence `P` holds of `φ ∘ (f₁, …, fₙ)`
for `f₁, …, fₙ ∈ K` and `φ` continuous on the (compact) range: the polynomials
in `f₁, …, fₙ` are in `P` by multiplicativity, linearity and the constants, and
Stone-Weierstrass approximates `φ` by them uniformly.  (iii) Taking for `φ` the
continuous functions increasing to the indicator of a box gives `P` of the
indicator of every member of `ioiCells K`; that family is a π-system generating
`generateFromFuns K` (`isPiSystem_ioiCells`,
`generateFromFuns_eq_generateFrom_ioiCells`), so
`MeasurableSpace.induction_on_inter` carries `P` to the indicator of every set
of `generateFromFuns K`.  (iv) Linearity gives the simple functions and one more
bounded monotone limit gives every bounded `generateFromFuns K`-measurable
function.

Step (i) is proved, and so is the π-system half of step (iii).  What is left is
the Stone-Weierstrass step (ii), the approximation of the indicator of a box
that turns it into `P` of an indicator, and the routine step (iv). -/
@[elab_as_elim]
theorem induction_on_mulSystem {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    (f : Ω → ℝ) (hf : Measurable[generateFromFuns K] f) (hfbdd : ∃ C, ∀ x, |f x| ≤ C) :
    P f := sorry

/-- Two finite measures that agree on the total mass and integrate every member
of a multiplicative system of bounded measurable functions alike agree on
`generateFromFuns K`.  The total mass has to be assumed separately: the
multiplicative system need not contain the constants, and `∫ f ∂μ = ∫ f ∂ν` for
`f ∈ K` says nothing about `μ univ`. -/
theorem ext_of_forall_integral_eq_of_isMulSystem {mΩ : MeasurableSpace Ω}
    {K : Set (Ω → ℝ)} (hK : IsMulSystem K) (hKm : ∀ f ∈ K, Measurable f)
    (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ)
    (h : ∀ f ∈ K, ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    ∀ s, MeasurableSet[generateFromFuns K] s → μ s = ν s := sorry

/-- Orthogonality against a multiplicative system propagates to the whole
σ-algebra it generates.

The hypothesis `hg0` on the constant `1` is not removable, for the same reason
as the total mass in `ext_of_forall_integral_eq_of_isMulSystem`: with
`K = {0}`, `generateFromFuns K` is `⊥`, every bounded `⊥`-measurable function on
a nonempty `Ω` is constant, and `∫ g * c ∂μ = c ∫ g ∂μ` is `0` only if
`∫ g ∂μ = 0`, which the hypothesis on `K` does not give.  It is implied by, and
weaker than, asking `(1 : Ω → ℝ) ∈ K`. -/
theorem integral_mul_eq_zero_of_isMulSystem {mΩ : MeasurableSpace Ω}
    {K : Set (Ω → ℝ)} (hK : IsMulSystem K) (hKm : ∀ f ∈ K, Measurable f)
    (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (μ : Measure Ω) [IsFiniteMeasure μ] {g : Ω → ℝ} (hg : Integrable g μ)
    (hg0 : ∫ x, g x ∂μ = 0)
    (h : ∀ f ∈ K, ∫ x, g x * f x ∂μ = 0) :
    ∀ f : Ω → ℝ, Measurable[generateFromFuns K] f → (∃ C, ∀ x, |f x| ≤ C) →
      ∫ x, g x * f x ∂μ = 0 := sorry

/-- The conditional form, and the one in which the martingale property is
verified: testing against a multiplicative system suffices.  Apply
`integral_mul_eq_zero_of_isMulSystem` to `g = X - Y`. -/
theorem condExp_eq_of_forall_integral_mul_eq {mΩ : MeasurableSpace Ω}
    {K : Set (Ω → ℝ)} (hK : IsMulSystem K) (hKm : ∀ f ∈ K, Measurable f)
    (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C) (hKle : generateFromFuns K ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (h1 : ∫ x, X x ∂μ = ∫ x, Y x ∂μ)
    (h : ∀ f ∈ K, ∫ x, X x * f x ∂μ = ∫ x, Y x * f x ∂μ) :
    μ[X | generateFromFuns K] =ᵐ[μ] μ[Y | generateFromFuns K] := sorry

end MulSystem

end MeasureTheory
