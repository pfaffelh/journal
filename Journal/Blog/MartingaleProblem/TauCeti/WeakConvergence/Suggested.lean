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

Since 2026-09-07, eighth run, **step (ii) itself is proved**:
`of_continuous_comp_of_isMulSystem`, the approximation of a continuous function
of finitely many members of `K` by elements of the subalgebra they generate.  It
is the Stone-Weierstrass step of the functional monotone class theorem, and it
needs no import beyond what this file already had --- the anchor is
`ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`,
the variant in which `X` need not be compact and only the approximation is
confined to a compact set, so no subtype `↥box` ever appears.

Since 2026-09-07, ninth run, **the functional monotone class theorem itself is
proved**, `induction_on_mulSystem`, together with steps (iii) and (iv) --
`ioiApprox` and its six lemmas, `of_indicator_mem_ioiCells`,
`of_indicator_of_measurable`, `of_simpleFunc`, `of_nonneg_of_measurable` -- and
all three of its corollaries -- `ext_of_forall_integral_eq_of_isMulSystem`,
`integral_mul_eq_zero_of_isMulSystem` and
`condExp_eq_of_forall_integral_mul_eq` -- and the `RCLike` bridge
`integral_mul_ofReal_eq_zero_of_isMulSystem`, which is the shape
`MartingaleProblems` consumes, together with
`generateFromFuns_setOf_continuous_bounded`, which is what makes a criterion
tested against bounded continuous functions a criterion about the Borel
σ-algebra.  Two things are worth knowing before touching
them.  The ramps of step (iii) have to be taken jointly, as one
continuous function of the `n` values, because `P` is not closed under
multiplication; and the property carried through the induction in the
corollaries has to include integrability, because `add` and `mono_lim` must
hold of arbitrary functions and the integral is additive only on integrable
ones.

Since 2026-09-07, thirteenth run, **`isSeparating_pi` is proved**, together with
the machinery it runs on: `weightedMap` with `isFiniteMeasure_weightedMap` and
`integral_weightedMap`, the Jordan pair `sepPos`/`sepNeg` with
`integral_sepPos_sub_integral_sepNeg`, the engine
`integral_indicator_mul_eq_of_isSeparating`, and, on the product side,
`exists_nonneg_bound_prod`, `boxes`, `isPiSystem_boxes` and
`generateFrom_boxes`.  The statement gained two hypotheses it could not do
without -- every member of every `Γ i` bounded and measurable -- and the reason
is in its doc string.  The route is not the functional monotone class theorem:
products out of separating classes need not be a multiplicative system.

Since 2026-09-07, fourteenth run, **`isConvergenceDetermining_pi` is proved**,
the convergence determining half of the same point, together with the three
declarations it rests on: `IsTightMeasureSet.pi`, the tightness of a countable
product from the tightness of its one-coordinate marginals, which Mathlib has
only for two factors (`IsTightMeasureSet.prodMk`); `isTightMeasureSet_of_tendsto`,
the tightness of a convergent sequence on a Polish space; and
`tendsto_of_isSeparating_of_isTightMeasureSet`, Prokhorov plus identification --
a separating class of bounded continuous functions tests weak convergence along
a tight sequence.  The last is the plain-class counterpart of Mathlib's
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, which asks for a
`StarSubalgebra` separating points rather than a class separating measures.
Continuity is where the convergence determining half parts company with the
separating one: the identification of a subsequential limit evaluates the class
against a weakly convergent sequence, which sees bounded continuous functions
and nothing else.

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

/-- From
`MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
(`MeasureTheory/Measure/FiniteMeasureExt.lean:36`).  That
theorem is stated for a `StarSubalgebra 𝕜 (E →ᵇ 𝕜)` with `[RCLike 𝕜]` and the
hypothesis `(A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints`; over `ℝ` the star
operation is trivial, and the real form of the separation hypothesis is the one
that occurs inside its proof
(`Analysis/SpecialFunctions/MulExpNegMulSqIntegral.lean:161`).

The bundle is the weaker of Mathlib's two: `PseudoEMetricSpace` with
`CompleteSpace` and `SecondCountableTopology`, not `PolishSpace`.  Mathlib's
`..._of_polish` (`:72`) is one line of `upgradeIsCompletelyMetrizable` away from
the one used here, so nothing is lost, and the metric may be a pseudometric --
the separation of `E` never enters, only the separation of the algebra. -/
theorem IsSeparating.of_subalgebra [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
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
  exact ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable (𝕜 := ℝ) hsep'
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

/-! ### From separating to convergence determining, along a tight sequence

This is Prokhorov's theorem used the way Ethier-Kurtz uses it in Chapter 3: a
separating class of *bounded continuous* functions tests weak convergence as
soon as the sequence is tight, because tightness makes the closure of its range
compact and the separating class pins every subsequential limit to the same
measure.

It is the plain-class counterpart of
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`MeasureTheory/Measure/LevyConvergence.lean:154`), which asks for a
`StarSubalgebra` separating *points* rather than a class separating *measures*,
and it is what a separating class alone cannot do: continuity is used, and has
to be, in the identification step -- weak convergence of the subsequence gives
convergence of `∫ f` only for `f` bounded continuous, so a member of `Γ` that is
merely bounded measurable would leave the limit unidentified. -/

/-- A convergent sequence of probability measures on a Polish space is tight: its
range together with its limit is compact, hence closed, hence tight by
`isTightMeasureSet_of_isCompact_closure` (`Measure/Prokhorov.lean:635`).

There is no circularity here of the kind the tightness-free Stone-Weierstrass
statement fell into: the convergence is a *hypothesis*, not the conclusion. -/
theorem isTightMeasureSet_of_tendsto [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto μ atTop (𝓝 ν)) :
    IsTightMeasureSet {((μ n : ProbabilityMeasure E) : Measure E) | n} := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  have hc : IsCompact (insert ν (Set.range μ)) := h.isCompact_insert_range
  have hcl : closure (insert ν (Set.range μ)) = insert ν (Set.range μ) := hc.isClosed.closure_eq
  have key := isTightMeasureSet_of_isCompact_closure (S := insert ν (Set.range μ))
    (by rw [hcl]; exact hc)
  refine key.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨μ n, Or.inr ⟨n, rfl⟩, rfl⟩

/-- A separating class of bounded continuous functions is convergence determining
**along tight sequences**.  Prokhorov gives a compact closure, `tendsto_subseq`
a convergent subsequence of any subsequence, the class identifies its limit as
`ν`, and `tendsto_of_subseq_tendsto` puts the sequence back together.

The two side conditions are the same pair `isSeparating_pi` carries, with
continuity in place of measurability, and continuity is the one that cannot be
dropped: it is what lets weak convergence of the subsequence be evaluated
against `f`. -/
theorem tendsto_of_isSeparating_of_isTightMeasureSet [TopologicalSpace E] [PolishSpace E]
    [BorelSpace E] {Γ : Set (E → ℝ)} (hsep : IsSeparating Γ)
    (hcont : ∀ f ∈ Γ, Continuous f) (hbdd : ∀ f ∈ Γ, ∃ C, ∀ x, |f x| ≤ C)
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (htight : IsTightMeasureSet {((μ n : ProbabilityMeasure E) : Measure E) | n})
    (hconv : ∀ f ∈ Γ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E)))) :
    Tendsto μ atTop (𝓝 ν) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  have hcomp : IsCompact (closure (Set.range μ)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    have hset : {((m : ProbabilityMeasure E) : Measure E) | m ∈ Set.range μ}
        = {((μ n : ProbabilityMeasure E) : Measure E) | n} := by
      ext ρ
      constructor
      · rintro ⟨m, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
    rw [hset]
    exact htight
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq
    (x := fun k => μ (ns k)) (fun k => subset_closure ⟨ns k, rfl⟩)
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hav : a = ν := by
    have : (a : Measure E) = (ν : Measure E) := by
      refine hsep _ _ fun f hf => ?_
      obtain ⟨C, hC⟩ := hbdd f hf
      set g : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f (hcont f hf) C
        (fun x => by simpa [Real.norm_eq_abs] using hC x) with hg
      have hgf : ⇑g = f := rfl
      have h1 : Tendsto (fun k => ∫ x, g x ∂((μ (ns (φ k)) : ProbabilityMeasure E) : Measure E))
          atTop (𝓝 (∫ x, g x ∂(a : Measure E))) :=
        ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim g
      rw [hgf] at h1
      exact tendsto_nhds_unique h1 ((hconv _ hf).comp hsub)
    exact ProbabilityMeasure.toMeasure_injective this
  rw [← hav]
  exact hlim

/-! ### The engine behind `isSeparating_pi`

A separating class is a *linear* condition in disguise: `Γ` separates probability
measures exactly when no nonzero signed measure of total mass zero annihilates it,
since every such signed measure is a scalar multiple of a difference of probability
measures.  What follows exploits that without ever mentioning a signed measure: the
pair `sepPos`/`sepNeg` is the Jordan decomposition of `W • (μ - ν)`, written as two
honest positive measures, and `IsSeparating` is applied to their normalisations. -/

section Weighted

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

theorem integrable_of_measurable_of_bounded {ρ : Measure Ω} [IsFiniteMeasure ρ] {g : Ω → ℝ}
    (hg : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) : Integrable g ρ :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb x)

theorem abs_max_zero_le {a b : ℝ} (h : |a| ≤ b) : |max a 0| ≤ b := by
  rw [abs_of_nonneg (le_max_right a 0)]
  exact (max_le (le_abs_self a) (abs_nonneg a)).trans h

theorem abs_mul_le_mul {a b c d : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ d) : |a * b| ≤ c * d := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

/-- The image under `T` of `ρ` reweighted by the positive part of `w`. -/
noncomputable def weightedMap (T : Ω → S) (ρ : Measure Ω) (w : Ω → ℝ) : Measure S :=
  (ρ.withDensity fun x => ENNReal.ofReal (w x)).map T

theorem isFiniteMeasure_weightedMap (T : Ω → S) (ρ : Measure Ω) [IsFiniteMeasure ρ]
    {w : Ω → ℝ} {C : ℝ} (hwb : ∀ x, w x ≤ C) : IsFiniteMeasure (weightedMap T ρ w) := by
  have hfin : ∫⁻ x, ENNReal.ofReal (w x) ∂ρ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hwb x))
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ _)
  have := isFiniteMeasure_withDensity hfin
  exact Measure.isFiniteMeasure_map _ _

theorem integral_weightedMap {T : Ω → S} (hT : Measurable T) {ρ : Measure Ω}
    {w : Ω → ℝ} (hw : Measurable w) {h : S → ℝ} (hh : Measurable h) :
    ∫ y, h y ∂(weightedMap T ρ w) = ∫ x, max (w x) 0 * h (T x) ∂ρ := by
  rw [weightedMap, integral_map hT.aemeasurable hh.aestronglyMeasurable]
  rw [show (fun x => ENNReal.ofReal (w x))
      = (fun x => ((Real.toNNReal (w x) : NNReal) : ENNReal)) from rfl]
  rw [integral_withDensity_eq_integral_smul (hw.real_toNNReal)]
  simp [NNReal.smul_def, Real.coe_toNNReal']

variable {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {T : Ω → S} {W : Ω → ℝ} {CW : ℝ}

/-- The positive half of the Jordan pair. -/
noncomputable def sepPos (T : Ω → S) (μ ν : Measure Ω) (W : Ω → ℝ) : Measure S :=
  weightedMap T μ W + weightedMap T ν (fun x => -W x)

/-- The negative half of the Jordan pair. -/
noncomputable def sepNeg (T : Ω → S) (μ ν : Measure Ω) (W : Ω → ℝ) : Measure S :=
  weightedMap T ν W + weightedMap T μ (fun x => -W x)

theorem isFiniteMeasure_sepPos (hWb : ∀ x, |W x| ≤ CW) :
    IsFiniteMeasure (sepPos T μ ν W) := by
  haveI h1 := isFiniteMeasure_weightedMap T μ (w := W) (C := CW)
    fun x => (abs_le.1 (hWb x)).2
  haveI h2 := isFiniteMeasure_weightedMap T ν (w := fun x => -W x) (C := CW)
    fun x => by have := (abs_le.1 (hWb x)).1; linarith
  exact inferInstanceAs
    (IsFiniteMeasure (weightedMap T μ W + weightedMap T ν fun x => -W x))

theorem isFiniteMeasure_sepNeg (hWb : ∀ x, |W x| ≤ CW) :
    IsFiniteMeasure (sepNeg T μ ν W) := by
  haveI h1 := isFiniteMeasure_weightedMap T ν (w := W) (C := CW)
    fun x => (abs_le.1 (hWb x)).2
  haveI h2 := isFiniteMeasure_weightedMap T μ (w := fun x => -W x) (C := CW)
    fun x => by have := (abs_le.1 (hWb x)).1; linarith
  exact inferInstanceAs
    (IsFiniteMeasure (weightedMap T ν W + weightedMap T μ fun x => -W x))

/-- The defining identity of the Jordan pair. -/
theorem integral_sepPos_sub_integral_sepNeg (hT : Measurable T) (hW : Measurable W)
    (hWb : ∀ x, |W x| ≤ CW) {h : S → ℝ} (hh : Measurable h) {D : ℝ} (hhb : ∀ y, |h y| ≤ D) :
    ∫ y, h y ∂(sepPos T μ ν W) - ∫ y, h y ∂(sepNeg T μ ν W)
      = ∫ x, W x * h (T x) ∂μ - ∫ x, W x * h (T x) ∂ν := by
  haveI hfp : IsFiniteMeasure (sepPos T μ ν W) := isFiniteMeasure_sepPos hWb
  haveI hfn : IsFiniteMeasure (sepNeg T μ ν W) := isFiniteMeasure_sepNeg hWb
  haveI hμW := isFiniteMeasure_weightedMap T μ (w := W) (C := CW) fun x => (abs_le.1 (hWb x)).2
  haveI hνW := isFiniteMeasure_weightedMap T ν (w := W) (C := CW) fun x => (abs_le.1 (hWb x)).2
  haveI hμN := isFiniteMeasure_weightedMap T μ (w := fun x => -W x) (C := CW)
    fun x => by have := (abs_le.1 (hWb x)).1; linarith
  haveI hνN := isFiniteMeasure_weightedMap T ν (w := fun x => -W x) (C := CW)
    fun x => by have := (abs_le.1 (hWb x)).1; linarith
  have hint : ∀ (ρ : Measure S), IsFiniteMeasure ρ → Integrable h ρ :=
    fun ρ hρ => integrable_of_measurable_of_bounded hh hhb
  -- split the two sums
  rw [sepPos, sepNeg, integral_add_measure (hint _ hμW) (hint _ hνN),
    integral_add_measure (hint _ hνW) (hint _ hμN)]
  simp only [integral_weightedMap hT hW hh,
    integral_weightedMap hT (show Measurable fun x => -W x from hW.neg) hh]
  -- and recombine, on each measure separately
  have key : ∀ (ρ : Measure Ω), IsFiniteMeasure ρ →
      ∫ x, max (W x) 0 * h (T x) ∂ρ - ∫ x, max (-W x) 0 * h (T x) ∂ρ
        = ∫ x, W x * h (T x) ∂ρ := by
    intro ρ hρ
    have hp : Integrable (fun x => max (W x) 0 * h (T x)) ρ :=
      integrable_of_measurable_of_bounded ((hW.max measurable_const).mul (hh.comp hT))
        (C := CW * D) fun x => abs_mul_le_mul (abs_max_zero_le (hWb x)) (hhb _)
    have hn : Integrable (fun x => max (-W x) 0 * h (T x)) ρ :=
      integrable_of_measurable_of_bounded ((hW.neg.max measurable_const).mul (hh.comp hT))
        (C := CW * D) fun x => abs_mul_le_mul
          (abs_max_zero_le (by rw [abs_neg]; exact hWb x)) (hhb _)
    rw [← integral_sub hp hn]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← sub_mul]
    congr 1
    rcases le_total 0 (W x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have kμ := key μ inferInstance
  have kν := key ν inferInstance
  linarith

/-- **The engine.**  A separating class on the target of `T` turns equality of `W`-weighted
integrals along `Γ` into equality of `W`-weighted integrals along indicators.  No signed
measure appears: the Jordan pair `sepPos`/`sepNeg` is built out of the positive parts. -/
theorem integral_indicator_mul_eq_of_isSeparating
    {Γ : Set (S → ℝ)} (hΓ : IsSeparating Γ)
    (hΓm : ∀ f ∈ Γ, Measurable f) (hΓb : ∀ f ∈ Γ, ∃ C, ∀ y, |f y| ≤ C)
    (hT : Measurable T) (hW : Measurable W) (hWb : ∀ x, |W x| ≤ CW)
    (h0 : ∫ x, W x ∂μ = ∫ x, W x ∂ν)
    (hΓint : ∀ f ∈ Γ, ∫ x, W x * f (T x) ∂μ = ∫ x, W x * f (T x) ∂ν)
    {A : Set S} (hA : MeasurableSet A) :
    ∫ x, W x * A.indicator (1 : S → ℝ) (T x) ∂μ
      = ∫ x, W x * A.indicator (1 : S → ℝ) (T x) ∂ν := by
  haveI hfp : IsFiniteMeasure (sepPos T μ ν W) := isFiniteMeasure_sepPos hWb
  haveI hfn : IsFiniteMeasure (sepNeg T μ ν W) := isFiniteMeasure_sepNeg hWb
  set p := sepPos T μ ν W with hpdef
  set q := sepNeg T μ ν W with hqdef
  have hone : ∫ _y : S, (1:ℝ) ∂p - ∫ _y : S, (1:ℝ) ∂q = 0 := by
    rw [integral_sepPos_sub_integral_sepNeg hT hW hWb (h := fun _ => (1:ℝ))
      measurable_const (D := 1) (fun y => by norm_num)]
    simp only [mul_one, h0, sub_self]
  have hmass : p univ = q univ := by
    have h1 : (p univ).toReal = (q univ).toReal := by
      have := sub_eq_zero.1 hone
      simpa [integral_const, measureReal_def] using this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h1
  have hpq : p = q := by
    rcases eq_or_ne (p univ) 0 with hz | hz
    · have hp0 : p = 0 := by rwa [← Measure.measure_univ_eq_zero]
      have hq0 : q = 0 := by
        rw [← Measure.measure_univ_eq_zero, ← hmass]; exact hz
      rw [hp0, hq0]
    · have hne : p univ ≠ ∞ := measure_ne_top _ _
      haveI : IsProbabilityMeasure ((p univ)⁻¹ • p) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hz hne]⟩
      haveI : IsProbabilityMeasure ((p univ)⁻¹ • q) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hmass, ENNReal.inv_mul_cancel hz hne]⟩
      have hsep : (p univ)⁻¹ • p = (p univ)⁻¹ • q := by
        refine hΓ _ _ ?_
        intro f hf
        obtain ⟨C, hC⟩ := hΓb f hf
        rw [integral_smul_measure, integral_smul_measure]
        congr 1
        have hd := integral_sepPos_sub_integral_sepNeg (μ := μ) (ν := ν) hT hW hWb
          (hΓm f hf) hC
        rw [hΓint f hf, sub_self] at hd
        exact sub_eq_zero.1 hd
      have := congrArg (fun ρ : Measure S => (p univ) • ρ) hsep
      simpa [smul_smul, ENNReal.mul_inv_cancel hz hne] using this
  have hd := integral_sepPos_sub_integral_sepNeg (μ := μ) (ν := ν) hT hW hWb
    (h := A.indicator (1 : S → ℝ)) (measurable_const.indicator hA) (D := 1)
    (fun y => by by_cases hy : y ∈ A <;> simp [hy])
  rw [← hpdef, ← hqdef, hpq, sub_self] at hd
  exact sub_eq_zero.1 hd.symm

end Weighted

section Pi

variable {ι : Type*} {S : ι → Type*} [∀ i, MeasurableSpace (S i)]

theorem exists_nonneg_bound_prod {α : Type*} (F : ι → α → ℝ) (J : Finset ι)
    (h : ∀ i ∈ J, ∃ C, ∀ y, |F i y| ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ y, |∏ i ∈ J, F i y| ≤ C := by
  classical
  revert h
  induction J using Finset.induction_on with
  | empty => intro _; exact ⟨1, zero_le_one, fun y => by simp⟩
  | @insert i s hi ih =>
      intro h
      obtain ⟨C, hC0, hC⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      obtain ⟨D, hD⟩ := h i (Finset.mem_insert_self i s)
      refine ⟨max D 0 * C, mul_nonneg (le_max_right _ _) hC0, fun y => ?_⟩
      rw [Finset.prod_insert hi, abs_mul]
      exact mul_le_mul ((hD y).trans (le_max_left _ _)) (hC y) (abs_nonneg _) (le_max_right _ _)

/-- The finite dimensional boxes: a `Set.pi` over a finite index set. -/
def boxes (S : ι → Type*) [∀ i, MeasurableSpace (S i)] : Set (Set (∀ i, S i)) :=
  {t | ∃ (J : Finset ι) (B : ∀ i, Set (S i)), (∀ i, MeasurableSet (B i)) ∧ t = Set.pi ↑J B}

theorem isPiSystem_boxes : IsPiSystem (boxes S) := by
  classical
  rintro _ ⟨J₁, B₁, hB₁, rfl⟩ _ ⟨J₂, B₂, hB₂, rfl⟩ -
  refine ⟨J₁ ∪ J₂, fun i => (if i ∈ J₁ then B₁ i else univ) ∩ (if i ∈ J₂ then B₂ i else univ),
    fun i => ?_, ?_⟩
  · exact MeasurableSet.inter (by by_cases h : i ∈ J₁ <;> simp [h, hB₁ i])
      (by by_cases h : i ∈ J₂ <;> simp [h, hB₂ i])
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      refine ⟨?_, ?_⟩
      · by_cases h : i ∈ J₁
        · simpa [h] using h1 i h
        · simp [h]
      · by_cases h : i ∈ J₂
        · simpa [h] using h2 i h
        · simp [h]
    · intro h
      exact ⟨fun i hi => by have := (h i (Or.inl hi)).1; simpa [hi] using this,
        fun i hi => by have := (h i (Or.inr hi)).2; simpa [hi] using this⟩

theorem generateFrom_boxes :
    MeasurableSpace.generateFrom (boxes S) = (MeasurableSpace.pi : MeasurableSpace (∀ i, S i)) := by
  classical
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (iSup_le fun i => ?_)
  · rintro _ ⟨J, B, hB, rfl⟩
    exact MeasurableSet.pi (Finset.countable_toSet J) fun i _ => hB i
  · rintro s ⟨t, ht, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨{i}, Function.update (fun _ => univ) i t, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Function.update_of_ne hj]
    · ext x
      simp

/-- Missing from Mathlib: products, for an **arbitrary** index type.  This is what
makes finite dimensional distributions determine a law; for a process the index
is the time set, so the finite case does not suffice.

The two side conditions are not decoration.  `IsSeparating` says nothing about the
members of `Γ i` themselves -- a non-integrable `f` contributes `∫ f = 0` on both
sides -- and the proof needs each `g i` as an honest weight: `W` has to be a bounded
measurable function for `sepPos T μ ν W` to be a finite measure at all.  Without
them the statement is not false but unproved, and the place where the argument
breaks is `isFiniteMeasure_weightedMap`.

The proof is an induction on `J` that replaces the members of `Γ i` by indicators
one index at a time, `integral_indicator_mul_eq_of_isSeparating` doing each step;
what comes out is equality on the boxes `Set.pi ↑J B`, and `isPiSystem_boxes`
together with `generateFrom_boxes` turns that into equality of measures. -/
theorem isSeparating_pi (Γ : ∀ i, Set (S i → ℝ)) (hsep : ∀ i, IsSeparating (Γ i))
    (hmeas : ∀ i, ∀ f ∈ Γ i, Measurable f)
    (hbdd : ∀ i, ∀ f ∈ Γ i, ∃ C, ∀ y, |f y| ≤ C) :
    IsSeparating {f : (∀ i, S i) → ℝ |
      ∃ (J : Finset ι) (g : ∀ i, S i → ℝ), (∀ i ∈ J, g i ∈ Γ i) ∧
        f = fun x => ∏ i ∈ J, g i (x i)} := by
  classical
  intro μ ν _ _ hyp
  have main : ∀ (J : Finset ι) (B : ∀ i, Set (S i)), (∀ i, MeasurableSet (B i)) →
      ∀ (J' : Finset ι), (∀ i ∈ J, i ∉ J') → ∀ (g : ∀ i, S i → ℝ), (∀ i ∈ J', g i ∈ Γ i) →
      ∫ x, (∏ i ∈ J, (B i).indicator (1 : S i → ℝ) (x i)) * ∏ i ∈ J', g i (x i) ∂μ
        = ∫ x, (∏ i ∈ J, (B i).indicator (1 : S i → ℝ) (x i)) * ∏ i ∈ J', g i (x i) ∂ν := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
        intro B hB J' _ g hg
        simp only [Finset.prod_empty, one_mul]
        exact hyp _ ⟨J', g, hg, rfl⟩
    | @insert i₀ J hi₀ ih =>
        intro B hB J' hdis g hg
        have hi₀J' : i₀ ∉ J' := hdis i₀ (Finset.mem_insert_self i₀ J)
        have hdis' : ∀ i ∈ J, i ∉ J' := fun i hi => hdis i (Finset.mem_insert_of_mem hi)
        set W : (∀ i, S i) → ℝ :=
          fun x => (∏ i ∈ J, (B i).indicator (1 : S i → ℝ) (x i)) * ∏ i ∈ J', g i (x i)
          with hWdef
        have hWmeas : Measurable W := by
          refine Measurable.mul (Finset.measurable_prod _ fun i _ => ?_)
            (Finset.measurable_prod _ fun i hi => ?_)
          · exact (measurable_const.indicator (hB i)).comp (measurable_pi_apply i)
          · exact (hmeas i (g i) (hg i hi)).comp (measurable_pi_apply i)
        obtain ⟨C1, hC10, hC1⟩ := exists_nonneg_bound_prod
          (fun i (x : ∀ i, S i) => (B i).indicator (1 : S i → ℝ) (x i)) J
          (fun i _ => ⟨1, fun x => by by_cases hx : x i ∈ B i <;> simp [hx]⟩)
        obtain ⟨C2, hC20, hC2⟩ := exists_nonneg_bound_prod
          (fun i (x : ∀ i, S i) => g i (x i)) J'
          (fun i hi => by
            obtain ⟨C, hC⟩ := hbdd i (g i) (hg i hi)
            exact ⟨C, fun x => hC _⟩)
        have hWb : ∀ x, |W x| ≤ C1 * C2 := fun x => abs_mul_le_mul (hC1 x) (hC2 x)
        have h0 : ∫ x, W x ∂μ = ∫ x, W x ∂ν := ih B hB J' hdis' g hg
        have hΓ : ∀ f ∈ Γ i₀, ∫ x, W x * f (x i₀) ∂μ = ∫ x, W x * f (x i₀) ∂ν := by
          intro f hf
          have hdis'' : ∀ i ∈ J, i ∉ insert i₀ J' := by
            intro i hi
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hi₀ (h ▸ hi), hdis' i hi⟩
          have hg' : ∀ i ∈ insert i₀ J', Function.update g i₀ f i ∈ Γ i := by
            intro i hi
            rcases Finset.mem_insert.1 hi with rfl | hi'
            · simpa using hf
            · have hne : i ≠ i₀ := by
                intro hEq
                subst hEq
                exact hi₀J' hi'
              rw [Function.update_of_ne hne]
              exact hg i hi'
          have key := ih B hB (insert i₀ J') hdis'' (Function.update g i₀ f) hg'
          have hrw : ∀ (ρ : Measure (∀ i, S i)),
              ∫ x, (∏ i ∈ J, (B i).indicator (1 : S i → ℝ) (x i)) *
                  ∏ i ∈ insert i₀ J', Function.update g i₀ f i (x i) ∂ρ
                = ∫ x, W x * f (x i₀) ∂ρ := by
            intro ρ
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            dsimp only
            rw [Finset.prod_insert hi₀J']
            have hres : ∀ i ∈ J', Function.update g i₀ f i (x i) = g i (x i) := by
              intro i hi
              rw [Function.update_of_ne (by rintro rfl; exact hi₀J' hi)]
            rw [Finset.prod_congr rfl hres, Function.update_self]
            simp only [hWdef]
            ring
          rw [hrw μ, hrw ν] at key
          exact key
        have hres := integral_indicator_mul_eq_of_isSeparating (hsep i₀) (hmeas i₀) (hbdd i₀)
          (measurable_pi_apply i₀) hWmeas hWb h0 hΓ (hB i₀)
        have hrw2 : ∀ (ρ : Measure (∀ i, S i)),
            ∫ x, (∏ i ∈ insert i₀ J, (B i).indicator (1 : S i → ℝ) (x i)) *
                ∏ i ∈ J', g i (x i) ∂ρ
              = ∫ x, W x * (B i₀).indicator (1 : S i₀ → ℝ) (x i₀) ∂ρ := by
          intro ρ
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [Finset.prod_insert hi₀]
          simp only [hWdef]
          ring
        rw [hrw2 μ, hrw2 ν]
        exact hres
  have hbox : ∀ s ∈ boxes S, μ s = ν s := by
    rintro _ ⟨J, B, hB, rfl⟩
    have h1 := main J B hB ∅ (fun i _ => Finset.notMem_empty i) (fun _ _ => 1) (by simp)
    simp only [Finset.prod_empty, mul_one] at h1
    have hind : ∀ (x : ∀ i, S i), (∏ i ∈ J, (B i).indicator (1 : S i → ℝ) (x i))
        = (Set.pi ↑J B).indicator (1 : (∀ i, S i) → ℝ) x := by
      intro x
      by_cases hx : x ∈ Set.pi (↑J : Set ι) B
      · rw [Set.indicator_of_mem hx]
        refine Finset.prod_eq_one fun i hi => ?_
        rw [Set.indicator_of_mem (hx i hi)]
        rfl
      · rw [Set.indicator_of_notMem hx]
        simp only [Set.mem_pi, Finset.mem_coe, not_forall] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        refine Finset.prod_eq_zero hi ?_
        rw [Set.indicator_of_notMem hxi]
    simp only [hind] at h1
    rw [integral_indicator_one (MeasurableSet.pi (Finset.countable_toSet J) fun i _ => hB i),
      integral_indicator_one (MeasurableSet.pi (Finset.countable_toSet J) fun i _ => hB i)] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h1
  exact ext_of_generate_finite (boxes S) generateFrom_boxes.symm isPiSystem_boxes hbox
    (by simp)

/-- Missing from Mathlib, which has the two-factor case as
`IsTightMeasureSet.prodMk` (`MeasureTheory/Measure/Tight.lean:144`) and nothing
for a countable product: if every family of one-coordinate marginals is tight,
so is the family itself.

The proof is the `ε 2⁻ⁿ` argument, and countability of the index is what makes it
work twice over -- once to distribute `ε` (`ENNReal.exists_pos_sum_of_countable'`)
and once for the countable subadditivity that turns
`(univ.pi K)ᶜ ⊆ ⋃ i, (· i) ⁻¹' (K i)ᶜ` into a sum.  Tychonoff supplies the compact
set, `isCompact_univ_pi`, and no separation or Borel hypothesis is needed: the
complement of the compact set is measured as an outer measure, so it never has to
be measurable. -/
theorem IsTightMeasureSet.pi [Countable ι] [∀ i, TopologicalSpace (S i)]
    {T : Set (Measure (∀ i, S i))}
    (h : ∀ i, IsTightMeasureSet ((fun ρ : Measure (∀ i, S i) => ρ.map (fun x => x i)) '' T)) :
    IsTightMeasureSet T := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  have h' : ∀ i, ∃ K : Set (S i), IsCompact K ∧
      ∀ ρ ∈ T, (ρ.map (fun x => x i)) Kᶜ ≤ δ i := by
    intro i
    obtain ⟨K, hK, hKle⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (h i) (δ i) (hδpos i)
    exact ⟨K, hK, fun ρ hρ => hKle _ ⟨ρ, hρ, rfl⟩⟩
  choose K hK hKle using h'
  refine ⟨Set.univ.pi K, isCompact_univ_pi hK, fun ρ hρ => ?_⟩
  have hsub : (Set.univ.pi K)ᶜ ⊆ ⋃ i, (fun x : ∀ i, S i => x i) ⁻¹' (K i)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc ρ (Set.univ.pi K)ᶜ
      ≤ ρ (⋃ i, (fun x : ∀ i, S i => x i) ⁻¹' (K i)ᶜ) := measure_mono hsub
    _ ≤ ∑' i, ρ ((fun x : ∀ i, S i => x i) ⁻¹' (K i)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' i, δ i := ENNReal.tsum_le_tsum fun i =>
        (Measure.le_map_apply (measurable_pi_apply i).aemeasurable _).trans (hKle i ρ hρ)
    _ ≤ ε := hδsum.le

/-- The convergence determining half of the product point, and the reason it
carries hypotheses `isSeparating_pi` does not: a **countable** index and
**Polish** factors.  Both enter through tightness and nowhere else.  Countability
is what `IsTightMeasureSet.pi` needs; Polishness is what turns the convergence of
the one-coordinate marginals into their tightness
(`isTightMeasureSet_of_tendsto`), and it is also what
`tendsto_of_isSeparating_of_isTightMeasureSet` needs for Prokhorov.

Continuity replaces the measurability hypothesis of `isSeparating_pi`, and the
boundedness hypothesis is the same one.  Continuity is not a convenience: the
identification of a subsequential limit tests it against the class, and weak
convergence sees only bounded continuous functions.

The proof is three steps and no new analysis.  Testing the hypothesis on the
one-index members `x ↦ f (x i)` of the product class shows every marginal
sequence converges, which is `IsConvergenceDetermining (Γ i)` read backwards;
each marginal family is then tight, hence so is the family itself; and
`isSeparating_pi` identifies the limit. -/
theorem isConvergenceDetermining_pi [Countable ι] [∀ i, TopologicalSpace (S i)]
    [∀ i, PolishSpace (S i)] [∀ i, BorelSpace (S i)]
    (Γ : ∀ i, Set (S i → ℝ)) (hcd : ∀ i, IsConvergenceDetermining (Γ i))
    (hcont : ∀ i, ∀ f ∈ Γ i, Continuous f)
    (hbdd : ∀ i, ∀ f ∈ Γ i, ∃ C, ∀ y, |f y| ≤ C) :
    IsConvergenceDetermining {f : (∀ i, S i) → ℝ |
      ∃ (J : Finset ι) (g : ∀ i, S i → ℝ), (∀ i ∈ J, g i ∈ Γ i) ∧
        f = fun x => ∏ i ∈ J, g i (x i)} := by
  classical
  intro μ ν hyp
  -- `x ↦ f (x i)` is the member of the product class with `J = {i}`.
  have hmem : ∀ (i : ι), ∀ f ∈ Γ i, (fun x : ∀ j, S j => f (x i)) ∈
      {f : (∀ i, S i) → ℝ | ∃ (J : Finset ι) (g : ∀ i, S i → ℝ), (∀ i ∈ J, g i ∈ Γ i) ∧
        f = fun x => ∏ i ∈ J, g i (x i)} := by
    intro i f hf
    refine ⟨{i}, Function.update (fun j => (0 : S j → ℝ)) i f, ?_, ?_⟩
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      simpa using hf
    · funext x
      simp
  -- Step 1: every one-coordinate marginal converges.
  have hmarg : ∀ i, Tendsto
      (fun n => (μ n).map (f := fun x : ∀ j, S j => x i) (measurable_pi_apply i).aemeasurable)
      atTop (𝓝 (ν.map (f := fun x : ∀ j, S j => x i) (measurable_pi_apply i).aemeasurable)) := by
    intro i
    refine hcd i _ _ fun f hf => ?_
    have hint : ∀ ρ : ProbabilityMeasure (∀ j, S j),
        ∫ y, f y ∂((ρ.map (f := fun x : ∀ j, S j => x i)
            (measurable_pi_apply i).aemeasurable : ProbabilityMeasure (S i)) : Measure (S i))
          = ∫ x, f (x i) ∂(ρ : Measure (∀ j, S j)) := by
      intro ρ
      rw [ProbabilityMeasure.toMeasure_map]
      exact integral_map (measurable_pi_apply i).aemeasurable
        (hcont i f hf).aestronglyMeasurable
    simp only [hint]
    exact hyp _ (hmem i f hf)
  -- Step 2: hence each marginal family is tight, and hence so is the family itself.
  have htight : IsTightMeasureSet
      {((μ n : ProbabilityMeasure (∀ j, S j)) : Measure (∀ j, S j)) | n} := by
    refine IsTightMeasureSet.pi fun i => ?_
    have h1 := isTightMeasureSet_of_tendsto (hmarg i)
    have hset : (fun ρ : Measure (∀ j, S j) => ρ.map (fun x => x i)) ''
        {((μ n : ProbabilityMeasure (∀ j, S j)) : Measure (∀ j, S j)) | n}
        = {((μ n).map (f := fun x : ∀ j, S j => x i)
            (measurable_pi_apply i).aemeasurable : Measure (S i)) | n} := by
      ext ρ
      constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨(μ n : Measure (∀ j, S j)), ⟨n, rfl⟩, rfl⟩
    rw [hset]
    exact h1
  -- Step 3: the product class separates, so it identifies the limit.
  refine tendsto_of_isSeparating_of_isTightMeasureSet
    (isSeparating_pi Γ (fun i => (hcd i).isSeparating)
      (fun i f hf => (hcont i f hf).measurable) hbdd) ?_ ?_ htight hyp
  · rintro _ ⟨J, g, hg, rfl⟩
    exact continuous_finsetProd J fun i hi => (hcont i (g i) (hg i hi)).comp (continuous_apply i)
  · rintro _ ⟨J, g, hg, rfl⟩
    obtain ⟨C, -, hC⟩ := exists_nonneg_bound_prod (fun i (x : ∀ j, S j) => g i (x i)) J
      (fun i hi => by
        obtain ⟨D, hD⟩ := hbdd i (g i) (hg i hi)
        exact ⟨D, fun x => hD _⟩)
    exact ⟨C, hC⟩

end Pi

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
proof -- on `upstream/master`.  In `v4.33.1` it is `ibid.:608` and takes an
`AEMeasurable` proof, with the function implicit, so the statement below is the
one place in this file that `lake env lean` reports an error; that is the
deliberate choice recorded in the module doc, and the fix against `v4.33.1`
would be to write `hh.aemeasurable` for `h` twice. -/

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
    P (fun x => φ (fun i => f i x)) := by
  classical
  -- One bound for the finitely many members of `K` in play.  The sum of the
  -- absolute values, not the supremum: `Fin n` may be empty, and a supremum
  -- over an empty family is a junk value.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (i : Fin n) (x : Ω), |f i x| ≤ C := by
    choose c hc using fun i : Fin n => hKbdd (f i) (hf i)
    refine ⟨∑ j, |c j|, fun i x => ?_⟩
    calc |f i x| ≤ c i := hc i x
      _ ≤ |c i| := le_abs_self _
      _ ≤ ∑ j, |c j| :=
          Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
  -- The compact box in which the vector of values lives.
  set box : Set (Fin n → ℝ) := Set.Icc (fun _ => -C) (fun _ => C) with hbox
  have hboxc : IsCompact box := isCompact_Icc
  have hmem : ∀ x : Ω, (fun i => f i x) ∈ box :=
    fun x => ⟨fun i => (abs_le.1 (hC i x)).1, fun i => (abs_le.1 (hC i x)).2⟩
  -- The subalgebra generated by `K`, and the pullback of functions of the box
  -- into it.  The pullback is an algebra map, so it suffices to check the
  -- generators, and there it is the identity: the `i`-th coordinate pulls back
  -- to `f i`.
  set B : Subalgebra ℝ (Ω → ℝ) :=
    (Submodule.span ℝ (insert (1 : Ω → ℝ) K)).toSubalgebra
      (Submodule.subset_span (Set.mem_insert _ _))
      (fun _ _ hu hv => mul_mem_span_insert_one_of_isMulSystem hK hu hv) with hB
  set Ψ : C(Fin n → ℝ, ℝ) →ₐ[ℝ] (Ω → ℝ) :=
    { toFun := fun g x => g (fun i => f i x)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl } with hΨ
  set coord : Fin n → C(Fin n → ℝ, ℝ) :=
    fun i => ⟨fun z => z i, continuous_apply i⟩ with hcoord
  set A : Subalgebra ℝ C(Fin n → ℝ, ℝ) := Algebra.adjoin ℝ (Set.range coord) with hA
  have hpull : ∀ g ∈ A,
      (fun x => (g : (Fin n → ℝ) → ℝ) (fun i => f i x)) ∈
        Submodule.span ℝ (insert (1 : Ω → ℝ) K) := by
    have hle : A ≤ Subalgebra.comap Ψ B := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (hf i))
    exact fun g hg => hle hg
  -- The coordinates separate the points of the box, so Stone-Weierstrass
  -- approximates `φ` there to any accuracy.
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hzw
    exact ⟨_, ⟨coord i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, hi⟩
  have happrox : ∀ k : ℕ, ∃ u : Ω → ℝ,
      u ∈ Submodule.span ℝ (insert (1 : Ω → ℝ) K) ∧
        ∀ x, |u x - φ (fun i => f i x)| ≤ 1 / (k + 1 : ℝ) := by
    intro k
    obtain ⟨g, hgA, hg⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
        hsep ⟨φ, hφ⟩ hboxc (show (0:ℝ) < 1 / (k + 1 : ℝ) by positivity)
    exact ⟨_, hpull g hgA, fun x => by
      simpa [Real.norm_eq_abs] using (hg _ (hmem x)).le⟩
  choose u hu hu' using happrox
  -- The approximants are in `P` by linearity, and the uniform limit is in `P`
  -- by the first step.
  refine of_tendstoUniformly_of_mono_lim const add mono_lim
    (fun k => of_mem_span_insert_one basic const add smul (hu k)) ?_ ?_
  · obtain ⟨D, hD⟩ := hboxc.exists_bound_of_continuousOn hφ.continuousOn
    exact ⟨D, fun x => by simpa [Real.norm_eq_abs] using hD _ (hmem x)⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with k hk x
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (hu' k x) (lt_of_le_of_lt ?_ hN)
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
    linarith

/-! ### The indicators: step (iii)

Step (ii) hands out `P (φ ∘ (f₁, …, fₙ))` for every continuous `φ`.  Feeding it
a product of `n` continuous ramps, the `i`-th rising from `0` to `1` just above
the level `cᵢ`, produces an increasing sequence in `P` converging pointwise to
the indicator of the cell `⋂ᵢ fᵢ⁻¹(cᵢ, ∞)`; the cells form a π-system generating
`generateFromFuns K` (`isPiSystem_ioiCells`,
`generateFromFuns_eq_generateFrom_ioiCells`), so Dynkin's π-λ theorem carries
`P` to the indicator of every set of that σ-algebra.

The ramps have to be taken **jointly**, as one continuous function of the `n`
values, not one factor at a time: `P` is not closed under multiplication, and a
factorwise argument would need exactly that.  This is why step (ii) is stated
for a continuous function of finitely many members of `K` and not for one. -/

/-- The continuous ramp approximating the indicator of `Set.Ioi 0` from below:
`ioiApprox k` vanishes on `(-∞, 0]`, rises with slope `k + 1`, and equals `1`
from `1 / (k + 1)` on.  The slope is `k + 1` rather than `k` so that the family
is nondecreasing from `k = 0` on, with no degenerate first member. -/
noncomputable def ioiApprox (k : ℕ) (t : ℝ) : ℝ := min 1 (max 0 (((k : ℝ) + 1) * t))

theorem continuous_ioiApprox (k : ℕ) : Continuous (ioiApprox k) :=
  continuous_const.min (continuous_const.max (continuous_const.mul continuous_id))

theorem ioiApprox_nonneg (k : ℕ) (t : ℝ) : 0 ≤ ioiApprox k t :=
  le_min zero_le_one (le_max_left _ _)

theorem ioiApprox_le_one (k : ℕ) (t : ℝ) : ioiApprox k t ≤ 1 := min_le_left _ _

/-- Below the level the ramp is flat at `0`, for every `k`: this is what makes
the limit of the products vanish off the cell. -/
theorem ioiApprox_of_nonpos {t : ℝ} (ht : t ≤ 0) (k : ℕ) : ioiApprox k t = 0 := by
  have h : ((k : ℝ) + 1) * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  rw [ioiApprox, max_eq_left h, min_eq_right zero_le_one]

/-- Above the level the ramp has reached `1` as soon as the slope is large
enough. -/
theorem ioiApprox_of_one_le {t : ℝ} {k : ℕ} (h : 1 ≤ ((k : ℝ) + 1) * t) :
    ioiApprox k t = 1 :=
  min_eq_left (le_max_of_le_right h)

theorem monotone_ioiApprox (t : ℝ) : Monotone fun k : ℕ => ioiApprox k t := by
  intro k m hkm
  show ioiApprox k t ≤ ioiApprox m t
  rcases le_or_gt t 0 with ht | ht
  · rw [ioiApprox_of_nonpos ht, ioiApprox_of_nonpos ht]
  · have hk : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hkm
    exact min_le_min le_rfl
      (max_le_max le_rfl (mul_le_mul_of_nonneg_right (by linarith) ht.le))

/-- Step (iii), first half: `P` holds of the indicator of every cell.

The cell of a list `l` is `⋂ p ∈ l, p.1 ⁻¹' Ioi p.2`, and its indicator is the
pointwise increasing limit of the products
`∏ᵢ ioiApprox k (fᵢ x - cᵢ)`, each of which is a continuous function of
`f₁ x, …, fₙ x` and so lies in `P` by `of_continuous_comp_of_isMulSystem`.  Off
the cell some factor is `0` for every `k`; on it every factor reaches `1` for
`k` large, and that is the one place where the finiteness of the list is
used. -/
theorem of_indicator_mem_ioiCells {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    {s : Set Ω} (hs : s ∈ ioiCells K) :
    P (Set.indicator s (1 : Ω → ℝ)) := by
  classical
  obtain ⟨l, hl, rfl⟩ := hs
  have hf : ∀ i : Fin l.length, (l[(i : ℕ)]'i.isLt).1 ∈ K := fun i =>
    hl _ (List.getElem_mem _)
  have hmem : ∀ x : Ω, x ∈ (⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2) ↔
      ∀ i : Fin l.length, 0 < (l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2 := by
    intro x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos]
    constructor
    · intro hx i
      exact hx _ (List.getElem_mem _)
    · intro hx p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      exact hx ⟨i, hi⟩
  refine mono_lim (fun k x => ∏ i : Fin l.length,
    ioiApprox k ((l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2)) _ ?_ ?_ ⟨1, ?_⟩ ?_
  · intro x k m hkm
    exact Finset.prod_le_prod (fun i _ => ioiApprox_nonneg _ _)
      (fun i _ => monotone_ioiApprox _ hkm)
  · intro k
    exact of_continuous_comp_of_isMulSystem hK hKbdd basic const add smul mono_lim
      (fun i : Fin l.length => (l[(i : ℕ)]'i.isLt).1) hf
      (φ := fun z => ∏ i : Fin l.length, ioiApprox k (z i - (l[(i : ℕ)]'i.isLt).2))
      (continuous_finsetProd _ fun i _ =>
        (continuous_ioiApprox k).comp ((continuous_apply i).sub continuous_const))
  · intro k x
    have h0 : (0 : ℝ) ≤ ∏ i : Fin l.length,
        ioiApprox k ((l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2) :=
      Finset.prod_nonneg fun i _ => ioiApprox_nonneg _ _
    have h1 : (∏ i : Fin l.length,
        ioiApprox k ((l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => ioiApprox_nonneg _ _) fun i _ => ioiApprox_le_one _ _
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  · intro x
    by_cases hx : x ∈ (⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2)
    · have hval : Set.indicator (⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2) (1 : Ω → ℝ) x = 1 := by
        simp [Set.indicator_of_mem hx]
      rw [hval]
      have hpos := (hmem x).1 hx
      choose N hN using fun i : Fin l.length =>
        exists_nat_gt (1 / ((l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2))
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (∑ i : Fin l.length, N i)] with k hk
      symm
      refine Finset.prod_eq_one fun i _ => ioiApprox_of_one_le ?_
      have hNi : (N i : ℝ) ≤ (k : ℝ) := by
        have hle : N i ≤ k :=
          le_trans (Finset.single_le_sum (f := fun j => N j)
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) hk
        exact_mod_cast hle
      have hlt : 1 / ((l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2) < (k : ℝ) + 1 := by
        have := hN i
        linarith
      rw [div_lt_iff₀ (hpos i)] at hlt
      exact hlt.le
    · have hval : Set.indicator (⋂ p ∈ l, p.1 ⁻¹' Set.Ioi p.2) (1 : Ω → ℝ) x = 0 :=
        Set.indicator_of_notMem hx _
      rw [hval]
      obtain ⟨i, hi⟩ : ∃ i : Fin l.length,
          ¬ 0 < (l[(i : ℕ)]'i.isLt).1 x - (l[(i : ℕ)]'i.isLt).2 := by
        by_contra hcon
        exact hx ((hmem x).2 fun i => not_not.1 fun h => hcon ⟨i, h⟩)
      have hzero : ∀ k : ℕ, (∏ j : Fin l.length,
          ioiApprox k ((l[(j : ℕ)]'j.isLt).1 x - (l[(j : ℕ)]'j.isLt).2)) = 0 :=
        fun k => Finset.prod_eq_zero (Finset.mem_univ i)
          (ioiApprox_of_nonpos (not_lt.1 hi) k)
      simp only [hzero]
      exact tendsto_const_nhds

/-- Step (iii), second half: `P` holds of the indicator of every
`generateFromFuns K`-measurable set.

This is Dynkin's π-λ theorem, `MeasurableSpace.induction_on_inter`
(`MeasureTheory/PiSystem.lean:713`), along the π-system `ioiCells K`.  The three
non-basic cases are where the shape of `P` is used and nothing else:
`Set.indicator ∅ 1` is the constant `0`; `Set.indicator sᶜ 1` is
`1 + (-1) • Set.indicator s 1`, so complements come from linearity and the
constants; and the indicator of a disjoint union is the increasing, uniformly
bounded limit of the partial sums, so countable disjoint unions come from
`mono_lim`.  Disjointness enters exactly once, in the bound `≤ 1`: without it
the partial sums still increase, but they are not bounded. -/
theorem of_indicator_of_measurable {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    (s : Set Ω) (hs : MeasurableSet[generateFromFuns K] s) :
    P (Set.indicator s (1 : Ω → ℝ)) := by
  classical
  refine MeasurableSpace.induction_on_inter (m := generateFromFuns K)
    (C := fun t _ => P (Set.indicator t (1 : Ω → ℝ)))
    (generateFromFuns_eq_generateFrom_ioiCells K) (isPiSystem_ioiCells K)
    ?_ ?_ ?_ ?_ s hs
  · have he : Set.indicator (∅ : Set Ω) (1 : Ω → ℝ) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [he]
    exact const 0
  · intro t ht
    exact of_indicator_mem_ioiCells hK hKbdd basic const add smul mono_lim ht
  · intro t _ ih
    have he : Set.indicator tᶜ (1 : Ω → ℝ)
        = (fun _ => (1 : ℝ)) + (-1 : ℝ) • Set.indicator t (1 : Ω → ℝ) := by
      funext x
      by_cases hxt : x ∈ t <;> simp [hxt]
    rw [he]
    exact add _ _ (const 1) (smul _ _ ih)
  · intro g hgd _ hgP
    have hone : ∀ (i m : ℕ) (x : Ω), x ∈ g i → i < m →
        ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x = 1 := by
      intro i m x hxi him
      have hmem : i ∈ Finset.range m := Finset.mem_range.2 him
      have h0 : ∀ j ∈ Finset.range m, j ≠ i → Set.indicator (g j) (1 : Ω → ℝ) x = 0 :=
        fun j _ hne =>
          Set.indicator_of_notMem (fun hxj => Set.disjoint_left.1 (hgd hne) hxj hxi) _
      rw [Finset.sum_eq_single_of_mem i hmem h0, Set.indicator_of_mem hxi, Pi.one_apply]
    have hzero : ∀ (m : ℕ) (x : Ω), (∀ i, x ∉ g i) →
        ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x = 0 :=
      fun m x hx => Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hx j) _
    refine mono_lim
      (fun m x => ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x)
      _ ?_ ?_ ⟨1, ?_⟩ ?_
    · intro x m m' hmm'
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmm')
        fun j _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x
    · intro m
      induction m with
      | zero => simpa using const 0
      | succ m ih =>
        have he : (fun x => ∑ j ∈ Finset.range (m + 1), Set.indicator (g j) (1 : Ω → ℝ) x)
            = (fun x => ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x)
              + Set.indicator (g m) (1 : Ω → ℝ) := by
          funext x
          simp [Finset.sum_range_succ]
        rw [he]
        exact add _ _ ih (hgP m)
    · intro m x
      have hnonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x :=
        Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have hle : ∑ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x ≤ 1 := by
        by_cases hx : ∃ i, x ∈ g i
        · obtain ⟨i, hi⟩ := hx
          by_cases him : i < m
          · rw [hone i m x hi him]
          · have hall : ∀ j ∈ Finset.range m, Set.indicator (g j) (1 : Ω → ℝ) x = 0 := by
              intro j hj
              refine Set.indicator_of_notMem (fun hxj => ?_) _
              have hne : j ≠ i := by
                rintro rfl
                exact him (Finset.mem_range.1 hj)
              exact Set.disjoint_left.1 (hgd hne) hxj hi
            rw [Finset.sum_congr rfl hall]
            simp
        · rw [hzero m x fun i hxi => hx ⟨i, hxi⟩]
          norm_num
      rw [abs_le]
      exact ⟨by linarith, hle⟩
    · intro x
      by_cases hx : x ∈ ⋃ i, g i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        rw [Set.indicator_of_mem hx, Pi.one_apply]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_gt_atTop i] with m hm
        exact (hone i m x hi hm).symm
      · rw [Set.indicator_of_notMem hx]
        have hx' : ∀ i, x ∉ g i := fun i hxi => hx (Set.mem_iUnion.2 ⟨i, hxi⟩)
        simp only [hzero _ x hx']
        exact tendsto_const_nhds

/-! ### The measurable functions: step (iv)

From the indicators to every bounded measurable function, in two moves that use
nothing about `K` any more: a simple function is a finite sum of scalar
multiples of indicators, and a nonnegative measurable function is the increasing
limit of simple ones. -/

/-- Step (iv), first half: `P` holds of every simple function for the σ-algebra
generated by `K`.

`MeasureTheory.SimpleFunc.induction` cuts a simple function into scalar
multiples of indicators of measurable sets and sums of those, which is exactly
what `smul`, `add` and step (iii) supply.  Boundedness is not a hypothesis here:
a simple function has finite range and is bounded of itself. -/
theorem of_simpleFunc {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    (f : @SimpleFunc Ω (generateFromFuns K) ℝ) : P ⇑f := by
  classical
  let _ : MeasurableSpace Ω := generateFromFuns K
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    have he : ⇑(SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0))
        = c • Set.indicator s (1 : Ω → ℝ) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [he]
    exact smul _ _ (of_indicator_of_measurable hK hKbdd basic const add smul mono_lim s hs)
  | add _ hf hg => exact add _ _ hf hg

/-- Step (iv), second half, for a nonnegative function: the increasing limit of
`MeasureTheory.SimpleFunc.eapprox`.

The detour through `ℝ≥0∞` is what makes the approximation *increasing*, which is
what `mono_lim` needs and what `SimpleFunc.approxOn` does not give; the values
are finite throughout (`SimpleFunc.eapprox_lt_top`), so `ENNReal.toReal` carries
the monotonicity and the limit back to `ℝ`.  Boundedness of the approximants is
free from `eapprox f n ≤ f`. -/
theorem of_nonneg_of_measurable {K : Set (Ω → ℝ)} {P : (Ω → ℝ) → Prop}
    (hK : IsMulSystem K) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (basic : ∀ f ∈ K, P f)
    (const : ∀ c : ℝ, P (fun _ => c))
    (add : ∀ f g : Ω → ℝ, P f → P g → P (f + g))
    (smul : ∀ (c : ℝ) (f : Ω → ℝ), P f → P (c • f))
    (mono_lim : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => f n x) →
      (∀ n, P (f n)) → (∃ C, ∀ (n : ℕ) (x : Ω), |f n x| ≤ C) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → P g)
    (f : Ω → ℝ) (hf : Measurable[generateFromFuns K] f) (hf0 : ∀ x, 0 ≤ f x)
    (hfbdd : ∃ C, ∀ x, |f x| ≤ C) : P f := by
  classical
  let _ : MeasurableSpace Ω := generateFromFuns K
  obtain ⟨C, hC⟩ := hfbdd
  have hmeas : Measurable fun x => ENNReal.ofReal (f x) := hf.ennreal_ofReal
  set e : ℕ → SimpleFunc Ω ℝ≥0∞ :=
    fun n => SimpleFunc.eapprox (fun x => ENNReal.ofReal (f x)) n
    with he
  have hlt : ∀ (n : ℕ) (x : Ω), e n x ≠ ∞ := fun n x =>
    (SimpleFunc.eapprox_lt_top (fun y => ENNReal.ofReal (f y)) n x).ne
  have hle : ∀ (n : ℕ) (x : Ω), e n x ≤ ENNReal.ofReal (f x) := by
    intro n x
    rw [← SimpleFunc.iSup_eapprox_apply hmeas x]
    exact le_iSup (fun n => (SimpleFunc.eapprox (fun y => ENNReal.ofReal (f y)) n) x) n
  refine mono_lim (fun n x => (e n x).toReal) f (fun x n m hnm => ?_) (fun n => ?_)
    ⟨C, fun n x => ?_⟩ fun x => ?_
  · exact ENNReal.toReal_mono (hlt m x) (SimpleFunc.monotone_eapprox _ hnm x)
  · have hcoe : (fun x => (e n x).toReal) = ⇑((e n).map ENNReal.toReal) := rfl
    rw [hcoe]
    exact of_simpleFunc hK hKbdd basic const add smul mono_lim _
  · have h1 : (e n x).toReal ≤ f x := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle n x)
      rwa [ENNReal.toReal_ofReal (hf0 x)] at this
    have h2 : (0 : ℝ) ≤ (e n x).toReal := ENNReal.toReal_nonneg
    have h3 : f x ≤ C := (abs_le.1 (hC x)).2
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · have htend : Tendsto (fun n => (e n x).toReal) atTop (𝓝 (ENNReal.ofReal (f x)).toReal) :=
      (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
        (SimpleFunc.tendsto_eapprox hmeas x)
    rwa [ENNReal.toReal_ofReal (hf0 x)] at htend

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

All four steps are proved: `of_tendstoUniformly_of_mono_lim`,
`of_continuous_comp_of_isMulSystem`, `of_indicator_mem_ioiCells` together with
`of_indicator_of_measurable`, and `of_simpleFunc` together with
`of_nonneg_of_measurable`.  What is left here is the reduction of a bounded
measurable function to a nonnegative one, which is the shift by its bound: `P`
contains the constants and is closed under addition, so `f = (f + C) + (-C)`. -/
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
    P f := by
  classical
  let _ : MeasurableSpace Ω := generateFromFuns K
  obtain ⟨C, hC⟩ := hfbdd
  have hshift : P (fun x => f x + C) :=
    of_nonneg_of_measurable hK hKbdd basic const add smul mono_lim _
      (hf.add_const C) (fun x => by have := (abs_le.1 (hC x)).1; linarith)
      ⟨2 * C, fun x => by
        have h1 := (abs_le.1 (hC x)).1
        have h2 := (abs_le.1 (hC x)).2
        rw [abs_le]
        constructor <;> linarith⟩
  have hsum := add _ _ hshift (const (-C))
  have he : ((fun x => f x + C) + fun _ => (-C)) = f := by funext x; simp
  rwa [he] at hsum

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
    ∀ s, MeasurableSet[generateFromFuns K] s → μ s = ν s := by
  classical
  have hle : generateFromFuns K ≤ mΩ := generateFromFuns_le_iff.2 hKm
  -- Bounded and measurable is integrable, on a finite measure.
  have hint : ∀ {ρ : Measure Ω}, IsFiniteMeasure ρ → ∀ (g : Ω → ℝ),
      AEStronglyMeasurable g ρ → ∀ C : ℝ, (∀ x, |g x| ≤ C) → Integrable g ρ := by
    intro ρ hρ g hg C hC
    have : IsFiniteMeasure ρ := hρ
    exact Integrable.mono' (integrable_const C) hg
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  -- The property carried through the induction: integrable on both sides, and
  -- with the same integral.  Integrability has to travel with the equality --
  -- the additivity of the integral is what needs it.
  have hbasic : ∀ f ∈ K, Integrable f μ ∧ Integrable f ν ∧ ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    intro f hf
    obtain ⟨C, hC⟩ := hKbdd f hf
    have hm : AEStronglyMeasurable f μ := (hKm f hf).aestronglyMeasurable
    have hm' : AEStronglyMeasurable f ν := (hKm f hf).aestronglyMeasurable
    exact ⟨hint inferInstance f hm C hC, hint inferInstance f hm' C hC, h f hf⟩
  have hconst : ∀ c : ℝ,
      Integrable (fun _ : Ω => c) μ ∧ Integrable (fun _ : Ω => c) ν ∧
        ∫ _ : Ω, c ∂μ = ∫ _ : Ω, c ∂ν := by
    intro c
    refine ⟨integrable_const c, integrable_const c, ?_⟩
    simp only [integral_const, measureReal_def, hmass]
  have hadd : ∀ f g : Ω → ℝ,
      (Integrable f μ ∧ Integrable f ν ∧ ∫ x, f x ∂μ = ∫ x, f x ∂ν) →
      (Integrable g μ ∧ Integrable g ν ∧ ∫ x, g x ∂μ = ∫ x, g x ∂ν) →
      (Integrable (f + g) μ ∧ Integrable (f + g) ν ∧
        ∫ x, (f + g) x ∂μ = ∫ x, (f + g) x ∂ν) := by
    rintro f g ⟨hfμ, hfν, hfe⟩ ⟨hgμ, hgν, hge⟩
    refine ⟨hfμ.add hgμ, hfν.add hgν, ?_⟩
    simp only [Pi.add_apply]
    rw [integral_add hfμ hgμ, integral_add hfν hgν, hfe, hge]
  have hsmul : ∀ (c : ℝ) (f : Ω → ℝ),
      (Integrable f μ ∧ Integrable f ν ∧ ∫ x, f x ∂μ = ∫ x, f x ∂ν) →
      (Integrable (c • f) μ ∧ Integrable (c • f) ν ∧
        ∫ x, (c • f) x ∂μ = ∫ x, (c • f) x ∂ν) := by
    rintro c f ⟨hfμ, hfν, hfe⟩
    refine ⟨hfμ.smul c, hfν.smul c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hfe]
  have hmono : ∀ (F : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ x, Monotone fun n => F n x) →
      (∀ n, Integrable (F n) μ ∧ Integrable (F n) ν ∧
        ∫ x, F n x ∂μ = ∫ x, F n x ∂ν) →
      (∃ C, ∀ (n : ℕ) (x : Ω), |F n x| ≤ C) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x))) →
      (Integrable g μ ∧ Integrable g ν ∧ ∫ x, g x ∂μ = ∫ x, g x ∂ν) := by
    rintro F g _ hFP ⟨C, hC⟩ hlim
    have hgμ : AEStronglyMeasurable g μ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hFP n).1.aestronglyMeasurable)
        (Filter.Eventually.of_forall hlim)
    have hgν : AEStronglyMeasurable g ν :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hFP n).2.1.aestronglyMeasurable)
        (Filter.Eventually.of_forall hlim)
    have hgbdd : ∀ x, |g x| ≤ C := fun x =>
      le_of_tendsto (hlim x).abs (Filter.Eventually.of_forall fun n => hC n x)
    refine ⟨hint inferInstance g hgμ C hgbdd, hint inferInstance g hgν C hgbdd, ?_⟩
    have h1 : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (hFP n).1.aestronglyMeasurable) (integrable_const C)
        (fun n => Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC n x)
        (Filter.Eventually.of_forall hlim)
    have h2 : Tendsto (fun n => ∫ x, F n x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) :=
      tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (hFP n).2.1.aestronglyMeasurable) (integrable_const C)
        (fun n => Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC n x)
        (Filter.Eventually.of_forall hlim)
    have h3 : (fun n => ∫ x, F n x ∂μ) = fun n => ∫ x, F n x ∂ν :=
      funext fun n => (hFP n).2.2
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  intro s hs
  have hsm : MeasurableSet s := hle s hs
  have hind : Measurable[generateFromFuns K] (Set.indicator s (1 : Ω → ℝ)) :=
    measurable_const.indicator hs
  have hbdd : ∀ x, |Set.indicator s (1 : Ω → ℝ) x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  -- The expected type has to be written out: `induction_on_mulSystem` is
  -- `@[elab_as_elim]`, and the motive is read off the goal.
  have hres : Integrable (Set.indicator s (1 : Ω → ℝ)) μ ∧
      Integrable (Set.indicator s (1 : Ω → ℝ)) ν ∧
      ∫ x, Set.indicator s (1 : Ω → ℝ) x ∂μ
        = ∫ x, Set.indicator s (1 : Ω → ℝ) x ∂ν :=
    induction_on_mulSystem hK hKbdd hbasic hconst hadd hsmul hmono
      (Set.indicator s (1 : Ω → ℝ)) hind ⟨1, hbdd⟩
  have hreal : μ.real s = ν.real s := by
    have := hres.2.2
    rwa [integral_indicator_one hsm, integral_indicator_one hsm] at this
  exact (measureReal_eq_measureReal_iff (measure_ne_top μ s) (measure_ne_top ν s)).1 hreal

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
      ∫ x, g x * f x ∂μ = 0 := by
  classical
  -- Integrability of the product travels with the vanishing, as in
  -- `ext_of_forall_integral_eq_of_isMulSystem`, and for the same reason.
  have hbasic : ∀ f ∈ K, Integrable (fun x => g x * f x) μ ∧ ∫ x, g x * f x ∂μ = 0 := by
    intro f hf
    obtain ⟨C, hC⟩ := hKbdd f hf
    refine ⟨?_, h f hf⟩
    refine Integrable.mono' (hg.abs.const_mul C)
      (hg.aestronglyMeasurable.mul (hKm f hf).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _) |>.trans_eq (mul_comm _ _)
  have hconst : ∀ c : ℝ,
      Integrable (fun x => g x * c) μ ∧ ∫ x, g x * c ∂μ = 0 := by
    intro c
    refine ⟨hg.mul_const c, ?_⟩
    rw [integral_mul_const, hg0, zero_mul]
  have hadd : ∀ f₁ f₂ : Ω → ℝ,
      (Integrable (fun x => g x * f₁ x) μ ∧ ∫ x, g x * f₁ x ∂μ = 0) →
      (Integrable (fun x => g x * f₂ x) μ ∧ ∫ x, g x * f₂ x ∂μ = 0) →
      (Integrable (fun x => g x * (f₁ + f₂) x) μ ∧ ∫ x, g x * (f₁ + f₂) x ∂μ = 0) := by
    rintro f₁ f₂ ⟨hi₁, he₁⟩ ⟨hi₂, he₂⟩
    have hfun : (fun x => g x * (f₁ + f₂) x)
        = (fun x => g x * f₁ x) + fun x => g x * f₂ x := by
      funext x; simp [mul_add]
    rw [hfun]
    refine ⟨hi₁.add hi₂, ?_⟩
    show ∫ x, (g x * f₁ x + g x * f₂ x) ∂μ = 0
    rw [integral_add hi₁ hi₂, he₁, he₂, add_zero]
  have hsmul : ∀ (c : ℝ) (f : Ω → ℝ),
      (Integrable (fun x => g x * f x) μ ∧ ∫ x, g x * f x ∂μ = 0) →
      (Integrable (fun x => g x * (c • f) x) μ ∧ ∫ x, g x * (c • f) x ∂μ = 0) := by
    rintro c f ⟨hi, he⟩
    have hfun : (fun x => g x * (c • f) x) = c • fun x => g x * f x := by
      funext x
      show g x * (c * f x) = c * (g x * f x)
      ring
    rw [hfun]
    refine ⟨hi.smul c, ?_⟩
    show ∫ x, c • (g x * f x) ∂μ = 0
    rw [integral_smul, he, smul_zero]
  have hmono : ∀ (F : ℕ → Ω → ℝ) (u : Ω → ℝ), (∀ x, Monotone fun n => F n x) →
      (∀ n, Integrable (fun x => g x * F n x) μ ∧ ∫ x, g x * F n x ∂μ = 0) →
      (∃ C, ∀ (n : ℕ) (x : Ω), |F n x| ≤ C) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (u x))) →
      (Integrable (fun x => g x * u x) μ ∧ ∫ x, g x * u x ∂μ = 0) := by
    rintro F u _ hFP ⟨C, hC⟩ hlim
    have hlim' : ∀ x, Tendsto (fun n => g x * F n x) atTop (𝓝 (g x * u x)) :=
      fun x => (hlim x).const_mul (g x)
    have hmeas : AEStronglyMeasurable (fun x => g x * u x) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hFP n).1.aestronglyMeasurable) (Filter.Eventually.of_forall hlim')
    have hbound : ∀ (n : ℕ), ∀ᵐ x ∂μ, ‖g x * F n x‖ ≤ C * |g x| := by
      intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hC n x) (abs_nonneg _)).trans_eq (mul_comm _ _)
    have hubdd : ∀ x, |u x| ≤ C := fun x =>
      le_of_tendsto (hlim x).abs (Filter.Eventually.of_forall fun n => hC n x)
    refine ⟨Integrable.mono' (hg.abs.const_mul C) hmeas
      (Filter.Eventually.of_forall fun x => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hubdd x) (abs_nonneg _)).trans_eq (mul_comm _ _)
    · have htend : Tendsto (fun n => ∫ x, g x * F n x ∂μ) atTop (𝓝 (∫ x, g x * u x ∂μ)) :=
        tendsto_integral_of_dominated_convergence (fun x => C * |g x|)
          (fun n => (hFP n).1.aestronglyMeasurable) (hg.abs.const_mul C) hbound
          (Filter.Eventually.of_forall hlim')
      have hzero : (fun n => ∫ x, g x * F n x ∂μ) = fun _ => (0 : ℝ) :=
        funext fun n => (hFP n).2
      rw [hzero] at htend
      exact tendsto_nhds_unique htend tendsto_const_nhds
  intro f hf hfbdd
  have hres : Integrable (fun x => g x * f x) μ ∧ ∫ x, g x * f x ∂μ = 0 :=
    induction_on_mulSystem hK hKbdd hbasic hconst hadd hsmul hmono f hf hfbdd
  exact hres.2

/-- On a pseudo-metrizable space the bounded continuous real functions generate
the Borel σ-algebra.

This is what turns a criterion tested against bounded continuous functions into
one tested against every bounded Borel function, and it is where the topology of
the state space enters `induction_on_mulSystem`: the multiplicative system in
the applications is built from bounded continuous functions, and the σ-algebra
it generates has to be the Borel one for the conclusion to say anything.

One direction is that a continuous function is measurable.  The other is the
truncated distance to the complement, `fun x ↦ min 1 (Metric.infDist x Uᶜ)`,
which is bounded, continuous, and has `U` as the preimage of `Set.Ioi 0` when
`U` is open --- except for `U = univ`, where `Uᶜ = ∅` and `infDist x ∅ = 0` by
convention, so that case is taken separately.  Metrizability is used only here;
the statement is false without a topology fine enough to separate a point from a
closed set by a continuous function. -/
theorem generateFromFuns_setOf_continuous_bounded {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [m : MeasurableSpace E] [BorelSpace E] :
    generateFromFuns {f : E → ℝ | Continuous f ∧ ∃ C, ∀ x, |f x| ≤ C} = m := by
  classical
  let _ : PseudoMetricSpace E := TopologicalSpace.pseudoMetrizableSpacePseudoMetric E
  refine le_antisymm (generateFromFuns_le_iff.2 fun f hf => hf.1.measurable) ?_
  rw [BorelSpace.measurable_eq (α := E), borel]
  refine MeasurableSpace.generateFrom_le fun U hU => ?_
  rcases Set.eq_empty_or_nonempty Uᶜ with hc | hc
  · have : U = Set.univ := by
      rw [← Set.compl_empty, ← hc, compl_compl]
    rw [this]
    exact MeasurableSet.univ
  · have hcl : IsClosed Uᶜ := hU.isClosed_compl
    have hcont : Continuous fun x : E => min 1 (Metric.infDist x Uᶜ) :=
      continuous_const.min (Metric.continuous_infDist_pt Uᶜ)
    have hmem : (fun x : E => min 1 (Metric.infDist x Uᶜ))
        ∈ {f : E → ℝ | Continuous f ∧ ∃ C, ∀ x, |f x| ≤ C} := by
      refine ⟨hcont, 1, fun x => ?_⟩
      rw [abs_le]
      exact ⟨by
        have := Metric.infDist_nonneg (x := x) (s := Uᶜ)
        have : (0 : ℝ) ≤ min 1 (Metric.infDist x Uᶜ) := le_min zero_le_one this
        linarith, min_le_left _ _⟩
    have hpre : U = (fun x : E => min 1 (Metric.infDist x Uᶜ)) ⁻¹' Set.Ioi 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, lt_min_iff]
      constructor
      · intro hx
        refine ⟨zero_lt_one, ?_⟩
        have hx' : x ∉ closure Uᶜ := by rwa [hcl.closure_eq, Set.notMem_compl_iff]
        exact (Metric.infDist_pos_iff_notMem_closure hc).1 hx'
      · rintro ⟨-, hx⟩
        have hx' : x ∉ closure Uᶜ := (Metric.infDist_pos_iff_notMem_closure hc).2 hx
        rw [hcl.closure_eq, Set.notMem_compl_iff] at hx'
        exact hx'
    rw [hpre]
    exact measurable_generateFromFuns_of_mem hmem measurableSet_Ioi

/-- The `RCLike`-valued form of `integral_mul_eq_zero_of_isMulSystem`, with the
multiplicative system still **real**.

This is the shape in which the criterion is consumed: in
`MartingaleProblems.isMPSolution_iff_forall_fdd_continuous` the test functions
are real -- products of bounded continuous functions of finitely many
coordinates -- while the integrand `f (X t) - f (X s) - ∫ g (X u)` takes its
values in `𝕂`.  It is *not* the `RCLike` variant listed in the milestone, which
makes `K` itself `𝕂`-valued and has to pass through the real subalgebra of the
algebra generated by `K`; here `K` stays real and only the other factor moves,
so taking real and imaginary parts splits the statement without ever touching
the multiplicativity. -/
theorem integral_mul_ofReal_eq_zero_of_isMulSystem {mΩ : MeasurableSpace Ω}
    {𝕂 : Type*} [RCLike 𝕂] {K : Set (Ω → ℝ)} (hK : IsMulSystem K)
    (hKm : ∀ f ∈ K, Measurable f) (hKbdd : ∀ f ∈ K, ∃ C, ∀ x, |f x| ≤ C)
    (μ : Measure Ω) [IsFiniteMeasure μ] {g : Ω → 𝕂} (hg : Integrable g μ)
    (hg0 : ∫ x, g x ∂μ = 0)
    (h : ∀ f ∈ K, ∫ x, g x * (f x : 𝕂) ∂μ = 0) :
    ∀ f : Ω → ℝ, Measurable[generateFromFuns K] f → (∃ C, ∀ x, |f x| ≤ C) →
      ∫ x, g x * (f x : 𝕂) ∂μ = 0 := by
  classical
  have hle : generateFromFuns K ≤ mΩ := generateFromFuns_le_iff.2 hKm
  have hprod : ∀ u : Ω → ℝ, Measurable u → (∃ C, ∀ x, |u x| ≤ C) →
      Integrable (fun x => g x * (u x : 𝕂)) μ := by
    rintro u hu ⟨C, hC⟩
    refine Integrable.mono' (hg.norm.const_mul C)
      (hg.aestronglyMeasurable.mul
        (RCLike.continuous_ofReal.comp_aestronglyMeasurable hu.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, RCLike.norm_ofReal]
    exact (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)).trans_eq (mul_comm _ _)
  intro f hf hfbdd
  have hfm : Measurable f := hf.mono hle le_rfl
  have hfint : Integrable (fun x => g x * (f x : 𝕂)) μ := hprod f hfm hfbdd
  have hre : ∫ x, RCLike.re (g x * (f x : 𝕂)) ∂μ = 0 := by
    have hK0 : ∀ u ∈ K, ∫ x, RCLike.re (g x) * u x ∂μ = 0 := by
      intro u hu
      have hmul : ∀ x, RCLike.re (g x) * u x = RCLike.re (g x * (u x : 𝕂)) := by
        intro x; simp [RCLike.mul_re]
      simp only [hmul]
      rw [integral_re (hprod u (hKm u hu) (hKbdd u hu)), h u hu, map_zero]
    have hz : ∫ x, RCLike.re (g x) ∂μ = 0 := by rw [integral_re hg, hg0, map_zero]
    have hres := integral_mul_eq_zero_of_isMulSystem hK hKm hKbdd μ hg.re hz hK0 f hf hfbdd
    have hmul : ∀ x, RCLike.re (g x * (f x : 𝕂)) = RCLike.re (g x) * f x := by
      intro x; simp [RCLike.mul_re]
    simp only [hmul]
    exact hres
  have him : ∫ x, RCLike.im (g x * (f x : 𝕂)) ∂μ = 0 := by
    have hK0 : ∀ u ∈ K, ∫ x, RCLike.im (g x) * u x ∂μ = 0 := by
      intro u hu
      have hmul : ∀ x, RCLike.im (g x) * u x = RCLike.im (g x * (u x : 𝕂)) := by
        intro x; simp [RCLike.mul_im]
      simp only [hmul]
      rw [integral_im (hprod u (hKm u hu) (hKbdd u hu)), h u hu, map_zero]
    have hz : ∫ x, RCLike.im (g x) ∂μ = 0 := by rw [integral_im hg, hg0, map_zero]
    have hres := integral_mul_eq_zero_of_isMulSystem hK hKm hKbdd μ hg.im hz hK0 f hf hfbdd
    have hmul : ∀ x, RCLike.im (g x * (f x : 𝕂)) = RCLike.im (g x) * f x := by
      intro x; simp [RCLike.mul_im]
    simp only [hmul]
    exact hres
  refine RCLike.ext ?_ ?_
  · rw [← integral_re hfint, hre]
    simp
  · rw [← integral_im hfint, him]
    simp

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
    μ[X | generateFromFuns K] =ᵐ[μ] μ[Y | generateFromFuns K] := by
  classical
  -- Every bounded member of `K` multiplies an integrable function into an
  -- integrable one, on a finite measure.
  have hprod : ∀ (Z : Ω → ℝ), Integrable Z μ → ∀ f ∈ K,
      Integrable (fun x => Z x * f x) μ := by
    intro Z hZ f hf
    obtain ⟨C, hC⟩ := hKbdd f hf
    refine Integrable.mono' (hZ.abs.const_mul C)
      (hZ.aestronglyMeasurable.mul (hKm f hf).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hg : Integrable (fun x => X x - Y x) μ := hX.sub hY
  have hg0 : ∫ x, (X x - Y x) ∂μ = 0 := by rw [integral_sub hX hY, h1, sub_self]
  have hmul : ∀ f ∈ K, ∫ x, (X x - Y x) * f x ∂μ = 0 := by
    intro f hf
    have hsub : ∀ x, (X x - Y x) * f x = X x * f x - Y x * f x := fun x => by ring
    simp only [hsub]
    rw [integral_sub (hprod X hX f hf) (hprod Y hY f hf), h f hf, sub_self]
  have hzero := integral_mul_eq_zero_of_isMulSystem hK hKm hKbdd μ hg hg0 hmul
  -- The set form: the two conditional expectations have the same integral over
  -- every set of the generated σ-algebra.
  have hset : ∀ s : Set Ω, MeasurableSet[generateFromFuns K] s →
      ∫ x in s, Y x ∂μ = ∫ x in s, X x ∂μ := by
    intro s hs
    have hsm : MeasurableSet s := hKle s hs
    have hind : Measurable[generateFromFuns K] (Set.indicator s (1 : Ω → ℝ)) :=
      measurable_const.indicator hs
    have hbdd : ∀ x, |Set.indicator s (1 : Ω → ℝ) x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ s <;> simp [hx]
    have hz := hzero (Set.indicator s (1 : Ω → ℝ)) hind ⟨1, hbdd⟩
    have hfun : (fun x => (X x - Y x) * Set.indicator s (1 : Ω → ℝ) x)
        = Set.indicator s (fun x => X x - Y x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, integral_indicator hsm,
      integral_sub (hX.integrableOn) (hY.integrableOn), sub_eq_zero] at hz
    exact hz.symm
  have : SigmaFinite (μ.trim hKle) := inferInstance
  refine (ae_eq_condExp_of_forall_setIntegral_eq hKle hX
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp hKle hY hs]
  exact hset s hs

end MulSystem

end MeasureTheory
