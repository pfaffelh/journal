/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UrysohnsLemma

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

Since 2026-09-07, fifteenth run, **`fact:convdet` has its first half proved**,
`isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`, together
with the cutoff it runs on: `ballCutoff` with `ballCutoff_nonneg`,
`ballCutoff_le_one`, `abs_ballCutoff_le_one`, `ballCutoff_eq_one`,
`support_ballCutoff`, `lipschitzWith_ballCutoff` and `tendsto_ballCutoff`, and
the two auxiliary lemmas `lipschitzWith_mul_of_bounded` and
`integrable_of_continuous_of_bounded`.  The statement **lost its separability
hypothesis**: Ethier-Kurtz and the manuscript state Proposition 3.4.4 for
separable `S`, and no step of the proof uses a countable dense set.  The route
is Mathlib's `tendsto_iff_forall_lipschitz_integral_tendsto`, which reduces weak
convergence to the bounded Lipschitz functions, and the truncation of such a
function by a cutoff drawn from the class itself; the truncation is licensed by
the tightness the cutoffs deliver.

Since 2026-09-07, sixteenth run, **the second half is proved as well**,
`isConvergenceDetermining_setOf_hasCompactSupport`: on a locally compact
separable metric space the continuous functions of compact support are
convergence determining.  The truncation step of the first half was factored out
beforehand as `tendsto_integral_of_tendsto_integral_mul`, which takes an
arbitrary family of `[0,1]`-valued continuous cutoffs whose integrals against
the limit measure tend to `1`; both halves are that lemma with a different
family, `ballCutoff x₀ m` for the first and a compactly supported Urysohn
function over `compactCovering E m` for the second.  Nothing had to be
approximated: the naive route through uniform approximation of the larger class
by the smaller is not available, an infinite discrete space of diameter `1`
carrying the constant `1` as a uniformly continuous function of bounded support
at uniform distance `1` from every compactly supported function.

The same run also proved `StronglySeparatesPoints.exists_finite_cover`, the
geometric core of Ethier-Kurtz, Theorem 3.4.5(b), and hence the second of the
four steps that `isTightMeasureSet_of_stronglySeparatesPoints` -- the one
remaining `sorry` of Milestone 1 that is not a corollary of another -- is
composed of.  The four steps are listed in the roadmap.

Since 2026-09-07, seventeenth run, **steps (1) and (3) are proved as well**:
`tendsto_integral_comp_of_forall_tendsto_integral` with `coordMap`,
`coordAlgebra`, `separatesPoints_coordAlgebra` and
`exists_mem_subalgebra_comp_of_mem_coordAlgebra`, its portmanteau consequence
`le_liminf_measure_preimage_of_isOpen`, and
`le_liminf_measure_thickening_of_stronglySeparatesPoints`.  The index of the
finite family is an arbitrary `Fintype` rather than `Fin k`, which is what lets
step (3) index the functions of the cover by the finite set of those it
mentions, with no enumeration.  The same run also proved the harder half of
step (4), the statement about tightness alone that is missing from Mathlib:
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`, the
relaxed criterion of Ethier-Kurtz, Theorem 3.2.2 -- Mathlib's
`IsTightMeasureSet` asks for the compact set itself, and the thickening of a
compact set is compact only on a **proper** space, not on a merely complete
one, so this is not superfluous.  The witnessing set is the one Mathlib's own
proof of the Prokhorov converse builds, an intersection of shrinking
`cthickening`s of a sequence of compacts, made compact by
`TotallyBounded.isCompact_of_isClosed`.

The same run **corrected the statement** of
`isTightMeasureSet_of_stronglySeparatesPoints`: over an arbitrary `NeBot` filter
it is false, and the hypothesis it was missing is `Filter.cofinite ≤ 𝓕`.  The
witness is in its doc string.

Since 2026-09-08, first run, **Milestone 1 carries no `sorry` at all**: the
bookkeeping half of step (4) is proved, and with it
`isTightMeasureSet_of_stronglySeparatesPoints` and its corollary
`isConvergenceDetermining_of_stronglySeparatesPoints`, which is
`fact:stoneweierstrass` in the form the manuscript states it.  Both depend only
on `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`).  Their
bundle is `[MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
[BorelSpace E]` rather than `[PolishSpace E]`, the same class of spaces with the
completeness attached to the *given* metric, which is what the proof runs in;
the reason is in the doc string of the tightness theorem.  This is the one place
where the file imports `Mathlib.MeasureTheory.Measure.LevyConvergence`, for
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`.

The same run proved the content of Milestone 2,
`tendsto_of_measure_setOf_not_continuousAt_eq_zero`, the continuous mapping
result for maps continuous almost everywhere: the image measures are given
as data with their defining equations, which is what lets one statement elaborate
against both `v4.33.1` and `upstream/master`.  The packaged form
`tendsto_map_of_measure_setOf_continuousAt_eq_one` is that theorem instantiated
and keeps its `sorry` for the version reason alone.

The same run also proved the first point of Milestone 3,
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball`, which turned out to be
the relaxed tightness criterion of Milestone 1 in four lines, and weakened that
criterion's own bundle to `[PseudoMetricSpace E] [CompleteSpace E]`.

The second and third runs of 2026-09-08 proved the four statements that
`separableSpace_probabilityMeasure` rests on -- the two Lévy-Prokhorov estimates
`levyProkhorovEDist_sum_dirac_le` and `levyProkhorovEDist_sum_dirac_weights_le`
with the evaluation lemma `sum_smul_dirac_apply`, the finite partition
`exists_finite_partition_ball_of_denseRange` and the rational weights
`exists_nat_weights` -- and the fourth run put them together.
`separableSpace_levyProkhorov_probabilityMeasure`,
`separableSpace_probabilityMeasure` and
`secondCountableTopology_probabilityMeasure` are proved and depend, by
`#print axioms`, on `propext`, `Classical.choice` and `Quot.sound` alone;
the same run then proved the completeness of the Lévy-Prokhorov metric
(`isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt`,
`isTightMeasureSet_of_cauchySeq`,
`completeSpace_levyProkhorov_probabilityMeasure`,
`isCompletelyMetrizableSpace_probabilityMeasure`), so that
`polishSpace_probabilityMeasure` too rests on nothing unproved.  What is left of
Milestone 3 is the Skorokhod representation alone.

The fifth run of 2026-09-08 proved the step the Skorokhod representation rests
on, `exists_measurable_partition_diam_le_null_frontier`, together with the two
frontier statements it needed and Mathlib does not have,
`frontier_biInter_range_subset` and `frontier_disjointed_subset`; all three
depend on `propext`, `Classical.choice` and `Quot.sound` alone.  The same run
proved the second input of the representation, the Scheffé step for a countable
partition -- `tendsto_tsum_posPart_sub_of_tendsto_measure` and its total
variation form `tendsto_tsum_abs_sub_of_tendsto_measure`, with
`summable_toReal_measure_of_pairwise_disjoint` and `tsum_toReal_measure_eq_one`;
this is the one place where the file imports
`Mathlib.Analysis.Normed.Group.Tannery`.  Of Milestone 3 only
`exists_ae_tendsto_of_tendsto` itself is now unproved.

One statement is deliberately written for `upstream/master` rather than for
`v4.33.1`, and so does not elaborate here:
`tendsto_map_of_measure_setOf_continuousAt_eq_one` uses
`ProbabilityMeasure.map`, which on master takes the *function*
(`MeasureTheory/Measure/ProbabilityMeasure.lean:626`) and in `v4.33.1` takes an
`AEMeasurable` proof as well.  Master is what Tau Ceti builds on, so the
statement follows master.
-/

open Filter Topology MeasureTheory Set ENNReal
open scoped BoundedContinuousFunction NNReal

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

/-- A bounded continuous function is integrable against a finite measure. -/
lemma integrable_of_continuous_of_bounded [TopologicalSpace E] [OpensMeasurableSpace E]
    {ρ : Measure E} [IsFiniteMeasure ρ] {g : E → ℝ} {C : ℝ}
    (hg : Continuous g) (hb : ∀ x, |g x| ≤ C) : Integrable g ρ :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb x)

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

omit [MeasurableSpace E] in
/-- The geometric core of Ethier-Kurtz, Theorem 3.4.5(b), free of measures: a
strongly separating class produces, around every compact `K` and for every
`δ > 0`, a **finite** cover of `K` by basic open sets of the class which stays
inside the `δ`-thickening of `K`.

The two inclusions come from the two halves of `StronglySeparatesPoints`.  Each
centre lies in its own set, `|f x - f x| = 0 < ε x`, which makes the sets a
cover and lets compactness cut it down to a finite one.  Conversely, a point at
distance `δ` or more from the centre is separated by some member of the finite
family by at least `ε x`, so it is not in the set -- read contrapositively, the
set sits inside `Metric.ball x δ`, and the centres were chosen in `K`.

This is what the tightness step of `fact:stoneweierstrass` needs from strong
separation, and it is all it needs from it: the remaining steps only ever see
the sets `{y | ∀ f ∈ s x, |f y - f x| < ε x}` as preimages of open sets of
`ℝ^m` under `fun y ↦ (‖f y - f (x l)‖)_l`, and run on `ℝ^m`. -/
theorem StronglySeparatesPoints.exists_finite_cover [MetricSpace E] {Γ : Set (E → ℝ)}
    (hΓ : StronglySeparatesPoints Γ) (hcont : ∀ f ∈ Γ, Continuous f)
    {K : Set E} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : E → Finset (E → ℝ)) (ε : E → ℝ) (t : Set E),
      (∀ x, ↑(s x) ⊆ Γ) ∧ (∀ x, 0 < ε x) ∧ t ⊆ K ∧ t.Finite ∧
      K ⊆ ⋃ x ∈ t, {y | ∀ f ∈ s x, |f y - f x| < ε x} ∧
      (⋃ x ∈ t, {y | ∀ f ∈ s x, |f y - f x| < ε x}) ⊆ Metric.thickening δ K := by
  choose s ε hsΓ hε hsep using fun x : E => hΓ x δ hδ
  set G : E → Set E := fun x => {y | ∀ f ∈ s x, |f y - f x| < ε x} with hG
  have hGopen : ∀ x, IsOpen (G x) := by
    intro x
    have hEq : G x = ⋂ f ∈ s x, {y | |f y - f x| < ε x} := by
      ext y; simp [hG]
    rw [hEq]
    refine isOpen_biInter_finset fun f hf => ?_
    exact isOpen_lt (((hcont f (hsΓ x (Finset.mem_coe.2 hf))).sub continuous_const).abs)
      continuous_const
  have hmemG : ∀ x, x ∈ G x := by
    intro x f _
    simpa using hε x
  have hGsub : ∀ x, G x ⊆ Metric.ball x δ := by
    intro x y hy
    simp only [Metric.mem_ball]
    by_contra h
    obtain ⟨f, hf, hfle⟩ := hsep x y (not_lt.1 h)
    exact absurd (hy f hf) (not_lt.2 hfle)
  obtain ⟨t, htK, htfin, htcov⟩ := hK.elim_finite_subcover_image (b := K) (c := G)
    (fun x _ => hGopen x) (fun x hx => Set.mem_iUnion₂.2 ⟨x, hx, hmemG x⟩)
  refine ⟨s, ε, t, hsΓ, hε, htK, htfin, htcov, ?_⟩
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
  exact Metric.mem_thickening_iff.2 ⟨x, htK hx, hGsub x hyx⟩

/-! #### Step (1): the pushforwards to `κ → ℝ`

The functions the cover of step (2) mentions are finitely many members of `A`,
and everything the remaining steps do with them happens on `κ → ℝ` for a finite
`κ`, not on `E`.  Two declarations carry that passage: the convergence of the
integrals of every bounded continuous function of finitely many members, and its
portmanteau consequence for preimages of open sets. -/

/-- The `i`-th coordinate of `κ → ℝ`, as a continuous map. -/
def coordMap (κ : Type*) (i : κ) : C(κ → ℝ, ℝ) := ⟨fun y => y i, continuous_apply i⟩

/-- The subalgebra of `C(κ → ℝ, ℝ)` generated by the coordinates.  Over a finite
`κ` its members are exactly the polynomial functions, and it is what
Stone-Weierstrass is applied to on the box holding the joint range. -/
def coordAlgebra (κ : Type*) : Subalgebra ℝ C(κ → ℝ, ℝ) :=
  Algebra.adjoin ℝ (Set.range (coordMap κ))

/-- Two distinct points of `κ → ℝ` differ in a coordinate, and the coordinates
are generators. -/
lemma separatesPoints_coordAlgebra (κ : Type*) : (coordAlgebra κ).SeparatesPoints := by
  intro y z hyz
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := by
    by_contra h
    exact hyz (funext fun i => not_not.1 fun hh => h ⟨i, hh⟩)
  exact ⟨fun w => w i, ⟨coordMap κ i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, hi⟩

omit [MeasurableSpace E] in
/-- Pulling the coordinate algebra back along finitely many members of `A` lands
inside `A` again: `A` is an algebra, so it is closed under the operations the
generation of `coordAlgebra` performs, and the generators pull back to the `f i`
themselves.  The induction is `Algebra.adjoin_induction`; the constants come
from `A.smul_mem A.one_mem`, which is where `A` being an `ℝ`-subalgebra rather
than a subring is used.

No boundedness argument is needed anywhere: the conclusion produces an element
of `E →ᵇ ℝ` whose coefficient function *equals* `g ∘ (fun x i => f i x)`, so the
bound comes with it. -/
lemma exists_mem_subalgebra_comp_of_mem_coordAlgebra [TopologicalSpace E]
    {A : Subalgebra ℝ (E →ᵇ ℝ)} {κ : Type*}
    (f : κ → (E →ᵇ ℝ)) (hf : ∀ i, f i ∈ A)
    {g : C(κ → ℝ, ℝ)} (hg : g ∈ coordAlgebra κ) :
    ∃ h ∈ A, ∀ x, h x = g (fun i => f i x) := by
  induction hg using Algebra.adjoin_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact ⟨f i, hf i, fun x => rfl⟩
  | algebraMap r =>
      refine ⟨r • (1 : E →ᵇ ℝ), A.smul_mem A.one_mem r, fun x => ?_⟩
      simp
  | add p q hp hq ihp ihq =>
      obtain ⟨hp', hp'A, hp'eq⟩ := ihp
      obtain ⟨hq', hq'A, hq'eq⟩ := ihq
      exact ⟨hp' + hq', A.add_mem hp'A hq'A, fun x => by simp [hp'eq x, hq'eq x]⟩
  | mul p q hp hq ihp ihq =>
      obtain ⟨hp', hp'A, hp'eq⟩ := ihp
      obtain ⟨hq', hq'A, hq'eq⟩ := ihq
      exact ⟨hp' * hq', A.mul_mem hp'A hq'A, fun x => by simp [hp'eq x, hq'eq x]⟩

/-- Step (1) of Ethier-Kurtz, Theorem 3.4.5(b), in the form the later steps use:
if the integrals over the subalgebra `A` converge, then so do the integrals of
`F ∘ (fun x i => f i x)` for **every** bounded continuous `F` on `κ → ℝ` and
every finite family `f` from `A`.

The hypothesis only gives the polynomials in the `f i`, which is what
`exists_mem_subalgebra_comp_of_mem_coordAlgebra` extracts from `A` being an
algebra; the passage to all of `C(κ → ℝ, ℝ)` is Stone-Weierstrass on a compact
box.  The box is `Metric.closedBall 0 (∑ i, ‖f i‖)`, compact because `κ → ℝ` is
a proper space for `κ` finite (`pi_properSpace`), and it holds the joint range
because the sup-metric on `κ → ℝ` compares coordinatewise
(`dist_pi_le_iff`).  Membership of the range in the box is all that is used of
it, so no subtype of the box ever appears --- the variant of
Stone-Weierstrass with a compact set rather than a compact space
(`ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`)
is the one that fits.

The `ε / 3` split is the usual one: the two outer thirds are the approximation
error, transported to each measure by
`|∫ F ∘ Φ ∂ρ - ∫ h ∂ρ| ≤ ε / 3` for *every* probability measure `ρ`, and the
middle third is the hypothesis applied to the single member `h`. -/
theorem tendsto_integral_comp_of_forall_tendsto_integral [TopologicalSpace E]
    [OpensMeasurableSpace E] {A : Subalgebra ℝ (E →ᵇ ℝ)}
    {ι : Type*} {𝓕 : Filter ι} {μ : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, g x ∂(μ₀ : Measure E))))
    {κ : Type*} [Fintype κ] (f : κ → (E →ᵇ ℝ)) (hf : ∀ i, f i ∈ A) (F : (κ → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (fun i => f i x) ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, F (fun i => f i x) ∂(μ₀ : Measure E))) := by
  set Φ : E → (κ → ℝ) := fun x i => f i x with hΦdef
  have hΦcont : Continuous Φ := continuous_pi fun i => (f i).continuous
  set R : ℝ := ∑ i, ‖f i‖ with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hRmem : ∀ x, Φ x ∈ Metric.closedBall (0 : κ → ℝ) R := by
    intro x
    rw [Metric.mem_closedBall, dist_pi_le_iff hR0]
    intro i
    have h1 : dist (Φ x i) ((0 : κ → ℝ) i) ≤ ‖f i‖ := by
      simpa [Real.dist_eq, Φ] using (f i).norm_coe_le_norm x
    exact h1.trans (Finset.single_le_sum (f := fun j => ‖f j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i))
  have hK : IsCompact (Metric.closedBall (0 : κ → ℝ) R) := isCompact_closedBall _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgA, hgapp⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (separatesPoints_coordAlgebra κ) F.toContinuousMap hK (ε := ε / 3) (by positivity)
  obtain ⟨h, hhA, hheq⟩ := exists_mem_subalgebra_comp_of_mem_coordAlgebra f hf hgA
  have key : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ],
      |(∫ x, F (Φ x) ∂ρ) - ∫ x, h x ∂ρ| ≤ ε / 3 := by
    intro ρ _
    have hint1 : Integrable (fun x => F (Φ x)) ρ :=
      integrable_of_continuous_of_bounded (F.continuous.comp hΦcont)
        (fun x => by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (Φ x))
    have hint2 : Integrable (fun x => h x) ρ :=
      integrable_of_continuous_of_bounded h.continuous
        (fun x => by simpa [Real.norm_eq_abs] using h.norm_coe_le_norm x)
    rw [← integral_sub hint1 hint2]
    have hb : ∀ᵐ x ∂ρ, ‖F (Φ x) - h x‖ ≤ ε / 3 := by
      filter_upwards with x
      have := hgapp (Φ x) (hRmem x)
      rw [hheq x, Real.norm_eq_abs, abs_sub_comm]
      simpa using this.le
    simpa using norm_integral_le_of_norm_le_const (μ := ρ) hb
  have h3 := hμ h hhA
  rw [Metric.tendsto_nhds] at h3
  filter_upwards [h3 (ε / 3) (by positivity)] with n hn
  have b1 := abs_le.1 (key (μ n : Measure E))
  have b2 := abs_le.1 (key (μ₀ : Measure E))
  rw [Real.dist_eq, abs_lt] at hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith; linarith]

/-- The portmanteau half of step (3), separated from the geometry: step (1) says
the pushforwards of the `μ n` under `fun x i => f i x` converge weakly on
`κ → ℝ`, so the portmanteau inequality for open sets holds there, and it reads
on `E` as a statement about preimages.

`ProbabilityMeasure.map` is what turns step (1) into weak convergence
(`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` in one direction,
`integral_map` to move the integral back to `E`), and
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`
(`Measure/Portmanteau.lean:326`) is stated over an arbitrary filter, which is
why no sequence appears here. -/
theorem le_liminf_measure_preimage_of_isOpen [TopologicalSpace E] [OpensMeasurableSpace E]
    {A : Subalgebra ℝ (E →ᵇ ℝ)}
    {ι : Type*} {𝓕 : Filter ι} {μ : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, g x ∂(μ₀ : Measure E))))
    {κ : Type*} [Fintype κ] (f : κ → (E →ᵇ ℝ)) (hf : ∀ i, f i ∈ A)
    {U : Set (κ → ℝ)} (hU : IsOpen U) :
    (μ₀ : Measure E) ((fun x i => f i x) ⁻¹' U)
      ≤ 𝓕.liminf fun n => (μ n : Measure E) ((fun x i => f i x) ⁻¹' U) := by
  set Φ : E → (κ → ℝ) := fun x i => f i x with hΦdef
  have hΦcont : Continuous Φ := continuous_pi fun i => (f i).continuous
  have hΦm : Measurable Φ := hΦcont.measurable
  have hcomp : ∀ (F : (κ → ℝ) →ᵇ ℝ) (ρ : Measure E), ∫ y, F y ∂(ρ.map Φ) = ∫ x, F (Φ x) ∂ρ :=
    fun F ρ => integral_map hΦm.aemeasurable F.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun n => (μ n).map (hΦm.aemeasurable)) 𝓕
      (𝓝 (μ₀.map hΦm.aemeasurable)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    simp only [ProbabilityMeasure.toMeasure_map, hcomp]
    exact tendsto_integral_comp_of_forall_tendsto_integral hμ f hf F
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU
  simpa only [ProbabilityMeasure.toMeasure_map, Measure.map_apply hΦm hU.measurableSet]
    using hport

/-- Step (3) of Ethier-Kurtz, Theorem 3.4.5(b): the mass the limit measure gives
to a compact `K` is a lower bound for the liminf of the mass the `μ n` give to
any thickening of `K`.

Steps (1) and (2) meet here.  The cover of step (2) is a union of finitely many
sets `{y | ∀ f ∈ s x, |f y - f x| < ε x}`, and the finitely many functions all
these sets mention -- collected as one `Finset (E → ℝ)` and turned into an index
type `κ` -- exhibit the union as the preimage under `fun y i => f i y` of an
open subset of `κ → ℝ`, whereupon step (1) applies.  The two inclusions of step
(2) then bracket the preimage between `K` and `Metric.thickening δ K`.

Strong separation enters only through step (2), and the continuity of the
members of the class only through the choice of a bounded continuous
representative of each: a member of `{f | ∃ g ∈ A, ⇑g = f}` *is* a bounded
continuous function, which is where the class being drawn from a subalgebra of
`E →ᵇ ℝ` rather than from `C(E, ℝ)` is used. -/
theorem le_liminf_measure_thickening_of_stronglySeparatesPoints [MetricSpace E]
    [OpensMeasurableSpace E] {A : Subalgebra ℝ (E →ᵇ ℝ)}
    (hA : StronglySeparatesPoints {f : E → ℝ | ∃ g ∈ A, ⇑g = f})
    {ι : Type*} {𝓕 : Filter ι} {μ : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, g x ∂(μ₀ : Measure E))))
    {K : Set E} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    (μ₀ : Measure E) K ≤ 𝓕.liminf fun n => (μ n : Measure E) (Metric.thickening δ K) := by
  classical
  have hcont : ∀ f ∈ {f : E → ℝ | ∃ g ∈ A, ⇑g = f}, Continuous f := by
    rintro f ⟨g, -, rfl⟩
    exact g.continuous
  obtain ⟨s, ε, t, hsΓ, hε, htK, htfin, htcov, htthick⟩ := hA.exists_finite_cover hcont hK hδ
  -- all the functions the cover mentions, as one finite set
  set T : Finset (E → ℝ) := htfin.toFinset.biUnion s with hTdef
  have hTΓ : ∀ f ∈ T, ∃ g ∈ A, ⇑g = f := by
    intro f hf
    obtain ⟨x, -, hfx⟩ := Finset.mem_biUnion.1 hf
    exact hsΓ x (Finset.mem_coe.2 hfx)
  have hchoice : ∀ i : {f : E → ℝ // f ∈ T}, ∃ g : E →ᵇ ℝ, g ∈ A ∧ ⇑g = (i : E → ℝ) := by
    intro i
    obtain ⟨g, hgA, hgeq⟩ := hTΓ i.1 i.2
    exact ⟨g, hgA, hgeq⟩
  choose g hgA hgeq using hchoice
  have hval : ∀ (i : {f : E → ℝ // f ∈ T}) (y : E), g i y = (i : E → ℝ) y :=
    fun i y => congrFun (hgeq i) y
  -- the open subset of `({f // f ∈ T}) → ℝ` whose preimage is the cover
  set U : Set ({f : E → ℝ // f ∈ T} → ℝ) :=
    ⋃ x ∈ t, {z | ∀ i : {f : E → ℝ // f ∈ T}, (i : E → ℝ) ∈ s x → |z i - (i : E → ℝ) x| < ε x}
    with hUdef
  have hUopen : IsOpen U := by
    refine isOpen_biUnion fun x _ => ?_
    have hEq : {z : {f : E → ℝ // f ∈ T} → ℝ |
          ∀ i : {f : E → ℝ // f ∈ T}, (i : E → ℝ) ∈ s x → |z i - (i : E → ℝ) x| < ε x}
        = ⋂ i : {f : E → ℝ // f ∈ T},
          {z : {f : E → ℝ // f ∈ T} → ℝ | (i : E → ℝ) ∈ s x → |z i - (i : E → ℝ) x| < ε x} := by
      ext z; simp
    rw [hEq]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : (i : E → ℝ) ∈ s x
    · have hset : {z : {f : E → ℝ // f ∈ T} → ℝ |
            (i : E → ℝ) ∈ s x → |z i - (i : E → ℝ) x| < ε x}
          = {z : {f : E → ℝ // f ∈ T} → ℝ | |z i - (i : E → ℝ) x| < ε x} := by
        ext z; simp [hi]
      rw [hset]
      exact isOpen_lt (((continuous_apply i).sub continuous_const).abs) continuous_const
    · have hset : {z : {f : E → ℝ // f ∈ T} → ℝ |
            (i : E → ℝ) ∈ s x → |z i - (i : E → ℝ) x| < ε x} = Set.univ := by
        ext z; simp [hi]
      rw [hset]
      exact isOpen_univ
  have hpre : (fun (y : E) i => g i y) ⁻¹' U = ⋃ x ∈ t, {y | ∀ f ∈ s x, |f y - f x| < ε x} := by
    ext y
    simp only [hUdef, mem_preimage, mem_iUnion₂]
    constructor
    · rintro ⟨x, hx, hy⟩
      refine ⟨x, hx, fun f hf => ?_⟩
      have hfT : f ∈ T := Finset.mem_biUnion.2 ⟨x, htfin.mem_toFinset.2 hx, hf⟩
      simpa [hval ⟨f, hfT⟩ y] using hy ⟨f, hfT⟩ hf
    · rintro ⟨x, hx, hy⟩
      refine ⟨x, hx, fun i hi => ?_⟩
      simpa [hval i y] using hy (i : E → ℝ) hi
  calc (μ₀ : Measure E) K
      ≤ (μ₀ : Measure E) ((fun (y : E) i => g i y) ⁻¹' U) := by
        refine measure_mono ?_
        rw [hpre]
        exact htcov
    _ ≤ 𝓕.liminf fun n => (μ n : Measure E) ((fun (y : E) i => g i y) ⁻¹' U) :=
        le_liminf_measure_preimage_of_isOpen hμ g hgA hUopen
    _ ≤ 𝓕.liminf fun n => (μ n : Measure E) (Metric.thickening δ K) := by
        refine liminf_le_liminf (Eventually.of_forall fun n => measure_mono ?_)
        rw [hpre]
        exact htthick

/-- The relaxed tightness criterion, Ethier-Kurtz, Theorem 3.2.2, and missing
from Mathlib: on a complete metric space it is enough to catch the mass in a
**thickening** of a compact set, with the thickening as small as one pleases.
Mathlib's `IsTightMeasureSet` asks for the compact set itself, and that is not
what a limit argument delivers, because the thickening of a compact set is
compact only on a proper space (`IsCompact.cthickening`, and the closed unit
ball of an infinite-dimensional Banach space is the counterexample on a merely
complete one).  Separability is not a hypothesis: no step below needs a
countable dense set, only completeness.

The set that does it is the one Mathlib's own proof of the Prokhorov converse
builds (`isTightMeasureSet_of_isCompact_closure`,
`Measure/Prokhorov.lean`): pick, for a null sequence `u m ↓ 0`, compact sets
`K m` with `μ ((Metric.thickening (u m) (K m))ᶜ) ≤ ε * 2⁻¹ ^ (m + 1)` for every
`μ ∈ S`, and take `⋂ m, Metric.cthickening (u m) (K m)`.  It is closed, and
totally bounded because it sits, for every `m`, inside the `u m`-thickening of a
compact set; completeness turns that into compactness
(`TotallyBounded.isCompact_of_isClosed`), and the geometric series bounds
`μ` of its complement by `ε`.  Nothing is assumed of the measures beyond what
`IsTightMeasureSet` says, so no finiteness hypothesis appears.

The bundle is `[PseudoMetricSpace E] [CompleteSpace E]` and nothing else: the
proof measures no set it has not been handed, using only `measure_mono` and
`measure_iUnion_le`, so no `BorelSpace` or `OpensMeasurableSpace` occurs, and
the metric may be a pseudometric. -/
theorem isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le
    [PseudoMetricSpace E] [CompleteSpace E] {S : Set (Measure E)}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ K : Set E, IsCompact K ∧
      ∀ μ ∈ S, μ ((Metric.thickening δ K)ᶜ) ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hpos : ∀ m : ℕ, (0 : ℝ≥0∞) < ε * 2⁻¹ ^ (m + 1) :=
    fun m => ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by simp))
  have hupos : ∀ m : ℕ, (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := fun m => by positivity
  choose K hKcomp hKμ using fun m : ℕ => h _ (hpos m) _ (hupos m)
  refine ⟨⋂ m : ℕ, Metric.cthickening ((m : ℝ) + 1)⁻¹ (K m), ?_, ?_⟩
  · refine TotallyBounded.isCompact_of_isClosed ?_
      (isClosed_iInter fun m => Metric.isClosed_cthickening)
    rw [Metric.totallyBounded_iff]
    intro δ hδ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m : ℝ) + 1)⁻¹ < δ / 2 := by
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < δ / 2)
      exact ⟨m, by simpa [one_div] using hm⟩
    obtain ⟨t, htfin, htcov⟩ :=
      Metric.totallyBounded_iff.1 (hKcomp m).totallyBounded (δ / 2) (by positivity)
    refine ⟨t, htfin, fun y hy => ?_⟩
    have hy' : y ∈ Metric.cthickening ((m : ℝ) + 1)⁻¹ (K m) := Set.iInter_subset _ m hy
    have hy'' : y ∈ Metric.thickening (δ / 2) (K m) :=
      Metric.cthickening_subset_thickening' (by positivity) hm _ hy'
    obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.1 hy''
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (htcov hz)
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have htri : dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    simp only [Metric.mem_ball] at hzx ⊢
    linarith
  · intro μ hμS
    rw [Set.compl_iInter]
    calc μ (⋃ m : ℕ, (Metric.cthickening ((m : ℝ) + 1)⁻¹ (K m))ᶜ)
        ≤ ∑' m : ℕ, μ (Metric.cthickening ((m : ℝ) + 1)⁻¹ (K m))ᶜ := measure_iUnion_le _
      _ ≤ ∑' m : ℕ, ε * 2⁻¹ ^ (m + 1) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          refine le_trans (measure_mono ?_) (hKμ m μ hμS)
          exact Set.compl_subset_compl.2 (Metric.thickening_subset_cthickening _ _)
      _ = ε := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one,
            ENNReal.one_sub_inv_two, inv_inv]
          rw [show (2⁻¹ : ℝ≥0∞) * 2 = 1 by
            rw [ENNReal.inv_mul_cancel] <;> simp]
          rw [mul_one]

/-- Missing from Mathlib, and the whole of what `fact:stoneweierstrass` still
owes: a strongly separating subalgebra forces tightness of any family whose
integrals over it converge.  Given this,
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` supplies the rest.

That strong separation is what does the work is visible on `E = ℝ` with the
algebra generated by `arctan`, which is strongly separating: `∫ arctan ∂δ n`
converges, to `π / 2`, and no probability measure has `∫ arctan = π / 2`, so the
hypothesis below is vacuous there rather than false.

**`Filter.cofinite ≤ 𝓕` is not decoration.** Without it the statement is false,
and cheaply: take `ι = ℕ`, `𝓕 = pure 0`, `E = ℝ`, `A = ⊤` (which strongly
separates points, `fun y => min (dist y x) δ` being a bounded continuous witness
at `x` with `ε = δ`), `μ n = δ n` and `μ₀ = δ 0`.  Convergence along `pure 0` is
the single equation `∫ g ∂μ 0 = ∫ g ∂μ₀`, which holds, and it says nothing
whatever about `μ n` for `n ≥ 1`; but `{δ n | n}` is not tight, every compact
subset of `ℝ` being bounded.  The hypothesis is what makes the complement of an
`𝓕`-eventual set finite (`Filter.mem_cofinite`), which is what Ethier-Kurtz use
when they apply their Lemma 2.1 "to `P` and to finitely many terms of the
sequence".  For a sequence it is free: `Nat.cofinite_eq_atTop`.

**Why `CompleteSpace E` and not `PolishSpace E`.**  `PolishSpace` says that
*some* compatible metric is complete; the proof below runs entirely in the given
one, because `Metric.thickening` does, and
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le` turns
totally bounded into compact by completeness of that metric.  Together with
`SecondCountableTopology E` -- which is what makes a single finite measure tight,
`isTightMeasureSet_singleton` -- the two hypotheses give `PolishSpace E` back as
an instance, so no consumer pays for the change.  The statement is presumably
true under `PolishSpace E` alone, strong separation being a condition on the
neighbourhood filter and hence independent of the compatible metric chosen; the
proof of that would upgrade the metric first, and is not carried out here. -/
theorem isTightMeasureSet_of_stronglySeparatesPoints [MetricSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E]
    {ι : Type*} {𝓕 : Filter ι} [𝓕.NeBot]
    (h𝓕 : Filter.cofinite ≤ 𝓕)
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : StronglySeparatesPoints {f : E → ℝ | ∃ g ∈ A, ⇑g = f})
    {μ : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) 𝓕
      (𝓝 (∫ x, g x ∂(μ₀ : Measure E)))) :
    IsTightMeasureSet {((μ n : ProbabilityMeasure E) : Measure E) | n} := by
  classical
  refine isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le ?_
  intro ε hε δ hδ
  rcases le_or_gt 1 ε with h1 | h1
  · exact ⟨∅, isCompact_empty, by rintro ν ⟨n, rfl⟩; exact prob_le_one.trans h1⟩
  -- every single probability measure is tight, `E` being complete and second countable
  have hsingle : ∀ ρ : Measure E, IsProbabilityMeasure ρ →
      ∀ η : ℝ≥0∞, 0 < η → ∃ C : Set E, IsCompact C ∧ ρ Cᶜ ≤ η := by
    intro ρ hρ η hη
    have ht : IsTightMeasureSet {ρ} := isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
    obtain ⟨C, hC, hC'⟩ := ht η hη
    exact ⟨C, hC, hC' ρ rfl⟩
  -- a compact set carrying all but `ε / 2` of the limit measure
  obtain ⟨K₀, hK₀, hK₀μ⟩ :=
    hsingle (μ₀ : Measure E) inferInstance (ε / 2) (ENNReal.half_pos hε.ne')
  have hhalf : ε / 2 < ε := ENNReal.half_lt_self hε.ne' (ne_top_of_lt h1)
  have hK₀ge : 1 - ε / 2 ≤ (μ₀ : Measure E) K₀ := by
    have hc : (μ₀ : Measure E) K₀ᶜ = 1 - (μ₀ : Measure E) K₀ := by
      rw [measure_compl hK₀.isClosed.measurableSet (measure_ne_top _ _), measure_univ]
    rw [hc, tsub_le_iff_right] at hK₀μ
    rw [tsub_le_iff_right, add_comm]
    exact hK₀μ
  -- step (3), and the strict gap that turns a `liminf` bound into an eventual one
  have hstep3 := le_liminf_measure_thickening_of_stronglySeparatesPoints hA hμ hK₀ hδ
  have hne : (1 : ℝ≥0∞) - ε ≠ ⊤ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  have hlt : (1 : ℝ≥0∞) - ε < 1 - ε / 2 :=
    (ENNReal.cancel_of_ne hne).tsub_lt_tsub_left_of_le h1.le hhalf
  have hev : ∀ᶠ n in 𝓕, (μ n : Measure E) ((Metric.thickening δ K₀)ᶜ) ≤ ε := by
    have := Filter.eventually_lt_of_lt_liminf (hlt.trans_le (hK₀ge.trans hstep3))
    filter_upwards [this] with n hn
    rw [measure_compl Metric.isOpen_thickening.measurableSet (measure_ne_top _ _), measure_univ]
    calc 1 - (μ n : Measure E) (Metric.thickening δ K₀) ≤ 1 - (1 - ε) :=
          tsub_le_tsub_left hn.le 1
      _ = ε := ENNReal.sub_sub_cancel (by simp) h1.le
  -- the finitely many exceptional indices, absorbed by their own tightness
  set P : Set ι := {n | (μ n : Measure E) ((Metric.thickening δ K₀)ᶜ) ≤ ε} with hPdef
  have hPfin : Pᶜ.Finite := Filter.mem_cofinite.1 (h𝓕 hev)
  have hC : ∀ n : ι, ∃ C : Set E, IsCompact C ∧ (μ n : Measure E) Cᶜ ≤ ε :=
    fun n => hsingle _ inferInstance ε hε
  choose C hCcomp hCμ using hC
  refine ⟨K₀ ∪ ⋃ n ∈ Pᶜ, C n, hK₀.union (hPfin.isCompact_biUnion fun n _ => hCcomp n), ?_⟩
  rintro ν ⟨n, rfl⟩
  by_cases hn : n ∈ P
  · refine le_trans (measure_mono ?_) hn
    exact compl_subset_compl.2 (Metric.thickening_subset_of_subset δ subset_union_left)
  · refine le_trans (measure_mono ?_) (hCμ n)
    refine compl_subset_compl.2
      ((Set.subset_biUnion_of_mem (u := C) (show n ∈ Pᶜ from hn)).trans ?_)
    exact subset_union_right.trans (Metric.self_subset_thickening hδ _)

/-- `fact:stoneweierstrass`, convergence half.  From
`isTightMeasureSet_of_stronglySeparatesPoints` and
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, whose separation
hypothesis comes from `StronglySeparatesPoints.separatesPoints`.

`IsConvergenceDetermining` quantifies over sequences, so the filter hypothesis of
the tightness theorem is free here: `Nat.cofinite_eq_atTop`. -/
theorem isConvergenceDetermining_of_stronglySeparatesPoints [MetricSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E]
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : StronglySeparatesPoints {f : E → ℝ | ∃ g ∈ A, ⇑g = f}) :
    IsConvergenceDetermining {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := by
  intro μ ν hconv
  have hμ : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure E))) := fun g hg => hconv _ ⟨g, hg, rfl⟩
  have htight : IsTightMeasureSet {((μ n : ProbabilityMeasure E) : Measure E) | n} :=
    isTightMeasureSet_of_stronglySeparatesPoints (le_of_eq Nat.cofinite_eq_atTop) A hA hμ
  -- over `ℝ` the star operation is the identity, so `A` is a `StarSubalgebra` as it stands
  let A' : StarSubalgebra ℝ (E →ᵇ ℝ) :=
    { toSubalgebra := A
      star_mem' := fun {g} hg => by
        have hstar : star g = g := by ext a; simp
        rwa [hstar] }
  have hsep : (A'.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨g, hg, rfl⟩, hne⟩ := hA.separatesPoints hxy
    exact ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ g, ⟨g, hg, rfl⟩, rfl⟩, hne⟩
  exact ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℝ htight hsep hμ

/-! ### The cutoff, and the truncation it performs

`fact:convdet` needs one construction and one estimate.  The construction is a
`1`-Lipschitz cutoff which is `1` on a ball and vanishes off the ball of one
larger radius; it is a member of the class, and multiplying by it keeps a
bounded Lipschitz function inside the class.  The estimate is that the
truncation error is at most `‖f‖_∞` times the mass the cutoff misses, which is
what turns convergence along the cutoffs into a tightness statement. -/

section Cutoff

variable [PseudoMetricSpace E]

/-- The `1`-Lipschitz cutoff which is `1` on `closedBall x₀ R` and vanishes off
`closedBall x₀ (R + 1)`. -/
noncomputable def ballCutoff (x₀ : E) (R : ℝ) (x : E) : ℝ := min 1 (max 0 (R + 1 - dist x x₀))

omit [MeasurableSpace E] in
lemma ballCutoff_nonneg (x₀ : E) (R : ℝ) (x : E) : 0 ≤ ballCutoff x₀ R x :=
  le_min zero_le_one (le_max_left _ _)

omit [MeasurableSpace E] in
lemma ballCutoff_le_one (x₀ : E) (R : ℝ) (x : E) : ballCutoff x₀ R x ≤ 1 := min_le_left _ _

omit [MeasurableSpace E] in
lemma abs_ballCutoff_le_one (x₀ : E) (R : ℝ) (x : E) : |ballCutoff x₀ R x| ≤ 1 :=
  abs_le.2 ⟨by linarith [ballCutoff_nonneg x₀ R x], ballCutoff_le_one x₀ R x⟩

omit [MeasurableSpace E] in
lemma ballCutoff_eq_one {x₀ : E} {R : ℝ} {x : E} (h : dist x x₀ ≤ R) :
    ballCutoff x₀ R x = 1 := by
  unfold ballCutoff
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

omit [MeasurableSpace E] in
lemma support_ballCutoff (x₀ : E) (R : ℝ) :
    Function.support (ballCutoff x₀ R) ⊆ Metric.closedBall x₀ (R + 1) := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  simp only [Metric.mem_closedBall]
  by_contra h
  push_neg at h
  refine hx ?_
  unfold ballCutoff
  rw [max_eq_left (by linarith), min_eq_right (by norm_num)]

omit [MeasurableSpace E] in
lemma lipschitzWith_ballCutoff (x₀ : E) (R : ℝ) : LipschitzWith 1 (ballCutoff x₀ R) := by
  have h0 : LipschitzWith 1 (fun x : E => R + 1 - dist x x₀) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have h : R + 1 - dist x x₀ - (R + 1 - dist y x₀) = dist y x₀ - dist x x₀ := by ring
    rw [h]
    exact (abs_dist_sub_le y x x₀).trans_eq (dist_comm y x)
  exact (h0.const_max 0).const_min 1

omit [MeasurableSpace E] in
/-- The cutoffs of integer radius increase to `1` pointwise: each point lies in
all but finitely many of the balls. -/
lemma tendsto_ballCutoff (x₀ : E) (x : E) :
    Tendsto (fun m : ℕ => ballCutoff x₀ (m : ℝ) x) atTop (𝓝 1) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈dist x x₀⌉₊) fun m hm => ?_
  exact ballCutoff_eq_one ((Nat.le_ceil _).trans (by exact_mod_cast hm))

omit [MeasurableSpace E] in
/-- A product of two bounded Lipschitz functions is Lipschitz.  Mathlib's
`LipschitzWith.mul` is the `to_additive` companion of `LipschitzWith.add` and
concerns the group operation, so it does not apply to a product of real valued
functions; boundedness of both factors is what makes the statement true. -/
lemma lipschitzWith_mul_of_bounded {f g : E → ℝ} {Kf Kg : ℝ≥0} {Cf Cg : ℝ}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    LipschitzWith (Cf.toNNReal * Kg + Cg.toNNReal * Kf) fun x => f x * g x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hfd : |f x - f y| ≤ Kf * dist x y := by
    simpa [Real.dist_eq] using hf.dist_le_mul x y
  have hgd : |g x - g y| ≤ Kg * dist x y := by
    simpa [Real.dist_eq] using hg.dist_le_mul x y
  have hfb' : ∀ x, |f x| ≤ max Cf 0 := fun x => (hfb x).trans (le_max_left _ _)
  have hgb' : ∀ x, |g x| ≤ max Cg 0 := fun x => (hgb x).trans (le_max_left _ _)
  have h1 : |f x * g x - f y * g y| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
    calc |f x * g x - f y * g y| = |f x * (g x - g y) + (f x - f y) * g y| := by
          congr 1; ring
      _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by
          rw [abs_mul, abs_mul]; ring
  have h2 : |f x| * |g x - g y| ≤ max Cf 0 * (Kg * dist x y) :=
    mul_le_mul (hfb' x) hgd (abs_nonneg _) (le_max_right _ _)
  have h3 : |g y| * |f x - f y| ≤ max Cg 0 * (Kf * dist x y) :=
    mul_le_mul (hgb' y) hfd (abs_nonneg _) (le_max_right _ _)
  have hcoe : ((Cf.toNNReal * Kg + Cg.toNNReal * Kf : ℝ≥0) : ℝ) * dist x y
      = max Cf 0 * (Kg * dist x y) + max Cg 0 * (Kf * dist x y) := by
    push_cast [Real.coe_toNNReal']
    ring
  rw [Real.dist_eq, hcoe]
  linarith

end Cutoff

/-- The truncation step of Ethier-Kurtz, Proposition 3.4.4, isolated from the
class it is applied to.

Given a bounded continuous `f` and a sequence of cutoffs `ψ m` with values in
`[0, 1]` whose integrals against the limit measure tend to `1`, convergence of
the integrals of `ψ m` and of `f * ψ m` along the sequence forces convergence of
the integrals of `f` itself.  The point is that `ψ m` sees how much mass the
truncation loses: `|∫ f ∂ρ - ∫ f · ψ m ∂ρ| ≤ ‖f‖ · (1 - ∫ ψ m ∂ρ)` for every
probability measure `ρ`, and the hypothesis on `ψ m` transports the smallness of
that defect from `ν` to `μ n`.

Both halves of `fact:convdet` are this lemma applied to a different family of
cutoffs: `ballCutoff x₀ m` for the uniformly continuous functions of bounded
support, a compactly supported Urysohn function for `C_c`.  Nothing metric
enters, only the order and the boundedness of `ψ`. -/
theorem tendsto_integral_of_tendsto_integral_mul
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    {f : E → ℝ} {C : ℝ} {ψ : ℕ → E → ℝ}
    (hfc : Continuous f) (hCb : ∀ x, |f x| ≤ C)
    (hψc : ∀ m, Continuous (ψ m)) (hψ0 : ∀ m x, 0 ≤ ψ m x) (hψ1 : ∀ m x, ψ m x ≤ 1)
    (hψν : Tendsto (fun m => ∫ x, ψ m x ∂(ν : Measure E)) atTop (𝓝 1))
    (hψconv : ∀ m, Tendsto (fun n => ∫ x, ψ m x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, ψ m x ∂(ν : Measure E))))
    (hfψconv : ∀ m, Tendsto (fun n => ∫ x, f x * ψ m x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x * ψ m x ∂(ν : Measure E)))) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E))) := by
  set D : ℝ := max C 0 with hDdef
  have hD : ∀ x, |f x| ≤ D := fun x => (hCb x).trans (le_max_left _ _)
  have hD0 : (0:ℝ) ≤ D := le_max_right _ _
  have habsψ : ∀ m x, |ψ m x| ≤ 1 := fun m x => abs_le.2 ⟨by linarith [hψ0 m x], hψ1 m x⟩
  have hfint : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ], Integrable f ρ :=
    fun ρ _ => integrable_of_continuous_of_bounded hfc hD
  have hψint : ∀ (m : ℕ) (ρ : Measure E) [IsProbabilityMeasure ρ], Integrable (ψ m) ρ :=
    fun m ρ _ => integrable_of_continuous_of_bounded (hψc m) (habsψ m)
  have hfψint : ∀ (m : ℕ) (ρ : Measure E) [IsProbabilityMeasure ρ],
      Integrable (fun x => f x * ψ m x) ρ := by
    intro m ρ _
    refine integrable_of_continuous_of_bounded (C := D) (hfc.mul (hψc m)) fun x => ?_
    rw [abs_mul]
    calc |f x| * |ψ m x| ≤ D * 1 := mul_le_mul (hD x) (habsψ m x) (abs_nonneg _) hD0
      _ = D := mul_one D
  -- The truncation error is controlled by the mass the cutoff misses.
  have hkey : ∀ (m : ℕ) (ρ : Measure E) [IsProbabilityMeasure ρ],
      |∫ x, f x ∂ρ - ∫ x, f x * ψ m x ∂ρ| ≤ D * (1 - ∫ x, ψ m x ∂ρ) := by
    intro m ρ _
    rw [← integral_sub (hfint ρ) (hfψint m ρ)]
    calc |∫ x, (f x - f x * ψ m x) ∂ρ|
        ≤ ∫ x, |f x - f x * ψ m x| ∂ρ := abs_integral_le_integral_abs
      _ ≤ ∫ x, D * (1 - ψ m x) ∂ρ := by
          refine integral_mono ((hfint ρ).sub (hfψint m ρ)).abs
            (((integrable_const (1:ℝ)).sub (hψint m ρ)).const_mul D) fun x => ?_
          have hb : (0:ℝ) ≤ 1 - ψ m x := by linarith [hψ1 m x]
          have h1 : f x - f x * ψ m x = f x * (1 - ψ m x) := by ring
          rw [h1, abs_mul, abs_of_nonneg hb]
          exact mul_le_mul_of_nonneg_right (hD x) hb
      _ = D * (1 - ∫ x, ψ m x ∂ρ) := by
          rw [integral_const_mul, integral_sub (integrable_const (1:ℝ)) (hψint m ρ)]
          simp
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set ε' : ℝ := ε / (8 * (D + 1)) with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨m, hm⟩ := (hψν.eventually_const_lt (show (1:ℝ) - ε' < 1 by linarith)).exists
  have h1 : ∀ᶠ n in atTop, 1 - ∫ x, ψ m x ∂(μ n : Measure E) < 2 * ε' := by
    filter_upwards [(hψconv m).eventually_const_lt
      (show 1 - 2 * ε' < ∫ x, ψ m x ∂(ν : Measure E) by linarith)] with n hn
    linarith
  have h2 : ∀ᶠ n in atTop, |∫ x, f x * ψ m x ∂(μ n : Measure E) -
      ∫ x, f x * ψ m x ∂(ν : Measure E)| < ε' :=
    (Metric.tendsto_nhds.1 (hfψconv m) ε' hε').mono fun n hn => by rwa [Real.dist_eq] at hn
  filter_upwards [h1, h2] with n hn1 hn2
  rw [Real.dist_eq]
  have e1 := hkey m (μ n : Measure E)
  have e2 := hkey m (ν : Measure E)
  have habs3 : ∀ a b c d : ℝ, |a - d| ≤ |a - b| + |b - c| + |c - d| := by
    intro a b c d
    calc |a - d| = |(a - b) + (b - c) + (c - d)| := by congr 1; ring
      _ ≤ |(a - b) + (b - c)| + |c - d| := abs_add_le _ _
      _ ≤ |a - b| + |b - c| + |c - d| := by
          have := abs_add_le (a - b) (b - c); linarith
  have htri := habs3 (∫ x, f x ∂(μ n : Measure E))
    (∫ x, f x * ψ m x ∂(μ n : Measure E))
    (∫ x, f x * ψ m x ∂(ν : Measure E)) (∫ x, f x ∂(ν : Measure E))
  have e2' : |∫ x, f x * ψ m x ∂(ν : Measure E) - ∫ x, f x ∂(ν : Measure E)|
      ≤ D * (1 - ∫ x, ψ m x ∂(ν : Measure E)) := by
    rw [abs_sub_comm]; exact e2
  have b1 : D * (1 - ∫ x, ψ m x ∂(μ n : Measure E)) ≤ D * (2 * ε') :=
    mul_le_mul_of_nonneg_left hn1.le hD0
  have b2 : D * (1 - ∫ x, ψ m x ∂(ν : Measure E)) ≤ D * ε' :=
    mul_le_mul_of_nonneg_left (by linarith) hD0
  have hfin : D * (2 * ε') + ε' + D * ε' < ε := by
    have hεeq : ε' * (8 * (D + 1)) = ε := by
      rw [hε'def]; field_simp
    calc D * (2 * ε') + ε' + D * ε' = (3 * D + 1) * ε' := by ring
      _ < (8 * (D + 1)) * ε' := mul_lt_mul_of_pos_right (by linarith) hε'
      _ = ε := by rw [mul_comm]; exact hεeq
  linarith

/-- `fact:convdet` (Ethier-Kurtz, Proposition 3.4.4), first half: on a metric
space the uniformly continuous bounded functions with bounded support are
convergence determining.

**Separability is not needed**, and neither is completeness or local
compactness -- the manuscript and Ethier-Kurtz state the fact for separable `S`,
but no step below uses a countable dense set.  What carries the proof is
Mathlib's `tendsto_iff_forall_lipschitz_integral_tendsto`
(`MeasureTheory/Measure/Portmanteau.lean:688`), which reduces weak convergence
to the bounded *Lipschitz* functions, plus the truncation of such a function by
`ballCutoff`, which is `tendsto_integral_of_tendsto_integral_mul`.  The
truncation is legitimate only after the sequence is known to put almost all of
its mass in a fixed ball, and that is the tightness step: the cutoffs are
themselves members of the class, so their integrals converge, and
`tendsto_ballCutoff` with dominated convergence says the limit measure charges
the balls fully.

Nonemptiness of `E` is not a hypothesis but a consequence: `ν` is a probability
measure, so `E` cannot be empty, and the argument needs a centre for its
balls. -/
theorem isConvergenceDetermining_setOf_uniformContinuous_isBounded_support
    [MetricSpace E] [OpensMeasurableSpace E] :
    IsConvergenceDetermining {f : E → ℝ | UniformContinuous f ∧
      (∃ C, ∀ x, |f x| ≤ C) ∧ Bornology.IsBounded (Function.support f)} := by
  intro μ ν hconv
  -- The space is nonempty, since it carries a probability measure.
  have hne : Nonempty E := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : (ν : Measure E) univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨x₀⟩ := hne
  -- The cutoffs belong to the class.
  have hcut : ∀ m : ℕ, ballCutoff x₀ (m : ℝ) ∈ {f : E → ℝ | UniformContinuous f ∧
      (∃ C, ∀ x, |f x| ≤ C) ∧ Bornology.IsBounded (Function.support f)} := by
    intro m
    refine ⟨(lipschitzWith_ballCutoff x₀ (m : ℝ)).uniformContinuous,
      ⟨1, abs_ballCutoff_le_one x₀ (m : ℝ)⟩, ?_⟩
    exact (Metric.isBounded_closedBall).subset (support_ballCutoff x₀ (m : ℝ))
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hfbdd hflip
  obtain ⟨K, hK⟩ := hflip
  obtain ⟨C₀, hC₀⟩ := hfbdd
  -- A pointwise bound for `f`.
  set C : ℝ := C₀ + |f x₀| with hCdef
  have hC : ∀ x, |f x| ≤ C := by
    intro x
    have h := hC₀ x x₀
    rw [Real.dist_eq] at h
    calc |f x| = |f x - f x₀ + f x₀| := by congr 1; ring
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ C := by simp only [hCdef]; linarith
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x₀)
  -- The truncated functions belong to the class as well.
  have hfψmem : ∀ m : ℕ, (fun x => f x * ballCutoff x₀ (m : ℝ) x) ∈
      {f : E → ℝ | UniformContinuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧
        Bornology.IsBounded (Function.support f)} := by
    intro m
    refine ⟨(lipschitzWith_mul_of_bounded hK (lipschitzWith_ballCutoff x₀ (m : ℝ)) hC
      (abs_ballCutoff_le_one x₀ (m : ℝ))).uniformContinuous, ⟨C, fun x => ?_⟩, ?_⟩
    · rw [abs_mul]
      calc |f x| * |ballCutoff x₀ (m : ℝ) x| ≤ C * 1 :=
            mul_le_mul (hC x) (abs_ballCutoff_le_one _ _ _) (abs_nonneg _) hC0
        _ = C := mul_one C
    · have hsupp : Function.support (fun x => f x * ballCutoff x₀ (m : ℝ) x) ⊆
          Function.support (ballCutoff x₀ (m : ℝ)) := by
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h
        exact hx (by rw [h, mul_zero])
      exact (Metric.isBounded_closedBall).subset
        (hsupp.trans (support_ballCutoff x₀ (m : ℝ)))
  -- The cutoffs exhaust the limit measure.
  have hDCT : Tendsto (fun m : ℕ => ∫ x, ballCutoff x₀ (m : ℝ) x ∂(ν : Measure E))
      atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (ν : Measure E))
      (F := fun (m : ℕ) (x : E) => ballCutoff x₀ (m : ℝ) x) (f := fun _ : E => (1:ℝ))
      (bound := fun _ : E => (1:ℝ))
      (fun m => ((lipschitzWith_ballCutoff x₀ (m : ℝ)).continuous).aestronglyMeasurable)
      (integrable_const 1)
      (fun m => ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using abs_ballCutoff_le_one x₀ (m : ℝ) x)
      (ae_of_all _ fun x => tendsto_ballCutoff x₀ x)
    simpa using h
  exact tendsto_integral_of_tendsto_integral_mul hK.continuous hC
    (fun m => (lipschitzWith_ballCutoff x₀ (m : ℝ)).continuous)
    (fun m => ballCutoff_nonneg x₀ (m : ℝ)) (fun m => ballCutoff_le_one x₀ (m : ℝ))
    hDCT (fun m => hconv _ (hcut m)) (fun m => hconv _ (hfψmem m))

/-- `fact:convdet`, second half: on a locally compact separable metric space the
continuous functions of compact support are convergence determining.  The total
mass is not seen by them, and does not have to be: the measures are probability
measures on both sides.

The proof is the first half plus one family of cutoffs.  Separability makes the
space second countable, second countable and locally compact make it
σ-compact, and `compactCovering` is then an increasing exhaustion by compact
sets; Urysohn's lemma in its locally compact form
(`exists_continuous_one_zero_of_isCompact`,
`Topology/UrysohnsLemma.lean:404`) turns each of them into a continuous
`ψ m : E → [0,1]` of **compact** support which is `1` on `compactCovering E m`.
Every point lies in all but finitely many members of the exhaustion, so
`ψ m → 1` pointwise, and dominated convergence carries that to the integrals
against the limit measure.  Since `f · ψ m` again has compact support,
`tendsto_integral_of_tendsto_integral_mul` upgrades convergence along the
compactly supported functions to convergence along the uniformly continuous
functions of bounded support, and the first half concludes.

Local compactness enters exactly once, in Urysohn's lemma, and it is not
removable: on an infinite discrete space of diameter `1` -- locally compact, so
not a counterexample to the statement, but the place to see what the cutoffs do
-- the constant `1` is uniformly continuous with bounded support and is *not*
uniformly approximable by compactly supported functions.  A proof by uniform
approximation of the larger class by the smaller therefore cannot work; what
works is the truncation above, which only ever needs `∫ ψ m` to be close
to `1`. -/
theorem isConvergenceDetermining_setOf_hasCompactSupport
    [MetricSpace E] [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    [LocallyCompactSpace E] :
    IsConvergenceDetermining {f : E → ℝ | Continuous f ∧ HasCompactSupport f} := by
  intro μ ν hconv
  have : SigmaCompactSpace E := sigmaCompactSpace_of_locallyCompact_secondCountable
  choose ψ hψone _ hψsupp hψ01 using fun m : ℕ =>
    exists_continuous_one_zero_of_isCompact (X := E) (isCompact_compactCovering E m)
      isClosed_empty (disjoint_empty _)
  have hψ0 : ∀ m x, 0 ≤ ψ m x := fun m x => (hψ01 m x).1
  have hψ1 : ∀ m x, ψ m x ≤ 1 := fun m x => (hψ01 m x).2
  -- Each point lies in all but finitely many members of the exhaustion.
  have hptw : ∀ x, Tendsto (fun m => ψ m x) atTop (𝓝 1) := by
    intro x
    obtain ⟨n, hn⟩ := exists_mem_compactCovering x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hψone m (compactCovering_subset E hm hn)).symm
  have hmemΓ : ∀ m : ℕ, (⇑(ψ m) : E → ℝ) ∈
      {f : E → ℝ | Continuous f ∧ HasCompactSupport f} :=
    fun m => ⟨(ψ m).continuous, hψsupp m⟩
  have hψν : Tendsto (fun m => ∫ x, ψ m x ∂(ν : Measure E)) atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (ν : Measure E))
      (F := fun (m : ℕ) (x : E) => ψ m x) (f := fun _ : E => (1:ℝ))
      (bound := fun _ : E => (1:ℝ))
      (fun m => ((ψ m).continuous).aestronglyMeasurable)
      (integrable_const 1)
      (fun m => ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using abs_le.2 ⟨by linarith [hψ0 m x], hψ1 m x⟩)
      (ae_of_all _ hptw)
    simpa using h
  refine isConvergenceDetermining_setOf_uniformContinuous_isBounded_support μ ν ?_
  rintro f ⟨hfuc, ⟨C, hCb⟩, -⟩
  refine tendsto_integral_of_tendsto_integral_mul hfuc.continuous hCb
    (fun m => (ψ m).continuous) hψ0 hψ1 hψν (fun m => hconv _ (hmemΓ m)) fun m => ?_
  exact hconv _ ⟨hfuc.continuous.mul (ψ m).continuous, (hψsupp m).mul_left⟩

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

/-- The continuous mapping theorem for almost everywhere continuous maps,
`fact:cmt` (Ethier-Kurtz, Corollary 3.1.9), and the half of it Mathlib does not
have.  The image measures are taken as data with their defining equations
rather than through `ProbabilityMeasure.map`, which is the one construction
whose signature differs between `v4.33.1` and `upstream/master`; the packaged
form below is this theorem with `μ' n = (μ n).map h`, in whichever of the two
spellings the version at hand uses.

The proof is portmanteau on both sides and nothing else: for `F` closed,
`closure (h ⁻¹' F) ⊆ h ⁻¹' F ∪ {x | ¬ ContinuousAt h x}`, the second set being
`ν`-null, so `limsup (μ n) (h ⁻¹' F) ≤ ν (closure (h ⁻¹' F)) ≤ ν (h ⁻¹' F)`, and
`tendsto_of_forall_isClosed_limsup_le'` reads that back as weak convergence.
The inclusion is `ContinuousWithinAt.mem_closure_image` together with
`IsClosed.closure_subset_iff`.

Hypotheses: `E` needs `HasOuterApproxClosed`, which is what
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` asks and which every
pseudo-EMetric space has; `E'` needs no metric at all, only
`OpensMeasurableSpace`, because the converse portmanteau implication is stated
over an arbitrary topological space and a countably generated filter.
Separability of `E` is not used.

The hypothesis is the **null discontinuity set** and not
`ν {x | ContinuousAt h x} = 1`.  For a set not known to be measurable the two
are not the same statement, a set and its complement both being able to have
outer measure `1`; and this way no metric on `E'` is needed to see that the
continuity set is Borel.  Where it is wanted, Mathlib supplies the passage:
`measurableSet_of_continuousAt`
(`MeasureTheory/Constructions/BorelSpace/Basic.lean:252`, root namespace, for
`[OpensMeasurableSpace E]` and `[PseudoEMetricSpace E']`) with
`prob_compl_eq_zero_iff`. -/
theorem tendsto_of_measure_setOf_not_continuousAt_eq_zero
    [TopologicalSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    [TopologicalSpace E'] [OpensMeasurableSpace E']
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} {h : E → E'}
    (hh : Measurable h) (hconv : Tendsto μ atTop (𝓝 ν))
    (hcont : (ν : Measure E) {x | ¬ ContinuousAt h x} = 0)
    {μ' : ℕ → ProbabilityMeasure E'} {ν' : ProbabilityMeasure E'}
    (hμ' : ∀ n, (μ' n : Measure E') = (μ n : Measure E).map h)
    (hν' : (ν' : Measure E') = (ν : Measure E).map h) :
    Tendsto μ' atTop (𝓝 ν') := by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF => ?_
  have hsub : closure (h ⁻¹' F) ⊆ h ⁻¹' F ∪ {x | ¬ ContinuousAt h x} := by
    intro x hx
    by_cases hc : ContinuousAt h x
    · refine Or.inl ?_
      have hmem : h x ∈ closure (h '' (h ⁻¹' F)) := hc.continuousWithinAt.mem_closure_image hx
      have hcl : closure (h '' (h ⁻¹' F)) ⊆ F :=
        hF.closure_subset_iff.2 (image_preimage_subset h F)
      exact hcl hmem
    · exact Or.inr hc
  simp only [hμ', hν', Measure.map_apply hh hF.measurableSet]
  calc Filter.limsup (fun n => (μ n : Measure E) (h ⁻¹' F)) atTop
      ≤ Filter.limsup (fun n => (μ n : Measure E) (closure (h ⁻¹' F))) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n => measure_mono subset_closure)
    _ ≤ (ν : Measure E) (closure (h ⁻¹' F)) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv isClosed_closure
    _ ≤ (ν : Measure E) (h ⁻¹' F ∪ {x | ¬ ContinuousAt h x}) := measure_mono hsub
    _ ≤ (ν : Measure E) (h ⁻¹' F) + (ν : Measure E) {x | ¬ ContinuousAt h x} :=
        measure_union_le _ _
    _ = (ν : Measure E) (h ⁻¹' F) := by rw [hcont, add_zero]

/-- The packaged form, for `upstream/master`.  It is
`tendsto_of_measure_setOf_not_continuousAt_eq_zero` at `μ' n = (μ n).map h` and
`ν' = ν.map h`, whose defining equations are `rfl` there, with
`measurableSet_setOf_continuousAt` turning `ν {x | ContinuousAt h x} = 1` into
the null discontinuity set.  Only the spelling of `ProbabilityMeasure.map`
keeps it from elaborating against `v4.33.1`. -/
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

/-- A finite convex combination of Dirac measures, evaluated on a measurable set.

The bookkeeping lemma under the two Lévy-Prokhorov estimates below.  It is
stated with `Set.indicator` rather than with a `Finset.filter` over
`{i | y i ∈ T}` on purpose: the filter needs a `DecidablePred` instance in the
*statement*, which then has to be matched at every use site, while the
indicator carries its own case distinction. -/
theorem sum_smul_dirac_apply {n : ℕ} (w : Fin n → ℝ≥0∞) (y : Fin n → E) {T : Set E}
    (hT : MeasurableSet T) :
    (∑ i, w i • Measure.dirac (y i)) T = ∑ i, w i * T.indicator 1 (y i) := by
  simp [Measure.coe_finsetSum, Measure.dirac_apply' _ hT]

/-- **Rounding a measure onto finitely many atoms.**  If `A` is a finite
measurable partition of `E`, `G` a set of `μ`-mass at most `ε`, and each `A i`
lies within `ε` of the point `y i` off `G`, then the discrete measure
`∑ i, μ (A i) • δ (y i)` is at Lévy-Prokhorov distance at most `ε` from `μ`.

This is the geometric half of `separableSpace_probabilityMeasure`, and it is
where the separability of `E` will enter: the partition is the
disjointification of finitely many balls of radius `ε` around a dense sequence,
and `G` is what those balls fail to cover.

Both inequalities of `levyProkhorovEDist_le_of_forall` come out of the same two
observations, and neither needs `μ` to be finite.  For `μ B`: off `G` every
point of `B` lies in some `A i`, whose representative `y i` is then in the
`c`-thickening of `B`, so `B \ G` is covered by those `A i` whose weight the
discrete measure already puts inside the thickening.  For the discrete measure
of `B`: its mass on `B` is `μ (⋃ i ∈ {i | y i ∈ B}, A i)` by disjointness, and
off `G` that union lies in the thickening of `B`.  The mass of `G` is the `ε`
of the estimate on both sides. -/
theorem levyProkhorovEDist_sum_dirac_le [PseudoMetricSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} {n : ℕ} {A : Fin n → Set E} {y : Fin n → E}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : (⋃ i, A i) = univ)
    {G : Set E} {ε : ℝ≥0∞} (hεG : μ G ≤ ε)
    (hd : ∀ i, ∀ z ∈ A i \ G, dist z (y i) ≤ ε.toReal) :
    levyProkhorovEDist μ (∑ i, μ (A i) • Measure.dirac (y i)) ≤ ε := by
  classical
  refine levyProkhorovEDist_le_of_forall _ _ _ fun c B hc hc' hB => ?_
  have hεtop : ε ≠ ∞ := (hc.trans hc').ne
  have hlt : ε.toReal < c.toReal := (ENNReal.toReal_lt_toReal hεtop hc'.ne).2 hc
  have hthick : MeasurableSet (Metric.thickening c.toReal B) :=
    Metric.isOpen_thickening.measurableSet
  have heq : ∀ T : Set E, MeasurableSet T →
      (∑ i, μ (A i) • Measure.dirac (y i)) T
        = μ (⋃ i ∈ Finset.univ.filter (fun i => y i ∈ T), A i) := by
    intro T hT
    rw [sum_smul_dirac_apply _ _ hT,
      measure_biUnion_finset (fun i _ j _ hij => hdisj hij) (fun i _ => hA i), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : y i ∈ T <;> simp [h]
  constructor
  · have h1 : μ B ≤ μ (B \ G) + μ G :=
      (measure_mono (Set.subset_sdiff_union B G)).trans (measure_union_le _ _)
    have hsub : B \ G ⊆
        ⋃ i ∈ Finset.univ.filter (fun i => y i ∈ Metric.thickening c.toReal B), A i := by
      intro z hz
      obtain ⟨i, hi⟩ : ∃ i, z ∈ A i := by
        have hz' : z ∈ (⋃ i, A i) := hcover ▸ mem_univ z
        simpa using hz'
      refine Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩) hi
      refine Metric.mem_thickening_iff.2 ⟨z, hz.1, ?_⟩
      calc dist (y i) z = dist z (y i) := dist_comm _ _
        _ ≤ ε.toReal := hd i z ⟨hi, hz.2⟩
        _ < c.toReal := hlt
    rw [heq _ hthick]
    exact h1.trans (add_le_add (measure_mono hsub) (hεG.trans hc.le))
  · rw [heq _ hB]
    set U := ⋃ i ∈ Finset.univ.filter (fun i => y i ∈ B), A i with hU
    have h1 : μ U ≤ μ (U \ G) + μ G :=
      (measure_mono (Set.subset_sdiff_union U G)).trans (measure_union_le _ _)
    have hsub2 : U \ G ⊆ Metric.thickening c.toReal B := by
      rintro z ⟨hz, hzG⟩
      rw [hU] at hz
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop] at hz
      obtain ⟨i, hyi, hzi⟩ := hz
      exact Metric.mem_thickening_iff.2 ⟨y i, hyi, lt_of_le_of_lt (hd i z ⟨hzi, hzG⟩) hlt⟩
    exact h1.trans (add_le_add (measure_mono hsub2) (hεG.trans hc.le))

/-- **Perturbing the weights of finitely many atoms.**  Two discrete measures
on the same atoms are Lévy-Prokhorov close as soon as their weights differ, atom
by atom, by amounts of small total.

This is the arithmetic half of `separableSpace_probabilityMeasure`: it is what
turns the weights `μ (A i)` of `levyProkhorovEDist_sum_dirac_le`, which are
arbitrary reals, into rational ones, and so a countable family.  The
discrepancies are given as a third vector `d` rather than as `|c i - q i|`
because `ℝ≥0∞` has no subtraction worth using; `c i ≤ q i + d i` and
`q i ≤ c i + d i` say the same thing without one. -/
theorem levyProkhorovEDist_sum_dirac_weights_le [PseudoMetricSpace E] [OpensMeasurableSpace E]
    {n : ℕ} {y : Fin n → E} {c q d : Fin n → ℝ≥0∞} {δ : ℝ≥0∞}
    (hcq : ∀ i, c i ≤ q i + d i) (hqc : ∀ i, q i ≤ c i + d i) (hd : ∑ i, d i ≤ δ) :
    levyProkhorovEDist (∑ i, c i • Measure.dirac (y i))
      (∑ i, q i • Measure.dirac (y i)) ≤ δ := by
  refine levyProkhorovEDist_le_of_forall _ _ _ fun e B he he' hB => ?_
  have hthick : MeasurableSet (Metric.thickening e.toReal B) :=
    Metric.isOpen_thickening.measurableSet
  have hepos : 0 < e.toReal := ENNReal.toReal_pos (pos_of_gt he).ne' he'.ne
  have hBsub : B ⊆ Metric.thickening e.toReal B := Metric.self_subset_thickening hepos B
  have key : ∀ v w : Fin n → ℝ≥0∞, (∀ i, v i ≤ w i + d i) →
      (∑ i, v i • Measure.dirac (y i)) B
        ≤ (∑ i, w i • Measure.dirac (y i)) (Metric.thickening e.toReal B) + e := by
    intro v w hvw
    rw [sum_smul_dirac_apply _ _ hB, sum_smul_dirac_apply _ _ hthick]
    have pt : ∀ i, v i * B.indicator (1 : E → ℝ≥0∞) (y i)
        ≤ w i * (Metric.thickening e.toReal B).indicator 1 (y i) + d i := by
      intro i
      by_cases h : y i ∈ B
      · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hBsub h), Pi.one_apply, mul_one]
        exact hvw i
      · simp [h]
    calc ∑ i, v i * B.indicator 1 (y i)
        ≤ ∑ i, (w i * (Metric.thickening e.toReal B).indicator 1 (y i) + d i) :=
          Finset.sum_le_sum fun i _ => pt i
      _ = (∑ i, w i * (Metric.thickening e.toReal B).indicator 1 (y i)) + ∑ i, d i :=
          Finset.sum_add_distrib
      _ ≤ (∑ i, w i * (Metric.thickening e.toReal B).indicator 1 (y i)) + e :=
          add_le_add le_rfl (hd.trans he.le)
  exact ⟨key c q hcq, key q c hqc⟩

/-- **The finite partition into small pieces with named representatives.**  On a
metric space with a dense sequence `x`, a finite measure `μ`, a mass `ε > 0` and
a radius `r > 0`, there is a finite measurable partition `A` of `E`, a set `G`
of `μ`-mass at most `ε`, and indices `k` such that off `G` every point of `A i`
is within `r` of `x (k i)`.

This is the hypothesis of `levyProkhorovEDist_sum_dirac_le` produced, and it is
the one place in `separableSpace_probabilityMeasure` where separability of `E`
is consumed.  The representatives are returned as *indices* `k : Fin n → ℕ`
into the dense sequence, not as points: it is the indices that make the
approximating family countable.

The construction is the disjointification of the first `n` balls of radius `r`
around the sequence, `A i = ball (x i) r \ ⋃ j < i, ball (x j) r`, together with
the uncovered remainder `G = (⋃ j < n, ball (x j) r)ᶜ` as the last piece --- so
`G` is at once a piece of the partition and the exceptional set, and the
condition on it is vacuous.  The cutoff `n` exists because those unions increase
to `E` by density, so their complements decrease to `∅` and, `μ` being finite,
their masses tend to `0` (`tendsto_measure_iInter_atTop`).

Mathlib's `SeparableSpace.exists_measurable_partition_diam_le`
(`Measure/LevyProkhorovMetric.lean:540`) is the same disjointification, but
indexed by all of `ℕ` and with the representatives forgotten; neither the finite
index nor the points survive it, which is why the partition is built here. -/
theorem exists_finite_partition_ball_of_denseRange [PseudoMetricSpace E]
    [OpensMeasurableSpace E]
    {x : ℕ → E} (hx : DenseRange x) (μ : Measure E) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) {r : ℝ} (hr : 0 < r) :
    ∃ (n : ℕ) (A : Fin n → Set E) (k : Fin n → ℕ) (G : Set E),
      (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      (⋃ i, A i) = univ ∧ MeasurableSet G ∧ μ G ≤ ε ∧
      ∀ i, ∀ z ∈ A i \ G, dist z (x (k i)) ≤ r := by
  classical
  set U : ℕ → Set E := fun m => ⋃ j < m, Metric.ball (x j) r with hUdef
  have hUmeas : ∀ m, MeasurableSet (U m) := fun m =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => Metric.isOpen_ball.measurableSet
  have hUmono : Monotone U := by
    intro a b hab z hz
    simp only [hUdef, mem_iUnion, exists_prop] at hz ⊢
    obtain ⟨j, hj, hzj⟩ := hz
    exact ⟨j, hj.trans_le hab, hzj⟩
  have hUuniv : (⋃ m, U m) = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨j, hj⟩ := hx.exists_dist_lt z hr
    refine mem_iUnion.2 ⟨j + 1, ?_⟩
    simp only [hUdef, mem_iUnion, exists_prop]
    exact ⟨j, Nat.lt_succ_self j, Metric.mem_ball.2 hj⟩
  have hten : Tendsto (fun m => μ (U m)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun m => (U m)ᶜ)
      (fun m => (hUmeas m).compl.nullMeasurableSet)
      (fun a b hab => compl_subset_compl.2 (hUmono hab)) ⟨0, measure_ne_top _ _⟩
    rwa [← compl_iUnion, hUuniv, compl_univ, measure_empty] at h
  obtain ⟨n, hn⟩ : ∃ n, μ (U n)ᶜ < ε := (hten.eventually (gt_mem_nhds hε)).exists
  set A : Fin (n + 1) → Set E :=
    fun i => if h : (i : ℕ) < n then Metric.ball (x i) r \ U i else (U n)ᶜ with hAdef
  have hAsub : ∀ i : Fin (n + 1), (h : (i : ℕ) < n) → A i ⊆ Metric.ball (x i) r := by
    intro i h
    simp only [hAdef, dif_pos h]
    exact Set.sdiff_subset
  have hAdisj : ∀ i : Fin (n + 1), (h : (i : ℕ) < n) → Disjoint (A i) (U i) := by
    intro i h
    simp only [hAdef, dif_pos h]
    exact disjoint_sdiff_left
  have hball : ∀ (i : ℕ) (m : ℕ), i < m → Metric.ball (x i) r ⊆ U m := by
    intro i m him z hz
    simp only [hUdef, mem_iUnion, exists_prop]
    exact ⟨i, him, hz⟩
  refine ⟨n + 1, A, fun i => if (i : ℕ) < n then (i : ℕ) else 0, (U n)ᶜ, ?_, ?_, ?_,
    (hUmeas n).compl, hn.le, ?_⟩
  · intro i
    simp only [hAdef]
    split
    · exact Metric.isOpen_ball.measurableSet.diff (hUmeas _)
    · exact (hUmeas n).compl
  · have key : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) → Disjoint (A i) (A j) := by
      intro i j hij
      by_cases hj : (j : ℕ) < n
      · have hi : (i : ℕ) < n := hij.trans hj
        exact ((hAdisj j hj).mono_right ((hAsub i hi).trans (hball _ _ hij))).symm
      · have hi : (i : ℕ) < n := lt_of_lt_of_le hij (by omega)
        have hAj : A j = (U n)ᶜ := by simp only [hAdef, dif_neg hj]
        rw [hAj]
        exact Disjoint.mono_left ((hAsub i hi).trans (hball _ _ hi)) disjoint_compl_right
    intro i j hne
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hne (Fin.ext h)) with h | h
    · exact key i j h
    · exact (key j i h).symm
  · refine eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ U n
    · have hex : ∃ j, z ∈ Metric.ball (x j) r := by
        simp only [hUdef, mem_iUnion, exists_prop] at hz
        obtain ⟨j, _, hzj⟩ := hz
        exact ⟨j, hzj⟩
      have hlt : Nat.find hex < n := by
        simp only [hUdef, mem_iUnion, exists_prop] at hz
        obtain ⟨j, hjn, hzj⟩ := hz
        exact lt_of_le_of_lt (Nat.find_le hzj) hjn
      refine mem_iUnion.2 ⟨⟨Nat.find hex, by omega⟩, ?_⟩
      simp only [hAdef, dif_pos hlt]
      refine ⟨Nat.find_spec hex, ?_⟩
      simp only [hUdef, mem_iUnion, exists_prop, not_exists, not_and]
      exact fun l hl => Nat.find_min hex hl
    · refine mem_iUnion.2 ⟨Fin.last n, ?_⟩
      simp only [hAdef, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
      exact hz
  · intro i z hz
    by_cases h : (i : ℕ) < n
    · simp only [if_pos h]
      exact le_of_lt (Metric.mem_ball.1 (hAsub i h hz.1))
    · exact absurd hz.1 (by simp only [hAdef, dif_neg h]; exact hz.2)

/-- **Rational approximation of a finite probability vector.**  A weight vector
`c : Fin n → ℝ≥0∞` of total mass `1` is approximated, to within a total error
`δ`, by the *normalised* integer vector `m i / ∑ j, m j`.

This is what feeds `levyProkhorovEDist_sum_dirac_weights_le` and makes the
approximating family countable: after it the family is indexed by
`Σ n, (Fin n → ℕ) × (Fin n → ℕ)` --- the indices into the dense sequence and the
numerators --- rather than by arbitrary reals.

Normalising is what makes the proof short, and it is the reason the weights are
integers here rather than elements of `ℚ≥0`.  Take `m i = ⌊(c i).toReal * N⌋₊ + 1`:
then `∑ j, m j` lies between `N` and `N + n`, each `m i` between
`(c i).toReal * N` and `(c i).toReal * N + 1`, so every normalised weight is
within `(n + 1) / N` of `c i` and the total discrepancy is at most
`n (n + 1) / N`, which the choice of `N` makes at most `δ`.  Pinning the sum to
`1` instead --- rounding down and letting one exceptional index absorb the slack
--- would need truncated subtraction in `ℝ≥0∞` and a case distinction at that
index; normalising needs neither, because `∑ i, m i / ∑ j, m j = 1` holds by
construction.

The `+ 1` in the numerators is not cosmetic: it is what makes `∑ j, m j`
positive, so that the normalisation is defined even when every `c i` is small
enough for its floor to vanish. -/
theorem exists_nat_weights {n : ℕ} (c : Fin n → ℝ≥0∞) (hc : ∑ i, c i = 1)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m : Fin n → ℕ, 0 < ∑ j, m j ∧
      ∃ d : Fin n → ℝ≥0∞,
        (∀ i, c i ≤ (m i : ℝ≥0∞) / ((∑ j, m j : ℕ) : ℝ≥0∞) + d i) ∧
        (∀ i, (m i : ℝ≥0∞) / ((∑ j, m j : ℕ) : ℝ≥0∞) ≤ c i + d i) ∧
        ∑ i, d i ≤ δ := by
  classical
  set δ₀ : ℝ≥0∞ := min δ 1 with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min hδ one_pos
  have hδ₀top : δ₀ ≠ ∞ := ne_top_of_le_ne_top one_ne_top (min_le_right _ _)
  have hδ₀real : 0 < δ₀.toReal := ENNReal.toReal_pos hδ₀pos.ne' hδ₀top
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hc
    · exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hctop : ∀ i, c i ≠ ∞ := fun i => ne_top_of_le_ne_top one_ne_top
    (hc ▸ Finset.single_le_sum (f := c) (fun j _ => zero_le) (Finset.mem_univ i))
  set b : Fin n → ℝ := fun i => (c i).toReal with hbdef
  have hb0 : ∀ i, 0 ≤ b i := fun i => ENNReal.toReal_nonneg
  have hbsum : ∑ i, b i = 1 := by
    rw [hbdef, ← ENNReal.toReal_sum (fun i _ => hctop i), hc]
    simp
  have hb1 : ∀ i, b i ≤ 1 :=
    fun i => hbsum ▸ Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ i)
  obtain ⟨N, hN⟩ := exists_nat_gt (((n : ℝ) * (n + 1)) / δ₀.toReal)
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0] at hN
    have : 0 < ((n : ℝ) * (n + 1)) / δ₀.toReal := by
      apply div_pos _ hδ₀real
      have : (0 : ℝ) < n := by exact_mod_cast hn
      nlinarith
    simp at hN
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set m : Fin n → ℕ := fun i => ⌊b i * N⌋₊ + 1 with hmdef
  set M : ℕ := ∑ j, m j with hMdef
  have hMpos : 0 < M := Finset.sum_pos (fun i _ => Nat.succ_pos _) Finset.univ_nonempty
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hlow : ∀ i, b i * N ≤ (m i : ℝ) := by
    intro i
    have h := Nat.lt_floor_add_one (b i * N)
    simp only [hmdef, Nat.cast_add, Nat.cast_one]
    linarith
  have hhigh : ∀ i, (m i : ℝ) ≤ b i * N + 1 := by
    intro i
    have h : (⌊b i * N⌋₊ : ℝ) ≤ b i * N :=
      Nat.floor_le (mul_nonneg (hb0 i) (Nat.cast_nonneg N))
    simp only [hmdef, Nat.cast_add, Nat.cast_one]
    linarith
  have hMlow : (N : ℝ) ≤ M := by
    have h1 : (N : ℝ) = ∑ i, b i * N := by rw [← Finset.sum_mul, hbsum, one_mul]
    have h2 : ((M : ℕ) : ℝ) = ∑ i, ((m i : ℕ) : ℝ) := by rw [hMdef]; push_cast; ring
    rw [h1, h2]
    exact Finset.sum_le_sum fun i _ => hlow i
  have hMhigh : (M : ℝ) ≤ (N : ℝ) + n := by
    have h1 : ∑ i, (b i * N + 1) = (N : ℝ) + n := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hbsum, one_mul]
      simp
    have h2 : ((M : ℕ) : ℝ) = ∑ i, ((m i : ℕ) : ℝ) := by rw [hMdef]; push_cast; ring
    rw [h2, ← h1]
    exact Finset.sum_le_sum fun i _ => hhigh i
  set η : ℝ := ((n : ℝ) + 1) / N with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hNne : (N : ℝ) ≠ 0 := hNr.ne'
  have hηN : η * N = (n : ℝ) + 1 := by rw [hηdef, div_mul_cancel₀ _ hNne]
  have hup : ∀ i, (m i : ℝ) / M ≤ b i + η := by
    intro i
    rw [div_le_iff₀ hMr]
    have hbη : (0 : ℝ) ≤ b i + η := add_nonneg (hb0 i) hη0
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    calc (m i : ℝ) ≤ b i * N + 1 := hhigh i
      _ ≤ b i * N + η * N := by rw [hηN]; linarith
      _ = (b i + η) * N := by ring
      _ ≤ (b i + η) * M := mul_le_mul_of_nonneg_left hMlow hbη
  have hdown : ∀ i, b i ≤ (m i : ℝ) / M + η := by
    intro i
    rw [← sub_le_iff_le_add, le_div_iff₀ hMr]
    have h1 : b i * ((M : ℝ) - N) ≤ (n : ℝ) := by nlinarith [hb0 i, hb1 i, hMhigh, hMlow]
    have h2 : (n : ℝ) ≤ η * M := by nlinarith [hηN, hMlow, hη0]
    nlinarith [hlow i]
  refine ⟨m, hMpos, fun _ => ENNReal.ofReal η, ?_, ?_, ?_⟩
  · intro i
    have hw : (m i : ℝ≥0∞) / ((M : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m i : ℝ) / M) := by
      rw [ENNReal.ofReal_div_of_pos hMr]
      simp
    rw [hw, ← ENNReal.ofReal_toReal (hctop i), ← ENNReal.ofReal_add (by positivity) hη0]
    exact ENNReal.ofReal_le_ofReal (hdown i)
  · intro i
    have hw : (m i : ℝ≥0∞) / ((M : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m i : ℝ) / M) := by
      rw [ENNReal.ofReal_div_of_pos hMr]
      simp
    rw [hw, ← ENNReal.ofReal_toReal (hctop i), ← ENNReal.ofReal_add ENNReal.toReal_nonneg hη0]
    exact ENNReal.ofReal_le_ofReal (hup i)
  · have hsum : ∑ _i : Fin n, ENNReal.ofReal η = ENNReal.ofReal ((n : ℝ) * η) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    rw [hsum]
    have hle : (n : ℝ) * η ≤ δ₀.toReal := by
      rw [hηdef]
      rw [div_lt_iff₀ hδ₀real] at hN
      rw [mul_div_assoc']
      rw [div_le_iff₀ hNr]
      nlinarith [hN]
    calc ENNReal.ofReal ((n : ℝ) * η) ≤ ENNReal.ofReal δ₀.toReal :=
          ENNReal.ofReal_le_ofReal hle
      _ = δ₀ := ENNReal.ofReal_toReal hδ₀top
      _ ≤ δ := min_le_left _ _

/-- The member of the approximating family attached to a triple `(n, k, m)`: the
atoms `x (k i)` carry the normalised integer weights `m i / ∑ j, m j`.

Naming the family as a function of the triple, rather than describing it inside
the proof, is what makes its countability a one-liner: the triples form the
countable type `Σ n, (Fin n → ℕ) × (Fin n → ℕ)`, and the family is its range. -/
noncomputable def natWeightMeasure (x : ℕ → E) {n : ℕ} (k m : Fin n → ℕ) : Measure E :=
  ∑ i, ((m i : ℝ≥0∞) / ((∑ j, m j : ℕ) : ℝ≥0∞)) • Measure.dirac (x (k i))

/-- `natWeightMeasure` is a probability measure as soon as the numerators do not
all vanish -- the total mass is `(∑ j, m j) / (∑ j, m j)`, and that is where the
`+ 1` of `exists_nat_weights` earns its keep. -/
theorem isProbabilityMeasure_natWeightMeasure (x : ℕ → E) {n : ℕ} (k m : Fin n → ℕ)
    (hm : 0 < ∑ j, m j) : IsProbabilityMeasure (natWeightMeasure x k m) := by
  constructor
  have hM0 : ((∑ j, m j : ℕ) : ℝ≥0∞) ≠ 0 := by simpa using hm.ne'
  have hMtop : ((∑ j, m j : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [natWeightMeasure, sum_smul_dirac_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one, div_eq_mul_inv,
    ← Finset.sum_mul, ← Nat.cast_sum]
  rw [← div_eq_mul_inv]
  exact ENNReal.div_self hM0 hMtop

/-- The laws on a separable metric space form a separable space -- stated on the
Lévy-Prokhorov synonym, where there is a metric to estimate in.

The countable dense family is `natWeightMeasure x k m`, the measures
`∑ i, ((m i : ℝ≥0∞) / ∑ j, m j) • δ (x (k i))` with `m : Fin n → ℕ` and `x` a
dense sequence.  Countability is the image of the countable type
`Σ n, (Fin n → ℕ) × (Fin n → ℕ)`, pulled back along the injective coercion
`ProbabilityMeasure.toMeasure_injective`.

The bookkeeping is: given `μ` and `r > 0`, put `ε = ENNReal.ofReal (r / 4)` and
apply `exists_finite_partition_ball_of_denseRange` with radius `ε.toReal` to get
the partition `A`, the indices `k` and the exceptional set `G`;
`levyProkhorovEDist_sum_dirac_le` makes `∑ i, μ (A i) • δ (x (k i))` `ε`-close to
`μ`; `exists_nat_weights` applies to `c i = μ (A i)`, whose total is `1` because
`A` is a partition, and `levyProkhorovEDist_sum_dirac_weights_le` says the
normalised integer weights cost another `ε`; `levyProkhorovEDist_triangle`
(`Measure/LevyProkhorovMetric.lean:127`) gives `2ε`, that is `r / 2 < r`.

The statement is made here on `LevyProkhorov (ProbabilityMeasure E)` and not on
`ProbabilityMeasure E`, because that is where `Metric.dense_iff` applies, and
because `LevyProkhorov` is a structure with one field and *not* a type synonym:
a set of laws and its image under `LevyProkhorov.ofMeasure` are different terms,
so the density has to be carried across and cannot be reinterpreted.

The empty `E` is a separate line and not a hypothesis:
`TopologicalSpace.exists_dense_seq` (`Topology/Bases.lean:346`) asks for
`[Nonempty E]`, and over an empty `E` there is no probability measure at all
(`μ univ = 1` while `univ = ∅`), so `ProbabilityMeasure E` is empty and
countable. -/
theorem separableSpace_levyProkhorov_probabilityMeasure [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (LevyProkhorov (ProbabilityMeasure E)) := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · have hempty : IsEmpty (ProbabilityMeasure E) := by
      refine ⟨fun μ => ?_⟩
      have h : (μ : Measure E) univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h
      exact zero_ne_one h
    have : IsEmpty (LevyProkhorov (ProbabilityMeasure E)) := ⟨fun p => hempty.elim p.toMeasure⟩
    infer_instance
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq E
  set S : Set (ProbabilityMeasure E) :=
    {ν | ∃ (n : ℕ) (k m : Fin n → ℕ), (ν : Measure E) = natWeightMeasure x k m} with hSdef
  have hcount : S.Countable := by
    have hrange : (Set.range
        (fun p : Σ n : ℕ, (Fin n → ℕ) × (Fin n → ℕ) =>
          natWeightMeasure x p.2.1 p.2.2)).Countable := Set.countable_range _
    refine Set.Countable.mono ?_ (hrange.preimage ProbabilityMeasure.toMeasure_injective)
    rintro ν ⟨n, k, m, hν⟩
    exact ⟨⟨n, k, m⟩, hν.symm⟩
  have hdense : Dense (LevyProkhorov.ofMeasure '' S) := by
    rw [Metric.dense_iff]
    rintro p r hr
    set μ : ProbabilityMeasure E := p.toMeasure with hμdef
    set ε : ℝ≥0∞ := ENNReal.ofReal (r / 4) with hεdef
    have hεpos : 0 < ε := ENNReal.ofReal_pos.2 (by linarith)
    have hεtop : ε ≠ ∞ := ENNReal.ofReal_ne_top
    have hεreal : ε.toReal = r / 4 := by rw [hεdef, ENNReal.toReal_ofReal (by linarith)]
    have hεrealpos : 0 < ε.toReal := by rw [hεreal]; linarith
    obtain ⟨n, A, k, G, hA, hdisj, hcover, hGm, hG, hd⟩ :=
      exists_finite_partition_ball_of_denseRange (μ := (μ : Measure E))
        hx (ε := ε) hεpos (r := ε.toReal) hεrealpos
    have hfirst : levyProkhorovEDist (μ : Measure E)
        (∑ i, (μ : Measure E) (A i) • Measure.dirac (x (k i))) ≤ ε :=
      levyProkhorovEDist_sum_dirac_le hA hdisj hcover hG hd
    have hc : ∑ i, (μ : Measure E) (A i) = 1 := by
      rw [← measure_univ (μ := (μ : Measure E)), ← hcover, measure_iUnion hdisj hA, tsum_fintype]
    obtain ⟨m, hm, d, hcq, hqc, hdsum⟩ :=
      exists_nat_weights (fun i => (μ : Measure E) (A i)) hc (δ := ε) hεpos
    have hsecond : levyProkhorovEDist (∑ i, (μ : Measure E) (A i) • Measure.dirac (x (k i)))
        (natWeightMeasure x k m) ≤ ε :=
      levyProkhorovEDist_sum_dirac_weights_le hcq hqc hdsum
    have : IsProbabilityMeasure (natWeightMeasure x k m) :=
      isProbabilityMeasure_natWeightMeasure x k m hm
    set ν : ProbabilityMeasure E := ⟨natWeightMeasure x k m, inferInstance⟩ with hνdef
    have hνS : ν ∈ S := ⟨n, k, m, rfl⟩
    refine ⟨LevyProkhorov.ofMeasure ν, ?_, ⟨ν, hνS, rfl⟩⟩
    have htri : levyProkhorovEDist (μ : Measure E) (ν : Measure E) ≤ ε + ε :=
      (levyProkhorovEDist_triangle _ _ _).trans (add_le_add hfirst hsecond)
    have hdist : dist (LevyProkhorov.ofMeasure ν) p
        = (levyProkhorovEDist (ν : Measure E) (μ : Measure E)).toReal := rfl
    rw [Metric.mem_ball, hdist, levyProkhorovEDist_comm]
    have : (levyProkhorovEDist (μ : Measure E) (ν : Measure E)).toReal ≤ (ε + ε).toReal :=
      ENNReal.toReal_mono (by simp [hεtop]) htri
    rw [ENNReal.toReal_add hεtop hεtop, hεreal] at this
    linarith
  exact ⟨⟨LevyProkhorov.ofMeasure '' S, hcount.image _, hdense⟩⟩

/-- **The laws on a separable metric space form a separable space.**  The
statement of the milestone, carried from the Lévy-Prokhorov synonym along
`LevyProkhorov.probabilityMeasureHomeomorph` (`Measure/LevyProkhorovMetric.lean:676`)
by `DenseRange.separableSpace` (`Topology/Bases.lean:378`) -- the inverse
homeomorphism is surjective, and a surjection has dense range. -/
theorem separableSpace_probabilityMeasure [PseudoMetricSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (ProbabilityMeasure E) := by
  have := separableSpace_levyProkhorov_probabilityMeasure (E := E)
  have hhom := LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)
  exact hhom.symm.surjective.denseRange.separableSpace hhom.symm.continuous

/-- The space of laws is second countable.  This is the item above read on the
synonym, where there is a uniformity to argue with:
`UniformSpace.secondCountable_of_separable` (`Topology/UniformSpace/Cauchy.lean:932`)
asks for a uniform space with countably generated uniformity, which
`ProbabilityMeasure E` is not, and the metric synonym is; the conclusion is
topological and comes back by `Homeomorph.secondCountableTopology`
(`Topology/Homeomorph/Lemmas.lean:37`). -/
theorem secondCountableTopology_probabilityMeasure [PseudoMetricSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SeparableSpace E] :
    SecondCountableTopology (ProbabilityMeasure E) := by
  have := separableSpace_levyProkhorov_probabilityMeasure (E := E)
  have : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure E)) :=
    UniformSpace.secondCountable_of_separable _
  exact (LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).secondCountableTopology

/-- The skeleton of the proof of `isTightMeasureSet_of_isCompact_closure`, which
Mathlib inlines there: uniform total boundedness in measure already gives
tightness.  A Cauchy sequence has no compact closure to start from, so the
completeness below needs this form.  `IsTightMeasureSet`
(`MeasureTheory/Measure/Tight.lean:55`) is a predicate on `Set (Measure E)`, and
`isCompact_closure_of_isTightMeasureSet` (`Measure/Prokhorov.lean:530`) takes it
in exactly the image form written here.

It is `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`
of Milestone 1 in four lines: a finite `F` is compact, and
`Metric.thickening_eq_biUnion_ball` says that the `r`-thickening of `F` **is**
the union of the balls of radius `r` around its points, so the hypothesis is the
relaxed criterion's with `K = F`.  `SecondCountableTopology E` was among the
hypotheses and is not used by that route. -/
theorem isTightMeasureSet_of_forall_exists_finite_iUnion_ball [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [CompleteSpace E]
    {S : Set (ProbabilityMeasure E)}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∀ r : ℝ, 0 < r →
      ∃ F : Finset E, ∀ μ ∈ S, (μ : Measure E) (⋃ x ∈ F, Metric.ball x r)ᶜ ≤ ε) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := by
  refine isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le ?_
  intro ε hε δ hδ
  obtain ⟨F, hF⟩ := h ε hε δ hδ
  refine ⟨(F : Set E), F.finite_toSet.isCompact, ?_⟩
  rintro ν ⟨μ, hμS, rfl⟩
  refine le_trans (measure_mono (compl_subset_compl.2 ?_)) (hF μ hμS)
  rw [Metric.thickening_eq_biUnion_ball]
  simp

/-- **A Cauchy sequence of laws is tight.**  Stated with the Lévy-Prokhorov
distance spelled out rather than as `CauchySeq`, so that it can be read off
without an instance in sight; `isTightMeasureSet_of_cauchySeq` is the packaged
form.

The proof is the one place in Milestone 3 where the completeness of `E` is
used, and it is used twice over: once through Ulam's theorem
`isTightMeasureSet_singleton` (`Measure/Tight.lean:99`), which makes each single
law tight, and once through
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball`, which turns uniform
total boundedness in measure back into tightness.

Given `ε` and a radius `r`, put `δ = min (ε/2) (ENNReal.ofReal (r/2))` and take
`N` from the Cauchy property at `δ`.  The first `N + 1` laws are carried by the
compact `L = ⋃ n ≤ N, K n`, whose `r/2`-net `F` is the finite set asked for; off
`L` each of them has mass at most `ε/2`.  For `n > N` the Lévy-Prokhorov
inequality `right_measure_le_of_levyProkhorovEDist_lt`
(`Measure/LevyProkhorovMetric.lean:74`) sends the ball union `B` of radius `r/2`
into its `δ`-thickening, which sits inside the union `A` of the balls of radius
`r`, and `1 = (u N) B + (u N) Bᶜ ≤ ((u n) A + δ) + ε/2` gives `(u n) Aᶜ ≤ ε`.
The subtraction is avoided throughout by `measure_add_measure_compl` and
`ENNReal.add_le_add_iff_left`. -/
theorem isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt [MetricSpace E]
    [BorelSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {u : ℕ → ProbabilityMeasure E}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ N, ∀ n, N ≤ n →
      levyProkhorovEDist (u n : Measure E) (u N : Measure E) < δ) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ Set.range u} := by
  classical
  refine isTightMeasureSet_of_forall_exists_finite_iUnion_ball ?_
  intro ε hε r hr
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact ⟨∅, fun μ _ => le_top⟩
  have hεhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  set δ : ℝ≥0∞ := min (ε / 2) (ENNReal.ofReal (r / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hεhalf (ENNReal.ofReal_pos.2 (by linarith))
  have hδhalf : δ ≤ ε / 2 := min_le_left _ _
  have hδr : δ.toReal ≤ r / 2 := by
    refine (ENNReal.toReal_le_toReal ?_ ENNReal.ofReal_ne_top).2 (min_le_right _ _) |>.trans ?_
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
    · rw [ENNReal.toReal_ofReal (by linarith)]
  obtain ⟨N, hN⟩ := h δ hδpos
  -- the compact set carrying the first `N + 1` measures
  have hK : ∀ n : ℕ, ∃ K : Set E, IsCompact K ∧ (u n : Measure E) Kᶜ ≤ ε / 2 := by
    intro n
    have ht : IsTightMeasureSet {((u n : ProbabilityMeasure E) : Measure E)} :=
      isTightMeasureSet_singleton
    obtain ⟨K, hKc, hKle⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 ht (ε / 2) hεhalf
    exact ⟨K, hKc, hKle _ rfl⟩
  choose K hKc hKle using hK
  set L : Set E := ⋃ n ∈ Finset.range (N + 1), K n with hLdef
  have hLc : IsCompact L :=
    (Finset.range (N + 1)).finite_toSet.isCompact_biUnion fun n _ => hKc n
  obtain ⟨t, htfin, htsub⟩ :=
    Metric.totallyBounded_iff.1 hLc.totallyBounded (r / 2) (by linarith)
  refine ⟨htfin.toFinset, ?_⟩
  set F : Finset E := htfin.toFinset with hFdef
  set A : Set E := ⋃ x ∈ F, Metric.ball x r with hAdef
  set B : Set E := ⋃ x ∈ F, Metric.ball x (r / 2) with hBdef
  have hAmeas : MeasurableSet A :=
    Finset.measurableSet_biUnion _ fun x _ => Metric.isOpen_ball.measurableSet
  have hBmeas : MeasurableSet B :=
    Finset.measurableSet_biUnion _ fun x _ => Metric.isOpen_ball.measurableSet
  have hBA : B ⊆ A := by
    refine iUnion₂_mono fun x _ => Metric.ball_subset_ball (by linarith)
  have hLB : L ⊆ B := by
    refine htsub.trans ?_
    simp only [hBdef, hFdef, Set.Finite.mem_toFinset]
    exact subset_rfl
  have hthick : Metric.thickening δ.toReal B ⊆ A := by
    intro y hy
    obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.1 hy
    simp only [hBdef, mem_iUnion, Metric.mem_ball, exists_prop] at hz
    obtain ⟨x, hxF, hxz⟩ := hz
    simp only [hAdef, mem_iUnion, Metric.mem_ball, exists_prop]
    refine ⟨x, hxF, ?_⟩
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add_of_lt_of_lt (lt_of_lt_of_le hdz hδr) hxz
      _ = r := by ring
  -- the tail bound, `μ Aᶜ ≤ ε`, one index at a time
  rintro μ ⟨n, rfl⟩
  have hKL : ∀ m : ℕ, m ≤ N → K m ⊆ L := fun m hm =>
    subset_biUnion_of_mem (u := fun i => K i) (Finset.mem_range.2 (by omega))
  have hcompl : ∀ m : ℕ, m ≤ N → (u m : Measure E) Aᶜ ≤ ε / 2 := fun m hm =>
    le_trans (measure_mono (compl_subset_compl.2 (((hKL m hm).trans hLB).trans hBA))) (hKle m)
  rcases le_or_gt n N with hn | hn
  · exact (hcompl n hn).trans (ENNReal.half_le_self)
  · have hlp : (u N : Measure E) B ≤ (u n : Measure E) (Metric.thickening δ.toReal B) + δ :=
      right_measure_le_of_levyProkhorovEDist_lt (hN n hn.le) hBmeas
    have hlp' : (u N : Measure E) B ≤ (u n : Measure E) A + δ :=
      hlp.trans (add_le_add (measure_mono hthick) le_rfl)
    have hone : (u N : Measure E) B + (u N : Measure E) Bᶜ = 1 := by
      rw [measure_add_measure_compl hBmeas, measure_univ]
    have hNB : (u N : Measure E) Bᶜ ≤ ε / 2 :=
      le_trans (measure_mono (compl_subset_compl.2 ((hKL N le_rfl).trans hLB))) (hKle N)
    have hlow : (1 : ℝ≥0∞) ≤ (u n : Measure E) A + (δ + ε / 2) := by
      calc (1 : ℝ≥0∞) = (u N : Measure E) B + (u N : Measure E) Bᶜ := hone.symm
        _ ≤ ((u n : Measure E) A + δ) + ε / 2 := add_le_add hlp' hNB
        _ = (u n : Measure E) A + (δ + ε / 2) := by rw [add_assoc]
    have hsum : (u n : Measure E) A + (u n : Measure E) Aᶜ = 1 := by
      rw [measure_add_measure_compl hAmeas, measure_univ]
    have hAtop : (u n : Measure E) A ≠ ∞ := measure_ne_top _ _
    have : (u n : Measure E) Aᶜ ≤ δ + ε / 2 := by
      rw [← ENNReal.add_le_add_iff_left hAtop, hsum]
      exact hlow
    refine this.trans ?_
    calc δ + ε / 2 ≤ ε / 2 + ε / 2 := add_le_add hδhalf le_rfl
      _ = ε := ENNReal.add_halves ε

/-- A Cauchy sequence in the Lévy-Prokhorov metric is tight -- the previous
theorem with the hypothesis read off `EMetric.cauchySeq_iff'`, which is possible
because `edist` on `LevyProkhorov (ProbabilityMeasure E)` *is*
`levyProkhorovEDist` (`edist_probabilityMeasure_def`). -/
theorem isTightMeasureSet_of_cauchySeq [MetricSpace E] [BorelSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] {u : ℕ → LevyProkhorov (ProbabilityMeasure E)}
    (hu : CauchySeq u) :
    IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ Set.range fun n => (u n).toMeasure} := by
  refine isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt fun δ hδ => ?_
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.1 hu δ hδ
  exact ⟨N, fun n hn => hN n hn⟩

/-- **The space of laws over a complete separable metric space is complete in
the Lévy-Prokhorov metric.**  Tightness of the sequence comes from the theorem
above, `isCompact_closure_of_isTightMeasureSet` (`Measure/Prokhorov.lean:530`)
turns it into a compact closure, a compact set in the metrizable
`ProbabilityMeasure E` is sequentially compact (`IsCompact.tendsto_subseq`), and
`tendsto_nhds_of_cauchySeq_of_subseq` (`UniformSpace/Cauchy.lean:277`) upgrades
the convergent subsequence to the sequence.  The subsequence converges in the
*weak* topology and the sequence has to converge in the *metric* one, which is
what `probabilityMeasureHomeomorph` is for. -/
theorem completeSpace_levyProkhorov_probabilityMeasure [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] :
    CompleteSpace (LevyProkhorov (ProbabilityMeasure E)) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set v : ℕ → ProbabilityMeasure E := fun n => (u n).toMeasure with hv
  have hcomp : IsCompact (closure (Set.range v)) :=
    isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_of_cauchySeq hu)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq fun n => subset_closure ⟨n, rfl⟩
  refine ⟨LevyProkhorov.ofMeasure a, ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop ?_
  exact ((LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).continuous.tendsto a).comp hlim

/-- Complete metrizability of the space of laws: the item above read on the
space of laws itself, along `Homeomorph.isClosedEmbedding` and
`Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
(`Topology/Metrizable/CompletelyMetrizable.lean:249`).  This is the topological
shadow of the completeness, and it is what `polishSpace_probabilityMeasure`
consumes. -/
theorem isCompletelyMetrizableSpace_probabilityMeasure [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (ProbabilityMeasure E) := by
  have : CompleteSpace (LevyProkhorov (ProbabilityMeasure E)) :=
    completeSpace_levyProkhorov_probabilityMeasure
  exact (LevyProkhorov.probabilityMeasureHomeomorph
    (Ω := E)).isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The space of laws over a Polish space is Polish.**

`PolishSpace` is `SecondCountableTopology` together with
`IsCompletelyMetrizableSpace` (`Topology/MetricSpace/Polish.lean:62`), and
Mathlib turns a separable completely metrizable space into a Polish one
(`ibid.:65`); so this is `isCompletelyMetrizableSpace_probabilityMeasure` and
`separableSpace_probabilityMeasure` put together, and nothing else.

The statement carries **no metric on `E`**, and that is not economy but
necessity: with a `[MetricSpace E]` in the signature, the complete metric
supplied by `TopologicalSpace.upgradeIsCompletelyMetrizable`
(`Topology/Metrizable/CompletelyMetrizable.lean:205`) is a second, competing
instance, and the `CompleteSpace E` read off the upgrade is stated for the
upgraded uniformity while the goal wants the given one -- the two do not meet.
A Polish space has no distinguished metric, the upgrade provides the only one,
and both hypotheses of the two inputs are then available at once. -/
theorem polishSpace_probabilityMeasure [TopologicalSpace E] [PolishSpace E] [BorelSpace E] :
    PolishSpace (ProbabilityMeasure E) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  have hsep : TopologicalSpace.SeparableSpace (ProbabilityMeasure E) :=
    separableSpace_probabilityMeasure
  have hmetr : TopologicalSpace.IsCompletelyMetrizableSpace (ProbabilityMeasure E) :=
    isCompletelyMetrizableSpace_probabilityMeasure
  infer_instance

/-- The frontier of a finite intersection is contained in the union of the
frontiers.  Mathlib has the two-set case, `frontier_inter_subset`
(`Topology/Closure.lean:537`), but not the finite one; the induction is over
`Finset.range_add_one` (`Data/Finset/Range.lean:79`, *not* `Finset.range_succ`,
which does not exist). -/
theorem frontier_biInter_range_subset [TopologicalSpace E] (S : ℕ → Set E) (n : ℕ) :
    frontier (⋂ j ∈ Finset.range n, S j) ⊆ ⋃ j ∈ Finset.range n, frontier (S j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.set_biInter_insert]
      refine (frontier_inter_subset _ _).trans ?_
      intro x hx
      rw [Finset.set_biUnion_insert]
      rcases hx with h | h
      · exact Or.inl h.1
      · exact Or.inr (ih h.2)

/-- Disjointification keeps null frontiers null: the frontier of `disjointed S n`
is covered by the frontiers of `S 0, …, S n`.  This is the reason the fixed-radius
partition can be replaced by one whose pieces have `μ`-null frontier without any
further choice -- once the balls have null frontiers, so do the disjointified
pieces.  Uses `disjointed_eq_inter_compl` (`Order/Disjointed.lean:323`) and
`frontier_compl` (`Topology/Closure.lean:528`). -/
theorem frontier_disjointed_subset [TopologicalSpace E] (S : ℕ → Set E) (n : ℕ) :
    frontier (disjointed S n) ⊆ ⋃ j ∈ Finset.range (n + 1), frontier (S j) := by
  have hd : disjointed S n = S n ∩ ⋂ j ∈ Finset.range n, (S j)ᶜ := by
    rw [disjointed_eq_inter_compl]
    simp
  rw [hd]
  refine (frontier_inter_subset _ _).trans ?_
  intro x hx
  rw [Finset.range_add_one, Finset.set_biUnion_insert]
  rcases hx with h | h
  · exact Or.inl h.1
  · refine Or.inr ?_
    have := frontier_biInter_range_subset (fun j => (S j)ᶜ) n h.2
    simpa [frontier_compl] using this

/-- Mathlib's `SeparableSpace.exists_measurable_partition_diam_le`
(`MeasureTheory/Measure/LevyProkhorovMetric.lean:540`, in namespace
`MeasureTheory`, with `Ω` explicit) uses balls of one fixed radius and says
nothing about frontiers; the Skorokhod construction needs the radii chosen so
that the frontiers are null.  Its boundedness clause is kept here, because the
proof is the same disjointification of balls.

The proof is Mathlib's with one change: the radius is chosen **per centre**, in
`Ioo (ε/4) (ε/2)`, by `exists_null_frontier_thickening`
(`Measure/Portmanteau.lean:401`) applied to the singleton `{xs n}` and read as a
ball through `Metric.thickening_singleton`
(`Topology/MetricSpace/Thickening.lean:157`).  The lower bound `ε/4` is what
still makes the balls cover `E`, the upper bound `ε/2` is what keeps the diameter
below `ε`, and the interval has to be *open* on both sides because
`exists_null_frontier_thickening` only avoids countably many charged radii. -/
theorem exists_measurable_partition_diam_le_null_frontier [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ As : ℕ → Set E, (∀ n, MeasurableSet (As n)) ∧ (∀ n, Bornology.IsBounded (As n)) ∧
      (∀ n, Metric.diam (As n) ≤ ε) ∧ (∀ n, μ (frontier (As n)) = 0) ∧
      (⋃ n, As n = univ) ∧ Pairwise (fun n m : ℕ => Disjoint (As n) (As m)) := by
  cases isEmpty_or_nonempty E
  · refine ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ ↦ Bornology.isBounded_empty,
      fun _ ↦ by simpa only [Metric.diam_empty] using hε.le, fun _ ↦ by simp, ?_,
      fun _ _ _ ↦ disjoint_of_subsingleton⟩
    subsingleton
  obtain ⟨xs, xs_dense⟩ := TopologicalSpace.exists_dense_seq E
  have hchoice : ∀ n, ∃ r ∈ Set.Ioo (ε / 4) (ε / 2),
      μ (frontier (Metric.ball (xs n) r)) = 0 := by
    intro n
    obtain ⟨r, hr, hr0⟩ :=
      exists_null_frontier_thickening μ ({xs n} : Set E) (by linarith : ε / 4 < ε / 2)
    exact ⟨r, hr, by rwa [Metric.thickening_singleton] at hr0⟩
  choose r hr hr0 using hchoice
  set Bs : ℕ → Set E := fun n ↦ Metric.ball (xs n) (r n) with hBs
  set As := disjointed Bs with hAs
  have hrpos : ∀ n, 0 < r n := fun n ↦ lt_trans (by linarith) (hr n).1
  refine ⟨As, ?_, ?_, ?_, ?_, ?_, disjoint_disjointed Bs⟩
  · exact MeasurableSet.disjointed fun n ↦ measurableSet_ball
  · exact fun n ↦ Bornology.IsBounded.subset Metric.isBounded_ball (disjointed_subset Bs n)
  · intro n
    refine (Metric.diam_mono (disjointed_subset Bs n) Metric.isBounded_ball).trans ?_
    refine (Metric.diam_ball (hrpos n).le).trans ?_
    have := (hr n).2
    linarith
  · intro n
    refine measure_mono_null (frontier_disjointed_subset Bs n) ?_
    refine (measure_biUnion_null_iff (Finset.range (n + 1)).countable_toSet).2 ?_
    exact fun j _ ↦ hr0 j
  · rw [hAs, iUnion_disjointed]
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp xs_dense y (ε / 4) (by linarith)
    exact Set.mem_iUnion.2 ⟨n, by simpa [hBs, Metric.mem_ball, dist_comm] using hn.trans (hr n).1⟩

/-- The masses a countable measurable partition carries under a finite measure are
summable as reals.  Small, but it is the hypothesis every statement below needs
and it is where `measure_iUnion` is spent. -/
theorem summable_toReal_measure_of_pairwise_disjoint {ν : Measure E} [IsFiniteMeasure ν]
    {A : ℕ → Set E} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Function.onFun Disjoint A)) :
    Summable fun i => (ν (A i)).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [← measure_iUnion hAd hAm]
  exact measure_ne_top ν _

theorem tsum_toReal_measure_eq_one {ν : Measure E} [IsProbabilityMeasure ν] {A : ℕ → Set E}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hAu : ⋃ i, A i = univ) : ∑' i, (ν (A i)).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq fun i => measure_ne_top ν (A i), ← measure_iUnion hAd hAm, hAu]
  simp

/-- **Scheffé's step for a countable partition**: if the mass of every piece
converges, then the *positive parts* of the mass defects converge to zero
**summed over all pieces at once**.  This is the analytic content the Skorokhod
construction consumes: it is what says that the coupling built stage by stage
misplaces a total mass that tends to zero, and it does not follow from the
piecewise convergence by any finite argument.

The proof is Tannery's theorem, `tendsto_tsum_of_dominated_convergence`
(`Analysis/Normed/Group/Tannery.lean:40`), with the limit measure's own masses as
the dominating summable function -- the domination
`max (ν (A i) - μ n (A i)) 0 ≤ ν (A i)` holds because `μ n (A i) ≥ 0`, and that is
the whole reason the *positive part* and not the absolute value is the quantity
that admits an `n`-free bound. -/
theorem tendsto_tsum_posPart_sub_of_tendsto_measure {μ : ℕ → Measure E} {ν : Measure E}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν] {A : ℕ → Set E}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hconv : ∀ i, Tendsto (fun n => μ n (A i)) atTop (𝓝 (ν (A i)))) :
    Tendsto (fun n => ∑' i, max ((ν (A i)).toReal - (μ n (A i)).toReal) 0) atTop (𝓝 0) := by
  have hbound := summable_toReal_measure_of_pairwise_disjoint (ν := ν) hAm hAd
  have key : Tendsto (fun n => ∑' i, max ((ν (A i)).toReal - (μ n (A i)).toReal) 0) atTop
      (𝓝 (∑' _i : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i => (ν (A i)).toReal) hbound
      (fun i => ?_) (Eventually.of_forall fun n i => ?_)
    · have h := ((ENNReal.tendsto_toReal (measure_ne_top ν (A i))).comp (hconv i))
      have h2 := ((tendsto_const_nhds (x := (ν (A i)).toReal)).sub h).max
        (tendsto_const_nhds (x := (0 : ℝ)))
      simpa using h2
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by simp [ENNReal.toReal_nonneg]) ENNReal.toReal_nonneg
  simpa using key

/-- The same convergence for the absolute values, which is the form the coupling
consumes: the total variation distance of the two laws *read on the partition*
tends to zero.  It is not a second application of Tannery -- the absolute values
admit no `n`-free summable bound -- but follows from the positive parts and the
identity `|d| = 2 * max d 0 - d`, together with the fact that the defects sum to
`1 - 1 = 0` because both measures are probability measures.  This is where the
covering hypothesis `hAu` is spent, and it is the only place. -/
theorem tendsto_tsum_abs_sub_of_tendsto_measure {μ : ℕ → Measure E} {ν : Measure E}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν] {A : ℕ → Set E}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hAu : ⋃ i, A i = univ)
    (hconv : ∀ i, Tendsto (fun n => μ n (A i)) atTop (𝓝 (ν (A i)))) :
    Tendsto (fun n => ∑' i, |(ν (A i)).toReal - (μ n (A i)).toReal|) atTop (𝓝 0) := by
  have hpos := tendsto_tsum_posPart_sub_of_tendsto_measure hAm hAd hconv
  have hrw : ∀ n, ∑' i, |(ν (A i)).toReal - (μ n (A i)).toReal|
      = 2 * ∑' i, max ((ν (A i)).toReal - (μ n (A i)).toReal) 0 := by
    intro n
    have hsν := summable_toReal_measure_of_pairwise_disjoint (ν := ν) hAm hAd
    have hsμ := summable_toReal_measure_of_pairwise_disjoint (ν := μ n) hAm hAd
    have hd : Summable fun i => (ν (A i)).toReal - (μ n (A i)).toReal := hsν.sub hsμ
    have hmax : Summable fun i => max ((ν (A i)).toReal - (μ n (A i)).toReal) 0 :=
      hsν.of_nonneg_of_le (fun i => le_max_right _ _)
        (fun i => max_le (by simp [ENNReal.toReal_nonneg]) ENNReal.toReal_nonneg)
    have habs : ∀ i, |(ν (A i)).toReal - (μ n (A i)).toReal|
        = 2 * max ((ν (A i)).toReal - (μ n (A i)).toReal) 0
          - ((ν (A i)).toReal - (μ n (A i)).toReal) := by
      intro i
      rcases le_total ((ν (A i)).toReal - (μ n (A i)).toReal) 0 with h | h
      · rw [abs_of_nonpos h, max_eq_right h]; ring
      · rw [abs_of_nonneg h, max_eq_left h]; ring
    rw [tsum_congr habs, (hmax.mul_left 2).tsum_sub hd, tsum_mul_left,
      hsν.tsum_sub hsμ, tsum_toReal_measure_eq_one hAm hAd hAu,
      tsum_toReal_measure_eq_one hAm hAd hAu]
    ring
  simp only [hrw]
  simpa using hpos.const_mul (2 : ℝ)

/-- The discrete realisation on the unit interval: a probability vector `p` and a
sequence of points `x` are realised by a measurable map out of `(0,1]` with
Lebesgue measure, namely the one that is constant `x i` on the `i`-th interval of
the partition of `(0,1]` by the partial sums of `p`.  It is the construction step
of the Skorokhod representation, separated from the analysis: no weak convergence
enters, only the bookkeeping of `Finset.sum` over `Set.Ioc`.  The image measure is
written with `Measure.sum` rather than a `tsum`, which is Mathlib's form for a
countable superposition of measures. -/
theorem exists_measurable_map_restrict_volume_eq_sum_smul_dirac
    {p : ℕ → ℝ≥0∞} (hp : ∑' i, p i = 1) (x : ℕ → E) :
    ∃ g : ℝ → E, Measurable g ∧
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).map g
        = Measure.sum fun i => p i • Measure.dirac (x i) := sorry

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
