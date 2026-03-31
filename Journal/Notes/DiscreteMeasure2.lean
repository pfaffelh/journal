/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib

/-!
# Discrete measures

We develop a setup for discrete (probability) measures, which is an alternative to PMFs (Probability Mass Functions). Here, a `μ : DiscreteMeasure` coerces to a sum of `dirac`s with weights given by `μ.weight : α → ℝ≥0∞`.

For the coercion to `Measure`, note that `μ : DiscreteMeasure α` is not only σ-additive, but additive; see `DiscreteMeasure.m_iUnion`.

This setup combines the following features:

* We can use the `Measure`-library right from the start (as opposed to `PMF`s). (E.g., integrating wrt a discrete Measure can use linearity in the Measure, and integrating wrt `dirac`. The proofs of the usual properties between `map`, `bind` and `join` can use their counterparts in `Measure`.)
* We establish that `DiscreteMeasure α` is a `LawfulMonad`. In particular, it allows for `do`-notation.
* It will be easier to connect `DiscreteMeasure` with `Measure` (since they coerce to measures). E.g., weak convergence of `P : ℕ → DiscreteMeasure α` to some `Measure α` is easy to formulate. (For this, we have to `trim` the `P n`s to the corresponding `MeasureableSpace α` instance.)

As one example, we have started to establish some results on `coin p`, which is a Bernoulli distribution, as well as alternative formulations for the usual binomial distribution.

-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

--#37060
@[to_additive]
lemma mulSupport_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ → Set α} (f : α → β)
  (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport)))
  (i : α) (j : γ) (hj : i ∈ s j) :
    (fun d ↦ (s d).mulIndicator f i).mulSupport ⊆ {j} := by
  simp only [Pairwise, Disjoint, Set.le_eq_subset, Set.subset_inter_iff,] at hs
  simp only [Set.subset_singleton_iff, mem_mulSupport, ne_eq, Set.mulIndicator_apply_eq_one,
    Classical.not_imp, and_imp]
  intro j' hj' hi
  by_contra h
  change f i ≠ 1 at hi
  rw [← mem_mulSupport] at hi
  simp_rw [← Set.singleton_subset_iff] at hs hj hj' hi
  simpa only [Set.singleton_subset_iff] using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

@[to_additive]
lemma mulSupport_subsingleton_of_disjoint [One β] {s : γ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) (j : γ)
    (hj : i ∈ s j) : (fun d ↦ (s d).mulIndicator f i).mulSupport ⊆ {j} :=
  mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1) i j hj

--#37060
@[to_additive]
lemma tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α)
    (i : β) (hi : i ∈ ⋃ d, s d) (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) :
    ∏' d, (s d).mulIndicator f i = f i := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]
lemma tprod_mulIndicator_of_mem_union_disjoint [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α) (hs : Pairwise (Disjoint on s))
    (i : β) (hi : i ∈ ⋃ d, s d) : ∏' d, (s d).mulIndicator f i = f i :=
  tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem  s f i hi (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1)

@[to_additive]
lemma tprod_mulIndicator_of_notMem [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α) (i : β) (hi : ∀ d, i ∉ s d) :
    ∏' d, (s d).mulIndicator f i = 1 := by
  aesop

@[to_additive]
lemma mulIndicator_iUnion_of_disjoint_on_mulSupport [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α)
    (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) (i : β) :
    (⋃ d, s d).mulIndicator f i = ∏' d, (s d).mulIndicator f i := by
  by_cases h₀ : i ∈ ⋃ d, s d
  · simp only [h₀, Set.mulIndicator_of_mem]
    apply Eq.symm <| tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem  _ _ _ h₀ hs
  · aesop

@[to_additive]
lemma mulIndicator_iUnion_of_pairwise_disjoint [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (hs : Pairwise (Disjoint on s)) (f : β → α) :
    (⋃ d, s d).mulIndicator f = fun i ↦ ∏' d, (s d).mulIndicator f i := by
  ext i
  exact mulIndicator_iUnion_of_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1) i

-- Set.indicator

-- #34138
@[simp]
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

-- #34138
lemma Set.PairwiseDisjoint.singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  apply pairwise_disjoint_fiber id
  exact Subtype.coe_ne_coe.mpr hab

-- #34138
lemma Set.PairwiseDisjoint.fiber_subtype {g : α → β} (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)


-- start `DiscreteMeasure` here.
universe u v w

variable {α β γ δ : Type*}

structure DiscreteMeasure (α : Type*) : Type _ where
  weight : α → ℝ≥0∞

namespace MeasureTheory

/-- The `Measure α` as defined through a `DiscreteMeasure α` (mass function) through a weighted sum
of diracs, using a given `MeasurableSpace α`. -/
noncomputable def DiscreteMeasure.toMeasure [MeasurableSpace α] (μ : DiscreteMeasure α) : Measure α :=
  Measure.sum (fun x ↦ μ.weight x • .dirac x)

noncomputable instance [MeasurableSpace α] : Coe (DiscreteMeasure α) (Measure α) where
  coe μ := μ.toMeasure

instance instFunLike : FunLike (DiscreteMeasure α) α ℝ≥0∞ where
  coe p a := p.weight a
  coe_injective' p q h := by
    cases p
    cases q
    simp_all

namespace DiscreteMeasure

@[simp]
lemma weight_eq (μ : DiscreteMeasure α) (x : α) : μ.weight x = μ x := by rfl

-- #34138
@[ext]
protected theorem ext {v w : DiscreteMeasure α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

-- #34138
@[simp]
theorem mem_support_iff (w : DiscreteMeasure α) (a : α) : a ∈ w.weight.support ↔ w a ≠ 0 := Iff.rfl

-- #34138
theorem apply_eq_zero_iff (w : DiscreteMeasure α) (a : α) : w a = 0 ↔ a ∉ w.weight.support := by
  rw [mem_support_iff, Classical.not_not]

-- #34138
theorem apply_pos_iff (w : DiscreteMeasure α) (a : α) : 0 < w a ↔ a ∈ w.weight.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

-- #34138
lemma toMeasure_apply' [MeasurableSpace α] (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (a : α), (μ.weight a) • dirac a s := by
  rw [toMeasure, sum_apply (hs := hs)]
  simp_rw [smul_apply]

-- #34138
lemma toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s):
    μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  rw [μ.toMeasure_apply' hs]
  simp

-- #34138
lemma toMeasure_apply₁ [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s):
    μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [μ.toMeasure_apply hs]

-- #34138
lemma toMeasure_apply₂ [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [μ.toMeasure_apply hs, tsum_subtype]

-- #34138
@[simp]
lemma toMeasure_apply_singleton [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) (a : α) : μ.toMeasure {a} = μ a := by
  simp only [μ.toMeasure_apply (measurableSet_singleton a), Set.indicator.mul_indicator_eq, ← tsum_subtype,tsum_singleton]

-- #34138
theorem toMeasure_apply_eq_zero_iff [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} {s : Set α} (hs : MeasurableSet s):
    μ.toMeasure s = 0 ↔ Disjoint μ.weight.support s := by
  rw [toMeasure_apply₁ (hs := hs), ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

-- #34138
@[simp]
theorem toMeasure_apply_inter_support [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} {s u : Set α} (hs : MeasurableSet s) (hu : MeasurableSet u) (h : μ.weight.support ⊆ u) :
    μ.toMeasure (s ∩ u) = μ.toMeasure s := by
  simp only [toMeasure_apply (hs := hs), toMeasure_apply (hs := MeasurableSet.inter hs hu)]
  apply tsum_congr (fun a ↦ ?_)
  repeat rw [Set.indicator.mul_indicator_eq, Set.indicator]
  simp only [support_subset_iff, weight_eq, ne_eq] at h
  specialize h a
  aesop

-- #34138
theorem toMeasure_apply_eq_of_inter_support_eq [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) (h_support : μ.weight.support ⊆ u)
    (h : s ∩ u = t ∩ u) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support hs hu h_support, ← toMeasure_apply_inter_support ht hu h_support, h]

-- #34138
/- Additivity for `μ.toMeasure` for a `μ : DiscreteMeasure` not only applies to countable unions, but
to arbitrary ones. -/
lemma toMeasure_additive [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) {s : δ → Set α} (h₀ : ∀ d, MeasurableSet (s d)) (h₁ : MeasurableSet (⋃ d, s d)) (hs : Pairwise (Disjoint on s)) :
    μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply (hs := h₁), Set.indicator.mul_indicator_eq]
  conv => right; left; intro d; rw [toMeasure_apply (hs := h₀ _)]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  apply tsum_congr <| fun b ↦ by rw [indicator_iUnion_of_pairwise_disjoint s hs μ]

-- #34138
theorem toMeasure_apply_finset [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} (s : Finset α) : μ.toMeasure s = ∑ x ∈ s, μ x
    := by
  rw [toMeasure_apply₁ (hs := by measurability), tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

-- #34138
@[simp]
theorem toMeasure_apply_fintype [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} (s : Set α) [Fintype α] :
    μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [μ.toMeasure_apply₁ (by measurability)]
  exact tsum_fintype (s.indicator μ)

-- #34138
lemma toMeasure_apply_univ [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

-- #34138
lemma toMeasure_apply_univ' [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) {s : δ → Set α} (h : ∀ d, MeasurableSet (s d)) (hs₀ : Pairwise (Disjoint on s))
    (hs₁ : Set.univ = ⋃ d, s d) : μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ h (Eq.symm hs₁ ▸ MeasurableSet.univ) hs₀

-- #34138
theorem toMeasure_injective [MeasurableSpace α] [MeasurableSingletonClass α] : (@toMeasure α _).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton μ, ← toMeasure_apply_singleton ν, h]

-- #34138
@[simp]
theorem toMeasure_inj [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α} : μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

-- #34138
theorem toMeasure_ext [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α} (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_inj.mp h

-- #34138
theorem toMeasure_mono [MeasurableSpace α] [MeasurableSingletonClass α] {s t u : Set α} (hs : MeasurableSet s) (hu : MeasurableSet u) {μ : DiscreteMeasure α} (h : s ∩ u ⊆ t) (h_support : μ.weight.support ⊆ u) :
    μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support hs hu h_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

-- #34138
@[simp]
theorem restrict_toMeasure_support [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} {u : Set α} (hu : MeasurableSet u) (h : μ.weight.support ⊆ u):
    μ.toMeasure.restrict u = μ.toMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support hs hu h]

lemma nsupport_weight [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) (P : α → Prop) (hμ : μ.toMeasure {a : α | P a} = 0) (a : α) (ha : P a) : μ a = 0 :=
  by
  rw [← nonpos_iff_eq_zero, ← DiscreteMeasure.toMeasure_apply_singleton μ a, ← hμ]
  apply OuterMeasureClass.measure_mono μ.toMeasure
  simp [ha]

section IsFiniteOrProbabilityMeasure

lemma isProbabilityMeasure_iff_hasSum [MeasurableSpace α] [MeasurableSingletonClass α] {p : DiscreteMeasure α} :
    IsProbabilityMeasure p.toMeasure ↔ HasSum p 1 := by
  rw [isProbabilityMeasure_iff, DiscreteMeasure.toMeasure_apply_univ, Summable.hasSum_iff ENNReal.summable]

lemma isProbabilityMeasure_iff_tsumOne [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} : IsProbabilityMeasure μ.toMeasure ↔ ∑' a, μ a = 1 := by
  rw [isProbabilityMeasure_iff_hasSum, Summable.hasSum_iff ENNReal.summable]

lemma isFiniteMeasure_iff_tsum_ne_top [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} : IsFiniteMeasure μ.toMeasure ↔ ∑' a, μ a ≠ ⊤ := by
  rw [isFiniteMeasure_iff, DiscreteMeasure.toMeasure_apply_univ, lt_top_iff_ne_top]

theorem toMeasure_ne_top_of_isFiniteMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s ≠ ∞ := measure_ne_top p.toMeasure s

theorem toMeasure_le_top_of_isFiniteMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s < ∞ := by
  exact measure_lt_top p.toMeasure s

theorem coe_ne_zero [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsProbabilityMeasure p.toMeasure): p.weight ≠ (fun _ ↦ 0) := by
  by_contra h'
  rw [isProbabilityMeasure_iff] at h
  have g : p.toMeasure Set.univ = 0 := by
    rw [DiscreteMeasure.toMeasure_apply_univ]
    simp_rw [← weight_eq, h']
    simp only [tsum_zero]
  apply zero_ne_one' ℝ≥0∞
  rw [← g, ← h]

@[simp]
theorem support_nonempty [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsProbabilityMeasure p.toMeasure): p.weight.support.Nonempty := by
  apply Function.support_nonempty_iff.2 (coe_ne_zero p h)

@[simp]
theorem support_countable [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure): p.weight.support.Countable :=
  Summable.countable_support_ennreal <| isFiniteMeasure_iff_tsum_ne_top.mp h

theorem toMeasure_apply_eq_toMeasure_univ_iff [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) (ha : p.toMeasure s ≠ ⊤) : p.toMeasure s = p.toMeasure Set.univ ↔ p.weight.support ⊆ s := by
  refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ ?_⟩
  · rw [← Set.compl_subset_compl]
    simp at ⊢
    rw [← measure_add_measure_compl (s := s) (by measurability)] at h₀
    nth_rw 1 [← add_zero (p.toMeasure s)] at h₀
    rw [ENNReal.add_right_inj ha] at h₀
    obtain h₀' := Eq.symm h₀
    rw [DiscreteMeasure.toMeasure_apply_eq_zero_iff (MeasurableSet.compl_iff.mpr hs)] at h₀'
    exact Set.disjoint_compl_right_iff_subset.mp h₀'
  · rw [← DiscreteMeasure.toMeasure_apply_inter_support hs MeasurableSet.univ (fun x hx ↦ trivial)]
    rw [← DiscreteMeasure.toMeasure_apply_inter_support MeasurableSet.univ hs h₀, Set.inter_comm]

theorem apply_eq_toMeasure_univ_iff [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (hp : p.weight ≠ fun _ ↦ 0) (a : α) (ha : p a ≠ ⊤) : p a = p.toMeasure Set.univ ↔ p.weight.support = {a} := by
  rw [← DiscreteMeasure.toMeasure_apply_singleton p a, toMeasure_apply_eq_toMeasure_univ_iff p (by measurability)]
  · refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ h₀.le⟩
    apply le_antisymm h₀
    simp at h₀ ⊢
    obtain h₀' : ∀ (y : α), y ≠ a → p y = 0 := by
      intro y hy
      exact (DiscreteMeasure.apply_eq_zero_iff p y).mpr fun a => hy (h₀ y a)
    by_contra h₂
    apply hp
    ext x
    by_cases h₃ : x = a
    · exact h₃ ▸ h₂
    · exact h₀' x h₃
  · simp [ha]

theorem coe_le_toMeasure_univ [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (a : α) : p a ≤ p.toMeasure Set.univ := by
  rw [← DiscreteMeasure.toMeasure_apply_singleton p a]
  apply DiscreteMeasure.toMeasure_mono (by measurability) MeasurableSet.univ (by simp) (by simp)

theorem apply_le_one [MeasurableSpace α] [MeasurableSingletonClass α] {w : DiscreteMeasure α} [IsProbabilityMeasure w.toMeasure] (a : α) : w a ≤ 1 := by
  have h : w.toMeasure Set.univ = 1 := by
    rw [← isProbabilityMeasure_iff]
    infer_instance
  rw [← toMeasure_apply_singleton w a, ← h]
  exact measure_mono (Set.subset_univ _)

end IsFiniteOrProbabilityMeasure

end DiscreteMeasure

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `DiscreteMeasure`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toDiscreteMeasure [hmeas : MeasurableSpace α] (μ : Measure α)
    : DiscreteMeasure α := ⟨fun x => μ ({x} : Set α)⟩

variable [MeasurableSpace α] (μ : Measure α)

theorem toDiscreteMeasure_apply (x : α) : μ.toDiscreteMeasure x = μ {x} := rfl

@[simp]
theorem toDiscreteMeasure_toMeasure [MeasurableSingletonClass α] [Countable α] : μ.toDiscreteMeasure.toMeasure = μ := by
  apply Measure.ext
  intro s hs
  rw [μ.toDiscreteMeasure.toMeasure_apply hs, ← μ.tsum_indicator_apply_singleton s hs]
  apply tsum_congr (fun b ↦ ?_)
  rw [Set.indicator.mul_indicator_eq]
  congr

end Measure

namespace DiscreteMeasure

section countable

variable (p : DiscreteMeasure α)

variable  [hmeas : MeasurableSpace α] [MeasurableSingletonClass α]


@[simp]
theorem toMeasure_toDiscreteMeasure : toDiscreteMeasure p.toMeasure = p := by
  ext x
  simp_rw [toDiscreteMeasure, toMeasure_apply_singleton]
  rfl

theorem toMeasure_eq_iff_eq_toDiscreteMeasure [Countable α] (μ : Measure α) :
    p.toMeasure = μ ↔ p = μ.toDiscreteMeasure := by
  rw [Measure.ext_iff]
  -- conv => left; intro s hs; rw [trim_measurableSet_eq _ hs]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x
    specialize h {x} (measurableSet_singleton x)
    rw [DiscreteMeasure.toMeasure_apply_singleton] at h
    rw [h]
    rfl
  · intro s hs
    rw [h]
    nth_rw 2 [← toDiscreteMeasure_toMeasure μ]

end countable

/- Now we enter the monad world. -/

section map

/-- The functorial action of a function on a `DiscreteMeasure`. -/
noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where weight := fun b ↦ (∑' a, (g⁻¹' {b}).indicator μ.weight a)

noncomputable instance : Functor DiscreteMeasure where
  map := map

@[simp]
lemma map_eq [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β]
(μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (x : β) : (μ.map g) x = μ.toMeasure (g⁻¹' {x}) := by
  rw [map, toMeasure_apply _ (by measurability)]
  aesop

lemma map_eq' [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (x : β) : (μ.map g) x =  ∑' (i : α), μ i * ({x} : Set β).indicator 1 (g i) := by
  rw [map_eq μ g hg, toMeasure_apply _ (by measurability)]
  apply tsum_congr (fun b ↦ by congr)

lemma map_coe [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (f : α → β) (hf : Measurable f) : toMeasure (μ.map f : DiscreteMeasure β) = Measure.map f (toMeasure μ) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (hs := hs) (hf := hf)]
  rw [toMeasure_apply₂ (hs := hs)]
  conv => left; left; intro a; rw [@map_eq α β _ _ _ _ μ f hf a.val]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by  simp
  nth_rw 1 [h]
  exact (@toMeasure_additive α s _ _ μ _ (by measurability) (by measurability) (Set.PairwiseDisjoint.fiber_subtype s)).symm

lemma map_coe' (μ : DiscreteMeasure α) (f : α → β) : @toMeasure β ⊤ (μ.map f : DiscreteMeasure β) = @Measure.map _ _ ⊤ ⊤ f (@toMeasure α ⊤ μ) := by
  apply @Measure.ext _ ⊤ _ _
  intro s hs
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [@toMeasure_apply₂ β ⊤ _ _ _ hs]
  conv => left; left; intro a; rw [@map_eq α β ⊤ _ ⊤ _ μ f (@Measurable.of_discrete α β ⊤ ⊤ _ _) a.val]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by  simp
  nth_rw 1 [h]
  exact (@toMeasure_additive α s ⊤ _ μ _ (by measurability) (by measurability) (Set.PairwiseDisjoint.fiber_subtype s)).symm


lemma map_toMeasure' [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) : (μ.map g).toMeasure = sum (fun a ↦ μ a • (dirac (g a))) := by
  rw [map_coe (hf := hg)]
  apply @Measure.ext _ _
  intro s hs
  rw [toMeasure, @Measure.map_sum (hf := by measurability)]
  simp_rw [Measure.map_smul, @Measure.map_dirac α β _ _ g (by measurability)]
  rfl

lemma map_map [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ] [MeasurableSingletonClass γ] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (h : β → γ) (hh : Measurable h): (μ.map g).map h = μ.map (h ∘ g) := by
  rw [← toMeasure_inj, map_coe (hf := by measurability), map_coe (hf := hg), map_coe (hf := by measurability), Measure.map_map (by measurability) (by measurability)]

lemma map_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = μ.toMeasure (g⁻¹' s) := by
  rw [map_coe (hf := hg)]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (x : β) : μ.map g x = μ.toMeasure (g⁻¹' {x}) := by
  rw [← toMeasure_apply_singleton (map g μ)]
  apply map_toMeasure_apply (hs := by measurability) (hg := hg)


lemma map_toMeasure_apply₁ [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), μ a * s.indicator 1 (g a) := by
  rw [map_toMeasure' (hg := hg)]
  rw [sum_apply (hs := hs)]
  simp_rw [smul_apply, dirac_apply' _ hs, smul_eq_mul]

lemma map_apply₂ (μ : DiscreteMeasure α) (g : α → β) (x : β) : μ.map g x = ∑' (a : α), μ a * ({x} : Set β).indicator 1 (g a) := by
  rw[@map_apply α β ⊤ _ ⊤ _ (hg := by measurability)]
  rw [@toMeasure_apply α ⊤ _ (hs := by measurability)]
  apply tsum_congr (fun b ↦ by rfl)

lemma map_toMeasure_apply₂ [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), (g⁻¹' s).indicator μ a := by
  rw [@map_toMeasure' α β ⊤ _ _ _ _ g (by measurability)]
  rw [sum_apply (hs := hs)]
  simp_rw [@smul_apply, dirac_apply' (hs := hs), smul_eq_mul]
  apply tsum_congr (fun b ↦ ?_)
  exact Set.indicator.mul_indicator_eq μ (fun b => s (g b)) b

lemma map_toMeasure_apply₃ [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (b : s), μ.toMeasure (g⁻¹' {b.val}) := by
  rw [toMeasure_apply₂ (hs := hs)]
  apply tsum_congr (fun b ↦ ?_)
  exact map_eq μ g hg b.val

lemma map_toMeasure_apply₄ [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s) : (μ.map g).toMeasure s = ∑' (a : g⁻¹' s), (μ a.val) := by
  rw [map_toMeasure_apply (hg := hg) (hs := hs), toMeasure_apply₂ (hs := by measurability)]

theorem id_map (μ : DiscreteMeasure α) :
μ.map id = μ := by
  apply @toMeasure_ext α ⊤ _
  rw [@map_coe α α ⊤ _ ⊤ _ μ id (by measurability)]
  exact Measure.map_id

theorem isProbabilityMeasure_map_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) [hμ : IsProbabilityMeasure μ.toMeasure] (f : α → β) (hf : Measurable f): IsProbabilityMeasure (μ.map f).toMeasure := by
  rw [map_coe (hf := hf)]
  apply isProbabilityMeasure_map (hf := by measurability)


end map

section lintegral

lemma lintegral_eq_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : ∫⁻ (a : α), g a ∂ μ.toMeasure = ∑' (a : α), μ a * (g a) := by
  rw [toMeasure]
  simp

-- TODO: integral_map

lemma lintegral_map [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (f : β → ℝ≥0∞) (hf : Measurable f) : ∫⁻ (a : β), (f a) ∂ (map g μ).toMeasure = ∫⁻ (a : α), f (g a) ∂ μ.toMeasure := by
  rw [map_coe (hf := hg), MeasureTheory.lintegral_map (hf := hf) (hg := hg)]

end lintegral


section join

/-- The monadic join operation for `DiscreteMeasure`. -/
noncomputable def join (m : DiscreteMeasure (DiscreteMeasure α)) : (DiscreteMeasure α) := ⟨fun a ↦ ∑' (μ : DiscreteMeasure α), m μ * μ a⟩

@[simp]
lemma join_weight (m : DiscreteMeasure (DiscreteMeasure α)) (x : α) : m.join x = ∑' (μ : DiscreteMeasure α), m μ * μ x := by
  rfl

instance : MeasurableSpace (DiscreteMeasure α) := ⊤

lemma Measurable_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] : Measurable (@toMeasure α _) := by
  measurability

lemma join_coe [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = Measure.join ((Measure.map toMeasure m.toMeasure)):= by
  apply @Measure.ext _ _
  intro s hs
  rw [Measure.join_apply (hs := by measurability)]
  rw [MeasureTheory.lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [lintegral_eq_toMeasure, toMeasure_apply₂ (hs := hs)]
  simp_rw [join_weight]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left, toMeasure_apply₂ (hs := hs)]

-- #34239
-- join commutes with sum
-- This goes to MeasureTheory.Measure
lemma Measure.join_sum {α : Type u_1} {mα : MeasurableSpace α} {ι : Type u_7} (m : ι → Measure (Measure α)) :
(sum m).join = sum fun (i : ι) ↦ (m i).join := by
  simp_rw [Measure.join, lintegral_sum_measure]
  ext s hs
  rw [ofMeasurable_apply s hs, Measure.sum_apply _ hs]
  apply tsum_congr (fun i ↦ ?_)
  rw [ofMeasurable_apply s hs]

lemma join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m μ • μ.toMeasure) := by
  apply @Measure.ext _ _
  intro s hs
  rw [join_coe, toMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, Measure.map_smul, Measure.join_smul, Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.map_dirac, Measure.join_dirac]
  repeat measurability

lemma join_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) (hs : MeasurableSet s): m.join.toMeasure s = ∑' (μ : DiscreteMeasure α), m μ * μ.toMeasure s := by
  simp only [join_toMeasure]
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  simp

-- #34239
open Measure in
theorem isProbabilityMeasure_join [MeasurableSpace α] {m : Measure (Measure α)} [IsProbabilityMeasure m] (hm : ∀ᵐ μ ∂m, IsProbabilityMeasure μ) : IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

lemma ae_iff_support [MeasurableSpace α] [MeasurableSingletonClass α] (P : α → Prop) (hP : MeasurableSet {x | P x}) (μ : DiscreteMeasure α) : (∀ᵐ x ∂μ.toMeasure, P x) ↔ (∀ x ∈ μ.weight.support, P x) := by
  simp_rw [ae_iff, mem_support_iff, ne_eq, ← not_imp_comm]
  rw [toMeasure_apply₂ (hs := by measurability)]
  simp

lemma isProbabilityMeasure_join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) (hm : IsProbabilityMeasure m.toMeasure) (hμ : ∀ μ, m μ ≠ 0 → IsProbabilityMeasure μ.toMeasure) : IsProbabilityMeasure (m.join).toMeasure := by
  rw [join_coe]
  apply @isProbabilityMeasure_join α _ _ (isProbabilityMeasure_map AEMeasurable.of_discrete)
  simp_rw [← mem_support_iff, ← ae_iff_support (P := fun μ ↦ IsProbabilityMeasure (toMeasure μ)) (hP := by measurability)] at hμ
  exact (ae_map_iff AEMeasurable.of_discrete (@MeasureTheory.ProbabilityMeasure.measurableSet_isProbabilityMeasure _ _)).mpr hμ

end join

section bind

/-- The monadic bind operation for `DiscreteMeasure`. -/
noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := (μ.map g).join

-- define a mixture
noncomputable def mixture {n : ℕ} (p : DiscreteMeasure (Fin n)) (μ : Fin n → DiscreteMeasure α) := p.bind μ



lemma bind_toMeasure_apply_eq_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s) : (μ.bind g).toMeasure s = μ.toMeasure.bind (toMeasure ∘ g) s := by
  rw [bind, Measure.bind, join_coe, ← Measure.map_map (hg := by measurability) (hf := by measurability), map_coe (hf := hg)]

lemma bind_coe [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g) : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  apply @Measure.ext _ _
  intro s hs
  rw [bind_toMeasure_apply_eq_toMeasure (hg := hg) (hs := hs)]

-- #34239
open Measure in
theorem isProbabilityMeasure_bind [MeasurableSpace α] [MeasurableSpace β] {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β} (hf₀ : AEMeasurable f m) (hf₁ : ∀ᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp [Measure.bind]
  apply @isProbabilityMeasure_join _ _ _ (isProbabilityMeasure_map hf₀) ((ae_map_iff hf₀ ProbabilityMeasure.measurableSet_isProbabilityMeasure).mpr hf₁)

-- #34239
-- bind commutes with sum
-- This goes to MeasureTheory.Measure
lemma Measure.bind_sum {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {ι : Type u_7} (m : ι → Measure α) (f : α → Measure β) (h : AEMeasurable f (sum fun i => m i)) :
  (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [Measure.bind, Measure.map_sum h, Measure.join_sum]

-- #34239
-- scalar multiplication commutes with bind
-- This goes to MeasureTheory.Measure
lemma Measure.bind_smul {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α) (f : α → Measure β) :
  (c • m).bind f = c • (m.bind f) := by
  simp_rw [Measure.bind, Measure.map_smul, Measure.join_smul]

lemma bind_toMeasure (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (μ.bind g).toMeasure  = sum (fun a ↦ (μ a) • (g a).toMeasure) := by
  apply @Measure.ext _ ⊤
  intro s _
  rw [bind_toMeasure_apply_eq_toMeasure, toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_toMeasure_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : (μ.bind g).toMeasure s = ∑' (a : α), μ a * (g a).toMeasure s := by
  rw [bind_toMeasure]
  simp

@[simp]
lemma bind_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g) x = ∑' (a : α), μ a * (g a) x := by
  simp_rw [← toMeasure_apply_singleton (μ.bind g) x, ← toMeasure_apply_singleton _ x, bind_toMeasure_apply]

lemma join_map_map (m : DiscreteMeasure (DiscreteMeasure α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  rw [← toMeasure_apply_singleton (m.bind (map f)), ← toMeasure_apply_singleton (map f m.join), bind_toMeasure_apply, map_toMeasure_apply, join_toMeasure_apply]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_singleton, DiscreteMeasure.map_apply]


theorem bind_const (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) : (μ₁.bind fun (_ : α) => μ₂).toMeasure =  (μ₁.toMeasure Set.univ) • μ₂.toMeasure := by
  rw [bind_coe, Function.comp_apply', Measure.bind_const]

theorem bind_bind (μ₁ : DiscreteMeasure α) (f : α → DiscreteMeasure β) (g : β → DiscreteMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  apply toMeasure_ext
  repeat rw [bind_coe]
  rw [@Measure.bind_bind (hf := AEMeasurable.of_discrete) (hg := AEMeasurable.of_discrete)]
  congr
  ext a'
  rw [comp_apply, comp_apply, bind_coe]

theorem bind_comm (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) (f : α → β → DiscreteMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  ext x
  repeat simp_rw [bind_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ tsum_congr (fun a ↦ ?_))
  ring

lemma isProbabilityMeasure_bind_toMeasure {m : DiscreteMeasure α} [hm : IsProbabilityMeasure m.toMeasure] {f : α → DiscreteMeasure β} (hf₁ : ∀ (a : α), IsProbabilityMeasure (f a).toMeasure) : IsProbabilityMeasure (m.bind f).toMeasure := by
  rw [bind_coe]
  refine @isProbabilityMeasure_bind β α ⊤ ⊤ m.toMeasure _ (toMeasure ∘ f) AEMeasurable.of_discrete ?_
  simp [hf₁]


end bind

section pure

/-- The pure `DiscreteMeasure` puts all the mass lies in one point. The value of `pure a` is `1` at `a` and
`0` elsewhere. In other words, `pure ∘ toMeasure = Measure.dirac`. -/
noncomputable def pure (a : α) : DiscreteMeasure α := ({a} : Set α).indicator 1

lemma pure_apply (a : α) : pure a = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma pure_apply_self {a : α} : pure a a = 1 := by
  rw [pure_apply]
  simp

@[simp]
lemma pure_apply_nonself {a b : α} (h : b ≠ a) : pure a b = 0 := by
  rw [pure_apply]
  simp [h]

lemma pure_comm {a a' : α} : pure a a' = pure a' a := by
  rw [pure_apply, pure_apply, Set.indicator, Set.indicator]
  congr 1
  simp only [Set.mem_singleton_iff, eq_iff_iff]
  exact eq_comm

@[simp]
lemma pure_toMeasure_apply (a : α) (s : Set α) : (pure a).toMeasure s = s.indicator 1 a := by
  rw [toMeasure_apply₁, pure_apply, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h),
      ← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe (a : α) : (pure a).toMeasure = @Measure.dirac α ⊤ a := by
  apply @Measure.ext α ⊤
  simp_rw [pure_toMeasure_apply, Measure.dirac_apply, MeasurableSpace.measurableSet_top, imp_self, implies_true]

lemma toMeasure_pure_eq_dirac : (toMeasure ∘ pure) = @Measure.dirac α ⊤ := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum (a : α) : HasSum (pure a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, pure_apply, ← tsum_subtype, tsum_singleton]
  rfl

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  rw [← toMeasure_inj, pure_coe, map_coe, pure_coe, @Measure.map_dirac _ _ ⊤ ⊤ f (by measurability)]

theorem pure_bind (a : α) (f : α → DiscreteMeasure β) :
(pure a).bind f = f a := by
  apply toMeasure_ext
  rw [bind_coe, pure_coe, dirac_bind (hf :=  by measurability)]
  rfl

theorem bind_pure (μ : DiscreteMeasure α) :
μ.bind pure = μ := by
  apply toMeasure_ext
  rw [bind_coe, Measure.bind, toMeasure_pure_eq_dirac, ← Measure.bind, Measure.bind_dirac]

@[simp, monad_norm]
lemma bind_pure_comp (f : α → β) (μ : DiscreteMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply toMeasure_ext
  simp_rw [bind_coe, map_coe, Function.comp_apply', pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := by measurability)]

lemma isProbabilityMeasure_pure_toMeasure (a : α) : IsProbabilityMeasure ((pure a).toMeasure) := by
  rw [pure_coe]
  exact @dirac.isProbabilityMeasure α ⊤ a

@[simp]
lemma tsum_pure (a : α) (f : α → ℝ≥0∞): ∑' (x : α), (f x) * pure a x = f a := by
  rw [pure_apply]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype]
  simp

end pure


noncomputable instance : Functor DiscreteMeasure where
  map := map

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map g h μ := (@map_map _ _ _ ⊤ _ ⊤ _ ⊤ _ μ g (by measurability) h (by measurability)).symm
