/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

-- #34138: Intro to MassFunction
-- #34239: giry monad extensions, bind and join


import Mathlib

-- feat(MeasureTheory): Introduce Mass Function α giving rise to a Measure α ⊤` #34138

/-!
# Mass functions
This file is about discrete measures as given by a (weight) function `α → ℝ≥0∞`.

xxx add in next PR
Construction of monadic `pure`, `map` and `bind` is found as well.

Given `μ : MassFunction α`, `MassFunction.toMeasure` constructs a `Measure α ⊤`,
by assigning each set the sum of the weights of each of its elements.
For this measure, every set is measurable.

## Tags

weight function, discrete measure

-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal

universe u v w

variable {α β γ δ : Type*}

-- to Set.indicator

lemma Set.indicator_sum_singleton (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = (f x) := by
  rw [← tsum_subtype, tsum_singleton]

-- #34138
@[simp]
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

-- #34138
lemma Set.PairwiseDisjoint.singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  simp_rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
  exact Subtype.coe_ne_coe.mpr hab

-- #34138
lemma Set.PairwiseDisjoint.fiber_subtype {g : α → β} (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)

-- #34138
open Classical in
lemma Function.support_subsingleton_of_disjoint [Zero β] {s : δ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) (j : δ) (hj : i ∈ s j) :
    Function.support (fun d ↦ if i ∈ s d then f i else 0) ⊆ {j} := by
  intro d
  simp_rw [Set.mem_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
  rw [← not_imp_not]
  intro hd e
  obtain r := Set.disjoint_iff_inter_eq_empty.mp (hs hd)
  revert r
  change s d ∩ s j ≠ ∅
  rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
  exact ⟨i, ⟨e.1, hj⟩⟩

-- #34138
lemma Set.indicator_iUnion_of_disjoint [AddCommMonoid β] [TopologicalSpace β]
    (s : δ → Set α) (hs : Pairwise (Disjoint on s)) (f : α → β) (i : α) :
    (⋃ d, s d).indicator f i = ∑' d, (s d).indicator f i := by
  classical
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ d, i ∈ s d <;> simp only [h₀, ↓reduceIte]
  · obtain ⟨j, hj⟩ := h₀
    rw [← tsum_subtype_eq_of_support_subset (s := {j})]
    · simp only [tsum_fintype, Finset.univ_unique, Set.default_coe_singleton, Finset.sum_singleton,
      left_eq_ite_iff]
      exact fun h ↦ False.elim (h hj)
    · apply (support_subsingleton_of_disjoint f hs i j hj)
  · push_neg at h₀
    simp_rw [if_neg (h₀ _), tsum_zero]

noncomputable section

variable {α : Type*}

open ENNReal MeasureTheory

namespace MeasureTheory

-- #34138
/-- A mass function, or discrete measures is a function `α → ℝ≥0∞`. -/
def MassFunction (α : Type u) : Type u := α → ℝ≥0∞

namespace MassFunction

-- #34138
instance instFunLike : FunLike (MassFunction α) α ℝ≥0∞ where
  coe p a := p a
  coe_injective' _ _ h := h

-- #34138
@[ext]
protected theorem ext {v w : MassFunction α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

-- #34138
/-- The support of a `MassFunction` is the set where it is nonzero. -/
def support (w : MassFunction α) : Set α := Function.support w

-- #34138
@[simp]
theorem mem_support_iff (w : MassFunction α) (a : α) : a ∈ w.support ↔ w a ≠ 0 := Iff.rfl

-- #34138
theorem apply_eq_zero_iff (w : MassFunction α) (a : α) : w a = 0 ↔ a ∉ w.support := by
  rw [mem_support_iff, Classical.not_not]

-- #34138
theorem apply_pos_iff (w : MassFunction α) (a : α) : 0 < w a ↔ a ∈ w.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

-- #34138
/-- The `@Measure α ⊤` as defined through a `MassFunction α` (mass function) through a sum of
diracs. -/
noncomputable def toMeasure (w : MassFunction α) : Measure[⊤] α :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α ⊤ a)

noncomputable def toMeasure' (w : MassFunction α) (mα : MeasurableSpace α := ⊤) : Measure[mα] α :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α mα a)

lemma toMeasure_trim (w : MassFunction α) [mα : MeasurableSpace α] : (w.toMeasure).trim (le_top) = Measure.sum (fun a ↦ (w a) • Measure.dirac a) := by
  ext s hs
  rw [trim_measurableSet_eq _ hs]
  rw [toMeasure]
  rw [sum_apply, sum_apply]
  simp_rw [smul_apply]
  apply tsum_congr fun b ↦ ?_
  congr 1
  simp
  rw [dirac_apply']
  exact hs
  exact hs
  simp only [MeasurableSpace.measurableSet_top]



-- #34138
lemma toMeasure_apply (μ : MassFunction α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  simp [toMeasure]

-- #34138
lemma toMeasure_apply₁ (μ : MassFunction α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [toMeasure_apply]

-- #34138
lemma toMeasure_apply₂ (μ : MassFunction α) (s : Set α) : μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [toMeasure_apply, tsum_subtype]

-- #34138
@[simp]
lemma toMeasure_apply_singleton (μ : MassFunction α) (a : α) : μ.toMeasure {a} = μ a := by
  simp only [toMeasure_apply, Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype, tsum_singleton]

-- #34138
theorem toMeasure_apply_eq_zero_iff {μ : MassFunction α} {s : Set α} :
    μ.toMeasure s = 0 ↔ Disjoint μ.support s := by
  rw [toMeasure_apply₁, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

-- #34138
@[simp]
theorem toMeasure_apply_inter_support {μ : MassFunction α} {s : Set α} :
    μ.toMeasure (s ∩ μ.support) = μ.toMeasure s := by
  simp only [toMeasure_apply, support]
  apply tsum_congr (fun a ↦ ?_)
  aesop

theorem toMeasure_apply_inter_support' {μ : MassFunction α} {s : Set α} (t : Set α) (ht : μ.support ⊆ t) :
    μ.toMeasure (s ∩ t) = μ.toMeasure s := by
  rw [← toMeasure_apply_inter_support, ← toMeasure_apply_inter_support (s := s), Set.inter_assoc]
  congr 1
  rw [← Set.left_eq_inter, Set.inter_comm] at ht
  rw [← ht]

-- #34138
theorem toMeasure_apply_eq_of_inter_support_eq {μ : MassFunction α} {s t : Set α}
    (h : s ∩ μ.support = t ∩ μ.support) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support (s := s), ← toMeasure_apply_inter_support (s := t), h]

lemma Set.indicator_iUnion_of_disjoint (s : δ → Set α) (hs : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) (i : α) : (⋃ d, s d).indicator f i = ∑' d, (s d).indicator f i := by
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ d, i ∈ s d <;> simp only [Set.mem_iUnion, h₀, ↓reduceIte]
  · obtain ⟨j, hj⟩ := h₀
    rw [ENNReal.tsum_eq_add_tsum_ite j]
    simp only [hj, ↓reduceIte]
    nth_rw 1 [← add_zero (f i)] ; congr
    apply (ENNReal.tsum_eq_zero.mpr ?_).symm
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    exact fun k hk hb ↦ False.elim <| Disjoint.notMem_of_mem_left (hs (id (Ne.symm hk))) hj hb
  · refine (ENNReal.tsum_eq_zero.mpr (fun j ↦ ?_)).symm
    push_neg at h₀
    simp [h₀ j]

-- #34138
/- Additivity for `μ.toMeasure` for a `μ : MassFunction` not only applies to countable unions, but
to arbitrary ones. -/
lemma toMeasure_additive (μ : MassFunction α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) :
    μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply, Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  exact tsum_congr (fun b ↦ Set.indicator_iUnion_of_disjoint s hs μ b)

-- #34138
@[simp]
theorem toMeasure_apply_finset {μ : MassFunction α} (s : Finset α) : μ.toMeasure s = ∑ x ∈ s, μ x
    := by
  rw [toMeasure_apply₁, tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

-- #34138
@[simp]
theorem toMeasure_apply_fintype {μ : MassFunction α} (s : Set α) [Fintype α] :
    μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [toMeasure_apply₁]
  exact tsum_fintype (s.indicator μ)

-- #34138
lemma toMeasure_apply_univ (μ : MassFunction α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

-- #34138
lemma toMeasure_apply_univ' (μ : MassFunction α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s))
    (hs₁ : Set.univ = ⋃ d, s d) : μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ s hs₀

-- #34138
theorem toMeasure_injective : (toMeasure : MassFunction α → @Measure α ⊤).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton μ, ← toMeasure_apply_singleton ν, h]

-- #34138
@[simp]
theorem toMeasure_inj {μ ν : MassFunction α} : μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

-- #34138
theorem toMeasure_ext {μ ν : MassFunction α} (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_inj.mp h

-- #34138
theorem toMeasure_mono {s t : Set α} {μ : MassFunction α} (h : s ∩ μ.support ⊆ t) :
    μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

-- #34138
@[simp]
theorem restrict_toMeasure_support {μ : MassFunction α} :
    μ.toMeasure.restrict μ.support = μ.toMeasure := by
  apply @Measure.ext α ⊤
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support]

lemma nsupport_weight (μ : MassFunction α) (P : α → Prop) (hμ : μ.toMeasure {a : α | P a} = 0) (a : α) (ha : P a) : μ a = 0 :=
  by
  rw [← nonpos_iff_eq_zero, ← MassFunction.toMeasure_apply_singleton μ a, ← hμ]
  apply OuterMeasureClass.measure_mono μ.toMeasure
  simp [ha]
section IsFiniteOrProbabilityMeasure

lemma isProbabilityMeasure_iff_hasSum {p : MassFunction α} :
    IsProbabilityMeasure p.toMeasure ↔ HasSum p 1 := by
  rw [isProbabilityMeasure_iff, MassFunction.toMeasure_apply_univ, Summable.hasSum_iff ENNReal.summable]

lemma isProbabilityMeasure_iff_tsumOne {μ : MassFunction α} : IsProbabilityMeasure μ.toMeasure ↔ ∑' a, μ a = 1 := by
  rw [isProbabilityMeasure_iff_hasSum, Summable.hasSum_iff ENNReal.summable]

lemma isFiniteMeasure_iff_tsum_ne_top {μ : MassFunction α} : IsFiniteMeasure μ.toMeasure ↔ ∑' a, μ a ≠ ⊤ := by
  rw [isFiniteMeasure_iff, MassFunction.toMeasure_apply_univ, lt_top_iff_ne_top]

theorem toMeasure_ne_top_of_isFiniteMeasure (p : MassFunction α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s ≠ ∞ := measure_ne_top p.toMeasure s

theorem toMeasure_le_top_of_isFiniteMeasure (p : MassFunction α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s < ∞ := by
  exact measure_lt_top p.toMeasure s

theorem coe_ne_zero (p : MassFunction α) (h : IsProbabilityMeasure p.toMeasure): p ≠ (fun _ ↦ 0) := by
  by_contra h'
  rw [isProbabilityMeasure_iff] at h
  have g : p.toMeasure Set.univ = 0 := by
    rw [h', MassFunction.toMeasure_apply_univ]
    simp
  apply zero_ne_one' ℝ≥0∞
  rw [← g, ← h]

@[simp]
theorem support_nonempty (p : MassFunction α) (h : IsProbabilityMeasure p.toMeasure): p.support.Nonempty := by
  apply Function.support_nonempty_iff.2 (coe_ne_zero p h)

@[simp]
theorem support_countable (p : MassFunction α) (h : IsFiniteMeasure p.toMeasure): p.support.Countable :=
  Summable.countable_support_ennreal <| isFiniteMeasure_iff_tsum_ne_top.mp h

theorem toMeasure_apply_eq_toMeasure_univ_iff (p : MassFunction α) (s : Set α) (ha : p.toMeasure s ≠ ⊤) : p.toMeasure s = p.toMeasure Set.univ ↔ p.support ⊆ s := by
  refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ ?_⟩
  · rw [← Set.compl_subset_compl]
    simp at ⊢
    rw [← measure_add_measure_compl (s := s) (by measurability)] at h₀
    nth_rw 1 [← add_zero (p.toMeasure s)] at h₀
    rw [ENNReal.add_right_inj ha] at h₀
    obtain h₀' := Eq.symm h₀
    rw [MassFunction.toMeasure_apply_eq_zero_iff] at h₀'
    exact Set.disjoint_compl_right_iff_subset.mp h₀'
  · rw [← MassFunction.toMeasure_apply_inter_support (s := s), ← MassFunction.toMeasure_apply_inter_support (s := Set.univ)]
    simp [Set.inter_eq_self_of_subset_right h₀]

theorem apply_eq_toMeasure_univ_iff (p : MassFunction α) (hp : p ≠ fun _ ↦ 0) (a : α) (ha : p a ≠ ⊤) : p a = p.toMeasure Set.univ ↔ p.support = {a} := by
  rw [← MassFunction.toMeasure_apply_singleton p a, toMeasure_apply_eq_toMeasure_univ_iff]
  · refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ h₀.le⟩
    apply le_antisymm h₀
    simp at h₀ ⊢
    obtain h₀' : ∀ (y : α), y ≠ a → p y = 0 := by
      intro y hy
      exact (MassFunction.apply_eq_zero_iff p y).mpr fun a => hy (h₀ y a)
    by_contra h₂
    apply hp
    ext x
    by_cases h₃ : x = a
    · exact h₃ ▸ h₂
    · exact h₀' x h₃
  simp [ha]

theorem coe_le_toMeasure_univ (p : MassFunction α) (a : α) : p a ≤ p.toMeasure Set.univ := by
  rw [← MassFunction.toMeasure_apply_singleton p a]
  exact MassFunction.toMeasure_mono fun ⦃a_1⦄ a => trivial

end IsFiniteOrProbabilityMeasure

end MassFunction

-- The following is not yet PRed

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `MassFunction`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toMassFunction [hmeas : MeasurableSpace α] (μ : Measure α)
    : MassFunction α :=  fun x => μ ({x} : Set α)

variable [MeasurableSpace α] (μ : Measure α)

theorem toMassFunction_apply (x : α) : μ.toMassFunction x = μ {x} := rfl

@[simp]
theorem toMassFunction_toMeasure [MeasurableSingletonClass α] [Countable α] : μ.toMassFunction.toMeasure.trim (m := by infer_instance) (m0 := ⊤) (hm := le_top) = μ := by
  apply Measure.ext
  intro s hs
  rw [trim_measurableSet_eq _ hs]
  rw [μ.toMassFunction.toMeasure_apply s, ← μ.tsum_indicator_apply_singleton s hs]
  apply tsum_congr (fun b ↦ ?_)
  rw [Set.indicator.mul_indicator_eq]
  congr

end Measure

namespace MassFunction

section countable

variable (p : MassFunction α)

@[simp]
theorem toMeasure_toMassFunction : toMassFunction p.toMeasure (hmeas := ⊤) = p := by
  ext x
  simp [toMassFunction]

variable  [hmeas : MeasurableSpace α] [MeasurableSingletonClass α]

theorem toMeasure_eq_iff_eq_toMassFunction [Countable α] (μ : Measure α) :
    p.toMeasure.trim (m := by infer_instance) (m0 := ⊤) (hm := le_top) = μ ↔ p = μ.toMassFunction := by
  rw [Measure.ext_iff]
  conv => left; intro s hs; rw [trim_measurableSet_eq _ hs]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x
    specialize h {x} (measurableSet_singleton x)
    rw [MassFunction.toMeasure_apply_singleton] at h
    rw [h]
    rfl
  · intro s hs
    rw [h]
    nth_rw 2 [← toMassFunction_toMeasure μ]
    rw [trim_measurableSet_eq _ hs]

end countable

/- Now we enter the monad world. -/

section map

/-- The functorial action of a function on a `PMassFunction`. -/
noncomputable def map (g : α → β) (μ : MassFunction α) : MassFunction β := fun b ↦ μ.toMeasure (g⁻¹' {b})

noncomputable instance : Functor MassFunction where
  map := map

@[simp]
lemma map_eq (μ : MassFunction α) (g : α → β) (x : β) : (μ.map g) x = μ.toMeasure (g⁻¹' {x}) := by
  rfl

lemma map_eq' (μ : MassFunction α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : α), μ i * ({x} : Set β).indicator 1 (g i) := by
  rw [map_eq, toMeasure_apply]
  apply tsum_congr (fun b ↦ by congr)

lemma map_coe (μ : MassFunction α) (f : α → β) : (μ.map f : MassFunction β).toMeasure = @Measure.map _ _ ⊤ ⊤ f (μ.toMeasure) := by
  apply @Measure.ext _ ⊤ _ _
  intro s
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [toMeasure_apply₂]
  simp_rw [map_eq]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  intro hs
  exact (toMeasure_additive _ _ (Set.PairwiseDisjoint.fiber_subtype s)).symm

lemma map_toMeasure' (μ : MassFunction α) (g : α → β)  : (μ.map g).toMeasure = sum (m0 := ⊤) (fun a ↦ μ a • (@dirac β ⊤ (g a))) := by
  rw [map_coe]
  apply @Measure.ext _ ⊤
  intro s hs
  rw [toMeasure, @Measure.map_sum]
  simp_rw [Measure.map_smul, @Measure.map_dirac α β ⊤ ⊤ g (by measurability)]
  apply @AEMeasurable.of_discrete α β ⊤ ⊤

lemma map_map (μ : MassFunction α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  rw [← toMeasure_inj, map_coe, map_coe, map_coe, Measure.map_map (by measurability) (by measurability)]

lemma toMeasure_map_apply (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = μ.toMeasure (g⁻¹' s) := by
  rw [map_coe]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply (μ : MassFunction α) (g : α → β) (x : β) : μ.map g x = μ.toMeasure (g⁻¹' {x}) := by
  rw [← toMeasure_apply_singleton (map g μ)]
  apply toMeasure_map_apply

lemma toMeasure_map_apply₁ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : α), μ a * s.indicator 1 (g a) := by
  rw [map_toMeasure']
  simp

lemma toMeasure_map_apply₂ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : α), (g⁻¹' s).indicator μ a := by
  rw [map_toMeasure']
  simp only [MeasurableSpace.measurableSet_top, sum_apply, smul_apply, dirac_apply', smul_eq_mul]
  apply tsum_congr (fun b ↦ ?_)
  exact Set.indicator.mul_indicator_eq μ (fun b => s (g b)) b

lemma toMeasure_map_apply₃ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (b : s), μ.toMeasure (g⁻¹' {b.val}) := by
  rw [toMeasure_apply₂]
  rfl

lemma toMeasure_map_apply₄ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : g⁻¹' s), (μ a.val) := by
  rw [toMeasure_map_apply, toMeasure_apply₂]

theorem id_map (μ : MassFunction α) :
μ.map id = μ :=
  toMeasure_ext <| (map_coe μ id) ▸ Measure.map_id

theorem isProbabilityMeasure_toMeasure_map (μ : MassFunction α) [IsProbabilityMeasure μ.toMeasure] (f : α → β) : IsProbabilityMeasure (μ.map f).toMeasure := by
  rw [map_coe]
  exact @isProbabilityMeasure_map _ _ ⊤ ⊤ μ.toMeasure _ f
    <| @AEMeasurable.of_discrete _ _ ⊤ ⊤ _ _ _

end map

section lintegral

lemma lintegral_eq_toMeasure (μ : MassFunction α) (g : α → ℝ≥0∞) : ∫⁻ (a : α), g a ∂ μ.toMeasure = ∑' (a : α), μ a * (g a) := by
  rw [toMeasure]
  simp

-- TODO: integral_map

end lintegral
section join


/-- The monadic join operation for `PMassFunction`. -/
noncomputable def join (m : MassFunction (MassFunction α)) : (MassFunction α) := fun a ↦ ∑' (μ : MassFunction α), m μ * μ a

@[simp]
lemma join_weight (m : MassFunction (MassFunction α)) (x : α) : m.join x = ∑' (μ : MassFunction α), m μ * μ x := by
  rfl

instance : MeasurableSpace (MassFunction α) := ⊤

lemma join_coe (m : MassFunction (MassFunction α)) : m.join.toMeasure = Measure.join (mα := ⊤) ((Measure.map toMeasure m.toMeasure)):= by
  apply @Measure.ext _ ⊤
  intro s _
  rw [Measure.join_apply (mα := ⊤) (hs := by measurability)]
  rw [lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [lintegral_eq_toMeasure, toMeasure_apply₂]
  simp_rw [join_weight]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left, toMeasure_apply₂]

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


lemma join_toMeasure (m : MassFunction (MassFunction α)) : m.join.toMeasure = sum (fun μ  ↦ m μ • μ.toMeasure) := by
  apply @Measure.ext _ ⊤
  intro s _
  rw [join_coe, toMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, Measure.map_smul, Measure.join_smul, Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.map_dirac, Measure.join_dirac]
  measurability

lemma toMeasure_join_apply (m : MassFunction (MassFunction α)) (s : Set α) : m.join.toMeasure s = ∑' (μ : MassFunction α), m μ * μ.toMeasure s := by
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

lemma ae_iff_support (P : α → Prop) (μ : MassFunction α) : (∀ᵐ x ∂μ.toMeasure, P x) ↔ (∀ x ∈ μ.support, P x) := by
  simp_rw [ae_iff, mem_support_iff, ne_eq, ← not_imp_comm]
  simp [toMeasure_apply₂]

lemma isProbabilityMeasure_join_toMeasure (m : MassFunction (MassFunction α)) (hm : IsProbabilityMeasure m.toMeasure) (hμ : ∀ μ, m μ ≠ 0 → IsProbabilityMeasure μ.toMeasure) : IsProbabilityMeasure (m.join).toMeasure := by
  rw [join_coe]
  apply @isProbabilityMeasure_join α ⊤ _ (isProbabilityMeasure_map AEMeasurable.of_discrete)
  simp_rw [← mem_support_iff, ← ae_iff_support] at hμ
  exact (ae_map_iff AEMeasurable.of_discrete (@MeasureTheory.ProbabilityMeasure.measurableSet_isProbabilityMeasure _ ⊤)).mpr hμ

end join

section bind

/-- The monadic bind operation for `MassFunction`. -/
noncomputable def bind (μ : MassFunction α) (g : α → MassFunction β) : (MassFunction β) := (μ.map g).join

lemma toMeasure_bind_apply_eq_toMeasure (μ : MassFunction α) (g : α → MassFunction β) (s : Set β) : (μ.bind g).toMeasure s = μ.toMeasure.bind (toMeasure ∘ g) s := by
  rw [bind, Measure.bind, join_coe, ← Measure.map_map (hg := by measurability) (hf := by measurability), map_coe]

lemma bind_coe (μ : MassFunction α) (g : α → MassFunction β)  : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  apply @Measure.ext _ ⊤
  intro _ _
  rw [toMeasure_bind_apply_eq_toMeasure]


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

lemma bind_toMeasure' (μ : MassFunction α) (g : α → MassFunction β) : (μ.bind g).toMeasure  = sum (fun a ↦ (μ a) • (g a).toMeasure) := by
  apply @Measure.ext _ ⊤
  intro s _
  rw [toMeasure_bind_apply_eq_toMeasure, toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma toMeasure_bind_apply (μ : MassFunction α) (g : α → MassFunction β) (s : Set β) : (μ.bind g).toMeasure s = ∑' (a : α), μ a * (g a).toMeasure s := by
  rw [bind_toMeasure']
  simp

@[simp]
lemma bind_apply (μ : MassFunction α) (g : α → MassFunction β) (x : β) : (μ.bind g) x = ∑' (a : α), μ a * (g a) x := by
  simp_rw [← toMeasure_apply_singleton (μ.bind g) x, ← toMeasure_apply_singleton _ x, toMeasure_bind_apply]

lemma join_map_map (m : MassFunction (MassFunction α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  rw [← toMeasure_apply_singleton (m.bind (map f)), ← toMeasure_apply_singleton (map f m.join), toMeasure_bind_apply, toMeasure_map_apply, toMeasure_join_apply]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_singleton, MassFunction.map_apply]

-- to Function

lemma Function.comp_apply'  {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} : (f ∘ fun x => g x) = fun x => f (g x) := by
  -- simp_rw [← Function.comp_apply]
  rfl

theorem bind_const (μ₁ : MassFunction α) (μ₂ : MassFunction β) : (μ₁.bind fun (_ : α) => μ₂).toMeasure =  (μ₁.toMeasure Set.univ) • μ₂.toMeasure := by
  rw [bind_coe, Function.comp_apply', Measure.bind_const]

theorem bind_bind (μ₁ : MassFunction α) (f : α → MassFunction β) (g : β → MassFunction γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  apply toMeasure_ext
  repeat rw [bind_coe]
  rw [@Measure.bind_bind (hf := AEMeasurable.of_discrete) (hg := AEMeasurable.of_discrete)]
  congr
  ext a'
  rw [comp_apply, comp_apply, bind_coe]

theorem bind_comm (μ₁ : MassFunction α) (μ₂ : MassFunction β) (f : α → β → MassFunction γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  ext x
  repeat simp_rw [bind_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ tsum_congr (fun a ↦ ?_))
  ring






end bind

section pure

/-- The pure `MassFunction` puts all the mass lies in one point. The value of `pure a` is `1` at `a` and
`0` elsewhere. In other words, `pure ∘ toMeasure = Measure.dirac`. -/
noncomputable def pure (a : α) : MassFunction α := ({a} : Set α).indicator 1

lemma pure_apply (a : α) : pure a = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma toMeasure_pure_apply (a : α) (s : Set α) : (pure a).toMeasure s = s.indicator 1 a := by
  rw [toMeasure_apply₁, pure_apply, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h),
      ← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe (a : α) : (pure a).toMeasure = @Measure.dirac α ⊤ a := by
  apply @Measure.ext α ⊤
  simp_rw [toMeasure_pure_apply, Measure.dirac_apply, MeasurableSpace.measurableSet_top, imp_self, implies_true]

lemma map_toDirac : (toMeasure ∘ pure) = @Measure.dirac α ⊤ := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum (a : α) : HasSum (pure a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, pure_apply, ← tsum_subtype, tsum_singleton]
  rfl

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  rw [← toMeasure_inj, pure_coe, map_coe, pure_coe, @Measure.map_dirac _ _ ⊤ ⊤ f (by measurability)]

theorem pure_bind (a : α) (f : α → MassFunction β) :
(pure a).bind f = f a := by
  apply toMeasure_ext
  rw [bind_coe, pure_coe, dirac_bind (hf :=  by measurability)]
  rfl

theorem bind_pure (μ : MassFunction α) :
μ.bind pure = μ := by
  apply toMeasure_ext
  rw [bind_coe, Measure.bind, map_toDirac, ← Measure.bind, Measure.bind_dirac]

@[simp, monad_norm]
lemma bind_pure_comp (f : α → β) (μ : MassFunction α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply toMeasure_ext
  simp_rw [bind_coe, map_coe, Function.comp_apply', pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := by measurability)]

end pure

section seq

/-- The monadic sequencing operation for `MassFunction`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q : MassFunction (α → β)) (p :  Unit → MassFunction α) : MassFunction β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

@[simp, monad_norm]
lemma bind_map_eq_seq (q : MassFunction (α → β)) (p : Unit → MassFunction α) : seq q p = q.bind (fun m => (p ()).map m) := by
  simp_rw [← bind_pure_comp]
  rfl

variable (q : MassFunction (α → β)) (p : Unit → MassFunction α) (b : β)

open scoped Classical in
@[simp]
theorem seq_apply : seq q p b = ∑' (f : α → β) (a : α), q f * if b = f a then (p ()) a else 0 := by
  simp_rw [seq, bind_apply, pure_apply, Set.indicator, Set.mem_singleton_iff, ← ENNReal.tsum_mul_left]
  repeat apply tsum_congr (fun f ↦ ?_)
  split_ifs <;> simp

theorem seq_apply₁ : seq q p b = ∑' (f : α → β) (a : f⁻¹' {b}), q f * (p ()) a := by
  simp_rw [seq_apply, ENNReal.tsum_mul_left, tsum_subtype, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr 1
  apply tsum_congr (fun g ↦ ?_)
  grind

@[simp]
theorem seq_apply₂ : seq q p b = ∑' (f : α → β), q f * ∑' (a : α), (f⁻¹' {b}).indicator (p ()) a := by
  simp_rw [seq, bind_apply, pure_apply, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr
  funext a
  simp only [Pi.one_apply, mul_ite, mul_one, mul_zero, Set.mem_preimage, Set.mem_singleton_iff]
  grind

end seq

section monad

noncomputable instance : Functor MassFunction where
  map := map

noncomputable instance : Seq MassFunction where
  seq := seq

noncomputable instance : Monad MassFunction where
  pure := pure
  bind := bind

instance : LawfulFunctor MassFunction where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulMonad MassFunction :=
  LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)
  (bind_map :=
  fun q p ↦ (bind_map_eq_seq q (fun _ ↦ p)).symm)

@[simp, monad_norm]
lemma pure_eq_pure : @pure α = @Pure.pure MassFunction _ α := by rfl

@[simp, monad_norm]
lemma map_eq_map {α β : Type u} (f : α → β) (p : MassFunction α) : (map f p) = (Functor.map f p) := rfl

@[simp, monad_norm]
lemma seq_eq_seq {α β : Type u} (p : MassFunction (α → β)) (q : Unit → MassFunction α) : seq p q = Seq.seq p q := by
  rfl

@[simp, monad_norm]
lemma bind_eq_bind {α β : Type u} (μ : MassFunction α) (g : α → MassFunction β)  : (bind μ g) = (Bind.bind μ g) := rfl

/--
This instance allows `do` notation for `MassFunction` to be used across universes, for instance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
noncomputable instance : ULiftable MassFunction.{u} MassFunction.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by rw [map_map, Equiv.symm_comp_self, id_map]
      right_inv := fun a => by simp [map_map]
      }

end monad

section sequence

-- `MassFunction`s on lists

@[simp]
lemma sequence_nil {α : Type u} {f : Type u → Type u} [Applicative f] : sequence ([] : List (f α)) = (Pure.pure []) := by
  exact List.traverse_nil id

#print sequence
#check List.traverse_nil

-- @[simp]
-- lemma sequence_nil : sequence ([] : List (MassFunction α)) = (MassFunction.pure []) := by
--   exact rfl

lemma sequence_cons {α : Type u} {f : Type u → Type u} [Applicative f] (μs : List (f α)) (ν : f α) : sequence (ν::μs) = List.cons <$> ν <*> (sequence μs) := by
  exact List.traverse_cons id _ _

open Classical
lemma cons_pure_weight (a a' : α) (l l' : List α) : ((MassFunction.pure ∘ List.cons a') l') (a :: l) = if a = a' ∧ l = l' then 1 else 0 := by
  rw [comp_apply, pure, Set.indicator]
  simp

open Classical
lemma cons_pure_weight_of_empty (a' : α) : ((MassFunction.pure ∘ List.cons a') l') [] = 0 := by
  rw [comp_apply, MassFunction.pure, Set.indicator]
  simp

lemma cons_map_weight_of_empty (μs : MassFunction (List α)) (ν : MassFunction α) : (List.cons <$> ν <*> μs) [] = 0 := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, cons_pure_weight_of_empty]
  simp

lemma cons_map_weight (μs : MassFunction (List α)) (ν : MassFunction α) (l : List α) (a : α) : (List.cons <$> ν <*> μs) (a :: l) = ν a * (μs l) := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, cons_pure_weight]
  have h (a_1 : α) (a_2 : List α) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List α)).indicator (1 : List α → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]

lemma sequence_weight_cons_of_empty (μs : List (MassFunction α)) (ν : MassFunction α) : (sequence (ν::μs)) [] = 0 := by
  exact cons_map_weight_of_empty (sequence μs) ν

lemma sequence_weight_cons (μs : List (MassFunction α)) (ν : MassFunction α) (l : List α) (a : α) : (sequence (ν::μs)) (a::l) = (ν a)*((sequence μs) l) := by
  exact cons_map_weight (sequence μs) ν l a

example (s t : Set α) (h : s ⊆ t) (m : MassFunction α) : m.toMeasure s ≤ m.toMeasure t := by
  exact
  OuterMeasureClass.measure_mono m.toMeasure h

example (a : ℝ≥0∞) : a ≤ 0 ↔ a = 0 := by exact nonpos_iff_eq_zero


lemma sequence_weight₀ (μs : List (MassFunction α)) (l : List α) (hl : l.length = μs.length) :
    (sequence μs) l = List.prod (μs.zipWith (fun a b ↦ a b) l) :=
  by
  induction μs generalizing l with
  | nil =>
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    simp [sequence_nil]
    simp [hl, ← pure_eq_pure, pure_apply]
  | cons μ μs ih =>
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp [List.length_cons] at hl
      rw [sequence_weight_cons]
      rw [ih l hl]
      simp

lemma sequence_weight₁ (μs : List (MassFunction α)) (l : List α) (hl : ¬ l.length = μs.length) :
    (sequence μs) l = 0 :=
  by
  induction μs generalizing l with
  | nil =>
    rw [sequence_nil, ← pure_eq_pure, pure_apply]
    simpa using hl
    | cons μ μs ih =>
      cases l with
      | nil =>
        simp at hl
        rw [sequence_weight_cons_of_empty]
      | cons a l =>
        simp [List.length_cons] at hl
        rw [sequence_weight_cons]
        rw [ih l hl]
        simp

lemma sequence_weight (μs : List (MassFunction α)) (l : List α) :
    (sequence μs) l = if l.length = μs.length then List.prod (μs.zipWith (fun a b ↦ a b) l) else 0 :=
  by
  split_ifs with hl
  · exact sequence_weight₀ μs l hl
  · exact sequence_weight₁ μs l hl

lemma sequence_support_subset (μs : List (MassFunction α)) : (sequence μs).support ⊆ {l | l.length = μs.length} := by
  intro l hl
  simp at hl
  simp
  by_contra h
  apply hl
  simp [sequence_weight, h]


@[simp]
lemma prod_apply_replicate (l : List α) (f : α → β) :
  l.map f = (List.replicate l.length f).zipWith (fun a b ↦ a b) l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.length, ih]; rfl

lemma cons_eq_append_singleton (a : α) (l : List α) : (a::l) = [a] ++ l := by
  simp only [List.cons_append, List.nil_append]

lemma List.nmem_toFinset (b : α) (l : List α) [DecidableEq α] : b ∉ l.toFinset ↔ b ∉ l := by
  rw [List.mem_toFinset]

lemma tprod_eq_prod_of_pow_count (l : List α) (f : α → ℝ≥0∞) [DecidableEq α] : (∏' a, (f a)^(l.count (α := α) a)) = (∏ a ∈ l.toFinset, f a ^ (l.count (α := α) a)) := by
  rw [tprod_eq_prod]
  intro b hb
  rw [List.nmem_toFinset, ← List.count_eq_zero] at hb
  rw [hb, pow_zero]

lemma tsum_eq_sum_of_mul_count (l : List α) (f : α → ℝ≥0∞) : (∑' a, (l.count a) * (f a)) = (∑ a ∈ l.toFinset, (l.count a) * f a) := by
  rw [tsum_eq_sum]
  intro b hb
  rw [List.nmem_toFinset, ← List.count_eq_zero] at hb
  rw [hb]
  ring

lemma list_map_sum_eq_count (l : List α) (f : α → ℝ≥0∞) : (List.map f l).sum = ∑' (a : α), (l.count a) * (f a) := by
  rw [tsum_eq_sum_of_mul_count]
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]

lemma list_map_prod_eq_count (l : List α) (f : α → ℝ≥0∞) [DecidableEq α] : (List.map f l).prod = ∏' (a : α), (f a) ^ (l.count a) := by
  rw [tprod_eq_prod_of_pow_count]
  exact Finset.prod_list_map_count l f

-- define marginal distributions




end sequence

section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : MassFunction α) :  MassFunction (List α) := sequence (List.replicate n μ)

lemma iidSequence_weight (n : ℕ) (μ : MassFunction α) (l : List α) :
    (iidSequence n μ) l = ({l : List α | l.length = n}.indicator (fun l ↦ (List.prod (l.map μ))) l) := by
  rw [Set.indicator]
  split_ifs with hl
  · rw [iidSequence, ← hl]
    rw [sequence_weight]
    simp only [List.length_replicate, ↓reduceIte, prod_apply_replicate]
    rfl
  · simp only [Set.mem_setOf_eq] at hl
    rw [iidSequence, sequence_weight]
    simp [hl]

lemma iidSequence_weight' (n : ℕ) (μ : MassFunction α) [DecidableEq α] (l : List α) :
    iidSequence n μ l = ({l : List α | l.length = n}.indicator (fun l ↦ (∏' (a : α), (μ a) ^ (l.count (α := α) a))) l) := by
  rw [iidSequence_weight n μ l, Set.indicator]
  split_ifs with hl <;> simp at hl
  · rw [list_map_prod_eq_count]
    simp only [Set.mem_setOf_eq, hl, Set.indicator_of_mem]
  · simp [hl]

lemma pure_sequence (ν : MassFunction α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : MassFunction α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

end iidSequence

open NNReal
noncomputable def coinReal (p : ℝ≥0∞) : MassFunction ℝ := fun (b : ℝ) ↦ if b = 1 then (p : ℝ≥0∞) else (if b = 0 then (1 - p : ℝ≥0∞) else 0)

example (a b : Set α) : a ⊆ b ↔ bᶜ ⊆ aᶜ := by exact Iff.symm Set.compl_subset_compl

lemma coinReal_support (p : ℝ≥0∞) : (coinReal p).support ⊆ {0, 1} := by
  rw [← Set.compl_subset_compl]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  rw [Set.mem_compl_iff, ← apply_eq_zero_iff]
  simp [coinReal, hx]

example {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (s : Set α) (hs : MeasurableSet s) : P sᶜ = P Set.univ - P s := by
  refine measure_compl hs ?_

example {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (s : Set α) (hs : MeasurableSet s) : Measure.map (s.indicator 1) P = (coinReal (P s)).toMeasure.trim (le_top) := by
  classical
  ext b hb
  have h : s.indicator 1 ⁻¹' b = (if 1 ∈ b then s else ∅) ∪ (if 0 ∈ b then sᶜ else ∅) := by
    sorry
  rw [Measure.map_apply]
  rw [h]
  rw [trim_measurableSet_eq]
  rw [← toMeasure_apply_inter_support' _ (coinReal_support (P s))]
  rw [toMeasure_apply₁]
  by_cases g₀ : 0 ∈ b <;> simp [g₀]
  · by_cases g₁ : 1 ∈ b <;> simp [g₁]
    · have hb' : b ∩ {0, 1} = {0, 1} := by sorry
      simp_rw [hb']
      sorry
    · have hb' : b ∩ {0, 1} = {0} := by sorry
      simp_rw [hb']
      simp only [toMeasure_apply_singleton]
      rw [measure_compl hs (measure_ne_top P s)]
      simp [coinReal]
  · by_cases g₁ : 1 ∈ b <;> simp [g₁]


    sorry


    grind
    sorry
  rw [h]


  sorry

#check (true.toNat : ℝ)

end MassFunction

-- nonTop


end MeasureTheory
