/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib

/-!
# Mass functions
This file is about discrete measures as given by a (weight) function `α → ℝ≥0∞`.

xxx add in next PR
Construction of monadic `pure`, `map` and `bind` is found as well.

Given `μ : MF α`, `MF.toMeasure` constructs a `Measure α ⊤`,
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

@[simp]
lemma Set.indicator_sum_singleton (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = (f x) := by
  rw [← tsum_subtype, tsum_singleton]

@[simp]
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

-- add to Set.PairwiseDisjoint
lemma Set.PairwiseDisjoint.singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  simp_rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
  exact Subtype.coe_ne_coe.mpr hab

lemma Set.PairwiseDisjoint.fiber_subtype {g : α → β} (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)

noncomputable section

variable {α : Type*}

open ENNReal MeasureTheory

namespace MeasureTheory

/-- A mass function, or discrete measures is a function `α → ℝ≥0∞`. -/
def MF (α : Type u) : Type u := α → ℝ≥0∞

namespace MF

instance instFunLike : FunLike (MF α) α ℝ≥0∞ where
  coe p a := p a
  coe_injective' _ _ h := h

@[ext]
protected theorem ext {v w : MF α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

/-- The support of a `MF` is the set where it is nonzero. -/
def support (w : MF α) : Set α := Function.support w

@[simp]
theorem mem_support_iff (w : MF α) (a : α) : a ∈ w.support ↔ w a ≠ 0 := Iff.rfl

theorem apply_eq_zero_iff (w : MF α) (a : α) : w a = 0 ↔ a ∉ w.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (w : MF α) (a : α) : 0 < w a ↔ a ∈ w.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

/-- The `@Measure α ⊤` as defined through a `MF α` (mass function) through a sum of diracs. -/
def toMeasure (w : MF α) : @Measure α ⊤ :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α ⊤ a)

/-
For some reasons, these instances have no effect...

noncomputable instance : Coe (MF α) (@Measure α ⊤) where
  coe w : @Measure α ⊤ := w.toMeasure

noncomputable instance : CoeFun (MF α) (fun _ => Set α → ℝ≥0∞) where
  coe w := w.toMeasure
-/

lemma toMeasure_apply (μ : MF α) (s : Set α) : μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  simp [toMeasure]

lemma toMeasure_apply₁ (μ : MF α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [toMeasure_apply]

lemma toMeasure_apply₂ (μ : MF α) (s : Set α) : μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [toMeasure_apply, tsum_subtype]

@[simp]
lemma toMeasure_apply_singleton (μ : MF α) (a : α) :
    ∑' (i : α), ({a} : Set α).indicator μ i = μ a := by
  rw [← tsum_subtype, tsum_singleton]

@[simp]
lemma toMeasure_apply_singleton' (μ : MF α) (a : α) : μ.toMeasure {a} = μ a := by
  simp [toMeasure_apply]

lemma toMeasure_singleton_eq_weight (μ : MF α) : (fun (a : α) ↦ μ.toMeasure {a}) = μ := by
  simp [toMeasure_apply]

theorem toMeasure_apply_eq_zero_iff {μ : MF α} {s : Set α} : μ.toMeasure s = 0 ↔ Disjoint μ.support s := by
  rw [toMeasure_apply₁, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

@[simp]
theorem toMeasure_apply_inter_support {μ : MF α} {s : Set α} :
    μ.toMeasure (s ∩ μ.support) = μ.toMeasure s := by
  simp only [toMeasure_apply, support]
  apply tsum_congr (fun a ↦ ?_)
  aesop

theorem toMeasure_apply_eq_of_inter_support_eq {μ : MF α} {s t : Set α} (h : s ∩ μ.support = t ∩ μ.support) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support (s := s), ← toMeasure_apply_inter_support (s := t), h]

/- Additivity for `μ.toMeasure` for a `μ : MF` not only applies to countable unions, but to arbitrary ones. -/
lemma toMeasure_additive (μ : MF α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ ?_)
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ i, b ∈ s i <;> simp [h₀]
  · obtain ⟨i, hi⟩ := h₀
    rw [ENNReal.tsum_eq_add_tsum_ite i]
    simp only [hi, ↓reduceIte]
    nth_rw 1 [← add_zero (μ b)] ; congr
    apply (ENNReal.tsum_eq_zero.mpr ?_).symm
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    exact fun j hj hb ↦ False.elim <| Disjoint.notMem_of_mem_left (hs (id (Ne.symm hj))) hi hb
  · refine (ENNReal.tsum_eq_zero.mpr (fun j ↦ ?_)).symm
    push_neg at h₀
    simp [h₀ j]

@[simp]
theorem toMeasure_apply_finset {μ : MF α} (s : Finset α) : μ.toMeasure s = ∑ x ∈ s, μ x := by
  rw [toMeasure_apply₁, tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

@[simp]
theorem toMeasure_apply_fintype {μ : MF α} (s : Set α) [Fintype α] : μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [toMeasure_apply₁]
  exact tsum_fintype (s.indicator μ)

lemma toMeasure_apply_univ (μ : MF α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

lemma toMeasure_apply_univ' (μ : MF α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d): μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ s hs₀

theorem toMeasure_injective : (toMeasure : MF α → @Measure α ⊤).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton' μ, ← toMeasure_apply_singleton' ν, h]

@[simp]
theorem toMeasure_inj {μ ν : MF α} : μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

theorem toMeasure_mono {s t : Set α} {μ : MF α} (h : s ∩ μ.support ⊆ t) : μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

@[simp]
theorem restrict_toMeasure_support {μ : MF α} : μ.toMeasure.restrict μ.support = μ.toMeasure := by
  apply @Measure.ext α ⊤
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support]

section IsFiniteOrProbabilityMeasure

lemma isProbabilityMeasure_iff_hasSum {p : MF α} :
    IsProbabilityMeasure p.toMeasure ↔ HasSum p 1 := by
  rw [isProbabilityMeasure_iff, MF.toMeasure_apply_univ, Summable.hasSum_iff ENNReal.summable]

lemma isProbabilityMeasure_iff_tsumOne {μ : MF α} : IsProbabilityMeasure μ.toMeasure ↔ ∑' a, μ a = 1 := by
  rw [isProbabilityMeasure_iff_hasSum, Summable.hasSum_iff ENNReal.summable]

lemma isFiniteMeasure_iff_tsum_ne_top {μ : MF α} : IsFiniteMeasure μ.toMeasure ↔ ∑' a, μ a ≠ ⊤ := by
  rw [isFiniteMeasure_iff, MF.toMeasure_apply_univ, lt_top_iff_ne_top]

theorem toMeasure_ne_top_of_isFiniteMeasure (p : MF α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s ≠ ∞ := measure_ne_top p.toMeasure s

theorem toMeasure_le_top_of_isFiniteMeasure (p : MF α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s < ∞ := by
  exact measure_lt_top p.toMeasure s

theorem coe_ne_zero (p : MF α) (h : IsProbabilityMeasure p.toMeasure): p ≠ (fun _ ↦ 0) := by
  by_contra h'
  rw [isProbabilityMeasure_iff] at h
  have g : p.toMeasure Set.univ = 0 := by
    rw [h', MF.toMeasure_apply_univ]
    simp
  apply zero_ne_one' ℝ≥0∞
  rw [← g, ← h]

@[simp]
theorem support_nonempty (p : MF α) (h : IsProbabilityMeasure p.toMeasure): p.support.Nonempty := by
  apply Function.support_nonempty_iff.2 (coe_ne_zero p h)

@[simp]
theorem support_countable (p : MF α) (h : IsFiniteMeasure p.toMeasure): p.support.Countable :=
  Summable.countable_support_ennreal <| isFiniteMeasure_iff_tsum_ne_top.mp h

theorem toMeasure_apply_eq_toMeasure_univ_iff (p : MF α) (s : Set α) (ha : p.toMeasure s ≠ ⊤) : p.toMeasure s = p.toMeasure Set.univ ↔ p.support ⊆ s := by
  refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ ?_⟩
  · rw [← Set.compl_subset_compl]
    simp at ⊢
    rw [← measure_add_measure_compl (s := s) (by measurability)] at h₀
    nth_rw 1 [← add_zero (p.toMeasure s)] at h₀
    rw [ENNReal.add_right_inj ha] at h₀
    obtain h₀' := Eq.symm h₀
    rw [MF.toMeasure_apply_eq_zero_iff] at h₀'
    exact Set.disjoint_compl_right_iff_subset.mp h₀'
  · rw [← MF.toMeasure_apply_inter_support (s := s), ← MF.toMeasure_apply_inter_support (s := Set.univ)]
    simp [Set.inter_eq_self_of_subset_right h₀]

theorem apply_eq_toMeasure_univ_iff (p : MF α) (hp : p ≠ fun _ ↦ 0) (a : α) (ha : p a ≠ ⊤) : p a = p.toMeasure Set.univ ↔ p.support = {a} := by
  rw [← MF.toMeasure_apply_singleton' p a, toMeasure_apply_eq_toMeasure_univ_iff]
  · refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ h₀.le⟩
    apply le_antisymm h₀
    simp at h₀ ⊢
    obtain h₀' : ∀ (y : α), y ≠ a → p y = 0 := by
      intro y hy
      exact (MF.apply_eq_zero_iff p y).mpr fun a => hy (h₀ y a)
    by_contra h₂
    apply hp
    ext x
    by_cases h₃ : x = a
    · exact h₃ ▸ h₂
    · exact h₀' x h₃
  simp [ha]

theorem coe_le_toMeasure_univ (p : MF α) (a : α) : p a ≤ p.toMeasure Set.univ := by
  rw [← MF.toMeasure_apply_singleton' p a]
  exact MF.toMeasure_mono fun ⦃a_1⦄ a => trivial

end IsFiniteOrProbabilityMeasure

end MF

-- The following is not yet PRed

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `MF`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toMF [Countable α] [hmeas : MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    : MF α :=  fun x => μ ({x} : Set α)

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)

theorem toMF_apply (x : α) : μ.toMF x = μ {x} := rfl

@[simp]
theorem toMF_toMeasure : μ.toMF.toMeasure.trim (m := by infer_instance) (m0 := ⊤) (hm := le_top) = μ := by
  apply Measure.ext
  intro s hs
  rw [trim_measurableSet_eq _ hs]
  rw [μ.toMF.toMeasure_apply s, ← μ.tsum_indicator_apply_singleton s hs]
  apply tsum_congr (fun b ↦ ?_)
  rw [Set.indicator.mul_indicator_eq]
  congr

end Measure

namespace MF

section countable

variable [Countable α] (p : MF α)

@[simp]
theorem toMeasure_toMF : toMF p.toMeasure (hmeas := ⊤) = p := by
  ext x
  simp [toMF]

variable  [hmeas : MeasurableSpace α] [MeasurableSingletonClass α]

theorem toMeasure_eq_iff_eq_toMF (μ : Measure α) :
    p.toMeasure.trim (m := by infer_instance) (m0 := ⊤) (hm := le_top) = μ ↔ p = μ.toMF := by
  rw [Measure.ext_iff]
  conv => left; intro s hs; rw [trim_measurableSet_eq _ hs]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x
    specialize h {x} (measurableSet_singleton x)
    rw [MF.toMeasure_apply_singleton'] at h
    rw [h]
    rfl
  · intro s hs
    rw [h]
    nth_rw 2 [← toMF_toMeasure μ]
    rw [trim_measurableSet_eq _ hs]

end countable

/- Now we enter the monad world. -/

section map

noncomputable def map (g : α → β) (μ : MF α) : MF β := fun b ↦ μ.toMeasure (g⁻¹' {b})

noncomputable instance : Functor MF where
  map := map

@[simp]
lemma map_eq (μ : MF α) (g : α → β) (x : β) : (μ.map g) x = μ.toMeasure (g⁻¹' {x}) := by
  rfl

lemma map_eq' (μ : MF α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : α), μ i * ({x} : Set β).indicator 1 (g i) := by
  rw [map_eq, toMeasure_apply]
  apply tsum_congr (fun b ↦ by congr)

lemma map_coe (μ : MF α) (f : α → β) : (μ.map f : MF β).toMeasure = @Measure.map _ _ ⊤ ⊤ f (μ.toMeasure) := by
  apply @Measure.ext _ ⊤ _ _
  intro s
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [toMeasure_apply₂]
  simp_rw [map_eq]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  intro hs
  exact (toMeasure_additive _ _ (Set.PairwiseDisjoint.fiber_subtype s)).symm

lemma map_toMeasure' (μ : MF α) (g : α → β)  : (μ.map g).toMeasure = sum (m0 := ⊤) (fun a ↦ μ a • (@dirac β ⊤ (g a))) := by
  rw [map_coe]
  apply @Measure.ext _ ⊤
  intro s hs
  rw [toMeasure, @Measure.map_sum]
  simp_rw [Measure.map_smul, @Measure.map_dirac α β ⊤ ⊤ g (by measurability)]
  apply @AEMeasurable.of_discrete α β ⊤ ⊤

lemma map_map (μ : MF α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext x
  rw [← toMeasure_apply_singleton', ← apply_singleton', map_coe, map_coe, map_coe]
  rw [Measure.map_map (by measurability) (by measurability)]

lemma map_apply₀ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = μ (g⁻¹' s) := by
  rw [map_coe]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply₁ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), μ.weight a * s.indicator 1 (g a) := by
  rw [map_toMeasure']
  simp

lemma map_apply₂ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), (g⁻¹' s).indicator μ.weight a := by
  rw [map_toMeasure']
  simp only [MeasurableSpace.measurableSet_top, sum_apply, smul_apply, dirac_apply', smul_eq_mul]
  apply tsum_congr (fun b ↦ ?_)
  exact Set.indicator.mul_indicator_eq μ.weight (fun b => s (g b)) b

lemma map_apply₃ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (b : s), μ (g⁻¹' {b.val}) := by
  rw [apply₂]
  rfl

lemma map_apply₄ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : g⁻¹' s), (μ.weight a.val) := by
  rw [map_apply₀, apply₂]

theorem id_map (μ : DiscreteMeasure α) :
μ.map id = μ := toMeasure_ext' <| (map_coe μ id) ▸ Measure.map_id

end map

section pure

noncomputable def pure (a : α) : MF α := ({a} : Set α).indicator 1

@[simp]
lemma pure_eq (a : α) : pure a = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma pure_apply (a : α) (s : Set α) : (pure a).toMeasure s = s.indicator 1 a := by
  rw [toMeasure_apply₁, pure_eq, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]
    rw [← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe (a : α) : (pure a).toMeasure = @Measure.dirac α ⊤ a := by
  apply @Measure.ext α ⊤
  simp_rw [pure_apply, Measure.dirac_apply, MeasurableSpace.measurableSet_top, imp_self, implies_true]

lemma map_toDirac : (toMeasure ∘ pure) = @Measure.dirac α ⊤ := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum (a : α) : HasSum (pure a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, pure_eq, ← tsum_subtype, tsum_singleton]
  rfl

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  ext x
  rw [map_weight, pure_weight, pure_apply]
  exact Set.indicator_eq_indicator (id comm.symm) rfl

theorem pure_bind (a : α) (f : α → DiscreteMeasure β) :
(pure a).bind f = f a := by
  apply toMeasure_ext'
  rw [bind_coe, pure_coe, dirac_bind (hf :=  by measurability)]
  rfl

theorem bind_pure (μ : DiscreteMeasure α) :
μ.bind pure = μ := by
  apply toMeasure_ext'
  rw [bind_coe, Measure.bind, map_toDirac, ← Measure.bind, Measure.bind_dirac]

lemma bind_pure_comp (f : α → β) (μ : DiscreteMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply toMeasure_ext'
  simp_rw [bind_coe, map_coe, Function.comp_apply', pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := by measurability)]

end pure

end MF

end MeasureTheory

#min_imports
