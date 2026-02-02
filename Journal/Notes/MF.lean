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

lemma Set.indicator_sum_singleton (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = f x := by
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
lemma Function.support_subsingleton_of_disjoint [Zero β] {s : δ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) [DecidablePred (fun d => i ∈ s d)] (j : δ)
    (hj : i ∈ s j) : Function.support (fun d ↦ if i ∈ s d then f i else 0) ⊆ {j} := by
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

-- #34138
/-- The `@Measure α mα` as defined through a `MassFunction α` (mass function) through a sum of
diracs, using a given `MeasurableSpace α`. -/
noncomputable def toMeasure' (w : MassFunction α) (mα : MeasurableSpace α) : Measure[mα] α :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α mα a)

-- #34138
lemma toMeasure_trim_eq_toMeasure' (w : MassFunction α) [mα : MeasurableSpace α] : (w.toMeasure).trim (le_top) = w.toMeasure' mα := by
  ext s hs
  rw [trim_measurableSet_eq _ hs, toMeasure, toMeasure', sum_apply, sum_apply]
  simp_rw [smul_apply]
  · apply tsum_congr fun b ↦ ?_
    congr 1
    simp only [dirac_apply', MeasurableSpace.measurableSet_top]
    rw [dirac_apply' _ hs]
  · exact hs
  · simp only [MeasurableSpace.measurableSet_top]

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

-- #34138
/- Additivity for `μ.toMeasure` for a `μ : MassFunction` not only applies to countable unions, but
to arbitrary ones. -/
lemma toMeasure_additive (μ : MassFunction α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) :
    μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply, Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  exact tsum_congr (fun b ↦ Set.indicator_iUnion_of_disjoint s hs μ b)

-- #34138
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

lemma lintegral_map_coin (μ : MassFunction α) (g : α → β) (f : β → ℝ≥0∞) : ∫⁻ (a : β), (f a) ∂ (map g μ).toMeasure = ∫⁻ (a : α), f (g a) ∂ μ.toMeasure := by
  rw [map_coe, @MeasureTheory.lintegral_map _ _ ⊤ ⊤ _ _ _ (by measurability) (by exact fun ⦃t⦄ a => a)]

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

-- to List.traverse or List.sequence
#check sequence (t := flip List.Vector 0) (f := MassFunction) (List.Vector.nil (α := MassFunction α))

@[simp]
lemma _root_.List.Vector.sequence_nil {α : Type u} {f : Type u → Type u} [Applicative f] : sequence (t := flip List.Vector 0) (List.Vector.nil (α := f α)) = (Pure.pure List.Vector.nil) := by
  rfl

@[simp]
lemma _root_.List.Vector.sequence_cons {α : Type u} {f : Type u → Type u} [Applicative f] (μs : List.Vector (f α) n) (ν : f α) : List.Vector.cons <$> ν <*> (sequence (t := flip List.Vector n) μs) = sequence (t := flip List.Vector (n + 1)) (List.Vector.cons ν μs) := by
  obtain ⟨μs1, μs2⟩ := μs
  subst μs2
  rfl

open Classical in
lemma indicator_mul (a : α) (b : β) (s : Set α) (t : Set β) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) : (if (a ∈ s ∧ b ∈ t) then ((f a) * (g b)) else 0) = s.indicator f a * t.indicator g b := by
  simp only [Set.indicator]
  aesop

-- infrastructure
@[simp]
lemma List.Vector.eq_iff {n : ℕ} (l l' : List.Vector α n) :
  l = l' ↔ l.toList = l'.toList := by
  refine Iff.symm (Injective.eq_iff ?_)
  intro l l' h
  obtain ⟨lv, lp⟩ := l
  congr

@[simp]
lemma List.Vector.cons.injEq {n : ℕ} (a : α) (l : List.Vector α n) (a' : α) (l' : List.Vector α n) :
  (a ::ᵥ l = a' ::ᵥ l') = (a = a' ∧ l = l') := by
  simp

open Classical
lemma List.Vector.pure_cons_apply_cons {n : ℕ} (a a' : α) (l l' : List.Vector α n) : pure (a' ::ᵥ l') (a ::ᵥ l) = (if a = a' ∧ l = l' then 1 else 0) := by
  rw [pure, Set.indicator]
  simp

/-
lemma list_pure_cons_apply_cons (a a' : α) (l l' : List α) : pure (a' :: l') (a :: l) = if a = a' ∧ l = l' then 1 else 0 := by
  rw [pure, Set.indicator]
  simp only [Set.mem_singleton_iff,
    List.cons.injEq, Pi.one_apply]
-/

-- no equivalent in List.Vector exists since the length is wrong anyway.
lemma list_pure_cons_apply_nil {a : α} {l : List α} : pure (a :: l) [] = 0 := by
  rw [pure, Set.indicator]
  simp only [Set.mem_singleton_iff, List.nil_eq, reduceCtorEq, ↓reduceIte]


lemma List.Vector.cons_map_seq_do {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) :
  (do
    let X ← ν
    let Y ← μs
    return (X ::ᵥ Y)
  ) = (List.Vector.cons <$> ν <*> μs) := by
  simp [monad_norm]

/-
lemma list_cons_map_seq_do (μs : MassFunction (List α)) (ν : MassFunction α) :
  (do
    let X ← ν
    let Y ← μs
    return (X :: Y)
  ) = (List.cons <$> ν <*> μs) := by
  simp [monad_norm]
-/

lemma List.Vector.sequence_cons_do {n : ℕ} (μs : (List.Vector (MassFunction α) n)) (ν : MassFunction α) :
  (do
    let X ← ν
    let Y ← sequence (t := flip List.Vector n) μs
    return (X ::ᵥ Y)
  ) = sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs) := by
  simp [sequence, traverse, monad_norm]

/-
lemma list_sequence_cons_do (μs : (List (MassFunction  α))) (ν : MassFunction α) :
  (do
    let X ← ν
    let Y ← sequence μs
    return (X :: Y)
  ) = sequence (ν :: μs) := by
  simp [sequence, monad_norm]
-/

lemma cons_map_seq_nil {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) : (ν >>= fun X => μs >>= Pure.pure ∘ List.Vector.cons X) = (List.Vector.cons <$> ν <*> μs)  := by
  simp [monad_norm]

/-
lemma cons_map_seq_nil (μs : MassFunction (List α)) (ν : MassFunction α) : (ν >>= fun X => μs >>= Pure.pure ∘ List.cons X) = (List.cons <$> ν <*> μs)  := by
  simp [monad_norm]
-/

lemma cons_map_seq_apply {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) (l : List.Vector α (n + 1)): (List.Vector.cons <$> ν <*> μs) l = ∑' (a' : α), ν a' * ∑' (l' : List.Vector α n), μs l' * pure (a' ::ᵥ l') l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]

/-
lemma cons_map_seq_apply (μs : MassFunction (List α)) (ν : MassFunction α) (l : List α): (List.cons <$> ν <*> μs) l = ∑' (a : α), ν a * ∑' (a_1 : List α), μs a_1 * pure (a :: a_1) l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]
-/

-- does not make sense for List.Vector since lengths do not match
lemma cons_map_seq_apply_nil (μs : MassFunction (List α)) (ν : MassFunction α) : (List.cons <$> ν <*> μs) [] = 0 := by
  sorry
  --rw [cons_map_seq_apply]
  --simp_rw [list_pure_cons_apply_nil]
  --simp

lemma List.Vector.cons_map_seq_apply_cons {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) (l : List.Vector α n) (a : α) : (List.Vector.cons <$> ν <*> μs) (a ::ᵥ l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [List.Vector.pure_cons_apply_cons]
  have h (a_1 : α) (a_2 : List.Vector α n) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List.Vector α n)).indicator (1 : List.Vector α n → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]

/-
lemma list_cons_map_seq_apply_cons (μs : MassFunction (List α)) (ν : MassFunction α) (l : List α) (a : α) : (List.cons <$> ν <*> μs) (a :: l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [list_pure_cons_apply_cons]
  have h (a_1 : α) (a_2 : List α) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List α)).indicator (1 : List α → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]
-/

-- does not make sense for List.Vector
@[simp]
lemma sequence_cons_apply_nil (μs : List (MassFunction α)) (ν : MassFunction α) : (sequence (ν::μs)) [] = 0 := by
  simp only [sequence, List.traverse_cons, id_eq]
  exact cons_map_seq_apply_nil (sequence μs) ν

lemma List.Vector.sequence_cons_apply_cons {n : ℕ} (μs : List.Vector (MassFunction α) n) (ν : MassFunction α) (l : List.Vector α n) (a : α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) (a ::ᵥ l) = (ν a) * ((sequence (t := flip List.Vector n) μs) l) := by
  rw [← List.Vector.sequence_cons]
  exact List.Vector.cons_map_seq_apply_cons (sequence (t := flip List.Vector n) μs) ν l a

/-
lemma list_sequence_cons_apply_cons (μs : List (MassFunction α)) (ν : MassFunction α) (l : List α) (a : α) : (sequence (ν::μs)) (a::l) = (ν a)*((sequence μs) l) := by
  exact list_cons_map_seq_apply_cons (sequence μs) ν l a
-/

-- infrastructure
@[simp]
lemma List.Vector.nil_iff (l : List.Vector α 0) : l = List.Vector.nil := by simp

@[simp]
lemma List.Vector.nil_val : (List.Vector.nil (α := α)).val = [] := by
  congr



lemma sequence_apply₀ {n : ℕ} (μs : List.Vector (MassFunction α) n) (l : List.Vector α n) :
    (sequence (t := flip List.Vector n) μs) l = List.prod (μs.zipWith (fun a b ↦ a b) l).toList :=
  by
  induction μs with
  | nil =>
    simp only [List.Vector.nil_iff, List.Vector.sequence_nil]
    rw [← pure_eq_pure, pure_apply]
    simp
  | cons hl =>
    rw [← List.Vector.cons_head_tail l, List.Vector.sequence_cons_apply_cons]
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one,
      List.Vector.zipWith_toList, List.Vector.toList_cons]
    rw [List.zipWith_cons_cons]
    simp [hl]

/-
lemma ssequence_apply₀ (μs : List (MassFunction α)) (l : List α) (hl : l.length = μs.length) :
    (sequence μs) l = List.prod (μs.zipWith (fun a b ↦ a b) l) :=
  by
  induction μs generalizing l with
  | nil =>
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    simp [sequence, List.traverse_nil]
    simp [hl, ← pure_eq_pure, pure_apply]
  | cons μ μs ih =>
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp [List.length_cons] at hl
      rw [list_sequence_cons_apply_cons]
      rw [ih l hl]
      simp
-/

-- does not make sense for List.Vector
/-
lemma sequence_apply₁ (μs : List (MassFunction α)) (l : List α) (hl : ¬ l.length = μs.length) :
    (sequence μs) l = 0 :=
  by
  induction μs generalizing l with
  | nil =>
    rw [sequence, List.traverse_nil, ← pure_eq_pure, pure_apply]
    simpa using hl
    | cons μ μs ih =>
      cases l with
      | nil =>
        simp at hl
        rw [sequence_cons_apply_nil]
      | cons a l =>
        simp [List.length_cons] at hl
        rw [list_sequence_cons_apply_cons]
        rw [ih l hl]
        simp

lemma sequence_apply (μs : List (MassFunction α)) (l : List α) :
    (sequence μs) l = if l.length = μs.length then List.prod (μs.zipWith (fun a b ↦ a b) l) else 0 :=
  by
  split_ifs with hl
  · exact sequence_apply₀ μs l hl
  · exact sequence_apply₁ μs l hl

lemma sequence_support_subset (μs : List (MassFunction α)) : (sequence μs).support ⊆ {l | l.length = μs.length} := by
  intro l hl
  simp at hl
  simp
  by_contra h
  apply hl
  simp [sequence_apply, h]
-/

@[simp]
lemma List.Vector.prod_apply_replicate {n : ℕ} (l : List.Vector α n) (f : α → β) :
  l.map f = (List.Vector.replicate n f).zipWith (fun a b ↦ a b) l := by
  induction l with
  | nil => simp
  | cons a => simp [a]

/-
@[simp]
lemma prod_apply_replicate (l : List α) (f : α → β) :
  l.map f = (List.replicate l.length f).zipWith (fun a b ↦ a b) l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.length, ih]; rfl
-/

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

@[simp]
lemma List.Vector.zipWith_coe {n : ℕ} (f : List.Vector (α → β) n) (l : List.Vector α n) : (List.Vector.zipWith (fun a b => a b) f l).val = (List.zipWith (fun a b => a b) f.val l.val) := by rfl

@[simp]
lemma List.Vector.replicate_coe {n : ℕ} (a : α) : (List.Vector.replicate n a).val = List.replicate n a := by
  rfl

lemma List.Vector.map_coe {n : ℕ} (l : List.Vector α n) : (List.Vector.map f l).val = List.map f l.val := by
  simp only [prod_apply_replicate, zipWith_coe, replicate_coe]
  refine List.ext_get (by simp) (fun _ _ _ ↦ by simp)

-- def List.Vector.count {n : ℕ} (l : List.Vector α n) (a : α) : Fin (n + 1) := ⟨l.val.count a, lt_of_le_of_lt l.val.count_le_length (lt_of_le_of_lt l.prop.le (lt_add_one n))⟩

lemma List.Vector.map_sum_eq_count {n : ℕ} (l : List.Vector α n) (f : α → ℝ≥0∞) : (List.Vector.map f l).val.sum = ∑' (a : α), (l.val.count a) * (f a) := by
  rw [tsum_eq_sum_of_mul_count]
  rw [List.Vector.map_coe]
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]

/-
lemma list_map_sum_eq_count (l : List α) (f : α → ℝ≥0∞) : (List.map f l).sum = ∑' (a : α), (l.count a) * (f a) := by
  rw [tsum_eq_sum_of_mul_count]
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
-/

lemma List.Vector.map_prod_eq_count {n : ℕ} (l : List.Vector α n) (f : α → ℝ≥0∞) [DecidableEq α] : (List.Vector.map f l).val.prod = ∏' (a : α), (f a) ^ (l.val.count a) := by
  rw [tprod_eq_prod_of_pow_count]
  exact Finset.prod_list_map_count l.val f

/-
lemma list_map_prod_eq_count (l : List α) (f : α → ℝ≥0∞) [DecidableEq α] : (List.map f l).prod = ∏' (a : α), (f a) ^ (l.count a) := by
  rw [tprod_eq_prod_of_pow_count]
  exact Finset.prod_list_map_count l f
-/
-- define marginal distributions




end sequence

section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : MassFunction α) : MassFunction (List.Vector α n) := sequence (t := flip List.Vector n) (List.Vector.replicate n μ)


lemma iidSequence_apply (n : ℕ) (μ : MassFunction α) (l : List α) :
    (iidSequence n μ) l = ({l : List α | l.length = n}.indicator (fun l ↦ (List.prod (l.map μ))) l) := by
  rw [Set.indicator]
  split_ifs with hl
  · rw [iidSequence, ← hl]
    rw [sequence_apply]
    simp only [List.length_replicate, ↓reduceIte, prod_apply_replicate]
    rfl
  · simp only [Set.mem_setOf_eq] at hl
    rw [iidSequence, sequence_apply]
    simp [hl]

lemma iidSequence_apply' (n : ℕ) (μ : MassFunction α) [DecidableEq α] (l : List α) :
    iidSequence n μ l = ({l : List α | l.length = n}.indicator (fun l ↦ (∏' (a : α), (μ a) ^ (l.count (α := α) a))) l) := by
  rw [iidSequence_apply n μ l, Set.indicator]
  split_ifs with hl <;> simp at hl
  · rw [list_map_prod_eq_count]
    simp only [Set.mem_setOf_eq, hl, Set.indicator_of_mem]
  · simp [hl]

lemma pure_sequence (ν : MassFunction α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : MassFunction α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

end iidSequence

section coin

open Bool ENNReal NNReal

noncomputable def coin (p : ℝ≥0∞) : MassFunction Bool := fun
  | true => p
  | false => 1 - p

lemma coin_apply (p : ℝ≥0∞) (b : Bool) : (coin p) b = if b then p else (1 - p) := by
  by_cases h : b <;> simp only [h, ↓reduceIte] <;> rfl

lemma isProbabilityMeasure_coin (p : ℝ≥0∞) (h : p ≤ 1) : IsProbabilityMeasure (coin p).toMeasure := by
  rw [isProbabilityMeasure_iff, toMeasure_apply_univ]
  simp [coin, h]

lemma lintegral_coin_id (p : ℝ≥0∞) (g : Bool → ℝ≥0∞) : ∫⁻ (a : Bool), (g a) ∂ (coin p).toMeasure = (1 - p) * (g false) + p * (g true) := by
  rw [lintegral_eq_toMeasure]
  rw [tsum_bool, coin_apply, coin_apply]
  simp only [false_eq_true, ↓reduceIte]

lemma lintegral_coin (p : ℝ≥0∞) : ∫⁻ (a : Bool), ({true} : Set Bool).indicator 1 a ∂ (coin p).toMeasure = p := by
  rw [lintegral_coin_id]
  simp

lemma Bool.mem_not (b : Bool) : not ⁻¹' {b} = {!b} := by
    ext y; cases' y <;> simp

lemma bool_if_not (x y : ℝ≥0∞) (b : Bool) : (if !b then x else y) = (if b then y else x) := by
  by_cases h : b <;> simp [h]

lemma coin_not (p : ℝ≥0) (h : (p : ℝ≥0∞) ≤ 1) : (coin p).map not = coin (1-p) := by
  ext x
  rw [map_apply, Bool.mem_not, toMeasure_apply_singleton, coin_apply, coin_apply]
  rw [(ENNReal.sub_sub_cancel one_ne_top h)]
  rw [bool_if_not]

-- now we come to multiple coins

lemma sequence_coin_apply (p : ℝ≥0∞) (n : ℕ) (l : List Bool) : (iidSequence n (coin p)) l = ({l | l.length = n}.indicator 1 l) * p ^ (l.count true) * (1 - p) ^ (l.count false) := by
  rw [iidSequence_apply' n (coin p)]
  simp [coin, Set.indicator]

end coin

section binom

-- Defining the binomial distribution via the mass function
noncomputable def binom₁ (p : ℝ≥0∞) (n : ℕ) : MassFunction ℕ := fun k ↦ (p ^ k * (1 - p) ^ (n - k)) * (Nat.choose n k)

lemma isProbabilityMeasure_binom₁ (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : IsProbabilityMeasure (binom₁ p n).toMeasure := by
  have g : ∑' (k : ℕ), (p : ℝ≥0∞) ^ k * (1 - p) ^ (n - k) * (n.choose k) = ∑ (k ∈ Finset.range (n + 1)), p ^ k * (1 - p) ^ (n - k) * (n.choose k) := by
    refine tsum_eq_sum (fun b hb ↦ ?_)
    simp only [Finset.mem_range, not_lt, mul_eq_zero, pow_eq_zero_iff', ne_eq,
      Nat.cast_eq_zero] at hb ⊢
    exact Or.inr (Nat.choose_eq_zero_iff.mpr hb)
  rw [isProbabilityMeasure_iff_tsumOne]
  simp_rw [binom₁]
  rw [g, ← add_pow p (1 - p) n]
  simp only [h, add_tsub_cancel_of_le, one_pow]

-- Defining the binomial distribution as the sum of toNats in a sequence of Bernoulli trials
noncomputable def binom₂ (p : ℝ≥0∞) (n : ℕ) : MassFunction ℕ := (iidSequence n ((coin p).map Bool.toNat)).map List.sum

-- Defining the binomial distribution as the count of trues in a sequence of Bernoulli trials
noncomputable def binom₃ (p : ℝ≥0∞) (n : ℕ) : MassFunction ℕ := (iidSequence n (coin p)).map (List.count true)

lemma List.length_sub_count_false (l : List Bool) : l.length - l.count true = l.count false := by
  rw [Nat.sub_eq_iff_eq_add (List.count_le_length), add_comm, List.count_true_add_count_false]

open Finset

lemma List.card_idxsOf_toFinset_eq_count {α : Type*} [BEq α] (l : List α) (a : α) :
    (l.idxsOf a).toFinset.card = l.count a := by
  rw [List.card_toFinset, List.Nodup.dedup List.nodup_idxsOf, List.length_idxsOf]

lemma List.count_ofFn_eq_card [DecidableEq α] (n : ℕ) (f : Fin n → α) (a : α)
    [DecidablePred fun i ↦ f i = a] :
    List.count a (List.ofFn f) = Finset.card {i | f i = a} := by
  rw [← List.card_idxsOf_toFinset_eq_count]
  let s := {i | f i = a}.toFinset
  refine card_bij (fun b hb ↦ ⟨b, ?_⟩) (fun c hc ↦ ?_) (fun d hd1 hd2 hd3 ↦ ?_) (fun e he ↦ ?_)
  · aesop
  · simp only [List.mem_toFinset, List.mem_idxsOf_iff_getElem_sub_pos, Nat.zero_le, Nat.sub_zero,
    List.getElem_ofFn, beq_iff_eq, List.length_ofFn, true_and] at hc
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact Exists.elim hc fun a_1 a ↦ a
  · simp
  · aesop

/-- The types `Fin n → Bool` and `Finset (Fin n)` are eqivalent by using `s : Finset (Fin n)`
as the set where the `f : Fin n → Bool` is `true`. -/
def Equiv_fnFinBool_finsetFin (n : ℕ) : (Fin n → Bool) ≃ (Finset (Fin n)) where
  toFun := fun f ↦ {i | f i}
  invFun := fun s i ↦ i ∈ s
  left_inv := fun l ↦ by simp
  right_inv := fun l ↦ by simp

lemma Equiv_fnFinBool_finsetFin_mem_powersetCard_iff (n k : ℕ) (f : Fin n → Bool) :
    #{i | f i = true} = k ↔ (Equiv_fnFinBool_finsetFin n) f ∈ powersetCard k univ := by
  simp [Equiv_fnFinBool_finsetFin]

/-- The number of maps `f : Fin n → Bool` with `#{i | f i} = k` equals `n.choose k`. -/
-- must stay here
lemma card_fnFinBool {k n : ℕ} : #{ f : Fin n → Bool | #{i | f i} = k } = n.choose k := by
  conv => right; rw [← card_fin n]
  rw [← card_powersetCard k (univ : Finset (Fin n))]
  apply card_equiv (Equiv_fnFinBool_finsetFin n) (fun f ↦ ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact Equiv_fnFinBool_finsetFin_mem_powersetCard_iff n k f

/-- The types `List.Vector α n` and `Fin n → α`are eqivalent by using `List.ofFn`. -/
def Equiv_fnFinBool_listVector (n : ℕ) : List.Vector α n ≃ (Fin n → α) where
  toFun := fun l i ↦ l.val.get (l.prop.symm ▸ i)
  invFun := fun f ↦ ⟨List.ofFn f, List.length_ofFn⟩
  left_inv := fun l ↦ by
    obtain ⟨val, property⟩ := l
    subst property
    simp_rw [List.get_eq_getElem]
    exact Subtype.ext (List.ofFn_getElem val)
  right_inv := fun f ↦ by
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    ext i
    congr <;> simp

lemma card_listVector_card {k n : ℕ} :
    #{v : List.Vector Bool n | v.val.count true = k} = n.choose k := by
  rw [← card_fnFinBool]
  apply card_equiv (Equiv_fnFinBool_listVector n) (fun v ↦ ?_)
  obtain ⟨l, hl⟩ := v
  simp only [mem_filter, mem_univ, true_and, Equiv_fnFinBool_listVector, List.get_eq_getElem,
    Equiv.coe_fn_mk]
  refine ⟨fun h ↦ ?_,fun h ↦ ?_⟩ <;> rw [← h, ← List.count_ofFn_eq_card n _ true] <;> aesop







lemma binom₁_eq_binom₃ : binom₃ = binom₁ := by
  ext p n k
  have h : (List.count true ⁻¹' {k} ∩ {l | l.length = n}) = {l : List Bool | l.length = n ∧ l.count true = k} := by sorry

  rw [binom₁]
  have g (i : List Bool) (s : Set ℕ): (s.indicator (@OfNat.ofNat (ℕ → ℝ≥0∞) 1 One.toOfNat1) ((List.count true i))) = (((List.count true))⁻¹' s).indicator 1 i := by
    rfl
  calc
    ((binom₃ p n) k) = (∑' (i : List Bool),
    {l | l.length = n}.indicator (fun l => ∏' (a : Bool), (coin p) a ^ List.count (α := Bool) a l) i *
      ({k} : Set ℕ).indicator 1 ((List.count true i))) := by
      rw [binom₃, map_apply, toMeasure_apply]
      simp_rw [iidSequence_apply' n (coin p)]
      rfl
    _ = ∑' (i : List Bool),
    (List.count true ⁻¹' {k} ∩ {l | l.length = n}).indicator
      (fun l => ∏' (a : Bool), (coin p) a ^ List.count a l) i := by
        simp_rw [g _ ({k} : Set ℕ)]
        simp_rw [Set.indicator.mul_indicator_eq]
        rw [Set.indicator_indicator]
    _ = ∑' (x : ↑(List.count true ⁻¹' {k} ∩ {l | l.length = n})), ↑p ^ List.count true ↑x * (1 - ↑p) ^ List.count false ↑x := by
        rw [← tsum_subtype]
        simp_rw [tprod_bool, coin_apply, mul_comm]
        simp only [↓reduceIte, Bool.false_eq_true]
    _ = ∑' (x : ↑(List.count true ⁻¹' {k} ∩ {l | l.length = n})), ↑p ^ k * (1 - ↑p) ^ (n - k) := by
        congr
        ext x
        rw [x.prop.1, ← List.length_sub_count_false, x.prop.2, x.prop.1]
    _ = (p ^ k * (1 - p) ^ (n - k)) * (Nat.choose n k) := by
        rw [h]




        simp only [Set.coe_setOf, ENNReal.tsum_const]
        rw [mul_comm]
        congr
        rw [← count_card_eq_choose]
        norm_cast







        simp only [ENNReal.tsum_const, ENat.card_coe_set_eq]
        congr
        norm_cast
        rw [Set.inter_comm, ←  count_encard_eq_choose k n]
        rfl

example (l : List Bool) : List.ofFn l.get = l := by exact List.ofFn_get l

example (f : Fin n → Bool) : (List.ofFn f).length = n := by exact List.length_ofFn

example (f : Fin n → Bool) : (List.ofFn f).get = (fun i ↦ f ⟨i.val, List.length_ofFn ▸ i.prop⟩ ) := by

  apply?

def Equiv_listset_powersetCard {n k : ℕ} :{ l : List Bool | l.length = n ∧ l.count true = k } ≃ {f : Fin n → Bool | (List.ofFn f).count true = k} where
  toFun := fun ⟨l, hl⟩ ↦ ⟨by simp at hl; exact hl.1 ▸ l.get, by
    simp at hl
    simp [hl]


    sorry⟩
  invFun := fun ⟨f, hf⟩ ↦ ⟨List.ofFn f, by
    simp
    simp at hf
    rw [← hf]
  ⟩
  left_inv := by
    intro l
    simp
  right_inv := by
    simp
    intro
    simp


end binom

end MassFunction

-- nonTop

end MeasureTheory
