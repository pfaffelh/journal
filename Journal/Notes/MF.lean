/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib

/-!
# Mass functions

This file is about discrete measures as given by a weight function `α → ℝ≥0∞`.

Construction of monadic `pure`, `map` and `bind` is found as well.

Given `μ : MF α`, `MF.toMeasure` constructs an `Measure α ⊤`,
by assigning each set the sum of the weights of each of its elements.
For this measure, every set is measurable.

## Tags

weight function, discrete measure

-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

@[simp]
lemma Set.indicator_sum_singleton (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = (f x) := by
  rw [← tsum_subtype, tsum_singleton]

@[simp]
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory

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
def support (w : MF α) : Set α :=
  Function.support w

@[simp]
theorem mem_support_iff (w : MF α) (a : α) : a ∈ w.support ↔ w a ≠ 0 := Iff.rfl

theorem apply_eq_zero_iff (w : MF α) (a : α) : w a = 0 ↔ a ∉ w.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (w : MF α) (a : α) : 0 < w a ↔ a ∈ w.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

def toMeasure (w : MF α) : @Measure α ⊤ :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α ⊤ a)

noncomputable instance : Coe (MF α) (@Measure α ⊤) where
  coe w : @Measure α ⊤ := w.toMeasure

noncomputable instance : CoeFun (MF α) (fun _ => Set α → ℝ≥0∞) where
  coe w := w.toMeasure

lemma toMeasure_apply (μ : MF α) (s : Set α) : μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  simp [toMeasure]

lemma toMeasure_apply₁ (μ : MF α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [toMeasure_apply]

lemma toMeasure_apply₂ (μ : MF α) (s : Set α) : μ.toMeasure s =
    ∑' (a : s), (μ a) := by
  simp [toMeasure_apply, tsum_subtype]

@[simp]
lemma toMeasure_apply_singleton (μ : MF α) (a : α) :
    ∑' (i : α), ({a} : Set α).indicator μ i = μ a := by
  rw [← tsum_subtype, tsum_singleton]

@[simp]
lemma toMeasure_apply_singleton' (μ : MF α) (a : α) : μ.toMeasure {a} =
    μ a := by
  simp [toMeasure_apply]

lemma toMeasure_singleton_eq_weight (μ : MF α) : (fun (a : α) ↦ μ.toMeasure {a}) = μ := by
  simp [toMeasure_apply]

theorem toMeasure_injective : (toMeasure : MF α → @Measure α ⊤).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton' μ, ← toMeasure_apply_singleton' ν, h]

@[simp]
theorem toMeasure_inj {μ ν : MF α} : μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

theorem toMeasure_apply_eq_zero_iff {μ : MF α} {s : Set α} : μ.toMeasure s = 0 ↔ Disjoint μ.support s := by
  rw [toMeasure_apply₁, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

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
theorem toMeasure_apply_inter_support {μ : MF α} {s : Set α} :
    μ.toMeasure (s ∩ μ.support) = μ.toMeasure s := by
  simp only [toMeasure_apply, support]
  apply tsum_congr (fun a ↦ ?_)
  aesop

theorem toMeasure_mono {s t : Set α} {μ : MF α} (h : s ∩ μ.support ⊆ t) : μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

@[simp]
theorem restrict_toMeasure_support {μ : MF α} : μ.toMeasure.restrict μ.support = μ.toMeasure := by
  sorry

theorem toMeasure_apply_eq_of_inter_support_eq {μ : MF α} {s t : Set α} (h : s ∩ μ.support = t ∩ μ.support) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support]
  nth_rw 2 [← toMeasure_apply_inter_support]
  rw [h]

@[simp]
theorem toMeasure_apply_finset {μ : MF α} (s : Finset α) : μ.toMeasure s = ∑ x ∈ s, μ x := by
  simp [toMeasure_apply₁]
  rw [tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

lemma toMeasure_apply_univ (μ : MF α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]


lemma apply_univ' (μ : MF α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d): μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ s hs₀

end MF



section IsProbabilityMeasure

lemma isProbabilityMeasure_iff_hasSum {p : MF α} :
    IsProbabilityMeasure p.toMeasure ↔ HasSum p 1 := by
  rw [isProbabilityMeasure_iff, MF.toMeasure_apply_univ, Summable.hasSum_iff ENNReal.summable]

lemma isProbabilityMeasure_iff_tsumOne {μ : MF α} : IsProbabilityMeasure μ.toMeasure ↔ ∑' a, μ a = 1 := by
  rw [isProbabilityMeasure_iff_hasSum, Summable.hasSum_iff ENNReal.summable]

theorem toMeasure_ne_top (p : MF α) (h : IsProbabilityMeasure p.toMeasure) (s : Set α) : p.toMeasure s ≠ ∞ := by
  exact measure_ne_top p.toMeasure s

example : (0 : ℝ≥0∞) ≠ 1 := by
  exact zero_ne_one' ℝ≥0∞

@[simp]
theorem coe_ne_zero (p : MF α) (h : IsProbabilityMeasure p.toMeasure): ⇑p ≠ 0 := by
  by_contra h'
  rw [isProbabilityMeasure_iff] at h
  have g : p.toMeasure Set.univ = 0 := by
    rw [h']
    simp
  apply zero_ne_one' ℝ≥0∞
  rw [← g, ← h]

theorem hasSum_coe_one (p : PMF α) : HasSum p 1 :=
  p.2

@[simp]
theorem tsum_coe (p : PMF α) : ∑' a, p a = 1 :=
  p.hasSum_coe_one.tsum_eq

theorem tsum_coe_ne_top (p : PMF α) : ∑' a, p a ≠ ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top

theorem tsum_coe_indicator_ne_top (p : PMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]
theorem coe_ne_zero (p : PMF α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

@[simp]
theorem support_nonempty (p : PMF α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]
theorem support_countable (p : PMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)


theorem apply_eq_one_iff (p : PMF α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
    fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero, ENNReal.summable.tsum_ne_zero_iff]
    exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]

theorem coe_le_one (p : PMF α) (a : α) : p a ≤ 1 := by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]

theorem apply_ne_top (p : PMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

theorem apply_lt_top (p : PMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)


end IsProbabilityMeasure




section OuterMeasure

open OuterMeasure

/-- Construct an `OuterMeasure` from a `PMF`, by assigning measure to each set `s : Set α` equal
  to the sum of `p x` for each `x ∈ α`. -/
def toOuterMeasure (p : PMF α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x

variable (p : PMF α) (s : Set α)

theorem toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

@[simp]
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ := by
  refine eq_top_iff.2 <| le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[simp]
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x ∈ s, p x := by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _

theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a := by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
  · classical exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · classical exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl

theorem toOuterMeasure_injective : (toOuterMeasure : PMF α → OuterMeasure α).Injective :=
  fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[simp]
theorem toOuterMeasure_inj {p q : PMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff

theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s := by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices ∀ (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.notMem_subset h ha

@[simp]
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

/-- Slightly stronger than `OuterMeasure.mono` having an intersection with `p.support`. -/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[simp]
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

end OuterMeasure

section Measure

/-- Since every set is Carathéodory-measurable under `PMF.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`. -/
def toMeasure [MeasurableSpace α] (p : PMF α) : Measure α :=
  p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

variable [MeasurableSpace α] (p : PMF α) {s : Set α}

theorem toOuterMeasure_apply_le_toMeasure_apply (s : Set α) : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s

theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs

theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)

theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]

theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_eq_zero_iff]

theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s

theorem toMeasure_mono {t : Set α} (hs : MeasurableSet s)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[simp]
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s :=
  (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[simp]
theorem restrict_toMeasure_support : p.toMeasure.restrict p.support = p.toMeasure := by
  ext s hs
  rw [Measure.restrict_apply hs, p.toMeasure_apply_inter_support hs]

theorem toMeasure_apply_eq_of_inter_support_eq {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

theorem toMeasure_injective : (toMeasure : PMF α → Measure α).Injective := by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x,
    ← q.toMeasure_apply_singleton x <| measurableSet_singleton x, h]

@[simp]
theorem toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff

theorem toMeasure_apply_eq_toOuterMeasure (s : Set α) : p.toMeasure s = p.toOuterMeasure s := by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support, Measure.restrict_apply' p.support_countable.measurableSet,
    p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_inter_support]

@[simp]
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x ∈ s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)

theorem toMeasure_apply_eq_tsum (s : Set α) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[deprecated (since := "2025-06-23")] alias toMeasure_apply_of_finite := toMeasure_apply_eq_tsum

@[simp]
theorem toMeasure_apply_fintype (s : Set α) [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

end MeasurableSingletonClass

end Measure

end PMF

namespace MeasureTheory

open PMF

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `PMF`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toPMF [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : PMF α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]

theorem toPMF_apply (x : α) : μ.toPMF x = μ {x} := rfl

@[simp]
theorem toPMF_toMeasure : μ.toPMF.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs, ← μ.tsum_indicator_apply_singleton s hs]
    rfl

end Measure

end MeasureTheory

namespace PMF

/-- The measure associated to a `PMF` by `toMeasure` is a probability measure. -/
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : PMF α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)

@[simp]
theorem toMeasure_toPMF : p.toMeasure.toPMF = p :=
  PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x), p.toMeasure.toPMF_apply]

theorem toMeasure_eq_iff_eq_toPMF (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPMF := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

theorem toPMF_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPMF = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

end PMF
