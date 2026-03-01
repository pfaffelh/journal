/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

-- #34138 feat(MeasureTheory): Introduce Mass Function α giving rise to a Measure α ⊤`
-- #34239: giry monad extensions, bind and join
-- #34702: cardinality of {l : List.Vector Bool n | List.Vector.countFin true l = k}

import Mathlib
#check List.range

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

-- to List

namespace List

#loogle List.zipWith, List.map

@[simp]
lemma map_eq_replicateZipWith (l : List α) (f : α → β) :
  ((List.replicate l.length f).zipWith (fun a b ↦ a b) l) = (l.map f) := by
  induction l with
  | nil => simp
  | cons a l hl =>
  rw [map_cons, length_cons, ← hl]
  rfl

/-
lemma tprod_eq_prod_of_pow_count (l : List α) (f : α → ℝ≥0∞) [DecidableEq α] : (∏' a, (f a)^(l.count a)) = (∏ a ∈ l.toFinset, f a ^ (l.count a)) := by
  rw [tprod_eq_prod (fun b hb ↦ ?_)]
  rw [List.mem_toFinset, ← List.count_eq_zero] at hb
  rw [hb, pow_zero]

#check List.prod_map_eq_pow_single
-/
/-
lemma map_prod_eq_count {M : Type u_4} [CommMonoid M] (l : List α) (f : α → M) [DecidableEq α] : (map f l).prod = ∏ a ∈ l.toFinset, (f a) ^ (l.count a) := by
  exact Finset.prod_list_map_count l f
-/

/-
lemma tsum_eq_sum_of_mul_count [DecidableEq α] (l : List α) (f : α → ℝ≥0∞) : (∑' a, (l.count a) * (f a)) = (∑ a ∈ l.toFinset, (l.count a) * f a) := by
  rw [tsum_eq_sum (fun b hb ↦ ?_)]
  rw [List.mem_toFinset, ← List.count_eq_zero] at hb
  rw [hb, CharP.cast_eq_zero, zero_mul]

#check List.sum_map_ite_eq

lemma map_sum_eq_count [DecidableEq α] (l : List α) (f : α → ℝ≥0∞) : (map f l).sum = ∑ a ∈ l.toFinset, (f a) * (l.count a) := by
  simp_rw [Finset.sum_list_map_count, nsmul_eq_mul]

-/
end List

-- to List.Vector

namespace List.Vector

#check List.traverse_nil

@[simp]
lemma traverse_nil {F : Type u → Type u} [inst: Applicative F] {α' β' : Type u} (f : α' → F β') : traverse (t := flip List.Vector 0) f (nil (α := α')) = (Pure.pure nil) := by
  rfl

-- #check List.sequence_nil

@[simp]
lemma sequence_nil {F : Type u → Type u} [inst: Applicative F] {α : Type u} : sequence (t := flip List.Vector 0) (nil (α := F α)) = (Pure.pure nil) := by
  rfl

#check List.traverse_cons

@[simp]
lemma traverse_cons {F : Type u → Type u} [Applicative F] {α' β' : Type u} (f : α' → F β') {n : ℕ} (a : α') (l : List.Vector α' n) : traverse (t := flip List.Vector (n + 1)) f (a ::ᵥ l) = (fun x1 x2 => x1 ::ᵥ x2) <$> f a <*> traverse (t := flip List.Vector n) f l := by
  obtain ⟨l1, l2⟩ := l
  subst l2
  rfl

-- #check List.sequence_cons

@[simp]
lemma sequence_cons {F : Type u → Type u} [Applicative F] {α : Type u} {n : ℕ} (l : List.Vector (F α) n) (a : F α) : sequence (t := flip List.Vector (n + 1)) (a ::ᵥ l) = cons <$> a <*> (sequence (t := flip List.Vector n) l) := (traverse_cons id a l)

lemma Injective_toList {n : ℕ} : Injective (toList : List.Vector α n → List α) := by
  intro l l' h
  obtain ⟨lv, lp⟩ := l
  congr

@[simp]
lemma eq_iff {n : ℕ} {l l' : List.Vector α n} :
  l = l' ↔ l.toList = l'.toList := by
  rw [Injective.eq_iff Injective_toList]

@[simp]
lemma cons.injEq {n : ℕ} (head : α) (tail : List.Vector α n) (head' : α) (tail' : List.Vector α n) :
  (head ::ᵥ tail = head' ::ᵥ tail') = (head = head' ∧ tail = tail') := by
  simp [List.cons.injEq]

@[simp]
lemma nil_iff (l : List.Vector α 0) : l = nil := by
  simp

@[simp]
lemma nil_val : (nil (α := α)).toList = [] := by
  rfl

@[simp]
lemma toList_replicate {n : ℕ} (a : α) : (replicate n a).toList = List.replicate n a := by
  rfl

def countFin [BEq α] {n : ℕ} (a : α) : (l : List.Vector α n) → Fin (n + 1) := fun l ↦
  ⟨l.toList.count a, lt_of_le_of_lt l.toList.count_le_length (lt_of_le_of_lt l.prop.le (lt_add_one n))⟩

lemma countFin_eq_count₁ [BEq α] {n : ℕ} (l : List.Vector α n) (a : α) (k : Fin (n + 1)) : (countFin a l) = k ↔ (l.toList.count (α := α) a) = k := by
  exact eq_iff_eq_of_cmp_eq_cmp rfl


#check List.Vector.toList

end List.Vector

-- to Set.indicator

--unused...
lemma indicator_mul (a : α) (b : β) (s : Set α) (t : Set β) [Decidable (a ∈ s ∧ b ∈ t)
] (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) : (if (a ∈ s ∧ b ∈ t) then ((f a) * (g b)) else 0) = s.indicator f a * t.indicator g b := by
  simp only [Set.indicator]
  aesop

-- to Function

lemma Function.comp_apply'  {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} : (f ∘ fun x => g x) = fun x => f (g x) := by
  -- simp_rw [← Function.comp_apply]
  rfl

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

theorem apply_le_one {w : MassFunction α} [IsProbabilityMeasure w.toMeasure] (a : α) : w a ≤ 1 := by
  have h : w.toMeasure Set.univ = 1 := by
    rw [← isProbabilityMeasure_iff]
    infer_instance
  rw [← toMeasure_apply_singleton w a, ← h]
  exact measure_mono (Set.subset_univ _)

end IsFiniteOrProbabilityMeasure

end MassFunction


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

lemma map_toMeasure_apply (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = μ.toMeasure (g⁻¹' s) := by
  rw [map_coe]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply (μ : MassFunction α) (g : α → β) (x : β) : μ.map g x = μ.toMeasure (g⁻¹' {x}) := by
  rw [← toMeasure_apply_singleton (map g μ)]
  apply map_toMeasure_apply

lemma map_toMeasure_apply₁ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : α), μ a * s.indicator 1 (g a) := by
  rw [map_toMeasure']
  simp

lemma map_apply₂ (μ : MassFunction α) (g : α → β) (x : β) : μ.map g x = ∑' (a : α), μ a * ({x} : Set β).indicator 1 (g a) := by
  rw[map_apply]
  rw [toMeasure_apply]
  apply tsum_congr (fun b ↦ by rfl)

lemma map_toMeasure_apply₂ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : α), (g⁻¹' s).indicator μ a := by
  rw [map_toMeasure']
  simp only [MeasurableSpace.measurableSet_top, sum_apply, smul_apply, dirac_apply', smul_eq_mul]
  apply tsum_congr (fun b ↦ ?_)
  exact Set.indicator.mul_indicator_eq μ (fun b => s (g b)) b

lemma map_toMeasure_apply₃ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (b : s), μ.toMeasure (g⁻¹' {b.val}) := by
  rw [toMeasure_apply₂]
  rfl

lemma map_toMeasure_apply₄ (μ : MassFunction α) (g : α → β) (s : Set β) : (μ.map g).toMeasure s = ∑' (a : g⁻¹' s), (μ a.val) := by
  rw [map_toMeasure_apply, toMeasure_apply₂]

theorem id_map (μ : MassFunction α) :
μ.map id = μ :=
  toMeasure_ext <| (map_coe μ id) ▸ Measure.map_id

theorem isProbabilityMeasure_map_toMeasure (μ : MassFunction α) [IsProbabilityMeasure μ.toMeasure] (f : α → β) : IsProbabilityMeasure (μ.map f).toMeasure := by
  rw [map_coe]
  exact @isProbabilityMeasure_map _ _ ⊤ ⊤ μ.toMeasure _ f
    <| @AEMeasurable.of_discrete _ _ ⊤ ⊤ _ _ _

end map

section lintegral

lemma lintegral_eq_toMeasure (μ : MassFunction α) (g : α → ℝ≥0∞) : ∫⁻ (a : α), g a ∂ μ.toMeasure = ∑' (a : α), μ a * (g a) := by
  rw [toMeasure]
  simp

-- TODO: integral_map

lemma lintegral_map (μ : MassFunction α) (g : α → β) (f : β → ℝ≥0∞) : ∫⁻ (a : β), (f a) ∂ (map g μ).toMeasure = ∫⁻ (a : α), f (g a) ∂ μ.toMeasure := by
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
  rw [MeasureTheory.lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
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

lemma join_toMeasure_apply (m : MassFunction (MassFunction α)) (s : Set α) : m.join.toMeasure s = ∑' (μ : MassFunction α), m μ * μ.toMeasure s := by
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

lemma bind_toMeasure_apply_eq_toMeasure (μ : MassFunction α) (g : α → MassFunction β) (s : Set β) : (μ.bind g).toMeasure s = μ.toMeasure.bind (toMeasure ∘ g) s := by
  rw [bind, Measure.bind, join_coe, ← Measure.map_map (hg := by measurability) (hf := by measurability), map_coe]

lemma bind_coe (μ : MassFunction α) (g : α → MassFunction β)  : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  apply @Measure.ext _ ⊤
  intro _ _
  rw [bind_toMeasure_apply_eq_toMeasure]


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

lemma bind_toMeasure (μ : MassFunction α) (g : α → MassFunction β) : (μ.bind g).toMeasure  = sum (fun a ↦ (μ a) • (g a).toMeasure) := by
  apply @Measure.ext _ ⊤
  intro s _
  rw [bind_toMeasure_apply_eq_toMeasure, toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_toMeasure_apply (μ : MassFunction α) (g : α → MassFunction β) (s : Set β) : (μ.bind g).toMeasure s = ∑' (a : α), μ a * (g a).toMeasure s := by
  rw [bind_toMeasure]
  simp

@[simp]
lemma bind_apply (μ : MassFunction α) (g : α → MassFunction β) (x : β) : (μ.bind g) x = ∑' (a : α), μ a * (g a) x := by
  simp_rw [← toMeasure_apply_singleton (μ.bind g) x, ← toMeasure_apply_singleton _ x, bind_toMeasure_apply]

lemma join_map_map (m : MassFunction (MassFunction α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  rw [← toMeasure_apply_singleton (m.bind (map f)), ← toMeasure_apply_singleton (map f m.join), bind_toMeasure_apply, map_toMeasure_apply, join_toMeasure_apply]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_singleton, MassFunction.map_apply]


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

lemma isProbabilityMeasure_bind_toMeasure {m : MassFunction α} [IsProbabilityMeasure m.toMeasure] {f : α → MassFunction β} (hf₁ : ∀ (a : α), IsProbabilityMeasure (f a).toMeasure) : IsProbabilityMeasure (m.bind f).toMeasure := by
  rw [bind_coe]
  refine @isProbabilityMeasure_bind β α ⊤ ⊤ m.toMeasure _ (toMeasure ∘ f) AEMeasurable.of_discrete ?_
  simp [hf₁]


end bind

section pure

/-- The pure `MassFunction` puts all the mass lies in one point. The value of `pure a` is `1` at `a` and
`0` elsewhere. In other words, `pure ∘ toMeasure = Measure.dirac`. -/
noncomputable def pure (a : α) : MassFunction α := ({a} : Set α).indicator 1

lemma pure_apply (a : α) : pure a = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma pure_apply_self {a : α} : pure a a = 1 := by
  rw [pure_apply]
  simp

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

theorem pure_bind (a : α) (f : α → MassFunction β) :
(pure a).bind f = f a := by
  apply toMeasure_ext
  rw [bind_coe, pure_coe, dirac_bind (hf :=  by measurability)]
  rfl

theorem bind_pure (μ : MassFunction α) :
μ.bind pure = μ := by
  apply toMeasure_ext
  rw [bind_coe, Measure.bind, toMeasure_pure_eq_dirac, ← Measure.bind, Measure.bind_dirac]

@[simp, monad_norm]
lemma bind_pure_comp (f : α → β) (μ : MassFunction α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply toMeasure_ext
  simp_rw [bind_coe, map_coe, Function.comp_apply', pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := by measurability)]

lemma isProbabilityMeasure_pure_toMeasure (a : α) : IsProbabilityMeasure ((pure a).toMeasure) := by
  rw [pure_coe]
  exact @dirac.isProbabilityMeasure α ⊤ a

end pure

section seq

variable (q : MassFunction (α → β)) (p : Unit → MassFunction α) (b : β)

/-- The monadic sequencing operation for `MassFunction`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q : MassFunction (α → β)) (p :  Unit → MassFunction α) : MassFunction β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

@[simp, monad_norm]
lemma bind_map_eq_seq (q : MassFunction (α → β)) (p : Unit → MassFunction α) : seq q p = q.bind (fun m => (p ()).map m) := by
  simp_rw [← bind_pure_comp]
  rfl

@[simp]
theorem seq_apply [DecidableEq β] : seq q p b = ∑' (f : α → β) (a : α), q f * if b = f a then (p ()) a else 0 := by
  simp_rw [seq, bind_apply, pure_apply, Set.indicator, Set.mem_singleton_iff, ← ENNReal.tsum_mul_left]
  repeat apply tsum_congr (fun f ↦ ?_)
  split_ifs <;> simp

theorem seq_apply₁ [DecidableEq β] : seq q p b = ∑' (f : α → β) (a : f⁻¹' {b}), q f * (p ()) a := by
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

lemma isProbabilityMeasure_seq_toMeasure [IsProbabilityMeasure q.toMeasure] [IsProbabilityMeasure (p ()).toMeasure] : IsProbabilityMeasure (seq q p).toMeasure := by
  rw [bind_map_eq_seq]
  refine @isProbabilityMeasure_bind_toMeasure β (α → β) q (by infer_instance) (fun m => map m (p ())) (fun a ↦ isProbabilityMeasure_map_toMeasure (p ()) a)

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






-- MF
lemma cons_map_seq_apply {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) (l : List.Vector α (n + 1)): (List.Vector.cons <$> ν <*> μs) l = ∑' (a' : α), ν a' * ∑' (l' : List.Vector α n), μs l' * pure (a' ::ᵥ l') l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]

lemma pure_cons_apply_cons [DecidableEq α] {n : ℕ} (a a' : α) (l l' : List.Vector α n) : pure (a' ::ᵥ l') (a ::ᵥ l) = (if a = a' ∧ l = l' then 1 else 0) := by
  rw [pure, Set.indicator]
  simp

-- MF
lemma cons_map_seq_apply_cons [DecidableEq α] {n : ℕ} (μs : MassFunction (List.Vector α n)) (ν : MassFunction α) (l : List.Vector α n) (a : α) : (List.Vector.cons <$> ν <*> μs) (a ::ᵥ l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [pure_cons_apply_cons]
  have h (a_1 : α) (a_2 : List.Vector α n) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List.Vector α n)).indicator (1 : List.Vector α n → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]

-- MF
lemma sequence_cons_apply_cons [DecidableEq α] {n : ℕ} (μs : List.Vector (MassFunction α) n) (ν : MassFunction α) (l : List.Vector α n) (a : α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) (a ::ᵥ l) = (ν a) * ((sequence (t := flip List.Vector n) μs) l) := by
  rw [List.Vector.sequence_cons]
  exact cons_map_seq_apply_cons (sequence (t := flip List.Vector n) μs) ν l a

lemma prod_zipWith {n : ℕ} (f : List.Vector (α → ℝ≥0∞) n) (l : List.Vector α n) : List.prod (f.zipWith (· ·) l).toList = ∏ i, (f.get i) (l.get i) := by
  simp

  sorry

lemma sequence_apply₀ [DecidableEq α] {n : ℕ} (μs : List.Vector (MassFunction α) n) (l : List.Vector α n) :
    (sequence (t := flip List.Vector n) μs) l = List.prod (μs.zipWith (· ·) l).toList :=
  by
  induction μs with
  | nil =>
    simp only [List.Vector.nil_iff, List.Vector.sequence_nil]
    rw [← pure_eq_pure]
    simp
  | cons hl =>
    rw [← List.Vector.cons_head_tail l, sequence_cons_apply_cons]
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one,
      List.Vector.zipWith_toList, List.Vector.toList_cons]
    rw [List.zipWith_cons_cons]
    simp [hl]

lemma sequence_apply₁ [DecidableEq α] {n : ℕ} (μs : List.Vector (MassFunction α) n) (l : List.Vector α n) :
    (sequence (t := flip List.Vector n) μs) l = ∏ i, (μs.get i) (l.get i) :=
  by
  rw [sequence_apply₀]
  exact prod_zipWith μs l

-- TODO: define marginal distributions

lemma isProbabilityMeasure_sequence_toMeasure {n : ℕ} (μs : List.Vector (MassFunction α) n) [∀ i, IsProbabilityMeasure (μs.get i).toMeasure] : IsProbabilityMeasure (sequence (t := flip List.Vector n) μs).toMeasure := by
  induction n with
  | zero =>
    simp [monad_norm]
    apply isProbabilityMeasure_pure_toMeasure
  | succ n hn =>
    let μs.tail' : List.Vector (_) n := μs.tail
    have g : μs.tail = μs.tail' := rfl
    rw [← List.Vector.cons_head_tail μs, List.Vector.sequence_cons, ← seq_eq_seq, ← map_eq_map, ← List.Vector.get_zero μs, g]
    expose_names
    have h (i : Fin n) : IsProbabilityMeasure (μs.tail'.get i).toMeasure := by
      rw [← g, List.Vector.get_tail]
      exact inst (Fin.succ i)
    exact @isProbabilityMeasure_seq_toMeasure (β := List.Vector α n.succ) (α := List.Vector α n)
      (q := map (β := List.Vector α n → List.Vector α n.succ) (α := α) List.Vector.cons (μs.get 0))
      (p := fun (_ : Unit) ↦ sequence (t := flip List.Vector n) μs.tail)
      (isProbabilityMeasure_map_toMeasure (μs.get 0) List.Vector.cons) (@hn μs.tail' h)

end sequence

section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : MassFunction α) : MassFunction (List.Vector α n) := sequence (t := flip List.Vector n) (List.Vector.replicate n μ)

lemma iidSequence_apply [DecidableEq α] (n : ℕ) (μ : MassFunction α) (l : List.Vector α n) :
    (iidSequence n μ) l = (l.map μ).toList.prod := by
  rw [iidSequence, List.Vector.toList_map, ← List.map_eq_replicateZipWith,
    List.Vector.toList_length]
  rw [sequence_apply₀]
  congr

lemma iidSequence_apply₁ {n : ℕ} {μ : MassFunction α} [DecidableEq α] {l : List.Vector α n} :
    iidSequence n μ l = (∏ a ∈ l.toList.toFinset, (μ a) ^ (List.Vector.countFin a l).val) := by
  rw [iidSequence_apply n μ l]
  rw [List.Vector.toList_map]
  simp_rw [List.Vector.countFin]
  exact Finset.prod_list_map_count l.toList μ

lemma iidSequence_apply₂ (n : ℕ) (μ : MassFunction α) [DecidableEq α] (l : List.Vector α n) :
    iidSequence n μ l = (∏' (a : α), (μ a) ^ (List.Vector.countFin a l).val) := by
  simp_rw [List.Vector.countFin]
  have hf : ∀ b ∉ l.toList.toFinset, μ b ^ (l.toList.count b) = 1 := by
    simp_rw [List.mem_toFinset, ← List.count_eq_zero]
    exact fun b hb ↦ hb ▸ pow_zero (μ b)
  rw [tprod_eq_prod hf]
  exact iidSequence_apply₁

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

lemma Bool_isProbabilityMeasure_not (μ : MassFunction Bool) [IsProbabilityMeasure μ.toMeasure] (b : Bool) : μ (!b) = 1 - μ b := by
  refine ENNReal.eq_sub_of_add_eq' one_ne_top ?_
  have h : μ.toMeasure Set.univ = μ true + μ false := by
    simp
  cases' b with h
  · rw [Bool.not_false, ← h, ← isProbabilityMeasure_iff]
    infer_instance
  · rw [Bool.not_true, add_comm, ← h, ← isProbabilityMeasure_iff]
    infer_instance

example (a b : Bool) : (!a) = b ↔ ¬a = b := by
  exact not_eq

lemma Bool_ext (μ ν : MassFunction Bool) [IsProbabilityMeasure μ.toMeasure] [IsProbabilityMeasure ν.toMeasure] (b : Bool) (h : μ b = ν b) : μ = ν := by
  ext a
  cases h' : decide (b = a)
  · simp only [decide_eq_false_iff_not] at h'
    change b ≠ a at h'
    rw [← not_eq] at h'
    rw [← h']
    rw [Bool_isProbabilityMeasure_not μ b]
    rw [Bool_isProbabilityMeasure_not ν b]
    rw [h]
  · simp at h'
    rw [← h', h]

@[simp]
lemma Bool_and : Bool.and true = id := by
  rfl

@[simp]
lemma Bool_false : Bool.and false = (fun _ ↦ false) := rfl

#check List.all


def List.Vector.all {n : ℕ} (l : List.Vector α n) (f : α → Bool) : Bool := l.toList.all f

def List.Vector.any {n : ℕ} (l : List.Vector α n) (f : α → Bool) : Bool := l.toList.any f

lemma List.Vector.all_id_preimage_true {n : ℕ} : (flip List.Vector.all id)⁻¹' {true} = {List.Vector.replicate n true} := by
  ext x
  sorry

lemma List.Vector.ext {n : ℕ} (l : List α) (l' : List.Vector α n) : l = l'.toList ↔ ∃ (h : l.length = n),  ∀ (i : Fin l.length), l.get i = l'.get (h ▸ i) := by
  sorry

example (l : List ℝ≥0∞) : l.prod = ∏ i, l.get i := by
  simp only [List.get_eq_getElem, Fin.prod_univ_getElem]

lemma multipleCoins_and_eq_coin {n : ℕ} (p : List.Vector ℝ≥0∞ n) (hp : ∀ i, p.get i ≤ 1) : map (flip List.Vector.all id) (sequence (t := flip List.Vector n) (List.Vector.map coin p)) = coin (p.toList.prod) := by
  haveI h₁ : IsProbabilityMeasure (map (flip List.Vector.all id) (sequence (t := flip List.Vector n) (List.Vector.map coin p))).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p.toList.prod)).toMeasure := by
    apply isProbabilityMeasure_coin
    have g : ∀ i, p.toList.get i ≤ 1 := by sorry
    simp [g]


    sorry
  apply Bool_ext _ _ true
  obtain ⟨p1, p2⟩ := p
  subst p2
  rw [map_apply]
  rw [List.Vector.all_id_preimage_true]
  rw [toMeasure_apply_singleton]
  rw [sequence_apply₁]
  simp [coin]
  rw [← Fin.prod_univ_getElem]
  exact rfl



/- multiple coins-/
lemma multipleCoins_and_eq_coin' {n : ℕ} (p : List ℝ≥0 ) (hp : ∀ i, p.get i ≤ 1) : (p.map coin).andM = coin (p.prod) := by
  haveI h₁ : IsProbabilityMeasure (List.andM (p.map coin)).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p.prod)).toMeasure := by sorry
  apply Bool_ext _ _ true
  simp only [List.pure_def, List.bind_eq_flatMap]



  sorry




lemma twoCoins_and_eq_coin (p q : ℝ≥0) (hp : p ≤ 1) (hq _: q ≤ 1) : Bool.and <$> (coin p)  <*>  (coin q) = coin (p * q) := by
  simp [monad_norm]
  haveI h₁ : IsProbabilityMeasure ((coin ↑p >>= fun x => coin ↑q >>= Pure.pure ∘ x.and)).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p * q)).toMeasure := by sorry
  apply Bool_ext _ _ true
  simp_rw [← bind_eq_bind, bind_apply, tsum_bool]
  simp [coin]
  rw [← pure_eq_pure, pure_apply, Set.indicator]
  simp


-- now we come to multiple coins
lemma sequence_coin_apply (p : ℝ≥0∞) (n : ℕ) (l : List.Vector Bool n) : (iidSequence n (coin p)) l = p ^ (List.Vector.countFin true l).val * (1 - p) ^ (List.Vector.countFin false l).val := by
  rw [iidSequence_apply₂ n (coin p)]
  simp [coin]

lemma massFunctionBool_eq_coin (P : MassFunction Bool) [IsProbabilityMeasure P.toMeasure] : P = coin (P true) := by
  haveI h : IsProbabilityMeasure (coin (P true)).toMeasure := isProbabilityMeasure_coin (P true) (apply_le_one true)
  exact Bool_ext P (coin (P true)) true (by rfl)

end coin

section uniform

variable {ι : Type*} [Fintype ι] [Inhabited ι]

def uniform : MassFunction ι := fun _ ↦ (Finset.univ : Finset ι).card⁻¹

lemma isProbabilityMeasure_uniform : IsProbabilityMeasure (uniform (ι := ι)).toMeasure := by
  rw [isProbabilityMeasure_iff_tsumOne]
  simp [uniform]
  refine ENNReal.mul_inv_cancel ?_ ?_
  simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  simp

end uniform


section binom

example (x y : ℕ) (hx : x < n) (hy : y < m) : x + y < n + m -1 := by
  linarith

example (n : ℕ) (x : Fin (n + 1)) (y : Bool) : x.val + y.toNat < (n + 1) + 1 := by
  refine Nat.add_le_add




-- Defining the binomial distribution inductively
noncomputable def binom_ind (p : ℝ≥0∞) (n : ℕ) : MassFunction (Fin (n + 1)) := match n with
  | .zero => pure 0
  | .succ n => do
    let X ← binom_ind p n
    let Y ← (coin p)
    return ⟨X.val + Y.toNat, by linarith⟩


fun k ↦ (p ^ k.val * (1 - p) ^ (n - k.val)) * (Nat.choose n k)

-- Defining the binomial distribution via the mass function
noncomputable def binom₁ (p : ℝ≥0∞) (n : ℕ) : MassFunction (Fin (n + 1)) := fun k ↦ (p ^ k.val * (1 - p) ^ (n - k.val)) * (Nat.choose n k)

example (f : ℕ → ℝ≥0∞) : ∑' (k : Fin (n + 1)), f k = ∑ (k ∈ Finset.range (n + 1)), f k := by
  simp only [tsum_fintype]
  exact Fin.sum_univ_eq_sum_range f (n + 1)

lemma isProbabilityMeasure_binom₁ (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : IsProbabilityMeasure (binom₁ p n).toMeasure := by
  simp_rw [isProbabilityMeasure_iff_tsumOne, binom₁]
  simp only [tsum_fintype]
  rw [Fin.sum_univ_eq_sum_range (fun a ↦ p ^ a * (1 - p) ^ (n - a) * ↑(n.choose a)) (n + 1)]
  rw [ ← add_pow p (1 - p) n]
  simp only [h, add_tsub_cancel_of_le, one_pow]

-- Defining the binomial distribution as the count of trues in a sequence of Bernoulli trials
noncomputable def binom₂ (p : ℝ≥0∞) (n : ℕ) : MassFunction (Fin (n + 1)) := (iidSequence n (coin p)).map (List.Vector.countFin true)

open Finset

-- #34702
lemma List.card_idxsOf_toFinset_eq_count {α : Type*} [BEq α] (l : List α) (a : α) :
    (l.idxsOf a).toFinset.card = l.count a := by
  rw [List.card_toFinset, List.Nodup.dedup List.nodup_idxsOf, List.length_idxsOf]

-- #34702
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

-- #34702
/-- For some `Fintype ι`, there is (computably) a bijection `ι → Bool` and `Finset ι` by using
`s : Finset ι` as the set where the `f : ι → Bool` is `true`. -/
def Equiv.fnBool_finset {ι : Type*} [DecidableEq ι] [Fintype ι] : (ι → Bool) ≃ (Finset ι) where
  toFun := fun f ↦ Finset.univ.filter (f · = true)
  invFun := fun s i ↦ decide (i ∈ s)
  left_inv := fun l ↦ by simp
  right_inv := fun l ↦ by simp

-- #34702
lemma Equiv_fnBool_finset_mem_powersetCard_iff  {ι : Type*} [DecidableEq ι] [Fintype ι] (k : ℕ) (f : ι → Bool) :
    #{i | f i = true} = k ↔ (Equiv.fnBool_finset) f ∈ powersetCard k univ := by
  simp [Equiv.fnBool_finset]

example : Equiv Bool Prop := by exact Equiv.propEquivBool.symm

-- #34702
/-- For some `Fintype ι`, the number of maps `f : ι → Bool` with `#{i | f i} = k` equals `n.choose k`. -/
-- must stay here
lemma card_fnBool {ι : Type*} [DecidableEq ι] [Fintype ι] {k : ℕ} : #{ f : ι → Bool | #{i | f i} = k } = (univ : Finset ι).card.choose k := by
  -- conv => right; rw [← card_fin n]
  rw [← card_powersetCard k (univ : Finset ι)]
  apply card_equiv (Equiv.fnBool_finset) (fun i ↦ ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact Equiv_fnBool_finset_mem_powersetCard_iff k i

-- #34702
lemma card_listVector_card {k n : ℕ} :
    #{v : List.Vector Bool n | v.toList.count true = k} = n.choose k := by
  rw [← card_fin n, ← card_fnBool, card_fin n]
  apply card_equiv (Equiv.vectorEquivFin _ n) (fun v ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Equiv.vectorEquivFin, Equiv.coe_fn_mk]
  refine ⟨fun h ↦ ?_,fun h ↦ ?_⟩ <;> rw [← h, ← List.count_ofFn_eq_card _ _ true] <;> congr <;>
  rw [← List.ofFn_get (l :=  v.toList)] <;> aesop

lemma binom₂_eq_binom₁ : binom₂ = binom₁ := by
  ext p n k
  let s (k : Fin (n + 1)) : Finset (List.Vector Bool n) := {l : List.Vector Bool n | (List.Vector.countFin true l) = k}
  have hs (k : Fin (n + 1)) : ((fun (l : List.Vector Bool n) => List.Vector.countFin true l) ⁻¹' {k}) = s k := by
    aesop
  have ht (k : Fin (n + 1)) : ∀ x ∈ s k, List.Vector.countFin true x = k := by
    aesop
  have hf (k : Fin (n + 1)) : ∀ x ∈ s k, List.Vector.countFin false x = n - k := by
    intro ⟨x1, x2⟩ hx
    refine Nat.eq_sub_of_add_eq' ?_
    rw [← ht k ⟨x1, x2⟩ hx, List.Vector.countFin, List.Vector.countFin, List.count_true_add_count_false, List.Vector.toList_mk, x2]
  rw [binom₁, binom₂, map_apply, toMeasure_apply]
  simp_rw [iidSequence_apply₂ n (coin p), tprod_bool, coin_apply]
  conv => left; left; intro i; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hs, Set.indicator.mul_indicator_eq (f := fun (i : List.Vector Bool n) ↦ (1 - p) ^ (List.Vector.countFin false i).val * p ^ (List.Vector.countFin true i).val) (a := i)]
  rw [tsum_eq_sum (s := s k), ← Finset.tsum_subtype]
  conv =>
    left; left; intro x; simp only [Subtype.coe_prop, Set.indicator_of_mem]; rw [ht k x.val x.prop, hf k x.val x.prop, mul_comm]
  · simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    rw [mul_comm, ← card_listVector_card]
    simp_rw [← List.Vector.countFin_eq_count₁]
    rfl
  · aesop

-- showing that binom is a probability measure without any computation!
lemma isProbabilityMeasure_binom₂ (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : IsProbabilityMeasure (binom₂ p n).toMeasure := by
  refine @isProbabilityMeasure_map_toMeasure _ _ (iidSequence n (coin p)) (@isProbabilityMeasure_sequence_toMeasure _ n (List.Vector.replicate n (coin p)) (fun i ↦ (List.Vector.get_replicate _ i) ▸ isProbabilityMeasure_coin p h)) (List.Vector.countFin true)

def succ_cast (x : Fin (n + 1)) (i : Fin (x + 1)) : Fin (n + 1) := ⟨i.val, lt_of_lt_of_le i.prop x.prop⟩


lemma thinning₁ (p q : ℝ≥0∞) {n : ℕ} (hp : p ≤ 1) (hq : q ≤ 1) : ((binom₁ p n) >>= (fun X ↦ map (succ_cast X) (binom₁ q X.val))) = binom₁ (p * q) n := by
  sorry

lemma thinning₂ (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) :
  (do
    let X ← coin p
    let Y ← coin q
    return X ∧ Y)
  = coin (p * q) := by
  simp [monad_norm]
  simp_rw [← bind_eq_bind]
  haveI h₀ : IsProbabilityMeasure ((coin p).bind fun X => (coin q).bind (Pure.pure ∘ X.and)).toMeasure := by sorry
  haveI h₁ : IsProbabilityMeasure (coin (p * q)).toMeasure := by sorry
  apply Bool_ext _ _ true
  rw [bind_apply, tsum_bool, bind_apply, tsum_bool, ← pure_eq_pure]
  simp [coin]



  sorry

lemma thinning₃ (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) : (coin p).bind (fun X ↦ (coin q).bind (fun Y ↦ Pure.pure (X && Y))) = coin (p * q) := by
  -- simp [monad_norm]
  -- simp_rw [← bind_eq_bind]
  haveI h₀ : IsProbabilityMeasure (((coin p).bind fun X => (coin q).bind fun Y => Pure.pure (X && Y))).toMeasure := by sorry
  haveI h₁ : IsProbabilityMeasure (coin (p * q)).toMeasure := by sorry
  apply Bool_ext _ _ true
  rw [bind_apply, tsum_bool, bind_apply, tsum_bool, coin_apply]
  simp [coin]
  rw [← pure_eq_pure]
  simp_rw [pure_apply]
  simp [Set.indicator]

lemma coin_not' (p : ℝ≥0∞) (hp : p ≤ 1) : map not (coin p) = coin (1 - p) := by
  haveI h₀ : IsProbabilityMeasure (map not (coin p)).toMeasure := by sorry
  haveI h₁ : IsProbabilityMeasure (coin (1 - p)).toMeasure := by sorry
  apply Bool_ext _ _ true
  rw [map_apply₂]
  rw [tsum_bool, Set.indicator, Set.indicator, Bool.not_false, coin, coin, coin]
  simp_rw [Set.mem_singleton_iff, if_true, Bool.not_true, Bool.false_eq_true, if_false, mul_zero, add_zero, Pi.one_apply, mul_one]


  simp? [coin]

  sorry

end binom

end MassFunction

end MeasureTheory
