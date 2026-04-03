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

namespace List

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

-- somewhere else
instance addBoolFin {n : ℕ} : HAdd Bool (Fin n) (Fin (n + 1)) where
  hAdd b i := match b with
  | false => Fin.castSucc i
  | true  => Fin.addNat i 1

-- somewhere else
@[simp]
lemma addBoolFin_false {n : ℕ} (i : Fin n) : addBoolFin.hAdd false i = Fin.castSucc i := by
  rfl

-- somewhere else
@[simp]
lemma addBoolFin_true {n : ℕ} (i : Fin n) : addBoolFin.hAdd true i = Fin.addNat i 1 := by rfl



-- to List.Vector

namespace List.Vector

@[simp]
lemma traverse_nil {F : Type u → Type u} [inst: Applicative F] {α' β' : Type u} (f : α' → F β') : traverse (t := flip List.Vector 0) f (nil (α := α')) = (Pure.pure nil) := by
  rfl

-- #check List.sequence_nil

@[simp]
lemma sequence_nil {F : Type u → Type u} [inst: Applicative F] {α : Type u} : sequence (t := flip List.Vector 0) (nil (α := F α)) = (Pure.pure nil) := by
  rfl

@[simp]
lemma traverse_cons {F : Type u → Type u} [Applicative F] {α' β' : Type u} (f : α' → F β') {n : ℕ} (a : α') (l : List.Vector α' n) : traverse (t := flip List.Vector (n + 1)) f (a ::ᵥ l) = (fun x1 x2 => x1 ::ᵥ x2) <$> f a <*> traverse (t := flip List.Vector n) f l := by
  obtain ⟨l1, l2⟩ := l
  subst l2
  rfl

-- #check List.sequence_cons

@[simp]
lemma sequence_cons {F : Type u → Type u} [Applicative F] {α : Type u} {n : ℕ} (l : List.Vector (F α) n) (a : F α) : sequence (t := flip List.Vector (n + 1)) (a ::ᵥ l) = cons <$> a <*> (sequence (t := flip List.Vector n) l) := (traverse_cons id a l)

lemma sequence_bind_cons {F : Type u → Type u} [Monad F] {α : Type u} {n : ℕ} (ν : F α) (μ : List.Vector (F α) n) : sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μ) = List.Vector.cons <$> ν <*> sequence (t := flip List.Vector n) μ := by
  exact sequence_cons μ ν

lemma sequence_cons' {F : Type u → Type u} [Monad F] [LawfulMonad F] {α : Type u} {n : ℕ} (ν : F α) (μ : List.Vector (F α) n) : (ν >>= fun y => sequence (t := flip List.Vector n) μ  >>= fun x => pure (List.Vector.cons y x)) = sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μ) := by
  simp [monad_norm]
  rfl

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

lemma countFin_eq_count₂ [BEq α] {n : ℕ} (l : List.Vector α n) (a : α) : (countFin a l).val = (l.toList.count (α := α) a) := by
  apply Eq.symm
  rw [← countFin_eq_count₁]

@[simp]
lemma List.Vector.count_nil {α : Type u_1} [BEq α] (a : α): List.Vector.countFin (α := α) a List.Vector.nil = 0 := by
  rw [List.Vector.countFin_eq_count₁ List.Vector.nil a 0]
  simp

end List.Vector

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

-- to Function

lemma Function.comp_apply'  {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} : (f ∘ fun x => g x) = fun x => f (g x) := by
  -- simp_rw [← Function.comp_apply]
  rfl

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

@[simp]
lemma map_eq
(μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x = (∑' a, (g⁻¹' {x}).indicator μ.weight a) := by
  rfl

lemma map_eq' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : α), μ i * ({x} : Set β).indicator 1 (g i) := by
  rw [map]
  apply tsum_congr (fun b ↦ ?_)
  rw [← Set.indicator.mul_indicator_eq]
  rfl

lemma map_eq'' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : g⁻¹' {x}), μ i := by
  rw [tsum_subtype]
  rfl

lemma map_coe [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (f : α → β) (hf : Measurable f) : toMeasure (μ.map f : DiscreteMeasure β) = Measure.map f (toMeasure μ) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (hs := hs) (hf := hf)]
  rw [toMeasure_apply₂ (hs := hs)]
  conv => left; left; intro a; rw [map_eq' μ f a.val]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  simp_rw [@toMeasure_additive α s _ _ μ _ (by measurability) (by measurability) (Set.PairwiseDisjoint.fiber_subtype s)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply μ (by measurability)]
  rfl

lemma map_toMeasure
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) : (μ.map g).toMeasure = sum (fun a ↦ μ a • (dirac (g a))) := by
  letI hα : MeasurableSpace α := ⊤
  rw [map_coe (hf := Measurable.of_discrete)]
  apply @Measure.ext _ _
  intro s hs
  rw [toMeasure, @Measure.map_sum (hf := AEMeasurable.of_discrete)]
  simp_rw [Measure.map_smul, @Measure.map_dirac α β _ _ g (by measurability)]
  rfl

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  rw [← @toMeasure_inj γ ⊤, @map_coe β γ ⊤ _ ⊤ _ (hf := by measurability), @map_coe α β ⊤ _ ⊤ _ (hf := by measurability), @map_coe α γ ⊤ _ ⊤ _ (hf := by measurability), Measure.map_map (by measurability) (by measurability)]

lemma map_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = μ.toMeasure (g⁻¹' s) := by
  rw [map_coe (hf := hg)]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (x : β) : μ.map g x = μ.toMeasure (g⁻¹' {x}) := by
  rw [← toMeasure_apply_singleton (map g μ)]
  apply map_toMeasure_apply (hs := by measurability) (hg := hg)

lemma map_toMeasure_apply₁ [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), μ a * s.indicator 1 (g a) := by
  rw [map_toMeasure]
  rw [sum_apply (hs := hs)]
  simp_rw [smul_apply, dirac_apply' _ hs, smul_eq_mul]

lemma map_apply₂ (μ : DiscreteMeasure α) (g : α → β) (x : β) : μ.map g x = ∑' (a : α), μ a * ({x} : Set β).indicator 1 (g a) := by
  rw[@map_apply α β ⊤ _ ⊤ _ (hg := by measurability)]
  rw [@toMeasure_apply α ⊤ _ (hs := by measurability)]
  apply tsum_congr (fun b ↦ by rfl)

lemma map_toMeasure_apply₂ [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), (g⁻¹' s).indicator μ a := by
  simp_rw [map_toMeasure, sum_apply (hs := hs), smul_apply, dirac_apply' (hs := hs), smul_eq_mul]
  exact tsum_congr (fun b ↦ Set.indicator.mul_indicator_eq μ (fun b => s (g b)) b)

lemma map_toMeasure_apply₃ [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (b : s), μ.toMeasure (g⁻¹' {b.val}) := by
  rw [toMeasure_apply₂ (hs := hs)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply (hs := by measurability), map_eq']
  rfl

lemma map_toMeasure_apply₄ [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s) : (μ.map g).toMeasure s = ∑' (a : g⁻¹' s), (μ a.val) := by
  letI mα : MeasurableSpace α := ⊤
  rw [map_toMeasure_apply (hg := Measurable.of_discrete) (hs := hs), toMeasure_apply₂ (hs := by measurability)]

theorem id_map (μ : DiscreteMeasure α) :
μ.map id = μ := by
  ext x
  rw [map_eq'']
  simp

theorem isProbabilityMeasure_map_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α)  (hμ : HasSum μ.weight 1) (f : α → β)  : IsProbabilityMeasure (μ.map f).toMeasure := by
  letI mα : MeasurableSpace α := ⊤
  haveI : IsProbabilityMeasure μ.toMeasure := by exact isProbabilityMeasure_iff_hasSum.mpr hμ
  rw [map_coe (hf := Measurable.of_discrete)]
  apply isProbabilityMeasure_map (hf := AEMeasurable.of_discrete)

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

/-
noncomputable instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (DiscreteMeasure α) := MeasurableSpace.comap toMeasure Measure.instMeasurableSpace

lemma comap_def [m : MeasurableSpace α] (f : β → α) {s : Set β} : MeasurableSet[m.comap f] s ↔ ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s := Iff.rfl

@[measurability]
lemma measurable_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] : Measurable (@toMeasure α _) := by
  intro s hs
  rw [comap_def]
  use s

lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl


-- set_option maxHeartbeats 0
lemma measurable_map [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (f : α → β) (hf : Measurable f) : Measurable (map f) := by
  intro s hs
  rw [comap_def]


  sorry

noncomputable instance Measure.instMeasurableSingletonClass [MeasurableSpace α] [MeasurableSingletonClass α] : MeasurableSingletonClass (Measure α) := by
  sorry

  /- refine { measurableSet_singleton := ?_ }
  intro x
  refine MeasurableSpace.measurableSet_generateFrom ?_
  simp
  use ∅
  refine MeasurableSpace.measurableSet_generateFrom ?_
  simp


  refine MeasurableSpace.measurableSet_iInf.mpr (fun i => ?_)
  rw [comap_def]
  rw [comap_def]


  rw [MeasurableSpace.map_def]


  apply?
  refine MeasurableSet.singleton x

  sorry-/


noncomputable instance instMeasurableSingletonClass [MeasurableSpace α] [MeasurableSingletonClass α] : MeasurableSingletonClass (DiscreteMeasure α) := by
  refine { measurableSet_singleton := ?_ }
  intro x
  rw [comap_def]
  use toMeasure '' {x}
  refine ⟨?_, ?_⟩
  · sorry
  · refine Injective.preimage_image toMeasure_injective {x}


-/

lemma join_coe [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)] [MeasurableSingletonClass (DiscreteMeasure α)] {h : Measurable (@toMeasure α _)} (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = Measure.join ((Measure.map toMeasure m.toMeasure)):= by
  apply Measure.ext
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

lemma join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)] [MeasurableSingletonClass (DiscreteMeasure α)] (h : Measurable (@toMeasure α _)) (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m μ • μ.toMeasure) := by
  apply Measure.ext
  intro s hs
  rw [join_coe, toMeasure, Measure.map_sum (hf := by measurability), Measure.join_sum, Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, Measure.map_smul, Measure.join_smul, Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.map_dirac, Measure.join_dirac]
  repeat measurability

lemma join_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)]  [MeasurableSingletonClass (DiscreteMeasure α)] (h : Measurable (@toMeasure α _)) (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) (hs : MeasurableSet s): m.join.toMeasure s = ∑' (μ : DiscreteMeasure α), m μ * μ.toMeasure s := by
  simp only [join_toMeasure h]
  rw [Measure.sum_apply (hs := by measurability)]
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

lemma isProbabilityMeasure_join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) (hm : HasSum m.weight 1) (hμ : ∀ μ ∈ m.weight.support, HasSum μ 1) : IsProbabilityMeasure (m.join).toMeasure := by
  letI hα : MeasurableSpace (DiscreteMeasure α) := ⊤
  simp_rw [Summable.hasSum_iff ENNReal.summable] at hm hμ
  simp_rw [isProbabilityMeasure_iff, toMeasure_apply_univ, join_weight, ← hm]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ ?_)
  by_cases h : m b = 0
  · simp [h]
  · rw [ENNReal.tsum_mul_left, hμ b <| (mem_support_iff m b).mpr h]
    simp

end join

/-- The monadic bind operation for `DiscreteMeasure`. -/
noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := (μ.map g).join

-- define a mixture
noncomputable def mixture {n : ℕ} (p : DiscreteMeasure (Fin n)) (μ : Fin n → DiscreteMeasure α) := p.bind μ

lemma bind_toMeasure_apply_eq_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g)
 : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  rw [bind, Measure.bind, join_coe (h := htoβ), ← Measure.map_map (hf := hg) (hg := htoβ), map_coe (hf := hg)]

lemma bind_coe [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g) : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  apply Measure.ext
  intro s hs
  rw [bind_toMeasure_apply_eq_toMeasure (htoβ := htoβ) (hg := hg)]

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


lemma bind_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β]
(μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (μ.bind g).toMeasure  = sum (fun a ↦ (μ a) • (g a).toMeasure) := by
  letI hα : MeasurableSpace α := ⊤
  letI hDα : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI hDβ : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply Measure.ext
  intro s _
  rw [bind_toMeasure_apply_eq_toMeasure (htoβ := by measurability) (hg := by measurability), toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_toMeasure_apply [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  (s : Set β) (hs : MeasurableSet s): (μ.bind g).toMeasure s = ∑' (a : α), μ a * (g a).toMeasure s := by
  simp_rw [bind_toMeasure, Measure.sum_apply (hs := hs), smul_apply, smul_eq_mul]

@[simp]
lemma bind_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g) x = ∑' (a : α), μ a * (g a) x := by
  letI : MeasurableSpace β := ⊤
  simp_rw [← toMeasure_apply_singleton (μ.bind g) x, ← toMeasure_apply_singleton _ x]
  exact bind_toMeasure_apply μ g _ (by measurability)

lemma join_map_map (m : DiscreteMeasure (DiscreteMeasure α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  letI hα : MeasurableSpace α := ⊤
  letI hDα : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI hβ : MeasurableSpace β := ⊤
  rw [← toMeasure_apply_singleton (m.bind (map f)), ← toMeasure_apply_singleton (map f m.join), bind_toMeasure_apply, map_toMeasure_apply (hg := Measurable.of_discrete) (hs := MeasurableSet.of_discrete), join_toMeasure_apply (h := Measurable.of_discrete) (hs := MeasurableSet.of_discrete)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_singleton, DiscreteMeasure.map_apply (hg := Measurable.of_discrete)]
  exact MeasurableSet.of_discrete

/- currently not needed!

noncomputable instance : HSMul ℝ≥0∞ (DiscreteMeasure β) (DiscreteMeasure β) := by
  exact { hSMul := fun a x ↦ ⟨fun i ↦ a * x.weight i⟩ }

lemma smul_apply' {α : Type u_1} {R : Type u_6} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  {_m : MeasurableSpace α} (c : R) (μ : DiscreteMeasure α) (x : Set α) : (c • μ) s = c • μ s

lemma hSMul_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (a : ℝ≥0∞) (x : DiscreteMeasure α) : (a • x).toMeasure = a • x.toMeasure := by
  ext s hs
  rw [smul_apply]

  sorry

theorem bind_const (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) : (μ₁.bind fun (_ : α) => μ₂) =  (∑' a, μ₁ a) • μ₂ := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  rw [← toMeasure_inj]
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := by measurability), Function.comp_apply', Measure.bind_const]
  rw [toMeasure_apply_univ, hSMul_toMeasure_apply]

-/

theorem bind_bind (μ₁ : DiscreteMeasure α) (f : α → DiscreteMeasure β) (g : β → DiscreteMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace γ := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  letI : MeasurableSpace (DiscreteMeasure γ) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete)]
  rw [Measure.bind_bind AEMeasurable.of_discrete AEMeasurable.of_discrete]
  congr
  ext a'
  rw [comp_apply, comp_apply, bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete)]

theorem bind_comm (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) (f : α → β → DiscreteMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  ext x
  repeat simp_rw [bind_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ tsum_congr (fun a ↦ ?_))
  ring

/- lemma isProbabilityMeasure_bind_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} {m : DiscreteMeasure α} [hm : IsProbabilityMeasure m.toMeasure] {f : α → DiscreteMeasure β} (hf : Measurable f) (hf₁ : ∀ (a : α), IsProbabilityMeasure (f a).toMeasure) : IsProbabilityMeasure (m.bind f).toMeasure := by
  rw [bind_coe (htoβ := htoβ) (hg := hf)]
  exact @isProbabilityMeasure_bind α β  _ _ m.toMeasure _ (toMeasure ∘ f) ((htoβ.comp hf).aemeasurable) (ae_of_all (toMeasure m) hf₁)
-/

lemma isProbabilityMeasure_bind_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β] {m : DiscreteMeasure α} (hm : HasSum m.weight 1) {f : α → DiscreteMeasure β} (hf₁ : ∀ a ∈ support m.weight, HasSum (f a).weight 1) : IsProbabilityMeasure (m.bind f).toMeasure := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  rw [bind_coe (hg := by measurability) (htoβ := Measurable.of_discrete)]
  haveI : IsProbabilityMeasure (toMeasure m) := isProbabilityMeasure_iff_hasSum.mpr hm
  exact isProbabilityMeasure_bind AEMeasurable.of_discrete (hf₁ := (ae_iff_support (fun x => IsProbabilityMeasure ((toMeasure ∘ f) x)) trivial m).mpr (fun x hx ↦ isProbabilityMeasure_iff_hasSum.mpr (hf₁ x hx)))

-- end bind

section pure

/-- The pure `DiscreteMeasure` puts all the mass lies in one point. The value of `pure a` is `1` at `a` and
`0` elsewhere. In other words, `pure ∘ toMeasure = Measure.dirac`. -/
noncomputable def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩

lemma pure_apply (a b : α) : (pure a) b = ({a} : Set α).indicator 1 b := rfl

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
lemma pure_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) (s : Set α) (hs : MeasurableSet s): (pure a).toMeasure s = s.indicator 1 a := by
  rw [toMeasure_apply₁ (hs := hs)]
  simp_rw [← Set.indicator.mul_indicator_eq (f := (pure a))]
  simp_rw [pure_apply, Set.indicator.mul_indicator_eq, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h),
      ← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe [MeasurableSpace α] [MeasurableSingletonClass α]  (a : α) : (pure a).toMeasure = .dirac a := by
  apply Measure.ext
  intro s hs
  simp_rw [pure_toMeasure_apply (hs := hs), Measure.dirac_apply]

lemma toMeasure_pure_eq_dirac [MeasurableSpace α] [MeasurableSingletonClass α] : (toMeasure ∘ @pure α) = .dirac := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) : HasSum (pure a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp_rw [pure_apply, ← tsum_subtype, tsum_singleton]
  rfl

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  rw [← toMeasure_inj, pure_coe, map_coe (hf := by measurability), pure_coe, Measure.map_dirac (by measurability)]

theorem pure_bind (a : α) (f : α → DiscreteMeasure β) :
(pure a).bind f = f a := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), pure_coe, dirac_bind (hf := Measurable.of_discrete)]
  rfl

theorem bind_pure  (μ : DiscreteMeasure α) :
μ.bind pure = μ := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace (DiscreteMeasure α) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), Measure.bind, toMeasure_pure_eq_dirac, ← Measure.bind, Measure.bind_dirac]

@[simp, monad_norm]
lemma bind_pure_comp (f : α → β) (μ : DiscreteMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), map_coe (hf := Measurable.of_discrete), Function.comp_apply']
  simp_rw [pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := Measurable.of_discrete)]

lemma isProbabilityMeasure_pure_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) : IsProbabilityMeasure ((pure a).toMeasure) := by
  rw [pure_coe]
  exact dirac.isProbabilityMeasure

@[simp]
lemma tsum_pure (a : α) (f : α → ℝ≥0∞): ∑' (x : α), (f x) * pure a x = f a := by
  simp_rw [pure_apply]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype]
  simp

end pure

section seq

variable (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) (b : β)

/-- The monadic sequencing operation for `DiscreteMeasure`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q :DiscreteMeasure (α → β)) (p :  Unit →DiscreteMeasure α) :DiscreteMeasure β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

@[simp, monad_norm]
lemma bind_map_eq_seq (q :DiscreteMeasure (α → β)) (p : Unit →DiscreteMeasure α) : seq q p = q.bind (fun m => (p ()).map m) := by
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

lemma isProbabilityMeasure_seq_toMeasure  [MeasurableSpace β] [MeasurableSingletonClass β] {hq : HasSum q.weight 1} {hp : HasSum (p ()).weight 1} : IsProbabilityMeasure (seq q p).toMeasure := by
  letI hα : MeasurableSpace α := ⊤
  rw [bind_map_eq_seq]
  apply isProbabilityMeasure_bind_toMeasure hq (fun a ha ↦ isProbabilityMeasure_iff_hasSum.mp <| isProbabilityMeasure_map_toMeasure _ hp _ )

end seq

noncomputable instance : Functor DiscreteMeasure where
  map := map

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map g h μ := (map_map μ g h).symm

section monad

noncomputable instance : Functor DiscreteMeasure where
  map := map

noncomputable instance : Seq DiscreteMeasure where
  seq := seq

noncomputable instance : Monad DiscreteMeasure where
  pure := pure
  bind := bind

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulMonad DiscreteMeasure :=
  LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)
  (bind_map :=
  fun q p ↦ (bind_map_eq_seq q (fun _ ↦ p)).symm)

@[simp, monad_norm]
lemma pure_eq_pure : @pure α = @Pure.pure DiscreteMeasure _ α := by rfl

@[simp, monad_norm]
lemma map_eq_map {α β : Type u} (f : α → β) (p : DiscreteMeasure α) : (map f p) = (Functor.map f p) := rfl

@[simp, monad_norm]
lemma seq_eq_seq {α β : Type u} (p : DiscreteMeasure (α → β)) (q : Unit → DiscreteMeasure α) : seq p q = Seq.seq p q := by
  rfl

@[simp, monad_norm]
lemma bind_eq_bind {α β : Type u} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (bind μ g) = (Bind.bind μ g) := rfl

/--
This instance allows `do` notation for `DiscreteMeasure` to be used across universes, for instance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
noncomputable instance : ULiftable DiscreteMeasure.{u} DiscreteMeasure.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by rw [map_map, Equiv.symm_comp_self, id_map]
      right_inv := fun a => by simp [map_map]
      }

end monad

section sequence

-- `DiscreteMeasure`s on lists

-- MF
lemma cons_map_seq_apply {n : ℕ} (μs : DiscreteMeasure (List.Vector α n)) (ν : DiscreteMeasure α) (l : List.Vector α (n + 1)): (List.Vector.cons <$> ν <*> μs) l = ∑' (a' : α), ν a' * ∑' (l' : List.Vector α n), μs l' * pure (a' ::ᵥ l') l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]

lemma pure_cons_apply_cons [DecidableEq α] {n : ℕ} (a a' : α) (l l' : List.Vector α n) : pure (a' ::ᵥ l') (a ::ᵥ l) = (pure a' a) * (pure l' l) := by
  repeat rw [pure_apply, Set.indicator]
  aesop

-- MF
lemma cons_map_seq_apply_cons [DecidableEq α] {n : ℕ} (μs : DiscreteMeasure (List.Vector α n)) (ν : DiscreteMeasure α) (l : List.Vector α n) (a : α) : (List.Vector.cons <$> ν <*> μs) (a ::ᵥ l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [pure_cons_apply_cons, ← mul_assoc, pure_comm]
  conv => left; left; intro a'; right; left; intro l'; rw [mul_assoc]; right; rw [mul_comm]
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ← mul_assoc, tsum_pure]

-- MF
lemma sequence_cons_eq_seq_sequence [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (ν : DiscreteMeasure α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) = (List.Vector.cons <$> ν <*> sequence (t := flip List.Vector n) μs) := by
  rw [sequence, sequence, List.Vector.traverse_cons id]
  simp

-- lemma traverse_cons_eq_seq_traverse [DecidableEq α] {n : ℕ} (f : α → DiscreteMeasure β) (μs : List.Vector α n) (ν : α) : (traverse (t := flip List.Vector (n + 1)) (m := DiscreteMeasure) f (ν ::ᵥ μs)) = (List.Vector.cons <$> (f ν) <*> traverse (t := flip List.Vector n) (m := DiscreteMeasure) f μs) := by
--  rw [sequence, sequence, List.Vector.traverse_cons id]
--  simp

lemma sequence_cons_apply_cons [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (ν : DiscreteMeasure α) (l : List.Vector α n) (a : α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) (a ::ᵥ l) = (ν a) * ((sequence (t := flip List.Vector n) μs) l) := by
  rw [List.Vector.sequence_cons]
  exact cons_map_seq_apply_cons (sequence (t := flip List.Vector n) μs) ν l a


lemma prod_zipWith {n : ℕ} (f : List.Vector (α → ℝ≥0∞) n) (l : List.Vector α n) : List.prod (f.zipWith (· ·) l).toList = ∏ i, (f.get i) (l.get i) := by
  have : (f.zipWith (· ·) l).toList = List.ofFn (fun i => (f.get i) (l.get i)) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_ofFn, List.Vector.zipWith_toList, List.getElem_zipWith]
      rfl
  rw [this, List.prod_ofFn]


set_option backward.isDefEq.respectTransparency false

lemma sequence_apply₀ [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (l : List.Vector α n) :
    (sequence (t := flip List.Vector n) μs) l = List.prod (μs.zipWith (· ·) l).toList :=
  by
  induction μs with
  | nil =>
    simp only [List.Vector.nil_iff, List.Vector.sequence_nil]
    rw [← pure_eq_pure]
    rw [pure_apply_self]
    simp
  | cons hl =>
    rw [← List.Vector.cons_head_tail l, sequence_cons_apply_cons]
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one,
      List.Vector.zipWith_toList, List.Vector.toList_cons]
    rw [List.zipWith_cons_cons]
    simp [hl]

lemma sequence_apply₁ [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (l : List.Vector α n) :
    (sequence (t := flip List.Vector n) μs) l = ∏ i, (μs.get i) (l.get i) :=
  by
  rw [sequence_apply₀]
  exact prod_zipWith μs l

-- TODO: define marginal distributions

lemma isProbabilityMeasure_sequence_toMeasure {n : ℕ} [MeasurableSpace (flip List.Vector n α)] [MeasurableSingletonClass (flip List.Vector n α)] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) {hμ : ∀ i, HasSum (μs.get i).weight 1} : IsProbabilityMeasure (sequence (t := flip List.Vector n) μs).toMeasure := by
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

noncomputable def iidSequence (n : ℕ) (μ : DiscreteMeasure α) : DiscreteMeasure (List.Vector α n) := sequence (t := flip List.Vector n) (List.Vector.replicate n μ)

lemma iidSequence_apply [DecidableEq α] (n : ℕ) (μ : DiscreteMeasure α) (l : List.Vector α n) :
    (iidSequence n μ) l = (l.map μ).toList.prod := by
  rw [iidSequence, List.Vector.toList_map, ← List.map_eq_replicateZipWith,
    List.Vector.toList_length]
  rw [sequence_apply₀]
  congr

lemma iidSequence_apply₁ {n : ℕ} {μ : DiscreteMeasure α} [DecidableEq α] {l : List.Vector α n} :
    iidSequence n μ l = (∏ a ∈ l.toList.toFinset, (μ a) ^ (List.Vector.countFin a l).val) := by
  rw [iidSequence_apply n μ l]
  rw [List.Vector.toList_map]
  simp_rw [List.Vector.countFin]
  exact Finset.prod_list_map_count l.toList μ

lemma iidSequence_apply₂ (n : ℕ) (μ : DiscreteMeasure α) [DecidableEq α] (l : List.Vector α n) :
    iidSequence n μ l = (∏' (a : α), (μ a) ^ (List.Vector.countFin a l).val) := by
  simp_rw [List.Vector.countFin]
  have hf : ∀ b ∉ l.toList.toFinset, μ b ^ (l.toList.count b) = 1 := by
    simp_rw [List.mem_toFinset, ← List.count_eq_zero]
    exact fun b hb ↦ hb ▸ pow_zero (μ b)
  rw [tprod_eq_prod hf]
  exact iidSequence_apply₁

lemma pure_sequence (ν : DiscreteMeasure α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : DiscreteMeasure α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

lemma iidSequence_cons (ν : DiscreteMeasure α) : (ν >>= fun y => (iidSequence n ν) >>= fun x => pure (x.cons y)) = iidSequence (n+1) ν := by
  simp [monad_norm, iidSequence]

end iidSequence

section coin

open Bool ENNReal NNReal

noncomputable def coin (p : ℝ≥0∞) : DiscreteMeasure Bool where weight := fun
  | true => p
  | false => 1 - p

lemma coin_apply (p : ℝ≥0∞) (b : Bool) : (coin p) b = if b then p else (1 - p) := by
  by_cases h : b <;> simp only [h, ↓reduceIte] <;> rfl

instance isProbabilityMeasure_coin (p : ℝ≥0∞) (h : p ≤ 1) : IsProbabilityMeasure (coin p).toMeasure := by
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

lemma Bool_isProbabilityMeasure_not (μ : DiscreteMeasure Bool) [IsProbabilityMeasure μ.toMeasure] (b : Bool) : μ (!b) = 1 - μ b := by
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

lemma Bool_ext (μ ν : DiscreteMeasure Bool) [IsProbabilityMeasure μ.toMeasure] [IsProbabilityMeasure ν.toMeasure] (b : Bool) (h : μ b = ν b) : μ = ν := by
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

lemma massFunctionBool_eq_coin (P : DiscreteMeasure Bool) [IsProbabilityMeasure P.toMeasure] : P = coin (P true) := by
  haveI h : IsProbabilityMeasure (coin (P true)).toMeasure := isProbabilityMeasure_coin (P true) (apply_le_one true)
  exact Bool_ext P (coin (P true)) true (by rfl)

end coin

section uniform

variable {ι : Type*} [Fintype ι] [Inhabited ι]

def uniform : DiscreteMeasure ι := fun _ ↦ (Finset.univ : Finset ι).card⁻¹

lemma isProbabilityMeasure_uniform : IsProbabilityMeasure (uniform (ι := ι)).toMeasure := by
  rw [isProbabilityMeasure_iff_tsumOne]
  simp [uniform]
  refine ENNReal.mul_inv_cancel ?_ ?_
  simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  simp

end uniform


section binom

-- Defining the binomial distribution inductively
noncomputable def binom (p : ℝ≥0∞) (n : ℕ) : DiscreteMeasure (Fin (n + 1)) := match n with
  | .zero => pure 0
  | .succ n => do
    let X ← coin p
    let Y ← binom p n
    return addBoolFin.hAdd X Y

@[simp]
lemma binom_zero (p : ℝ≥0∞) : binom p 0 = pure 0 := by rfl

lemma isProbabilityMeasure_binom (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : IsProbabilityMeasure (binom p n).toMeasure := by
  induction n with
    | zero =>
      apply isProbabilityMeasure_pure_toMeasure
    | succ n hn =>
      simp only [binom, Nat.succ_eq_add_one,
        LawfulMonad.bind_pure_comp, map_eq_bind_pure_comp]
      exact @isProbabilityMeasure_bind_toMeasure _ _ _ (isProbabilityMeasure_coin p h) _
        (fun a ↦ isProbabilityMeasure_bind_toMeasure
        (fun i ↦ isProbabilityMeasure_pure_toMeasure _))

lemma binom_succ (p : ℝ≥0∞) (n : ℕ) : binom p (n + 1) = (coin p) >>= fun X ↦  binom p n >>= fun Y ↦ pure (addBoolFin.hAdd X Y) := by rfl

lemma binom_seq (p : ℝ≥0∞) (n : ℕ) : binom p (n + 1) =
addBoolFin.hAdd <$>  (coin p) <*> (binom p n) := by
  simp [binom, monad_norm]

theorem binom_eq_count_true (p : ℝ≥0∞) (n : ℕ) : binom p n = (iidSequence n (coin p)).map (List.Vector.countFin true) := by
  induction n with
    | zero =>
      simp [binom, iidSequence]
    | succ n h  =>
      rw [binom_seq, h, iidSequence, iidSequence, List.Vector.replicate_succ,
        List.Vector.sequence_cons]
      simp only [map_eq_bind_pure_comp, map_eq_map, seq_eq_bind_map, comp_apply,
        LawfulMonad.bind_pure_comp, bind_assoc, LawfulMonad.pure_bind,
        Nat.succ_eq_add_one]
      congr
      have h (x : Bool) (a : List.Vector Bool n) : addBoolFin.hAdd x (List.Vector.countFin true a) = List.Vector.countFin true (x ::ᵥ a) := by
        cases x <;> rw [Fin.ext_iff] <;> repeat rw [List.Vector.countFin_eq_count₂]
        · exact Nat.add_zero (List.countP.go (fun x => x == true) a.toList 0)
        · simp [List.Vector.countFin_eq_count₂]
      simp_rw [h]

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

theorem binom_formula (p : ℝ≥0∞) (n : ℕ) : binom p n = fun (k : Fin (n + 1)) ↦ (p ^ k.val * (1 - p) ^ (n - k.val)) * (Nat.choose n k) := by
  ext k
  let s (k : Fin (n + 1)) : Finset (List.Vector Bool n) := {l : List.Vector Bool n | (List.Vector.countFin true l) = k}
  have hs (k : Fin (n + 1)) : ((fun (l : List.Vector Bool n) => List.Vector.countFin true l) ⁻¹' {k}) = s k := by
    aesop
  have ht (k : Fin (n + 1)) : ∀ x ∈ s k, List.Vector.countFin true x = k := by
    aesop
  have hf (k : Fin (n + 1)) : ∀ x ∈ s k, List.Vector.countFin false x = n - k := by
    intro ⟨x1, x2⟩ hx
    refine Nat.eq_sub_of_add_eq' ?_
    rw [← ht k ⟨x1, x2⟩ hx, List.Vector.countFin, List.Vector.countFin, List.count_true_add_count_false, List.Vector.toList_mk, x2]
  rw [binom_eq_count_true, map_apply, toMeasure_apply]
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

section thinning

def succ_cast {n : ℕ} (x : Fin (n + 1)) (i : Fin (x + 1)) : Fin (n + 1) := ⟨i.val, lt_of_lt_of_le i.prop x.prop⟩


lemma thinning₁ (p q : ℝ≥0∞) {n : ℕ} (hp : p ≤ 1) (hq : q ≤ 1) : ((binom p n) >>= (fun X ↦ (succ_cast X) <$> (binom q X.val))) = binom (p * q) n := by
  induction n with
  | zero =>
    simp
    rfl
  | succ d hd =>
    simp [binom]
    simp [monad_norm] at hd ⊢
    rw [← hd]
    simp



    sorry

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
  haveI h₁ : IsProbabilityMeasure (coin (p * q)).toMeasure := by
    exact isProbabilityMeasure_coin (p * q) (Left.mul_le_one hp hq)
  apply Bool_ext _ _ true
  rw [bind_apply, tsum_bool, bind_apply, tsum_bool, ← pure_eq_pure]
  simp [coin_apply]
  rw [← pure_eq_pure]
  simp

lemma thinning₃ (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) : (coin p).bind (fun X ↦ (coin q).bind (fun Y ↦ Pure.pure (X && Y))) = coin (p * q) := by
  haveI h₀ : IsProbabilityMeasure (((coin p).bind fun X => (coin q).bind fun Y => Pure.pure (X && Y))).toMeasure := by
    apply isProbabilityMeasure_bind_toMeasure (hm := isProbabilityMeasure_coin p hp)
    intro a
    apply isProbabilityMeasure_bind_toMeasure (hm := isProbabilityMeasure_coin q hq)
    intro b
    apply isProbabilityMeasure_pure_toMeasure
  haveI h₁ : IsProbabilityMeasure (coin (p * q)).toMeasure := by
    apply isProbabilityMeasure_coin
    exact Left.mul_le_one hp hq
  apply Bool_ext _ _ true
  rw [bind_apply, tsum_bool, bind_apply, tsum_bool, coin_apply]
  simp [coin, ← pure_eq_pure, pure_apply]

lemma g : (not ⁻¹' {true}) = {false} := by

    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, Bool.not_eq_eq_eq_not, Bool.not_true]



lemma coin_not' (p : ℝ≥0∞) (h : p ≤ 1) : map not (coin p) = coin (1 - p) := by
  haveI h₁ : IsProbabilityMeasure (coin (1 - p)).toMeasure := by
    refine isProbabilityMeasure_coin (1 - p) tsub_le_self
  haveI h₀ : IsProbabilityMeasure (map not (coin p)).toMeasure := by
    refine isProbabilityMeasure_map_toMeasure (coin p) (hμ := isProbabilityMeasure_coin p h) not
  apply Bool_ext _ _ true
  rw [map_apply]
  rw [g]
  rw [toMeasure_apply_singleton]
  rfl

end thinning

end binom

section geometric

-- how many failures before the first success
def geometric (p : ℝ≥0∞) (h : p ≤ 1) : DiscreteMeasure ℕ :=
  fun n ↦ match n with
  | .zero => p
  | .succ n => (1 - p) * geometric p h n

example (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) : (1 - (1 - p) * (1 - q)) ≤ 1 := by
  exact tsub_le_self

lemma geometric_min (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) : geometric (1 - (1 - p) * (1 - q)) tsub_le_self =
  do
    let X ← geometric p hp
    let Y ← geometric q hq
    return min X Y := by
  simp [monad_norm]

  sorry

instance a : HSMul ℝ≥0∞ (DiscreteMeasure α) := fun p μ ↦ fun x ↦ p * (μ x)


-- (a, n)
def neg_binomialAux (p : ℝ≥0∞) (h : p ≤ 1) (a : ℕ) : ℕ → ℝ≥0∞
  | .zero => p ^ a
  | .succ n => p * (neg_binomialAux p h a n) + (1-p) * (neg_binomialAux p h (a+1) n)

def neg_binomialAux' (p : ℝ≥0∞) (h : p ≤ 1) (a : ℕ) : ℕ → ℝ≥0∞
  | .zero => p ^ a
  | .succ n => (coin p).bind (fun b => match b with
    | true  => neg_binomialAux' p h a
    | false => neg_binomialAux' p h (a + 1)) n
termination_by n => n
decreasing_by
  sorry
  sorry



-- how many failures before the ath success
private def neg_binomial_aux (p : ℝ≥0∞) (h : p ≤ 1) (a : ℕ) (n : ℕ) : ℝ≥0∞ := match a, n with
  | .zero, _ => pure (0 : ℕ) n
  | .succ _, .zero => p ^ a
  | .succ k, .succ n' => p * neg_binomial_aux p h k n' + (1 - p) * neg_binomial_aux p h (k + 1) n'
termination_by (a, n)

def neg_binomial (p : ℝ≥0∞) (h : p ≤ 1) (a : ℕ) : DiscreteMeasure ℕ :=
  neg_binomial_aux p h a

lemma neg_binomial_succ_succ (p : ℝ≥0∞) (h : p ≤ 1) (k n : ℕ) :
    neg_binomial p h (k + 1) (n + 1) =
      (coin p).bind (fun b => match b with
        | true  => neg_binomial p h k
        | false => neg_binomial p h (k + 1)) n := by
  simp only [neg_binomial, neg_binomial_aux, bind_apply, coin]
  simp only [tsum_bool]
  ring


lemma geometric_apply (p : ℝ≥0∞) (h : p ≤ 1) (k : ℕ) : geometric p h k = (1 - p) ^ k * p := by
  induction k with
  | zero =>
    simp [geometric]
  | succ k hk =>
    simp [geometric, hk]
    ring

lemma isProbabilityMeasure_geometric_toMeasure (p : ℝ≥0∞) (h₀ : p ≤ 1) (h₁ : p ≠ 0) : IsProbabilityMeasure (geometric p h₀).toMeasure := by
  simp_rw [isProbabilityMeasure_iff_tsumOne, geometric_apply]
  rw [ENNReal.tsum_mul_right]
  simp only [tsum_geometric]
  rw [ENNReal.sub_sub_cancel one_ne_top h₀]
  refine ENNReal.inv_mul_cancel h₁ (lt_of_le_of_lt h₀ one_lt_top).ne

end geometric



end DiscreteMeasure

end MeasureTheory
