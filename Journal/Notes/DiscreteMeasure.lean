/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib

/-!
# Discrete measures and discrete probability measures

We develop a setup for discrete (probability) measures, which is an alternative to PMFs (Probability Mass Functions). Here, a `μ : DiscreteMeasure` is a sum of `dirac`s with weights given by `μ.weight : α → ℝ≥0∞`. Since `dirac a` is a `@Measure α ⊤`, we immediately have that a `DiscreteMeasure α` is a `@Measure α ⊤`, i.e., it is defined on the power set of `α`. We implement a coercion to `Measure`. Note that `μ : DiscreteMeasure α` is not only σ-additive, but additive; see `DiscreteMeasure.m_iUnion`.

`DiscreteProbabilityMeasure α` is the subtype of `DiscreteMeasure α`, such that `μ : DiscreteProbabilityMeasure α` has `HasSum μ.weight 1` (as for PMFs).

This setup combines the following features:

* We can use the `Measure`-library right from the start (as opposed to `PMF`s). (E.g., integrating wrt a discrete Measure can use linearity in the Measure, and integrating wrt `dirac`. The proofs of the usual properties between `map`, `bind` and `join` can use their counterparts in `Measure`.)
* We establish that `DiscreteProbabilityMeasure α` is a `LawfulMonad` (as well as `DiscreteMeasure`). In particular, it allows for `do`-notation.
* We do not only have probability measures in this setup (as in `PMF`), but `DiscreteMeasure`s as well. This will allow for a similar treatment of these two cases. (Discrete measures appear frequently in probability theory in the form of random measures.)
* It will be easier to connect `DiscreteMeasure` with `Measure` (since they are already measures). E.g., weak convergence of `P : ℕ → DiscreteMeasure α` to some `Measure α` is easy to formulate. (For this, we have to `trim` the `P n`s to the corresponding `MeasureableSpace α` instance.)

As one example, we have started to establish some results on `coin p`, which is a Bernoulli distribution, as well as alternative formulations for the usual binomial distribution.

-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

-- add to Set.indicator

--@[simp]
--lemma Set.indicator.mul_indicator_eq' (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator (fun _ ↦ 1) a = s.indicator f a := by
--  simp [Set.indicator]

-- currently not used
@[simp]
lemma Set.indicator.ite_ite (d : Prop) [Decidable d] (a b c : α) : (if d then a else if d then b else c) = (if d then a else c) := by
  grind

lemma Set.indicator_comm_singleton (i b : β) : ({i} : Set β).indicator (1 : β → ℝ≥0∞) b = ({b} : Set β).indicator (1 : β → ℝ≥0∞) i := by
  refine Set.indicator_eq_indicator ?_ rfl
  simp only [Set.mem_singleton_iff, eq_comm]

@[simp]
lemma Set.indicator_sum_singleton (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = (f x) := by
  rw [← tsum_subtype, tsum_singleton]

-- used frequently
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



-- to Function

lemma Function.comp_apply'  {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} : (f ∘ fun x => g x) = fun x => f (g x) := by
  -- simp_rw [← Function.comp_apply]
  rfl



-- to Mathlib.MeasureTheory.Measure.AEMeasurable
-- join commutes with sum
lemma Measure.join_sum {α : Type u_1} {mα : MeasurableSpace α} {ι : Type u_7} (m : ι → Measure (Measure α)) :
(sum m).join = sum fun (i : ι) ↦ (m i).join := by
  simp_rw [Measure.join, lintegral_sum_measure]
  ext s hs
  rw [ofMeasurable_apply s hs, Measure.sum_apply _ hs]
  apply tsum_congr (fun i ↦ ?_)
  rw [ofMeasurable_apply s hs]

-- bind commutes with sum
lemma Measure.bind_sum {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {ι : Type u_7} (m : ι → Measure α) (f : α → Measure β) (h : AEMeasurable f (sum fun i => m i)) :
  (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [Measure.bind, Measure.map_sum h, Measure.join_sum]

-- scalar multiplication commutes with bind
lemma Measure.bind_smul {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α) (f : α → Measure β) :
  (c • m).bind f = c • (m.bind f) := by
  simp_rw [Measure.bind, Measure.map_smul, Measure.join_smul]



section discreteMeasures

-- let us start with discrete measures now!

/- We will define all measures on `⊤`, i.e., the power set σ-algebra. Later, we might want to use them on smaller σ-algebras. For this, then take `toMeasure.trim`. -/

instance : (MeasurableSpace α) := ⊤

instance : (MeasurableSpace β) := ⊤

structure DiscreteMeasure (α : Type*) where
  weight : α → ℝ≥0∞

namespace DiscreteMeasure

@[coe]
noncomputable def toMeasure : DiscreteMeasure α → @Measure α ⊤ := fun μ ↦ sum (fun a ↦ (μ.weight a) • @Measure.dirac α ⊤ a)

noncomputable instance : Coe (DiscreteMeasure α) (@Measure α ⊤) where
  coe μ : @Measure α ⊤ := μ.toMeasure

noncomputable instance : CoeFun (DiscreteMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toMeasure

lemma apply (μ : DiscreteMeasure α) (s : Set α) :
    μ s = ∑' (i : α), s.indicator μ.weight i := by
  simp [toMeasure]

lemma apply₁ (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (i : α), μ.weight i * s.indicator 1 i := by
  simp [apply]

lemma apply₂ (μ : DiscreteMeasure α) (s : Set α) : μ s =
    ∑' (a : s), (μ.weight a) := by
  simp [apply, tsum_subtype]

@[simp]
lemma apply_singleton (μ : DiscreteMeasure α) (a : α) :
    ∑' (i : α), ({a} : Set α).indicator μ.weight i = μ.weight a := by
  rw [← tsum_subtype, tsum_singleton]

lemma apply_singleton' (μ : DiscreteMeasure α) (a : α) : μ {a} =
    μ.weight a := by
  simp [apply]

lemma singleton_eq_weight (μ : DiscreteMeasure α) : (fun (a : α) ↦ μ {a}) = μ.weight := by
  simp [apply]

/- Additivity for a `DiscreteMeasure` not only applies to countable unions, but to arbitrary ones. -/
lemma m_iUnion (μ : DiscreteMeasure α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : μ (⋃ d, s d) = ∑' (d : δ), μ (s d) := by
  simp only [apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ ?_)
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ i, b ∈ s i <;> simp [h₀]
  · obtain ⟨i, hi⟩ := h₀
    rw [ENNReal.tsum_eq_add_tsum_ite i]
    simp only [hi, ↓reduceIte]
    nth_rw 1 [← add_zero (μ.weight b)] ; congr
    apply (ENNReal.tsum_eq_zero.mpr ?_).symm
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    exact fun j hj hb ↦ False.elim <| Disjoint.notMem_of_mem_left (hs (id (Ne.symm hj))) hi hb
  · refine (ENNReal.tsum_eq_zero.mpr (fun j ↦ ?_)).symm
    push_neg at h₀
    simp [h₀ j]

lemma m_iUnion_singleton (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (x : s), μ {x.val} := by
  nth_rw 1 [← Set.iUnion_of_singleton_coe s]
  exact m_iUnion μ _ (Set.PairwiseDisjoint.singleton_subtype s)

lemma ext_weight {μ₁ μ₂ : DiscreteMeasure α}
  (h : μ₁.weight = μ₂.weight) : μ₁ = μ₂ :=
by
  cases μ₁
  simp only at h
  rw [h]

@[ext]
lemma ext {μ₁ μ₂ : DiscreteMeasure α}
    (h : ∀ a, μ₁.weight a = μ₂.weight a) : μ₁ = μ₂ := ext_weight <| funext h

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteMeasure α} (h : μ₁.toMeasure = μ₂.toMeasure) : μ₁ = μ₂ :=
by
  ext x
  rw [← singleton_eq_weight, ← singleton_eq_weight, h]

lemma apply_univ (μ : DiscreteMeasure α) : μ Set.univ = ∑' (a : α), μ.weight a := by
  simp [apply]


lemma apply_univ' (μ : DiscreteMeasure α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d): μ Set.univ = ∑' (d : δ), μ (s d) := by
  rw [hs₁]
  exact m_iUnion μ s hs₀

lemma isProbabilityMeasure_iff (μ : DiscreteMeasure α) : IsProbabilityMeasure μ.toMeasure ↔ HasSum μ.weight 1 := by
  rw [MeasureTheory.isProbabilityMeasure_iff, DiscreteMeasure.apply_univ, Summable.hasSum_iff ENNReal.summable]

section map

noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : (DiscreteMeasure β) where
  weight := fun b ↦ μ (g⁻¹' {b})

noncomputable instance : Functor DiscreteMeasure where
  map := map

@[simp]
lemma map_weight (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x = μ (g⁻¹' {x}) := by
  rfl

lemma map_weight' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x =  ∑' (i : α), μ.weight i * ({x} : Set β).indicator 1 (g i) := by
  rw [map_weight, apply₁]
  apply tsum_congr (fun b ↦ by congr)

lemma map_coe (μ : DiscreteMeasure α) (f : α → β) : ((μ.map f : DiscreteMeasure β) : @Measure β ⊤) = Measure.map f (μ : @Measure α ⊤) := by
  ext s
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [apply₂]
  simp_rw [map_weight]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  exact (m_iUnion _ _ (Set.PairwiseDisjoint.fiber_subtype s)).symm

lemma map_toMeasure' (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = sum (m0 := ⊤) (fun a ↦ μ.weight a • (@dirac β ⊤ (g a))) := by
  rw [map_coe]
  ext s
  rw [toMeasure, Measure.map_sum]
  have gh : Measurable g := by measurability
  simp_rw [Measure.map_smul, @Measure.map_dirac α β ⊤ ⊤ g (by measurability)]
  apply @AEMeasurable.of_discrete α β ⊤ ⊤

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext s
  rw [← apply_singleton', ← apply_singleton', map_coe, map_coe, map_coe]
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


section lintegral

noncomputable def lintegral (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : ℝ≥0∞ := ∑' (a : α), μ.weight a * (g a)

lemma lintegral_eq_toMeasure (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : μ.lintegral g = ∫⁻ (a : α), g a ∂ μ.toMeasure := by
  rw [toMeasure, lintegral]
  simp

-- TODO: integral_map

end lintegral

section join

noncomputable def join (m : DiscreteMeasure (DiscreteMeasure α)) : (DiscreteMeasure α) := ⟨fun a ↦ ∑' (μ : DiscreteMeasure α), m {μ} * μ {a}⟩

@[simp]
lemma join_weight (m : DiscreteMeasure (DiscreteMeasure α)) (x : α) : m.join.weight x = ∑' (μ : DiscreteMeasure α), m {μ} * μ {x} := by
  rfl

lemma join_coe (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = Measure.join (mα := ⊤) ((Measure.map toMeasure m.toMeasure)):= by
  ext s
  rw [Measure.join_apply (mα := ⊤) (hs := by measurability)]
  rw [lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [← lintegral_eq_toMeasure, apply₂]
  simp_rw [join_weight, lintegral]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left, apply_singleton']
  simp_rw [apply_singleton', ← apply₂]

lemma join_toMeasure (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m.weight μ • μ.toMeasure) := by
  ext s
  rw [join_coe, toMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, Measure.map_smul, Measure.join_smul, Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.map_dirac, Measure.join_dirac]
  measurability

lemma join_apply (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) : m.join s = ∑' (μ : DiscreteMeasure α), m {μ} * μ s := by
  simp only [join_toMeasure]
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  simp
  simp [apply]

lemma join_hasSum (m : DiscreteMeasure (DiscreteMeasure α)) (hm : HasSum m.weight 1) (hμ : ∀ μ, m.weight μ ≠ 0 → HasSum μ.weight 1) : HasSum m.join.weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp_rw [join_weight]
  rw [ENNReal.tsum_comm]
  have h : ∀ μ, m.weight μ * ∑' (a : α), μ.weight a = m.weight μ := by
    intro μ
    by_cases hμ' : m.weight μ = 0
    · rw [hμ', zero_mul]
    · simp_rw [Summable.hasSum_iff ENNReal.summable] at hμ
      rw [hμ μ hμ', mul_one]
  simp_rw [ENNReal.tsum_mul_left, apply_singleton']
  conv => left; left; intro b; rw [h b]
  exact HasSum.tsum_eq hm

end join

section bind

noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := (μ.map g).join

lemma bind_apply_eq_toMeasure (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : μ.bind g s = μ.toMeasure.bind (toMeasure ∘ g) s := by
  rw [bind, Measure.bind, join_coe, ← Measure.map_map (hg := by measurability) (hf := by measurability), map_coe]

lemma bind_coe (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  ext s
  rw [bind_apply_eq_toMeasure]

lemma bind_toMeasure' (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : μ.bind g  = sum (fun a ↦ μ.weight a • (g a).toMeasure) := by
  ext s
  rw [bind_apply_eq_toMeasure, toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : μ.bind g s = ∑' (a : α), μ.weight a * (g a) s := by
  rw [bind_toMeasure']
  simp

@[simp]
lemma bind_weight (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g).weight x = ∑' (a : α), μ.weight a * (g a).weight x := by
  simp_rw [← apply_singleton', bind_apply, apply_singleton']

lemma join_map_map (m : DiscreteMeasure (DiscreteMeasure α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  rw [← apply_singleton', bind_apply, map_weight, join_apply]
  apply tsum_congr (fun b ↦ ?_)
  congr 1 <;> rw [apply_singleton']
  rw [map_weight]

theorem bind_const (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) : (μ₁.bind fun (_ : α) => μ₂) =  (μ₁ Set.univ) • μ₂.toMeasure := by
  rw [bind_coe, Function.comp_apply', Measure.bind_const]

theorem bind_bind (μ₁ : DiscreteMeasure α) (f : α → DiscreteMeasure β) (g : β → DiscreteMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  apply toMeasure_ext'
  repeat rw [bind_coe]
  rw [Measure.bind_bind (hf := AEMeasurable.of_discrete) (hg := AEMeasurable.of_discrete)]
  congr
  ext a' s
  rw [comp_apply, comp_apply, bind_coe]

theorem bind_comm (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) (f : α → β → DiscreteMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  ext x
  repeat simp_rw [bind_weight, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ tsum_congr (fun a ↦ ?_))
  ring

end bind

section pure

noncomputable def pure (a : α) : DiscreteMeasure α where
  weight := ({a} : Set α).indicator 1

@[simp]
lemma pure_weight (a : α) : (pure a).weight = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma pure_apply (a : α) (s : Set α) : (pure a) s = s.indicator 1 a := by
  rw [apply, pure_weight, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]
    rw [← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe (a : α) : (pure a).toMeasure = Measure.dirac a := by
  ext s
  rw [pure_apply, Measure.dirac_apply]

lemma map_toDirac : (toMeasure ∘ pure) = @Measure.dirac α ⊤ := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum (a : α) : HasSum (pure a).weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, pure_weight, ← tsum_subtype, tsum_singleton]
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

section seq

/-- The monadic sequencing operation for `DiscreteMeasure`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q : DiscreteMeasure (α → β)) (p :  Unit → DiscreteMeasure α) : DiscreteMeasure β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

lemma bind_map_eq_seq (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) : q.bind (fun m => (p ()).map m) = seq q p := by
  simp_rw [← bind_pure_comp]
  rfl

noncomputable instance : Seq DiscreteMeasure where
  seq := seq

variable (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) (b : β)

open scoped Classical in
@[simp]
theorem seq_weight : (seq q p).weight b = ∑' (f : α → β) (a : α), q.weight f * if b = f a then (p ()).weight a else 0 := by
  simp_rw [seq, bind_weight, pure_weight, Set.indicator, Set.mem_singleton_iff, ← ENNReal.tsum_mul_left]
  repeat apply tsum_congr (fun f ↦ ?_)
  split_ifs <;> simp

theorem seq_weight' : (seq q p).weight b = ∑' (f : α → β) (a : f⁻¹' {b}), q.weight f * (p ()).weight a := by
  simp_rw [seq_weight, ENNReal.tsum_mul_left, tsum_subtype, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr 1
  apply tsum_congr (fun g ↦ ?_)
  grind

@[simp]
theorem seq_weight'' : (seq q p).weight b = ∑' (f : α → β), q.weight f * ∑' (a : α), (f⁻¹' {b}).indicator (p ()).weight a := by
  simp_rw [seq, bind_weight, pure_weight, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr
  funext a
  simp only [Pi.one_apply, mul_ite, mul_one, mul_zero, Set.mem_preimage, Set.mem_singleton_iff]
  grind

lemma seq_pure {α β : Type u} (g : DiscreteMeasure (α → β)) (x : α) : seq g (fun _ ↦ pure x) = map (fun h => h x) g := by
  ext b
  rw [map_weight, apply, seq_weight'']
  simp_rw [pure_weight]
  apply tsum_congr (fun c ↦ ?_)
  simp_rw [Set.indicator_indicator, Set.inter_comm, ← Set.indicator_indicator, ← tsum_subtype, tsum_singleton]
  nth_rw 2 [← Set.indicator.mul_indicator_eq]
  congr 1

lemma pure_seq {α β : Type u} (g : (α → β)) (x : Unit → DiscreteMeasure α) : seq (pure g) x = (x ()).map g := by
  ext b
  rw [seq_weight'', pure_weight, map_weight, apply]
  simp_rw [mul_comm, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun c ↦ ?_)
  let f := fun a ↦ (a ⁻¹' {b}).indicator (x ()).weight c
  change ∑' (a : α → β), f a * ({g} : Set (α → β)).indicator 1 a= _
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype, tsum_singleton]

lemma seq_assoc (p : DiscreteMeasure α) (q : DiscreteMeasure (α → β)) (r : DiscreteMeasure (β → γ)) : (r.seq fun _ => q.seq fun _ => p) = ((map comp r).seq fun _ => q).seq fun _ => p := by
  simp_rw [← bind_map_eq_seq, ← bind_pure_comp, bind_bind, pure_bind]
  rfl






end seq

section monad

noncomputable instance : Applicative DiscreteMeasure where
  pure := pure
  map := map
  seq  := seq

@[simp, monad_norm]
lemma pure_eq_pure : @pure α = @Pure.pure DiscreteMeasure _ α := by rfl

@[simp, monad_norm]
lemma map_eq_map {α β : Type u} (f : α → β) (p : DiscreteMeasure α) : (map f p) = (Functor.map f p) := rfl

@[simp, monad_norm]
lemma seq_eq_seq {α β : Type u} (p : DiscreteMeasure (α → β)) (q : Unit → DiscreteMeasure α) : seq p q = Seq.seq p q := by
  rfl

lemma seqLeft_eq_map_seq {α β : Type u} (x : DiscreteMeasure α) (y : DiscreteMeasure β) : x <* y = (map (const β) x).seq fun _ => y := rfl

lemma rightSeq_eq_map_seq {α β : Type u} (x : DiscreteMeasure α) (y : DiscreteMeasure β) : x *> y = const α id <$> x <*> y := rfl

noncomputable instance : Monad DiscreteMeasure where
  bind := bind
  map := map

@[simp, monad_norm]
lemma bind_eq_bind {α β : Type u} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (bind μ g) = (Bind.bind μ g) := rfl

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulApplicative DiscreteMeasure := LawfulApplicative.mk
  (seqLeft_eq := seqLeft_eq_map_seq)
  (seqRight_eq := rightSeq_eq_map_seq)
  (pure_seq := fun q p ↦ pure_seq q (fun _ ↦ p))
  (map_pure := by
    intro α β m a
    rw [← pure_eq_pure, ← pure_eq_pure, ← map_eq_map, map_pure])
  (seq_pure := seq_pure)
  (seq_assoc := seq_assoc
)

instance : LawfulMonad DiscreteMeasure :=
  LawfulMonad.mk
    (pure_bind := pure_bind)
    (bind_assoc := bind_bind)
    (bind_pure_comp := bind_pure_comp)
    (bind_map := fun q p ↦ bind_map_eq_seq q (fun _ ↦ p))

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

-- Is this needed?
lemma map_seq {α β γ : Type u}(f : β → γ) (u : DiscreteMeasure (α → β)) (v : DiscreteMeasure α) : (u.seq (fun _ ↦ v)).map f = (u.map (fun (g : α → β) => f ∘ g)).seq (fun _ ↦ v) := by
  rw [map_eq_map, seq_eq_seq, map_eq_map, seq_eq_seq]
  simp [monad_norm]
  rfl


section sequence

lemma sequence_nil : sequence ([] : List (DiscreteMeasure α)) = (DiscreteMeasure.pure [] : DiscreteMeasure (List α)) := by
  simp [sequence]

-- Measures on lists

open Classical
lemma cons_pure_weight (a a' : α) (l l' : List α) : ((DiscreteMeasure.pure ∘ List.cons a') l').weight (a :: l) = if a = a' ∧ l = l' then 1 else 0 := by
  rw [comp_apply, DiscreteMeasure.pure_weight, Set.indicator]
  simp only [Set.mem_singleton_iff, List.cons.injEq, Pi.one_apply]

open Classical
lemma cons_pure_weight_of_empty (a' : α) : ((DiscreteMeasure.pure ∘ List.cons a') l').weight [] = 0 := by
  rw [comp_apply, DiscreteMeasure.pure_weight, Set.indicator]
  simp

open DiscreteMeasure
lemma cons_map_weight_of_empty (μs : DiscreteMeasure (List α)) (ν : DiscreteMeasure α) : (List.cons <$> ν <*> μs).weight [] = 0 := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_weight]
  simp_rw [← bind_eq_bind, bind_weight]
  simp_rw [← pure_eq_pure, cons_pure_weight_of_empty]
  simp

lemma cons_map_weight (μs : DiscreteMeasure (List α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (List.cons <$> ν <*> μs).weight (a :: l) = ν.weight a * (μs.weight l) := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_weight]
  simp_rw [← bind_eq_bind, bind_weight]
  simp_rw [← pure_eq_pure, cons_pure_weight]
  have h (a_1 : α) (a_2 : List α) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List α)).indicator (1 : List α → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs.weight a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]

lemma sequence_cons (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) : sequence (ν::μs) = List.cons <$> ν <*> (sequence μs) := by
  rfl

lemma sequence_weight_cons_of_empty (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) : (sequence (ν::μs)).weight [] = 0 := by
  exact cons_map_weight_of_empty (sequence μs) ν

lemma sequence_weight_cons (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (sequence (ν::μs)).weight (a::l) = (ν.weight a)*((sequence μs).weight l) := by
  exact cons_map_weight (sequence μs) ν l a

lemma nsupport_weight (μ : DiscreteMeasure α) (P : α → Prop) (hμ : μ.toMeasure {a : α | ¬ P a} = 0) (a : α) (ha : ¬ P a) : μ.weight a = 0 :=
  by
  rw [DiscreteMeasure.apply, ENNReal.tsum_eq_zero] at hμ
  specialize hμ a
  simp only [Set.mem_setOf_eq, ha, not_false_eq_true, Set.indicator_of_mem] at hμ
  exact hμ

lemma sequence_weight₀ (μs : List (DiscreteMeasure α)) (l : List α) (hl : l.length = μs.length) :
    (sequence μs).weight l = List.prod ((μs.map weight).zipWith (fun a b ↦ a b) l) :=
  by
  induction μs generalizing l with
  | nil =>
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    simp [sequence_nil]
    simp [hl, ← pure_eq_pure]
  | cons μ μs ih =>
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp [List.length_cons] at hl
      rw [sequence_weight_cons]
      rw [ih l hl]
      simp

lemma sequence_weight₁ (μs : List (DiscreteMeasure α)) (l : List α) (hl : ¬ l.length = μs.length) :
    (sequence μs).weight l = 0 :=
  by
  induction μs generalizing l with
  | nil =>
    rw [sequence_nil, pure_weight]
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

lemma sequence_weight (μs : List (DiscreteMeasure α)) (l : List α) :
    (sequence μs).weight l = if l.length = μs.length then List.prod ((μs.map weight).zipWith (fun a b ↦ a b) l) else 0 :=
  by
  split_ifs with hl
  · exact sequence_weight₀ μs l hl
  · exact sequence_weight₁ μs l hl

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


section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : DiscreteMeasure α) :  DiscreteMeasure (List α) := sequence (List.replicate n μ)

lemma iidSequence_weight (n : ℕ) (μ : DiscreteMeasure α) (l : List α) :
    (iidSequence n μ).weight l = ({l : List α | l.length = n}.indicator (fun l ↦ (List.prod (l.map μ.weight))) l) := by
  rw [Set.indicator]
  split_ifs with hl
  · rw [iidSequence, ← hl, sequence_weight]
    simp
  · simp only [Set.mem_setOf_eq] at hl
    rw [iidSequence, sequence_weight]
    simp [hl]

lemma iidSequence_weight' (n : ℕ) (μ : DiscreteMeasure α) [DecidableEq α] (l : List α) :
    (iidSequence n μ).weight l = ({l : List α | l.length = n}.indicator (fun l ↦ (∏' (a : α), (μ.weight a) ^ (l.count (α := α) a))) l) := by
  rw [iidSequence_weight n μ l, Set.indicator]
  split_ifs with hl <;> simp at hl
  · rw [list_map_prod_eq_count]
    simp only [Set.mem_setOf_eq, hl, Set.indicator_of_mem]
  · simp [hl]

lemma pure_sequence (ν : DiscreteMeasure α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : DiscreteMeasure α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

end iidSequence

end sequence

end DiscreteMeasure





section DiscreteProbabilityMeasure

/-- A `DiscreteProbabilityMeasure` is a `DiscreteMeasure` with the property `IsProbabilityMeasure`. -/
def DiscreteProbabilityMeasure' (α : Type*) : Type _ :=
  { μ : DiscreteMeasure α // HasSum μ.weight 1 }

structure DiscreteProbabilityMeasure (α : Type*) where
  toDiscreteMeasure : DiscreteMeasure α
  hasSum_one : HasSum toDiscreteMeasure.weight 1

instance (μ : DiscreteProbabilityMeasure α) : IsProbabilityMeasure μ.toDiscreteMeasure.toMeasure := by
  rw [DiscreteMeasure.isProbabilityMeasure_iff]
  exact μ.hasSum_one

/-- A discrete probability measure can be interpreted as a discrete measure. -/
noncomputable instance : Coe (DiscreteProbabilityMeasure α) (DiscreteMeasure α) where
  coe := DiscreteProbabilityMeasure.toDiscreteMeasure

noncomputable instance : CoeFun (DiscreteProbabilityMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toDiscreteMeasure.toMeasure

namespace DiscreteProbabilityMeasure

/-- Coercion from `MeasureTheory.DiscreteProbabilityMeasure α` to `MeasureTheory.DiscreteMeasure α`. -/
--@[coe]
--def toDiscreteMeasure : DiscreteProbabilityMeasure α → DiscreteMeasure α := DiscreteProbabilityMeasure.toDiscreteMeasure

noncomputable def toProbabilityMeasure (μ : DiscreteProbabilityMeasure α) : @ProbabilityMeasure α ⊤ := ⟨μ.toDiscreteMeasure, by infer_instance⟩

noncomputable instance :
  CoeFun (DiscreteProbabilityMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toDiscreteMeasure.toMeasure

def ofDiscreteMeasure (μ : DiscreteMeasure α) (hμ : HasSum μ.weight 1) : DiscreteProbabilityMeasure α where
  toDiscreteMeasure := μ
  hasSum_one := hμ

def ofDiscreteMeasure' (μ : DiscreteMeasure α) (hμ : IsProbabilityMeasure μ.toMeasure) : DiscreteProbabilityMeasure α where
  toDiscreteMeasure := μ
  hasSum_one := (DiscreteMeasure.isProbabilityMeasure_iff μ).mp hμ

@[simp]
lemma apply_univ_eq_one (P : DiscreteProbabilityMeasure α) : P Set.univ = 1 := by
  rw [DiscreteMeasure.apply_univ]
  exact HasSum.tsum_eq P.hasSum_one

lemma prob_le_one (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≤ 1 := MeasureTheory.prob_le_one

lemma measure_ne_top (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≠ ⊤ := MeasureTheory.measure_ne_top P s

@[simp]
lemma toProbabilityMeasure_apply (P : DiscreteProbabilityMeasure α) (s : Set α) : (toProbabilityMeasure P).toMeasure s = ∑' (i : α), s.indicator P.toDiscreteMeasure.weight i := by
  rw [← DiscreteMeasure.apply] ; rfl

lemma singleton_eq_weight (μ : DiscreteProbabilityMeasure α) : (fun (a : α) ↦ μ {a}) = μ.toDiscreteMeasure.weight := by
  exact μ.toDiscreteMeasure.singleton_eq_weight

@[ext]
lemma ext {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : ∀ (a : α), μ₁.toDiscreteMeasure.weight a = μ₂.toDiscreteMeasure.weight a) : μ₁ = μ₂ := by
  cases μ₁
  cases μ₂
  simp only [mk.injEq] at h ⊢
  ext x
  exact h x

lemma ext_val' {μ₁ μ₂ : DiscreteProbabilityMeasure α} :
  (toDiscreteMeasure μ₁ = toDiscreteMeasure μ₂) ↔ μ₁ = μ₂ :=
by
  exact ⟨fun h ↦ ext fun a ↦ by rw [h], fun h ↦ by rw [h]⟩

lemma ext_weight {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : μ₁.toDiscreteMeasure.weight = μ₂.toDiscreteMeasure.weight) : μ₁ = μ₂ :=
by
  ext x
  rw [h]

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteProbabilityMeasure α} (h : μ₁.toDiscreteMeasure.toMeasure = μ₂.toDiscreteMeasure.toMeasure) : μ₁ = μ₂ :=
by
  rw [← ext_val']
  exact DiscreteMeasure.toMeasure_ext' h

-- map
lemma map_isProbabilityMeasure (g : α → β) (μ : DiscreteProbabilityMeasure α) : HasSum (μ.toDiscreteMeasure.map g).weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp_rw [μ.toDiscreteMeasure.map_weight]
  rw [← apply_univ_eq_one μ]
  rw [μ.toDiscreteMeasure.apply_univ' _ (pairwise_disjoint_fiber g)]
  ext x ; simp

noncomputable def map (g : α → β) (μ : DiscreteProbabilityMeasure α) : (DiscreteProbabilityMeasure β) where
  toDiscreteMeasure := ⟨fun b ↦ μ (g⁻¹' {b})⟩
  hasSum_one := map_isProbabilityMeasure g μ

--example {α β : Type u} (f : α → β) (μ : DiscreteProbabilityMeasure α): f <$> μ = (map f μ) := --by rfl

lemma map_coe (g : α → β) (μ : DiscreteProbabilityMeasure α) : (μ.map g) = μ.toDiscreteMeasure.map g := by
  rfl

--example {α β : Type u} (f : α → β) (μ : DiscreteProbabilityMeasure α) : f <$> μ.toDiscreteMeasure = (f <$> μ).--val := by rfl

lemma map_map (μ : DiscreteProbabilityMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext x
  simp [map_coe, DiscreteMeasure.map_map]

theorem id_map (μ : DiscreteProbabilityMeasure α) :
μ.map id = μ := by
  ext x
  simp [map_coe]

-- join
noncomputable def join (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : (DiscreteProbabilityMeasure α) where
  toDiscreteMeasure := (DiscreteMeasure.map toDiscreteMeasure m.toDiscreteMeasure).join
  hasSum_one := by
    refine DiscreteMeasure.join_hasSum (DiscreteMeasure.map toDiscreteMeasure m.toDiscreteMeasure) ?_ ?_
    · exact map_isProbabilityMeasure toDiscreteMeasure m
    · intro μ
      rw [← not_imp_not, ne_eq, not_not]
      intro hμ
      rw [DiscreteMeasure.map_weight, DiscreteMeasure.apply₂, ENNReal.tsum_eq_zero]
      simp only [Subtype.forall, Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ν hν ↦ False.elim <| hμ <| hν.symm ▸ ν.hasSum_one

lemma join_coe (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : m.join = (DiscreteMeasure.map toDiscreteMeasure m.toDiscreteMeasure).join := by
  rfl

-- bind
noncomputable def bind (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : (DiscreteProbabilityMeasure β) := (μ.map g).join

-- Such a lemma must be generic!
--lemma coe_fun (f : γ → DiscreteProbabilityMeasure α) : Subtype.val ∘ f = fun c ↦ Subtype.val (f c) := by
--  rfl


lemma bind_coe (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : μ.bind g = μ.toDiscreteMeasure.bind (toDiscreteMeasure ∘ g) := by
  rw [bind, DiscreteMeasure.bind, join_coe, ← DiscreteMeasure.map_map]
  rfl

lemma join_map_map (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) (g : α → β) : map g m.join = (map (map g) m).join := by
  ext x
  rw [map_coe, join_coe, join_coe, map_coe, ← DiscreteMeasure.join_map_map, DiscreteMeasure.map_map, DiscreteMeasure.map_map]
  rfl

theorem bind_const (μ₁ : DiscreteProbabilityMeasure α) (μ₂ : DiscreteProbabilityMeasure β) : (μ₁.bind fun (_ : α) => μ₂) = μ₂ := by
  rw [← ext_val']
  apply DiscreteMeasure.toMeasure_ext'
  rw [bind_coe, Function.comp_apply', DiscreteMeasure.bind_const, measure_univ, one_smul]

theorem bind_bind (μ₁ : DiscreteProbabilityMeasure α) (f : α → DiscreteProbabilityMeasure β) (g : β → DiscreteProbabilityMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  rw [← ext_val']
  rw [bind_coe, bind_coe, bind_coe, DiscreteMeasure.bind_bind]
  congr
  ext s
  rw [comp_apply, comp_apply, bind_coe]

theorem bind_comm (μ₁ : DiscreteProbabilityMeasure α) (μ₂ : DiscreteProbabilityMeasure β) (f : α → β → DiscreteProbabilityMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  rw [← ext_val']
  repeat rw [bind_coe]
  rw [Function.comp_apply']
  rw [Function.comp_apply']
  simp_rw [bind_coe]
  rw [DiscreteMeasure.bind_comm]
  rfl
section pure

noncomputable def pure (a : α) : DiscreteProbabilityMeasure α :=
  ⟨DiscreteMeasure.pure a, DiscreteMeasure.pure_hasSum a⟩

@[simp]
lemma pure_coe (a : α) : DiscreteProbabilityMeasure.pure a = (DiscreteMeasure.pure a) := by
  rfl

lemma pure_coe' : DiscreteMeasure.pure (α := α)= (toDiscreteMeasure ∘ DiscreteProbabilityMeasure.pure) := by
  rfl

lemma map_pure (a : α) (f : α → β) : (DiscreteProbabilityMeasure.pure a).map f = DiscreteProbabilityMeasure.pure (f a) := by
  rw [← ext_val']
  rw [map_coe, pure_coe, DiscreteMeasure.map_pure]
  rfl

theorem pure_bind (a : α) (f : α → DiscreteProbabilityMeasure β) :
(pure a).bind f = f a := by
  rw [← ext_val']
  rw [bind_coe, pure_coe]
  rw [DiscreteMeasure.pure_bind]
  rfl

theorem bind_pure (μ : DiscreteProbabilityMeasure α) :
μ.bind pure = μ := by
  rw [← ext_val']
  rw [bind_coe, ← pure_coe']
  rw [DiscreteMeasure.bind_pure]

lemma bind_pure_comp (f : α → β) (μ : DiscreteProbabilityMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  rw [← ext_val']
  rw [bind_coe, comp_apply', map_coe]
  simp_rw [pure_coe]
  rw [DiscreteMeasure.bind_pure_comp]


end pure
section seq

/-- The monadic sequencing operation for `DiscreteProbabilityMeasure`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q : DiscreteProbabilityMeasure (α → β)) (p :  Unit → DiscreteProbabilityMeasure α) : DiscreteProbabilityMeasure β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

lemma seq_coe (q : DiscreteProbabilityMeasure (α → β)) (p :  Unit → DiscreteProbabilityMeasure α) : q.seq p = q.toDiscreteMeasure.seq (toDiscreteMeasure ∘ p) := by
  rw [seq, DiscreteMeasure.seq, bind_coe, comp_apply']
  simp_rw [bind_coe]
  rfl

lemma bind_map_eq_seq (q : DiscreteProbabilityMeasure (α → β)) (p : Unit → DiscreteProbabilityMeasure α) : q.bind (fun m => (p ()).map m) = seq q p := by
  rw [← ext_val']
  simp_rw [bind_coe, seq_coe, comp_apply', map_coe, ← DiscreteMeasure.bind_map_eq_seq]

noncomputable instance : Seq DiscreteProbabilityMeasure where
  seq := seq

variable (q : DiscreteProbabilityMeasure (α → β)) (p : Unit → DiscreteProbabilityMeasure α) (b : β)

lemma seq_pure {α β : Type u} (g : DiscreteProbabilityMeasure (α → β)) (x : α) : seq g (fun _ ↦ pure x) = map (fun h => h x) g := by
  rw [← ext_val']
  rw [seq_coe, map_coe, comp_apply', pure_coe, DiscreteMeasure.seq_pure]

lemma pure_seq {α β : Type u} (g : (α → β)) (x : Unit → DiscreteProbabilityMeasure α) : seq (pure g) x = (x ()).map g := by
  rw [← ext_val']
  rw [seq_coe, map_coe, pure_coe, DiscreteMeasure.pure_seq]
  rfl

lemma seq_assoc (p : DiscreteProbabilityMeasure α) (q : DiscreteProbabilityMeasure (α → β)) (r : DiscreteProbabilityMeasure (β → γ)) : (r.seq fun _ => q.seq fun _ => p) = ((map comp r).seq fun _ => q).seq fun _ => p := by
  rw [← ext_val']
  simp_rw [seq_coe, map_coe, comp_apply', seq_coe, ← DiscreteMeasure.seq_assoc]
  rfl

end seq

section monad

noncomputable instance : Functor DiscreteProbabilityMeasure where
  map := map

noncomputable instance : Applicative DiscreteProbabilityMeasure where
  pure := pure
  map := map
  seq  := seq

@[simp, monad_norm]
lemma pure_eq_pure : @pure α = @Pure.pure DiscreteProbabilityMeasure _ α := by rfl

@[simp, monad_norm]
lemma map_eq_map {α β : Type u} (f : α → β) (p : DiscreteProbabilityMeasure α) : (map f p) = (Functor.map f p) := rfl

@[simp, monad_norm]
lemma seq_eq_seq {α β : Type u} (p : DiscreteProbabilityMeasure (α → β)) (q : Unit → DiscreteProbabilityMeasure α) : seq p q = Seq.seq p q := by
  rfl

lemma seqLeft_eq_map_seq {α β : Type u} (x : DiscreteProbabilityMeasure α) (y : DiscreteProbabilityMeasure β) : x <* y = (map (const β) x).seq fun _ => y := rfl

lemma rightSeq_eq_map_seq {α β : Type u} (x : DiscreteProbabilityMeasure α) (y : DiscreteProbabilityMeasure β) : x *> y = const α id <$> x <*> y := rfl

noncomputable instance : Monad DiscreteProbabilityMeasure where
  bind := bind
  map := map

@[simp, monad_norm]
lemma bind_eq_bind {α β : Type u} (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β)  : (bind μ g) = (Bind.bind μ g) := rfl

instance : LawfulFunctor DiscreteProbabilityMeasure where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulApplicative DiscreteProbabilityMeasure := LawfulApplicative.mk
  (seqLeft_eq := seqLeft_eq_map_seq)
  (seqRight_eq := rightSeq_eq_map_seq)
  (pure_seq := fun q p ↦ pure_seq q (fun _ ↦ p))
  (map_pure := by
    intro α β m a
    rw [← pure_eq_pure, ← pure_eq_pure, ← map_eq_map, map_pure])
  (seq_pure := seq_pure)
  (seq_assoc := seq_assoc
)

noncomputable instance : Monad DiscreteProbabilityMeasure where
  pure a := pure a
  bind pa pb := pa.bind pb

instance : LawfulMonad DiscreteProbabilityMeasure :=
  LawfulMonad.mk
    (pure_bind := pure_bind)
    (bind_assoc := bind_bind)
    (bind_pure_comp := bind_pure_comp)
    (bind_map := fun q p ↦ bind_map_eq_seq q (fun _ ↦ p))

noncomputable instance : ULiftable DiscreteProbabilityMeasure.{u} DiscreteProbabilityMeasure.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by
        simp only [map_map, Equiv.symm_comp_self, id_map]
      right_inv := fun a => by
        simp only [map_map, Equiv.self_comp_symm, id_map]
      }

-- We have do notation (as for PMF)!
example (μ : DiscreteProbabilityMeasure α) : μ = do
  let X ← μ
  return X
  := by
  simp

end monad

section lintegral

lemma lintegral_coe (μ : DiscreteProbabilityMeasure α) (g : α → ℝ≥0): ∫⁻ (a : α), g a ∂ μ.toDiscreteMeasure.toMeasure = ∑' (a : α),  (μ.toDiscreteMeasure.weight a) * g a := by
  rw [← DiscreteMeasure.lintegral_eq_toMeasure]
  rw [DiscreteMeasure.lintegral]

end lintegral

end DiscreteProbabilityMeasure

end DiscreteProbabilityMeasure


namespace DiscreteProbabilityMeasure

section sequence

lemma sequence_coe (μ : List (DiscreteProbabilityMeasure α)) : (sequence μ).toDiscreteMeasure = sequence (μ.map toDiscreteMeasure) := by
  induction μ with
  | nil =>
    simp
    rfl
  | cons a l hl =>
    rw [sequence] at hl
    rw [sequence, List.traverse_cons (F := DiscreteProbabilityMeasure), ← seq_eq_seq, seq_coe, comp_apply', hl, ← map_eq_map, map_coe, DiscreteMeasure.map_eq_map, DiscreteMeasure.seq_eq_seq, ← DiscreteMeasure.sequence_cons]
    rfl

noncomputable def iidSequence (n : ℕ) (μ : DiscreteProbabilityMeasure α) :  DiscreteProbabilityMeasure (List α) := sequence (List.replicate n μ)

lemma iidSequence_coe (n : ℕ) (μ : DiscreteProbabilityMeasure α) : (iidSequence n μ).toDiscreteMeasure = (DiscreteMeasure.iidSequence n μ.toDiscreteMeasure) := by
  rw [iidSequence, sequence_coe, DiscreteMeasure.iidSequence, List.map_replicate]

-- todo lintegral_sum_iidSequence

end sequence
section coin

open Bool ENNReal

noncomputable def coin (p : ℝ≥0) (h : p ≤ 1) : DiscreteProbabilityMeasure Bool where
  toDiscreteMeasure := ⟨fun (b : Bool) ↦ if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞)⟩
  hasSum_one := by
    simp [Summable.hasSum_iff ENNReal.summable, h]

lemma coin_weight (p : ℝ≥0) (h : p ≤ 1) (b : Bool) : (coin p h).1.weight b = if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞) := by
  rfl

lemma lintegral_coin (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ≥0∞): ∫⁻ (a : Bool), (g a) ∂ (coin p h).toDiscreteMeasure.toMeasure = (1 - p) * (g false) + p * (g true) := by
  rw [← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral]
  simp_rw [coin]
  rw [tsum_bool]
  grind

lemma lintegral_map_coin (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ≥0): ∫⁻ (a : ℝ≥0), (id a) ∂ (map g (coin p h)).toDiscreteMeasure.toMeasure = ∫⁻ (a : Bool), (g a) ∂ (coin p h).toDiscreteMeasure.toMeasure := by
  rw [map_coe, DiscreteMeasure.map_coe, @MeasureTheory.lintegral_map _ _ ⊤ ⊤ _ _ _ (by measurability) (by exact fun ⦃t⦄ a => a), ← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral, ← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral]
  rfl

lemma expectation_coin (p : ℝ≥0) (h : p ≤ 1) : ∫⁻ (a : Bool), ({true} : Set Bool).indicator 1 a ∂ (coin p h).toDiscreteMeasure.toMeasure = p := by
  rw [lintegral_coin]
  simp

lemma Bool.mem_not (b : Bool) : not ⁻¹' {b} = {!b} := by
    ext y; cases' y <;> simp

lemma coin_not (p : ℝ≥0) (h : p ≤ 1) : (coin p h).map not  = coin (1-p) (tsub_le_self) := by
  ext x
  rw [DiscreteProbabilityMeasure.map_coe]
  cases x <;> rw [DiscreteMeasure.map_weight, Bool.mem_not, DiscreteMeasure.apply_singleton', coin_weight, coin_weight] <;> norm_cast
  rw[tsub_tsub_cancel_of_le h]
  simp

end coin

section binom

-- Defining the binomial distribution via the weights
noncomputable def binom₁ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure ℕ where
  toDiscreteMeasure := ⟨fun k ↦ (p ^ k * (1 - p) ^ (n - k)) * (Nat.choose n k)⟩
  hasSum_one := by
    have g : ∑' (k : ℕ), (p : ℝ≥0∞) ^ k * (1 - p) ^ (n - k) * (n.choose k) = ∑ (k ∈ Finset.range (n + 1)), p ^ k * (1 - p) ^ (n - k) * (n.choose k) := by
      simp only [ENNReal.coe_finset_sum, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_sub,
        ENNReal.coe_one, ENNReal.coe_natCast]
      refine tsum_eq_sum (fun b hb ↦ ?_)
      simp only [Finset.mem_range, not_lt, mul_eq_zero, pow_eq_zero_iff', ENNReal.coe_eq_zero, ne_eq, Nat.cast_eq_zero] at hb ⊢
      exact Or.inr (Nat.choose_eq_zero_iff.mpr hb)
    rw [Summable.hasSum_iff ENNReal.summable, g, ← add_pow p (1 - p) n]
    simp [h]

-- Defining the binomial distribution as the sum of toNats in a sequence of Bernoulli trials
noncomputable def binom₂ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure ℕ := ((sequence <| List.replicate n (coin p h)).map (List.map Bool.toNat)).map List.sum

-- Defining the binomial distribution as the count of trues in a sequence of Bernoulli trials
noncomputable def binom₃ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure ℕ := (DiscreteProbabilityMeasure.iidSequence n (coin p h)).map (List.count (α := Bool) true)

-- To List.bool
lemma List.sum_eq_count : List.sum ∘ List.map Bool.toNat = List.count true := by
  ext l
  induction l with
  | nil =>
    simp
  | cons a l hl => grind

lemma binom₂_eq_binom₃ : binom₂ = binom₃ := by
  funext p h n
  rw [binom₂, binom₃, iidSequence, map_map, List.sum_eq_count]

-- As in `binom₃` but using `do`-notation.
noncomputable def binom₄ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :=
  do
    let X ← sequence (List.replicate n (coin p h))
    return X.count true

lemma binom₃_eq_binom₄ : binom₃ = binom₄ := by
  funext p hp n
  rw [binom₃, binom₄, iidSequence]
  simp [monad_norm]

-- Defining the binomial distribution inductively
noncomputable def binom₅ (p : ℝ≥0) (h : p ≤ 1) : (n : ℕ) → DiscreteProbabilityMeasure ℕ
  | 0 => DiscreteProbabilityMeasure.pure 0
  | n+1 => do
    let X ← binom₅ p h n
    let Head ← coin p h
    return X + Head.toNat

lemma binom₅_succ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : binom₅ p h (n + 1) = (binom₅ p h n >>= fun X => coin p h >>= Pure.pure ∘ fun a => X + a.toNat)
  := by
  simp [binom₅, monad_norm]

lemma binom₅_succ' (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : binom₅ p h (n + 1) = (coin p h >>= fun a => binom₅ p h n >>= Pure.pure ∘ fun X => X + a.toNat)
  := by
  simp [binom₅_succ, ← bind_eq_bind]
  rw [DiscreteProbabilityMeasure.bind_comm]
  rfl

-- `binom₅` using do-notation
lemma binom₅_induction(p : ℝ≥0) (h : p ≤ 1) (P : ℕ → DiscreteProbabilityMeasure ℕ) (zero : P 0 = pure 0) (succ : ∀ n, P (n + 1) = do
    let X ← P n
    let Head ← coin p h
    return X + Head.toNat) : P = binom₅ p h := by
  funext n
  induction n with
  | zero =>
    simp [binom₅, zero]
  | succ n hn =>
    simp [monad_norm, binom₅] at succ ⊢
    rw [succ n, hn]

open Std.Do

lemma LawfulMonad.sum_induction (n : ℕ) {m : Type → Type} [Monad m] [LawfulMonad m] (x : m ℕ) (P : ℕ → m ℕ) (hP : ∀ n, P n =
  do
    let mut sum := 0
    for _ in (List.range n) do
      let X ← x
      sum := sum + X
    return sum) :
  P (n + 1) =
  do
    let sum ← P n
    let X ← x
    return sum + X
    := by
  have h : List.range (n + 1) = ((List.range n).append [n]) := by
    simp only [List.range_succ, List.append_eq]
  simp at hP ⊢
  simp [monad_norm] at hP ⊢
  simp [hP, h]

noncomputable def binom₆ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :=
  do
    let mut S := 0
    for _ in List.range n do
      let X ← Bool.toNat <$> (coin p h)
      S := S + X
    return S

lemma binom₆_succ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : binom₆ p h (n + 1) = do
  let S ← binom₆ p h n
  let X ← Bool.toNat <$> coin p h
  return S + X
  := by
  exact LawfulMonad.sum_induction _ _ _ (fun n ↦ rfl)

lemma binom₅_eq_binom₆ : binom₅ = binom₆ := by
  funext p hp n
  induction n with
  | zero =>
    simp [binom₅, binom₆]
  | succ n hn =>
    rw [binom₆_succ, ← hn, binom₅_succ]
    simp [monad_norm]

lemma binom₆_norm (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : binom₆ p h n = List.foldlM (fun b _ => coin p h >>= Pure.pure ∘ fun c => b + c.toNat) 0 (List.range n) := by
  simp [binom₆]
  simp [monad_norm]

lemma binom₃_eq_binom₅ : binom₃ = binom₅ := by
  funext p hp n
  rw [binom₃, iidSequence]
  simp [monad_norm]
  induction n with
  | zero =>
    simp [binom₅, sequence]
  | succ n hn =>
    rw [List.replicate_succ, sequence, List.traverse_cons, ← sequence, binom₅_succ']
    rw [← hn]
    simp [monad_norm] at hn ⊢
    have f (X : Bool) (a : List Bool) : List.count true (X :: a) = List.count true a + X.toNat := by
      rw [List.count_cons]
      simp only [beq_true, Nat.add_left_cancel_iff]
      split_ifs with h <;> simp [h]
    simp_rw [f]


lemma List.mem_idxsOf_lt (l : List α) [DecidableEq α] (a : α) (i : ℕ) (hi : i ∈ List.idxsOf a l) : i < l.length := by
  grind

def trueFinset (l : List Bool) (n : ℕ) (hl : n = l.length) : Finset (Fin n) := ((l.idxsOf true).pmap Fin.mk (fun i ↦ hl ▸ fun hi ↦ List.mem_idxsOf_lt l true i hi)).toFinset

lemma filter_eq_count'' (n : ℕ) (l : List Bool) (hl : n = l.length) : (trueFinset l n hl).card = l.count true := by
  rw [trueFinset, List.card_toFinset, List.Nodup.dedup, List.length_pmap, List.length_idxsOf]
  refine List.Nodup.pmap (by simp only [Fin.mk.injEq, imp_self, implies_true])
    (by simp only [List.nodup_idxsOf])

open List

lemma List.ofFn_trueFinset (n : ℕ) (l : List Bool) (hl : n = l.length): (List.ofFn fun i => decide (i ∈ trueFinset l n hl)) = l := by
  apply List.ext_get
  · simp only [hl, List.length_ofFn]
  · intro i hi₁ hi₂
    simp [trueFinset, hi₂]

lemma trueFinset_eq_Fn (n : ℕ) (s : Finset (Fin n)) :
  s = (trueFinset (List.ofFn fun i => decide (i ∈ s)) n (by simp only [List.length_ofFn])) := by
  simp only [trueFinset]
  ext x
  simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · use x.val
    use ⟨x.prop, ?_⟩
    simp [h]
  · obtain ⟨y, ⟨⟨hy11, hy12⟩, hy2⟩⟩ := h
    rwa [← hy2]

def Equiv.ListBool_trueFinset (k n : ℕ) : { l : List Bool | n = l.length ∧ l.count true = k } ≃ { s : Finset (Fin n) | s.card = k } where
  toFun := fun ⟨l, hl⟩ ↦ ⟨trueFinset l n hl.1,
  by
    rw [Set.mem_setOf_eq, filter_eq_count'' n l hl.1]
    exact (filter_eq_count'' n l hl.1) ▸ hl.2⟩
  invFun := fun ⟨s, hs⟩ ↦ ⟨List.ofFn (fun i ↦ i ∈ s), by
    simp only [Set.mem_setOf_eq, List.length_ofFn, true_and]
    rw [← filter_eq_count'' n _ (by simp)]
    rw [← trueFinset_eq_Fn n s]
    exact hs⟩
  left_inv := by
    simp only [LeftInverse, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, Subtype.mk.injEq,
      forall_and_index]
    exact fun l hl hyp ↦ ofFn_trueFinset n l hl
  right_inv := by
    simp [RightInverse, LeftInverse]
    intro s hs
    exact Eq.symm (trueFinset_eq_Fn n s)

lemma Finset.cardk_card (n k : ℕ) : Finset.card { s : Finset (Fin n) | s.card = k } = n.choose k := by
  rw [← Finset.card_fin n, ← Finset.card_powersetCard]
  simp

lemma Set.cardk_encard (n k : ℕ) : Set.encard { s : Finset (Fin n) | s.card = k } = n.choose k := by
  rw [← Finset.cardk_card, ← Set.encard_coe_eq_coe_finsetCard]
  congr ; simp

lemma count_encard_eq_choose (k n : ℕ) : { l : List Bool | n = l.length ∧ l.count true = k}.encard = (n.choose k) := by
  haveI h : Finite ↑{l | n = l.length ∧ List.count true l = k} := by
    apply Finite.of_equiv (α := { s : Finset (Fin n) | s.card = k })
    exact (Equiv.ListBool_trueFinset k n).symm
  rw [Set.encard_congr (Equiv.ListBool_trueFinset k n)]
  exact Set.cardk_encard n k

lemma List.length_sub_count_false (l : List Bool) : l.length - l.count true = l.count false := by
  rw [Nat.sub_eq_iff_eq_add (List.count_le_length), add_comm, List.count_true_add_count_false]

lemma binom₁_eq_binom₃ : binom₃ = binom₁ := by
  ext p h n k
  rw [binom₁]
  have g (i : List Bool) (s : Set ℕ): (s.indicator (@OfNat.ofNat (ℕ → ℝ≥0∞) 1 One.toOfNat1) ((List.count true i))) = (((List.count true))⁻¹' s).indicator 1 i := by
    rfl
  calc
    ((binom₃ p h n).toDiscreteMeasure.weight k) = (∑' (i : List Bool),
    {l | l.length = n}.indicator (fun l => ∏' (a : Bool), (coin p h).1.weight a ^ List.count (α := Bool) a l) i *
      ({k} : Set ℕ).indicator 1 ((List.count true i))) := by
      rw [binom₃, map_coe, iidSequence_coe, DiscreteMeasure.map_weight']
      simp_rw [DiscreteMeasure.iidSequence_weight' n (coin p h).toDiscreteMeasure]
    _ = ∑' (i : List Bool),
    (List.count true ⁻¹' {k} ∩ {l | l.length = n}).indicator
      (fun l => ∏' (a : Bool), (coin p h).1.weight a ^ List.count a l) i := by
        simp_rw [g _ ({k} : Set ℕ)]
        simp_rw [Set.indicator.mul_indicator_eq]
        rw [Set.indicator_indicator]
    _ = ∑' (x : ↑(List.count true ⁻¹' {k} ∩ {l | l.length = n})), ↑p ^ List.count true ↑x * (1 - ↑p) ^ List.count false ↑x := by
        rw [← tsum_subtype]
        simp_rw [tprod_bool, coin_weight, mul_comm]
        simp only [↓reduceIte, Bool.false_eq_true]
    _ = ∑' (x : ↑(List.count true ⁻¹' {k} ∩ {l | l.length = n})), ↑p ^ k * (1 - ↑p) ^ (n - k) := by
        congr
        ext x
        rw [x.prop.1, ← List.length_sub_count_false, x.prop.2, x.prop.1]
    _ = (p ^ k * (1 - p) ^ (n - k)) * (Nat.choose n k) := by
        simp
        rw [mul_comm]
        congr
        norm_cast
        simp_rw [eq_comm (b := n)]
        rw [Set.inter_comm, ← count_encard_eq_choose k n]
        rfl

end binom

end DiscreteProbabilityMeasure

section support

section DiscreteMeasure

namespace DiscreteMeasure

def support (μ : DiscreteMeasure α) : Set α :=
  Function.support μ.weight

@[simp]
theorem mem_support_iff (μ : DiscreteMeasure α) (a : α) : a ∈ μ.support ↔ μ.weight a ≠ 0 := Iff.rfl

theorem support_subset_iff (μ : DiscreteMeasure α) (s : Set α) : μ.support ⊆ s ↔ ∀ a ∉ s, μ.weight a = 0 := by
  exact support_subset_iff'

@[simp]
theorem support_nonempty {μ : DiscreteMeasure α} (hμ : ∑' (i : α), μ.weight i ≠ 0) : μ.support.Nonempty := by
  apply Function.support_nonempty_iff.2
  simp only [ne_eq, ENNReal.tsum_eq_zero, not_forall] at hμ
  obtain ⟨x, hx⟩ := hμ
  exact fun a => hx (congrFun a x)

@[simp]
theorem support_countable (μ : DiscreteMeasure α) (hμ : ∑' (i : α), μ.weight i ≠ ⊤) : μ.support.Countable := by
  apply Summable.countable_support_ennreal hμ

def restrict (μ : DiscreteMeasure α) (s : Set α) : DiscreteMeasure s := ⟨fun a ↦ μ.weight a.val⟩

lemma restrict_weight (μ : DiscreteMeasure α) (s : Set α) (a : s) : (μ.restrict s).weight a = μ.weight a := by
  simp [restrict]

end DiscreteMeasure

end DiscreteMeasure

namespace DiscreteProbabilityMeasure

lemma hasSum_tsum (p : DiscreteProbabilityMeasure α) : ∑' (a : α), p.toDiscreteMeasure.weight a = 1 := by
  exact HasSum.tsum_eq p.hasSum_one

@[simp]
theorem support_nonempty (p : DiscreteProbabilityMeasure α) : p.toDiscreteMeasure.support.Nonempty := DiscreteMeasure.support_nonempty <| ne_zero_of_eq_one (HasSum.tsum_eq p.hasSum_one)

@[simp]
theorem support_countable (p : DiscreteProbabilityMeasure α) : p.toDiscreteMeasure.support.Countable := by
  apply DiscreteMeasure.support_countable
  exact (HasSum.tsum_eq p.hasSum_one) ▸ ENNReal.one_ne_top

def restrict (p : DiscreteProbabilityMeasure α) (s : Set α) (hs : p.toDiscreteMeasure.support ⊆ s) : DiscreteProbabilityMeasure s where
  toDiscreteMeasure := p.toDiscreteMeasure.restrict s
  hasSum_one := by
    simp_rw [Summable.hasSum_iff ENNReal.summable, DiscreteMeasure.restrict_weight, ← HasSum.tsum_eq p.hasSum_one]
    exact tsum_subtype_eq_of_support_subset hs

def restrict' (p : DiscreteProbabilityMeasure α) (P : α → Prop) (hP : p.toDiscreteMeasure.support ⊆ {a | P a}) : DiscreteProbabilityMeasure {a : α // P a} := restrict p {a | P a} hP

noncomputable def restrict_toFin (p : DiscreteProbabilityMeasure ℕ) (n : ℕ) (hP : p.toDiscreteMeasure.support ⊆ {k | k < n + 1}) : DiscreteProbabilityMeasure (Fin (n + 1)) where
  toDiscreteMeasure := (p.restrict {k | k < n + 1} hP).map (fun k ↦ Fin.mk k.val k.prop)
  hasSum_one := by apply map_isProbabilityMeasure

lemma support_binom₁ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : (binom₁ p h n).toDiscreteMeasure.support ⊆ {k | k < n + 1} := by
  rw [DiscreteMeasure.support_subset_iff]
  intro a ha
  simp only [Set.mem_setOf_eq, not_lt, binom₁, mul_eq_zero, pow_eq_zero_iff', ENNReal.coe_eq_zero, ne_eq, Nat.cast_eq_zero] at ha ⊢
  exact Or.inr (Nat.choose_eq_zero_iff.mpr ha)

noncomputable def binom₁_Fin' (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure (Fin (n + 1)) :=
  (binom₁ p h n).restrict_toFin n (support_binom₁ p h n)

end DiscreteProbabilityMeasure

end support



/- The following is deprecated. The reason is that the monad instance is not good to work with in computations. -/

section DiscreteMeasure'

open MeasureTheory

open scoped ENNReal

def DiscreteMeasure' (α : Type*) := @Measure α ⊤
namespace DiscreteMeasure'

noncomputable instance : Coe (DiscreteMeasure' α) (@Measure α ⊤) where
  coe := id

def toMeasure (μ : DiscreteMeasure' α) : @Measure α ⊤ := μ

noncomputable instance : CoeFun (DiscreteMeasure' α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toMeasure

noncomputable def map {α β : Type*} (f : α → β) (μ : DiscreteMeasure' α) : DiscreteMeasure' β :=
  @Measure.map _ _ ⊤ ⊤ f μ

noncomputable def pure {α : Type*} (x : α) : DiscreteMeasure' α := @Measure.dirac α ⊤ x

noncomputable def bind (q : DiscreteMeasure' α) (f : α → DiscreteMeasure' β) : DiscreteMeasure' β := @Measure.bind _ _ ⊤ ⊤ q f

lemma map_comp {α β γ : Type*} (f : α → β) (g : β → γ) (μ : DiscreteMeasure' α) :
    map g (map f μ) = map (g ∘ f) μ := by
  apply @Measure.map_map _ _ _ ⊤ ⊤ ⊤ μ g f (by measurability) (by measurability)

lemma bind_pure_comp {α β : Type*} (f : α → β) (μ : DiscreteMeasure' α) :
    bind μ (fun x ↦ pure (f x)) = map f μ := by
  apply @Measure.bind_dirac_eq_map _ _ ⊤ ⊤ μ f (by measurability)

lemma id_map {α : Type*} (μ : DiscreteMeasure' α) : map id μ = μ := Measure.map_id

lemma pure_bind (a : α) (f : α → DiscreteMeasure' β) : bind (pure a) f = f a := by
  apply @Measure.dirac_bind _ _ ⊤ ⊤ f (by measurability)

lemma bind_bind {α β γ : Type*} (μ : DiscreteMeasure' α) (f : α → DiscreteMeasure' β) (g : β → DiscreteMeasure' γ) :
    bind (bind μ f) g = bind μ (fun x ↦ bind (f x) g) := @Measure.bind_bind _ _ ⊤ ⊤ _ ⊤ μ f g (AEMeasurable.of_discrete) (AEMeasurable.of_discrete)

noncomputable instance : Monad DiscreteMeasure' where
  pure := pure
  map := map
  bind := bind

instance : LawfulFunctor DiscreteMeasure' where
  map_const := rfl
  id_map := id_map
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad DiscreteMeasure' := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

noncomputable def fromWeight {α : Type*} (w : α → ℝ≥0∞) : DiscreteMeasure' α :=
  sum fun a ↦ (w a) • (@Measure.dirac α ⊤ a)

lemma apply (w : α → ℝ≥0∞) (s : Set α) :
    (fromWeight w) s = ∑' (i : α), s.indicator w i := by
  simp [toMeasure, fromWeight]

noncomputable def coin (p : ℝ≥0) (h : p ≤ 1) : DiscreteMeasure' Bool := (p : ℝ≥0∞) • dirac true + ((1 - p) : ℝ≥0∞) • dirac false

noncomputable def binomial (p : ℝ≥0) (h : p ≤ 1) : (n : ℕ) → DiscreteMeasure' ℕ
  | 0 => return 0
  | n + 1 => do
    let x ← binomial p h n
    let y ← coin p h
    return x + y.toNat

end DiscreteMeasure'

end DiscreteMeasure'
