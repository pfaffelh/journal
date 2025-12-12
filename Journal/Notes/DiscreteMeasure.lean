/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Lean
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

As one example, we have started to establish some results on `coin p`, which is a Bernoulli distribution.

-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

-- add to indicator
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator (fun _ ↦ 1) a = s.indicator f a := by
  simp [Set.indicator]

lemma ite_ite (d : Prop) [Decidable d] (a b c : α) : (if d then a else if d then b else c) = (if d then a else c) := by
  split_ifs <;> rfl

lemma ite_double (d : Prop) [Decidable d] (a b : α) : (if d then a else if d then b else a) = a := by
  split_ifs <;> rfl

@[simp]
lemma Set.indicator.mul_indicator_eq' (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

@[simp]
lemma Set.indicator.fun_one (s : Set α) : s.indicator (fun _ ↦ 1) = s.indicator 1 := by
  rfl


-- add to pairwise disjoint
lemma pairwise_disjoint_singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  simp_rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
  exact Subtype.coe_ne_coe.mpr hab

lemma pairwise_disjoint_fiber' (s : Set β) : Pairwise (Disjoint on fun (x : β) => (g⁻¹' {x} : Set α)) := by
  exact pairwise_disjoint_fiber g

lemma pairwise_disjoint_fiber_subtype (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)



-- to Function

lemma Function.comp_apply' (f : α → β) (g : β → γ): (g ∘ fun x => f x) = fun x => g (f x) := by
  simp_rw [← comp_apply]



-- to Mathlib.MeasureTheory.Measure.AEMeasurable
lemma Measure.join_sum {α : Type u_1} {mα : MeasurableSpace α} {ι : Type u_7} (m : ι → Measure (Measure α)) :
(sum fun (i : ι) ↦ m i).join = sum fun (i : ι) ↦ (m i).join := by
  simp_rw [Measure.join, lintegral_sum_measure]
  ext s hs
  rw [ofMeasurable_apply, Measure.sum_apply]
  apply tsum_congr (fun i ↦ ?_)
  rw [ofMeasurable_apply]
  repeat assumption

lemma Measure.bind_sum {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {ι : Type u_7} (m : ι → Measure α) (f : α → Measure β) (h : AEMeasurable f (sum fun i => m i)) :
  (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [Measure.bind]
  rw [Measure.map_sum, Measure.join_sum]
  exact h

lemma Measure.bind_smul {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α) (f : α → Measure β) :
  (c • m).bind f = c • (m.bind f) := by
  simp_rw [Measure.bind, Measure.map_smul, Measure.join_smul]



section discreteMeasures

-- let us start with discrete measures now!


/- In this file, all measures are defined on `⊤`, i.e., the power set σ-algebra. Later, we might want to use them on small σ-algebras. For this, then take `toMeasure.trim`. -/
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

@[simp]
lemma apply (μ : DiscreteMeasure α) (s : Set α) :
    μ s = ∑' (i : α), s.indicator μ.weight i := by
  simp [toMeasure]

lemma apply' (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (i : α), μ.weight i * s.indicator 1 i := by
  simp

lemma apply'' (μ : DiscreteMeasure α) (s : Set α) : μ s =
    ∑' (a : s), (μ.weight a) := by
  simp [tsum_subtype]

@[simp]
lemma apply_singleton (μ : DiscreteMeasure α) (a : α) :
    ∑' (i : α), ({a} : Set α).indicator μ.weight i = μ.weight a := by
  rw [← tsum_subtype, tsum_singleton]

lemma apply_singleton' (μ : DiscreteMeasure α) (a : α) : μ {a} =
    μ.weight a := by
  simp

lemma singleton_eq_weight (μ : DiscreteMeasure α) : (fun (a : α) ↦ μ {a}) = μ.weight := by
  simp

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
  exact m_iUnion μ _ (pairwise_disjoint_singleton_subtype s)

lemma ext_weight {μ₁ μ₂ : DiscreteMeasure α}
  (h : μ₁.weight = μ₂.weight) : μ₁ = μ₂ :=
by
  cases μ₁
  simp only at h
  rw [h]

@[ext]
lemma ext {μ₁ μ₂ : DiscreteMeasure α}
    (h : ∀ a, μ₁.weight a = μ₂.weight a) : μ₁ = μ₂ :=by
  exact ext_weight <| funext h

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteMeasure α} (h : μ₁.toMeasure = μ₂.toMeasure) : μ₁ = μ₂ :=
by
  ext x
  rw [← singleton_eq_weight, ← singleton_eq_weight, h]

lemma apply_univ (μ : DiscreteMeasure α) : μ Set.univ = ∑' (a : α), μ.weight a := by
  simp


lemma apply_univ' (μ : DiscreteMeasure α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d): μ Set.univ = ∑' (d : δ), μ (s d) := by
  rw [hs₁]
  exact m_iUnion μ s hs₀

lemma isProbabilityMeasure_iff (μ : DiscreteMeasure α) : IsProbabilityMeasure μ.toMeasure ↔ HasSum μ.weight 1 := by
  rw [MeasureTheory.isProbabilityMeasure_iff, DiscreteMeasure.apply_univ, Summable.hasSum_iff ENNReal.summable]

section map

noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : (DiscreteMeasure β) := ⟨fun b ↦ μ (g⁻¹' {b})⟩

noncomputable instance : Functor DiscreteMeasure where
  map := map

@[simp]
lemma map_weight (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x = μ (g⁻¹' {x}) := by
  rfl

lemma map_weight' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x =  ∑' (i : α), μ.weight i * ({x} : Set β).indicator 1 (g i) := by
  rw [map_weight, apply']
  apply tsum_congr (fun b ↦ by congr)

lemma map_eq_toMeasure (μ : DiscreteMeasure α) (g : α → β) : μ.map g = Measure.map g μ.toMeasure := by
  ext s
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [apply'']
  simp_rw [map_weight]
  have h : g⁻¹' s = ⋃ (i : s), g⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  exact (m_iUnion _ _ (pairwise_disjoint_fiber_subtype s)).symm

lemma map_coe  (μ : DiscreteMeasure α) (f : α → β) : ((μ.map f : DiscreteMeasure β) : @Measure β ⊤) = Measure.map f (μ : @Measure α ⊤) := by
  exact map_eq_toMeasure μ f

lemma map_toMeasure' (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = sum (m0 := ⊤) (fun a ↦ μ.weight a • (@dirac β ⊤ (g a))) := by
  rw [map_eq_toMeasure]
  ext s
  rw [toMeasure, Measure.map_sum]
  have gh : Measurable g := by measurability
  simp_rw [Measure.map_smul, @Measure.map_dirac α β ⊤ ⊤ g (by measurability)]
  apply @AEMeasurable.of_discrete α β ⊤ ⊤

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext s
  rw [← apply_singleton', ← apply_singleton', map_coe, map_coe, map_coe]
  rw [Measure.map_map (by measurability) (by measurability)]

lemma map_apply'' (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), (g⁻¹' s).indicator μ.weight a := by
  rw [map_toMeasure']
  simp only [MeasurableSpace.measurableSet_top, sum_apply, smul_apply, dirac_apply', smul_eq_mul]
  apply tsum_congr (fun b ↦ ?_)
  exact Set.indicator.mul_indicator_eq' μ.weight (fun b => s (g b)) b

lemma map_apply (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = μ (g⁻¹' s) := by
  rw [map_coe]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply' (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), μ.weight a * s.indicator 1 (g a) := by
  rw [map_toMeasure']
  simp

lemma map_apply₁ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (b : s), μ (g⁻¹' {b.val}) := by
  rw [apply'']
  rfl

lemma map_apply''' (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : g⁻¹' s), (μ.weight a.val) := by
  rw [map_apply, apply'']

theorem id_map (μ : DiscreteMeasure α) :
μ.map id = μ := by
  apply toMeasure_ext'
  rw [map_coe]
  exact Measure.map_id

end map


section lintegral

noncomputable def lintegral (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : ℝ≥0∞ := ∑' (a : α), μ.weight a * (g a)

lemma lintegral_eq_toMeasure (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : μ.lintegral g = ∫⁻ (a : α), g a ∂ μ.toMeasure := by
  rw [toMeasure, lintegral]
  simp

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
  rw [← lintegral_eq_toMeasure, apply'']
  simp_rw [join_weight, lintegral]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left, apply_singleton']
  simp_rw [apply_singleton', ← apply'']

lemma join_toMeasure' (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m.weight μ • μ.toMeasure) := by
  ext s
  rw [join_coe, toMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply, Measure.sum_apply]
  · apply tsum_congr (fun μ ↦ ?_)
    rw [Measure.smul_apply]
    rw [Measure.map_smul]
    rw [Measure.join_smul]
    rw [Measure.smul_apply]
    rw [smul_eq_mul, smul_eq_mul]
    rw [Measure.map_dirac]
    rw [Measure.join_dirac]
    measurability
  · measurability
  · measurability

lemma join_apply (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) : m.join s = ∑' (μ : DiscreteMeasure α), m {μ} * μ s := by
  simp only [join_toMeasure']
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  simp

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
  rw [bind, Measure.bind]
  rw [join_coe]
  rw [← Measure.map_map (hg := by measurability) (hf := by measurability)]
  rw [map_coe]

lemma bind_coe (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  ext s
  rw [bind_apply_eq_toMeasure]

lemma bind_toMeasure' (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : μ.bind g  = sum (fun a ↦ μ.weight a • (g a).toMeasure) := by
  ext s
  rw [bind_apply_eq_toMeasure, toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete)]
  rw [Measure.sum_apply (hs := by measurability)]
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun b ↦ ?_)
  rw [Measure.bind_smul]
  rw [Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
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
  congr 1
  rw [apply_singleton']
  rw [apply_singleton']
  rw [map_weight]

theorem bind_const (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) : (μ₁.bind fun (_ : α) => μ₂) =  (μ₁ Set.univ) • μ₂.toMeasure := by
  rw [bind_coe]
  rw [Function.comp_apply']
  rw [Measure.bind_const]

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

noncomputable def pure (a : α) : DiscreteMeasure α :=
  ⟨({a} : Set α).indicator 1⟩

@[simp]
lemma pure_weight (a : α) : (pure a).weight = ({a} : Set α).indicator 1 := rfl

@[simp]
lemma pure_apply (a : α) (s : Set α) : (pure a) s = s.indicator 1 a := by
  rw [apply, pure_weight, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]
    simp only [h, Set.indicator_of_mem, Pi.one_apply]
    rw [← apply, apply'', tsum_singleton]
    rfl
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_eq_dirac (a : α) : (pure a).toMeasure = Measure.dirac a := by
  ext s
  rw [pure_apply, Measure.dirac_apply]

lemma map_toDirac : (toMeasure ∘ pure) = @Measure.dirac α ⊤ := by
  funext a
  rw [← pure_eq_dirac]
  simp only [comp_apply]

lemma pure_coe (a : α) : (pure a) = Measure.dirac a := by
  ext s
  rw [pure_apply, Measure.dirac_apply' a (by measurability)]

lemma pure_hasSum (a : α) : HasSum (pure a).weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, ← apply_univ,  pure_coe, dirac_apply_of_mem (Set.mem_univ a)]

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  ext x
  have h : a ∈ (f ⁻¹' {x}) ↔ (x ∈ ({f a} : Set β))  := by exact comm.symm
  rw [map_weight, pure_weight, pure_apply]
  exact Set.indicator_eq_indicator (id h) rfl

theorem pure_bind (a : α) (f : α → DiscreteMeasure β) :
(pure a).bind f = f a := by
  apply toMeasure_ext'
  rw [bind_coe]
  rw [pure_eq_dirac]
  rw [dirac_bind (hf :=  by measurability)]
  rfl

theorem bind_pure (μ : DiscreteMeasure α) :
μ.bind pure = μ := by
  apply toMeasure_ext'
  rw [bind_coe]
  rw [Measure.bind, map_toDirac, ← Measure.bind]
  rw [Measure.bind_dirac]

lemma bind_pure_comp (f : α → β) (μ : DiscreteMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply toMeasure_ext'
  rw [bind_coe, map_coe]
  rw [Function.comp_apply']
  simp_rw [pure_eq_dirac]
  rw [Measure.bind_dirac_eq_map (hf := by measurability)]

end pure

section seq

/-- The monadic sequencing operation for `DiscreteMeasure`. -/
noncomputable def seq (q : DiscreteMeasure (α → β)) (p :  Unit → DiscreteMeasure α) : DiscreteMeasure β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)

lemma bind_map_eq_seq (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) : q.bind (fun m => (p ()).map m) = seq q p := by
  simp_rw [← bind_pure_comp]
  rfl

noncomputable instance : Seq DiscreteMeasure where
  seq := seq

variable (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) (b : β)

open scoped Classical in
@[simp]
theorem seq_weight : (seq q p).weight b = ∑' (f : α → β) (a : α), q.weight f * if b = f a then (p ()).weight a else 0 := by
  rw [seq, bind_weight]
  simp_rw [bind_weight, pure_weight]
  simp_rw [Set.indicator, Set.mem_singleton_iff]
  apply tsum_congr (fun f ↦ ?_)
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr (fun g ↦ ?_)
  split_ifs <;> simp

open scoped Classical in
theorem seq_weight' : (seq q p).weight b = ∑' (f : α → β) (a : f⁻¹' {b}), q.weight f * (p ()).weight a := by
  rw [seq, bind_weight]
  simp_rw [bind_weight, pure_weight]
  simp_rw [ENNReal.tsum_mul_left]
  apply tsum_congr (fun f ↦ ?_)
  congr 1
  rw [tsum_subtype]
  apply tsum_congr (fun g ↦ ?_)
  nth_rw 2 [← Set.indicator.mul_indicator_eq]
  congr
  rw [Set.indicator]
  rw [Set.indicator]
  split_ifs with i j h <;> simp
  exact Ne.elim (fun a => j (id (Eq.symm a))) i
  exact Ne.elim (fun a => i (id (Eq.symm a))) h

open scoped Classical in
@[simp]
theorem seq_weight'' : (seq q p).weight b = ∑' (f : α → β), q.weight f * ∑' (a : α), (f⁻¹' {b}).indicator (p ()).weight a := by
  rw [seq, bind_weight]
  simp_rw [bind_weight, pure_weight]
  simp_rw [Set.indicator, Set.mem_singleton_iff]
  apply tsum_congr (fun f ↦ ?_)
  congr
  ext a
  simp only [Pi.one_apply, mul_ite, mul_one, mul_zero, Set.mem_preimage, Set.mem_singleton_iff]
  split_ifs with h' h''
  simp
  exact False.elim (h'' (id (Eq.symm h')))
  (expose_names; exact False.elim (h' (id (Eq.symm h))))
  rfl

lemma l1 (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), ({x} : Set α).indicator f a) = (f x) := by
  rw [← tsum_subtype, tsum_singleton]

lemma l1_left (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), (f a * ({x} : Set α).indicator (1 : α → ℝ≥0∞) a)) = (f x) := by
  simp_rw [Set.indicator.mul_indicator_eq']
  exact l1 f x

lemma l1_right (f : α → ℝ≥0∞) (x : α) : (∑' (a : α), (({x} : Set α).indicator (1 : α → ℝ≥0∞) a) * (f a)) = (f x) := by
  simp_rw [mul_comm, Set.indicator.mul_indicator_eq']
  exact l1 f x

lemma seq_pure {α β : Type u} (g : DiscreteMeasure (α → β)) (x : α) : seq g (fun _ ↦ pure x) = map (fun h => h x) g := by
  ext b
  rw [map_weight, apply, seq_weight'']
  simp_rw [pure_weight]
  apply tsum_congr (fun c ↦ ?_)
  simp_rw [Set.indicator_indicator, Set.inter_comm, ← Set.indicator_indicator, ← tsum_subtype, tsum_singleton]
  nth_rw 2 [← Set.indicator.mul_indicator_eq']
  congr 1

lemma pure_seq {α β : Type u} (g : (α → β)) (x : Unit → DiscreteMeasure α) : seq (pure g) x = (x ()).map g := by
  ext b
  rw [seq_weight'', pure_weight, map_weight, apply]
  simp_rw [mul_comm, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun c ↦ ?_)
  let f := fun a ↦ (a ⁻¹' {b}).indicator (x ()).weight c
  change ∑' (a : α → β), f a * ({g} : Set (α → β)).indicator 1 a= _
  simp_rw [Set.indicator.mul_indicator_eq']
  rw [← tsum_subtype, tsum_singleton]

lemma seq_assoc (p : DiscreteMeasure α) (q : DiscreteMeasure (α → β)) (r : DiscreteMeasure (β → γ)) : (r.seq fun _ => q.seq fun _ => p) = ((map comp r).seq fun _ => q).seq fun _ => p := by
  repeat rw [← bind_map_eq_seq]
  repeat rw [← bind_pure_comp]
  repeat rw [bind_bind]
  simp_rw [pure_bind]
  congr
  funext m
  rw [← bind_pure_comp, bind_bind, ← bind_pure_comp, bind_bind]
  simp_rw [pure_bind, bind_pure_comp, map_map]









noncomputable def binom₀ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF ℕ := do
  let choices ← sequence <| List.replicate n (PMF.bernoulli p h)
  return choices.count true

noncomputable def binom₁ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF ℕ := (sequence <| List.replicate n (PMF.bernoulli p h)).map (List.count true)

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

lemma map_seq {α β γ : Type u}(f : β → γ) (u : DiscreteMeasure (α → β)) (v : DiscreteMeasure α) : (u.seq (fun _ ↦ v)).map f = (u.map (fun (g : α → β) => f ∘ g)).seq (fun _ ↦ v) := by
  rw [map_eq_map, seq_eq_seq, map_eq_map, seq_eq_seq]
  simp [monad_norm]
  rfl

noncomputable def prod {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) : DiscreteMeasure (α × β) := (μ.bind fun X => (q X).bind fun Y => Pure.pure (X, Y))

lemma prod_eq {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) : prod μ q =
  do
    let X ← μ
    let Y ← q X
    return (X, Y)
 := by
  rw [prod]
  rw [bind_eq_bind]
  simp_rw [bind_eq_bind]

lemma l2  (i b : β) : ({i} : Set β).indicator (1 : β → ℝ≥0∞) b = ({b} : Set β).indicator (1 : β → ℝ≥0∞) i := by
  refine Set.indicator_eq_indicator ?_ rfl
  simp only [Set.mem_singleton_iff]
  exact eq_comm

lemma prod_weight {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) (a : α) (b : β): (prod μ q).weight (a, b) = μ.weight a * (q a).weight b := by
  rw [prod]
  simp_rw [← pure_eq_pure]
  rw [bind_weight]
  simp_rw [bind_weight, pure_weight]
  have h (a' : α) (b' : β) : ({(a', b')} : Set (α × β)).indicator (1 : α × β → ℝ≥0∞) (a, b) = (({a'} : Set α).indicator (1 : α → ℝ≥0∞) a) * (({b'} : Set β).indicator (1 : β → ℝ≥0∞) b) := by
    simp only [Set.indicator]
    aesop
  conv => left; left; intro a'; right; left; intro b'; right; rw [h]
  simp_rw [← mul_assoc]
  conv => left; left; intro a1; right; left; intro b1; rw [mul_assoc, mul_comm, mul_assoc]
  simp_rw [ENNReal.tsum_mul_left]
  conv => left; left; intro a'; right; right; conv => left; intro i; rw [l2]; ; rw [l1_right]
  conv => left; left; intro a'; rw [mul_comm, mul_assoc]
  simp_rw [l2, l1_right]
  rw [mul_comm]

noncomputable def pi {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : DiscreteMeasure (α × β) :=
prod μ (fun _ ↦ ν)

lemma pi_eq {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : pi μ ν = (μ.map Prod.mk).seq (fun _ ↦ ν) := by
  rw [seq_eq_seq, map_eq_map]
  simp [monad_norm]
  rfl

lemma pi_eq' {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : pi μ ν = ((pure Prod.mk).seq (fun _ ↦ μ)).seq fun _ ↦ ν := by
  rw [pi_eq, pure_eq_pure, seq_eq_seq, seq_eq_seq, seq_eq_seq, map_eq_map]
  simp [monad_norm]

lemma pi_weight {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) (a : α) (b : β): (pi μ ν).weight (a,b) = (μ.weight a) * (ν.weight b) := by
  rw [pi, prod_weight]






noncomputable def prodList (l : List (DiscreteMeasure α)) :
    DiscreteMeasure (List α) :=
l.foldr
  (fun μ rest => μ.bind (fun a => rest.map (fun as => a :: as)))
  (pure [])



end DiscreteMeasure





section DiscreteProbabilityMeasure
/-- A `DiscreteProbabilityMeasure` is a `DiscreteMeasure` with the property `IsProbabilityMeasure`. -/
def DiscreteProbabilityMeasure (α : Type*) : Type _ :=
  { μ : DiscreteMeasure α // HasSum μ.weight 1 }


instance (μ : DiscreteProbabilityMeasure α) : IsProbabilityMeasure μ.val.toMeasure := by
  rw [DiscreteMeasure.isProbabilityMeasure_iff]
  exact μ.prop

/-- A discrete probability measure can be interpreted as a discrete measure. -/
noncomputable instance : Coe (DiscreteProbabilityMeasure α) (DiscreteMeasure α) where
  coe μ := μ.val

noncomputable instance : CoeFun (DiscreteProbabilityMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.val.toMeasure





namespace DiscreteProbabilityMeasure

/-- Coercion from `MeasureTheory.DiscreteProbabilityMeasure α` to `MeasureTheory.DiscreteMeasure α`. -/
@[coe]
def toDiscreteMeasure : DiscreteProbabilityMeasure α → DiscreteMeasure α := Subtype.val

noncomputable def toProbabilityMeasure (μ : DiscreteProbabilityMeasure α) : @ProbabilityMeasure α ⊤ := ⟨μ.val, by infer_instance⟩

noncomputable instance :
  CoeFun (DiscreteProbabilityMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.val.toMeasure

def ofDiscreteMeasure (μ : DiscreteMeasure α) (hμ : HasSum μ.weight 1) : DiscreteProbabilityMeasure α := ⟨μ, hμ⟩

def ofDiscreteMeasure' (μ : DiscreteMeasure α) (hμ : IsProbabilityMeasure μ.toMeasure) : DiscreteProbabilityMeasure α :=
  ⟨μ, (DiscreteMeasure.isProbabilityMeasure_iff μ).mp hμ⟩

@[simp]
lemma apply_univ_eq_one (P : DiscreteProbabilityMeasure α) : P Set.univ = 1 := by
  rw [DiscreteMeasure.apply_univ]
  have h : HasSum P.val.weight 1 := P.prop
  exact HasSum.tsum_eq h

lemma apply_le_one (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≤ 1 := by
  exact prob_le_one

lemma apply_ne_top (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≠ ⊤ := by
  have h : IsProbabilityMeasure P.val.toMeasure := by exact
    instIsProbabilityMeasureToMeasureValDiscreteMeasureHasSumENNRealWeightOfNatUnconditional P
  rw [isProbabilityMeasure_iff] at h
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact apply_le_one P s

@[simp]
lemma toProbabilityMeasure_apply (P : DiscreteProbabilityMeasure α) (s : Set α) : (toProbabilityMeasure P).toMeasure s = ∑' (i : α), s.indicator P.val.weight i := by
  rw [← DiscreteMeasure.apply]
  rfl

lemma singleton_eq_weight (μ : DiscreteProbabilityMeasure α) : (fun (a : α) ↦ μ {a}) = μ.val.weight := by
  exact μ.val.singleton_eq_weight

@[ext]
lemma ext {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : ∀ (a : α), μ₁.val.weight a = μ₂.val.weight a) : μ₁ = μ₂ :=
Subtype.ext (DiscreteMeasure.ext h)

lemma ext_val' {μ₁ μ₂ : DiscreteProbabilityMeasure α} :
  (toDiscreteMeasure μ₁ = toDiscreteMeasure μ₂) ↔ μ₁ = μ₂ :=
by
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [h]⟩

lemma ext_weight {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : μ₁.val.weight = μ₂.val.weight) : μ₁ = μ₂ :=
by
  ext x
  rw [h]

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteProbabilityMeasure α} (h : μ₁.val.toMeasure = μ₂.val.toMeasure) : μ₁ = μ₂ :=
by
  apply Subtype.ext
  exact DiscreteMeasure.toMeasure_ext' h

-- map
lemma map_isProbabilityMeasure (g : α → β) (μ : DiscreteProbabilityMeasure α) : HasSum (μ.val.map g).weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp_rw [μ.val.map_weight]
  nth_rw 2 [← apply_univ_eq_one μ]
  rw [μ.val.apply_univ' _ (pairwise_disjoint_fiber g)]
  ext x
  simp

noncomputable def map (g : α → β) (μ : DiscreteProbabilityMeasure α) : (DiscreteProbabilityMeasure β) := ⟨⟨fun b ↦ μ (g⁻¹' {b})⟩, map_isProbabilityMeasure g μ⟩

noncomputable instance : Functor DiscreteProbabilityMeasure where
  map := map

example {α β : Type u} (f : α → β) (μ : DiscreteProbabilityMeasure α): f <$> μ = (map f μ) := by rfl

lemma map_coe (g : α → β) (μ : DiscreteProbabilityMeasure α) : (μ.map g) = μ.val.map g := by
  rfl

example {α β : Type u} (f : α → β) (μ : DiscreteProbabilityMeasure α) : f <$> μ.val = (f <$> μ).val := by rfl

lemma map_map (μ : DiscreteProbabilityMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  apply Subtype.ext
  simp [map_coe]
  rw [DiscreteMeasure.map_map]

theorem id_map (μ : DiscreteProbabilityMeasure α) :
μ.map id = μ := by

  apply Subtype.ext
  simp [map_coe]

-- join
noncomputable def join (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : (DiscreteProbabilityMeasure α) := by
  let m' : DiscreteMeasure (DiscreteMeasure α) := (DiscreteMeasure.map Subtype.val m.val)
  have hweight (μ : DiscreteMeasure α) (hμ : ¬ (HasSum μ.weight 1)) : m'.weight μ = 0 := by
    simp only [DiscreteMeasure.map_weight, DiscreteMeasure.apply, ENNReal.tsum_eq_zero, Set.indicator_apply_eq_zero,
      Set.mem_preimage, Set.mem_singleton_iff, Subtype.forall, m']
    exact fun  a ha haμ ↦ False.elim <| hμ (haμ.symm ▸ ha)
  have hm₀ (μ : DiscreteProbabilityMeasure α) :  m.val.weight μ = m'.weight μ.val := by
    simp only  [m', DiscreteMeasure.map_weight, DiscreteMeasure.apply]
    have h₄ : (Subtype.val ⁻¹' {toDiscreteMeasure μ}) = {μ} := by
      simp_rw [Set.preimage, Set.mem_singleton_iff]
      change {x | x.toDiscreteMeasure = μ.toDiscreteMeasure} = {μ}
      simp_rw [ext_val', Set.setOf_eq_eq_singleton]
    rw [← DiscreteMeasure.apply_singleton', DiscreteMeasure.apply]
    apply tsum_congr (fun b ↦ ?_)
    rw [← h₄]
    rfl
  have hm₀' : m.val.weight = m'.weight ∘ toDiscreteMeasure := by
    ext μ; simp only [hm₀, comp_apply]; rfl
  have hm₀'' : ∑' (μ : DiscreteProbabilityMeasure α),  m.val.weight μ = ∑' (μ : DiscreteProbabilityMeasure α), m'.weight μ := by
    congr
  have hm : HasSum m.val.weight 1 := m.prop
  rw [hm₀', Summable.hasSum_iff ENNReal.summable] at hm
  change ∑' (b : { μ : DiscreteMeasure α | HasSum μ.weight 1}), (m'.weight) b = 1 at hm
  rw [tsum_subtype] at hm
  have hm' : HasSum m'.weight 1 := by
    rw [Summable.hasSum_iff ENNReal.summable, ← hm]
    apply tsum_congr (fun b ↦ ?_)
    by_cases hb : HasSum b.weight 1
    · simp only [Set.mem_setOf_eq, hb, Set.indicator_of_mem]
    · simp only [Set.mem_setOf_eq, hb, not_false_eq_true, Set.indicator_of_notMem]
      exact hweight b hb
  have hm'' : ∀ μ, m'.weight μ ≠ 0 → HasSum μ.weight 1 := by
    intro μ
    rw [← not_imp_not]
    simp only [ne_eq, Decidable.not_not]
    exact fun a => hweight μ a
  exact ⟨DiscreteMeasure.join m', DiscreteMeasure.join_hasSum m' hm' (fun μ hμ ↦ hm'' μ hμ)⟩

lemma join_val (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : m.join.val = DiscreteMeasure.join (DiscreteMeasure.map Subtype.val m.val) := rfl

lemma join_coe (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : m.join = (DiscreteMeasure.map Subtype.val m.val).join := by
  rfl




-- bind
noncomputable def bind (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : (DiscreteProbabilityMeasure β) := (μ.map g).join

lemma bind_coe (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : μ.bind g = μ.val.bind (Subtype.val ∘ g) := by
  rw [bind, DiscreteMeasure.bind, join_coe]
  congr
  rw [← DiscreteMeasure.map_map]
  congr

lemma join_map_map (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) (g : α → β) : map g m.join = (map (map g) m).join := by
  ext x
  rw [map_coe, join_coe]
  rw [join_coe, map_coe]
  rw [← DiscreteMeasure.join_map_map]
  rw [DiscreteMeasure.map_map]
  rw [DiscreteMeasure.map_map]
  congr

theorem bind_const (μ₁ : DiscreteProbabilityMeasure α) (μ₂ : DiscreteProbabilityMeasure β) : (μ₁.bind fun (_ : α) => μ₂) = μ₂ := by
  apply Subtype.ext
  rw [bind_coe]
  rw [Function.comp_apply']
  apply DiscreteMeasure.toMeasure_ext'
  rw [DiscreteMeasure.bind_const]
  rw [measure_univ, one_smul]

theorem bind_bind (μ₁ : DiscreteProbabilityMeasure α) (f : α → DiscreteProbabilityMeasure β) (g : β → DiscreteProbabilityMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  apply Subtype.ext
  rw [bind_coe]
  rw [bind_coe]
  rw [bind_coe]
  rw [DiscreteMeasure.bind_bind]
  congr
  ext s
  rw [comp_apply, comp_apply, bind_coe]

theorem bind_comm (μ₁ : DiscreteProbabilityMeasure α) (μ₂ : DiscreteProbabilityMeasure β) (f : α → β → DiscreteProbabilityMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  apply Subtype.ext
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

lemma pure_coe' : DiscreteMeasure.pure (α := α)= (Subtype.val ∘ DiscreteProbabilityMeasure.pure) := by
  rfl

lemma map_pure (a : α) (f : α → β) : (DiscreteProbabilityMeasure.pure a).map f = DiscreteProbabilityMeasure.pure (f a) := by
  apply Subtype.ext
  rw [map_coe, pure_coe, DiscreteMeasure.map_pure]
  rfl

theorem pure_bind (a : α) (f : α → DiscreteProbabilityMeasure β) :
(pure a).bind f = f a := by
  apply Subtype.ext
  rw [bind_coe, pure_coe]
  rw [DiscreteMeasure.pure_bind]
  rfl

theorem bind_pure (μ : DiscreteProbabilityMeasure α) :
μ.bind pure = μ := by
  apply Subtype.ext
  rw [bind_coe, ← pure_coe']
  rw [DiscreteMeasure.bind_pure]

lemma bind_pure_comp (f : α → β) (μ : DiscreteProbabilityMeasure α) : μ.bind (fun a ↦ pure (f a)) =  μ.map f := by
  apply Subtype.ext
  rw [bind_coe, comp_apply', map_coe]
  simp_rw [pure_coe]
  rw [DiscreteMeasure.bind_pure_comp]


end pure

section monad

noncomputable instance : Monad DiscreteProbabilityMeasure where
  pure a := pure a
  bind pa pb := pa.bind pb

instance : LawfulFunctor DiscreteProbabilityMeasure where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulMonad DiscreteProbabilityMeasure := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

noncomputable instance : ULiftable DiscreteProbabilityMeasure.{u} DiscreteProbabilityMeasure.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by
        simp only [map_map, Equiv.symm_comp_self, id_map]
      right_inv := fun a => by
        simp only [map_map, Equiv.self_comp_symm, id_map]
      }

end monad

end DiscreteProbabilityMeasure

end DiscreteProbabilityMeasure



namespace DiscreteProbabilityMeasure

section coin

open Bool ENNReal DiscreteMeasure

noncomputable def coin (p : ℝ≥0) (h : p ≤ 1) : DiscreteProbabilityMeasure Bool :=
  ⟨⟨fun (b : Bool) ↦ if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞)⟩, by
    rw [Summable.hasSum_iff ENNReal.summable]
    rw [tsum_bool]
    simp only [false_eq_true, ↓reduceIte]
    norm_cast
    exact tsub_add_cancel_of_le h
  ⟩


lemma lintegral_coe (μ : DiscreteProbabilityMeasure α) (g : α → ℝ≥0): ∫⁻ (a : α), g a ∂ μ.val.toMeasure = ∑' (a : α),  (μ.val.weight a) * g a := by
  rw [← DiscreteMeasure.lintegral_eq_toMeasure]
  rw [DiscreteMeasure.lintegral]


lemma lintegral_coin (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ≥0): ∫⁻ (a : Bool), (g a) ∂ (coin p h).val.toMeasure = (1 - p) * (g false) + p * (g true) := by
  rw [← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral]
  simp_rw [coin]
  rw [tsum_bool]
  split_ifs <;> norm_cast


lemma lintegral_map_coin (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ≥0): ∫⁻ (a : ℝ≥0), (id a) ∂ (map g (coin p h)).val.toMeasure = ∫⁻ (a : Bool), (g a) ∂ (coin p h).val.toMeasure := by
  rw [map_coe, DiscreteMeasure.map_coe, @MeasureTheory.lintegral_map _ _ ⊤ ⊤ _ _ _ (by measurability) (by exact fun ⦃t⦄ a => a), ← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral, ← DiscreteMeasure.lintegral_eq_toMeasure, DiscreteMeasure.lintegral]
  rfl



lemma lintegral_coin' (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ): ∫ (a : Bool), (g a) ∂ (coin p h).val.toMeasure = p.toReal * (g true) + (1 - p).toReal * (g false) := by
  sorry


-- We have do notation (as for PMF)!
example (p : ℝ≥0) (h : p ≤ 1) : coin p h = do
  let X ← coin p h
  return X
  := by
  simp

lemma coin_weight (p : ℝ≥0) (h : p ≤ 1) (b : Bool) : (coin p h).1.weight b = if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞) := by
  rfl

lemma Bool.mem_not (b : Bool) : not ⁻¹' {b} = {!b} := by
    ext y; cases' y <;> simp

lemma coin_not (p : ℝ≥0) (h : p ≤ 1) : (coin p h).map not  = coin (1-p) (tsub_le_self) := by
  ext x
  rw [DiscreteProbabilityMeasure.map_coe]
  cases x <;> rw [map_weight, Bool.mem_not, apply_singleton', coin_weight, coin_weight] <;> norm_cast
  rw[tsub_tsub_cancel_of_le h]
  simp

noncomputable def binom₂ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure ℕ := ((sequence <| List.replicate n (coin p h)).map (List.map Bool.toNat)).map List.sum

-- a list of independent experiments
--noncomputable def pi (μs : List (DiscreteMeasure α)) :
--  DiscreteMeasure (List α) := sequence μs

noncomputable def bernoulliSequence (n : ℕ) (μ : DiscreteMeasure α) :  DiscreteMeasure (List α) := sequence (List.replicate n μ)

lemma sequence_nil : sequence ([] : List (DiscreteMeasure α)) = (DiscreteMeasure.pure [] : DiscreteMeasure (List α)) := by
  simp [sequence]

open Classical
lemma cons_pure_weight (a a' : α) (l l' : List α) : ((DiscreteMeasure.pure ∘ List.cons a') l').weight (a :: l) = if a = a' ∧ l = l' then 1 else 0 := by
  rw [comp_apply, pure_weight, Set.indicator]
  split_ifs with h₁ h₂ h₂ <;> simp only [Set.mem_singleton_iff, List.cons.injEq] at h₁
  · simp only [Pi.one_apply]
  · simp only [Pi.one_apply, one_ne_zero, h₂ h₁]
  · apply False.elim (h₁ h₂)
  · rfl

lemma cons_map_weight (μs : DiscreteMeasure (List α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (List.cons <$> ν <*> μs).weight (a :: l) = ν.weight a * (μs.weight l) := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_weight]
  simp_rw [← bind_eq_bind, bind_weight]
  simp_rw [← pure_eq_pure, cons_pure_weight]
  have h (a_1 : α) (a_2 : List α) : (if a = a_1 ∧ l = a_2 then 1 else 0) = ({a} : Set α).indicator (1 : α → ℝ≥0∞) a_1 * ({l} : Set (List α)).indicator (1 : List α → ℝ≥0∞) a_2 := by
    simp only [Set.indicator]
    aesop
  simp_rw [h]
  conv => left; left; intro a1; right; left; intro a2; rw [← mul_assoc]; rw [mul_comm (μs.weight a2) _, mul_assoc]; rw [Set.indicator.mul_indicator_eq']
  simp_rw [ENNReal.tsum_mul_left]
  simp_rw [← tsum_subtype, tsum_singleton, ← mul_assoc, Set.indicator.mul_indicator_eq']
  simp_rw [ENNReal.tsum_mul_right]
  rw [← tsum_subtype, tsum_singleton]

lemma sequence_cons (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) : sequence (ν::μs) = List.cons <$> ν <*> (sequence μs) := by
  rfl

lemma sequence_weight_cons (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (sequence (ν::μs)).weight (a::l) = (ν.weight a)*((sequence μs).weight l) := by
  exact cons_map_weight (sequence μs) ν l a

lemma sequence_weight (μs : List (DiscreteMeasure α)) (l : List α) (hl : l.length = μs.length) :
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


lemma prod_apply_replicate (l : List α) (f : α → β) :
  l.map f = (List.replicate l.length f).zipWith (fun a b ↦ a b) l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.length, ih]; rfl

lemma bernoulliSequence_weight (n : ℕ) (μ : DiscreteMeasure α) (l : List α) (hl : l.length = n) :
    (bernoulliSequence n μ).weight l = List.prod (l.map μ.weight) := by
  rw [bernoulliSequence, ← hl, sequence_weight]
  · rw [List.map_replicate]
    rw [prod_apply_replicate]
  · simp only [List.length_replicate]

lemma cons_eq_append_singleton (a : α) (l : List α) : (a::l) = [a] ++ l := by
  simp only [List.cons_append, List.nil_append]

example (a a' : α) (l' : List α) : (a::l) = [a] ++ l := by simp only [List.cons_append,
  List.nil_append]

example (a a' : α) (l' : List α) : List.count a (a'::l') = (List.count a [a']) + (List.count a l') := by
  rw [cons_eq_append_singleton]
  simp only [List.count, List.countP_append]

lemma count_cons (a a' : α) (l' : List α) : List.count a (a'::l') = (if a' = a then 1 else 0) + (List.count a l') := by
  rw [cons_eq_append_singleton]
  simp only [List.count, List.countP_append, List.countP_singleton, beq_iff_eq]


#check ContinuousMul

lemma multipliable_one : Multipliable (fun _ ↦ (1 : ℝ≥0∞) : α → ℝ≥0∞) := ⟨1, hasProd_one⟩

lemma HasProd.eventually_one (g : α → ℝ≥0∞) (hg : (g.mulSupport).Finite) : Multipliable g := by
  use ∏ (a : hg.toFinset), g a.val
  rw [← hasProd_subtype_iff_of_mulSupport_subset hg.coe_toFinset.symm.le]
  exact hasProd_fintype (g ∘ Subtype.val) (SummationFilter.unconditional ↑↑hg.toFinset)

example (l l': List α) (f : α → ℝ≥0∞) : (List.map f (l++l')).sum = (List.map f l).sum +  (List.map f l').sum := by
  simp only [List.map_append, List.sum_append]

lemma List.nmem_toFinset (b : α) (l : List α) : b ∉ l.toFinset ↔ b ∉ l := by
  rw [List.mem_toFinset]



lemma tprod_eq_prod_of_pow_count (l : List α) (f : α → ℝ≥0∞) : (∏' a, (f a)^(l.count a)) = (∏ a ∈ l.toFinset, f a ^ (l.count a)) := by
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

example (l : List α) (f : α → ℝ≥0∞) : (List.map f l).sum = ∑' (a : α), (l.count a) * (f a) := by
  rw [tsum_eq_sum_of_mul_count]
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]

example (l : List α) (f : α → ℝ≥0∞) : (List.map f l).prod = ∏' (a : α), (f a) ^ (l.count a) := by
  rw [tprod_eq_prod_of_pow_count]
  exact Finset.prod_list_map_count l f





lemma pure_sequence (ν : DiscreteMeasure α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]



lemma sequence_bind (μ ν : DiscreteMeasure α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]



noncomputable def pi' (μs : List (DiscreteProbabilityMeasure α)) :
  DiscreteProbabilityMeasure (List α) := sequence μs





-- noncomputable def binom₂' (p : ℝ≥0) (h : p ≤ 1) : (n : ℕ) → DiscreteProbabilityMeasure (Fin (n+1)) := fun n ↦ (sequence <| List.replicate n (coin p h)).map (List.count true)

def List.count' {α : Type u} [BEq α] (a : α) (n : ℕ) : (l : List α) → (hl : l.length = n) → Fin (n + 1) := fun l hl ↦ ⟨l.count a, by
  apply lt_of_le_of_lt List.count_le_length (hl ▸ lt_add_one l.length)⟩

noncomputable def binom₃ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure (Fin (n + 1)) := by
  have f : (List.replicate n (coin p h)).length = n := by exact List.length_replicate
  let l := (sequence <| List.replicate n (coin p h))

  -- have l := (sequence <| List.replicate n (coin p h)).map (List.count' true)

  sorry





noncomputable def prodList (v : List (DiscreteMeasure α))
  : DiscreteMeasure (List α) := v.traverse id


end coin

end DiscreteProbabilityMeasure



lemma traverse_singleton {α β : Type} (a : α) [Applicative m] :
  traverse id [DiscreteMeasure.pure a] = DiscreteMeasure.pure [a] := by
  simp
