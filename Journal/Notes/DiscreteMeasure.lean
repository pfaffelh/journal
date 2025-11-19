import Mathlib

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β δ : Type*}

-- add to indicator
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator (fun _ ↦ 1) a = s.indicator f a := by
  simp [Set.indicator]

lemma ite_ite (d : Prop) [Decidable d] (a b c : α) : (if d then a else if d then b else c) = (if d then a else c) := by
  by_cases h : d <;> simp only [h, ↓reduceIte]

lemma ite_double (d : Prop) [Decidable d] (a b : α) : (if d then a else if d then b else a) = a := by
  rw [ite_ite, ite_self]

@[simp]
lemma Set.indicator.mul_indicator_eq' (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp [Set.indicator]

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


-- to Mathlib.MeasureTheory.Measure.AEMeasurable
lemma Measure.join_sum {α : Type u_1} {mα : MeasurableSpace α} {ι : Type u_7} (m : ι → Measure (Measure α)) :
(sum fun (i : ι) ↦ m i).join = sum fun (i : ι) ↦ (m i).join := by
  rw [Measure.join]
  simp_rw [lintegral_sum_measure]
  simp_rw [Measure.join]
  ext s hs
  rw [ofMeasurable_apply]
  rw [Measure.sum_apply]
  apply tsum_congr (fun i ↦ ?_)
  rw [ofMeasurable_apply]
  repeat assumption

lemma Measure.bind_sum {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {ι : Type u_7} (m : ι → Measure α) (f : α → Measure β) (h : AEMeasurable f (sum fun i => m i)) :
  (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  rw [Measure.bind]
  simp_rw [Measure.bind]
  rw [Measure.map_sum]
  rw [Measure.join_sum]
  exact h

lemma Measure.bind_smul {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α) (f : α → Measure β) :
  (c • m).bind f = c • (m.bind f) := by
  rw [Measure.bind]
  simp_rw [Measure.bind]
  rw [Measure.map_smul]
  rw [Measure.join_smul]





noncomputable def discreteMeasure (f : α → ℝ≥0∞) : @Measure α ⊤ :=
  sum (fun a ↦ (f a) • (@Measure.dirac α ⊤ a))

@[simp]
lemma discreteMeasure_apply (f : α → ℝ≥0∞) (s : Set α) :
    discreteMeasure f s = ∑' (i : α), f i * s.indicator 1 i := by
  simp [discreteMeasure]

lemma discreteMeasure_apply₁ (f : α → ℝ≥0∞) (s : Set α) :
    discreteMeasure f s = ∑' (i : α), s.indicator f i := by
  simp [discreteMeasure]

lemma discreteMeasure_apply₂ (f : α → ℝ≥0∞) (s : Set α) :
    discreteMeasure f s = ∑' (i : s), f i := by
  simp [discreteMeasure, tsum_subtype]

@[simp]
lemma discreteMeasure_apply_singleton (f : α → ℝ≥0∞) (u : α) :
    discreteMeasure f {u} = f u := by
  rw [discreteMeasure_apply₂, tsum_singleton]

@[simp]
lemma discreteMeasure_apply_univ (f : α → ℝ≥0∞) :
    discreteMeasure f Set.univ = ∑' (a : α), f a := by
  simp_rw [discreteMeasure_apply₁, Set.indicator_univ]

structure DiscreteMeasure (α : Type*) where
  weight : α → ℝ≥0∞

namespace DiscreteMeasure

@[coe]
noncomputable def toMeasure : DiscreteMeasure α → @Measure α ⊤ := fun μ ↦ discreteMeasure μ.weight

noncomputable instance : Coe (DiscreteMeasure α) (@Measure α ⊤) where
  coe μ : @Measure α ⊤ := μ.toMeasure

noncomputable instance : CoeFun (DiscreteMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toMeasure

-- @[simp]
-- lemma toMeasure_apply (μ : DiscreteMeasure α) (s : Set α) : μ.toMeasure s = μ s := by
--   rfl

-- @[simp]
-- lemma coe_apply (μ : DiscreteMeasure α) (s : Set α) : (μ : @Measure α ⊤) s = μ s := rfl

@[simp]
lemma apply (μ : DiscreteMeasure α) (s : Set α) : μ s = discreteMeasure μ.weight s := by
  rfl

lemma apply₀ (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (i : α), μ.weight i * s.indicator 1 i := by
  simp

lemma apply₁ (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (i : α), s.indicator μ.weight i := by
  rw [apply₀]
  simp

lemma apply₂ (μ : DiscreteMeasure α) (s : Set α) : μ s =
    ∑' (a : s), (μ.weight a) := by
  simp [tsum_subtype]

@[simp]
lemma apply_singleton (μ : DiscreteMeasure α) (a : α) : μ {a} =
    μ.weight a := by
  rw [apply₂]
  simp only [tsum_singleton]

lemma singleton_eq_weight (μ : DiscreteMeasure α) : (fun (a : α) ↦ μ {a}) = μ.weight := by
  ext a
  rw [apply_singleton]

/- Additivity for a `DiscreteMeasure` not only applies to countable unions, but to arbitrary ones.-/
lemma m_iUnion (μ : DiscreteMeasure α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : μ (⋃ d, s d) = ∑' (d : δ), μ (s d) := by
  simp only [apply, discreteMeasure_apply, Set.indicator.mul_indicator_eq']
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

lemma m_iUnion_set_singleton (μ : DiscreteMeasure α) (s : Set α) : μ s = ∑' (a : s), μ {a.val} := by
  simp_rw [apply_singleton, apply₂]

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
lemma ext_singleton {μ₁ μ₂ : DiscreteMeasure α}
    (h : ∀ a, μ₁ {a} = μ₂ {a}) : μ₁ = μ₂ :=by
  simp_rw [apply_singleton] at h
  apply ext_weight
  ext x
  exact h x

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteMeasure α} (h : μ₁.toMeasure = μ₂.toMeasure) : μ₁ = μ₂ :=
by
  apply ext_weight
  rw [← singleton_eq_weight, ← singleton_eq_weight]
  simp [h]

@[simp]
lemma apply_univ (μ : DiscreteMeasure α) : μ Set.univ = ∑' (a : α), μ.weight a := by
  simp only [apply, discreteMeasure_apply, Set.indicator.mul_indicator_eq']
  simp_rw [Set.indicator_univ]

lemma isProbabilityMeasure_iff (μ : DiscreteMeasure α) : IsProbabilityMeasure μ.toMeasure ↔ HasSum μ.weight 1 := by
  rw [MeasureTheory.isProbabilityMeasure_iff, DiscreteMeasure.apply_univ, Summable.hasSum_iff ENNReal.summable]

section map

noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : (DiscreteMeasure β) := ⟨fun b ↦ μ (g⁻¹' {b})⟩

@[simp]
lemma map_weight (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x = μ (g⁻¹' {x}) := by
  rfl

instance topMeasurableSpace'' : MeasurableSpace α := ⊤

instance topMeasurableSpace : MeasurableSpace β := ⊤

instance topMeasurableSpace' : MeasurableSpace γ := ⊤

lemma map_eq_toMeasure (μ : DiscreteMeasure α) (g : α → β) : μ.map g = μ.toMeasure.map g := by
  ext s
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [m_iUnion_singleton]
  simp_rw [apply_singleton, map_weight]
  have h : g⁻¹' s = ⋃ (i : s), g⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  exact (m_iUnion _ _ (pairwise_disjoint_fiber_subtype s)).symm

-- lemma map_toMeasure (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = μ.toMeasure.map g := by
--   rw [map_eq_toMeasure]

lemma map_coe  (μ : DiscreteMeasure α) (f : α → β) : ((μ.map f : DiscreteMeasure β) : Measure β) = Measure.map f (μ : Measure α) := by
  exact map_eq_toMeasure μ f

lemma map_toMeasure' (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = sum (fun a ↦ μ.weight a • (@dirac β ⊤ (g a))) := by
  rw [map_eq_toMeasure]
  ext s
  rw [toMeasure, discreteMeasure, Measure.map_sum]
  simp_rw [Measure.map_smul, Measure.map_dirac (f := g) (hf := (by measurability))]
  measurability

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext s
  rw [map_coe, map_coe, map_coe]
  rw [Measure.map_map (by measurability) (by measurability)]

lemma map_apply (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (b : β), μ (g⁻¹' {b}) * s.indicator 1 b := by
  simp

lemma map_apply' (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), μ.weight a * s.indicator 1 (g a) := by
  rw [map_toMeasure']
  simp

lemma map_apply'' (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : α), μ.weight a * (g⁻¹' s).indicator 1 a := map_apply' μ g s

lemma map_apply₁ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (b : s), μ (g⁻¹' {b.val}) := by
  rw [map_apply]
  rw [tsum_subtype s (fun b ↦ μ.toMeasure (g ⁻¹' {↑b}))]
  apply tsum_congr (fun b ↦ ?_)
  by_cases h : b ∈ s <;> simp [h]

lemma map_apply₂ (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (a : g⁻¹' s), (μ {a.val}) := by
  rw [map_toMeasure', Measure.sum_apply]
  simp_rw [Measure.smul_apply]
  simp_rw [Measure.dirac_apply]
  · rw [tsum_subtype (g ⁻¹' s) (fun a ↦ μ.toMeasure {a})]
    apply tsum_congr (fun b ↦ ?_)
    nth_rw 2 [← Set.indicator.mul_indicator_eq]
    congr
    rw [apply_singleton μ b]
  · measurability

end map


section lintegral

noncomputable def lintegral (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : ℝ≥0∞ := ∑' (a : α), μ {a} * (g a)

lemma lintegral_eq_toMeasure (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : μ.lintegral g = ∫⁻ (a : α), g a ∂ μ.toMeasure := by
  rw [toMeasure, discreteMeasure, lintegral]
  simp only [lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp_rw [apply_singleton]

end lintegral

section join

noncomputable def join (m : DiscreteMeasure (DiscreteMeasure α)) : (DiscreteMeasure α) := ⟨fun a ↦ ∑' (μ : DiscreteMeasure α), m {μ} * μ {a}⟩

@[simp]
lemma join_weight (m : DiscreteMeasure (DiscreteMeasure α)) (x : α) : m.join.weight x = ∑' (μ : DiscreteMeasure α), m {μ} * μ {x} := by
  rfl

lemma join_coe (m : DiscreteMeasure (DiscreteMeasure α)) : m.join = (m.toMeasure.map toMeasure).join := by
  ext s
  rw [Measure.join_apply (mα := ⊤) (hs := by measurability)]
  rw [lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [← lintegral_eq_toMeasure, apply₂]
  simp_rw [join_weight, lintegral]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left]
  congr
  rw [m_iUnion_set_singleton]

lemma join_toMeasure' (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m.weight μ • μ.toMeasure) := by
  ext s hs
  rw [join_coe, toMeasure, discreteMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply]
  rw [Measure.map_smul]
  rw [Measure.join_smul]
  rw [Measure.smul_apply]
  rw [smul_eq_mul, smul_eq_mul]
  rw [Measure.map_dirac]
  rw [Measure.join_dirac]
  measurability

lemma join_apply (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) : m.join s = ∑' (μ : DiscreteMeasure α), m {μ} * μ s := by
  simp only [join_toMeasure']
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, smul_eq_mul]
  rw [apply_singleton]

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
  simp_rw [ENNReal.tsum_mul_left, apply_singleton]
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
  rw [bind_apply_eq_toMeasure, toMeasure, discreteMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete)]
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
lemma bind_weight (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g).weight x = ∑' (a : α), μ.weight a * (g a) {x} := by
  rw [← apply_singleton, bind_apply]

lemma join_map_map (m : DiscreteMeasure (DiscreteMeasure α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  rw [bind_apply, apply_singleton, map_weight, join_apply]
  apply tsum_congr (fun b ↦ ?_)
  congr <;> rw [apply_singleton]
  rw [map_weight]

end bind

section coin

open Bool ENNReal
example (p : ℝ≥0) (hp : p ≤ 1): ∑' (b : Bool), (if b then p else (1 - p)) = 1 := by
  rw [tsum_bool]
  simp only [false_eq_true, ↓reduceIte]
  exact tsub_add_cancel_of_le hp

noncomputable def coin (p : ℝ≥0) (_ : p ≤ 1) : DiscreteMeasure Bool :=
  ⟨fun (b : Bool) ↦ if b then p else (1 - p)⟩

lemma coin_weight (p : ℝ≥0) (h : p ≤ 1) (b : Bool) : (coin p h).weight b = if b then ofNNReal p else (1 - ofNNReal p) := by
  rfl

lemma coin_not (p : ℝ≥0) (h : p ≤ 1) : (coin p h).map not  = coin (1-p) (tsub_le_self) := by
  have g_not (b : Bool) : not ⁻¹' {b} = {!b} := by
    ext y; cases' y <;> simp
  ext x
  rw [map_apply, apply_singleton, tsum_bool, g_not, g_not, coin_weight, apply_singleton, coin_weight, apply_singleton, coin_weight]
  cases' x <;> simp [sub_sub_cancel one_ne_top (coe_le_one_iff.mpr h)]







end coin

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

def ofDiscreteMeasure' (μ : DiscreteMeasure α) (hμ : IsProbabilityMeasure μ.toMeasure) : DiscreteProbabilityMeasure α := by
  obtain h := (DiscreteMeasure.isProbabilityMeasure_iff μ).mp hμ
  exact ⟨μ, h⟩

lemma apply (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (i : α), (μ.val.weight i : ℝ≥0∞) * s.indicator 1 i := by
  rw [DiscreteMeasure.apply₀ μ s]

@[simp]
lemma apply_univ_eq_one (P : DiscreteProbabilityMeasure α) : P Set.univ = 1 := by
  rw [DiscreteMeasure.apply_univ]
  have h : HasSum P.val.weight 1 := P.prop
  exact HasSum.tsum_eq h

lemma apply_le_one (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≤ 1 := by
  exact prob_le_one

lemma apply_ne_top (P : DiscreteProbabilityMeasure α) (s : Set α) : P s ≠ ⊤ := by
  exact measure_ne_top P s

@[simp]
lemma toProbabilityMeasure_apply (P : DiscreteProbabilityMeasure α) (s : Set α) : P.toProbabilityMeasure s = P s := by
  simp only [toProbabilityMeasure, ProbabilityMeasure.mk_apply, DiscreteMeasure.apply, discreteMeasure_apply]
  exact ENNReal.coe_toNNReal ((P.apply s).symm ▸ apply_ne_top P s)

lemma apply₀ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (i : α), μ.val.weight i * s.indicator 1 i := by
  exact DiscreteProbabilityMeasure.apply μ s

lemma apply₁ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (i : α), s.indicator μ.val.weight i := by
  simp


lemma apply₂ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s =
    ∑' (a : s), (μ.val.weight a) := by
  simp [tsum_subtype]

@[simp]
lemma apply_singleton (μ : DiscreteProbabilityMeasure α) (a : α) : μ {a} =
    μ.val.weight a := by
  rw [apply₂]
  simp only [tsum_singleton]

/- Additivity for a `DiscreteProbabilityMeasure` not only applies to countable unions, but to arbitrary ones.-/
lemma m_iUnion (P : DiscreteProbabilityMeasure α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : P (⋃ d, s d) = ∑' (d : δ), P (s d) := by
  apply DiscreteMeasure.m_iUnion P s hs

lemma singleton_eq_weight (μ : DiscreteProbabilityMeasure α) : (fun (a : α) ↦ μ {a}) = μ.val.weight := by
  apply DiscreteMeasure.singleton_eq_weight

lemma m_iUnion_set_singleton (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (a : s), μ {a.val} := by
  simp_rw [apply_singleton, apply₂]

lemma m_iUnion_singleton (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (x : s), μ {x.val} := by
  apply DiscreteMeasure.m_iUnion_set_singleton

lemma ext_val {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : μ₁.val = μ₂.val) : μ₁ = μ₂ :=
by
  exact Subtype.ext h

lemma ext_val' {μ₁ μ₂ : DiscreteProbabilityMeasure α} :
  (toDiscreteMeasure μ₁ = toDiscreteMeasure μ₂) ↔ μ₁ = μ₂ :=
by
  exact ⟨fun h ↦ ext_val h, fun h ↦ by rw [h]⟩

lemma ext_weight {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : μ₁.val.weight = μ₂.val.weight) : μ₁ = μ₂ :=
by
  exact ext_val <| DiscreteMeasure.ext_weight h

@[ext]
lemma ext {μ₁ μ₂ : DiscreteProbabilityMeasure α}
    (h : ∀ a, μ₁ {a} = μ₂ {a}) : μ₁ = μ₂ :=by
  apply ext_weight
  simp_rw [apply_singleton] at h
  ext x
  exact h x

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteProbabilityMeasure α} (h : μ₁.val.toMeasure = μ₂.val.toMeasure) : μ₁ = μ₂ :=
by
  apply ext_val
  exact DiscreteMeasure.toMeasure_ext' h



-- map
lemma map_isProbabilityMeasure (g : α → β) (μ : DiscreteProbabilityMeasure α) : HasSum (μ.val.map g).weight 1 := by
  rw [← DiscreteMeasure.isProbabilityMeasure_iff]
  have h : IsProbabilityMeasure μ.val.toMeasure := by
    rw [DiscreteMeasure.isProbabilityMeasure_iff μ.val]
    exact μ.prop
  rw [DiscreteMeasure.map_coe]
  rw [@isProbabilityMeasure_map_iff α β ⊤ ⊤ μ.val.toMeasure g (by measurability)]
  exact h

noncomputable def map (g : α → β) (μ : DiscreteProbabilityMeasure α) : (DiscreteProbabilityMeasure β) := ⟨⟨fun b ↦ μ (g⁻¹' {b})⟩, map_isProbabilityMeasure g μ⟩

lemma map_eq_toDiscreteMeasure (g : α → β) (μ : DiscreteProbabilityMeasure α) : (μ.map g) = μ.val.map g := by
  congr

-- join
noncomputable def join (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : (DiscreteProbabilityMeasure α) := by
  let m' : DiscreteMeasure (DiscreteMeasure α) := (DiscreteMeasure.map Subtype.val m.val)
  have hweight (μ : DiscreteMeasure α) (hμ : ¬ (HasSum μ.weight 1)) : m'.weight μ = 0 := by
    simp only [DiscreteMeasure.map_weight, DiscreteMeasure.apply, discreteMeasure_apply,
      Set.indicator.mul_indicator_eq', ENNReal.tsum_eq_zero, Set.indicator_apply_eq_zero,
      Set.mem_preimage, Set.mem_singleton_iff, Subtype.forall, m']
    exact fun  a ha haμ ↦ False.elim <| hμ (haμ.symm ▸ ha)
  have hm₀ (μ : DiscreteProbabilityMeasure α) :  m.val.weight μ = m'.weight μ.val := by
    simp only  [m', DiscreteMeasure.map_weight, DiscreteMeasure.apply]
    have h₄ : (toDiscreteMeasure ⁻¹' {toDiscreteMeasure μ}) = {μ} := by
      simp_rw [Set.preimage, Set.mem_singleton_iff, ext_val', Set.setOf_eq_eq_singleton]
    change _ = m (toDiscreteMeasure ⁻¹' {toDiscreteMeasure μ})
    rw [h₄, DiscreteMeasure.apply_singleton]
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

lemma join_eq_toDiscreteMeasure (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) : m.join = (DiscreteMeasure.map Subtype.val m.val).join := by
  rfl




-- bind
noncomputable def bind (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : (DiscreteProbabilityMeasure β) := (μ.map g).join

lemma bind_eq_toDiscreteMeasure (μ : DiscreteProbabilityMeasure α) (g : α → DiscreteProbabilityMeasure β) : μ.bind g = μ.val.bind (Subtype.val ∘ g) := by
  rw [bind, DiscreteMeasure.bind, join_eq_toDiscreteMeasure]
  congr
  rw [← DiscreteMeasure.map_map]
  congr

lemma join_map_map (m : DiscreteProbabilityMeasure (DiscreteProbabilityMeasure α)) (g : α → β) : map g m.join = (map (map g) m).join := by
  ext x
  rw [map_eq_toDiscreteMeasure, join_eq_toDiscreteMeasure]
  rw [join_eq_toDiscreteMeasure, map_eq_toDiscreteMeasure]
  rw [← DiscreteMeasure.join_map_map]
  rw [DiscreteMeasure.map_map]
  rw [DiscreteMeasure.map_map]
  congr

end DiscreteProbabilityMeasure

open Classical
noncomputable def DiscreteMeasure.pure (a : α) : DiscreteMeasure α :=
  ⟨fun b ↦ if b = a then 1 else 0⟩

@[simp]
lemma DiscreteMeasure.pure_weight (a : α) : (DiscreteMeasure.pure a).weight = fun b ↦ if b = a then 1 else 0 := rfl

@[simp]
lemma DiscreteMeasure.pure_apply (a : α) (s : Set α) : (DiscreteMeasure.pure a) s = s.indicator 1 a := by
  simp only [apply, pure_weight, discreteMeasure_apply, ite_mul, one_mul, zero_mul]
  rw [ENNReal.tsum_eq_add_tsum_ite a]
  simp only [↓reduceIte]
  nth_rw 2 [← add_zero (s.indicator 1 a)]
  congr
  rw [ENNReal.tsum_eq_zero]
  intro i
  exact ite_double (i = a) 0 (s.indicator 1 i)

lemma DiscreteMeasure.pure_coe (a : α) : (DiscreteMeasure.pure a) = Measure.dirac a := by
  ext s
  rw [DiscreteMeasure.pure_apply, Measure.dirac_apply' a (by measurability)]

open Classical
noncomputable def DiscreteProbabilityMeasure.pure (a : α) : DiscreteProbabilityMeasure α :=
  ⟨DiscreteMeasure.pure a, by rw [Summable.hasSum_iff ENNReal.summable, DiscreteMeasure.pure, tsum_ite_eq]⟩

namespace DiscreteProbabilityMeasure

@[simp]
lemma pure_eq_toDiscreteMeasure (a : α) (s : Set α) : DiscreteProbabilityMeasure.pure a s = (DiscreteMeasure.pure a) s := by
  simp only [DiscreteProbabilityMeasure.pure, DiscreteMeasure.apply, discreteMeasure_apply, DiscreteMeasure.pure_weight]

theorem pure_bind (a : α) (f : α → DiscreteProbabilityMeasure β) :
(pure a).bind f = f a := by
  apply Subtype.ext


  rw [DiscreteMeasure.apply_singleton]
  rw [DiscreteMeasure.apply_singleton]
  rw [bind_eq_toDiscreteMeasure]
  rw [DiscreteMeasure.bind_weight]
  -- conv => left; left; intro b; simp?
  simp_rw [pure_eq_toDiscreteMeasure, DiscreteMeasure.pure_apply, mul_comm]

  rw [← tsum_subtype]

  , Set.indicator, Set.mem_singleton_iff]

  simp only [Set.mem_singleton_iff, Pi.one_apply, comp_apply, DiscreteMeasure.apply,
    discreteMeasure_apply, Set.indicator.mul_indicator_eq', ite_mul, one_mul, zero_mul]
  rw [Set.mem_singleton]


  simp?






  sorry


end DiscreteProbabilityMeasure
end DiscreteProbabilityMeasure
