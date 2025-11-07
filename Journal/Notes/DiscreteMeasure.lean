import Mathlib

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β : Type*}

-- add to indicator
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator (fun _ ↦ 1) a = s.indicator f a := by
  simp [Set.indicator]

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




noncomputable def discreteMeasure (f : α → ℝ≥0∞) : @Measure α ⊤ :=
  sum (fun a ↦ (f a) • (@Measure.dirac α ⊤ a))

noncomputable def discreteProbabilityMeasure (p : PMF α) : @Measure α ⊤ := discreteMeasure p


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

lemma discreteProbabilityMeasure.isProabilityMeasure (p : PMF α) : IsProbabilityMeasure (discreteProbabilityMeasure p) := by
  simp [discreteProbabilityMeasure]
  rw [isProbabilityMeasure_iff]
  rw [discreteMeasure_apply_univ]
  exact PMF.tsum_coe p





structure DiscreteMeasure (α : Type*) where
  weight : α → ℝ≥0∞

structure DiscreteProbabilityMeasure (α : Type*) where
  weight : PMF α

noncomputable def toDiscreteMeasure (μ : DiscreteProbabilityMeasure α) : DiscreteMeasure α :=
  ⟨μ.weight⟩

namespace DiscreteMeasure

noncomputable def toMeasure (μ : DiscreteMeasure α) : @Measure α ⊤ :=
  discreteMeasure μ.weight

noncomputable instance : Coe (DiscreteMeasure α) (@Measure α ⊤) where
  coe μ : @Measure α ⊤ := μ.toMeasure

noncomputable instance :
  CoeFun (DiscreteMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toMeasure

example (μ : DiscreteMeasure α) (s : Set α) : μ s = μ.toMeasure s := rfl

@[simp]
lemma toMeasure_apply (μ : DiscreteMeasure α) (s : Set α) : μ.toMeasure s = μ s := rfl

@[simp]
lemma coe_apply (μ : DiscreteMeasure α) (s : Set α) : (μ : @Measure α ⊤) s = μ s := rfl

@[simp]
lemma apply (μ : DiscreteMeasure α) (s : Set α) : μ s = discreteMeasure μ.weight s := rfl

example (μ : DiscreteMeasure α) : μ = sum fun (a : α) ↦ (μ.weight a) • (@dirac α ⊤ a) := by rfl

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

/- Additivity for a `DiscreteMeasure` not only applies to countable unions, but to arbitrary ones.-/
lemma m_iUnion (μ : DiscreteMeasure α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : μ (⋃ d, s d) = ∑' (d : δ), μ (s d) := by
  simp
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

lemma singleton_eq_weight (μ : DiscreteMeasure α) : (fun (a : α) ↦ μ {a}) = μ.weight := by
  ext a
  rw [apply_singleton]

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
lemma ext {μ₁ μ₂ : DiscreteMeasure α}
    (h : ∀ a, μ₁ {a} = μ₂ {a}) : μ₁ = μ₂ :=by
  apply ext_weight
  rw [← singleton_eq_weight, ← singleton_eq_weight]
  ext a
  exact h a

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteMeasure α} (h : μ₁.toMeasure = μ₂.toMeasure) : μ₁ = μ₂ :=
by
  apply ext_weight
  rw [← singleton_eq_weight, ← singleton_eq_weight]
  simp [h]

section map

noncomputable def map (μ : DiscreteMeasure α) (g : α → β) : (DiscreteMeasure β) := ⟨fun b ↦ μ (g⁻¹' {b})⟩

@[simp]
lemma map_weight (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g).weight x = μ (g⁻¹' {x}) := by
  rfl

instance topMeasurableSpace'' : MeasurableSpace α := ⊤

instance topMeasurableSpace : MeasurableSpace β := ⊤

instance topMeasurableSpace' : MeasurableSpace γ := ⊤

lemma map_apply_eq_toMeasure (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = μ.toMeasure.map g s := by
  rw [Measure.map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  rw [m_iUnion_singleton]
  simp_rw [apply_singleton, map_weight]
  have h : g⁻¹' s = ⋃ (i : s), g⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  exact (m_iUnion _ _ (pairwise_disjoint_fiber_subtype s)).symm

lemma map_toMeasure (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = μ.toMeasure.map g := by
  ext s
  rw [map_apply_eq_toMeasure]

lemma map_toMeasure' (μ : DiscreteMeasure α) (g : α → β)  : (μ.map g).toMeasure = sum (fun a ↦ μ.weight a • (@dirac β ⊤ (g a))) := by
  ext s
  rw [map_apply_eq_toMeasure, toMeasure, discreteMeasure, Measure.map_sum]
  simp_rw [Measure.map_smul, Measure.map_dirac (f := g) (hf := (by measurability))]
  measurability

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  ext s
  repeat rw [map_apply_eq_toMeasure]
  rw [map_toMeasure, Measure.map_map] <;> measurability

lemma map_apply (μ : DiscreteMeasure α) (g : α → β) (s : Set β) : μ.map g s = ∑' (b : β), μ (g⁻¹' {b}) * s.indicator 1 b := by
  simp

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

section bind

noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := ⟨fun b ↦ ∑' (a : α), μ {a} * (g a) {b}⟩




end bind




end DiscreteMeasure

instance topMeasurableSpace : MeasurableSpace α := ⊤

-- Given `f : α → ℝ≥0∞` and `g : α → β`, this is the measure (on `⊤`, i.e. the power set of `β`),
-- which adds mass `f a` to `g a`.
noncomputable def Function.to_discrete_measure (f : α → ℝ≥0∞) : @Measure α ⊤ :=
  sum (fun a ↦ (f a : ℝ≥0∞) • (@Measure.dirac α ⊤ a))

lemma l1 (b : β) : OuterMeasure.toMeasure (OuterMeasure.dirac b) ((OuterMeasure.dirac_caratheodory b).symm ▸ le_top) = @Measure.dirac β ⊤ b := by
  rfl

def DiscreteMeasure (α : Type u): Type (max 0 u) :=
  { μ : @Measure α ⊤ // ∃ (f : α → ℝ≥0∞), μ = f.to_discrete_measure}

noncomputable def DiscreteMeasure.f {α} (μ : @DiscreteMeasure α) : α → ℝ≥0∞ :=
  Classical.choose μ.prop

def map (μ : DiscreteMeasure α) (f : α → β) : DiscreteMeasure β := ⟨μ.val.map f, ?_⟩


lemma DiscreteMeasure.eq_to_discrete (μ : @DiscreteMeasure α) :
    μ.val = (DiscreteMeasure.f μ).to_discrete_measure := by
  exact Classical.choose_spec μ.prop

lemma DiscreteMeasure.eq_to_discrete' (μ : @DiscreteMeasure α) :
    μ.val = sum fun (a : α) ↦ (μ.f a) • (@dirac α ⊤ a) := by
  exact Classical.choose_spec μ.prop



@[simp]
lemma DiscreteMeasure.apply {f : α → ℝ≥0∞} {s : Set α} : f.to_discrete_measure s = ∑' (i : α), f i * s.indicator (fun _ => 1) i := by
  simp [to_discrete_measure]
  congr

-- add to indicator?
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator (fun _ ↦ 1) a = s.indicator f a := by
  simp [Set.indicator]


lemma DiscreteMeasure.apply' {f : α → ℝ≥0∞} {s : Set α} : f.to_discrete_measure s = ∑' (i : α), s.indicator f i := by
  simp only [DiscreteMeasure.apply]
  simp_rw [Set.indicator.mul_indicator_eq]

lemma DiscreteMeasure.apply'' (f : α → ℝ≥0∞) (s : Set α) : f.to_discrete_measure s =
    ∑' (a : s), (f a) := by
  simp only [DiscreteMeasure.apply', tsum_subtype]

lemma Function.to_discrete_measure.isProbabilityMeasure_iff (f : α → ℝ≥0∞) : (IsProbabilityMeasure f.to_discrete_measure) ↔ ∑' i, f i = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h.measure_univ, DiscreteMeasure.apply']
    simp
  · rw [MeasureTheory.isProbabilityMeasure_iff]
    simp [DiscreteMeasure.apply, h]


@[simp]
lemma DiscreteMeasure.apply_singleton (f : α → ℝ≥0∞) (u : α) :
    f.to_discrete_measure {u} = f u := by
  rw [DiscreteMeasure.apply'', tsum_singleton]


-- for ref only
lemma summable (f : α → ℝ≥0∞) : Summable f := by
  exact ENNReal.summable

-- delete
example (y : ℝ) : Set.univ.indicator (fun _ ↦ 1) y = 1 := by
  apply Set.indicator_of_mem (by trivial) fun x => 1

-- section finite measure
lemma support_countable (f : α → ℝ≥0∞) (hf : IsFiniteMeasure f.to_discrete_measure) : (support f).Countable := by
  simp [to_discrete_measure, isFiniteMeasure_iff] at hf
  refine Summable.countable_support_ennreal hf.ne




-- section support
open Classical
lemma tsum_support (f : α → ℝ≥0∞) (s : Set α) : f.to_discrete_measure s = f.to_discrete_measure ((support f) ∩ s) := by
  simp [to_discrete_measure]
  apply tsum_congr
  intro b
  simp only [Set.indicator, support]
  by_cases hb : f b = 0
  · simp_rw [hb]
    rw [zero_mul, zero_mul]
  · simp [hb]

example {α : Type*} (f : α → ℝ≥0∞) (a : α) :
    ∑' x, f x = f a + ∑' x, (if x = a then 0 else f x) := by
  exact ENNReal.tsum_eq_add_tsum_ite a


example (f : ι → ℝ≥0∞) (i : ι) : ∑' (i : ι), f i = f i + ∑' (j : ι), (Set.univ \{i}).indicator f j := by
  simp[Set.indicator]
  apply ENNReal.tsum_eq_add_tsum_ite i


/- Additivity for a `to_discrete_measure` not only applies to countable unions, but to arbitrary ones.-/
lemma m_iUnion (f : α → ℝ≥0∞) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : f.to_discrete_measure (⋃ d, s d) = ∑' (d : δ), f.to_discrete_measure (s d) := by
  simp only [DiscreteMeasure.apply]
  rw [ENNReal.tsum_comm (f := fun d i ↦ f i * (s d).indicator (fun x => 1) i)]
  apply tsum_congr
  intro b
  rw [ENNReal.tsum_mul_left]
  apply congrArg (HMul.hMul (f b))
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ i, b ∈ s i <;> simp only [h₀, ↓reduceIte]
  · obtain ⟨i, hi⟩ := h₀
    rw [ENNReal.tsum_eq_add_tsum_ite i]
    simp only [hi, ↓reduceIte]
    nth_rw 1 [← add_zero 1] ; congr
    apply (ENNReal.tsum_eq_zero.mpr ?_).symm
    simp_rw [ite_eq_left_iff, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun j hj ↦ Disjoint.notMem_of_mem_left (hs (id (Ne.symm hj))) hi
  · refine (ENNReal.tsum_eq_zero.mpr ?_).symm
    intro j
    push_neg at h₀
    specialize h₀ j
    simp [h₀]

lemma pairwise_disjoint_singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  simp_rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
  exact Subtype.coe_ne_coe.mpr hab

lemma m_iUnion_singleton (f : α → ℝ≥0∞) (s : Set α) : (to_discrete_measure f) s = ∑' (x : s), (to_discrete_measure f) {x.val} := by
  nth_rw 1 [← Set.iUnion_of_singleton_coe s]
  exact _root_.m_iUnion f _ (pairwise_disjoint_singleton_subtype s)

lemma l2 (f : α → ℝ≥0∞) : f = (fun b ↦ (f.to_discrete_measure) {b}) := by
  ext b
  rw [DiscreteMeasure.apply_singleton]


@[simp]
lemma to_id (f : α → ℝ≥0∞) : ((fun b ↦ (f.to_discrete_measure) {b}).to_discrete_measure) = (f.to_discrete_measure) := by
  simp_rw [DiscreteMeasure.apply_singleton]





-- section ofReal

noncomputable def Function.to_discrete_measure_ofReal (f : α → ℝ) : @Measure α ⊤ :=
  Function.to_discrete_measure (ENNReal.ofReal ∘ f)


lemma to_discrete_measure_ofReal_apply (f : α → ℝ) (s : Set α) :
    f.to_discrete_measure_ofReal s = ∑' a, (ENNReal.ofReal (f a)) * s.indicator (fun _ ↦ 1) a := by
  rw [to_discrete_measure_ofReal]
  exact DiscreteMeasure.apply


-- section ext

theorem eq_iff {f₁ f₂ : α → ℝ≥0∞} : f₁ = f₂ ↔
    f₁.to_discrete_measure = f₂.to_discrete_measure := by
  refine ⟨fun h ↦ by rw [h], ?_⟩
  rw [← not_imp_not]
  intro h
  obtain ⟨a, ha⟩ := ne_iff.mp h
  change _ ≠ _
  rw [DFunLike.ne_iff]
  use {a}
  simp only [DiscreteMeasure.apply_singleton]
  exact ha


example (f : α → ℝ≥0∞): x * ∑' y, f y = ∑' y, x * f y := by
  exact Eq.symm ENNReal.tsum_mul_left


example (h : 0 = a) : a = 0 := by exact id (Eq.symm h)


theorem Function.to_discrete_measure_map' (f : α → ℝ≥0∞) (g : α → β) :
    f.to_discrete_measure.map g = sum (fun a ↦ f a • (@dirac β ⊤ (g a))) := by
  simp [Function.to_discrete_measure]
  rw [Measure.map_sum]
  simp_rw [Measure.map_smul]
  congr
  simp_rw [Measure.map_dirac (f := g) (hf := (by measurability))]
  measurability

example (s : Set β) (g : β → ℝ≥0∞) : ∑' (b : β), (g b) * s.indicator (fun x => 1) b = ∑' (b : β), s.indicator g b := by
  simp_rw [Set.indicator.mul_indicator_eq]

example (s : Set β) (g : β → ℝ≥0∞) : ∑' (b : β), s.indicator (fun x => 1) b * (g b) = ∑' (b : s), g b.val := by
  simp_rw [mul_comm, Set.indicator.mul_indicator_eq]
  exact Eq.symm (tsum_subtype s g)

lemma pairwise_disjoint_fiber' (s : Set β) : Pairwise (Disjoint on fun (x : β) => (g⁻¹' {x} : Set α)) := by
  exact pairwise_disjoint_fiber g

lemma pairwise_disjoint_fiber_subtype (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
    fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)


theorem Function.to_discrete_measure_map (f : α → ℝ≥0∞) (g : α → β) :
    f.to_discrete_measure.map g = (fun b ↦ f.to_discrete_measure (g⁻¹' {b})).to_discrete_measure := by
  ext s
  rw [map_apply (mα := ⊤) (mβ := ⊤) (hf := by measurability) (hs := by measurability)]
  nth_rw 2 [DiscreteMeasure.apply']
  rw [← tsum_subtype]
  have h : g⁻¹' s = ⋃ (i : s), g⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  exact _root_.m_iUnion _ _ (pairwise_disjoint_fiber_subtype s)

lemma DM.map (μ : DiscreteMeasure α) (g : α → β) : μ.val.map g = (fun b ↦ (μ.val (g⁻¹' {b}))).to_discrete_measure := by
  rw [DiscreteMeasure.eq_to_discrete μ]
  exact to_discrete_measure_map μ.f g

theorem Function.to_discrete_measure_map_map (f : α → ℝ≥0∞) (g : α → β) (h : β → γ):
    f.to_discrete_measure.map (h ∘ g) = (f.to_discrete_measure.map g).map h := by
  repeat rw [Function.to_discrete_measure_map]
  simp_rw [Set.preimage_comp, ← eq_iff]
  ext x
  rw [← map_apply (hf := by measurability) (hs := by measurability), ← Function.to_discrete_measure_map]

namespace DiscreteMeasure

noncomputable def map (μ : DiscreteMeasure α) (g : α → β) : DiscreteMeasure β := ⟨μ.val.map g,
  ⟨fun b ↦ (μ.val (g⁻¹' {b})), DM.map μ g⟩⟩

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : μ.map (h ∘ g) = (μ.map g).map h := by
  rw [map, map, map]
  apply Subtype.ext
  simp only
  rw [DiscreteMeasure.eq_to_discrete μ]
  exact to_discrete_measure_map_map μ.f g h



-- to integral
variable {E : Type*} [NormedAddCommGroup E]

theorem integral_linear_combination_dirac
    {f : α → ℝ≥0∞} {g : α → ℝ≥0∞}
    :
    ∫⁻ (a : α), g a ∂ f.to_discrete_measure
    = ∑' a : α, (f a) • (g a) := by
  simp [Function.to_discrete_measure]

theorem lintegral (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) :
    ∫⁻ (a : α), g a ∂ μ.val = ∑' a : α, (μ.f a) • (g a) := by
  rw [DiscreteMeasure.eq_to_discrete μ]
  exact integral_linear_combination_dirac


--def pure (a : α) : DiscreteMeasure α :=
--  (({a} : Set α).indicator (fun _ ↦ 1)).to_discrete_measure



instance TopologicalSpaceTop : TopologicalSpace (α) := ⊤


example (s : Set α) (f : α → ℝ≥0∞) : (Measure.sum (fun (a : α) ↦ (f a) • (dirac a))) s = (∑' (a : α), (f a) • dirac a s) := by
  rw [Measure.sum_apply]
  simp_rw [Measure.smul_apply]
  measurability



def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : DiscreteMeasure β := ⟨μ.val.bind (fun a ↦ (g a).val),
  by
    use fun b : β ↦ ∑' (a : α), (μ.f a) * (g a).f b
    rw [Measure.bind]

    change Ξ.val = _
    sorry
  ⟩


def join (Ξ : DiscreteMeasure (DiscreteMeasure β)) : DiscreteMeasure β := ⟨Ξ.val.bind (fun a ↦ a.val),
  by
    use fun b : β ↦ ∑' (μ : DiscreteMeasure β), (Ξ.f μ) * ((μ.f) b)
    ext s
    rw [Measure.bind]
    rw [Measure.join_apply]
    rw [lintegral_map]
    rw [lintegral]
    rw [DiscreteMeasure.apply]








    rw [DiscreteMeasure.eq_to_discrete', to_discrete_measure]



    have hΞ : Ξ.val = ∑' (μ : DiscreteMeasure β), (Ξ.f μ) • (@Measure.dirac (DiscreteMeasure β) ⊤ μ) := by
      rw [DiscreteMeasure.eq_to_discrete Ξ]
      ext s
      simp [DiscreteMeasure.apply]




      rw [tsum_eq_sum]
      apply tsum_congr






    rw [Measure.bind, Measure.join, to_discrete_measure]
    rw [Measure.sum]
    simp only [smul_toOuterMeasure]





    simp_rw [← integral_linear_combination_dirac]


    sorry⟩

lemma bind (f : α → ℝ≥0∞) (g : α → (β → ℝ≥0∞)) : f.to_discrete_measure.bind (fun a ↦ (g a).to_discrete_measure) = ∑' (a : α), (f a) • (g a).to_discrete_measure := by
  rw [Measure.bind, Measure.map]



  -- ext s
  letI meaTop : MeasurableSpace (@Measure α ⊤) := ⊤
  rw [Measure.bind, Measure.map]
  simp [to_discrete_measure, AEMeasurable.of_discrete]
  have h₁ : Measurable (fun a => sum fun a_1 => g a a_1 • dirac a_1) := by
    measurability
  simp [h₁]







  · rw [integral_linear_combination_dirac]
    simp_rw [to_discrete_measure]
    simp?
    rw [tsum_apply]
    sorry
  · sorry
  · sorry


  rw [to_discrete_measure]
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure]
  simp_rw [lintegral_dirac]

  simp only [smul_eq_mul]

  congr


  rw [DiscreteMeasure.apply]

    (fun b ↦ f.to_discrete_measure g b) = (fun b ↦ (fun a ↦ f a • dirac (g a b)).to_discrete_measure) := by
  ext b
  rw [to_discrete_measure_map]
  congr
  ext a
  rw [dirac_apply]
  simp


noncomputable def Function.to_discrete_measure_bind (f : α → ℝ) (g : α → DiscreteMeasure β) := ∑' a : α, (f a) • (g a).val ∂ f.to_discrete_measure_ofReal



    ∑' (a : α), (f a) • (g a).val

def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : DiscreteMeasure β :=

end DiscreteMeasure













theorem to_discrete_measure_eq_iff'' {f₁ f₂ : α → ℝ≥0∞} (g₁ g₂ : α → β) : (∀ b : β, ∑' a : g₁⁻¹' {b}, f₁ a = ∑' a : g₂⁻¹' {b}, f₂ a) ↔
    f₁.to_discrete_measure g₁ = f₂.to_discrete_measure g₂ := by
  simp_rw [to_discrete_measure_eq']



  refine ⟨fun h b ↦ ?_, fun h b ↦ ?_⟩
  ·
    sorry
  · sorry

example (f : β → γ → ℝ≥0∞) : ∑' (c : γ) (b : β), f b c = ∑' (b : β) (c : γ), f b c := by
  exact ENNReal.tsum_comm

example (f : β → ℝ≥0∞) : (∑' (b : β), f b) * x  = ∑' (b : β) , f b * x := by
  exact Eq.symm ENNReal.tsum_mul_right



  simp [Set.indicator]


  simp


  apply tsum_congr
  intro b
  congr

end PMFassumsofDiracs

section coin

def coinFun (p : ℝ≥0) : Bool → ℝ≥0∞
  | true => p
  | false => 1-p

noncomputable def coin (p : ℝ≥0) := (coinFun p).to_discrete_measure id

theorem coin_map_false (p : ℝ≥0) : (coin p).map not = coin (1-p) := by
  simp [coin]
  rw [Function.to_discrete_measure_map]
  ext s
  rw [to_discrete_measure_apply]
  rw [to_discrete_measure_apply]


  rw [← to_discrete_measure_eq_iff]




  refine Measure.ext_iff.mpr ?_
  intro s
  sorry


end coin

def coinFun (p : ℝ≥0) : Bool → ℝ≥0∞
  | true => p
  | false => 1-p

noncomputable def coin (p : ℝ≥0) := (coinFun p).to_discrete_measure

theorem to_discrete_measure [MeasurableSpace β] (f : α → ℝ≥0∞) (g : α → β) : f.to_discrete_measure.map g = sum (fun a ↦ f a • (dirac (g a))) := by
  sorry

theorem coin_map_false (p : ℝ≥0) : (coin p).map not = coin (1-p) := by
  refine Measure.ext_iff.mpr ?_
  intro s
  sorry



end PMFassumsofDiracs

/- PR #29959 ----------------------/
section Existence

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}

universe u v

lemma exists_hasLaw_indepFun {ι : Type v} (𝓧 : ι → Type u)
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} (μ : (i : ι) → Measure (𝓧 i))
    [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : (i : ι) → Ω → (𝓧 i),
      (∀ i, HasLaw (X i) (μ i) P) ∧ (iIndepFun X P) := by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i ↦ Function.eval i
  refine ⟨fun i ↦ MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _), ?_⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), map_id']
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi μ i).map_eq).symm

lemma exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ι → Ω → 𝓧,
      (∀ i, HasLaw (X i) μ P) ∧ (iIndepFun X P) :=
  exists_hasLaw_indepFun (fun _ ↦ 𝓧) (fun _ ↦ μ)

end Existence

section charFun

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

/- From CLT Project (not my code) -/
lemma charFun_map_sum_pi_const (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun ((Measure.pi fun (_ : Fin n) ↦ μ).map fun x ↦ ∑ i, x i) t = charFun μ t ^ n := by
  induction n with
  | zero => simp [Measure.map_const, charFun_apply]
  | succ n ih =>
    rw [pow_succ', ← ih, ← charFun_conv]
    congr 1
    have h := (measurePreserving_piFinSuccAbove (fun (_ : Fin (n + 1)) ↦ μ) 0).map_eq
    nth_rw 2 [← μ.map_id]
    rw [Measure.conv, Measure.map_prod_map, ← h, Measure.map_map, Measure.map_map]
    · congr 1 with x
      apply Fin.sum_univ_succ
    all_goals { fun_prop }

variable {Ω : Type*} (n : ℕ) {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Fin n → Ω → E}

/- Corollary -/
lemma ProbabilityTheory.iIndepFun.idd_charFun (hn : 1 ≤ n) {μ : Measure E}
    [hμ : IsProbabilityMeasure μ] (hX : ∀ i, HasLaw (X i) μ P) (hXindep : iIndepFun X P) (t : E) :
    charFun (P.map (∑ i, X i)) t = charFun μ t ^ n := by
  have : IsProbabilityMeasure P :=
    sorry --((hX ⟨0, hn⟩).isProbabilityMeasure_iff).mp hμ
  rw [← charFun_map_sum_pi_const]
  congr
  rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)] at hXindep
  conv in μ => rw [← (hX _).map_eq]
  rw [← hXindep, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  congr
  ext _
  simp

end charFun

/- Discrete Probability API -------/
section DiscreteMeasure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable {α : Type*} [mα : MeasurableSpace α]

variable {β : Type*} [mβ : MeasurableSpace β]

noncomputable def Function.to_discrete_measure (f : α → ℝ≥0∞) : Measure α :=
  sum (fun a ↦  f a • (dirac a))

lemma Function.to_discrete_measure_isProbabilityMeasure {f : α → ℝ≥0∞} (hf : HasSum f 1) :
    IsProbabilityMeasure f.to_discrete_measure :=
  ⟨by simp [Function.to_discrete_measure, hf.tsum_eq]⟩

-- Optimize Measurability Assumptions
lemma Function.to_discrete_measure_map_eq (f : α → ℝ≥0∞) {φ : α → β} (hφ : Measurable φ) :
    f.to_discrete_measure.map φ = sum (fun a ↦ f a • (dirac (φ a))) := by
  simp [Function.to_discrete_measure, MeasureTheory.Measure.map_sum hφ.aemeasurable,
    Measure.map_smul, map_dirac hφ]

section Fintype

variable {α : Type*} [Fintype α]

variable {E : Type*} [NormedAddCommGroup E]

-- Optimize Measurability Assumptions
theorem integrable_linear_combination_dirac_fintype [MeasurableSingletonClass β]
    (f : α → ℝ) (φ : α → β) {g : β → E}
    (hg : AEStronglyMeasurable g (sum (fun a ↦ (ENNReal.ofReal ∘ f) a • (dirac (φ a))))) :
    Integrable g (sum (fun a ↦ (ENNReal.ofReal ∘ f) a • (dirac (φ a)))) := by
  refine ⟨hg, ?_⟩
  simp [HasFiniteIntegral]
  finiteness

-- Optimize Measurability Assumptions
theorem integral_linear_combination_dirac_fintype [MeasurableSingletonClass β]
    [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → ℝ} (hf : 0 ≤ f) {φ : α → β} {g : β → E}
    (hg : AEStronglyMeasurable g (sum (fun a ↦ (ENNReal.ofReal ∘ f) a • (dirac (φ a))))) :
    ∫ b : β, g b ∂ sum (fun a ↦ (ENNReal.ofReal ∘ f) a • (dirac (φ a)))
    = ∑ a : α, f a • g (φ a) := by
  rw [integral_sum_measure (integrable_linear_combination_dirac_fintype f φ hg)]
  simp [tsum_fintype, fun x ↦ ENNReal.toReal_ofReal (hf x)]


end Fintype

end DiscreteMeasure

namespace ProbabilityTheory

section Bernoulli

/- Bernoulli Measure -/

def bernoulli_PMF_Real (p : ℝ) (i : Fin 2) : ℝ := if i = 1 then p else 1 - p

def bernoulli_PMF_Real_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ bernoulli_PMF_Real p :=
  fun i ↦ by fin_cases i <;> simpa [bernoulli_PMF_Real]

def bernoulli_PMF (p : ℝ) : (Fin 2) → ℝ≥0∞ := ENNReal.ofReal ∘ (bernoulli_PMF_Real p)

noncomputable def fin_bernoulli (p : ℝ) : Measure (Fin 2) :=
  (bernoulli_PMF p).to_discrete_measure

lemma HasSum_bernoulli_PMF_one {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
  HasSum (bernoulli_PMF p) 1 := by
  convert hasSum_fintype (bernoulli_PMF p)
  have : 1 = ENNReal.ofReal (1 - p) + ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add (by bound) hp₀]
    simp
  simp only [bernoulli_PMF]
  simp only [comp_apply, bernoulli_PMF_Real]
  simp [this]

theorem isProbabilityMeasure_fin_bernoulli {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (fin_bernoulli p) :=
  (bernoulli_PMF p).to_discrete_measure_isProbabilityMeasure (HasSum_bernoulli_PMF_one hp₀ hp₁)

noncomputable def real_bernoulli (p : ℝ) : Measure ℝ :=
  (fin_bernoulli p).map (↑)

theorem real_bernoulli_def (p : ℝ) :
    real_bernoulli p = sum (fun i ↦ (bernoulli_PMF p i) • dirac (i : ℝ)) := by
  unfold real_bernoulli fin_bernoulli
  rw [(bernoulli_PMF p).to_discrete_measure_map_eq (by fun_prop)]

theorem isProbabilityMeasure_real_bernoulli {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (real_bernoulli p) :=
  have := isProbabilityMeasure_fin_bernoulli hp₀ hp₁
  isProbabilityMeasure_map (by fun_prop (maxTransitionDepth := 2))

theorem real_bernoulli_charFun_eq {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (t : ℝ) :
    charFun (real_bernoulli p) t = (1 - p) + p * exp (t * I) := by
  rw [charFun_apply, real_bernoulli_def, bernoulli_PMF,
    integral_linear_combination_dirac_fintype (bernoulli_PMF_Real_nonneg hp₀ hp₁) (by fun_prop)]
  simp [bernoulli_PMF_Real]

/- Bernoulli Random Variables -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {p : ℝ}

theorem HasLaw.real_bernoulli_ae_zero_or_one (hX : HasLaw X (real_bernoulli p) P) :
    ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
  change P (X ⁻¹' {0, 1}ᶜ) = 0
  rw [← Measure.map_apply₀ hX.aemeasurable (by simp), hX.map_eq,
    ← lintegral_indicator_one (by measurability), real_bernoulli_def]
  simp

theorem HasLaw.real_bernoulli_memLp (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) (q : ℝ≥0∞) :
    MemLp X q P := by
  have : IsProbabilityMeasure P := by
    refine isProbabilityMeasure_iff.mpr ?_
    sorry
    --hX.isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
  apply MemLp.of_bound (by fun_prop (maxTransitionDepth := 2)) 1
  filter_upwards [hX.real_bernoulli_ae_zero_or_one] with ω
  rintro (h | h) <;> simp [h]

theorem HasLaw.real_bernoulli_integrable (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    Integrable X P :=
  memLp_one_iff_integrable.mp (hX.real_bernoulli_memLp hp₀ hp₁ 1)

theorem HasLaw.real_bernoulli_moment_eq_p (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hX : HasLaw X (real_bernoulli p) P) :
    moment X n P = p := by
  unfold moment
  conv in (X ^ n) => change (· ^ n) ∘ X
  rw [hX.integral_comp (by fun_prop), real_bernoulli_def, bernoulli_PMF,
    integral_linear_combination_dirac_fintype (bernoulli_PMF_Real_nonneg hp₀ hp₁) (by fun_prop)]
  simp [bernoulli_PMF_Real]
  grind

theorem HasLaw.real_bernoulli_mean (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    P[X] = p := by
    sorry
  -- rw [← ProbabilityTheory.moment_one, hX.real_bernoulli_moment_eq_p hp₀ hp₁ (by rfl)]

theorem HasLaw.real_bernoulli_variance (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    Var[X; P] = p * (1 - p) := by
  have : IsProbabilityMeasure P :=
    sorry -- hX.isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
  sorry
  -- rw [variance_eq_sub (hX.real_bernoulli_memLp hp₀ hp₁ 2), ← moment_def,
    -- hX.real_bernoulli_moment_eq_p hp₀ hp₁ (by bound), hX.real_bernoulli_mean hp₀ hp₁]
  -- ring

end Bernoulli

section Binomial

/- Binomial Measure -/

def binomial_PMF_Real (p : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  p ^ (i : ℕ) * (1 - p) ^ (n - i) * (n.choose i)

def binomial_PMF_Real_nonneg {p : ℝ} (n : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ binomial_PMF_Real p n := by
  intro x
  simp [binomial_PMF_Real]
  bound

def binomial_PMF (p : ℝ) (n : ℕ) : (Fin (n + 1)) → ℝ≥0∞ := ENNReal.ofReal ∘ (binomial_PMF_Real p n)

noncomputable def fin_binomial (p : ℝ) (n : ℕ) : Measure (Fin (n + 1)) :=
  (binomial_PMF p n).to_discrete_measure

lemma HasSum_binomial_PMF_one {p : ℝ} (n : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
  HasSum (binomial_PMF p n) 1 := by
  convert hasSum_fintype (binomial_PMF p n)
  simp only [binomial_PMF, binomial_PMF_Real, comp_apply]
  let f (x : ℕ) : ℝ := p ^ x * (1 - p) ^ (n - x) * ↑(n.choose x)
  rw [← ENNReal.ofReal_sum_of_nonneg (by bound), Fin.sum_univ_eq_sum_range (f := f), ← add_pow]
  simp

theorem isProbabilityMeasure_fin_binomial {p : ℝ} (n : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (fin_binomial p n) :=
  (binomial_PMF p n).to_discrete_measure_isProbabilityMeasure (HasSum_binomial_PMF_one n hp₀ hp₁)

noncomputable def real_binomial (p : ℝ) (n : ℕ) : Measure ℝ :=
  (fin_binomial p n).map (↑)

theorem real_binomial_def (p : ℝ) (n : ℕ) :
    real_binomial p n = sum (fun i ↦ (binomial_PMF p n i) • dirac (i : ℝ)) := by
  unfold real_binomial fin_binomial
  rw [(binomial_PMF p n).to_discrete_measure_map_eq (by fun_prop)]

theorem isProbabilityMeasure_real_binomial {p : ℝ} (n : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (real_binomial p n) :=
  have := isProbabilityMeasure_fin_binomial n hp₀ hp₁
  isProbabilityMeasure_map (by fun_prop (maxTransitionDepth := 2))

theorem real_binomial_charFun_eq {p : ℝ} (n : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (t : ℝ) :
    charFun (real_binomial p n) t = ((1 - p) + p * exp (t * I)) ^ n := by
  rw [charFun_apply, real_binomial_def, binomial_PMF,
    integral_linear_combination_dirac_fintype (binomial_PMF_Real_nonneg n hp₀ hp₁) (by fun_prop)]
  simp [binomial_PMF_Real, add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
  congr
  ext i
  rw [mul_pow, ← exp_nat_mul, ← mul_assoc, mul_comm (i : ℂ)]
  ring

/- Bernoulli Binomial Connection -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem bernoulli_eq_binomial_one {p : ℝ} :
    real_bernoulli p = real_binomial p 1 := by
  rw [real_bernoulli_def, real_binomial_def, bernoulli_PMF, binomial_PMF]
  congr; ext _; congr; ext i
  fin_cases i <;> simp [bernoulli_PMF_Real, binomial_PMF_Real]

theorem iIndepFun.sum_bernoulli {p : ℝ} {n : ℕ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hn : 1 ≤ n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (real_bernoulli p) P) (hXindep : iIndepFun X P) :
    HasLaw (∑ i, X i) (real_binomial p n) P where
  map_eq := by
    have := isProbabilityMeasure_real_bernoulli hp₀ hp₁
    have := isProbabilityMeasure_real_binomial n hp₀ hp₁
    have : IsProbabilityMeasure P :=
      sorry
      -- (hX ⟨0, hn⟩).isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
    apply Measure.ext_of_charFun
    ext t
    rw [hXindep.idd_charFun n hn hX, real_bernoulli_charFun_eq hp₀ hp₁ t,
      real_binomial_charFun_eq n hp₀ hp₁ t]

theorem HasLaw.binomial_integral {p : ℝ} {n : ℕ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hn : 1 ≤ n)
    {X : Ω → ℝ} (hX : HasLaw X (real_binomial p n) P) : P[X] = n * p := by
  have := isProbabilityMeasure_real_bernoulli hp₀ hp₁
  obtain ⟨Ω, _, P, Y, hY, hIndep⟩ := exists_iid (Fin n) (real_bernoulli p)
  rw [hX.integral_eq, ← (hIndep.sum_bernoulli hp₀ hp₁ hn hY).integral_eq]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum _ (fun i _ ↦ (hY i).real_bernoulli_integrable hp₀ hp₁)]
  conv => enter [1, 2, i]; rw [(hY i).real_bernoulli_mean hp₀ hp₁]
  simp

end Binomial

end ProbabilityTheory


variable {p : ℝ}

def not' : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

example : (fin_bernoulli p).map not' = (fin_bernoulli (1 - p)) := by
  simp [fin_bernoulli, to_discrete_measure, bernoulli_PMF, bernoulli_PMF_Real]
  rw [Measure.map_add _ _ (by fun_prop)]
  repeat rw [Measure.map_smul]
  repeat rw [Measure.map_dirac (by fun_prop)]
  simp [not', add_comm]
