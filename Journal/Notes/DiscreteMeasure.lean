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

noncomputable def toMeasure (μ : DiscreteMeasure α) : @Measure α ⊤ := discreteMeasure μ.weight

noncomputable instance : Coe (DiscreteMeasure α) (@Measure α ⊤) where
  coe μ : @Measure α ⊤ := μ.toMeasure

noncomputable instance :
  CoeFun (DiscreteMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := μ.toMeasure

@[simp]
lemma toMeasure_apply (μ : DiscreteMeasure α) (s : Set α) : μ.toMeasure s = μ s := by
  rfl

@[simp]
lemma coe_apply (μ : DiscreteMeasure α) (s : Set α) : (μ : @Measure α ⊤) s = μ s := rfl

@[simp]
lemma apply (μ : DiscreteMeasure α) (s : Set α) : μ s = discreteMeasure μ.weight s := by
  rfl

example (μ : DiscreteMeasure α) : μ = sum fun (a : α) ↦ (μ.weight a) • (@dirac α ⊤ a) := by
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

@[simp]
lemma apply_univ (μ : DiscreteMeasure α) : μ Set.univ = ∑' (a : α), μ.weight a := by
  simp only [apply, discreteMeasure_apply, Set.indicator.mul_indicator_eq']
  simp_rw [Set.indicator_univ]
section map

noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : (DiscreteMeasure β) := ⟨fun b ↦ μ (g⁻¹' {b})⟩

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

lemma join_apply_eq_toMeasure (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) : m.join s = (m.toMeasure.map toMeasure).join s := by
  rw [Measure.join_apply (mα := ⊤) (hs := by measurability)]
  rw [lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [← lintegral_eq_toMeasure, apply₂]
  simp_rw [join_weight, lintegral]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left]
  congr
  rw [m_iUnion_set_singleton]

lemma join_toMeasure (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = (m.toMeasure.map toMeasure).join := by
  ext s
  rw [join_apply_eq_toMeasure]

@[simp]
lemma join_toMeasure' (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m.weight μ • μ.toMeasure) := by
  ext s hs
  rw [join_apply_eq_toMeasure, toMeasure, discreteMeasure, Measure.map_sum (hf := AEMeasurable.of_discrete), Measure.join_sum, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
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

end join

section bind

noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := (μ.map g).join

lemma bind_apply_eq_toMeasure (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : μ.bind g s = μ.toMeasure.bind (toMeasure ∘ g) s := by
  rw [bind, Measure.bind]
  rw [join_apply_eq_toMeasure]
  rw [← Measure.map_map (hg := by measurability) (hf := by measurability)]
  rw [map_toMeasure]

lemma bind_toMeasure (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  ext s
  rw [bind_apply_eq_toMeasure]

lemma bind_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : μ.bind g s = sum (fun a ↦ μ.weight a • (g a).toMeasure) s := by
  rw [bind_apply_eq_toMeasure, toMeasure, discreteMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete)]
  rw [Measure.sum_apply (hs := by measurability)]
  rw [Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun b ↦ ?_)
  rw [Measure.bind_smul]
  rw [Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_apply' (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (s : Set β) : μ.bind g s = ∑' (a : α), μ {a} * (g a) s := by
  rw [bind_apply, Measure.sum_apply (hs := by measurability)]
  simp_rw [apply_singleton, Measure.smul_apply]
  rfl

@[simp]
lemma bind_weight (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g).weight x = ∑' (a : α), μ {a} * (g a) {x} := by
  rw [← apply_singleton, bind_apply']

end bind

section coin

open Bool ENNReal

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


def DiscreteProbabilityMeasure (α : Type*) : Type _ :=
  { μ : DiscreteMeasure α // IsProbabilityMeasure μ.toMeasure }

lemma isProbabilityMeasure_iff (μ : DiscreteMeasure α) : IsProbabilityMeasure μ.toMeasure ↔ HasSum μ.weight 1 := by
  rw [MeasureTheory.isProbabilityMeasure_iff, DiscreteMeasure.apply_univ, Summable.hasSum_iff ENNReal.summable]

namespace DiscreteProbabilityMeasure

/-- Coercion from `MeasureTheory.DiscreteProbabilityMeasure α` to `MeasureTheory.DiscreteMeasure α`. -/
@[coe]
def toMeasure : DiscreteProbabilityMeasure α → DiscreteMeasure α := Subtype.val

/-- A discrete probability measure can be interpreted as a discrete measure. -/
instance : Coe (DiscreteProbabilityMeasure α) (DiscreteMeasure α) := { coe := toMeasure }

instance (μ : DiscreteProbabilityMeasure α) : IsProbabilityMeasure (μ : Measure α) :=
  μ.prop

noncomputable def toProbabilityMeasure (μ : DiscreteProbabilityMeasure α) : @ProbabilityMeasure α ⊤ := ⟨μ.val, μ.prop⟩

def ofDiscreteMeasure (μ : DiscreteMeasure α) (hμ : IsProbabilityMeasure μ.toMeasure) : DiscreteProbabilityMeasure α := ⟨μ, hμ⟩

lemma apply (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ.val s = ∑' (i : α), (μ.val.weight i : ℝ≥0∞) * s.indicator 1 i := μ.val.apply s ▸ discreteMeasure_apply μ.val.weight s



end DiscreteProbabilityMeasure

lemma hasSum_iff (f : α → ℝ≥0) (hf : HasSum f 1) : HasSum (ENNReal.ofNNReal ∘ f) (ENNReal.ofNNReal (1 : ℝ≥0)) := by
  change HasSum (fun a ↦ ENNReal.ofNNReal (f a)) (ENNReal.ofNNReal 1)
  rw [ENNReal.hasSum_coe]
  exact hf

@[simp] lemma tsum_ofNNReal (f : α → ℝ≥0) :
    ∑' a, (ENNReal.ofNNReal (f a)) = ∑' a, (f a : ℝ≥0∞) := by
  -- Diese ist einfach definitorisch:
  simp

@[simp]
lemma hasSum_ofNNReal {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a ↦ ENNReal.ofNNReal (f a)) (ENNReal.ofNNReal r) ↔
    HasSum (fun a ↦ (f a : ℝ≥0∞)) (r : ℝ≥0∞) := by
  -- beide Seiten sind definitionell gleich
  rfl






noncomputable def discreteProbabilityMeasure (p : { p : α → ℝ≥0 // HasSum p 1}) : @ProbabilityMeasure α ⊤ := ⟨discreteMeasure (ENNReal.ofNNReal ∘ p.val), by
  rw [isProbabilityMeasure_iff]
  rw [discreteMeasure_apply_univ]
  apply ENNReal.tsum_coe_eq p.prop
⟩

noncomputable def to_discreteMeasure (P : discreteProbabilityMeasure α) : DiscreteMeasure α :=
⟨fun (a : α) ↦ ↑(p.val a)⟩

lemma apply_eq

lemma l1 (x : ℝ≥0∞) (y: ℝ≥0) (hx : x ≠ ⊤) : x.toNNReal = y ↔ x = ENNReal.ofNNReal y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact Eq.symm (ENNReal.coe_toNNReal hx)
  · rw [h]
    exact rfl

lemma l2 (x : α → ℝ≥0∞) (y : α → ℝ≥0) (hy : Summable y) (h : ∀ a, (x a).toNNReal = y a) : ∑' a, x a = ∑' a, ENNReal.ofNNReal (y a) := by
  have h₀ : Summable (ENNReal.toNNReal ∘ x) := by sorry
  simp_rw [← h]
  apply tsum_congr (fun b ↦ ?_)

  apply?

  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact Eq.symm (ENNReal.coe_toNNReal hx)
  · rw [h]
    exact rfl



example (x y : α → ℝ≥0) (hxy : ∀ a, x a ≤ y a) (h : Summable y) : Summable x := by
  exact NNReal.summable_of_le hxy h

lemma discreteProbabilityMeasure_eq (p : { p : α → ℝ≥0 // HasSum p 1}) (s : Set α) :
    (discreteProbabilityMeasure p : Measure α) = discreteMeasure (toENNReal ∘ p.val) := by

  ext s
  simp

  sorry

@[simp]
lemma discreteProbabilityMeasure_apply (p : { p : α → ℝ≥0 // HasSum p 1}) (s : Set α) :
    discreteProbabilityMeasure p s = ∑' (i : α), (p.val i : ℝ≥0∞) * s.indicator 1 i := by
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  sorry

lemma discreteProbabilityMeasure_apply' (p : { p : α → ℝ≥0 // HasSum p 1}) (s : Set α) :
    discreteProbabilityMeasure p s = ∑' (i : α), p.val i * s.indicator 1 i := by
  classical
  simp [discreteProbabilityMeasure]
  have h₃ : HasSum p.val 1 := p.prop
  have h₂ : Summable p.val := by
      apply HasSum.summable p.prop
  have h₀ : Summable fun i => p.val i * s.indicator 1 i := by
    apply NNReal.summable_of_le _ h₂
    intro b
    nth_rw 2 [← mul_one (p.val b)]
    refine mul_le_mul' (by rfl) ?_
    rw [Set.indicator]
    apply ite_le_one
    rfl
    exact zero_le_one' ℝ≥0
  rw [l1]
  rw [ENNReal.coe_tsum h₀]
  apply tsum_congr (fun i ↦ ?_)
  simp
  rfl
  apply?
  apply ENNReal.summable_toNNReal_of_tsum_ne_top


  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  have h₄ : ∀ i, ENNReal.ofNNReal (p.val i) * s.indicator 1 i ≤ ENNReal.ofNNReal (p.val i) := by
    sorry

  apply?

  apply NNReal.tsum_mono
  sorry
  sorry











    apply?
    sorry


    sorry
  rw [h₁]
  apply tsum_congr (fun i ↦ ?_)
  simp only [ENNReal.coe_mul, ENNReal.coe_indicator, Pi.one_apply, ENNReal.coe_one]
  rfl
  sorry

namespace DiscreteProbabilityMeasure

noncomputable def toProbabilityMeasure (μ : DiscreteProbabilityMeasure α) : @ProbabilityMeasure α ⊤ :=
  ⟨discreteMeasure μ.weight, by
    rw [isProbabilityMeasure_iff]
    rw [discreteMeasure_apply_univ]
    rw [← Summable.hasSum_iff ENNReal.summable]
    exact μ.sum_weight⟩

noncomputable instance : Coe (DiscreteProbabilityMeasure α) (@ProbabilityMeasure α ⊤) where
  coe μ : @ProbabilityMeasure α ⊤ := μ.toProbabilityMeasure

noncomputable instance :
  CoeFun (DiscreteProbabilityMeasure α) (fun _ => Set α → ℝ≥0∞) where
  coe μ := fun s ↦ μ.toProbabilityMeasure s

-- not a coercion, but using this we can use code from DiscreteMeasure
noncomputable def toDiscreteMeasure
  (μ : DiscreteProbabilityMeasure α) : DiscreteMeasure α := ⟨μ.weight⟩

@[simp]
lemma toProbabilityMeasure_apply (P : DiscreteProbabilityMeasure α) (s : Set α) : P.toProbabilityMeasure s = P s := by
  rfl

@[simp]
lemma coe_apply (P : DiscreteProbabilityMeasure α) (s : Set α) : (P : @ProbabilityMeasure α ⊤) s = P s := rfl

@[simp]
lemma apply (P : DiscreteProbabilityMeasure α) (s : Set α) : P s = discreteProbabilityMeasure ⟨P.weight, P.sum_weight⟩ s := by
  rfl

lemma apply₀ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (i : α), μ.weight i * s.indicator 1 i := by

  simp?

lemma apply₁ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (i : α), s.indicator μ.weight i := by
  rw [apply₀]
  simp

lemma apply₂ (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s =
    ∑' (a : s), (μ.weight a) := by
  simp [tsum_subtype]

@[simp]
lemma apply_singleton (μ : DiscreteProbabilityMeasure α) (a : α) : μ {a} =
    μ.weight a := by
  rw [apply₂]
  simp only [tsum_singleton]

/- Additivity for a `DiscreteProbabilityMeasure` not only applies to countable unions, but to arbitrary ones.-/
lemma m_iUnion (μ : DiscreteProbabilityMeasure α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) : μ (⋃ d, s d) = ∑' (d : δ), μ (s d) := by
  simp only [apply, discreteProbabilityMeasure_apply, Set.indicator.mul_indicator_eq']
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

lemma singleton_eq_weight (μ : DiscreteProbabilityMeasure α) : (fun (a : α) ↦ μ {a}) = μ.weight := by
  ext a
  rw [apply_singleton]

lemma m_iUnion_set_singleton (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (a : s), μ {a.val} := by
  simp_rw [apply_singleton, apply₂]

lemma m_iUnion_singleton (μ : DiscreteProbabilityMeasure α) (s : Set α) : μ s = ∑' (x : s), μ {x.val} := by
  nth_rw 1 [← Set.iUnion_of_singleton_coe s]
  exact m_iUnion μ _ (pairwise_disjoint_singleton_subtype s)

lemma ext_weight {μ₁ μ₂ : DiscreteProbabilityMeasure α}
  (h : μ₁.weight = μ₂.weight) : μ₁ = μ₂ :=
by
  cases μ₁
  simp only at h
  rw [h]

@[ext]
lemma ext {μ₁ μ₂ : DiscreteProbabilityMeasure α}
    (h : ∀ a, μ₁ {a} = μ₂ {a}) : μ₁ = μ₂ :=by
  apply ext_weight
  rw [← singleton_eq_weight, ← singleton_eq_weight]
  ext a
  exact h a

lemma toMeasure_ext' {μ₁ μ₂ : DiscreteProbabilityMeasure α} (h : μ₁.toMeasure = μ₂.toMeasure) : μ₁ = μ₂ :=
by
  apply ext_weight
  rw [← singleton_eq_weight, ← singleton_eq_weight]
  simp [h]

end DiscreteProbabilityMeasure

end DiscreteProbabilityMeasure
