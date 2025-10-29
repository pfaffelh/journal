import Mathlib

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

section PMFassumsofDiracs

variable {α β γ : Type*}

example (s : Set β) (b : β): MeasurableSet[(OuterMeasure.dirac b).caratheodory] s := by
  simp only [OuterMeasure.dirac_caratheodory, MeasurableSpace.measurableSet_top]

instance topMeasurableSpace : MeasurableSpace β := ⊤

-- Given `f : α → ℝ≥0∞` and `g : α → β`, this is the measure (on `⊤`, i.e. the power set of `β`),
-- which adds mass `f a` to `g a`.
noncomputable def Function.to_discrete_measure (f : α → ℝ≥0∞) (g : α → β) : @Measure β ⊤ :=
  sum (fun a ↦ f a • (OuterMeasure.dirac (g a)).toMeasure
    ((OuterMeasure.dirac_caratheodory (g a)).symm ▸ le_top))

noncomputable def Function.to_discrete_measure_ofReal (f : α → ℝ) (g : α → β): @Measure β ⊤ :=
  Function.to_discrete_measure (ENNReal.ofReal ∘ f) g

lemma to_discrete_measure_apply' (f : α → ℝ≥0∞) (g : α → β) (s : Set β) : f.to_discrete_measure g s =
    ∑' a, (f a) * s.indicator (fun _ ↦ 1) (g a) := by
  simp only [to_discrete_measure, MeasurableSpace.measurableSet_top, sum_apply, smul_apply,
    toMeasure_apply, OuterMeasure.dirac_apply, smul_eq_mul]

lemma indicator_eq (f : α → ℝ≥0∞) (s : Set α) : f a * s.indicator 1 a = s.indicator f a := by
  simp [Set.indicator]

lemma indicator_eq' (f : α → ℝ≥0∞) (g : α → β) (s : Set β) : f a * s.indicator (fun _ ↦ 1) (g a) = (g⁻¹' s).indicator f a := by
  simp [Set.indicator]
  rfl

lemma to_discrete_measure_apply'' (f : α → ℝ≥0∞) (g : α → β) (s : Set β) : f.to_discrete_measure g s =
    ∑' (a : g⁻¹' s), (f a) := by
  rw [to_discrete_measure_apply']
  simp [tsum_subtype]
  apply tsum_congr
  intro b
  rw [indicator_eq' f g s]

lemma to_discrete_measure_apply (f : α → ℝ≥0∞) (g : α → β) (s : Set β) :
    f.to_discrete_measure g s = ∑' a, (f a) * s.indicator 1 (g a) := by
  rw [to_discrete_measure_apply']
  rfl

lemma to_discrete_measure_ofReal_apply (f : α → ℝ) (g : α → β) (s : Set β) :
    f.to_discrete_measure_ofReal g s = ∑' a, (ENNReal.ofReal (f a)) * s.indicator (fun _ ↦ 1) (g a) := by
  rw [to_discrete_measure_ofReal]
  exact to_discrete_measure_apply (ENNReal.ofReal ∘ f) g s

lemma to_discrete_measure_apply_id (f : α → ℝ≥0∞) (s : Set α) : f.to_discrete_measure id s = ∑' a, s.indicator f a := by
  rw [to_discrete_measure_apply]
  exact tsum_congr (fun _ ↦ indicator_eq f s)

lemma to_discrete_measure_apply_id_singleton (f : α → ℝ≥0∞) (u : α) :
    f.to_discrete_measure id {u} = f u := by
  rw [to_discrete_measure_apply_id, ← tsum_subtype, tsum_singleton]

theorem to_discrete_measure_eq_iff {f₁ f₂ : α → ℝ≥0∞} : f₁ = f₂ ↔
    f₁.to_discrete_measure id = f₂.to_discrete_measure id := by
  refine ⟨fun h ↦ by rw [h], ?_⟩
  rw [← not_imp_not]
  intro h
  change f₁ ≠ f₂ at h
  rw [ne_iff] at h
  obtain ⟨a, ha⟩ := h
  change _ ≠ _
  rw [DFunLike.ne_iff]
  use {a}
  simp [to_discrete_measure_apply_id_singleton, ha]

lemma indicator_tsum (s : Set β) (f : β → ℝ≥0∞) (x : β) : (s.indicator f x) = ∑' (a : s), ({ a.val } : Set β).indicator f x := by
  simp [Set.indicator]

  sorry

example (f : α → ℝ≥0∞): x * ∑' y, f y = ∑' y, x * f y := by
  exact Eq.symm ENNReal.tsum_mul_left

theorem to_discrete_measure_eq_tsum {f : α → ℝ≥0∞} (g : α → β) (s : Set β) :
    f.to_discrete_measure g s = ∑' (b : s), f.to_discrete_measure g ({ b.val } : Set β) := by
  rw [to_discrete_measure_apply'']
  simp_rw [to_discrete_measure_apply'']



  rw [tsum_subtype]
  simp_rw [tsum_subtype]

  conv => left; left; simp [indicator_tsum s (fun _ ↦ 1)]

  sorry

theorem to_discrete_measure_eq_iff' {f₁ f₂ : α → ℝ≥0∞} (g₁ g₂ : α → β) : (∀ b : β,  f₁.to_discrete_measure g₁ {b} = f₂.to_discrete_measure g₂ {b}) ↔
    f₁.to_discrete_measure g₁ = f₂.to_discrete_measure g₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext s
    rw [to_discrete_measure_eq_tsum]
    rw [to_discrete_measure_eq_tsum]
    apply tsum_congr
    intro b
    apply h b.val
  · rw [DFunLike.ext_iff] at h
    intro b
    exact h {b}


theorem to_discrete_measure_eq_iff'' {f₁ f₂ : α → ℝ≥0∞} (g₁ g₂ : α → β) : (∀ b : β, ∑' a : g₁⁻¹' {b}, f₁ a = ∑' a : g₂⁻¹' {b}, f₂ a) ↔
    f₁.to_discrete_measure g₁ = f₂.to_discrete_measure g₂ := by
  rw [← to_discrete_measure_eq_iff']
  refine ⟨fun h b ↦ ?_, fun h b ↦ ?_⟩
  ·
    sorry
  · sorry

theorem Function.to_discrete_measure_map (f : α → ℝ≥0∞) (g : α → β) (h : β → γ) :
    (f.to_discrete_measure g).map h = f.to_discrete_measure (h ∘ g) := by
  ext s
  rw [map_apply (by fun_prop) (by measurability)]
  rw [to_discrete_measure_apply']
  rw [to_discrete_measure_apply']
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
