import Mathlib

open MeasureTheory ProbabilityTheory Measure Function Complex

open scoped ENNReal NNReal

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
    ((hX ⟨0, hn⟩).isProbabilityMeasure_iff).mp hμ
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
    simp only [sub_add_cancel, ENNReal.ofReal_one]
  simp only [bernoulli_PMF]
  simp only [this, comp_apply, bernoulli_PMF_Real, Fin.isValue, Fin.sum_univ_two, zero_ne_one,
    ↓reduceIte]

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
  have : IsProbabilityMeasure P :=
    hX.isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
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
  rw [← moment_one, hX.real_bernoulli_moment_eq_p hp₀ hp₁ (by rfl)]

theorem HasLaw.real_bernoulli_variance (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    Var[X; P] = p * (1 - p) := by
  have : IsProbabilityMeasure P :=
    hX.isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
  rw [variance_eq_sub (hX.real_bernoulli_memLp hp₀ hp₁ 2), ← moment_def,
    hX.real_bernoulli_moment_eq_p hp₀ hp₁ (by bound), hX.real_bernoulli_mean hp₀ hp₁]
  ring

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
      (hX ⟨0, hn⟩).isProbabilityMeasure_iff.mp (isProbabilityMeasure_real_bernoulli hp₀ hp₁)
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


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}  (hX : HasLaw X (real_bernoulli p) P)

example : HasLaw (1 - X) (real_bernoulli (1 - p)) P where
  map_eq := by
    rw [Measure.ext_iff_lintegral]
    intro f hf
    rw [lintegral_map' (by fun_prop) (by fun_prop)]
    conv => enter [1, 2, a]; change (f ∘ (fun x ↦ 1 - x)) (X a)
    rw [hX.lintegral_comp (by fun_prop)]
    simp [real_bernoulli_def, bernoulli_PMF, bernoulli_PMF_Real, add_comm]
