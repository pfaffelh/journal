/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The stopped martingale theorem in continuous time

Scratch development for `TauCeti/MartingaleProblems/Suggested.lean`.
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

namespace TauCeti

/-! ### Dyadic rounding on the real line -/

/-- The dyadic ceiling of level `n`. -/
noncomputable def dyadCeil (n : ℕ) (s : ℝ) : ℝ := ((⌈s * 2 ^ n⌉ : ℤ) : ℝ) / 2 ^ n

/-- The dyadic floor of level `n`. -/
noncomputable def dyadFloor (n : ℕ) (s : ℝ) : ℝ := ((⌊s * 2 ^ n⌋ : ℤ) : ℝ) / 2 ^ n

theorem le_dyadCeil (n : ℕ) (s : ℝ) : s ≤ dyadCeil n s := by
  rw [dyadCeil, le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  exact Int.le_ceil _

theorem dyadCeil_le_add (n : ℕ) (s : ℝ) : dyadCeil n s ≤ s + (2 : ℝ)⁻¹ ^ n := by
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have h2 : ((2 : ℝ)⁻¹) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [dyadCeil, div_le_iff₀ hpow]
  have h1 : ((⌈s * 2 ^ n⌉ : ℤ) : ℝ) < s * 2 ^ n + 1 := Int.ceil_lt_add_one _
  nlinarith [h1, h2]

theorem dyadFloor_le (n : ℕ) (s : ℝ) : dyadFloor n s ≤ s := by
  rw [dyadFloor, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  exact Int.floor_le _

theorem dyadFloor_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ dyadFloor n s := by
  have : (0:ℤ) ≤ ⌊s * 2 ^ n⌋ := Int.floor_nonneg.2 (by positivity)
  rw [dyadFloor]
  positivity

theorem dyadCeil_le_iff (n : ℕ) (s t : ℝ) : dyadCeil n s ≤ t ↔ s ≤ dyadFloor n t := by
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  rw [dyadCeil, dyadFloor, div_le_iff₀ hpow, le_div_iff₀ hpow]
  constructor
  · intro h
    have h1 : ⌈s * 2 ^ n⌉ ≤ ⌊t * 2 ^ n⌋ := Int.le_floor.2 h
    exact (Int.le_ceil _).trans (by exact_mod_cast h1)
  · intro h
    have h1 : ⌈s * 2 ^ n⌉ ≤ ⌊t * 2 ^ n⌋ := Int.ceil_le.2 h
    calc ((⌈s * 2 ^ n⌉ : ℤ) : ℝ) ≤ ((⌊t * 2 ^ n⌋ : ℤ) : ℝ) := by exact_mod_cast h1
      _ ≤ t * 2 ^ n := Int.floor_le _

theorem countable_range_dyadCeil (n : ℕ) : (Set.range (dyadCeil n)).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range fun k : ℤ ↦ ((k : ℝ) / 2 ^ n))
  rintro _ ⟨s, rfl⟩
  exact ⟨⌈s * 2 ^ n⌉, rfl⟩

/-! ### The dyadic approximation from above of a bounded stopping time -/

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The dyadic approximation from above, at level `n`, of a stopping time capped at `j`. -/
noncomputable def dyadStop (j : ℝ≥0) (ρ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ((min j (Real.toNNReal (dyadCeil n (ρ ω).toReal)) : ℝ≥0) : ℝ≥0∞)

theorem dyadStop_le (j : ℝ≥0) (ρ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    dyadStop j ρ n ω ≤ (j : ℝ≥0∞) :=
  ENNReal.coe_le_coe.2 (min_le_left _ _)

theorem le_dyadStop {j : ℝ≥0} {ρ : Ω → ℝ≥0∞} (hρj : ∀ ω, ρ ω ≤ (j : ℝ≥0∞)) (n : ℕ) (ω : Ω) :
    ρ ω ≤ dyadStop j ρ n ω := by
  have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hρj ω)
  have hcoe : ((ρ ω).toNNReal : ℝ≥0∞) = ρ ω := ENNReal.coe_toNNReal hne
  have h1 : (ρ ω).toNNReal ≤ j := by
    rw [← ENNReal.coe_le_coe, hcoe]; exact hρj ω
  have h2 : (ρ ω).toNNReal ≤ Real.toNNReal (dyadCeil n (ρ ω).toReal) := by
    have : (ρ ω).toNNReal = Real.toNNReal (ρ ω).toReal := by
      simp [ENNReal.toReal, Real.toNNReal_coe]
    rw [this]
    exact Real.toNNReal_le_toNNReal (le_dyadCeil n _)
  rw [dyadStop, ← hcoe, ENNReal.coe_le_coe]
  exact le_min h1 h2

theorem countable_range_dyadStop (j : ℝ≥0) (ρ : Ω → ℝ≥0∞) (n : ℕ) :
    (Set.range (dyadStop j ρ n)).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range fun k : ℤ ↦
    ((min j (Real.toNNReal (((k : ℝ)) / 2 ^ n)) : ℝ≥0) : ℝ≥0∞))
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈(ρ ω).toReal * 2 ^ n⌉, rfl⟩

theorem isStoppingTime_dyadStop {𝓕 : Filtration ℝ≥0 m} {ρ : Ω → ℝ≥0∞}
    (hρ : IsStoppingTime 𝓕 ρ) {j : ℝ≥0} (hρj : ∀ ω, ρ ω ≤ (j : ℝ≥0∞)) (n : ℕ) :
    IsStoppingTime 𝓕 (dyadStop j ρ n) := by
  intro t
  show MeasurableSet[𝓕 t] {ω | dyadStop j ρ n ω ≤ (t : ℝ≥0∞)}
  rcases le_or_gt j t with hjt | htj
  · have hset : {ω | dyadStop j ρ n ω ≤ (t : ℝ≥0∞)} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (dyadStop_le j ρ n ω).trans (by exact_mod_cast hjt)
    rw [hset]
    exact MeasurableSet.univ
  · set c : ℝ≥0 := Real.toNNReal (dyadFloor n (t : ℝ)) with hc
    have hct : c ≤ t := Real.toNNReal_le_iff_le_coe.2 (dyadFloor_le n _)
    have hset : {ω | dyadStop j ρ n ω ≤ (t : ℝ≥0∞)} = {ω | ρ ω ≤ (c : ℝ≥0∞)} := by
      ext ω
      have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hρj ω)
      simp only [Set.mem_ofPred_eq, dyadStop, ENNReal.coe_le_coe]
      rw [min_le_iff]
      have hj : ¬ (j ≤ t) := not_le.2 htj
      rw [or_iff_right hj, Real.toNNReal_le_iff_le_coe, dyadCeil_le_iff]
      rw [show ((c : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (dyadFloor n (t : ℝ)) from rfl,
        ENNReal.le_ofReal_iff_toReal_le hne (dyadFloor_nonneg t.coe_nonneg n)]
    rw [hset]
    exact 𝓕.mono hct _ (hρ c)

theorem tendsto_dyadStop {j : ℝ≥0} {ρ : Ω → ℝ≥0∞} (hρj : ∀ ω, ρ ω ≤ (j : ℝ≥0∞)) (ω : Ω) :
    Tendsto (fun n ↦ (dyadStop j ρ n ω).toNNReal) atTop (𝓝[≥] (ρ ω).toNNReal) := by
  set r : ℝ≥0 := (ρ ω).toNNReal with hr
  have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hρj ω)
  have hrs : ((r : ℝ)) = (ρ ω).toReal := rfl
  have hval : ∀ n, (dyadStop j ρ n ω).toNNReal
      = min j (Real.toNNReal (dyadCeil n (r : ℝ))) := fun n ↦ by
    rw [dyadStop, ENNReal.toNNReal_coe, hrs]
  have hlow : ∀ n, r ≤ (dyadStop j ρ n ω).toNNReal := fun n ↦ by
    have h := ENNReal.toNNReal_mono (b := dyadStop j ρ n ω) (by simp [dyadStop])
      (le_dyadStop hρj n ω)
    rwa [hr]
  have hup : ∀ n, (dyadStop j ρ n ω).toNNReal ≤ r + Real.toNNReal ((2 : ℝ)⁻¹ ^ n) := fun n ↦ by
    rw [hval n]
    refine (min_le_right _ _).trans ?_
    have h1 : Real.toNNReal (dyadCeil n (r : ℝ))
        ≤ Real.toNNReal ((r : ℝ) + (2 : ℝ)⁻¹ ^ n) :=
      Real.toNNReal_le_toNNReal (dyadCeil_le_add n _)
    refine h1.trans ?_
    rw [Real.toNNReal_add r.coe_nonneg (by positivity), Real.toNNReal_coe]
  have hc : Tendsto (fun n : ℕ ↦ Real.toNNReal ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h0 : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simp only [NNReal.coe_zero]
    refine h0.congr fun n ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall hlow)
  have hsum : Tendsto (fun n : ℕ ↦ r + Real.toNNReal ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 (r + 0)) :=
    tendsto_const_nhds.add hc
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum hlow hup

/-! ### The optional sampling identity for a bounded stopping time -/

theorem untopA_eq_toNNReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : x.untopA = x.toNNReal := by
  lift x to ℝ≥0 using hx
  rfl

variable {𝓕 : Filtration ℝ≥0 m} {P : Measure Ω} [IsFiniteMeasure P] {Y : ℝ≥0 → Ω → ℝ}

/-- **The expectation of a martingale at a bounded stopping time of countable range.** -/
theorem integral_stoppedValue_eq_of_countable_range (hY : Martingale Y 𝓕 P)
    {σ : Ω → ℝ≥0∞} (hσ : IsStoppingTime 𝓕 σ) {j : ℝ≥0} (hσj : ∀ ω, σ ω ≤ (j : ℝ≥0∞))
    (hcount : (Set.range σ).Countable) :
    ∫ ω, stoppedValue Y σ ω ∂P = ∫ ω, Y j ω ∂P := by
  have h := hY.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hσ hσj hcount
  rw [integral_congr_ae h, integral_condExp (hσ.measurableSpace_le_of_le hσj)]

/-- **The expectation of a bounded right continuous martingale at a bounded stopping time.** -/
theorem integral_stoppedValue_eq (hY : Martingale Y 𝓕 P) (hprog : IsStronglyProgressive 𝓕 Y)
    (hrc : ∀ (ω : Ω) (s : ℝ≥0), Tendsto (fun r ↦ Y r ω) (𝓝[≥] s) (𝓝 (Y s ω)))
    {j : ℝ≥0} {C : ℝ} (hbdd : ∀ s ≤ j, ∀ ω, |Y s ω| ≤ C)
    {ρ : Ω → ℝ≥0∞} (hρ : IsStoppingTime 𝓕 ρ) (hρj : ∀ ω, ρ ω ≤ (j : ℝ≥0∞)) :
    ∫ ω, stoppedValue Y ρ ω ∂P = ∫ ω, Y j ω ∂P := by
  set F : ℕ → Ω → ℝ := fun n ↦ stoppedValue Y (dyadStop j ρ n) with hF
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) P := fun n ↦
    ((stronglyMeasurable_stoppedValue_of_le hprog (isStoppingTime_dyadStop hρ hρj n)
      (dyadStop_le j ρ n)).mono (𝓕.le j)).aestronglyMeasurable
  have hne' : ∀ (n : ℕ) (ω : Ω), dyadStop j ρ n ω ≠ ⊤ := fun n ω ↦ by
    rw [dyadStop]; exact ENNReal.coe_ne_top
  have hFbd : ∀ n ω, ‖F n ω‖ ≤ C := fun n ω ↦ by
    have h1 : (dyadStop j ρ n ω).untopA ≤ j := by
      rw [untopA_eq_toNNReal (hne' n ω), dyadStop, ENNReal.toNNReal_coe]
      exact min_le_left _ _
    simpa [hF, stoppedValue, Real.norm_eq_abs] using hbdd _ h1 ω
  have hlim : ∀ ω, Tendsto (fun n ↦ F n ω) atTop (𝓝 (stoppedValue Y ρ ω)) := fun ω ↦ by
    have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hρj ω)
    have hh : ∀ n, F n ω = Y ((dyadStop j ρ n ω).toNNReal) ω := fun n ↦ by
      rw [hF]
      simp only [stoppedValue]
      rw [untopA_eq_toNNReal (hne' n ω)]
    simp only [hh, stoppedValue, untopA_eq_toNNReal hne]
    exact (hrc ω (ρ ω).toNNReal).comp (tendsto_dyadStop hρj ω)
  have hconv : Tendsto (fun n ↦ ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, stoppedValue Y ρ ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ C) hFmeas (integrable_const C)
      (fun n ↦ Filter.Eventually.of_forall (hFbd n))
      (Filter.Eventually.of_forall hlim)
  have hconst : ∀ n, ∫ ω, F n ω ∂P = ∫ ω, Y j ω ∂P := fun n ↦
    integral_stoppedValue_eq_of_countable_range hY (isStoppingTime_dyadStop hρ hρj n)
      (dyadStop_le j ρ n) (countable_range_dyadStop j ρ n)
  simp only [hconst] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

/-! ### The stopped martingale theorem -/

theorem integrable_of_abs_le' {Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z P) {C : ℝ}
    (hC : ∀ ω, |Z ω| ≤ C) : Integrable Z P :=
  (memLp_top_of_bound hZ C (Filter.Eventually.of_forall fun ω ↦ by
    simpa [Real.norm_eq_abs] using hC ω)).integrable le_top

/-- **The stopped process of a martingale is a martingale**, in continuous time. -/
theorem martingale_stoppedProcess (hY : Martingale Y 𝓕 P) (hprog : IsStronglyProgressive 𝓕 Y)
    (hrc : ∀ (ω : Ω) (s : ℝ≥0), Tendsto (fun r ↦ Y r ω) (𝓝[≥] s) (𝓝 (Y s ω)))
    (hbdd : ∀ j : ℝ≥0, ∃ C, ∀ s ≤ j, ∀ ω, |Y s ω| ≤ C)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess Y τ) 𝓕 P := by
  have hadp := hprog.stronglyAdapted_stoppedProcess hτ
  refine ⟨hadp, fun i j hij ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbdd j
  have hSPeq : ∀ (k : ℝ≥0) (ω : Ω),
      stoppedProcess Y τ k ω = Y ((min (k : ℝ≥0∞) (τ ω)).untopA) ω := fun _ _ ↦ rfl
  have hSPbd : ∀ (k : ℝ≥0), k ≤ j → ∀ ω, |stoppedProcess Y τ k ω| ≤ C := fun k hk ω ↦ by
    rw [hSPeq]
    exact hC _ ((WithTop.untopA_le (min_le_left (k : ℝ≥0∞) (τ ω))).trans hk) ω
  have hint : ∀ (k : ℝ≥0), k ≤ j → Integrable (stoppedProcess Y τ k) P := fun k hk ↦
    integrable_of_abs_le' ((hadp k).mono (𝓕.le k)).aestronglyMeasurable (hSPbd k hk)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j le_rfl)
    (fun S _ _ ↦ (hint i hij).integrableOn) ?_ (hadp i).aestronglyMeasurable).symm
  intro S hS _
  classical
  set B : Set Ω := S ∩ {ω | (i : ℝ≥0∞) < τ ω} with hBdef
  set A₀ : Set Ω := S ∩ {ω | τ ω ≤ (i : ℝ≥0∞)} with hA₀def
  have hgt : MeasurableSet[𝓕 i] {ω | (i : ℝ≥0∞) < τ ω} := by
    have h : {ω | (i : ℝ≥0∞) < τ ω} = {ω | τ ω ≤ (i : ℝ≥0∞)}ᶜ := by
      ext ω; simp [not_le]
    rw [h]
    exact (hτ i).compl
  have hB : MeasurableSet[𝓕 i] B := hS.inter hgt
  have hA₀ : MeasurableSet[𝓕 i] A₀ := hS.inter (hτ i)
  have hBm : MeasurableSet B := 𝓕.le i _ hB
  have hA₀m : MeasurableSet A₀ := 𝓕.le i _ hA₀
  set ρ : Ω → ℝ≥0∞ :=
    B.piecewise (fun ω ↦ max (min (τ ω) (j : ℝ≥0∞)) (i : ℝ≥0∞)) (fun _ ↦ (i : ℝ≥0∞)) with hρdef
  have hρst : IsStoppingTime 𝓕 ρ :=
    ((hτ.min_const (j : ℝ≥0)).max_const (i : ℝ≥0)).piecewise_of_le
      (isStoppingTime_const 𝓕 i) (fun _ ↦ le_max_right _ _) (fun _ ↦ le_rfl) hB
  have hij' : (i : ℝ≥0∞) ≤ (j : ℝ≥0∞) := by exact_mod_cast hij
  have hρj : ∀ ω, ρ ω ≤ (j : ℝ≥0∞) := fun ω ↦ by
    by_cases hω : ω ∈ B
    · rw [hρdef, Set.piecewise_eq_of_mem _ _ _ hω]
      exact max_le (min_le_right _ _) hij'
    · rw [hρdef, Set.piecewise_eq_of_notMem _ _ _ hω]
      exact hij'
  have hkey : ∫ ω, stoppedValue Y ρ ω ∂P = ∫ ω, Y j ω ∂P :=
    integral_stoppedValue_eq hY hprog hrc hC hρst hρj
  have hconst : ∫ ω, Y i ω ∂P = ∫ ω, Y j ω ∂P := by
    have h := integral_stoppedValue_eq (Y := Y) hY hprog hrc hC
      (ρ := fun _ ↦ (i : ℝ≥0∞)) (isStoppingTime_const 𝓕 i) (fun _ ↦ hij')
    simpa only [show (stoppedValue Y (fun _ : Ω ↦ (i : ℝ≥0∞))) = Y i from rfl] using h
  have hvalB : ∀ ω ∈ B, stoppedValue Y ρ ω = stoppedProcess Y τ j ω := by
    intro ω hω
    have hiτ : (i : ℝ≥0∞) < τ ω := hω.2
    have hmin : (i : ℝ≥0∞) ≤ min (τ ω) (j : ℝ≥0∞) := le_min hiτ.le hij'
    simp only [stoppedValue, hρdef, Set.piecewise_eq_of_mem _ _ _ hω, max_eq_left hmin]
    rw [hSPeq, min_comm]
  have hvalBc : ∀ ω ∈ Bᶜ, stoppedValue Y ρ ω = Y i ω := by
    intro ω hω
    simp only [stoppedValue, hρdef, Set.piecewise_eq_of_notMem _ _ _ hω]
    rfl
  have hYint : ∀ (k : ℝ≥0), k ≤ j → Integrable (Y k) P := fun k hk ↦
    integrable_of_abs_le' ((hY.stronglyMeasurable k).mono (𝓕.le k)).aestronglyMeasurable
      (fun ω ↦ hC k hk ω)
  have hρint : Integrable (stoppedValue Y ρ) P :=
    integrable_of_abs_le'
      ((stronglyMeasurable_stoppedValue_of_le hprog hρst hρj).mono (𝓕.le j)).aestronglyMeasurable
      (fun ω ↦ by
        show |Y ((ρ ω).untopA) ω| ≤ C
        exact hC _ (WithTop.untopA_le (hρj ω)) ω)
  have hsplit1 : ∫ ω in B, stoppedProcess Y τ j ω ∂P + ∫ ω in Bᶜ, Y i ω ∂P
      = ∫ ω, Y j ω ∂P := by
    rw [← hkey, ← integral_add_compl hBm hρint,
      setIntegral_congr_fun hBm hvalB, setIntegral_congr_fun hBm.compl hvalBc]
  have hsplit2 : ∫ ω in B, Y i ω ∂P + ∫ ω in Bᶜ, Y i ω ∂P = ∫ ω, Y j ω ∂P := by
    rw [integral_add_compl hBm (hYint i hij), hconst]
  have hB1 : ∫ ω in B, stoppedProcess Y τ j ω ∂P = ∫ ω in B, Y i ω ∂P := by
    have h := hsplit1.trans hsplit2.symm
    linarith [h]
  have hB2 : ∫ ω in B, stoppedProcess Y τ i ω ∂P = ∫ ω in B, Y i ω ∂P := by
    refine setIntegral_congr_fun hBm fun ω hω ↦ ?_
    have hiτ : (i : ℝ≥0∞) < τ ω := hω.2
    rw [hSPeq, min_eq_left hiτ.le]
    rfl
  have hA₀eq : ∀ ω ∈ A₀, stoppedProcess Y τ i ω = stoppedProcess Y τ j ω := by
    intro ω hω
    have hτi : τ ω ≤ (i : ℝ≥0∞) := hω.2
    rw [hSPeq, hSPeq, min_eq_right hτi, min_eq_right (hτi.trans hij')]
  have hunion : B ∪ A₀ = S := by
    ext ω
    simp only [hBdef, hA₀def, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_or_ge (i : ℝ≥0∞) (τ ω) with hlt | hle
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hle⟩
  have hdisj : Disjoint B A₀ := by
    refine Set.disjoint_left.2 fun ω hω hω' ↦ ?_
    have h1 : (i : ℝ≥0∞) < τ ω := hω.2
    have h2 : τ ω ≤ (i : ℝ≥0∞) := hω'.2
    exact absurd h2 (not_le.2 h1)
  have hsp : ∀ (k : ℝ≥0), k ≤ j → ∫ ω in S, stoppedProcess Y τ k ω ∂P
      = ∫ ω in B, stoppedProcess Y τ k ω ∂P + ∫ ω in A₀, stoppedProcess Y τ k ω ∂P := by
    intro k hk
    rw [← hunion, setIntegral_union hdisj hA₀m (hint k hk).integrableOn (hint k hk).integrableOn]
  rw [hsp i hij, hsp j le_rfl, hB2, hB1, setIntegral_congr_fun hA₀m hA₀eq]

/-- **Emptiness check: the hypotheses are jointly satisfiable.**  The zero process is a
martingale, is progressive, has constant -- hence right continuous -- paths and is bounded by
`0` at every level, so the theorem is not a statement about an empty class. -/
theorem martingale_stoppedProcess_zero {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) τ) 𝓕 P :=
  martingale_stoppedProcess (martingale_zero ℝ 𝓕 P) (isStronglyProgressive_const 𝓕 0)
    (fun _ _ ↦ tendsto_const_nhds) (fun _ ↦ ⟨0, fun _ _ _ ↦ by simp⟩) hτ

/-- **Consistency check: at `τ = ⊤` the conclusion is the hypothesis.**  A stopping time that
never occurs must leave the process alone, and this is the instance at which an inverted `min`
or a misread `untopA` in the bookkeeping above would show. -/
theorem martingale_of_martingale_stoppedProcess_top (hY : Martingale Y 𝓕 P)
    (hprog : IsStronglyProgressive 𝓕 Y)
    (hrc : ∀ (ω : Ω) (s : ℝ≥0), Tendsto (fun r ↦ Y r ω) (𝓝[≥] s) (𝓝 (Y s ω)))
    (hbdd : ∀ j : ℝ≥0, ∃ C, ∀ s ≤ j, ∀ ω, |Y s ω| ≤ C) :
    Martingale Y 𝓕 P := by
  have h := martingale_stoppedProcess hY hprog hrc hbdd
    (τ := fun _ ↦ (⊤ : WithTop ℝ≥0)) (by simp [IsStoppingTime])
  rwa [stoppedProcess_const_top] at h

end TauCeti

