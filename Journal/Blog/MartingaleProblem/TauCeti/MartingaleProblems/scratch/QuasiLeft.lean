/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Quasi-left-continuity: the pathwise half

Scratch development for `TauCeti/MartingaleProblems/Suggested.lean`, Milestone 9.
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

namespace TauCeti

section Regularizing

variable {ι : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
variable {Ω : Type*} {m : MeasurableSpace Ω}
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Copy of the definition in `Suggested.lean`. -/
def IsCadlagPath (g : ι → E) : Prop :=
  (∀ t, ContinuousWithinAt g (Set.Ioi t) t) ∧ ∀ t, ∃ l, Tendsto g (𝓝[<] t) (𝓝 l)

/-- Copy of the definition in `Suggested.lean`. -/
def IsQuasiLeftContinuous (X : ι → Ω → E) (𝓕 : Filtration ι m)
    (P : Measure Ω) : Prop :=
  ∀ τ : ℕ → Ω → WithTop ι, (∀ n, IsStoppingTime 𝓕 (τ n)) → Monotone τ → ∀ t : ι,
    ∀ᵐ ω ∂P, (⨆ n, τ n ω) ≤ (t : WithTop ι) →
      Tendsto (fun n ↦ stoppedValue X (τ n) ω) atTop
        (𝓝 (stoppedValue X (fun ω ↦ ⨆ n, τ n ω) ω))

theorem coe_untopA {x : WithTop ι} (hx : x ≠ ⊤) : ((x.untopA : ι) : WithTop ι) = x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd rfl hx
  | coe a => rfl

/-- A càdlàg path converges along every nondecreasing sequence of indices with a
supremum: either the sequence reaches its supremum, and the values are eventually
constant, or it stays strictly below it, and the limit is the left limit. -/
theorem IsCadlagPath.exists_tendsto_comp_monotone {g : ι → E} (hg : IsCadlagPath g)
    {s : ℕ → ι} (hmono : Monotone s) {T : ι} (hle : ∀ n, s n ≤ T) (hsup : ⨆ n, s n = T) :
    ∃ l, Tendsto (fun n ↦ g (s n)) atTop (𝓝 l) := by
  by_cases h : ∃ N, s N = T
  · obtain ⟨N, hN⟩ := h
    refine ⟨g T, Tendsto.congr' ?_ tendsto_const_nhds⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact congrArg g (le_antisymm (hle n) (hN ▸ hmono hn)).symm
  · push_neg at h
    have hlt : ∀ n, s n < T := fun n ↦ lt_of_le_of_ne (hle n) (h n)
    obtain ⟨l, hl⟩ := hg.2 T
    have hbdd : BddAbove (Set.range s) := ⟨T, by rintro _ ⟨n, rfl⟩; exact hle n⟩
    have hts : Tendsto s atTop (𝓝 T) := hsup ▸ tendsto_atTop_ciSup hmono hbdd
    exact ⟨l, hl.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hts
      (.of_forall hlt))⟩

/-- **From countably many scalar convergences to quasi-left-continuity.**

The scalar statement is tested on one countable class `Φ₀` that separates the
points of `E` by continuous functions; the passage to the `E`-valued convergence
is the càdlàg property of the paths, which produces a limit, and the separation,
which identifies it.  No separation axiom on `E` and no compactness enter: the
limit exists by the path property, not by a compactness argument, and uniqueness
of limits is read in `𝕂`. -/
theorem isQuasiLeftContinuous_of_forall_ae_tendsto_comp {Φ₀ : Set (E → 𝕂)}
    {X : ι → Ω → E} {𝓕 : Filtration ι m} {P : Measure Ω}
    (hΦ₀c : Φ₀.Countable) (hcont : ∀ f ∈ Φ₀, Continuous f)
    (hsep : ∀ x y : E, x ≠ y → ∃ f ∈ Φ₀, f x ≠ f y)
    (hX : ∀ᵐ ω ∂P, IsCadlagPath (fun t ↦ X t ω))
    (hlim : ∀ f ∈ Φ₀, ∀ τ : ℕ → Ω → WithTop ι, (∀ n, IsStoppingTime 𝓕 (τ n)) → Monotone τ →
      ∀ t : ι, ∀ᵐ ω ∂P, (⨆ n, τ n ω) ≤ (t : WithTop ι) →
        Tendsto (fun n ↦ f (stoppedValue X (τ n) ω)) atTop
          (𝓝 (f (stoppedValue X (fun ω ↦ ⨆ n, τ n ω) ω)))) :
    IsQuasiLeftContinuous X 𝓕 P := by
  intro τ hτ hmono t
  have hall : ∀ᵐ ω ∂P, ∀ f ∈ Φ₀, (⨆ n, τ n ω) ≤ (t : WithTop ι) →
      Tendsto (fun n ↦ f (stoppedValue X (τ n) ω)) atTop
        (𝓝 (f (stoppedValue X (fun ω ↦ ⨆ n, τ n ω) ω))) :=
    (ae_ball_iff hΦ₀c).2 fun f hf ↦ hlim f hf τ hτ hmono t
  filter_upwards [hX, hall] with ω hcad hfω hle
  -- the supremum and every member of the sequence are finite at `ω`
  have hbddT : BddAbove (Set.range fun n ↦ τ n ω) := OrderTop.bddAbove _
  have hlen : ∀ n, τ n ω ≤ ⨆ k, τ k ω := fun n ↦ le_ciSup hbddT n
  have hsupne : (⨆ k, τ k ω) ≠ ⊤ := fun h ↦ by
    rw [h] at hle; exact absurd (top_le_iff.1 hle) (WithTop.coe_ne_top)
  have hnen : ∀ n, τ n ω ≠ ⊤ := fun n h ↦ hsupne (top_le_iff.1 (h ▸ hlen n))
  set s : ℕ → ι := fun n ↦ (τ n ω).untopA with hs
  set T : ι := (⨆ k, τ k ω).untopA with hT
  have hcoes : ∀ n, ((s n : ι) : WithTop ι) = τ n ω := fun n ↦ coe_untopA (hnen n)
  have hcoeT : ((T : ι) : WithTop ι) = ⨆ k, τ k ω := coe_untopA hsupne
  have hsle : ∀ n, s n ≤ T := fun n ↦ by
    have := hlen n
    rw [← hcoes n, ← hcoeT, WithTop.coe_le_coe] at this
    exact this
  have hsmono : Monotone s := fun a b hab ↦ by
    have := hmono hab ω
    rw [← hcoes a, ← hcoes b, WithTop.coe_le_coe] at this
    exact this
  have hsbdd : BddAbove (Set.range s) := ⟨T, by rintro _ ⟨n, rfl⟩; exact hsle n⟩
  have hssup : ⨆ n, s n = T := by
    have h1 : ((⨆ n, s n : ι) : WithTop ι) = ⨆ n, ((s n : ι) : WithTop ι) :=
      WithTop.coe_iSup s hsbdd
    have h2 : ((⨆ n, s n : ι) : WithTop ι) = ((T : ι) : WithTop ι) := by
      rw [h1, hcoeT]
      simp only [hcoes]
    exact WithTop.coe_inj.1 h2
  obtain ⟨l, hl⟩ := hcad.exists_tendsto_comp_monotone hsmono hsle hssup
  have hval : l = X T ω := by
    by_contra hne
    obtain ⟨f, hfΦ, hfne⟩ := hsep l (X T ω) hne
    have h1 : Tendsto (fun n ↦ f (X (s n) ω)) atTop (𝓝 (f l)) :=
      ((hcont f hfΦ).tendsto l).comp hl
    have h2 : Tendsto (fun n ↦ f (X (s n) ω)) atTop (𝓝 (f (X T ω))) := hfω f hfΦ hle
    exact hfne (tendsto_nhds_unique h1 h2)
  rw [hval] at hl
  exact hl

end Regularizing

section OptionalSampling

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **From the expectation form of optional sampling to the conditional form.** -/
theorem stoppedValue_ae_eq_condExp_of_forall_integral_eq
    {ι : Type*} [LinearOrder ι] [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [BorelSpace ι] [Nonempty ι]
    {𝓕 : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P] {Y : ι → Ω → ℝ}
    (hprog : IsStronglyProgressive 𝓕 Y) {j : ι} {C : ℝ}
    (hbdd : ∀ s ≤ j, ∀ ω, |Y s ω| ≤ C)
    (hint : ∀ ρ : Ω → WithTop ι, IsStoppingTime 𝓕 ρ → (∀ ω, ρ ω ≤ (j : WithTop ι)) →
      ∫ ω, stoppedValue Y ρ ω ∂P = ∫ ω, Y j ω ∂P)
    {σ : Ω → WithTop ι} (hσ : IsStoppingTime 𝓕 σ) (hσj : ∀ ω, σ ω ≤ (j : WithTop ι)) :
    stoppedValue Y σ =ᵐ[P] P[Y j | hσ.measurableSpace] := by
  classical
  have hle : hσ.measurableSpace ≤ m := hσ.measurableSpace_le_of_le hσj
  have hmeas : Measurable[hσ.measurableSpace] (stoppedValue Y σ) :=
    measurable_stoppedValue hprog hσ
  have hbd' : ∀ ω, |stoppedValue Y σ ω| ≤ C := fun ω ↦
    hbdd _ (WithTop.untopA_le (hσj ω)) ω
  have hσint : Integrable (stoppedValue Y σ) P :=
    (integrable_const C).mono' ((hmeas.mono hle le_rfl).stronglyMeasurable.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hbd' ω)
  have hYjint : Integrable (Y j) P :=
    (integrable_const C).mono'
      (((hprog.stronglyAdapted j).mono (𝓕.le j)).aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hbdd j le_rfl ω)
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hYjint
    (fun S _ _ ↦ hσint.integrableOn) ?_
    (hmeas.stronglyMeasurable.aestronglyMeasurable)
  intro S hS _
  have hSm : MeasurableSet S := hle S hS
  have hSj : MeasurableSet[𝓕 j] S := by
    have h := hS.2 j
    have heq : S ∩ {ω | σ ω ≤ (j : WithTop ι)} = S := by
      ext ω; simp [hσj ω]
    rwa [heq] at h
  set ρ : Ω → WithTop ι := S.piecewise σ (fun _ ↦ (j : WithTop ι)) with hρdef
  have hρj : ∀ ω, ρ ω ≤ (j : WithTop ι) := fun ω ↦ by
    by_cases h : ω ∈ S <;> simp [hρdef, Set.piecewise, h, hσj ω]
  have hρst : IsStoppingTime 𝓕 ρ := by
    intro t
    have heq : {ω | ρ ω ≤ (t : WithTop ι)}
        = (S ∩ {ω | σ ω ≤ (t : WithTop ι)}) ∪ (Sᶜ ∩ {ω | (j : WithTop ι) ≤ (t : WithTop ι)}) := by
      ext ω; by_cases h : ω ∈ S <;> simp [hρdef, Set.piecewise, h]
    rw [heq]
    refine MeasurableSet.union (hS.2 t) ?_
    by_cases hjt : (j : WithTop ι) ≤ (t : WithTop ι)
    · have hjt' : j ≤ t := by exact_mod_cast hjt
      simp only [hjt, Set.setOf_true, Set.inter_univ]
      exact (𝓕.mono hjt' _ hSj).compl
    · simp [hjt]
  have hρmeas : Measurable[𝓕 j] (stoppedValue Y ρ) := by
    have := stronglyMeasurable_stoppedValue_of_le hprog hρst hρj
    exact this.measurable
  have hρbd : ∀ ω, |stoppedValue Y ρ ω| ≤ C := fun ω ↦
    hbdd _ (WithTop.untopA_le (hρj ω)) ω
  have hρint : Integrable (stoppedValue Y ρ) P :=
    (integrable_const C).mono'
      ((hρmeas.mono (𝓕.le j) le_rfl).stronglyMeasurable.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hρbd ω)
  have hρval : ∀ ω, stoppedValue Y ρ ω = S.piecewise (stoppedValue Y σ) (Y j) ω := by
    intro ω
    by_cases h : ω ∈ S <;>
      simp [stoppedValue, hρdef, Set.piecewise, h]
  have h1 : ∫ ω, stoppedValue Y ρ ω ∂P
      = ∫ ω in S, stoppedValue Y σ ω ∂P + ∫ ω in Sᶜ, Y j ω ∂P := by
    rw [← integral_add_compl hSm hρint]
    congr 1
    · refine setIntegral_congr_fun hSm fun ω hω ↦ ?_
      rw [hρval ω]; simp [Set.piecewise, hω]
    · refine setIntegral_congr_fun hSm.compl fun ω hω ↦ ?_
      rw [hρval ω]; simp [Set.piecewise, Set.notMem_of_mem_compl hω]
  have h2 : ∫ ω, Y j ω ∂P = ∫ ω in S, Y j ω ∂P + ∫ ω in Sᶜ, Y j ω ∂P :=
    (integral_add_compl hSm hYjint).symm
  have h3 := hint ρ hρst hρj
  rw [h1, h2] at h3
  exact add_right_cancel h3

end OptionalSampling

end TauCeti
