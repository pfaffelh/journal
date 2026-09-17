/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Lévy's upward theorem for an `RCLike` valued integrand

Scratch development for `TauCeti/MartingaleProblems/Suggested.lean`, Milestone 9.
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

namespace TauCeti

section Levy

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m0} {𝕂 : Type*} [RCLike 𝕂]

/-- **Lévy's upward theorem for an `RCLike` valued integrand.** -/
theorem tendsto_ae_condExp_rclike (g : Ω → 𝕂) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[g | ℱ n]) ω) atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) ω)) := by
  by_cases hg : Integrable g μ
  · have hre := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (⇑(RCLike.re (K := 𝕂)) ∘ g)
    have him := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (⇑(RCLike.im (K := 𝕂)) ∘ g)
    have hcre : ∀ n, ∀ᵐ ω ∂μ,
        RCLike.re ((μ[g | ℱ n]) ω) = (μ[⇑(RCLike.re (K := 𝕂)) ∘ g | ℱ n]) ω := by
      intro n
      filter_upwards [(RCLike.reCLM (K := 𝕂)).comp_condExp_comm (m := ℱ n) hg] with ω hω
      simpa using hω
    have hcim : ∀ n, ∀ᵐ ω ∂μ,
        RCLike.im ((μ[g | ℱ n]) ω) = (μ[⇑(RCLike.im (K := 𝕂)) ∘ g | ℱ n]) ω := by
      intro n
      filter_upwards [(RCLike.imCLM (K := 𝕂)).comp_condExp_comm (m := ℱ n) hg] with ω hω
      simpa using hω
    have hLre : ∀ᵐ ω ∂μ,
        RCLike.re ((μ[g | ⨆ n, ℱ n]) ω) = (μ[⇑(RCLike.re (K := 𝕂)) ∘ g | ⨆ n, ℱ n]) ω := by
      filter_upwards [(RCLike.reCLM (K := 𝕂)).comp_condExp_comm (m := ⨆ n, ℱ n) hg] with ω hω
      simpa using hω
    have hLim : ∀ᵐ ω ∂μ,
        RCLike.im ((μ[g | ⨆ n, ℱ n]) ω) = (μ[⇑(RCLike.im (K := 𝕂)) ∘ g | ⨆ n, ℱ n]) ω := by
      filter_upwards [(RCLike.imCLM (K := 𝕂)).comp_condExp_comm (m := ⨆ n, ℱ n) hg] with ω hω
      simpa using hω
    rw [← ae_all_iff] at hcre hcim
    filter_upwards [hre, him, hcre, hcim, hLre, hLim] with ω hreω himω hcreω hcimω hLreω hLimω
    have h1 : Tendsto (fun n ↦ RCLike.re ((μ[g | ℱ n]) ω)) atTop
        (𝓝 (RCLike.re ((μ[g | ⨆ n, ℱ n]) ω))) := by
      rw [hLreω]
      exact hreω.congr fun n ↦ (hcreω n).symm
    have h2 : Tendsto (fun n ↦ RCLike.im ((μ[g | ℱ n]) ω)) atTop
        (𝓝 (RCLike.im ((μ[g | ⨆ n, ℱ n]) ω))) := by
      rw [hLimω]
      exact himω.congr fun n ↦ (hcimω n).symm
    have h3 : Tendsto (fun n ↦ ((RCLike.re ((μ[g | ℱ n]) ω) : 𝕂)
          + (RCLike.im ((μ[g | ℱ n]) ω) : 𝕂) * RCLike.I)) atTop
        (𝓝 ((RCLike.re ((μ[g | ⨆ n, ℱ n]) ω) : 𝕂)
          + (RCLike.im ((μ[g | ⨆ n, ℱ n]) ω) : 𝕂) * RCLike.I)) :=
      ((RCLike.continuous_ofReal.tendsto _).comp h1).add
        ((((RCLike.continuous_ofReal.tendsto _).comp h2)).mul tendsto_const_nhds)
    simpa only [RCLike.re_add_im] using h3
  · simp only [condExp_of_not_integrable hg, Pi.zero_apply]
    exact .of_forall fun _ ↦ tendsto_const_nhds

end Levy

section L1Perturbation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝕂 : Type*} [RCLike 𝕂]

/-- **A sequence that vanishes in `L¹` has conditional expectations that vanish in
`L¹`**, for an arbitrary sequence of sub-σ-algebras: conditional Jensen in the
form `integral_norm_condExp_le`, and nothing else.  No relation between the
σ-algebras is read, so this applies verbatim to `n ↦ (hτ n).measurableSpace`. -/
theorem tendsto_integral_norm_condExp_of_tendsto {m : ℕ → MeasurableSpace Ω}
    {Z : ℕ → Ω → 𝕂} (hZ : Tendsto (fun n ↦ ∫ ω, ‖Z n ω‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, ‖(μ[Z n | m n]) ω‖ ∂μ) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ integral_nonneg fun ω ↦ norm_nonneg _) (fun n ↦ ?_) hZ
  exact integral_norm_condExp_le (Z n)

/-- A sequence of integrable functions whose `L¹` norms tend to `0` tends to `0` in
measure.  Only `ofReal_integral_norm_eq_lintegral_enorm` stands between the Bochner
form in which `IsL1LeftContinuousAlongStoppingTimes` is stated and the `eLpNorm`
form in which Mathlib states the implication. -/
theorem tendstoInMeasure_zero_of_tendsto_integral_norm {Z : ℕ → Ω → 𝕂}
    (hZi : ∀ n, Integrable (Z n) μ)
    (hZ : Tendsto (fun n ↦ ∫ ω, ‖Z n ω‖ ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ Z atTop 0 := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    (fun n ↦ (hZi n).aestronglyMeasurable) aestronglyMeasurable_zero ?_
  have heq : ∀ n, eLpNorm (Z n - 0) 1 μ = ENNReal.ofReal (∫ ω, ‖Z n ω‖ ∂μ) := by
    intro n
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hZi n)]
  simp only [heq]
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal hZ

end L1Perturbation

section Identification

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m0} {𝕂 : Type*} [RCLike 𝕂]

/-- **The identification of a pathwise limit with a conditional expectation.**

If a sequence `a` splits, for each `n`, into the conditional expectation of one
fixed `W` for `ℱ n` plus the conditional expectation of a perturbation `Z n` that
vanishes in `L¹`, and if `a` converges almost surely to `A`, then
`A =ᵐ[μ] μ[W | ⨆ n, ℱ n]`.

Three inputs and nothing else: Lévy's upward theorem on the first summand,
conditional Jensen and a subsequence on the second, and uniqueness of limits.  The
`L¹` hypothesis on the perturbation yields an almost sure statement only along a
subsequence, and that is enough precisely because the *left* side converges along
the whole sequence. -/
theorem ae_eq_condExp_iSup_of_tendsto {W A : Ω → 𝕂} {a Z : ℕ → Ω → 𝕂}
    (hZ : Tendsto (fun n ↦ ∫ ω, ‖Z n ω‖ ∂μ) atTop (𝓝 0))
    (hdec : ∀ n, a n =ᵐ[μ] fun ω ↦ (μ[W | ℱ n]) ω + (μ[Z n | ℱ n]) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ a n ω) atTop (𝓝 (A ω))) :
    A =ᵐ[μ] μ[W | ⨆ n, ℱ n] := by
  have hCZ : Tendsto (fun n ↦ ∫ ω, ‖(μ[Z n | ℱ n]) ω‖ ∂μ) atTop (𝓝 0) :=
    tendsto_integral_norm_condExp_of_tendsto (m := fun n ↦ ℱ n) hZ
  have hmeas : TendstoInMeasure μ (fun n ↦ μ[Z n | ℱ n]) atTop 0 :=
    tendstoInMeasure_zero_of_tendsto_integral_norm (fun _ ↦ integrable_condExp) hCZ
  obtain ⟨ns, hns, hnsae⟩ := hmeas.exists_seq_tendsto_ae
  have hlevy := tendsto_ae_condExp_rclike (μ := μ) (ℱ := ℱ) W
  have hdec' : ∀ᵐ ω ∂μ, ∀ n, a n ω = (μ[W | ℱ n]) ω + (μ[Z n | ℱ n]) ω := ae_all_iff.2 hdec
  filter_upwards [hlim, hlevy, hdec', hnsae] with ω hlimω hlevyω hdecω hnsω
  have h1 : Tendsto (fun k ↦ a (ns k) ω) atTop (𝓝 (A ω)) :=
    hlimω.comp hns.tendsto_atTop
  have h2 : Tendsto (fun k ↦ a (ns k) ω) atTop (𝓝 ((μ[W | ⨆ n, ℱ n]) ω)) := by
    have hZ0 : Tendsto (fun k ↦ (μ[Z (ns k) | ℱ (ns k)]) ω) atTop (𝓝 0) := by
      simpa using hnsω
    have := (hlevyω.comp hns.tendsto_atTop).add hZ0
    rw [add_zero] at this
    exact this.congr fun k ↦ (hdecω (ns k)).symm
  exact tendsto_nhds_unique h1 h2

end Identification

end TauCeti

#print axioms TauCeti.tendsto_ae_condExp_rclike
#print axioms TauCeti.tendsto_integral_norm_condExp_of_tendsto
#print axioms TauCeti.tendstoInMeasure_zero_of_tendsto_integral_norm
#print axioms TauCeti.ae_eq_condExp_iSup_of_tendsto
