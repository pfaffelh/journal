import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧 𝓨} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} (X : Ω → 𝓧) (Y : Ω → 𝓨) (μ : Measure 𝓧) (μ : Measure 𝓧)
  (P : Measure Ω := by volume_tac)

/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
structure HasLaw : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

variable {X μ} {P : Measure Ω}

lemma HasLaw.congr {Y : Ω → 𝓧} (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [Measure.map_congr hY, hX.map_eq]

lemma MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) : HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

lemma HasLaw.comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

lemma HasLaw.fun_comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp hX

lemma HawLaw.hasLaw_pair [IsFiniteMeasure P] {M N : Type*} {mM : MeasurableSpace M} {mN : MeasurableSpace N}
    {μ : Measure M} {κ : Kernel M N} {X : Ω → M} {Y : Ω → N} (hX : HasLaw X μ P) (hY : ∀ ω, HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Measure.prod μ κ) P where
  aemeasurable := by
    refine AEMeasurable.prodMk hX.aemeasurable hY.aemeasurable
  map_eq := by
    refine MeasurePreserving.map_eq ?_
    simp [IndepFun, Kernel.IndepFun, Kernel.Indep] at hXY
    sorry

lemma hasLaw_eval : HasLaw id P P where
  aemeasurable := aemeasurable_id
  map_eq := Measure.map_id


lemma HawLaw.hasLaw_pair [IsFiniteMeasure P] {M N : Type*} {mM : MeasurableSpace M} {mN : MeasurableSpace N}
    {μ : Measure M} {ν : Measure N} {X : Ω → M} {Y : Ω → N} (hX : HasLaw X μ P) (hY : HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Measure.prod μ ν) P where
  aemeasurable := by
    refine AEMeasurable.prodMk hX.aemeasurable hY.aemeasurable
  map_eq := by
    refine MeasurePreserving.map_eq ?_
    simp [IndepFun, Kernel.IndepFun, Kernel.Indep] at hXY
    sorry

@[to_additive]
lemma IndepFun.hasLaw_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X μ P) (hY : HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  aemeasurable := hX.aemeasurable.mul hY.aemeasurable
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀ hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]

@[to_additive]
lemma IndepFun.hasLaw_fun_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X μ P) (hY : HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY

lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable]
  · rfl
  · rwa [hX.map_eq]

lemma HasLaw.lintegral_comp {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq, lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω → E} (hX : HasLaw X μ P) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X, hX.integral_comp aestronglyMeasurable_id]
  simp

lemma HasLaw.variance_eq {μ : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X μ P) :
    Var[X; P] = Var[id; μ] := by
  rw [← hX.map_eq, variance_map aemeasurable_id hX.aemeasurable, Function.id_comp]

end HasLaw
