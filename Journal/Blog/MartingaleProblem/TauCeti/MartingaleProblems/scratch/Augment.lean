/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-!
# The augmentation of a filtration by the null sets

Scratch file, written in the shape it will have in `Suggested.lean`: at the root namespace,
under `open Filter Topology MeasureTheory ProbabilityTheory Set`.
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

section Augmentation

variable {Ω ι : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Measurability modulo a σ-filter is monotone in the σ-algebra. -/
theorem eventuallyMeasurableSpace_mono {m m' : MeasurableSpace Ω} (h : m ≤ m')
    {l : Filter Ω} [CountableInterFilter l] :
    eventuallyMeasurableSpace m l ≤ eventuallyMeasurableSpace m' l := by
  rintro s ⟨t, ht, hst⟩
  exact ⟨t, h t ht, hst⟩

/-- **The augmentation of a filtration by the null sets of `μ`.** -/
def MeasureTheory.Filtration.augment [Preorder ι] (𝓕 : Filtration ι m₀) (μ : Measure Ω) :
    Filtration ι m₀ where
  seq i := eventuallyMeasurableSpace (𝓕 i) (ae μ) ⊓ m₀
  mono' _ _ hij := inf_le_inf (eventuallyMeasurableSpace_mono (𝓕.mono hij)) le_rfl
  le' _ := inf_le_right

variable [Preorder ι]

theorem MeasureTheory.Filtration.le_augment (𝓕 : Filtration ι m₀) (μ : Measure Ω) (i : ι) :
    𝓕 i ≤ 𝓕.augment μ i :=
  le_inf le_eventuallyMeasurableSpace (𝓕.le i)

theorem MeasureTheory.Filtration.exists_ae_eq_of_measurableSet_augment {𝓕 : Filtration ι m₀}
    {i : ι} {s : Set Ω} (hs : MeasurableSet[𝓕.augment μ i] s) :
    ∃ t, MeasurableSet[𝓕 i] t ∧ s =ᵐ[μ] t :=
  hs.1

theorem MeasureTheory.Filtration.measurableSet_augment_of_measure_zero {𝓕 : Filtration ι m₀}
    {i : ι} {s : Set Ω} (hs : MeasurableSet[m₀] s) (hμs : μ s = 0) :
    MeasurableSet[𝓕.augment μ i] s :=
  ⟨⟨∅, @MeasurableSet.empty _ (𝓕 i), ae_eq_empty.2 hμs⟩, hs⟩

theorem MeasureTheory.Filtration.measurableSet_augment_iff {𝓕 : Filtration ι m₀} {i : ι}
    {s : Set Ω} :
    MeasurableSet[𝓕.augment μ i] s ↔
      MeasurableSet[m₀] s ∧ ∃ t, MeasurableSet[𝓕 i] t ∧ s =ᵐ[μ] t :=
  ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- **The conditional expectation does not see an enlargement by null sets.** -/
theorem MeasureTheory.condExp_eq_condExp_of_forall_exists_ae_eq {m m' : MeasurableSpace Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m') (hm' : m' ≤ m₀)
    (happrox : ∀ s, MeasurableSet[m'] s → ∃ t, MeasurableSet[m] t ∧ s =ᵐ[μ] t)
    (f : Ω → F) : μ[f | m'] =ᵐ[μ] μ[f | m] := by
  by_cases hf : Integrable f μ
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hf
      (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
      ((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable)).symm
    obtain ⟨t, ht, hst⟩ := happrox s hs
    rw [setIntegral_congr_set hst, setIntegral_congr_set hst,
      setIntegral_condExp (hm.trans hm') hf ht]
  · simp [condExp_of_not_integrable hf]

/-- **The conditional expectation does not see the augmentation.** -/
theorem MeasureTheory.condExp_augment [IsFiniteMeasure μ] (𝓕 : Filtration ι m₀) (i : ι)
    (f : Ω → F) : μ[f | 𝓕.augment μ i] =ᵐ[μ] μ[f | 𝓕 i] :=
  condExp_eq_condExp_of_forall_exists_ae_eq (𝓕.le_augment μ i) ((𝓕.augment μ).le i)
    (fun _ hs ↦ Filtration.exists_ae_eq_of_measurableSet_augment hs) f

/-- **A martingale stays a martingale under the augmented filtration.** -/
theorem MeasureTheory.Martingale.augment [IsFiniteMeasure μ] {f : ι → Ω → F}
    {𝓕 : Filtration ι m₀} (hf : Martingale f 𝓕 μ) : Martingale f (𝓕.augment μ) μ :=
  ⟨fun i ↦ (hf.stronglyMeasurable i).mono (𝓕.le_augment μ i),
    fun i j hij ↦ (condExp_augment 𝓕 i (f j)).trans (hf.condExp_ae_eq hij)⟩

/-- **And it comes back down, provided the process is adapted to the smaller filtration.** -/
theorem MeasureTheory.Martingale.of_augment [IsFiniteMeasure μ] {f : ι → Ω → F}
    {𝓕 : Filtration ι m₀} (hf : Martingale f (𝓕.augment μ) μ) (hadapt : StronglyAdapted 𝓕 f) :
    Martingale f 𝓕 μ := by
  refine ⟨hadapt, fun i j hij ↦ ?_⟩
  calc μ[f j | 𝓕 i] =ᵐ[μ] μ[μ[f j | 𝓕.augment μ i] | 𝓕 i] :=
        (condExp_condExp_of_le (𝓕.le_augment μ i) ((𝓕.augment μ).le i)).symm
    _ =ᵐ[μ] μ[f i | 𝓕 i] := condExp_congr_ae (hf.condExp_ae_eq hij)
    _ = f i := condExp_of_stronglyMeasurable (𝓕.le i) (hadapt i) (hf.integrable i)

/-- **A stopping time of a filtration is one of its augmentation.** -/
theorem MeasureTheory.IsStoppingTime.augment {𝓕 : Filtration ι m₀} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) : IsStoppingTime (𝓕.augment μ) τ :=
  fun i ↦ 𝓕.le_augment μ i _ (hτ i)

/-- **A localizing sequence of a filtration is one of its augmentation.** -/
theorem ProbabilityTheory.IsLocalizingSequence.augment [TopologicalSpace ι] [OrderTopology ι]
    {𝓕 : Filtration ι m₀} {τ : ℕ → Ω → WithTop ι} (h : IsLocalizingSequence 𝓕 τ μ) :
    IsLocalizingSequence (𝓕.augment μ) τ μ where
  isStoppingTime n := (h.isStoppingTime n).augment
  tendsto_top := h.tendsto_top
  mono := h.mono

/-- **Two filtrations whose members agree up to null sets have the same augmentation.** -/
theorem MeasureTheory.Filtration.augment_eq_augment_of_forall_exists_ae_eq
    {𝓕 𝓖 : Filtration ι m₀}
    (h₁ : ∀ i s, MeasurableSet[𝓕 i] s → ∃ t, MeasurableSet[𝓖 i] t ∧ s =ᵐ[μ] t)
    (h₂ : ∀ i s, MeasurableSet[𝓖 i] s → ∃ t, MeasurableSet[𝓕 i] t ∧ s =ᵐ[μ] t) :
    𝓕.augment μ = 𝓖.augment μ := by
  have key : ∀ (𝓐 𝓑 : Filtration ι m₀),
      (∀ i s, MeasurableSet[𝓐 i] s → ∃ t, MeasurableSet[𝓑 i] t ∧ s =ᵐ[μ] t) →
      ∀ i, 𝓐.augment μ i ≤ 𝓑.augment μ i := by
    intro 𝓐 𝓑 h i s hs
    obtain ⟨t, ht, hst⟩ := Filtration.exists_ae_eq_of_measurableSet_augment hs
    obtain ⟨u, hu, htu⟩ := h i t ht
    exact ⟨⟨u, hu, hst.trans htu⟩, hs.2⟩
  exact Filtration.ext (funext fun i ↦ le_antisymm (key 𝓕 𝓖 h₁ i) (key 𝓖 𝓕 h₂ i))

end Augmentation

section AugmentationLocal

variable {Ω ι : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
variable {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- **A local property survives the augmentation**, whatever the property is: the filtration
enters `Locally` only through the localizing sequence. -/
theorem ProbabilityTheory.Locally.augment {p : (ι → Ω → F) → Prop} {𝓕 : Filtration ι m₀}
    {X : ι → Ω → F} (h : Locally p 𝓕 X μ) : Locally p (𝓕.augment μ) X μ := by
  obtain ⟨τ, hτ, hp⟩ := h
  exact ⟨τ, hτ.augment, hp⟩

end AugmentationLocal

#print axioms MeasureTheory.Filtration.augment
#print axioms MeasureTheory.condExp_augment
#print axioms MeasureTheory.Martingale.augment
#print axioms MeasureTheory.Martingale.of_augment
#print axioms MeasureTheory.IsStoppingTime.augment
#print axioms ProbabilityTheory.IsLocalizingSequence.augment
#print axioms ProbabilityTheory.Locally.augment
#print axioms MeasureTheory.Filtration.augment_eq_augment_of_forall_exists_ae_eq
#print axioms MeasureTheory.condExp_eq_condExp_of_forall_exists_ae_eq
#print axioms MeasureTheory.Filtration.measurableSet_augment_of_measure_zero
#print axioms MeasureTheory.Filtration.measurableSet_augment_iff
#print axioms MeasureTheory.Filtration.le_augment
#print axioms MeasureTheory.Filtration.exists_ae_eq_of_measurableSet_augment
#print axioms eventuallyMeasurableSpace_mono
