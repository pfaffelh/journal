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
# Scratch: augmented filtrations of almost everywhere equal data
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

section Prelude

variable {Ω ι : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem eventuallyMeasurableSpace_mono {m m' : MeasurableSpace Ω} (h : m ≤ m')
    {l : Filter Ω} [CountableInterFilter l] :
    eventuallyMeasurableSpace m l ≤ eventuallyMeasurableSpace m' l := by
  rintro s ⟨t, ht, hst⟩
  exact ⟨t, h t ht, hst⟩

def MeasureTheory.Filtration.augment [Preorder ι] (𝓕 : Filtration ι m₀) (μ : Measure Ω) :
    Filtration ι m₀ where
  seq i := eventuallyMeasurableSpace (𝓕 i) (ae μ) ⊓ m₀
  mono' _ _ hij := inf_le_inf (eventuallyMeasurableSpace_mono (𝓕.mono hij)) le_rfl
  le' _ := inf_le_right

def naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {F : Type*} [mF : MeasurableSpace F] (X : ι' → Ω' → F) (hX : ∀ i, Measurable (X i)) :
    Filtration ι' m' where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (X j) mF
  mono' _ _ hij := biSup_mono fun _ ↦ ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j - s ⟨u, hu, rfl⟩
    exact hX j hu

theorem measurable_naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*}
    {m' : MeasurableSpace Ω'} {F : Type*} [mF : MeasurableSpace F] {X : ι' → Ω' → F}
    (hX : ∀ i, Measurable (X i)) {i j : ι'} (hji : j ≤ i) :
    Measurable[naturalFiltration (m' := m') X hX i] (X j) :=
  Measurable.mono (comap_measurable (X j))
    (le_iSup₂ (f := fun j (_ : j ≤ i) ↦ MeasurableSpace.comap (X j) mF) j hji) le_rfl

end Prelude

section AugmentAe

variable {Ω ι : Type*} [Preorder ι] {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The augmentation is monotone under inclusion modulo null sets.** -/
theorem MeasureTheory.Filtration.augment_le_augment_of_le_eventuallyMeasurableSpace
    {𝓕 𝓖 : Filtration ι m₀} (h : ∀ i, 𝓕 i ≤ eventuallyMeasurableSpace (𝓖 i) (ae μ)) (i : ι) :
    𝓕.augment μ i ≤ 𝓖.augment μ i := by
  rintro s ⟨⟨t, ht, hst⟩, hs⟩
  obtain ⟨u, hu, htu⟩ := h i t ht
  exact ⟨⟨u, hu, hst.trans htu⟩, hs⟩

/-- **The natural filtration of a process is contained, modulo null sets, in that of any
process that agrees with it almost everywhere.** -/
theorem naturalFiltration_le_eventuallyMeasurableSpace_of_ae_eq {F : Type*}
    [MeasurableSpace F] {X X' : ι → Ω → F} (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, Measurable (X' i)) (h : ∀ i, X i =ᵐ[μ] X' i) (i : ι) :
    naturalFiltration (m' := m₀) X hX i
      ≤ eventuallyMeasurableSpace (naturalFiltration (m' := m₀) X' hX' i) (ae μ) := by
  refine iSup₂_le fun j hji ↦ ?_
  rintro s ⟨u, hu, rfl⟩
  exact ⟨X' j ⁻¹' u, measurable_naturalFiltration hX' hji hu, (h j).preimage u⟩

/-- **Two processes that agree almost everywhere have the same augmented natural filtration.**

This is the bridge the refuted σ-algebra identity needs: a statement that holds only almost
everywhere is repaired not by weakening it, but by modifying the data on a null set and
augmenting. -/
theorem naturalFiltration_augment_eq_of_ae_eq {F : Type*} [MeasurableSpace F]
    {X X' : ι → Ω → F} (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (h : ∀ i, X i =ᵐ[μ] X' i) :
    (naturalFiltration (m' := m₀) X hX).augment μ
      = (naturalFiltration (m' := m₀) X' hX').augment μ :=
  Filtration.ext (funext fun i ↦ le_antisymm
    (Filtration.augment_le_augment_of_le_eventuallyMeasurableSpace
      (naturalFiltration_le_eventuallyMeasurableSpace_of_ae_eq hX hX' h) i)
    (Filtration.augment_le_augment_of_le_eventuallyMeasurableSpace
      (naturalFiltration_le_eventuallyMeasurableSpace_of_ae_eq hX' hX
        (fun i ↦ (h i).symm)) i))

end AugmentAe

#print axioms MeasureTheory.Filtration.augment_le_augment_of_le_eventuallyMeasurableSpace
#print axioms naturalFiltration_le_eventuallyMeasurableSpace_of_ae_eq
#print axioms naturalFiltration_augment_eq_of_ae_eq
