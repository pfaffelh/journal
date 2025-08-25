import Mathlib

open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology

section atTopOf

def atTopOf [LE α] (p : α → Prop) : Filter α :=
  ⨅ K ∈ {K' | p K'}, 𝓟 {B | K ≤ B}

lemma mem_atTopOf_iff_of_directed [Preorder α] (p : α → Prop) (h₀ : {K' | p K'}.Nonempty) (h₁ : DirectedOn (fun x y ↦ x ≤ y) p) : s ∈ atTopOf p ↔ ∃ x ∈ {y | p y}, s ∈ 𝓟 {b | x ≤ b} := by
  simp only [atTopOf]
  rw [mem_biInf_of_directed _ h₀]
  refine directedOn_image.mp ?_
  simp only [DirectedOn] at h₁ ⊢
  intro x hx y hy
  simp only [mem_image, mem_setOf_eq] at hx hy
  obtain ⟨s, ⟨hs1, hs2⟩⟩ := hx
  obtain ⟨t, ⟨ht1, ht2⟩⟩ := hy
  simp only [mem_image, mem_setOf_eq, ge_iff_le, exists_exists_and_eq_and]
  obtain ⟨u, hu1, hu2, hu3⟩ := h₁ s hs1 t ht1
  use u
  refine ⟨hu1, ?_, ?_⟩
  · rw [← hs2]
    simp only [le_principal_iff, mem_principal, setOf_subset_setOf]
    intro a ha
    apply le_trans hu2 ha
  · rw [← ht2]
    simp only [le_principal_iff, mem_principal, setOf_subset_setOf]
    intro a ha
    apply le_trans hu3 ha

variable {α : Type*} [TopologicalSpace α]

lemma directedOn_of_isCompact : DirectedOn (α := Set α) (fun s t ↦ s ⊆ t) IsCompact :=
  fun x hx y hy ↦ ⟨x ∪ y, ⟨IsCompact.union hx hy, union_subset_iff.mp fun ⦃_⦄ a => a⟩⟩

lemma isCompact_nonempty : {K : Set α| IsCompact K}.Nonempty :=
  ⟨∅, isCompact_empty⟩

lemma mem_iInf_of_isCompact (a : Set (Set α)) : a ∈ atTopOf IsCompact ↔ ∃ K : Set α, IsCompact K ∧ ((𝓟 K).sets ⊆ a) := by
  rw [mem_atTopOf_iff_of_directed _ isCompact_nonempty directedOn_of_isCompact]
  simp only [mem_setOf_eq, le_eq_subset, mem_principal]
  rfl

end atTopOf

namespace MeasureTheory

namespace Measure

section tightMeasureSet

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (ℙ : Measure α) [IsProbabilityMeasure ℙ]

def IsTightMeasureSet (S : Set (Measure α)) := Tendsto (fun A ↦ ⨆ ℙ ∈ S, ℙ Aᶜ) (atTopOf IsCompact) (nhds 0)

lemma isTightMeasureSet_iff {S : Set (Measure α)} :
    IsTightMeasureSet S ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ ∀ ℙ ∈ S, ℙ Kᶜ ≤ ε := by
  simp only [IsTightMeasureSet]
  simp_rw [ENNReal.tendsto_nhds_zero, Filter.eventually_iff, mem_iInf_of_isCompact]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩ <;> obtain ⟨K, hK, hKε⟩ := h ε hε <;> refine ⟨K, hK, ?_⟩
  · specialize hKε (fun ⦃a⦄ a => a)
    simp only [iSup_le_iff, mem_setOf_eq] at hKε
    exact hKε
  · intro L hL
    simp only [Filter.mem_sets, mem_principal, iSup_le_iff, mem_setOf_eq] at hL ⊢
    intro ℙ hℙ
    specialize hKε ℙ hℙ
    rw [← compl_subset_compl] at hL
    exact le_trans (OuterMeasureClass.measure_mono ℙ hL) hKε

end tightMeasureSet

end Measure

end MeasureTheory
