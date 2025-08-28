import Mathlib

open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology

section atTopAbove

variable {α : Type*} [Preorder α] (p : α → Prop)

def atTopAbove : Filter α :=
  ⨅ (a : α) (_ : p a), Filter.principal (Set.Ici a)

lemma atTopAbove_eq : atTopAbove p = ⨅ a ∈ {x | p x}, Filter.principal (Set.Ici a) := by rfl

lemma mem_atTopAbove_iff_of_directed {s : Set α} (h₀ : {y | p y}.Nonempty) (h₁ : DirectedOn (fun x y ↦ x ≤ y) p) : s ∈ atTopAbove p ↔ ∃ (x : α) (_ : p x), s ∈ Filter.principal (Set.Ici x) := by
  rw [atTopAbove_eq, mem_biInf_of_directed _ h₀]
  · exact Iff.symm bex_def
  · rw [← directedOn_image]
    intro x hx y hy
    obtain ⟨s, ⟨hs1, hs2⟩⟩ := hx
    obtain ⟨t, ⟨ht1, ht2⟩⟩ := hy
    simp only [mem_image, mem_setOf_eq, ge_iff_le, exists_exists_and_eq_and]
    obtain ⟨u, hu1, hu2, hu3⟩ := h₁ s hs1 t ht1
    use u
    refine ⟨hu1, hs2.symm ▸ ?_, ht2.symm ▸ ?_⟩ <;> simp [hu2, hu3]

end atTopAbove

section Set

variable {α : Type*} {p : Set α → Prop}

lemma directedOn_of_unionMem (hp : ∀ (s : Set α) (_ : p s) (t : Set α) (_ : p t), p (s ∪ t)) : DirectedOn (α := Set α) (fun s t ↦ s ⊆ t) p :=
  fun x hx y hy ↦ ⟨x ∪ y, ⟨hp x hx y hy, union_subset_iff.mp fun ⦃_⦄ a => a⟩⟩

lemma mem_atTopAbove_iff_of_unionMem (a : Set (Set α)) (h : {s : Set α | p s }.Nonempty) (hp : ∀ (s : Set α) (_ : p s) (t : Set α) (_ : p t), p (s ∪ t)) : a ∈ atTopAbove p ↔ ∃ K : Set α, p K ∧ ((Filter.principal K).sets ⊆ a) := by
  rw [mem_atTopAbove_iff_of_directed p h (directedOn_of_unionMem hp)]
  simp_all only [mem_principal, exists_prop]
  rfl

end Set

section isCompact

variable {α : Type*} [TopologicalSpace α]

lemma mem_iInf_of_isCompact (a : Set (Set α)) : a ∈ atTopAbove IsCompact ↔
    ∃ K : Set α, IsCompact K ∧ ((𝓟 K).sets ⊆ a) :=
  mem_atTopAbove_iff_of_unionMem a ⟨∅, isCompact_empty⟩ (fun _ hs _ ht => IsCompact.union hs ht)

lemma mem_iInf_of_isCompactSubset (a : Set (Set α)) (t : Set α) : a ∈ atTopAbove
    (fun s ↦ IsCompact s ∧ s ⊆ t) ↔ ∃ K : Set α, (IsCompact K ∧ K ⊆ t) ∧ ((𝓟 K).sets ⊆ a) :=
  mem_atTopAbove_iff_of_unionMem a ⟨∅, ⟨isCompact_empty, empty_subset t⟩⟩
    (fun _ ⟨hs1, hs2⟩ _ ⟨hu1, hu2⟩ ↦ ⟨IsCompact.union hs1 hu1, union_subset hs2 hu2⟩)

end isCompact

namespace MeasureTheory

namespace Measure

section innerRegular

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (ℙ : Measure α) [IsProbabilityMeasure ℙ]

lemma mem_nhdsIci_iff (x : ℝ≥0∞) : s ∈ nhdsSet (Ici x) ↔ ∃ r < x,  Ioi r ⊆ s := by
  sorry

lemma innerRegular_iff (p q : Set α → Prop) (h₀ : p ∅) (hp : ∀ (s : Set α) (_ : p s) (t : Set α) (_ : p t), p (s ∪ t)) : ℙ.InnerRegularWRT p q ↔ ∀ (t : Set α) (ht : q t ∧ 0 < ℙ t), Tendsto (fun s ↦ ℙ s) (atTopAbove (fun s ↦ p s ∧ s ⊆ t)) (nhdsSet (Ici (ℙ t))) := by
  have h₀' (t : Set α): {s | p s ∧ s ⊆ t}.Nonempty := ⟨∅, ⟨h₀, empty_subset t⟩⟩
  have hp' (u : Set α) : ∀ (s : Set α) (_ : p s ∧ s ⊆ u) (t : Set α) (_ : p t ∧ t ⊆ u), p (s ∪ t) ∧ s ∪ t ⊆ u := fun s ⟨hs1, hs2⟩ t ⟨ht1, ht2⟩ ↦ ⟨hp s hs1 t ht1, union_subset hs2 ht2⟩
  simp only [InnerRegularWRT]
  simp_rw [tendsto_iff_forall_eventually_mem, mem_nhdsIci_iff]
  change _ ↔ (∀ t, q t ∧ ℙ t > 0→ ∀ s, _ → {x | ℙ x ∈ s} ∈ atTopAbove fun s => p s ∧ s ⊆ t)
  conv => right ; right ; right ; right ; right ;  rw [mem_atTopAbove_iff_of_unionMem _ (h₀' _) (hp' _)]
  refine ⟨fun h t ht ↦ fun s hs ↦ ?_, fun h t ht r hr ↦ ?_⟩
  · obtain ⟨r, ⟨hr1, hr2⟩⟩ := hs
    obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := h ht.1 r hr1
    refine ⟨K, ⟨hK2, hK1⟩, fun L hL ↦ hr2 <| lt_of_lt_of_le hK3 <| OuterMeasureClass.measure_mono ℙ hL⟩
  · specialize h t ⟨ht, lt_of_le_of_lt (zero_le r) hr⟩ (Ioi r) _
    · use r, hr
    · obtain ⟨K, ⟨hK2, hK1⟩, hK3⟩ := h
      exact ⟨K, hK1, hK2, hK3 fun ⦃a⦄ a => a⟩

end innerRegular


section tightMeasureSet

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (ℙ : Measure α) [IsProbabilityMeasure ℙ]

def IsTightMeasureSet (S : Set (Measure α)) := Tendsto (fun A ↦ ⨆ ℙ ∈ S, ℙ Aᶜ) (atTopAbove IsCompact) (nhds 0)

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
