import Mathlib

open Function Set

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

section squareCylinders

section Pi

-- in Data.Set.Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

variable [Preorder α] {f : α → Set β} {g : α → Set γ}

variable {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

/-
theorem pi_antitone (h : s₁ ⊆ s₂) : s₂.pi t ⊆ s₁.pi t := by
  rw [← union_diff_cancel h, union_pi]
  exact Set.inter_subset_left
-/

lemma pi_image_eq_of_subset {C : (i : ι) → Set (Set (α i))}
  (hC : ∀ i, Nonempty (C i))
  {s₁ s₂ : Set ι}
    (hst : s₁ ⊆ s₂) : s₁.pi '' s₁.pi C = s₁.pi '' s₂.pi C := by
  classical
  let C_mem (i : ι) : Set (α i) := ((Set.exists_mem_of_nonempty (C i)).choose : Set (α i))
  have h_mem (i : ι) : C_mem i ∈ C i := by
    simp [C_mem]
  ext f
  refine ⟨fun ⟨x, ⟨hx1, hx2⟩⟩ ↦ ?_, fun ⟨w, ⟨hw1, hw2⟩⟩ ↦ ?_⟩
  · use fun i ↦ if i ∈ s₁ then x i else C_mem i
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · by_cases h1 : i ∈ s₁ <;> simp only [h1, ↓reduceIte]
      · exact hx1 i h1
      · exact h_mem i
    · rw [← hx2]
      exact pi_congr rfl (fun i hi ↦ by simp only [hi, ↓reduceIte])
  · have hw3 := pi_mono' (fun _ _ _ hx ↦ hx) hst hw1
    use w

variable [∀ i, Nonempty (α i)]

/-
theorem pi_nonempty_iff' [∀ i, Decidable (i ∈ s)] :
    (s.pi t).Nonempty ↔ ∀ i ∈ s, (t i).Nonempty := by
  classical
  rw [pi_nonempty_iff]
  have h := fun i ↦ exists_mem_of_nonempty (α i)
  choose y hy using h
  refine ⟨fun h i hi ↦ ?_, fun h i ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h i
    exact ⟨x, hx hi⟩
  · choose x hx using h
    use (if g : i ∈ s then x i g else y i)
    intro hi
    simp only [hi, ↓reduceDIte]
    exact hx i hi
-/
end Pi

theorem squareCylinders_eq_iUnion_image' (C : ∀ i, Set (Set (α i))) (hC : ∀ i, Nonempty (C i)) :
    squareCylinders C = ⋃ s : Finset ι, (s : Set ι).pi '' (s : Set ι).pi C := by
  classical
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_setOf_eq, eq_comm (a := f)]
  have h (s : Set ι): s.pi '' s.pi C = s.pi '' univ.pi C := by
    refine pi_image_eq_of_subset hC (subset_univ s)
  simp_rw [← mem_image, h]

def squareCylinders_subset_of_or_univ (C : ∀ i, Set (Set (α i))) :
    squareCylinders C ⊆ (univ.pi '' univ.pi (fun i ↦ insert univ (C i))) := by
  classical
  intro x hx
  simp only [squareCylinders, mem_pi, mem_univ, forall_const, mem_setOf_eq] at hx
  obtain ⟨s, t, ⟨ht, hx⟩⟩ := hx
  simp only [mem_image, mem_pi, mem_univ, mem_insert_iff, forall_const]
  use fun i ↦ (if (i ∈ s) then (t i) else univ)
  refine ⟨?_, ?_⟩
  · intro i
    by_cases h : i ∈ s
    · right
      simp [h, ht]
    · left
      simp [h]
  · exact hx ▸ univ_pi_ite s t
