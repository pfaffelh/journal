/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber, Joachim Breitner
-/

-- feat(Data/Set/Dissipate): Introduce dissipate s x := ⋂ y ≤ x, s y #33975

-- PR 36013 introduce compact systems
-- PR 36089 Union
-- PR 36160 Pi
-- PR 36225 Inter

import Journal.Notes.dissipate
import Journal.Notes.cylinders
import Mathlib.Data.Set.Dissipate
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems.

This file defines compact systems of sets. These are set predicates `p : Set α → Prop` with the
following property: If `C : ℕ → Set α` is such that `∀ n, p (C n)` and `⋂ n, C n = ∅`, then
there is some `n : ℕ` with `⋂ k ≤ n, C k = ∅`.

## Main definitions

* `IsCompactSystem`: A predicate on sets `p : Set α → Prop` is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `IsCompactSystem.iff_isCompactSystem_of_or_univ`: A predicate on sets is a compact
system iff adding `p univ` gives a compact system.
* `IsClosedCompact.isCompactSystem`: The set of closed and compact sets is a compact system.
* `IsClosedCompact.isCompactSystem_of_T2Space`: In a `T2Space α`, the set of compact sets
  is a compact system in a `T2Space`.
* `IsCompactSystem.closedCompactSquareCylinders`: Closed and compact square cylinders form a
  compact system.
-/

open Set Nat MeasureTheory

open Set Finset Nat

variable {α : Type*} {S : Set (Set α)} {C : ℕ → Set α}

section definition

-- PR 36013
/-- A predicate on sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

-- PR 36013
lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC

-- PR 36013
lemma nonempty_iInter (hp : IsCompactSystem S) {C : ℕ → Set α} (hC : ∀ i, C i ∈ S)
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

-- PR 36013
theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

/-
open Classical in
/-- In a compact system, given a countable family with `⋂ i, C i = ∅`, we choose the smallest `n`
with `⋂ (i ≤ n), C i = ∅`. -/
noncomputable

def finite_of_empty (hp : IsCompactSystem S) (hC : ∀ i, C i ∈ S)
    (hC_empty : ⋂ i, C i = ∅) : ℕ := Nat.find (hp C hC hC_empty)
-/

/-
-- PR 36013
open Classical in
lemma dissipate_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    dissipate C (hp.finite_of_empty hC hC_empty) = ∅ := Nat.find_spec (hp C hC hC_empty)

-- PR 36013
theorem iff_nonempty_iInter (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC <;>
  push_neg at h2 <;> apply h2
  exact hn

-- PR 36013
-/

-- PR 36089
lemma iff_nonempty_iInter_of_lt' (S : Set (Set α)) : IsCompactSystem S ↔
    ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k : Fin (n + 1), C k).Nonempty) → (⋂ i, C i).Nonempty := by
  rw [iff_nonempty_iInter]
  simp_rw [dissipate_eq_ofFin]


-- PR 36013
/-- Any subset of a compact system is a compact system. -/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
    IsCompactSystem S := fun C hC1 hC2 ↦ hT C (fun i ↦ hST (hC1 i)) hC2

-- PR 36013
/-- Inserting `∅` into a compact system gives a compact system. -/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · push_neg at g
    refine h s (fun i ↦ ?_) hd
    specialize g i
    specialize h' i
    rw [Set.nonempty_iff_ne_empty] at g
    simpa [g] using h'

-- PR 36013
@[simp]
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

-- PR 36013
/-- Inserting `univ` into a compact system gives a compact system. -/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases h₀ : ∀ n, s n ∉ S
  · simp only [mem_insert_iff, h₀, or_false] at h'
    simp [h']
  push_neg at h₀
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if s i ∈ S then s i else s n
  have h₁ : ∀ i, s' i ∈ S := by simp [s']; grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! h_exists_empty
  obtain ⟨j, hj⟩ := h_exists_empty
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v:= by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq_iInter_lt ▸ (h' (n + 1))),
    fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g ↦ h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x ↦ by simp; grind) g

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (fun _ hs ↦ Set.mem_insert_of_mem ∅ hs), fun h ↦ h.insert_empty⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (fun _ hs ↦ Set.mem_insert_of_mem univ hs), fun h ↦ h.insert_univ⟩

-- PR 36013
theorem isCompactSystem_iff_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (fun x1 x2 ↦ x1 ⊇ x2) C) → (∀ i, C i ∈ S) → ⋂ i, C i = ∅ →
      ∃ n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [exists_dissipate_eq_empty_iff_of_directed C hdi]
    exact h C (by simp [hi])
  · have hpi' : IsPiSystem (insert ∅ S) := hpi.insert_empty
    rw [← biInter_le_eq_iInter] at h2
    obtain h' := h (dissipate C) directed_dissipate
    have h₀ (h₀ : ∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅) (h₁ : ⋂ n, dissipate C n = ∅) :
        ∃ n, dissipate C n = ∅ := by
      by_cases! f : ∀ n, dissipate C n ∈ S
      · apply h' f h₁
      · obtain ⟨n, hn⟩ := f
        exact ⟨n, by simpa [hn] using h₀ n⟩
    obtain h'' := IsPiSystem.dissipate_mem hpi' h1
    have h₁ : ∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅ := by
      intro n
      by_cases g : (dissipate C n).Nonempty
      · simpa [or_comm] using h'' n g
      · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)
    apply h₀ h₁ h2

-- PR 36013
theorem isCompactSystem_iff_directed' (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (fun x1 x2 ↦ x1 ⊇ x2) C) → (∀ i, C i ∈ S) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

-- maybe this belongs somewhere else...
/-- For a ∩-stable set of sets `p` on `α` and a sequence of sets `s` with this attribute,
`dissipate s n` belongs to `p`. -/
lemma IsPiSystem.dissipate_mem {s : ℕ → Set α} {p : Set (Set α)}
    (hp : IsPiSystem p) (h : ∀ n, s n ∈ p) (n : ℕ) (h' : (dissipate s n).Nonempty) :
      (dissipate s n) ∈ p := by
  induction n with
  | zero =>
    simp only [dissipate_def, Nat.le_zero_eq, iInter_iInter_eq_left]
    exact h 0
  | succ n hn =>
    rw [dissipate_succ] at *
    apply hp (dissipate s n) (hn (Nonempty.left h')) (s (n+1)) (h (n+1)) h'

section IsCompactIsClosed

variable {α : Type*} [TopologicalSpace α]

-- PR 36013
/-- The set of compact and closed sets is a compact system. -/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty ↦ ?_
  rw [← Set.iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) h_nonempty ?_ (fun n ↦ ?_)
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1
  · induction n with
    | zero => simp only [Set.dissipate_zero_nat]; exact (hC_cc 0).2
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hn.inter (hC_cc (n + 1)).2

-- PR 36013
/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert isCompactSystem_isCompact_isClosed α with s
  exact ⟨fun hs ↦ ⟨hs, hs.isClosed⟩, fun hs ↦ hs.1⟩

-- PR 36013
/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

-- PR 36089
section PrefixInduction

-- Should this section be private, or moved to a different file?

/- In this section, we prove a general induction principle, which we need for the construction
`Nat.prefixInduction q step0 step : (k : ℕ) →  (β k)` based on some
`q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop`. For
the induction start, `step0 : q 0 _` always holds since `Fin 0` cannot be satisfied, and
`step : (n : ℕ) → (k : (i : Fin n) → β i) → q n k → { a : β n // q (n + 1) (Fin.snoc k a) })`
`(n : ℕ) : β n` constructs the next element satisfying `q (n + 1) _` from a proof of `q n k`
and finding the next element.

In comparison to other induction principles, the proofs of `q n k` are needed in order to find
the next element. -/


/- A version of `Fin.elim0` using dependent types. -/
def Fin.elim0'.{u} (α : ℕ → Sort u) : (i : Fin 0) → (α i)
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

variable {β : ℕ → Type*} (q : ∀ n, (k : (i : Fin n) → β i) → Prop) (step0 : q 0 (Fin.elim0' _))
  (step : ∀ n (k : (i : Fin n) → β i) (_ : q n k), { a : β n // q (n + 1) (Fin.snoc k a)})

def Nat.prefixInduction.aux : ∀ (n : Nat), { k : (i : Fin n) → β i // q n k }
    | 0 => ⟨Fin.elim0' _, step0⟩
    | n + 1 =>
      let ⟨k, hk⟩ := aux n
      let ⟨a, ha⟩ := step n k hk
      ⟨Fin.snoc k a, ha⟩

theorem Nat.prefixInduction.auxConsistent (n : ℕ) (i : Fin n) :
    (Nat.prefixInduction.aux q step0 step (i + 1)).1 (Fin.last i) =
    (Nat.prefixInduction.aux q step0 step n).1 i := by
  revert i
  induction n with
  | zero => simp
  | succ n ih =>
    apply Fin.lastCases
    case last => simp
    case cast =>
      intro i
      simp_rw [Fin.val_castSucc, ih, aux]
      simp

/-- An induction principle showing that `q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop` holds
for all `n`. `step0` is satisfied by construction since `Fin 0` is empty.
In the induction `step`, we use that `q n k` holds for showing that `q (n + 1) (Fin.snoc k a)`
holds for some `a : β n`. -/
def Nat.prefixInduction (n : Nat) : β n :=
  (Nat.prefixInduction.aux q step0 step (n + 1)).1 (Fin.last n)

theorem Nat.prefixInduction_spec (n : Nat) : q n (Nat.prefixInduction q step0 step ·) := by
  cases n with
  | zero => convert step0
  | succ n =>
    have hk := (Nat.prefixInduction.aux q step0 step (n + 1)).2
    convert hk with i
    apply Nat.prefixInduction.auxConsistent

/- Often, `step` can only be proved by showing an `∃` statement. For this case, we use `step'`. -/
variable (step' : ∀ n (k : (i : Fin n) → β i) (_ : q n k), ∃ a, q (n + 1) (Fin.snoc k a))

/-- This version is noncomputable since it relies on an `∃`-statement -/
noncomputable def Nat.prefixInduction' (n : Nat) : β n :=
  (Nat.prefixInduction.aux q step0
    (fun n k hn ↦ ⟨(step' n k hn).choose, (step' n k hn).choose_spec⟩) (n + 1)).1 (Fin.last n)

theorem Nat.prefixInduction'_spec (n : Nat) : q n (Nat.prefixInduction' q step0 step' ·) := by
  apply prefixInduction_spec

end PrefixInduction

-- PR 36089
section Union

/- For a reference of `union.isCompactSystem`, see Pfanzagl, Pierlo.
Compact Systems of Sets. Springer, 1966, Lemma 1.4. -/

namespace IsCompactSystem

variable {L : ℕ → Finset (Set α)} {n : ℕ} {K : (k : Fin n) → Set α}

/-- `q n K` is the joint property that `∀ (k : Fin n), K k ∈ L k` and
`∀ N, (⋂ (j : Fin n), K j) ∩ (⋂ (k < N), ⋃₀ ↑(L (n + k))) ≠ ∅`.` holds. -/
def q (L : ℕ → Finset (Set α)) (n : ℕ) (K : (k : Fin n) → Set α) : Prop :=
  (∀ k : Fin n, K k ∈ L k) ∧ ∀ N, ((⋂ j, K j) ∩ ⋂ k < N, ⋃₀ L (n + k)).Nonempty

lemma q_iff_iInter (hK : ∀ k : Fin n, K k ∈ L k) :
    q L n K ↔
      ∀ N, ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩
        (⋂ k < N, ⋃₀ L (n + k))).Nonempty := by
  simp only [q, hK, implies_true, true_and]
  congr! 2 with N
  ext
  simp
  grind

lemma q_snoc_iff_iInter (hK : ∀ k : Fin n, K k ∈ L k) (y : Set α) :
    q L (n + 1) (Fin.snoc K y) ↔
      y ∈ L n ∧
        (∀ N, ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩ y ∩ (⋂ k < N, ⋃₀ L (n + k))).Nonempty) := by
  simp only [q]
  have h_imp : q L (n + 1) (Fin.snoc K y) → y ∈ L n := by
    intro ⟨h_mem, h⟩
    specialize h_mem ⟨n, by grind⟩
    simpa [Fin.snoc] using h_mem
  refine ⟨fun h' ↦ ⟨h_imp h', fun N ↦ ?_⟩, fun ⟨hy, h⟩ ↦ ⟨fun k ↦ ?_, fun N ↦ ?_⟩⟩
  · have ⟨h_mem, h⟩ := h'
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h N
    use x
    simp only [mem_iInter, mem_sUnion, SetLike.mem_coe, mem_inter_iff] at hx1 hx2 ⊢
    refine ⟨⟨fun i hi ↦ ?_, ?_⟩, fun i hi ↦ ?_⟩
    · simpa [Fin.snoc, hi] using hx1 ⟨i, hi.trans_le (le_succ n)⟩
    · simpa [Fin.snoc] using hx1 ⟨n, Nat.lt_add_one n⟩
    · have hy := h_imp h'
      cases i with
      | zero =>
        specialize hx1 ⟨n, Nat.lt_add_one n⟩
        simp only [Fin.snoc, lt_self_iff_false, ↓reduceDIte, cast_eq] at hx1
        exact ⟨y, hy, hx1⟩
      | succ n =>
        have hj' : n < N := by grind
        grind
  · unfold Fin.snoc
    by_cases hkn : k = n
    · simpa [hkn]
    · have hkn' : k < n := by grind
      grind
  · specialize h (N + 1)
    rw [Set.inter_nonempty_iff_exists_left] at h ⊢
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
    use x
    simp only [mem_inter_iff, mem_iInter, mem_sUnion, SetLike.mem_coe] at hx1 hx2 ⊢
    exact ⟨by simp [Fin.snoc]; grind, by grind⟩

lemma step0 {L : ℕ → Finset (Set α)} (hL : ∀ N, (⋂ k < N, ⋃₀ (L k : Set (Set α))).Nonempty) :
    q L 0 (Fin.elim0' (fun _ ↦ Set α)) :=
  ⟨by simp, by simpa using hL⟩

lemma inter_sUnion_eq_empty (s : Set α) (L : Set (Set α)) :
    (∀ a ∈ L, s ∩ a = ∅) ↔ s ∩ ⋃₀ L = ∅ := by
  simp_rw [← disjoint_iff_inter_eq_empty]
  exact Iff.symm disjoint_sUnion_right

lemma step' {L : ℕ → Finset (Set α)} (n : ℕ) (K : (k : Fin n) → Set α) (hK : q L n K) :
    ∃ a, q L (n + 1) (Fin.snoc K a) := by
  have hK' := hK.1
  simp_rw [q_iff_iInter hK'] at hK
  simp_rw [q_snoc_iff_iInter hK'] at ⊢
  by_contra! h
  choose b hb using h
  classical
  let b' := fun x ↦ dite (x ∈ (L n)) (fun c ↦ b x c) (fun _ ↦ 0)
  have hs : (L n : Set (Set α)).Nonempty := by
    specialize hK 1
    rw [Set.nonempty_def] at hK ⊢
    simp only [lt_one_iff, iInter_iInter_eq_left, add_zero, mem_inter_iff, mem_iInter, mem_sUnion,
      Finset.mem_coe] at hK ⊢
    obtain ⟨x, ⟨hx1, ⟨t, ⟨ht1, ht2⟩⟩⟩⟩ := hK
    use t
  obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L (Fin.last n)) b' hs
  simp_rw [Set.nonempty_iff_ne_empty] at hK
  apply hK (b' K0Max + 1)
  have h₂ (a : Set α) (ha : a ∈ L n) :
      ⋂ k < b' K0Max, ⋃₀ L (n + k) ⊆ ⋂ k < b a ha, ⋃₀ (L (n + k) : Set (Set α)) := by
    intro x hx
    simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    have f : b' a = b a ha := by simp [b', ha]
    exact fun i hi ↦ hx i (hi.trans_le (f ▸ hK0₂ a ha))
  have h₃ (a : Set α) (ha : a ∈ L (Fin.last n)) : (⋂ (j) (hj : j < n), K ⟨j, hj⟩) ∩ a ∩
      ⋂ k < b' K0Max, ⋃₀ L (n + k) = ∅ := by
    rw [← subset_empty_iff, ← hb a ha]
    exact inter_subset_inter (fun ⦃a⦄ a ↦ a) (h₂ a ha)
  simp_rw [inter_comm, inter_assoc] at h₃
  simp_rw [← disjoint_iff_inter_eq_empty] at h₃ ⊢
  simp only [Fin.val_last] at h₃
  have h₃'' := disjoint_iff_inter_eq_empty.mp (disjoint_sUnion_left.mpr h₃)
  rw [inter_comm, inter_assoc, ← disjoint_iff_inter_eq_empty] at h₃''
  apply disjoint_of_subset (fun ⦃a⦄ a ↦ a) _ h₃''
  simp only [subset_inter_iff, subset_iInter_iff]
  refine ⟨fun i hi x hx ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    obtain ⟨t, ht⟩ := hx i (lt_trans hi (Nat.lt_add_one _))
    use t
  · simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    obtain ⟨t, ht⟩ := hx 0 (zero_lt_succ _)
    use t
    simpa

/-- For `L : ℕ → Finset (Set α)` such that `L n ⊆ K` and
`h : ∀ N, ⋂ k < N, ⋃₀ L k ≠ ∅`, `memOfUnion h n` is some `K : ℕ → Set α` such that `K n ∈ L n`
for all `n` (this is `prop₀`) and `∀ N, ⋂ (j < n, K j) ∩ ⋂ (k < N), (⋃₀ L (n + k)) ≠ ∅`
(this is `prop₁`.) -/
noncomputable def memOfUnion (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k < N, ⋃₀ (L k : Set (Set α))).Nonempty) :
    ℕ → Set α :=
  Nat.prefixInduction' (q L) (step0 hL) step'

theorem memOfUnion.spec (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k < N, ⋃₀ (L k : Set (Set α))).Nonempty) (n : ℕ) :
    q L n (fun k : Fin n ↦ memOfUnion L hL k) :=
  Nat.prefixInduction'_spec (β := fun _ ↦ Set α) (q L) (step0 hL) step' n

lemma sInter_memOfUnion_nonempty (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k : Set (Set α))).Nonempty) (n : ℕ) :
    (⋂ (j : Fin n), memOfUnion L hL j).Nonempty := by
  simpa using (memOfUnion.spec L hL n).2 0

lemma sInter_memOfUnion_isSubset (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k < N, ⋃₀ (L k : Set (Set α))).Nonempty) :
    (⋂ j, memOfUnion L hL j) ⊆ ⋂ k, ⋃₀ L k := by
  exact iInter_mono <| fun n ↦
    subset_sUnion_of_subset (L n) (memOfUnion L hL n) (fun ⦃a⦄ a ↦ a)
      ((memOfUnion.spec L hL (n + 1)).1 ⟨n, by grind⟩)

/-- Finite unions of sets in a compact system. -/
def union (S : Set (Set α)) : Set (Set α) :=
  sUnion '' { L : Set (Set α) | L.Finite ∧ L ⊆ S}

lemma union.mem_iff (s : Set α) : s ∈ union S ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_setOf_eq] at hL
    use (hL.1.1).toFinset
    simpa [← hL.2] using hL.1.2
  · obtain ⟨L, hL⟩ := h
    use L
    simp [hL.1, hL.2]

/- If `IsCompactSystem S`, the set of finite unions of sets in `S` is also a compact system. -/
theorem union.isCompactSystem (S : Set (Set α)) (hS : IsCompactSystem S) :
    IsCompactSystem (union S) := by
  simp_rw [isCompactSystem_iff_nonempty_iInter_of_lt, mem_iff]
  intro C hi
  choose L' hL' using hi
  simp_rw [hL']
  intro hL
  refine Nonempty.mono (sInter_memOfUnion_isSubset L' hL) ?_
  exact (IsCompactSystem.iff_nonempty_iInter_of_lt' S).mp hS
    (fun k ↦ memOfUnion L' hL k)
    (fun i ↦ (hL' i).2 <| (memOfUnion.spec L' hL (i + 1)).1 ⟨i, by grind⟩)
    (fun n ↦ sInter_memOfUnion_nonempty L' hL (n + 1))

end IsCompactSystem

end Union

section Inter

namespace IsCompactSystem

/-- Finite intersections of sets in a compact system. -/
def inter (S : Set (Set α)) : Set (Set α) :=
  sInter '' { L : Set (Set α) | L.Countable ∧ L ⊆ S}

lemma inter.mem_iff (s : Set α) : s ∈ inter S ↔ ∃ L : Set (Set α), L.Countable ∧ s = ⋂₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_setOf_eq] at hL
    use L
    simp [hL]
  · obtain ⟨L, hL⟩ := h
    use L
    simp [hL.1, hL.2]

/- If `IsCompactSystem S`, the set of finite unions of sets in `S` is also a compact system. -/
theorem inter.isCompactSystem (S : Set (Set α)) (hS : IsCompactSystem S) :
    IsCompactSystem (inter S) := by
  by_cases h : Nonempty α
  · rw [IsCompactSystem] at hS ⊢
    intro D hD₁ hD₂
    simp_rw [inter.mem_iff] at hD₁
    choose E hE₁ using hD₁
    simp [hE₁] at hD₂
    rw [← sInter_iUnion] at hD₂
    have hE₃ : (⋃ i, E i).Countable := by
      simp [hE₁]
    have hE₄ : (⋃ i, E i) ⊆ S := by
      simp [hE₁]
    haveI : Nonempty (⋃ i, E i) := by
      contrapose! hD₂
      rw [Set.eq_empty_of_isEmpty (⋃ i, E i)]
      simp only [sInter_empty]
      refine nonempty_iff_univ_nonempty.mp h
    let ⟨x, hx⟩ := this
    rw [← range_enumerateCountable_of_mem hE₃ hx, sInter_range] at hD₂
    specialize hS (enumerateCountable hE₃ x)
    obtain ⟨n, hn⟩ := hS (fun i ↦ hE₄ (enumerateCountable_mem hE₃ hx i)) hD₂
    have g : ∀ i, ∃ j, enumerateCountable hE₃ x i ∈ E j := by
      intro i
      rw [← mem_iUnion]
      exact enumerateCountable_mem hE₃ hx i
    choose g hg using g
    use (Finset.range (n + 1)).sup g
    refine subset_eq_empty ?_ hn
    simp [dissipate]
    intro i hi
    apply le_trans (b := D (g i)) _ ((hE₁ (g i)).2.1 ▸ sInter_subset_of_mem (hg i))
    apply biInter_subset_of_mem
    change g i ≤ (Finset.range (n + 1)).sup g
    exact le_sup (mem_range_succ_iff.mpr hi)
  · simp at h
    exact of_IsEmpty (inter S)

end IsCompactSystem

end Inter


-- PR 3
section pi

namespace IsCompactSystem

variable {ι : Type*} {α : ι → Type*}

/- In a product space, the intersection of square cylinders is empty iff there is a coordinate `i`
such that the projections to `i` have empty intersection. -/
theorem iInter_pi_empty_iff {β : Type*} (s : β → Set ι) (t : β → (i : ι) → Set (α i)) :
   (⋂ b, ((s b).pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β) (_: i ∈ s b), (t b i) = ∅):= by
  rw [iInter_eq_empty_iff, not_iff_not.symm]
  push_neg
  simp only [Set.mem_pi, Set.nonempty_iInter, mem_iInter]
  refine ⟨fun ⟨x, hx⟩ i ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨x i, fun j hi ↦ hx j i hi⟩
  · choose x hx using h
    refine ⟨x, fun i j hj ↦ hx j i hj⟩

theorem iInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) :
   ( ⋂ b, (univ.pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β), (t b i) = ∅):= by
  rw [iInter_pi_empty_iff]
  simp only [mem_univ, iInter_true]

theorem biInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) (p : β → Prop) :
   ( ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) = ∅) ↔
      (∃ i : ι, ⋂ (b : β), ⋂ (_ : p b), (t b i) = ∅) := by
  have h :  ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) =
      ⋂ (b : { (b' : β) | p b' }), (univ.pi (t b.val)) := by
    exact biInter_eq_iInter p fun x h ↦ univ.pi (t x)
  have h' (i : ι) :  ⋂ (b : β), ⋂ (_ : p b), t b i =  ⋂ (b : { (b' : β) | p b' }), t b.val i := by
    exact biInter_eq_iInter p fun x h ↦ t x i
  simp_rw [h, h', iInter_univ_pi_empty_iff]

theorem pi (C : (i : ι) → Set (Set (α i))) (hC : ∀ i, IsCompactSystem (C i)) :
    IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  change ∀ i, S i ∈ univ.pi '' univ.pi C at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const] at hS
  choose x hx1 hx2 using hS
  simp_rw [← hx2] at h_empty ⊢
  simp_rw [iInter_univ_pi_empty_iff x] at h_empty
  obtain ⟨i, hi⟩ := h_empty
  let y := (fun b ↦ x b i)
  have hy (b : ℕ) : y b ∈ C i := by
    simp only [y]
    exact hx1 b i
  have ⟨n, hn⟩ := (hC i) y hy hi
  use n
  simp_rw [dissipate, ← hx2] at hn ⊢
  rw [biInter_univ_pi_empty_iff x]
  use i

end IsCompactSystem

end pi

section ClosedCompactSquareCylinders

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)
/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both,
closed and compact, for all `i ∈ s`. -/
def MeasureTheory.compactClosedSquareCylinders : Set (Set (Π i, α i)) :=
  MeasureTheory.squareCylinders (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })

/-- Products of compact and closed sets form a compact system. -/
theorem IsCompactSystem.compactClosedPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })) := IsCompactSystem.pi _ (fun _ ↦ isCompactSystem_isCompact_isClosed (α _))

theorem IsCompactSystem.compactClosedOrUnivPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ insert univ { t : Set (α i) | IsCompact t ∧ IsClosed t })) := IsCompactSystem.pi _ (fun i ↦ isCompactSystem_insert_univ_isCompact_isClosed (α i))

/-- Compact and closed square cylinders are a compact system. -/
theorem isCompactSystem.compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders α) := by
  apply IsCompactSystem.mono (IsCompactSystem.compactClosedOrUnivPi _)
    (MeasureTheory.squareCylinders_subset_of_or_univ _)

end ClosedCompactSquareCylinders
