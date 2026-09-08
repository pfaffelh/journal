/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The finite partition with pieces of positive mass, standalone

`WeakConvergence` Milestone 3.  Both declarations of this file also stand in
`WeakConvergence/Suggested.lean`, where the countable partition comes from
`exists_measurable_partition_diam_le_null_frontier`.  Here it is taken as an
explicit hypothesis (`hcountable`) instead, so that the file depends on nothing
but Mathlib and can be type-checked on its own:

    lake env lean .../scratch/FinitePartition.lean

Type-checked against Mathlib `v4.33.1` on 2026-09-08; no `sorry`, no errors, and
the only warnings are `linter.unusedSectionVars` and `linter.unusedSimpArgs`.
-/

open Filter Set MeasureTheory Topology
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E]

/-- The frontier of a finite union is contained in the union of the frontiers.
Mathlib has the two-set case, `frontier_union_subset` (`Topology/Closure.lean:544`),
but not the `Finset` one; the induction is `Finset.induction_on` over
`Finset.set_biUnion_insert`. -/
theorem frontier_biUnion_finset_subset [TopologicalSpace E] (K : Finset ℕ) (S : ℕ → Set E) :
    frontier (⋃ j ∈ K, S j) ⊆ ⋃ j ∈ K, frontier (S j) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
      rw [Finset.set_biUnion_insert]
      refine (frontier_union_subset _ _).trans ?_
      rw [Finset.set_biUnion_insert]
      refine union_subset ?_ ?_
      · exact inter_subset_left.trans subset_union_left
      · exact inter_subset_right.trans (ih.trans subset_union_right)

/-- **The finite partition with pieces of positive mass.**  Truncation of the countable
partition, with the pieces of zero mass absorbed into the remainder `A 0`. -/
theorem exists_finite_partition_diam_le_null_frontier [PseudoMetricSpace E]
    [OpensMeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {ε : ℝ} {η : ℝ≥0∞}
    (hη : 0 < η)
    (hcountable : ∃ As : ℕ → Set E, (∀ n, MeasurableSet (As n)) ∧
      (∀ n, Metric.diam (As n) ≤ ε) ∧ (∀ n, ν (frontier (As n)) = 0) ∧
      (⋃ n, As n = univ) ∧ Pairwise (fun n m : ℕ => Disjoint (As n) (As m))) :
    ∃ (K : Finset ℕ) (A : ℕ → Set E), 0 ∉ K ∧
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Function.onFun Disjoint A) ∧
      (⋃ i, A i) = univ ∧
      (∀ i, ν (frontier (A i)) = 0) ∧
      (∀ i, i ≠ 0 → i ∉ K → A i = ∅) ∧
      (∀ i ∈ K, 0 < ν (A i)) ∧
      (∀ i ∈ K, Metric.diam (A i) ≤ ε) ∧
      ν (A 0) ≤ η := by
  classical
  obtain ⟨As, hAsm, hAsdiam, hAsfr, hAsu, hAsd⟩ := hcountable
  -- the tails of the countable partition
  set T : ℕ → Set E := fun M => (⋃ i ∈ Finset.range M, As i)ᶜ with hT_def
  have hTm : ∀ M, MeasurableSet (T M) := by
    intro M
    exact (MeasurableSet.biUnion (Finset.range M).countable_toSet fun i _ => hAsm i).compl
  have hTanti : Antitone T := by
    intro M N hMN
    simp only [hT_def]
    refine compl_subset_compl.2 ?_
    intro x hx
    simp only [mem_iUnion, Finset.mem_coe, Finset.mem_range, exists_prop] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, lt_of_lt_of_le hi hMN, hxi⟩
  have hTint : (⋂ M, T M) = (∅ : Set E) := by
    ext x
    simp only [mem_iInter, hT_def, mem_compl_iff, mem_iUnion, Finset.mem_coe,
      Finset.mem_range, mem_empty_iff_false, iff_false, not_forall, not_not, exists_prop]
    have hx : x ∈ ⋃ n, As n := by rw [hAsu]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact ⟨i + 1, i, by omega, hi⟩
  have htend : Tendsto (fun M => ν (T M)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun M => (hTm M).nullMeasurableSet) hTanti ⟨0, measure_ne_top _ _⟩
    rw [hTint] at h
    simpa [Function.comp_def] using h
  obtain ⟨M, hM⟩ : ∃ M, ν (T M) ≤ η :=
    ((htend.eventually (eventually_lt_nhds hη)).exists).imp fun _ h => h.le
  -- the pieces of positive mass, shifted so that `0` is free for the remainder
  set K : Finset ℕ := ((Finset.range M).filter fun i => ν (As i) ≠ 0).image (· + 1) with hK_def
  have hK0 : (0 : ℕ) ∉ K := by simp [hK_def]
  have hKmem : ∀ j ∈ K, j ≠ 0 ∧ j - 1 < M ∧ ν (As (j - 1)) ≠ 0 := by
    intro j hj
    simp only [hK_def, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨i, ⟨hiM, hi0⟩, rfl⟩ := hj
    exact ⟨by omega, by omega, by simpa using hi0⟩
  have hKmem' : ∀ i, i < M → ν (As i) ≠ 0 → i + 1 ∈ K := by
    intro i hiM hi0
    simp only [hK_def, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨i, ⟨hiM, hi0⟩, rfl⟩
  set U : Set E := ⋃ j ∈ K, As (j - 1) with hU_def
  have hUm : MeasurableSet U :=
    MeasurableSet.biUnion K.countable_toSet fun j _ => hAsm (j - 1)
  set A : ℕ → Set E := fun i => if i ∈ K then As (i - 1) else if i = 0 then Uᶜ else ∅
    with hA_def
  have hA0 : A 0 = Uᶜ := by simp [hA_def, hK0]
  have hAK : ∀ j ∈ K, A j = As (j - 1) := fun j hj => by simp [hA_def, hj]
  have hAout : ∀ i, i ≠ 0 → i ∉ K → A i = ∅ := fun i hi0 hiK => by simp [hA_def, hi0, hiK]
  have hAsub : ∀ j ∈ K, A j ⊆ U := by
    intro j hj
    rw [hAK j hj]
    exact subset_biUnion_of_mem (u := fun j => As (j - 1)) (by simpa using hj)
  refine ⟨K, A, hK0, ?_, ?_, ?_, ?_, hAout, ?_, ?_, ?_⟩
  · -- measurability
    intro i
    by_cases hi : i ∈ K
    · rw [hAK i hi]; exact hAsm _
    · by_cases hi0 : i = 0
      · rw [hi0, hA0]; exact hUm.compl
      · rw [hAout i hi0 hi]; exact MeasurableSet.empty
  · -- pairwise disjointness
    intro i j hij
    show Disjoint (A i) (A j)
    have key : ∀ a b : ℕ, a ≠ b → a ∈ K → Disjoint (A a) (A b) := by
      intro a b hab ha
      by_cases hb : b ∈ K
      · rw [hAK a ha, hAK b hb]
        refine hAsd ?_
        have h1 := (hKmem a ha).1
        have h2 := (hKmem b hb).1
        omega
      · by_cases hb0 : b = 0
        · rw [hb0, hA0]
          exact disjoint_compl_right_iff_subset.2 (hAsub a ha)
        · rw [hAout b hb0 hb]; exact disjoint_bot_right
    by_cases hi : i ∈ K
    · exact key i j hij hi
    · by_cases hj : j ∈ K
      · exact (key j i (Ne.symm hij) hj).symm
      · by_cases hi0 : i = 0
        · have hj0 : j ≠ 0 := fun h => hij (by rw [hi0, h])
          rw [hAout j hj0 hj]; exact disjoint_bot_right
        · rw [hAout i hi0 hi]; exact disjoint_bot_left
  · -- the family covers
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
      exact mem_iUnion.2 ⟨j, by rw [hAK j (by simpa using hj)]; exact hxj⟩
    · exact mem_iUnion.2 ⟨0, by rw [hA0]; exact hx⟩
  · -- null frontiers
    intro i
    by_cases hi : i ∈ K
    · rw [hAK i hi]; exact hAsfr _
    · by_cases hi0 : i = 0
      · rw [hi0, hA0, frontier_compl]
        refine measure_mono_null (frontier_biUnion_finset_subset K fun j => As (j - 1)) ?_
        exact (measure_biUnion_null_iff K.countable_toSet).2 fun j _ => hAsfr _
      · rw [hAout i hi0 hi]; simp
  · -- positive mass
    intro j hj
    rw [hAK j hj]
    exact pos_iff_ne_zero.2 (hKmem j hj).2.2
  · -- small diameter
    intro j hj
    rw [hAK j hj]
    exact hAsdiam _
  · -- the remainder is small
    rw [hA0]
    have hsub : (U : Set E)ᶜ ⊆ T M ∪ ⋃ i ∈ (Finset.range M).filter fun i => ν (As i) = 0, As i := by
      intro x hx
      by_cases hxT : x ∈ T M
      · exact Or.inl hxT
      · simp only [hT_def, mem_compl_iff, not_not] at hxT
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxT
        simp only [Finset.mem_coe, Finset.mem_range] at hi
        by_cases hz : ν (As i) = 0
        · refine Or.inr (mem_iUnion₂.2 ⟨i, ?_, hxi⟩)
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hz⟩
        · refine absurd (mem_iUnion₂.2 ⟨i + 1, ?_, ?_⟩) hx
          · simpa using hKmem' i hi hz
          · simpa using hxi
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    have hnull : ν (⋃ i ∈ (Finset.range M).filter fun i => ν (As i) = 0, As i) = 0 :=
      (measure_biUnion_null_iff (Finset.finite_toSet _).countable).2 <| by
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
        exact hi.2
    rw [hnull, add_zero]
    exact hM

end MeasureTheory
