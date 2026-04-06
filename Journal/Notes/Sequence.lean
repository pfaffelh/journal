/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Journal.Notes.DiscreteMeasure.Monad

/-!
# DiscreteMeasure: Sequences and i.i.d. sequences

We define `sequence` for `DiscreteMeasure`s on `List.Vector`s, and `iidSequence` for
independent and identically distributed sequences. We prove formulas for
evaluating these at specific vectors.
-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section sequence

-- `DiscreteMeasure`s on lists

-- MF
lemma cons_map_seq_apply {n : ℕ} (μs : DiscreteMeasure (List.Vector α n)) (ν : DiscreteMeasure α) (l : List.Vector α (n + 1)): (List.Vector.cons <$> ν <*> μs) l = ∑' (a' : α), ν a' * ∑' (l' : List.Vector α n), μs l' * pure (a' ::ᵥ l') l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]

lemma pure_cons_apply_cons [DecidableEq α] {n : ℕ} (a a' : α) (l l' : List.Vector α n) : pure (a' ::ᵥ l') (a ::ᵥ l) = (pure a' a) * (pure l' l) := by
  repeat rw [pure_apply, Set.indicator]
  aesop

-- MF
lemma cons_map_seq_apply_cons [DecidableEq α] {n : ℕ} (μs : DiscreteMeasure (List.Vector α n)) (ν : DiscreteMeasure α) (l : List.Vector α n) (a : α) : (List.Vector.cons <$> ν <*> μs) (a ::ᵥ l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [pure_cons_apply_cons, ← mul_assoc, pure_comm]
  conv => left; left; intro a'; right; left; intro l'; rw [mul_assoc]; right; rw [mul_comm]
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ← mul_assoc, tsum_pure]

-- MF
lemma sequence_cons_eq_seq_sequence [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (ν : DiscreteMeasure α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) = (List.Vector.cons <$> ν <*> sequence (t := flip List.Vector n) μs) := by
  rw [sequence, sequence, List.Vector.traverse_cons id]
  simp

-- lemma traverse_cons_eq_seq_traverse [DecidableEq α] {n : ℕ} (f : α → DiscreteMeasure β) (μs : List.Vector α n) (ν : α) : (traverse (t := flip List.Vector (n + 1)) (m := DiscreteMeasure) f (ν ::ᵥ μs)) = (List.Vector.cons <$> (f ν) <*> traverse (t := flip List.Vector n) (m := DiscreteMeasure) f μs) := by
--  rw [sequence, sequence, List.Vector.traverse_cons id]
--  simp

lemma sequence_cons_apply_cons [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (ν : DiscreteMeasure α) (l : List.Vector α n) (a : α) : (sequence (t := flip List.Vector (n + 1)) (ν ::ᵥ μs)) (a ::ᵥ l) = (ν a) * ((sequence (t := flip List.Vector n) μs) l) := by
  rw [List.Vector.sequence_cons]
  exact cons_map_seq_apply_cons (sequence (t := flip List.Vector n) μs) ν l a

lemma zipWith_to_ofFn {n : ℕ} (f : List.Vector (α → ℝ≥0∞) n) (l : List.Vector α n) : (f.zipWith (· ·) l).toList = List.ofFn (fun i => (f.get i) (l.get i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.Vector.zipWith_toList, List.getElem_zipWith]
    rfl

lemma prod_zipWith {n : ℕ} (f : List.Vector (α → ℝ≥0∞) n) (l : List.Vector α n) : List.prod (f.zipWith (· ·) l).toList = ∏ i, (f.get i) (l.get i) := by
  rw [zipWith_to_ofFn, List.prod_ofFn]



set_option backward.isDefEq.respectTransparency false

lemma sequence_apply₀ [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (l : flip List.Vector n α) :
    (sequence (t := flip List.Vector n) μs) l = List.prod (μs.zipWith (· ·) l).toList :=
  by
  induction μs with
  | nil =>
    simp only [List.Vector.nil_iff, List.Vector.sequence_nil]
    rw [← pure_eq_pure]
    rw [pure_apply_self]
    simp
  | cons hl =>
    rw [← List.Vector.cons_head_tail l, sequence_cons_apply_cons]
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one,
      List.Vector.zipWith_toList, List.Vector.toList_cons]
    rw [List.zipWith_cons_cons]
    simp [hl]

lemma sequence_apply₁ [DecidableEq α] {n : ℕ} (μs : List.Vector (DiscreteMeasure α) n) (l : flip List.Vector n α) :
    sequence (t := flip List.Vector n) μs l = ∏ i, (List.Vector.get μs i) (List.Vector.get l i) :=
  by
  rw [sequence_apply₀]
  have h : List.Vector.zipWith (fun x1 x2 => x1 x2) μs l = List.Vector.zipWith (fun x1 x2 => x1 x2) (List.Vector.map (fun x ↦ x.weight) μs) l := by
    rw [List.Vector.ext_iff]
    simp
  rw [h, prod_zipWith]
  simp

-- TODO: define marginal distributions

lemma hasSum_sequence {n : ℕ} [DecidableEq α] {μs : List.Vector (DiscreteMeasure α) n} (hμ : ∀ i, HasSum (μs.get i).weight 1) : HasSum (sequence (t := flip List.Vector n) μs) 1 := by
  induction n with
  | zero =>
    simp [monad_norm]
    simp_rw [← pure_eq_pure]
    apply hasSum_pure
  | succ n hn =>
    rw [← List.Vector.cons_head_tail μs, List.Vector.sequence_cons, ← seq_eq_seq, ← map_eq_map, ← List.Vector.get_zero μs]
    have h (i : Fin n) : HasSum (μs.tail.get i).weight 1 := by
      rw [List.Vector.get_tail]
      simp [hμ]
    apply @hasSum_seq (β := List.Vector α n.succ) (α := List.Vector α n)
      (q := map (β := List.Vector α n → List.Vector α n.succ) (α := α) List.Vector.cons (μs.get 0))
      (p := fun (_ : Unit) ↦ sequence (t := flip List.Vector n) μs.tail) (hasSum_map (hμ 0) List.Vector.cons) (@hn μs.tail h)

lemma isProbabilityMeasure_sequence_toMeasure {n : ℕ} [MeasurableSpace (flip List.Vector n α)] [MeasurableSingletonClass (flip List.Vector n α)] [DecidableEq α] (μs : List.Vector (DiscreteMeasure α) n) {hμ : ∀ i, HasSum (μs.get i).weight 1} : IsProbabilityMeasure (sequence (t := flip List.Vector n) μs).toMeasure := by
  exact isProbabilityMeasure_iff_hasSum.mpr <| hasSum_sequence hμ

end sequence

section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : DiscreteMeasure α) : DiscreteMeasure (flip List.Vector n α) := sequence (t := flip List.Vector n) (List.Vector.replicate n μ)

lemma iidSequence_apply [DecidableEq α] (n : ℕ) (μ : DiscreteMeasure α) (l : flip List.Vector n α) :
    (iidSequence n μ) l = (l.map μ).toList.prod := by
  have h : n = (List.map (⇑μ) (List.Vector.toList l)).length := by simp
  rw [iidSequence, sequence_apply₁, List.Vector.toList_map]
  simp only [List.Vector.get_replicate]
  rw [← Fin.prod_univ_getElem (List.map (⇑μ) l.toList)]
  congr
  simp_rw [List.getElem_map, Fin.heq_fun_iff h]
  exact congrFun rfl

lemma iidSequence_apply₁ {n : ℕ} {μ : DiscreteMeasure α} [DecidableEq α] {l : List.Vector α n} :
    iidSequence n μ l = (∏ a ∈ l.toList.toFinset, (μ a) ^ (List.Vector.countFin a l).val) := by
  rw [iidSequence_apply n μ l]
  rw [List.Vector.toList_map]
  simp_rw [List.Vector.countFin]
  exact Finset.prod_list_map_count l.toList μ

lemma iidSequence_apply₂ (n : ℕ) (μ : DiscreteMeasure α) [DecidableEq α] (l : List.Vector α n) :
    iidSequence n μ l = (∏' (a : α), (μ a) ^ (List.Vector.countFin a l).val) := by
  simp_rw [List.Vector.countFin]
  have hf : ∀ b ∉ l.toList.toFinset, μ b ^ (l.toList.count b) = 1 := by
    simp_rw [List.mem_toFinset, ← List.count_eq_zero]
    exact fun b hb ↦ hb ▸ pow_zero (μ b)
  rw [tprod_eq_prod hf]
  exact iidSequence_apply₁

lemma pure_sequence (ν : DiscreteMeasure α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : DiscreteMeasure α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

lemma iidSequence_cons (ν : DiscreteMeasure α) : (ν >>= fun y => (iidSequence n ν) >>= fun x => pure (x.cons y)) = iidSequence (n+1) ν := by
  simp [monad_norm, iidSequence]
  rfl

end iidSequence

end DiscreteMeasure

end MeasureTheory
