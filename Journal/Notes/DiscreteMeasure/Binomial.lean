/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Journal.Notes.DiscreteMeasure.Bernoulli
import Journal.Notes.DiscreteMeasure.Sequence

/-!
# DiscreteMeasure: Binomial distribution

We define the binomial distribution `binom p n` as a `DiscreteMeasure ℕ`,
where `binom p n k` is the probability of getting exactly `k` successes in `n`
independent coin flips with success probability `p`.

The definition is inductive: `binom p 0 = pure 0` and
`binom p (n+1) = coin p >>= fun X => binom p n >>= fun Y => pure (Bool.toNat X + Y)`.

We prove the classical binomial formula:
`binom p n k = p ^ k * (1 - p) ^ (n - k) * (n.choose k)`.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset unitInterval

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section binom

/-- The binomial distribution with parameters `p` and `n`, as a `DiscreteMeasure ℕ`. -/
noncomputable def binom (p : unitInterval) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)

@[simp]
lemma binom_zero (p : unitInterval) : binom p 0 = pure 0 := rfl

lemma binom_succ (p : unitInterval) (n : ℕ) :
    binom p (n + 1) = (coin p) >>= fun X => binom p n >>= fun Y => pure (X.toNat + Y) := rfl

lemma hasSum_binom (p : unitInterval) (n : ℕ) : HasSum (binom p n) 1 := by
  induction n with
  | zero => exact hasSum_pure 0
  | succ n hn =>
    exact hasSum_bind (hasSum_coin p) (fun a _ => hasSum_bind hn (fun b _ => hasSum_pure _))

lemma isProbabilityMeasure_binom (p : unitInterval) (n : ℕ) :
    IsProbabilityMeasure (binom p n).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr (hasSum_binom p n)

lemma binom_seq (p : unitInterval) (n : ℕ) : binom p (n + 1) =
(fun b x ↦ b.toNat + x) <$> (coin p) <*> (binom p n) := by
  simp_rw [← seq_eq_seq, ← map_eq_map, binom, ← bind_eq_bind, bind_map_eq_seq, ← bind_pure_comp, bind_bind, pure_bind]

theorem binom_eq_count_true (p : unitInterval) (n : ℕ) : binom p n = (iidSequence n (coin p)).map (List.count true) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [binom_seq, hn, ← iidSequence_cons]
    simp only [monad_norm]
    simp [Bool.toNat, Bool.cond_eq_ite, add_comm,
      List.count_cons]


/-- `binom p n k = 0` when `k > n`, since we can't get more successes than trials. -/
lemma binom_eq_zero_of_gt (p : unitInterval) (n k : ℕ) (hk : n < k) : binom p n k = 0 := by
  induction n generalizing k with
  | zero =>
    simp only [binom]; exact pure_apply_nonself (by omega)
  | succ n ih =>
    change (coin p >>= fun X => binom p n >>= fun Y => pure (X.toNat + Y)) k = 0
    rw [← bind_eq_bind, bind_apply, ENNReal.tsum_eq_zero]
    intro b; apply mul_eq_zero_of_right
    rw [← bind_eq_bind, bind_apply, ENNReal.tsum_eq_zero]
    intro y
    by_cases hy : n < y
    · simp [ih y hy]
    · apply mul_eq_zero_of_right; rw [pure_apply_nonself]
      cases b <;> simp [Bool.toNat] <;> omega

open Finset

-- #34702
lemma List.card_idxsOf_toFinset_eq_count {α : Type*} [BEq α] (l : List α) (a : α) :
    (l.idxsOf a).toFinset.card = l.count a := by
  rw [List.card_toFinset, List.Nodup.dedup List.nodup_idxsOf, List.length_idxsOf]

-- #34702
lemma List.count_ofFn_eq_card [DecidableEq α] (n : ℕ) (f : Fin n → α) (a : α)
    [DecidablePred fun i ↦ f i = a] :
    List.count a (List.ofFn f) = Finset.card {i | f i = a} := by
  rw [← List.card_idxsOf_toFinset_eq_count]
  let s := {i | f i = a}.toFinset
  refine card_bij (fun b hb ↦ ⟨b, ?_⟩) (fun c hc ↦ ?_) (fun d hd1 hd2 hd3 ↦ ?_) (fun e he ↦ ?_)
  · aesop
  · simp only [List.mem_toFinset, List.mem_idxsOf_iff_getElem_sub_pos, Nat.zero_le, Nat.sub_zero,
    List.getElem_ofFn, beq_iff_eq, List.length_ofFn, true_and] at hc
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact Exists.elim hc fun a_1 a ↦ a
  · simp
  · aesop

-- #34702
/-- For some `Fintype ι`, there is (computably) a bijection `ι → Bool` and `Finset ι` by using
`s : Finset ι` as the set where the `f : ι → Bool` is `true`. -/
def Equiv.fnBool_finset {ι : Type*} [DecidableEq ι] [Fintype ι] : (ι → Bool) ≃ (Finset ι) where
  toFun := fun f ↦ Finset.univ.filter (f · = true)
  invFun := fun s i ↦ decide (i ∈ s)
  left_inv := fun l ↦ by simp
  right_inv := fun l ↦ by simp

-- #34702
lemma Equiv_fnBool_finset_mem_powersetCard_iff  {ι : Type*} [DecidableEq ι] [Fintype ι] (k : ℕ) (f : ι → Bool) :
    #{i | f i = true} = k ↔ (Equiv.fnBool_finset) f ∈ powersetCard k univ := by
  simp [Equiv.fnBool_finset]

-- #34702
/-- For some `Fintype ι`, the number of maps `f : ι → Bool` with `#{i | f i} = k` equals `n.choose k`. -/
lemma card_fnBool {ι : Type*} [DecidableEq ι] [Fintype ι] {k : ℕ} : #{ f : ι → Bool | #{i | f i} = k } = (univ : Finset ι).card.choose k := by
  rw [← card_powersetCard k (univ : Finset ι)]
  apply card_equiv (Equiv.fnBool_finset) (fun i ↦ ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact Equiv_fnBool_finset_mem_powersetCard_iff k i

-- #34702
lemma card_boolList_count {k n : ℕ} :
    #{v : List.Vector Bool n | v.toList.count true = k} = n.choose k := by
  rw [← card_fin n, ← card_fnBool, card_fin n]
  apply card_equiv (Equiv.vectorEquivFin _ n) (fun v ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Equiv.vectorEquivFin, Equiv.coe_fn_mk]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> rw [← h, ← List.count_ofFn_eq_card _ _ true] <;> congr <;>
  rw [← List.ofFn_get (l := v.toList)] <;> aesop

/-- The binomial formula: `binom p n k = C(n,k) * p^k * (1-p)^(n-k)`. -/
theorem binom_formula (p : unitInterval) (n k : ℕ) :
    binom p n k = (ENNReal.ofReal p) ^ k * (ENNReal.ofReal (symm p)) ^ (n - k) * (Nat.choose n k) := by
  induction n generalizing k with
  | zero =>
    simp only [binom]
    cases k with
    | zero => simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]; exact pure_apply_self
    | succ k =>
      simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero]
      exact pure_apply_nonself (by omega)
  | succ n ih =>
    change (coin p >>= fun X => binom p n >>= fun Y => pure (X.toNat + Y)) k = _
    rw [← bind_eq_bind, bind_apply]
    simp_rw [← bind_eq_bind, bind_apply]
    rw [tsum_bool]
    simp only [coin_apply, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.zero_add,
      Bool.toNat_true]
    -- Now LHS is: ofReal(symm p) * ∑' y, binom p n y * pure y k + ofReal p * ∑' y, binom p n y * pure (1 + y) k
    have hfalse : ∑' y, binom p n y * (DiscreteMeasure.pure y) k = binom p n k := by
      have : ∀ y, binom p n y * (DiscreteMeasure.pure y) k = if y = k then binom p n k else 0 := by
        intro y
        split_ifs with h
        · subst h; rw [pure_apply_self, mul_one]
        · rw [pure_apply_nonself (Ne.symm h), mul_zero]
      simp_rw [this, tsum_ite_eq]
    have htrue : ∑' y, binom p n y * (DiscreteMeasure.pure (1 + y)) k = if k = 0 then 0 else binom p n (k - 1) := by
      cases k with
      | zero =>
        simp only [ite_true]
        apply ENNReal.tsum_eq_zero.mpr
        intro y
        apply mul_eq_zero_of_right
        exact pure_apply_nonself (by omega)
      | succ k' =>
        rw [if_neg (by omega), show k' + 1 - 1 = k' from by omega]
        have : ∀ y, binom p n y * (DiscreteMeasure.pure (1 + y)) (k' + 1) = if y = k' then binom p n k' else 0 := by
          intro y
          by_cases h : y = k'
          · subst h
            rw [if_pos rfl, show 1 + y = y + 1 from by omega, pure_apply_self, mul_one]
          · rw [if_neg h]
            apply mul_eq_zero_of_right
            change (DiscreteMeasure.pure (1 + y)) (k' + 1) = 0
            exact pure_apply_nonself (show k' + 1 ≠ 1 + y from by omega)
        simp_rw [this, tsum_ite_eq]
    rw [hfalse, htrue]
    rw [ih]
    cases k with
    | zero =>
      simp only [ite_true, mul_zero, add_zero, pow_zero, one_mul, Nat.sub_zero,
        Nat.choose_zero_right, Nat.cast_one, mul_one]
      rw [pow_succ, mul_comm]
    | succ k =>
      rw [if_neg (by omega), show k + 1 - 1 = k from by omega]
      rw [ih]
      rw [Nat.choose_succ_succ]
      rw [show n + 1 - (k + 1) = n - k from by omega]
      by_cases hkn : k + 1 ≤ n
      · have hdk : n - (k + 1) = n - k - 1 := by omega
        rw [hdk]
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        rw [show n - k - 1 = m from by omega, hm]
        rw [pow_succ (ENNReal.ofReal (symm p)) m, pow_succ (ENNReal.ofReal p) k]
        push_cast
        ring
      · push_neg at hkn
        by_cases hkn' : k = n
        · subst hkn'
          simp only [Nat.sub_self, pow_zero, mul_one]
          have : Nat.choose k (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [this]; simp; rw [pow_succ]; ring
        · have h1 : Nat.choose n (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have h2 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [h1, h2]

theorem binom_eq_iidSequence (p : unitInterval) (n : ℕ) (k : ℕ) :
    binom p n k =
    ∑' (l : List Bool), iidSequence n (coin p) l *
      if l.count true = k then 1 else 0 := by
  sorry

instance : MeasurableSpace (List Bool) := ⊤

theorem binom_eq_iidSequence' (p : unitInterval) (n : ℕ) (k : ℕ) :
    binom p n k =
    (iidSequence n (coin p)).toMeasure {l | l.length = n ∧ l.count true = k} := by
  sorry

end binom

end DiscreteMeasure

end MeasureTheory
