/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Journal.Notes.DiscreteMeasure.Monad

/-!
# DiscreteMeasure: Bernoulli distribution (coin) and uniform distribution

We define `coin p` as the Bernoulli distribution with parameter `p : unitInterval`, i.e., the
`DiscreteMeasure Bool` with `coin p true = ENNReal.ofReal p` and `coin p false = ENNReal.ofReal (1 - p)`.
We prove basic properties, including that it is a probability measure.
We also define a `uniform` distribution on finite types.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section coin

open Bool ENNReal NNReal unitInterval

noncomputable def coin (p : unitInterval) : DiscreteMeasure Bool where weight := fun
  | true => ENNReal.ofReal p
  | false => ENNReal.ofReal (symm p)

lemma coin_apply (p : unitInterval) (b : Bool) : (coin p) b = if b then ENNReal.ofReal p else ENNReal.ofReal  (symm p) := by
  by_cases h : b <;> simp only [h] <;> rfl

lemma coin_apply_true (p : unitInterval) : (coin p) true = ENNReal.ofReal p := by
  rfl

lemma coin_apply_false (p : unitInterval) : (coin p) false = ENNReal.ofReal (symm p) := by
  rfl

@[simp]
lemma unitInterval.sum_symm_self {p : unitInterval} :
ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.prop.2) p.prop.1]
  simp [sub_add_cancel]

lemma hasSum_coin (p : unitInterval) : HasSum (coin p) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, tsum_bool]
  rw [coin_apply, coin_apply]
  simp

instance isProbabilityMeasure_coin (p : unitInterval) : IsProbabilityMeasure (coin p).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr <| hasSum_coin p

lemma lintegral_coin_id (p : unitInterval) (g : Bool → ℝ≥0∞) : ∫⁻ (a : Bool), (g a) ∂ (coin p).toMeasure = ENNReal.ofReal (1 - p) * (g false) + ENNReal.ofReal p * (g true) := by
  rw [lintegral_eq_toMeasure]
  rw [tsum_bool, coin_apply, coin_apply]
  simp

lemma lintegral_coin (p : unitInterval) : ∫⁻ (a : Bool), ({true} : Set Bool).indicator 1 a ∂ (coin p).toMeasure = ENNReal.ofReal p := by
  rw [lintegral_coin_id]
  simp

lemma Bool_hasSum_not (μ : DiscreteMeasure Bool) (hμ : HasSum μ 1) (b : Bool) : μ (!b) = 1 - μ b := by
  refine ENNReal.eq_sub_of_add_eq' one_ne_top ?_
  rw [Summable.hasSum_iff ENNReal.summable, tsum_bool] at hμ
  cases' b with h
  · rw [add_comm] ; simp [hμ]
  · simp [hμ]

lemma Bool_ext {μ ν : DiscreteMeasure Bool} (hμ : HasSum μ 1) (hν : HasSum ν 1) (b : Bool) (h : μ b = ν b) : μ = ν := by
  ext a
  cases h' : decide (b = a)
  · rw [decide_eq_false_iff_not, ← ne_eq b a, ← not_eq] at h'
    rw [← h', Bool_hasSum_not μ hμ b, Bool_hasSum_not ν hν b, h]
  · simp only [decide_eq_true_eq] at h'
    rw [← h', h]

lemma coin_not' (p : unitInterval) : (coin p).map not = coin (unitInterval.symm p) := by
  apply Bool_ext (hasSum_map (hasSum_coin p) not) (hasSum_coin (unitInterval.symm p)) true
  change map not (coin p) true = _
  rw [coin_apply_true, map_eq_of_inj (coin p) not Bool.not_injective false true Bool.not_false]
  rw [coin_apply_false, unitInterval.coe_symm_eq]

@[simp]
lemma Bool_and : Bool.and true = id := by
  rfl

/-
@[simp]
lemma Bool_false : Bool.and false = (fun _ ↦ false) := rfl

def List.Vector.all {n : ℕ} (l : List.Vector α n) (f : α → Bool) : Bool := l.toList.all f

def List.Vector.any {n : ℕ} (l : List.Vector α n) (f : α → Bool) : Bool := l.toList.any f

lemma List.Vector.all_id_preimage_true {n : ℕ} : (flip List.Vector.all id)⁻¹' {true} = {List.Vector.replicate n true} := by
  ext x
  sorry

lemma List.Vector.ext {n : ℕ} (l : List α) (l' : List.Vector α n) : l = l'.toList ↔ ∃ (h : l.length = n),  ∀ (i : Fin l.length), l.get i = l'.get (h ▸ i) := by
  sorry

example (l : List ℝ≥0∞) : l.prod = ∏ i, l.get i := by
  simp only [List.get_eq_getElem, Fin.prod_univ_getElem]

lemma multipleCoins_and_eq_coin {n : ℕ} (p : List.Vector ℝ≥0∞ n) (hp : ∀ i, p.get i ≤ 1) : map (flip List.Vector.all id) (sequence (t := flip List.Vector n) (List.Vector.map coin p)) = coin (p.toList.prod) := by
  haveI h₁ : IsProbabilityMeasure (map (flip List.Vector.all id) (sequence (t := flip List.Vector n) (List.Vector.map coin p))).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p.toList.prod)).toMeasure := by
    apply isProbabilityMeasure_coin
    have g : ∀ i, p.toList.get i ≤ 1 := by sorry
    simp [g]


    sorry
  apply Bool_ext _ _ true
  obtain ⟨p1, p2⟩ := p
  subst p2
  rw [map_apply]
  rw [List.Vector.all_id_preimage_true]
  rw [toMeasure_apply_singleton]
  rw [sequence_apply₁]
  simp [coin]
  rw [← Fin.prod_univ_getElem]
  exact rfl



/- multiple coins-/
lemma multipleCoins_and_eq_coin' {n : ℕ} (p : List ℝ≥0 ) (hp : ∀ i, p.get i ≤ 1) : (p.map coin).andM = coin (p.prod) := by
  haveI h₁ : IsProbabilityMeasure (List.andM (p.map coin)).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p.prod)).toMeasure := by sorry
  apply Bool_ext _ _ true
  simp only [List.pure_def, List.bind_eq_flatMap]



  sorry




lemma twoCoins_and_eq_coin (p q : ℝ≥0) (hp : p ≤ 1) (hq _: q ≤ 1) : Bool.and <$> (coin p)  <*>  (coin q) = coin (p * q) := by
  simp [monad_norm]
  haveI h₁ : IsProbabilityMeasure ((coin ↑p >>= fun x => coin ↑q >>= Pure.pure ∘ x.and)).toMeasure := by sorry
  haveI h₂ : IsProbabilityMeasure (coin (p * q)).toMeasure := by sorry
  apply Bool_ext _ _ true
  simp_rw [← bind_eq_bind, bind_apply, tsum_bool]
  simp [coin]
  rw [← pure_eq_pure, pure_apply, Set.indicator]
  simp


-- now we come to multiple coins
lemma sequence_coin_apply (p : ℝ≥0∞) (n : ℕ) (l : List.Vector Bool n) : (iidSequence n (coin p)) l = p ^ (List.Vector.countFin true l).val * (1 - p) ^ (List.Vector.countFin false l).val := by
  rw [iidSequence_apply₂ n (coin p)]
  simp [coin]

lemma massFunctionBool_eq_coin (P : DiscreteMeasure Bool) [IsProbabilityMeasure P.toMeasure] : P = coin (P true) := by
  haveI h : IsProbabilityMeasure (coin (P true)).toMeasure := isProbabilityMeasure_coin (P true) (apply_le_one true)
  exact Bool_ext P (coin (P true)) true (by rfl)
-/
end coin

/-
section uniform

variable {ι : Type*} [Fintype ι] [Inhabited ι]

def uniform : DiscreteMeasure ι := fun _ ↦ (Finset.univ : Finset ι).card⁻¹

lemma isProbabilityMeasure_uniform : IsProbabilityMeasure (uniform (ι := ι)).toMeasure := by
  rw [isProbabilityMeasure_iff_tsumOne]
  simp [uniform]
  refine ENNReal.mul_inv_cancel ?_ ?_
  simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  simp

end uniform

-/

end DiscreteMeasure

end MeasureTheory
