/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Journal.Notes.DiscreteMeasure.Uniform
--import Journal.Notes.DiscreteMeasure.Sequence

/-!
# DiscreteMeasure: Hypergeometric distribution

We define the hypergeometric distribution `hypergeometric K L n` as a `DiscreteMeasure ℕ`,
where `hypergeometric K L n k ` is the probability of getting exactly `k` black balls when drawin `n` balls from an urn with `K` black and `L` non-black balls without replacement.

-/

open MeasureTheory ProbabilityTheory Measure Function Finset unitInterval

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

/-- An urn is a finite collection of balls of various colors. The colors form a finite
type `ι`, and `card i` gives the number of balls of color `i`. -/
structure urn (ι : Type*) [Fintype ι] where
  card : ι → ℕ

variable {ι : Type*} [Fintype ι]

/-- The type of all balls in the urn: a pair `⟨color, index⟩` where `color : ι` is the
color and `index : Fin (u.card color)` identifies the ball within that color. -/
@[reducible] def urn.toSet (u : urn ι) : Type _ := Σ i : ι, Fin (u.card i)

instance (u : urn ι) : Fintype u.toSet := Sigma.instFintype

/-- The color of a ball. -/
def color {u : urn ι} (x : u.toSet) : ι := x.1

/-- The total number of balls equals the sum over all colors. -/
lemma card_toSet (u : urn ι) : Fintype.card u.toSet = ∑ i, u.card i := by
  unfold urn.toSet
  rw [Fintype.card_sigma]
  simp

/-- The set of `n`-element subsets of the urn (drawing `n` balls without replacement). -/
def urn.draw (u : urn ι) (n : ℕ) : Finset (Finset u.toSet) :=
  Finset.powersetCard n Finset.univ

lemma urn.draw_mem (u : urn ι) (n : ℕ) (s : Finset u.toSet) : s ∈ u.draw n ↔ #s = n := by simp [urn.draw]

/-- The number of `n`-element draws from an urn with `N` balls is `N.choose n`. -/
lemma card_draw (u : urn ι) (n : ℕ) :
    (u.draw n).card = (∑ i, u.card i).choose n := by
  rw [urn.draw, Finset.card_powersetCard, Finset.card_univ, card_toSet]

/-- The set of draws is nonempty when `n` does not exceed the total number of balls. -/
lemma draw_nonempty (u : urn ι) (n : ℕ) (hn : n ≤ ∑ i, u.card i) :
    (u.draw n).Nonempty := by
  rw [← Finset.card_pos, card_draw]
  exact Nat.choose_pos hn

namespace MeasureTheory

namespace DiscreteMeasure

open _root_.MeasureTheory.DiscreteMeasure

lemma urn.nonempty_draw (K L n : ℕ) (hn : n ≤ K + L) : Nonempty (({ card := fun b => if b = true then K else L } : urn Bool).draw n)
 := (draw_nonempty _ n (by simp [hn])).to_subtype

/-- The hypergeometric distribution with parameters `K`, `N`, and `n`: drawing `n` balls
without replacement from an urn with `K` black and `N - K` non-black balls, returning
the number of black balls drawn. -/
noncomputable def hypergeometric (K L n : ℕ) :
    DiscreteMeasure ℕ :=
  do
    let X ← uniform (ι := (⟨fun b ↦ if b then K else L⟩ : urn Bool).draw n)
    return (X.val.1.map color).count true

open Classical in
theorem hypergeometric_hasSum (K L n : ℕ) (h : n ≤ K + L) : HasSum (hypergeometric K L n).weight 1 := by
  haveI := inhabited_of_nonempty <|urn.nonempty_draw K L n h
  simp [hypergeometric]
  apply hasSum_map
  apply hasSum_uniform

/-- For each color `i`, the set of `n i`-element subsets of balls of color `i`. -/
def urn.colorDraw [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (i : ι) : Finset (Finset (Fin (u.card i))) :=
  Finset.powersetCard (n i) Finset.univ

lemma urn.colorDraw_mem [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (i : ι) (s :  (Finset (Fin (u.card i)))) : s ∈ urn.colorDraw u n i ↔ s.card = n i := by
  simp [urn.colorDraw]

/-- A colored draw: independently choose `n i` balls of each color `i`.
This is a `piFinset` of per-color draws. -/
def urn.coloredDraw [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    Finset (∀ i, Finset (Fin (u.card i))) :=
  Fintype.piFinset (u.colorDraw n)

lemma urn.coloredDraw_mem [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (s : (i : ι) → Finset (Fin (u.card i))) : s ∈ urn.coloredDraw u n ↔ ∀ i, #(s i) = n i := by
  simp_rw [coloredDraw, Fintype.mem_piFinset, urn.colorDraw_mem]

example [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (f : (i : ι) → Finset (Fin (u.card i))) (hf : f ∈ urn.coloredDraw u n) (i : ι): #(f i) = n i := by
  simpa [urn.colorDraw] using (Fintype.mem_piFinset.mp hf i)


/-- The cardinality of coloredDraw is `∏ i, (u.card i).choose (n i)` — immediate from piFinset. -/
lemma card_coloredDraw [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    (u.coloredDraw n).card = ∏ i, (u.card i).choose (n i) := by
  simp [urn.coloredDraw, urn.colorDraw, Fintype.card_piFinset, Finset.card_powersetCard]

-- Helper: extract balls of a given color from a draw
private noncomputable def extractColor [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) (i : ι) :
    Finset (Fin (u.card i)) :=
      { j | ⟨i, j⟩ ∈ d}
  --d.preimage (fun j => (⟨i, j⟩ : u.toSet)) (by intro a _ b _ h; cases h; rfl)

-- Helper: reassemble per-color choices into a single draw
private noncomputable def assembleColor [DecidableEq ι] {u : urn ι} (f : ∀ i, Finset (Fin (u.card i))) :
    Finset u.toSet :=
  (Finset.univ (α := ι)).sigma f

private lemma mem_assembleColor [DecidableEq ι] {u : urn ι} {f : ∀ i, Finset (Fin (u.card i))}
    {x : u.toSet} : x ∈ assembleColor f ↔ x.2 ∈ f x.1 := by
  simp [assembleColor]

private lemma mem_extractColor [DecidableEq ι] {u : urn ι} {d : Finset u.toSet}
    {i : ι} {j : Fin (u.card i)} : j ∈ extractColor d i ↔ (⟨i, j⟩ : u.toSet) ∈ d := by
  simp [extractColor]

private lemma assembleColor_extractColor [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) :
    assembleColor (extractColor d) = d := by
  ext ⟨i, j⟩
  rw [mem_assembleColor, mem_extractColor]

private lemma extractColor_assembleColor [DecidableEq ι] {u : urn ι}
    (f : ∀ i, Finset (Fin (u.card i))) :
    extractColor (assembleColor f) = f := by
  ext i j
  rw [mem_extractColor, mem_assembleColor]

lemma extractColor_mem_coloredDraw [ DecidableEq ι] (u : urn ι) (n : ι → ℕ) (d : Finset u.toSet) (h : ∀ (i : ι), (extractColor d i).card = n i) : extractColor d ∈ urn.coloredDraw u n := by
  simp [urn.coloredDraw, urn.colorDraw, h]

example [DecidableEq ι
] (n : ι → ℕ): f ∈ urn.coloredDraw u n
↔ assembleColor f ∈ u.draw (∑ i, n i) := by
  simp [urn.coloredDraw_mem, urn.draw_mem]


  sorry


private lemma count_eq_extractColor_card [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) (i : ι) :
    (d.val.map color).count i = (extractColor d i).card := by
  rw [Multiset.count_map]
  calc
    _ = (d.filter (fun x => x.1 = i)).card := by simp_rw [Finset.card, Finset.filter_val, color, eq_comm]
    _ = ((extractColor d i).map
      ⟨fun j => (⟨i, j⟩ : u.toSet), fun _ _ h => by simpa using h⟩).card := by
          congr; ext ⟨i', j'⟩; rw [extractColor]; aesop
    _ = (extractColor d i).card := by
      rw [Finset.card_map]

private lemma assembleColor_card [DecidableEq ι] {u : urn ι}
    (f : ∀ i, Finset (Fin (u.card i))) :
    (assembleColor f).card = ∑ i, (f i).card := by
  rw [assembleColor, Finset.card_sigma]

/-- Bijection between draws with fixed color counts and coloredDraw (piFinset). -/
lemma card_filter_draw_eq_coloredDraw [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    #{d ∈ u.draw (∑ i, n i) | ∀ i, (extractColor d i).card = n i} =
    (u.coloredDraw n).card := by
  apply Finset.card_bij'
    (i := fun d _ => extractColor d)
    (j := fun f _ => assembleColor f)
    (hi := fun d hd => by
      simp only [mem_filter] at hd
      exact extractColor_mem_coloredDraw u n d hd.2)
    (hj := fun f hf => by
      simp [urn.coloredDraw_mem] at hf
      simp [urn.draw_mem, extractColor_assembleColor, assembleColor_card, hf])
    (left_inv := fun d _ => assembleColor_extractColor d)
    (right_inv := fun f _ => (extractColor_assembleColor _))

/-- The number of draws with fixed color counts equals `∏ i, (u.card i).choose (n i)`. -/
lemma cases_card [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    #{d ∈ u.draw (∑ i, n i) | ∀ i, (d.val.map color).count i = n i} =
    ∏ i, (u.card i).choose (n i) := by
  simp_rw [count_eq_extractColor_card]
  rw [card_filter_draw_eq_coloredDraw, card_coloredDraw]


theorem hypergeometric_weight (K L n k : ℕ) (h : n ≤ K + L) :
    (hypergeometric K L n).weight k =
    (K.choose k * L.choose (n - k)) / ((K + L).choose n) := by
  haveI := inhabited_of_nonempty (urn.nonempty_draw K L n h)
  let u : urn Bool := ⟨fun b ↦ if b then K else L⟩
  -- hypergeometric unfolds to: (uniform.map f).weight k
  -- where f X = (X.val.1.map color).count true
  -- hypergeometric = Bind.bind uniform (Pure.pure ∘ f)
  -- First convert Bind.bind/Pure.pure to DiscreteMeasure.bind/pure
  -- hypergeometric K L n = (fun X => f X) <$> uniform = map f uniform
  -- So (hypergeometric K L n).weight k = ∑' X, uniform X * [f X = k]
  -- Directly compute using binom_eq_count_true-style approach
  -- hypergeometric K L n = (fun X => f X) <$> uniform
  -- weight k = #{X ∈ u.draw n | f X = k} / #(u.draw n)
  -- Use the monad-to-tsum lemma
  -- The key computation: unfold everything to a sum
  -- General lemma: (Bind.bind μ f).weight k = ∑' x, μ.weight x * (f x).weight k
  -- This is because Bind.bind = DiscreteMeasure.bind by the Monad instance
  have bind_weight : ∀ {α β : Type} (μ : DiscreteMeasure α)
      (f : α → DiscreteMeasure β) (y : β),
      (Bind.bind μ f : DiscreteMeasure β).weight y =
      ∑' x, μ.weight x * (f x).weight y := fun μ f y => by
    show (DiscreteMeasure.bind μ f) y = _
    rw [bind_apply]; rfl
  simp only [hypergeometric, bind_weight]
  -- Goal: ∑' x, uniform.weight x * (Pure.pure (f x)).weight k = ...
  -- Step 1: uniform.weight = const 1/#univ
  simp_rw [show ∀ X : ↥(u.draw n), uniform.weight X =
    ((Finset.univ : Finset ↥(u.draw n)).card : ℝ≥0∞)⁻¹ from fun _ => rfl]
  rw [ENNReal.tsum_mul_left]
  -- Step 2: Pure.pure m k = if m = k then 1 else 0
  have pure_weight : ∀ (m : ℕ), (Pure.pure m : DiscreteMeasure ℕ).weight k =
      if m = k then 1 else 0 := by
    intro m; show (DiscreteMeasure.pure m).weight k = _
    unfold DiscreteMeasure.pure; simp [Pi.single_apply, eq_comm]
  simp_rw [pure_weight]
  -- Step 3: ∑' x, if f x = k then 1 else 0 = #{x | f x = k}
  rw [tsum_fintype, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  -- Rewrite #univ = #(u.draw n) = (K+L).choose n
  rw [show Finset.card (Finset.univ : Finset ↥(u.draw n)) = (K + L).choose n from by
    rw [Finset.card_univ, Fintype.card_coe]; exact card_draw u n]
  -- Rewrite #{x | f x = k} using cases_card
  -- This requires relating the Finset.filter to cases_card
  -- a⁻¹ * b = b / a
  rw [mul_comm, ENNReal.div_eq_inv_mul]
  sorry

end DiscreteMeasure

end MeasureTheory
