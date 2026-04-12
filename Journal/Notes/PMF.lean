import Mathlib
-- import Journal.Notes.DiscreteMeasure

/- We extend `PMF`s in order to be more useful.

We have the following plan:

`PMF` has a function `toDiscreteMeasure` that turns a `PMF α` into a `DiscreteMeasure α`.

`PMF` has a function `toProbabilityMeasure` that turns a `PMF α` into a `DiscreteMeasure α`.

`PMF` coerces to `Measure`.

We avoid `PMF.toOuterMeasure` because `OuterMeasure` is not very useful.



-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

#check PMF

namespace PMF

noncomputable def binomial_real (p : ℝ≥0) (h : p ≤ 1)(n : ℕ) : PMF ℝ := Nat.cast <$> PMF.binomial p h n


#check geometricPMF α → ℝ≥0∞

lemma hp_pos (p q : ℝ) (hp₁ : 0 < p) (hp₂ : p ≤ 1) (hq₁ : 0 < q) (hq₂ : q ≤ 1) : 0 < 1 - (1 - p) * (1 - q) := by
  sorry

lemma hp_le_one (p q : ℝ) (hp₁ : 0 < p) (hp₂ : p ≤ 1) (hq₁ : 0 < q) (hq₂ : q ≤ 1) : 1 - (1 - p) * (1 - q) ≤ 1 := by
  sorry

example (p q : ℝ) (hp₁ : 0 < p) (hp₂ : p ≤ 1) (hq₁ : 0 < q) (hq₂ : q ≤ 1) : geometricPMF (p := 1 - (1 - p) * (1 - q)) (hp_pos p q hp₁ hp₂ hq₁ hq₂) (hp_le_one p q hp₁ hp₂ hq₁ hq₂) =
  do
    let X ← geometricPMF hp₁ hp₂
    let Y ← geometricPMF hq₁ hq₂
    return min X Y := by
  sorry

def toDiscreteMeasure {α : Type*} (p : PMF α) : DiscreteMeasure α where
  weight := p

/-- This function replaces to `PMF.toOuterMeasure` construction. -/
noncomputable def toMeasure' (p : PMF α) : @Measure α ⊤ := sum (fun a ↦ (p a) • @Measure.dirac α ⊤ a)

noncomputable instance : Coe (PMF α) (@Measure α ⊤) where
  coe p : @Measure α ⊤ := p.toMeasure

noncomputable instance : CoeFun (PMF α) (fun _ => Set α → ℝ≥0∞) where
  coe p := p.toMeasure'



#check PMF.toMeasure

end PMF
