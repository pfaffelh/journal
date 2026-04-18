import Mathlib

open MeasureTheory ProbabilityTheory unitInterval

section one

variable {R Ω : Type*} {m : MeasurableSpace Ω} {hM : MeasurableSpace R} [AddMonoidWithOne R] {X : Ω → ℝ}
  {P : Measure Ω} {n : ℕ} {p : I}

noncomputable instance cas : Coe (Measure ℕ) (@Measure R (by infer_instance)) where
  coe μ := μ.map Nat.cast

example (hX : HasLaw X (binomial n p) P) : True := sorry

example (hX : HasLaw X ((binomial n p : Measure ℕ)) P) : True := sorry

example (hX : HasLaw X Bin(ℝ, n, p) P) : True := sorry

example (hX : HasLaw X (binomial n p : Measure ℝ) P) : True := sorry

example (hX : HasLaw X Bin(ℝ, n, p) P) : True := sorry


#check HasLaw X (binomial n p) P

end one

section two

structure HasLaw {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} [m𝓧 : MeasurableSpace 𝓧] (X : Ω → 𝓧) (μ : Measure 𝓧) (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

example {X : Ω → ℕ} {n : ℕ} {p : I} (hX : _root_.HasLaw X (binomial n p) P) : True := sorry

end two

open ENNReal

example (f : Bool → ℝ≥0∞) : ∏ b, f b = f true * f false := by
  rw [Fintype.prod_bool]

-- Versuch: Type : Type ?
example : False := by
  have : Type = Type := rfl
  -- Lean verhindert Type : Type strikt; Girard's Paradox nicht reproduzierbar.
  sorry
