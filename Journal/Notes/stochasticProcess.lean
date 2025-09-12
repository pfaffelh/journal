import Mathlib

open MeasureTheory

namespace ProbabilityTheory

structure IsStochasticProcess {T Ω : Type*} {α : T → Type*} [MeasurableSpace Ω] (P : Measure Ω) [measα : ∀ t, MeasurableSpace (α t)] (X : (t : T) → Ω → (α t)) : Prop where
  protected aemeasurable : ∀ t : T, AEMeasurable (X t) P := by fun_prop

namespace IsStochasticProcess

variable {T Ω : Type*} {α : T → Type*} [MeasureSpace Ω] {P : Measure Ω} [(t : T) → MeasurableSpace (α t)] {X : (t : T) → Ω → (α t)}

lemma of_measurable (hX : ∀ t, Measurable (X t)) : IsStochasticProcess P X :=
  { aemeasurable := fun t ↦ (hX t).aemeasurable }

lemma measurablePair (hX : IsStochasticProcess P X) : ∀ s t : T, AEMeasurable (fun ω ↦ (X s ω, X t ω)) P :=
  fun s t ↦ AEMeasurable.prodMk (hX.aemeasurable s) (hX.aemeasurable t)

noncomputable def fdd (_ : IsStochasticProcess P X) := fun I : Finset T ↦ P.map (fun ω ↦ I.restrict (X · ω))

lemma fdd_eq (hX : IsStochasticProcess P X) : hX.fdd = fun I : Finset T ↦ P.map (fun ω ↦ I.restrict (X · ω)) := rfl

lemma fdd_eval (hX : IsStochasticProcess P X) (I : Finset T) : hX.fdd I = P.map (fun ω ↦ I.restrict (X · ω)) := rfl

lemma isProjectiveMeasureFamily_map_restrict (hX : IsStochasticProcess P X) :
    IsProjectiveMeasureFamily (hX.fdd) := by
  rw [fdd_eq hX]
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ ↦ hX.aemeasurable _

lemma projectiveFamily (hX : IsStochasticProcess P X): IsProjectiveMeasureFamily (fun J ↦ P.map (fun ω ↦ Finset.restrict J (X · ω))) := by
  sorry

instance (J : Finset T) : MeasurableSpace { x // x ∈ J } := by
  apply?
  sorry

lemma hasLaw_restrict_preBrownian (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (id ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  hasLaw_restrict_gaussianLimit.comp hasLaw_preBrownian






lemma aemeasurable_eval (hX : IsStochasticProcess P X) (t : T) : AEMeasurable (μ := P) (X t) := by
  refine hX.aemeasurable t



lemma hasLaw_eval_gaussianProjectiveFamily {I : Finset T} :
    HasLaw (fun x ↦ x s) (gaussianReal 0 s) (gaussianProjectiveFamily I) where
  aemeasurable := Measurable.aemeasurable <| by fun_prop
  map_eq := by


end IsStochasticProcess

end ProbabilityTheory

--  measurablePair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω)
--   kolmogorovCondition : ∀ s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q
