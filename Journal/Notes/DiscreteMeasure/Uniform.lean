/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Journal.Notes.DiscreteMeasure.Monad

/-!
# DiscreteMeasure: Uniform distribution

We define `uniform` as the uniform distribution on a finite inhabited type `ι`,
where each element has weight `(Finset.univ : Finset ι).card⁻¹`.
We prove that it is a probability measure.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section uniform

variable {ι : Type*} [Fintype ι]

noncomputable def uniform : DiscreteMeasure ι where
  weight := fun _ ↦ ((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹

@[simp]
lemma uniform_apply (i : ι) : (uniform : DiscreteMeasure ι) i = ((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹ := rfl

variable [Inhabited ι]

lemma hasSum_uniform : HasSum (uniform (ι := ι)) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp [uniform_apply, tsum_fintype]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

lemma isProbabilityMeasure_uniform [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    IsProbabilityMeasure (uniform (ι := ι)).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr hasSum_uniform

end uniform

end DiscreteMeasure

end MeasureTheory
