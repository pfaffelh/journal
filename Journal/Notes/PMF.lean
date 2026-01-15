import Mathlib
import Journal.Notes.DiscreteMeasure

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
