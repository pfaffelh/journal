/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Process.Stopping

/-!
# The supremum of a sequence of stopping times

Scratch development for `TauCeti/MartingaleProblems/Suggested.lean`, Milestone 9,
against Mathlib alone.  Mathlib carries `IsStoppingTime.iInf`
(`Probability/Process/Stopping.lean:385`) and not the supremum; the asymmetry is
real, since the infimum needs a right continuous filtration, a densely ordered
index and `NoMaxOrder`, while the supremum needs nothing beyond the
conditionally complete order of the index.
-/

open Filter Topology MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {m : MeasurableSpace Ω} {ι : Type*} [ConditionallyCompleteLinearOrder ι]

theorem isStoppingTime_iSup {𝓕 : Filtration ι m} {τ : ℕ → Ω → WithTop ι}
    (hτ : ∀ n, IsStoppingTime 𝓕 (τ n)) :
    IsStoppingTime 𝓕 fun ω ↦ ⨆ n, τ n ω := by
  intro i
  have hset : {ω | (⨆ n, τ n ω) ≤ (i : WithTop ι)} = ⋂ n, {ω | τ n ω ≤ (i : WithTop ι)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ciSup_le_iff (OrderTop.bddAbove _)
  rw [hset]
  exact MeasurableSet.iInter fun n ↦ hτ n i

end TauCeti
