/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.RCLike.Basic

/-!
# Suggested signatures for the martingale problems roadmap

Prototypes only. The abstract layer takes a family of test processes and never
mentions a state space; the Markovian layer specialises it.
-/

open Filter Topology MeasureTheory Set

/-! ## Milestone 1: the clock -/

/-- The two conventions for the compensating interval. -/
inductive Clock.Conv | optional | predictable

variable {ι : Type*} [Preorder ι]

/-- A measure on the index whose down-sets are measurable and of finite mass. -/
structure Clock (ι : Type*) [Preorder ι] where
  measurableSpace : MeasurableSpace ι
  q : @Measure ι measurableSpace
  measurableSet_Iic : ∀ t : ι, @MeasurableSet ι measurableSpace (Set.Iic t)
  measurableSet_Iio : ∀ t : ι, @MeasurableSet ι measurableSpace (Set.Iio t)
  measure_Iic_ne_top : ∀ t : ι, q (Set.Iic t) ≠ ⊤

/-- The compensating interval selected by the convention. -/
def Clock.interval (Q : Clock ι) (c : Clock.Conv) (s t : ι) : Set ι :=
  match c with
  | .optional => Set.Iic t \ Set.Iic s
  | .predictable => Set.Iio t \ Set.Iio s

theorem Clock.interval_union (Q : Clock ι) (c : Clock.Conv) {s t u : ι}
    (hst : s ≤ t) (htu : t ≤ u) :
    Q.interval c s u = Q.interval c s t ∪ Q.interval c t u ∧
      Disjoint (Q.interval c s t) (Q.interval c t u) := sorry

/-- The two conventions agree exactly for an atomless clock. -/
def Clock.IsAtomless (Q : Clock ι) : Prop := ∀ t : ι, Q.q {u | t ≤ u ∧ u ≤ t} = 0

/-! ## Milestone 2: the abstract martingale problem -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝕂 : Type*} [RCLike 𝕂]

/-- `P` solves the martingale problem for the family `𝓧` of test processes. -/
def IsMPSolution (𝓧 : Set (ι → Ω → 𝕂)) (F : Filtration ι m) (P : Measure Ω) : Prop :=
  ∀ Y ∈ 𝓧, Martingale Y F P

/-- The set of solutions. -/
def mpSolutions (𝓧 : Set (ι → Ω → 𝕂)) (F : Filtration ι m) : Set (Measure Ω) :=
  {P | IsMPSolution 𝓧 F P}

variable {E : Type*} [MeasurableSpace E]

/-- The test processes attached to an operator, a clock and a convention.
The operator is a relation, not a function. -/
def mpFamily (A : Set ((E → 𝕂) × (E → 𝕂))) (Q : Clock ι) (c : Clock.Conv)
    (X : ι → Ω → E) : Set (ι → Ω → 𝕂) :=
  {Y | ∃ p ∈ A, ∀ t ω, Y t ω =
    p.1 (X t ω) - ∫ s in Q.interval c 0 t, p.2 (X s ω) ∂Q.q}

/-! ## Milestone 3: determining sets and the finite dimensional criterion -/

/-- A family of bounded real test variables strong enough to detect the
martingale property. Real valued whatever `𝕂` is. -/
def IsDetermining {F : Type*} [MeasurableSpace F] (Z : ι → Set (F → ℝ))
    (𝓧 : Set (ι → Ω → 𝕂)) : Prop := sorry

theorem isMPSolution_iff_forall_fdd (A : Set ((E → 𝕂) × (E → 𝕂))) (Q : Clock ι)
    (c : Clock.Conv) (X : ι → Ω → E) (P : Measure Ω) :
    True := sorry

/-! ## Milestone 5: the restart lemma -/

/-- A shift on a path space. -/
structure Shift (F : Type*) [MeasurableSpace F] (ι : Type*) [Preorder ι] [Add ι]
    (E : Type*) [MeasurableSpace E] where
  θ : ι → F → F
  measurable : ∀ r, Measurable (θ r)
  eval_comp : ∀ r t (f : F), sorry

theorem restart : True := sorry

/-! ## Milestone 9: the regularizing class -/

/-- The three conditions on a class of functions that force a càdlàg
modification. The first is satisfied by `C := f ∘ X - Y`, so the content is the
choice of `Y` in `𝓧` and the last two conditions. -/
def IsRegularizingClass {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (Φ : Set (E → 𝕂)) (X : ι → Ω → E) (𝓧 : Set (ι → Ω → 𝕂))
    (F : Filtration ι m) (P : Measure Ω) (D : Set ι) : Prop := sorry

theorem exists_cadlag_modification_of_isRegularizingClass : True := sorry

/-! ## Milestone 10: the abstract convergence theorem

Stated without any topology on the path space: the hypothesis is convergence in
distribution of finitely many real random variables. -/

theorem mpSolution_of_tendsto : True := sorry
