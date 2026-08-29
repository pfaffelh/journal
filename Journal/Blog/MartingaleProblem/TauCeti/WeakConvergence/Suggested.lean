/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Suggested signatures for the weak convergence roadmap

Prototypes only.
-/

open Filter Topology MeasureTheory Set

variable {E E' : Type*} [MeasurableSpace E] [MeasurableSpace E']

/-! ## Milestone 1: separating and convergence determining classes -/

/-- A set of bounded measurable functions that separates Borel probability measures. -/
def IsSeparating (Γ : Set (E → ℝ)) : Prop :=
  ∀ μ ν : Measure E, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ f ∈ Γ, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν

/-- A set of bounded continuous functions along which weak convergence can be tested. -/
def IsConvergenceDetermining [TopologicalSpace E] (Γ : Set (E → ℝ)) : Prop :=
  ∀ (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E),
    (∀ f ∈ Γ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E)))) → Tendsto μ atTop (𝓝 ν)

theorem IsConvergenceDetermining.isSeparating [TopologicalSpace E] [BorelSpace E]
    {Γ : Set (E → ℝ)} (h : IsConvergenceDetermining Γ) : IsSeparating Γ := sorry

/-- On a Polish space a subalgebra of bounded continuous functions that separates
points and vanishes nowhere is convergence determining. -/
theorem isConvergenceDetermining_of_separatesPoints [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] (Γ : Subalgebra ℝ (E →ᵇ ℝ))
    (hsep : (Γ.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints) :
    IsConvergenceDetermining (fun f => ∃ g ∈ Γ, ⇑g = f) := sorry

/-! ## Milestone 2: the continuous mapping theorem -/

theorem tendsto_map_of_measure_continuousAt [TopologicalSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [MetricSpace E'] [BorelSpace E']
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} {h : E → E'}
    (hh : Measurable h) (hconv : Tendsto μ atTop (𝓝 ν))
    (hcont : (ν : Measure E) {x | ContinuousAt h x} = 1) :
    Tendsto (fun n => (μ n).map hh.aemeasurable) atTop (𝓝 (ν.map hh.aemeasurable)) := sorry

/-! ## Milestone 3: the Skorokhod representation theorem -/

theorem exists_ae_tendsto_of_tendsto [MetricSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {μ : ℕ → ProbabilityMeasure E}
    {ν : ProbabilityMeasure E} (h : Tendsto μ atTop (𝓝 ν)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → E) (Y : Ω → E),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, P.map (X n) = μ n) ∧ P.map Y = ν ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := sorry

/-! ## Milestone 4: Vitali -/

theorem tendsto_integral_of_tendsto_of_uniformIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {P : ℕ → Measure Ω} {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} :
    True := sorry
