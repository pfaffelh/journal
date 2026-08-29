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

/-! ## Milestone 1: the two predicates, and the instances Mathlib lacks

Mathlib proves that the bounded continuous functions separate finite measures
(`ext_of_forall_integral_eq_of_IsFiniteMeasure`) and are convergence determining
(`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), and that a
`StarSubalgebra` separating points separates finite measures
(`ext_of_forall_mem_subalgebra_integral_eq_of_polish`).  The predicates exist
because `IsSeparating` occurs as a hypothesis downstream. -/

/-- A set of bounded measurable functions that separates finite Borel measures. -/
def IsSeparating (Γ : Set (E → ℝ)) : Prop :=
  ∀ μ ν : Measure E, IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ f ∈ Γ, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν

/-- A set of functions along which weak convergence can be tested. -/
def IsConvergenceDetermining [TopologicalSpace E] (Γ : Set (E → ℝ)) : Prop :=
  ∀ (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E),
    (∀ f ∈ Γ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E)))) → Tendsto μ atTop (𝓝 ν)

theorem IsConvergenceDetermining.isSeparating [TopologicalSpace E] [BorelSpace E]
    {Γ : Set (E → ℝ)} (h : IsConvergenceDetermining Γ) : IsSeparating Γ := sorry

/-- One line from `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`. -/
theorem isSeparating_setOf_boundedContinuous [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] :
    IsSeparating {f : E → ℝ | ∃ g : E →ᵇ ℝ, ⇑g = f} := sorry

/-- Missing from Mathlib: the Stone-Weierstrass step for the *convergence*
notion.  Mathlib proves the separating half only. -/
theorem isConvergenceDetermining_of_separatesPoints [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hsep : (A.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints)
    (hvan : ∀ x : E, ∃ g ∈ A, g x ≠ 0) :
    IsConvergenceDetermining {f : E → ℝ | ∃ g ∈ A, ⇑g = f} := sorry

/-- Missing from Mathlib: products.  This is what makes finite dimensional
distributions determine a law. -/
theorem isSeparating_pi {k : ℕ} {S : Fin k → Type*} [∀ i, MeasurableSpace (S i)]
    (Γ : ∀ i, Set (S i → ℝ)) (h : ∀ i, IsSeparating (Γ i)) :
    IsSeparating {f : (∀ i, S i) → ℝ |
      ∃ g : ∀ i, S i → ℝ, (∀ i, g i ∈ Γ i) ∧ f = fun x => ∏ i, g i (x i)} := sorry

/-! ## Milestone 2: the continuous mapping theorem for almost everywhere continuous maps

Mathlib has `FiniteMeasure.tendsto_map_of_tendsto_of_continuous` for continuous
maps; this is the version the convergence theory needs. -/

theorem tendsto_map_of_measure_setOf_continuousAt_eq_one [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] [MetricSpace E'] [BorelSpace E']
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

/-! ## Milestone 4: uniform integrability against convergence in distribution

Mathlib's uniform integrability theory (`uniformIntegrable_iff`, the Vitali
theorems in `MeasureTheory/Function/UniformIntegrable.lean`) is about a single
measure.  This is the statement for laws on varying spaces; the Skorokhod
representation above reduces it to Mathlib's. -/

/-- Uniform integrability of a family of real random variables living on
different spaces, stated by truncation because that is the form the convergence
proof uses. -/
def IsUniformlyIntegrableLaws (μ : ℕ → ProbabilityMeasure ℝ) : Prop :=
  Tendsto (fun N : ℕ => ⨆ n, ∫ x, (|x| - min |x| N) ∂(μ n : Measure ℝ)) atTop (𝓝 0)

theorem tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto μ atTop (𝓝 ν)) (hui : IsUniformlyIntegrableLaws μ) :
    Integrable id (ν : Measure ℝ) ∧
      Tendsto (fun n => ∫ x, x ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, x ∂(ν : Measure ℝ))) :=
  sorry
