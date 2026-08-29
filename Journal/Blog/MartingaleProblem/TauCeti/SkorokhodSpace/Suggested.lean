/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Suggested signatures for the Skorokhod space roadmap

Prototypes only. Names and argument orders are suggestions; the statements are
the commitments. `sorry` marks a statement whose proof is the work, never an
empty proposition.
-/

open Filter Topology Set MeasureTheory

/-! ## Milestone 1: the index -/

/-- A metric additive along a linear order. Together with `OrderTopology` and
`ProperSpace` this pins the index down to a closed subset of `ℝ`. -/
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u

variable {ι : Type*} [LinearOrder ι] [MetricSpace ι] [OrderTopology ι]
  [AdditiveDist ι] [ProperSpace ι]

/-- The exhaustion by closed balls around a base point. -/
def exhaustion (t₀ : ι) (m : ℕ) : Set ι := Metric.closedBall t₀ m

theorem isCompact_exhaustion (t₀ : ι) (m : ℕ) : IsCompact (exhaustion t₀ m) := sorry

/-- The metric is the difference of the length function to a base point. -/
theorem dist_eq_sub_of_le {t₀ s t : ι} (h₀s : t₀ ≤ s) (hst : s ≤ t) :
    dist s t = dist t₀ t - dist t₀ s := by
  have := AdditiveDist.dist_add (α := ι) h₀s hst
  linarith

theorem monotoneOn_dist_basepoint {t₀ : ι} :
    MonotoneOn (fun t => dist t₀ t) (Set.Ici t₀) := sorry

/-- Definitional, but it does not fire through a `SetLike` hull: the lattice
`AddSubgroup.zmultiples h` needs its `Set` coercion, or this instance restated
for `SetLike` carriers. -/
instance instAdditiveDistSubtype {α : Type*} [LinearOrder α] [PseudoMetricSpace α]
    [AdditiveDist α] (s : Set α) : AdditiveDist s where
  dist_add {_ _ _} hab hbc := AdditiveDist.dist_add (α := α) hab hbc

/-- An index satisfying the four hypotheses is order isomorphic and isometric to
a closed subset of `ℝ`. -/
theorem exists_orderIso_isometry_real :
    ∃ (s : Set ℝ) (e : ι ≃o s), IsClosed s ∧ Isometry e := sorry

/-! ## Milestone 2: càdlàg functions

`Function.RightContinuous` and `IsCadlag` follow
`RemyDegenne/brownian-motion`, `BrownianMotion/StochasticIntegral/Cadlag.lean`
(Apache 2.0); reuse that file rather than restating it. -/

variable {E : Type*} [MetricSpace E]

/-- The set of points where the left limit differs from the value. -/
def leftJumpSet (f : ι → E) : Set ι := {x | Function.leftLim f x ≠ f x}

theorem countable_leftJumpSet {f : ι → E} (hf : IsCadlag f) :
    (leftJumpSet f).Countable := sorry

theorem IsCadlag.measurable [MeasurableSpace E] [BorelSpace E] {f : ι → E}
    (hf : IsCadlag f) : Measurable f := sorry

/-- A càdlàg function is determined by its values on a dense set. -/
theorem IsCadlag.eq_of_eqOn_dense {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g)
    {D : Set ι} (hD : Dense D) (h : EqOn f g D) : f = g := sorry

/-! ## Milestones 3 and 4: time changes and the metric -/

/-- Bi-Lipschitz order isomorphisms of the index. -/
structure TimeChange (ι : Type*) [LinearOrder ι] [MetricSpace ι] where
  toOrderIso : ι ≃o ι
  lipschitz : ∃ C, LipschitzWith C toOrderIso
  lipschitz_symm : ∃ C, LipschitzWith C toOrderIso.symm

/-- `log` of the larger of the two Lipschitz constants, computed on `exhaustion t₀ m`. -/
noncomputable def TimeChange.normOn (t₀ : ι) (m : ℕ) (l : TimeChange ι) : ℝ := sorry

theorem TimeChange.normOn_mul_le (t₀ : ι) (m : ℕ) (l l' : TimeChange ι) :
    TimeChange.normOn t₀ m (sorry : TimeChange ι) ≤
      TimeChange.normOn t₀ m l + TimeChange.normOn t₀ m l' := sorry

/-- Càdlàg paths from `ι` to `E`. -/
structure SkorokhodSpace (ι E : Type*) [LinearOrder ι] [MetricSpace ι]
    [TopologicalSpace E] where
  toFun : ι → E
  isCadlag : IsCadlag toFun

@[inherit_doc] notation "D(" ι ", " E ")" => SkorokhodSpace ι E

noncomputable instance : MetricSpace D(ι, E) := sorry

instance [PolishSpace E] : CompleteSpace D(ι, E) := sorry
instance [PolishSpace E] : TopologicalSpace.SeparableSpace D(ι, E) := sorry
instance [PolishSpace E] : PolishSpace D(ι, E) := sorry

/-- Evaluation is continuous exactly at the paths that do not jump at `t`. -/
theorem continuousAt_eval {t : ι} {f : D(ι, E)} :
    ContinuousAt (fun g : D(ι, E) => g.toFun t) f ↔
      Function.leftLim f.toFun t = f.toFun t := sorry

/-! ## Milestone 6: the Borel structure -/

variable [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

theorem measurableEmbedding_piDense {D : Set ι} (hD : D.Countable) (hD' : Dense D) :
    MeasurableEmbedding (fun f : D(ι, E) => fun t : D => f.toFun t) := sorry

theorem borel_eq_comap_eval :
    (borel D(ι, E)) = ⨆ t : ι, MeasurableSpace.comap (fun f : D(ι, E) => f.toFun t) inferInstance :=
  sorry

/-! ## Milestone 7: the modulus and compactness -/

/-- The càdlàg modulus on `exhaustion t₀ m`. -/
noncomputable def modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) (δ : ℝ) : ℝ := sorry

theorem tendsto_modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    Tendsto (modulus t₀ m f) (𝓝[>] 0) (𝓝 0) := sorry

theorem isCompact_closure_iff (t₀ : ι) (A : Set D(ι, E)) :
    IsCompact (closure A) ↔ ∀ m : ℕ,
      IsCompact (closure {x | ∃ f ∈ A, ∃ t ∈ exhaustion t₀ m, f.toFun t = x}) ∧
      Tendsto (fun δ => ⨆ f ∈ A, modulus t₀ m f δ) (𝓝[>] 0) (𝓝 0) := sorry
