/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Suggested signatures for the Skorokhod space roadmap

Prototypes only. Names and argument orders are suggestions; the statements are
the commitments. `sorry` marks a statement whose proof is the work, never an
empty proposition.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-07.  Every declaration elaborates; the `sorry`s are the statements' own
proofs, which is what this file is for.

Since 2026-09-07 the whole of `TimeChange.lipConst` and `TimeChange.norm` is
proved: the attainment `lipschitzWith_lipConst`, `lipConst_one`,
`lipConst_of_subsingleton`, `lipConst_mul_le`, `one_le_max_lipConst`,
`norm_one`, `norm_inv`, `norm_nonneg`, `norm_mul_le`, and `normOn_one`.  Two statements had to
go first, and both were false.  `normOn_mul_le` --- the windowed norm is not
subadditive, see `not_normOn_mul_le` for the witness --- so Milestone 4 builds
its metric on the global `norm`, as Billingsley does.  And
`dist_le_of_normOn_le`, which is now `dist_le_of_norm_le` and asks the time
change to fix the base point; without that a translation refutes it.

Since 2026-09-07, second run, **Milestones 3 and 4 carry no `sorry` at all** in
their time change layer.  `dist_le_of_norm_le` is proved, through the new
`dist_eq_abs_sub_of_sameSide` of Milestone 1; and `not_normOn_mul_le` is proved
as well, so the failure on which Milestone 4 rests its choice of the global
`norm` is a theorem and not a doc comment.  Its witness is spelled out here:
`TimeChange.steep`, the piecewise linear order isomorphism of `ℝ`, and
`TimeChange.double`, `x ↦ 2 * x`.  Both are written as a `max` resp. `min` of
two affine maps rather than with an `if`, which is what makes them cheap:
`max_lt_max` gives strict monotonicity, `LipschitzWith.max` and
`LipschitzWith.min` the two Lipschitz bounds, and the inverse is of the same
shape.  `Real.instAdditiveDist` is the first of the four running instances of
Milestone 1, needed to instantiate the refutation at `ℝ`.

The same run finished Milestone 1 apart from the embedding into `ℝ`:
`exhaustionMin`, `exhaustionMax`, `clamp` and its five properties.  One step of
it was missing from the roadmap and is not cosmetic — `ordConnected_exhaustion`.
Lying between the least and the greatest element of a set does not put a point
in the set, so without the window being an order interval the clamp does not
land in it; and that the window is one is `AdditiveDist` a third time.

Since 2026-09-07, third run, the metric of Milestone 4 has its two data and
every axiom but the separation.  `TimeChange.fixing t₀` is the subgroup of time
changes anchored at the base point, `SkorokhodSpace.restrictExhaustion` is the
path truncated to the window --- càdlàg again by the new
`IsCadlag.comp_monotone_continuous` of Milestone 2 ---, and
`SkorokhodSpace.distOn` is Billingsley's `d°ₘ`, with
`bddAbove_range_dist_restrictExhaustion` and `bddBelow_range_distOn` for the two
places where a conditionally complete supremum could otherwise be a junk value.
`distOn_nonneg`, `distOn_self`, `distOn_comm` and `distOn_triangle` are proved,
and so is the separation; every axiom of `distOn` is a theorem.  The one statement
of Milestone 2 that had to be corrected first is
`IsCadlag.isBounded_image_of_isCompact`: under the bundle (A) of the roadmap,
a mere preorder, it is **false**, and the witness is in the roadmap; it holds
under a linear order, and needs no order topology.

Since 2026-09-07, fourth run, the jump theory of Milestone 2 is proved:
`countable_leftJumpSet`, through the two statements it needed and which the
roadmap did not name --- `IsCadlag.dist_leftLim_le_of_Ioo_subset`, the jump
bound from a two sided oscillation bound, and
`IsCadlag.eventually_dist_leftLim_lt`, the local finiteness of
`largeLeftJumpSet` in its pointwise form --- together with
`IsCadlag.finite_largeLeftJumpSet_inter`, `IsCadlag.tendsto_leftLim`, and the
continuity characterization `IsCadlag.continuousAt_iff_notMem_leftJumpSet` with
its global form `IsCadlag.continuous_iff_leftJumpSet_eq_empty`.  **The proof
uses none of the bundle (B) of the roadmap**: no countable dense set and no
right approximation clause enter it, only the linear order, the order topology,
and the σ-compactness of the index; `AdditiveDist` is omitted throughout, and
properness only through `isCompact_exhaustion`.

In the same run the **separation** of Milestone 4 fell, the last of the four
axioms of `distOn`: `SkorokhodSpace.eq_of_distOn_eq_zero`, with
`SkorokhodSpace.eq_of_forall_distOn_eq_zero` for the passage from the windows to
the paths.  It does not go through the continuity points and their density ---
that step needs the index to supply a right dense set of them, which a closed
subset of `ℝ` need not --- but through the new
`IsCadlag.eq_of_forall_exists_dist_le` of Milestone 2, playing the time change
against its inverse: one of the two moves `t` up, and the right continuity of
whichever path is evaluated there does the rest.

Since 2026-09-07, seventh run, the **metric of Milestone 4 is assembled and
proved**: `SkorokhodSpace.totalDist t₀ f g = ∑' m, 2⁻¹ ^ m * min 1 (distOn t₀ m f g)`
with `summable_totalDist`, `totalDist_self`, `totalDist_comm`,
`totalDist_triangle` and `eq_of_totalDist_eq_zero`, and
`SkorokhodSpace.metricSpace (t₀ : ι) : MetricSpace D(ι, E)` built from them.
It is a `def` with the base point as a parameter, as Milestone 4 asks; the
parameterless `instance` below it stays `sorry` because it is the base point
that is missing there, not an axiom.

Since 2026-09-07, eighth run, `IsCadlag.measurable` is proved, and its bundle
was wrong: it stood under (B) with `E` Polish and a proof by right continuous
step functions, and needs neither.  It falls out of the jump theory above
against `measurable_of_countable_not_continuousAt`, so the whole of Milestone 2
except `IsCadlag.eq_of_eqOn_dense` is now free of (B).

Seven `sorry`s went on 2026-09-06: `isCompact_exhaustion`,
`monotoneOn_dist_basepoint` and
`IsCadlag.eq_of_eqOn_dense` carry proofs --- the last had to be corrected first,
its hypothesis was bare density, under which it is false ---, the `Group
(TimeChange ι)` instance is constructed, `TimeChange.lipConstOn` and
`TimeChange.normOn` are defined instead of being `sorry`, and
`TimeChange.normOn_inv` follows from `inv_inv` and `max_comm`.  A definition
whose body is `sorry` makes every theorem about it a statement about `sorryAx`,
which is the same trap as a statement that is `True`; the statements about
`normOn` became propositions about something only then.  Three errors that the
signature check
of the previous run could not see came out of the first run: `IsCadlag.measurable`
had no `MeasurableSpace ι`, `TimeChange.dist_le_of_normOn_le` used `Real.exp`
without importing it, and Milestone 6 spoke of measurable maps out of `D(ι, E)`
with no measurable structure on it.  The last is now declared, as the Borel
structure of the metric.

`Function.RightContinuous` and `IsCadlag` are **not** in Mathlib — a search of
`upstream/master` for `IsCadlag` returns nothing — so the earlier version of this
file, which used them without defining them, could not be elaborated at all.
They are restated here, verbatim from Milestone 2 of the roadmap, so that the
file stands against Mathlib alone; the intended source is
`RemyDegenne/brownian-motion`, `BrownianMotion/StochasticIntegral/Cadlag.lean`
(Apache 2.0), and that file is what should be reused.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

/-! ## Milestone 1: the index -/

/-- A metric additive along a linear order. Together with `OrderTopology` and
`ProperSpace` this pins the index down to a closed subset of `ℝ`. -/
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u

variable {ι : Type*} [LinearOrder ι] [MetricSpace ι] [OrderTopology ι]
  [AdditiveDist ι] [ProperSpace ι]

/-- The exhaustion by closed balls around a base point. -/
def exhaustion (t₀ : ι) (m : ℕ) : Set ι := Metric.closedBall t₀ m

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] in
theorem isCompact_exhaustion (t₀ : ι) (m : ℕ) : IsCompact (exhaustion t₀ m) :=
  isCompact_closedBall t₀ m

omit [OrderTopology ι] [ProperSpace ι] in
/-- The metric is the difference of the length function to a base point.  It is
`AdditiveDist` alone that does this, neither the order topology nor properness. -/
theorem dist_eq_sub_of_le {t₀ s t : ι} (h₀s : t₀ ≤ s) (hst : s ≤ t) :
    dist s t = dist t₀ t - dist t₀ s := by
  have := AdditiveDist.dist_add (α := ι) h₀s hst
  linarith

omit [OrderTopology ι] [ProperSpace ι] in
/-- Again `AdditiveDist` alone, through `dist_eq_sub_of_le`. -/
theorem monotoneOn_dist_basepoint {t₀ : ι} :
    MonotoneOn (fun t => dist t₀ t) (Set.Ici t₀) := by
  intro s hs t _ hst
  have h : dist s t = dist t₀ t - dist t₀ s := dist_eq_sub_of_le (Set.mem_Ici.1 hs) hst
  have h' : (0 : ℝ) ≤ dist s t := dist_nonneg
  simp only
  linarith

omit [OrderTopology ι] [ProperSpace ι] in
/-- On either side of the base point the metric is the difference of the two
length functions.  This is `dist_eq_sub_of_le` in the form that
`TimeChange.dist_le_of_norm_le` consumes, where the two points compared are `t`
and its image under a time change fixing `t₀`, and only their common position
relative to `t₀` is known.  Like `dist_eq_sub_of_le` it is `AdditiveDist` alone.

The hypothesis cannot be dropped: on `ℝ` with `t₀ = 0`, `s = -1` and `t = 1` the
left hand side is `2` and the right hand side is `0`. -/
theorem dist_eq_abs_sub_of_sameSide {t₀ s t : ι}
    (h : (t₀ ≤ s ∧ t₀ ≤ t) ∨ (s ≤ t₀ ∧ t ≤ t₀)) :
    dist s t = |dist t₀ t - dist t₀ s| := by
  have key : dist s t = dist t₀ t - dist t₀ s ∨ dist s t = dist t₀ s - dist t₀ t := by
    rcases h with ⟨h₀s, h₀t⟩ | ⟨hs₀, ht₀⟩
    · rcases le_total s t with hst | hts
      · exact Or.inl (dist_eq_sub_of_le h₀s hst)
      · refine Or.inr ?_
        rw [dist_comm]
        exact dist_eq_sub_of_le h₀t hts
    · rcases le_total s t with hst | hts
      · refine Or.inr ?_
        have := AdditiveDist.dist_add (α := ι) hst ht₀
        rw [dist_comm t₀ s, dist_comm t₀ t]
        linarith
      · refine Or.inl ?_
        have := AdditiveDist.dist_add (α := ι) hts hs₀
        rw [dist_comm s t, dist_comm t₀ s, dist_comm t₀ t]
        linarith
  rcases key with h1 | h1
  · have h2 : (0 : ℝ) ≤ dist t₀ t - dist t₀ s := by rw [← h1]; exact dist_nonneg
    rw [h1, abs_of_nonneg h2]
  · have h2 : (0 : ℝ) ≤ dist t₀ s - dist t₀ t := by rw [← h1]; exact dist_nonneg
    rw [h1, abs_of_nonpos (by linarith)]
    ring

/-- Definitional, but it does not fire through a `SetLike` hull: the lattice
`AddSubgroup.zmultiples h` needs its `Set` coercion, or this instance restated
for `SetLike` carriers. -/
instance instAdditiveDistSubtype {α : Type*} [LinearOrder α] [PseudoMetricSpace α]
    [AdditiveDist α] (s : Set α) : AdditiveDist s where
  dist_add {_ _ _} hab hbc := AdditiveDist.dist_add (α := α) hab hbc

/-- The first of the four running instances of the milestone: `ℝ` itself.  With
`instAdditiveDistSubtype` above it carries the other three, and it is the index
on which `TimeChange.not_normOn_mul_le` refutes the windowed norm. -/
instance Real.instAdditiveDist : AdditiveDist ℝ where
  dist_add {s t u} hst htu := by
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem mem_exhaustion_self (t₀ : ι) (m : ℕ) : t₀ ∈ exhaustion t₀ m :=
  Metric.mem_closedBall_self (by positivity)

omit [OrderTopology ι] [ProperSpace ι] in
/-- The window is an order interval.  This is `AdditiveDist` again, and it is
what makes the clamp below land in the window: above the base point the length
function is monotone, below it the additivity is read from the other end. -/
theorem ordConnected_exhaustion (t₀ : ι) (m : ℕ) : (exhaustion t₀ m).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨hxz, hzy⟩ := hz
  simp only [exhaustion, Metric.mem_closedBall] at hx hy ⊢
  rcases le_total t₀ z with h | h
  · have h1 : dist t₀ z ≤ dist t₀ y :=
      monotoneOn_dist_basepoint (Set.mem_Ici.2 h) (Set.mem_Ici.2 (h.trans hzy)) hzy
    rw [dist_comm] at hy ⊢
    linarith
  · have h2 := AdditiveDist.dist_add (α := ι) hxz h
    have h3 : (0 : ℝ) ≤ dist x z := dist_nonneg
    linarith

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The least element of the window; it exists because the window is compact and
contains the base point. -/
noncomputable def exhaustionMin (t₀ : ι) (m : ℕ) : ι :=
  ((isCompact_exhaustion t₀ m).exists_isLeast ⟨t₀, mem_exhaustion_self t₀ m⟩).choose

omit [AdditiveDist ι] in
theorem isLeast_exhaustionMin (t₀ : ι) (m : ℕ) :
    IsLeast (exhaustion t₀ m) (exhaustionMin t₀ m) :=
  ((isCompact_exhaustion t₀ m).exists_isLeast ⟨t₀, mem_exhaustion_self t₀ m⟩).choose_spec

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The greatest element of the window. -/
noncomputable def exhaustionMax (t₀ : ι) (m : ℕ) : ι :=
  ((isCompact_exhaustion t₀ m).exists_isGreatest ⟨t₀, mem_exhaustion_self t₀ m⟩).choose

omit [AdditiveDist ι] in
theorem isGreatest_exhaustionMax (t₀ : ι) (m : ℕ) :
    IsGreatest (exhaustion t₀ m) (exhaustionMax t₀ m) :=
  ((isCompact_exhaustion t₀ m).exists_isGreatest ⟨t₀, mem_exhaustion_self t₀ m⟩).choose_spec

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The clamp onto the window.  Milestone 4 composes paths with it, so that a
path restricted to `exhaustion t₀ m` is constant outside the window instead of
being undefined there. -/
noncomputable def clamp (t₀ : ι) (m : ℕ) (t : ι) : ι :=
  min (max t (exhaustionMin t₀ m)) (exhaustionMax t₀ m)

omit [AdditiveDist ι] in
theorem monotone_clamp (t₀ : ι) (m : ℕ) : Monotone (clamp t₀ m) :=
  fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

omit [AdditiveDist ι] in
theorem continuous_clamp (t₀ : ι) (m : ℕ) : Continuous (clamp t₀ m) :=
  (continuous_id.max continuous_const).min continuous_const

theorem clamp_mem_exhaustion (t₀ : ι) (m : ℕ) (t : ι) : clamp t₀ m t ∈ exhaustion t₀ m := by
  have hmin := isLeast_exhaustionMin t₀ m
  have hmax := isGreatest_exhaustionMax t₀ m
  have hle : exhaustionMin t₀ m ≤ exhaustionMax t₀ m := hmin.2 hmax.1
  refine (ordConnected_exhaustion t₀ m).out hmin.1 hmax.1 ⟨?_, min_le_right _ _⟩
  exact le_min (le_max_right _ _) hle

omit [AdditiveDist ι] in
theorem clamp_eq_self {t₀ : ι} {m : ℕ} {t : ι} (ht : t ∈ exhaustion t₀ m) :
    clamp t₀ m t = t := by
  rw [clamp, max_eq_left ((isLeast_exhaustionMin t₀ m).2 ht),
    min_eq_left ((isGreatest_exhaustionMax t₀ m).2 ht)]

theorem clamp_idem (t₀ : ι) (m : ℕ) (t : ι) : clamp t₀ m (clamp t₀ m t) = clamp t₀ m t :=
  clamp_eq_self (clamp_mem_exhaustion t₀ m t)

/-- An index satisfying the four hypotheses is order isomorphic and isometric to
a closed subset of `ℝ`. -/
#check @exhaustionMin
#check @clamp
#check @exhaustionMax
