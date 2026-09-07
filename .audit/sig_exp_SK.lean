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
theorem exists_orderIso_isometry_real :
    ∃ (s : Set ℝ) (e : ι ≃o s), IsClosed s ∧ Isometry e := sorry

/-! ## Milestone 2: càdlàg functions

Neither predicate is in Mathlib. `Function.leftLim` and `Function.rightLim` are
(`Mathlib/Topology/Order/LeftRightLim.lean:50` and `:59`), and the two lemmas
that connect the structure to them, `tendsto_leftLim_of_tendsto` and
`ContinuousWithinAt.rightLim_eq`, live in the same file. -/

/-- Right continuity at every point. -/
def Function.RightContinuous {α β : Type*} [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] (f : α → β) : Prop :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

/-- Right continuous with left limits. -/
structure IsCadlag {α β : Type*} [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] (f : α → β) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

variable {E : Type*} [MetricSpace E]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The set of points where the left limit differs from the value. -/
def leftJumpSet (f : ι → E) : Set ι := {x | Function.leftLim f x ≠ f x}

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The set of points where the left limit differs from the value by at least `ε`. -/
def largeLeftJumpSet (f : ι → E) (ε : ℝ) : Set ι :=
  {x | ε ≤ dist (Function.leftLim f x) (f x)}

omit [AdditiveDist ι] [ProperSpace ι] in
/-- The `left_limit` field, read through `Function.leftLim`.  This is what makes
the existing API of `Mathlib/Topology/Order/LeftRightLim.lean` apply, and it is
unconditional: `tendsto_leftLim_of_tendsto` covers the degenerate case
`𝓝[<] x = ⊥` itself. -/
theorem IsCadlag.tendsto_leftLim {f : ι → E} (hf : IsCadlag f) (x : ι) :
    Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x)) :=
  tendsto_leftLim_of_tendsto (hf.left_limit x)

omit [AdditiveDist ι] [ProperSpace ι] in
/-- If `f` stays `r`-close to a point `c` of `E` on `Set.Ioo a y` and at `y`,
then the jump of `f` at `y` is at most `2r`.  This is the one step of the jump
theory that touches `Function.leftLim` directly, and it is used on both sides of
a point: to the left with `c` the left limit there, to the right with `c` the
value there.

The degenerate case is not an exception but the reason the statement is about
the jump and not about the left limit alone: where `𝓝[<] y = ⊥` the left limit
*is* the value, by `Function.leftLim_eq_of_eq_bot`, and the jump is `0`. -/
theorem IsCadlag.dist_leftLim_le_of_Ioo_subset {f : ι → E} (hf : IsCadlag f) {a y : ι}
    (hay : a < y) {c : E} {r : ℝ} (hIoo : ∀ z ∈ Set.Ioo a y, dist (f z) c ≤ r)
    (hy : dist (f y) c ≤ r) :
    dist (Function.leftLim f y) (f y) ≤ r + r := by
  have hr : (0 : ℝ) ≤ r := dist_nonneg.trans hy
  rcases eq_or_neBot (𝓝[<] y) with hbot | hne
  · rw [leftLim_eq_of_eq_bot f hbot, dist_self]
    linarith
  · have : (𝓝[<] y).NeBot := hne
    have hmem : Set.Ioo a y ∈ 𝓝[<] y :=
      mem_of_superset (inter_mem_nhdsWithin (Set.Iio y) (Ioi_mem_nhds hay))
        fun z hz => ⟨hz.2, hz.1⟩
    have h1 : dist (Function.leftLim f y) c ≤ r := by
      refine le_of_tendsto ((hf.tendsto_leftLim y).dist tendsto_const_nhds) ?_
      filter_upwards [hmem] with z hz using hIoo z hz
    calc dist (Function.leftLim f y) (f y)
        ≤ dist (Function.leftLim f y) c + dist c (f y) := dist_triangle _ _ _
      _ ≤ r + r := by rw [dist_comm c]; exact add_le_add h1 hy

omit [AdditiveDist ι] [ProperSpace ι] in
/-- Local finiteness of the large jumps, in its sharpest form: **every** point of
the index has a neighbourhood on which the only jump of size `ε` is possibly the
point itself.  The point itself cannot be excluded --- a càdlàg function may jump
at any single point --- and it need not be, since a set that meets a
neighbourhood of each of its points in one point meets every compact set in a
finite set.

The proof is the two sided one, and it is where the linear order and the order
topology are used: `nhdsLT_sup_nhdsGE` splits a neighbourhood of `x` into its two
one sided halves, the left limit at `x` controls `f` on an interval `(a, x)` and
the right continuity at `x` controls it on an interval `[x, u)`, and on each of
the two `dist_leftLim_le_of_Ioo_subset` turns that control into a bound on the
jump at the *interior* points of the interval.  The two degenerate cases --- `x`
a bottom element, where `𝓝[<] x = ⊥`, and `x` a top element, where `Set.Ici x`
is `{x}` --- carry no content and are discharged separately. -/
theorem IsCadlag.eventually_dist_leftLim_lt {f : ι → E} (hf : IsCadlag f) (x : ι) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, y ≠ x → dist (Function.leftLim f y) (f y) < ε := by
  rw [← nhdsLT_sup_nhdsGE x, Filter.eventually_sup]
  constructor
  · by_cases hlt : ∃ l : ι, l < x
    · obtain ⟨l, hl⟩ := hlt
      have hA : {z | dist (f z) (Function.leftLim f x) ≤ ε / 4} ∈ 𝓝[<] x := by
        filter_upwards [Metric.tendsto_nhds.1 (hf.tendsto_leftLim x) (ε / 4) (by positivity)]
          with z hz using hz.le
      obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hl).1 hA
      filter_upwards [(mem_nhdsLT_iff_exists_Ioo_subset' hl).2 ⟨a, ha, subset_rfl⟩]
        with y hy _
      have h1 : ∀ z ∈ Set.Ioo a y, dist (f z) (Function.leftLim f x) ≤ ε / 4 :=
        fun z hz => hsub ⟨hz.1, hz.2.trans hy.2⟩
      have h2 := hf.dist_leftLim_le_of_Ioo_subset hy.1 h1 (hsub hy)
      linarith
    · have hIio : Set.Iio x = (∅ : Set ι) := by
        ext z
        simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
        exact fun hz => hlt ⟨z, hz⟩
      rw [hIio, nhdsWithin_empty]
      exact Filter.eventually_bot
  · by_cases hgt : ∃ u : ι, x < u
    · obtain ⟨u', hu'⟩ := hgt
      have hB : {z | dist (f z) (f x) ≤ ε / 4} ∈ 𝓝[≥] x := by
        have h2 : Tendsto f (𝓝[≥] x) (𝓝 (f x)) :=
          continuousWithinAt_Ioi_iff_Ici.1 (hf.right_continuous x)
        filter_upwards [Metric.tendsto_nhds.1 h2 (ε / 4) (by positivity)] with z hz using hz.le
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' hu').1 hB
      filter_upwards [(mem_nhdsGE_iff_exists_Ico_subset' hu').2 ⟨u, hu, subset_rfl⟩]
        with y hy hyx
      have hxy : x < y := lt_of_le_of_ne hy.1 (Ne.symm hyx)
      have h1 : ∀ z ∈ Set.Ioo x y, dist (f z) (f x) ≤ ε / 4 :=
        fun z hz => hsub ⟨hz.1.le, hz.2.trans hy.2⟩
      have h2 := hf.dist_leftLim_le_of_Ioo_subset hxy h1 (hsub hy)
      linarith
    · filter_upwards [self_mem_nhdsWithin] with y hy hyx
      exact absurd (le_antisymm (not_lt.1 fun h => hgt ⟨y, h⟩) hy) hyx

omit [AdditiveDist ι] [ProperSpace ι] in
/-- The jumps of size `ε` meet a compact set in a finite set.  This is
`eventually_dist_leftLim_lt` against `IsCompact.elim_nhds_subcover`: the
neighbourhoods it produces meet `largeLeftJumpSet f ε` in at most one point, and
finitely many of them cover the compact set. -/
theorem IsCadlag.finite_largeLeftJumpSet_inter {f : ι → E} (hf : IsCadlag f) {ε : ℝ}
    (hε : 0 < ε) {K : Set ι} (hK : IsCompact K) : (largeLeftJumpSet f ε ∩ K).Finite := by
  have key : ∀ x : ι, ∃ U ∈ 𝓝 x, largeLeftJumpSet f ε ∩ U ⊆ {x} := by
    intro x
    refine ⟨{y | y ≠ x → dist (Function.leftLim f y) (f y) < ε},
      hf.eventually_dist_leftLim_lt x hε, ?_⟩
    rintro y ⟨hy1, hy2⟩
    by_contra hne
    exact absurd (hy2 hne) (not_lt.2 hy1)
  choose U hU hUsub using key
  obtain ⟨s, -, hcover⟩ := hK.elim_nhds_subcover U fun x _ => hU x
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    fun x _ => Set.finite_singleton x) ?_
  rintro y ⟨hy1, hy2⟩
  obtain ⟨x, hxs, hx⟩ := Set.mem_iUnion₂.1 (hcover hy2)
  exact Set.mem_iUnion₂.2 ⟨x, hxs, hUsub x ⟨hy1, hx⟩⟩

omit [AdditiveDist ι] in
/-- The jump set of a càdlàg map is countable.  It decomposes over the jump size
into the sets `largeLeftJumpSet f (1 / (n + 1))`, and each of those meets each
member of the exhaustion in a finite set; properness of the index is what makes
the exhaustion compact, and that is the only place it is used.

The decomposition over `ε` is not a convenience: the jump set itself may have
accumulation points, as it does for
`f = ∑' n, 2⁻¹ ^ n * Set.indicator (Set.Ici (1 / (n + 1))) 1` at `0`. -/
theorem countable_leftJumpSet {f : ι → E} (hf : IsCadlag f) :
    (leftJumpSet f).Countable := by
  rcases isEmpty_or_nonempty ι with hι | hne
  · have := hι
    exact Set.Countable.mono (Set.subset_univ _) (Set.Finite.countable Set.finite_univ)
  · obtain ⟨t₀⟩ := hne
    have hsub : leftJumpSet f ⊆
        ⋃ (n : ℕ), ⋃ (m : ℕ), largeLeftJumpSet f (1 / (n + 1)) ∩ exhaustion t₀ m := by
      intro x hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hx)
      obtain ⟨m, hm⟩ := exists_nat_ge (dist t₀ x)
      refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, hn.le, ?_⟩⟩
      simpa [exhaustion, Metric.mem_closedBall, dist_comm x t₀] using hm
    refine Set.Countable.mono hsub
      (Set.countable_iUnion fun n => Set.countable_iUnion fun m => ?_)
    exact (hf.finite_largeLeftJumpSet_inter (by positivity)
      (isCompact_exhaustion t₀ m)).countable

omit [AdditiveDist ι] [ProperSpace ι] in
/-- A càdlàg map is continuous at `x` exactly where it does not jump.  The two
directions use the two fields separately: forwards it is
`ContinuousWithinAt.leftLim_eq` on the restriction of continuity to `Set.Iic x`,
backwards the left limit *is* the value, so `IsCadlag.tendsto_leftLim` gives
convergence along `𝓝[<] x`, which together with the right continuity along
`𝓝[≥] x` is convergence along `𝓝 x` by `nhdsLT_sup_nhdsGE`. -/
theorem IsCadlag.continuousAt_iff_notMem_leftJumpSet {f : ι → E} (hf : IsCadlag f) {x : ι} :
    ContinuousAt f x ↔ x ∉ leftJumpSet f := by
  constructor
  · intro hc
    simpa [leftJumpSet] using hc.continuousWithinAt.leftLim_eq
  · intro hx
    have hx' : Function.leftLim f x = f x := by simpa [leftJumpSet] using hx
    have h1 : Tendsto f (𝓝[<] x) (𝓝 (f x)) := hx' ▸ hf.tendsto_leftLim x
    have h2 : Tendsto f (𝓝[≥] x) (𝓝 (f x)) :=
      continuousWithinAt_Ioi_iff_Ici.1 (hf.right_continuous x)
    have := h1.sup h2
    rwa [nhdsLT_sup_nhdsGE] at this

omit [AdditiveDist ι] [ProperSpace ι] in
/-- The global form: a càdlàg map is continuous exactly when it has no jump. -/
theorem IsCadlag.continuous_iff_leftJumpSet_eq_empty {f : ι → E} (hf : IsCadlag f) :
    Continuous f ↔ leftJumpSet f = ∅ := by
  rw [continuous_iff_continuousAt, Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun x => hf.continuousAt_iff_notMem_leftJumpSet

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Two càdlàg maps agree at `t` as soon as, arbitrarily close to `t` **and on
its right**, one of them may be evaluated against the other's value at `t` with
arbitrarily small error.  The disjunction is not a weakening for convenience: it
is what the separation of `SkorokhodSpace.distOn` delivers, where the two
branches are the time change moving `t` up and its inverse doing so.

This replaces the classical route to that separation, which agrees on the
continuity points and then invokes their density.  Density is a statement about
the index, and it fails for an index of Milestone 1 whose jump points are not
right isolated; the right hand approximation here uses only the two
`right_continuous` fields, and nothing about the index at all. -/
theorem IsCadlag.eq_of_forall_exists_dist_le {F G : ι → E} (hF : IsCadlag F) (hG : IsCadlag G)
    {t : ι} (h : ∀ ρ > 0, ∀ η > 0, ∃ s, t ≤ s ∧ dist s t < ρ ∧
      (dist (F s) (G t) ≤ η ∨ dist (F t) (G s) ≤ η)) :
    F t = G t := by
  refine eq_of_forall_dist_le fun η hη => ?_
  have hFc : Tendsto F (𝓝[≥] t) (𝓝 (F t)) :=
    continuousWithinAt_Ioi_iff_Ici.1 (hF.right_continuous t)
  have hGc : Tendsto G (𝓝[≥] t) (𝓝 (G t)) :=
    continuousWithinAt_Ioi_iff_Ici.1 (hG.right_continuous t)
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.tendsto_nhdsWithin_nhds.1 hFc (η / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.tendsto_nhdsWithin_nhds.1 hGc (η / 2) (by positivity)
  obtain ⟨s, hts, hsρ, hcase⟩ := h (min ρ₁ ρ₂) (lt_min hρ₁ hρ₂) (η / 2) (by positivity)
  rcases hcase with hc | hc
  · have hd := h₁ (Set.mem_Ici.2 hts) (hsρ.trans_le (min_le_left _ _))
    calc dist (F t) (G t) ≤ dist (F t) (F s) + dist (F s) (G t) := dist_triangle _ _ _
      _ ≤ η / 2 + η / 2 := add_le_add (by rw [dist_comm]; exact hd.le) hc
      _ = η := by ring
  · have hd := h₂ (Set.mem_Ici.2 hts) (hsρ.trans_le (min_le_right _ _))
    calc dist (F t) (G t) ≤ dist (F t) (G s) + dist (G s) (G t) := dist_triangle _ _ _
      _ ≤ η / 2 + η / 2 := add_le_add hc hd.le
      _ = η := by ring

omit [AdditiveDist ι] in
/-- A càdlàg map is Borel measurable.  The route is **not** the approximation by
right continuous step functions along a countable dense set: that needs the
bundle (B) of the roadmap, and it needs a linear structure on `E` to define the
steps.  The jump theory above is enough and asks for neither.  A càdlàg map is
continuous off `leftJumpSet f` by `IsCadlag.continuousAt_iff_notMem_leftJumpSet`,
that set is countable by `countable_leftJumpSet`, and a map continuous off a
countable set is measurable by `measurable_of_countable_not_continuousAt`
(`MeasureTheory/Constructions/BorelSpace/Basic.lean:509`), whose
`MeasurableSingletonClass ι` comes from `T1Space` through
`OpensMeasurableSpace.toMeasurableSingletonClass` (`ibid.:351`).

So the hypotheses are those of `countable_leftJumpSet` --- the linear order, the
order topology and properness --- and `E` a metric space with its Borel
structure; `AdditiveDist` and `PolishSpace E` do not enter. -/
theorem IsCadlag.measurable [MeasurableSpace ι] [BorelSpace ι]
    [MeasurableSpace E] [BorelSpace E] {f : ι → E}
    (hf : IsCadlag f) : Measurable f := by
  refine measurable_of_countable_not_continuousAt ?_
  refine (countable_leftJumpSet hf).mono fun x hx => ?_
  by_contra hc
  exact hx (hf.continuousAt_iff_notMem_leftJumpSet.2 hc)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- A càdlàg function is determined by its values on a set that is dense **from
the right**: every point of the index either lies in `D` or is approached by
points of `D` from above.

Density alone is not enough, and the statement under it is false as soon as the
index has a point that is right isolated without being isolated -- which
Milestone 1 allows, since it pins the index down to a *closed subset of* `ℝ` and
not to an interval.  Take `ι = [0,1] ∪ {2}`, `D = ([0,1) ∩ ℚ) ∪ {2}`, which is
dense, `f = 0` and `g = ` the indicator of `{1}`.  Both are càdlàg: at `1` the
filter `𝓝[>] 1` is `⊥`, so right continuity there says nothing, and at `2` so is
`𝓝[<] 2`.  They agree on `D` and differ at `1`.

The hypothesis below is what the proof uses, and it implies `Dense D`.  Neither
the order topology nor `AdditiveDist` nor properness enters, so they are
omitted. -/
theorem IsCadlag.eq_of_eqOn_dense {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g)
    {D : Set ι} (hD : ∀ t : ι, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot) (h : EqOn f g D) :
    f = g := by
  funext t
  rcases hD t with ht | ht
  · exact h ht
  · have := ht
    have hf' : ContinuousWithinAt f (D ∩ Set.Ioi t) t :=
      (hf.right_continuous t).mono Set.inter_subset_right
    have hg' : ContinuousWithinAt g (D ∩ Set.Ioi t) t :=
      (hg.right_continuous t).mono Set.inter_subset_right
    have hfg : g =ᶠ[𝓝[D ∩ Set.Ioi t] t] f := by
      filter_upwards [self_mem_nhdsWithin] with x hx using (h hx.1).symm
    exact tendsto_nhds_unique hf' (Filter.Tendsto.congr' hfg hg')

omit [AdditiveDist ι] [ProperSpace ι] in
/-- Càdlàg functions are closed under precomposition with a monotone continuous
map of the index.  This is what makes `SkorokhodSpace.restrictExhaustion` of
Milestone 4 land in the space again, `clamp` being monotone and continuous.

Both fields need the monotonicity, and for different reasons.  On the right,
`clamp` maps `Set.Ioi a` into `Set.Ici (g a)`, which is where the right
continuity of `f` may be read through `continuousWithinAt_Ioi_iff_Ici`.  On the
left the proof splits: either `g` is already constant to the left of `x` --- and
then so is `f ∘ g` on the whole interval, by monotonicity between the two equal
values --- or `g y < g x` for every `y < x`, and then `g` tends to `g x` from
below, so the left limit of `f` at `g x` is the left limit of `f ∘ g` at `x`. -/
theorem IsCadlag.comp_monotone_continuous {f : ι → E} (hf : IsCadlag f) {g : ι → ι}
    (hgm : Monotone g) (hgc : Continuous g) : IsCadlag (f ∘ g) where
  right_continuous a := by
    have h₁ : ContinuousWithinAt f (Set.Ici (g a)) (g a) :=
      continuousWithinAt_Ioi_iff_Ici.1 (hf.right_continuous (g a))
    exact h₁.comp hgc.continuousWithinAt fun x hx => hgm (le_of_lt hx)
  left_limit x := by
    by_cases hconst : ∃ b, b < x ∧ g b = g x
    · obtain ⟨b, hbx, hgb⟩ := hconst
      refine ⟨f (g x), Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [Ioo_mem_nhdsLT hbx] with y hy
      have : g y = g x := le_antisymm (hgm hy.2.le) (hgb ▸ hgm hy.1.le)
      simp [Function.comp_apply, this]
    · simp only [not_exists, not_and] at hconst
      obtain ⟨l, hl⟩ := hf.left_limit (g x)
      refine ⟨l, hl.comp ?_⟩
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        hgc.continuousWithinAt ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact lt_of_le_of_ne (hgm (le_of_lt hy)) (hconst y hy)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The image of a compact set under a càdlàg map is bounded.  Milestone 4 needs
it to know that the supremum in its `distOn` is a real number: the paths there
are constant outside `exhaustion t₀ m`, which is compact.

Only `E` contributes a metric.  The index contributes compactness, the order
topology through `nhdsLT_sup_nhdsGE` --- a neighbourhood of a point is the join
of the two one sided ones, which is exactly the split the two fields of
`IsCadlag` cover --- and nothing else. -/
theorem IsCadlag.isBounded_image_of_isCompact {f : ι → E} (hf : IsCadlag f)
    {K : Set ι} (hK : IsCompact K) : Bornology.IsBounded (f '' K) := by
  have key : ∀ x : ι, ∃ r : ℝ, {y | dist (f y) (f x) ≤ r} ∈ 𝓝 x := by
    intro x
    obtain ⟨l, hl⟩ := hf.left_limit x
    refine ⟨1 + dist l (f x), ?_⟩
    rw [← nhdsLT_sup_nhdsGE x, Filter.mem_sup]
    constructor
    · filter_upwards [Metric.tendsto_nhds.1 hl 1 one_pos] with y hy
      calc dist (f y) (f x) ≤ dist (f y) l + dist l (f x) := dist_triangle _ _ _
        _ ≤ 1 + dist l (f x) := by linarith
    · have h2 : Tendsto f (𝓝[≥] x) (𝓝 (f x)) :=
        continuousWithinAt_Ioi_iff_Ici.1 (hf.right_continuous x)
      filter_upwards [Metric.tendsto_nhds.1 h2 1 one_pos] with y hy
      have hd : (0 : ℝ) ≤ dist l (f x) := dist_nonneg
      linarith
  choose r hr using key
  obtain ⟨s, -, hsub⟩ :=
    hK.elim_nhds_subcover (fun x => {y | dist (f y) (f x) ≤ r x}) fun x _ => hr x
  refine ((Bornology.isBounded_biUnion_finset s
      (f := fun x => Metric.closedBall (f x) (r x))).2
    (fun x _ => Metric.isBounded_closedBall)).subset ?_
  rintro _ ⟨y, hyK, rfl⟩
  obtain ⟨x, hxs, hx⟩ := Set.mem_iUnion₂.1 (hsub hyK)
  exact Set.mem_iUnion₂.2 ⟨x, hxs, by simpa [Metric.mem_closedBall] using hx⟩

/-! ## Milestones 3 and 4: time changes and the metric -/

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Bi-Lipschitz order isomorphisms of the index. -/
structure TimeChange (ι : Type*) [LinearOrder ι] [MetricSpace ι] where
  toOrderIso : ι ≃o ι
  lipschitz : ∃ C, LipschitzWith C toOrderIso
  lipschitz_symm : ∃ C, LipschitzWith C toOrderIso.symm

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Two time changes with the same order isomorphism are equal: the other two
fields are propositions. -/
@[ext]
theorem TimeChange.ext {l l' : TimeChange ι} (h : l.toOrderIso = l'.toOrderIso) :
    l = l' := by
  cases l; cases l'; subst h; rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.exists_lipschitzWith_trans {e e' : ι ≃o ι}
    (h : ∃ C, LipschitzWith C e) (h' : ∃ C, LipschitzWith C e') :
    ∃ C, LipschitzWith C (e.trans e') := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  exact ⟨C' * C, by simpa only [OrderIso.coe_trans] using hC'.comp hC⟩

/-- Composition and inversion make the time changes a group; this is what turns
`normOn` into a length function and gives the triangle inequality of the metric
below.  Multiplication is composition of functions, `l * l' = l ∘ l'`, which is
`OrderIso.trans` in the other order. -/
instance : Group (TimeChange ι) where
  mul l l' :=
    { toOrderIso := l'.toOrderIso.trans l.toOrderIso
      lipschitz := TimeChange.exists_lipschitzWith_trans l'.lipschitz l.lipschitz
      lipschitz_symm := by
        rw [OrderIso.symm_trans]
        exact TimeChange.exists_lipschitzWith_trans l.lipschitz_symm l'.lipschitz_symm }
  one :=
    { toOrderIso := OrderIso.refl ι
      lipschitz := ⟨1, LipschitzWith.id⟩
      lipschitz_symm := ⟨1, LipschitzWith.id⟩ }
  inv l :=
    { toOrderIso := l.toOrderIso.symm
      lipschitz := l.lipschitz_symm
      lipschitz_symm := by rw [OrderIso.symm_symm]; exact l.lipschitz }
  mul_assoc l l' l'' := TimeChange.ext rfl
  one_mul l := TimeChange.ext rfl
  mul_one l := TimeChange.ext rfl
  inv_mul_cancel l := TimeChange.ext (OrderIso.self_trans_symm l.toOrderIso)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The least Lipschitz constant. Mathlib carries no least Lipschitz constant:
`LipschitzWith (K : ℝ≥0) (f : α → β)`
(`Mathlib/Topology/EMetricSpace/Lipschitz.lean`) is a `Prop`, and
`LipschitzWith.const` there is the theorem that a constant map is `0`-Lipschitz,
not a constant attached to a map. -/
noncomputable def TimeChange.lipConst (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzWith K l.toOrderIso}

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The same constant computed on `exhaustion t₀ m` only. -/
noncomputable def TimeChange.lipConstOn (t₀ : ι) (m : ℕ) (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzOnWith K l.toOrderIso (exhaustion t₀ m)}

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The infimum is attained. This is where `ι` being a metric space and not
merely an extended metric space is used: `edist s t ≠ ∞`, so the inequality
`edist (l s) (l t) ≤ K * edist s t` may be divided by `edist s t` and passes to
the infimum over the admissible `K`. -/
theorem TimeChange.lipschitzWith_lipConst (l : TimeChange ι) :
    LipschitzWith l.lipConst ⇑l.toOrderIso := by
  obtain ⟨K₀, hK₀⟩ := l.lipschitz
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  rw [← ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)]
  have hr : ((edist (l.toOrderIso x) (l.toOrderIso y) / edist x y).toNNReal : ℝ≥0∞)
      = edist (l.toOrderIso x) (l.toOrderIso y) / edist x y :=
    ENNReal.coe_toNNReal (ENNReal.div_ne_top (edist_ne_top _ _) h0)
  rw [← hr, ENNReal.coe_le_coe, TimeChange.lipConst]
  refine le_csInf ⟨K₀, hK₀⟩ fun K hK => ?_
  rw [← ENNReal.coe_le_coe, hr]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 (hK x y)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- On a subsingleton index every constant is admissible, so the least one is
`0`; this is the degenerate case that `Real.log 0 = 0` carries below. -/
theorem TimeChange.lipConst_of_subsingleton [Subsingleton ι] (l : TimeChange ι) :
    l.lipConst = 0 := by
  refine le_antisymm (csInf_le' ?_) zero_le
  show LipschitzWith (0 : ℝ≥0) ⇑l.toOrderIso
  intro a b
  simp [Subsingleton.elim a b]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- With two distinct points the set of admissible constants of the identity is
`Set.Ici 1`, so its infimum is `1`. -/
theorem TimeChange.lipConst_one [Nontrivial ι] : (1 : TimeChange ι).lipConst = 1 := by
  have hone : ∀ t : ι, (1 : TimeChange ι).toOrderIso t = t := fun _ => rfl
  have hmem : LipschitzWith 1 ⇑(1 : TimeChange ι).toOrderIso := by
    intro a b; simp [hone]
  rw [TimeChange.lipConst]
  refine le_antisymm (csInf_le' hmem) (le_csInf ⟨1, hmem⟩ fun K hK => ?_)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ι
  have h := hK x y
  simp only [hone] at h
  have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  refine ENNReal.one_le_coe_iff.1 ?_
  have := (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 h
  rwa [ENNReal.div_self h0 hfin] at this

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Submultiplicativity, from `LipschitzWith.comp` and the attainment above.
`l * l'` is `l ∘ l'`, so `OrderIso.coe_trans` turns the composite into one. -/
theorem TimeChange.lipConst_mul_le (l l' : TimeChange ι) :
    (l * l').lipConst ≤ l.lipConst * l'.lipConst := by
  have hcomp : ⇑(l * l').toOrderIso = ⇑l.toOrderIso ∘ ⇑l'.toOrderIso := by
    show ⇑(l'.toOrderIso.trans l.toOrderIso) = _
    rw [OrderIso.coe_trans]
  have hmem : LipschitzWith (l.lipConst * l'.lipConst) ⇑(l * l').toOrderIso := by
    rw [hcomp]
    exact l.lipschitzWith_lipConst.comp l'.lipschitzWith_lipConst
  exact csInf_le' hmem

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- `log` of the larger of the two Lipschitz constants. This is Billingsley's
`‖λ‖`, and it is a **global** quantity: the windowed `normOn` below is not a
length function, see `TimeChange.not_normOn_mul_le`. -/
noncomputable def TimeChange.norm (l : TimeChange ι) : ℝ :=
  Real.log (max l.lipConst l⁻¹.lipConst)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The same, computed on `exhaustion t₀ m`. It is a lower bound for `norm` and
nothing more; the metric of Milestone 4 uses `norm`. -/
noncomputable def TimeChange.normOn (t₀ : ι) (m : ℕ) (l : TimeChange ι) : ℝ :=
  Real.log (max (TimeChange.lipConstOn t₀ m l) (TimeChange.lipConstOn t₀ m l⁻¹))

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.norm_inv (l : TimeChange ι) : (l⁻¹).norm = l.norm := by
  rw [TimeChange.norm, TimeChange.norm, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.normOn_inv (t₀ : ι) (m : ℕ) (l : TimeChange ι) :
    TimeChange.normOn t₀ m l⁻¹ = TimeChange.normOn t₀ m l := by
  rw [TimeChange.normOn, TimeChange.normOn, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The two cases the proof has to distinguish, and they are the reason the
statement is true at all: on an `exhaustion t₀ m` with two distinct points the
set of admissible constants for the identity is `Set.Ici 1`, so `lipConstOn` is
`1` and its logarithm is `0`; on a one point exhaustion -- `m = 0` in a discrete
index -- every constant is admissible, `lipConstOn` is `0`, and `Real.log 0 = 0`
by Mathlib's convention.  The junk value of `Real.log` is what carries the
degenerate case, which is worth saying out loud rather than leaving to the
reader. -/
theorem TimeChange.normOn_one (t₀ : ι) (m : ℕ) :
    TimeChange.normOn t₀ m (1 : TimeChange ι) = 0 := by
  have hone : ∀ t : ι, (1 : TimeChange ι).toOrderIso t = t := fun _ => rfl
  have key : TimeChange.lipConstOn t₀ m (1 : TimeChange ι) = 0 ∨
      TimeChange.lipConstOn t₀ m (1 : TimeChange ι) = 1 := by
    rw [TimeChange.lipConstOn]
    by_cases hs : (exhaustion t₀ m).Subsingleton
    · refine Or.inl (le_antisymm (csInf_le' ?_) zero_le)
      show LipschitzOnWith (0 : ℝ≥0) ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ m)
      intro a ha b hb
      simp [hone, hs ha hb]
    · obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hs
      have hmem : LipschitzOnWith 1 ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ m) := by
        intro a _ b _
        simp [hone]
      refine Or.inr (le_antisymm (csInf_le' hmem) (le_csInf ⟨1, hmem⟩ fun K hK => ?_))
      have h := hK hx hy
      simp only [hone] at h
      have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
      have hfin : edist x y ≠ ⊤ := edist_ne_top x y
      refine ENNReal.one_le_coe_iff.1 ?_
      have := (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 h
      rwa [ENNReal.div_self h0 hfin] at this
  rw [TimeChange.normOn, inv_one, max_self]
  rcases key with h | h <;> rw [h] <;> simp

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.norm_one : (1 : TimeChange ι).norm = 0 := by
  rw [TimeChange.norm, inv_one, max_self]
  rcases subsingleton_or_nontrivial ι with _ | _
  · rw [TimeChange.lipConst_of_subsingleton]; simp
  · rw [TimeChange.lipConst_one]; simp

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The quantity `norm` takes the logarithm of is at least `1` as soon as the
index has two points: `l` and `l⁻¹` compose to the identity, whose constant is
`1`, so the product of the two constants is at least `1`, hence so is the square
of their maximum. This is what makes the logarithm below well behaved. -/
theorem TimeChange.one_le_max_lipConst [Nontrivial ι] (l : TimeChange ι) :
    1 ≤ max l.lipConst l⁻¹.lipConst := by
  have h := TimeChange.lipConst_mul_le l l⁻¹
  rw [mul_inv_cancel, TimeChange.lipConst_one] at h
  have h2 : l.lipConst * l⁻¹.lipConst ≤
      max l.lipConst l⁻¹.lipConst * max l.lipConst l⁻¹.lipConst :=
    mul_le_mul' (le_max_left _ _) (le_max_right _ _)
  by_contra hc
  rw [not_le] at hc
  have h3 : (1 : ℝ) ≤ (max l.lipConst l⁻¹.lipConst : ℝ≥0) * (max l.lipConst l⁻¹.lipConst : ℝ≥0) := by
    exact_mod_cast h.trans h2
  have h4 : ((max l.lipConst l⁻¹.lipConst : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hc
  nlinarith [NNReal.coe_nonneg (max l.lipConst l⁻¹.lipConst)]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The norm is nonnegative. Milestone 4 takes a `max` of it with a supremum of
distances, so this is what makes that `max` the intended quantity.

The windowed `normOn` does **not** have this property, which is a second symptom
of the failure recorded at `not_normOn_mul_le`: `lipConstOn` measures `l` on the
window and `l⁻¹` on the window as well, not on the image of the window, so both
can be `1/2` at once.  On `ℝ` with `B 1 = [-1,1]`, let `l` have slope `1/2` on
`[-1,1]` and slope `2` on `[-6,-5]`, where it takes the values `[-1,1]`, and
slope `1` far out.  Then `lipConstOn 0 1 l = 1/2` and `lipConstOn 0 1 l⁻¹ = 1/2`,
so `normOn 0 1 l = -log 2 < 0`. -/
theorem TimeChange.norm_nonneg (l : TimeChange ι) : 0 ≤ l.norm := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · simp [TimeChange.norm, TimeChange.lipConst_of_subsingleton]
  · rw [TimeChange.norm]
    refine Real.log_nonneg ?_
    exact_mod_cast TimeChange.one_le_max_lipConst l

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The norm is a length function. This is the triangle inequality of the metric
of Milestone 4, and it holds for the **global** norm only. -/
theorem TimeChange.norm_mul_le (l l' : TimeChange ι) :
    (l * l').norm ≤ l.norm + l'.norm := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · simp [TimeChange.norm, TimeChange.lipConst_of_subsingleton]
  simp only [TimeChange.norm]
  set M := max (l.lipConst : ℝ) (l⁻¹.lipConst : ℝ) with hM
  set M' := max (l'.lipConst : ℝ) (l'⁻¹.lipConst : ℝ) with hM'
  have h1 : (1 : ℝ) ≤ M := by
    have := TimeChange.one_le_max_lipConst l
    rw [hM]; exact_mod_cast this
  have h1' : (1 : ℝ) ≤ M' := by
    have := TimeChange.one_le_max_lipConst l'
    rw [hM']; exact_mod_cast this
  have hA : ((l * l').lipConst : ℝ) ≤ M * M' := by
    have h3 : (l * l').lipConst ≤
        max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst :=
      (TimeChange.lipConst_mul_le l l').trans
        (mul_le_mul' (le_max_left _ _) (le_max_left _ _))
    rw [hM, hM']; exact_mod_cast h3
  have hB : (((l * l')⁻¹).lipConst : ℝ) ≤ M * M' := by
    have h3 : ((l * l')⁻¹).lipConst ≤
        max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst := by
      rw [mul_inv_rev]
      calc (l'⁻¹ * l⁻¹).lipConst ≤ l'⁻¹.lipConst * l⁻¹.lipConst :=
            TimeChange.lipConst_mul_le _ _
        _ ≤ max l'.lipConst l'⁻¹.lipConst * max l.lipConst l⁻¹.lipConst :=
            mul_le_mul' (le_max_right _ _) (le_max_right _ _)
        _ = max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst := mul_comm _ _
    rw [hM, hM']; exact_mod_cast h3
  have hpos : (0 : ℝ) < max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ) := by
    have h := TimeChange.one_le_max_lipConst (l * l')
    have h' : (1 : ℝ) ≤ max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ) := by
      exact_mod_cast h
    linarith
  calc Real.log (max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ))
      ≤ Real.log (M * M') := Real.log_le_log hpos (max_le hA hB)
    _ = Real.log M + Real.log M' := Real.log_mul (by linarith) (by linarith)

/-! ### The two time changes of `ℝ` that refute the windowed norm

Both are written as a `max` resp. `min` of two affine maps rather than with an
`if`, which is what makes `StrictMono` and the Lipschitz bounds one-liners:
`max_lt_max`, `LipschitzWith.max` and `LipschitzWith.min` do the work, and the
inverse is again of the same shape. -/

theorem strictMono_steepFun : StrictMono (fun x : ℝ => max x (100 * x - 99)) := by
  intro x y hxy
  exact max_lt_max hxy (by linarith)

theorem rightInverse_steepFun :
    Function.RightInverse (fun y : ℝ => min y ((y + 99) / 100))
      (fun x : ℝ => max x (100 * x - 99)) := by
  intro y
  show max (min y ((y + 99) / 100)) (100 * min y ((y + 99) / 100) - 99) = y
  rcases le_total y 1 with hy | hy
  · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring

theorem lipschitzWith_steepFun : LipschitzWith 100 (fun x : ℝ => max x (100 * x - 99)) := by
  have hg : LipschitzWith 100 (fun x : ℝ => 100 * x - 99) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq,
      show (100 : ℝ) * x - 99 - (100 * y - 99) = 100 * (x - y) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 100)]
    norm_num
  have h := LipschitzWith.max (Kf := 1) LipschitzWith.id hg
  simpa using h

theorem lipschitzWith_steepInvFun : LipschitzWith 1 (fun y : ℝ => min y ((y + 99) / 100)) := by
  have hg : LipschitzWith 1 (fun y : ℝ => (y + 99) / 100) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq,
      show (x + 99) / 100 - (y + 99) / 100 = (x - y) / 100 by ring, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 100),
      div_le_iff₀ (by norm_num : (0 : ℝ) < 100)]
    have : (0 : ℝ) ≤ |x - y| := abs_nonneg _
    push_cast
    nlinarith
  have h := LipschitzWith.min (Kf := 1) LipschitzWith.id hg
  simpa using h

/-- The order isomorphism of `ℝ` that is the identity on `Set.Iic 1` and has
slope `100` on `Set.Ici 1`, written as `x ↦ max x (100 * x - 99)`; the two
branches agree at `1`, and the switch is at `1` because `100 * x - 99 ≤ x` if and
only if `x ≤ 1`.  Its inverse is `y ↦ min y ((y + 99) / 100)`. -/
noncomputable def TimeChange.steep : TimeChange ℝ where
  toOrderIso :=
    StrictMono.orderIsoOfRightInverse (fun x => max x (100 * x - 99)) strictMono_steepFun
      (fun y => min y ((y + 99) / 100)) rightInverse_steepFun
  lipschitz := ⟨100, lipschitzWith_steepFun⟩
  lipschitz_symm := ⟨1, lipschitzWith_steepInvFun⟩

theorem strictMono_doubleFun : StrictMono (fun x : ℝ => 2 * x) := by
  intro x y hxy
  simp only
  linarith

theorem rightInverse_doubleFun :
    Function.RightInverse (fun y : ℝ => y / 2) (fun x : ℝ => 2 * x) := by
  intro y
  show 2 * (y / 2) = y
  ring

theorem lipschitzWith_doubleFun : LipschitzWith 2 (fun x : ℝ => 2 * x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, show (2 : ℝ) * x - 2 * y = 2 * (x - y) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem lipschitzWith_doubleInvFun : LipschitzWith 1 (fun y : ℝ => y / 2) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, show x / 2 - y / 2 = (x - y) / 2 by ring, abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : (0 : ℝ) ≤ |x - y| := abs_nonneg _
  push_cast
  nlinarith

/-- The doubling map of `ℝ`, `x ↦ 2 * x`, with inverse `y ↦ y / 2`. -/
noncomputable def TimeChange.double : TimeChange ℝ where
  toOrderIso :=
    StrictMono.orderIsoOfRightInverse (fun x => 2 * x) strictMono_doubleFun
      (fun y => y / 2) rightInverse_doubleFun
  lipschitz := ⟨2, lipschitzWith_doubleFun⟩
  lipschitz_symm := ⟨1, lipschitzWith_doubleInvFun⟩

@[simp] theorem TimeChange.steep_apply (x : ℝ) :
    TimeChange.steep.toOrderIso x = max x (100 * x - 99) := rfl

@[simp] theorem TimeChange.steep_symm_apply (y : ℝ) :
    (TimeChange.steep⁻¹).toOrderIso y = min y ((y + 99) / 100) := rfl

@[simp] theorem TimeChange.double_apply (x : ℝ) :
    TimeChange.double.toOrderIso x = 2 * x := rfl

@[simp] theorem TimeChange.double_symm_apply (y : ℝ) :
    (TimeChange.double⁻¹).toOrderIso y = y / 2 := rfl

/-- Membership in the window `exhaustion (0 : ℝ) 1 = [-1, 1]`, in the only form
the three estimates below use it. -/
theorem mem_exhaustion_real_iff {x : ℝ} : x ∈ exhaustion (0 : ℝ) 1 ↔ -1 ≤ x ∧ x ≤ 1 := by
  simp only [exhaustion, Metric.mem_closedBall, Real.dist_eq, sub_zero, Nat.cast_one]
  exact abs_le

/-- On the window `steep` and its inverse are the identity, so the windowed norm
of `steep` is `log 1 = 0`. -/
theorem TimeChange.normOn_steep_le : TimeChange.normOn (0 : ℝ) 1 TimeChange.steep ≤ 0 := by
  have h1 : TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.steep ≤ 1 := by
    refine csInf_le' ?_
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨_, hx1⟩ := mem_exhaustion_real_iff.1 hx
    obtain ⟨_, hy1⟩ := mem_exhaustion_real_iff.1 hy
    rw [TimeChange.steep_apply, TimeChange.steep_apply, max_eq_left (by linarith),
      max_eq_left (by linarith)]
    simp
  have h2 : TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.steep⁻¹ ≤ 1 := by
    refine csInf_le' ?_
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨_, hx1⟩ := mem_exhaustion_real_iff.1 hx
    obtain ⟨_, hy1⟩ := mem_exhaustion_real_iff.1 hy
    rw [TimeChange.steep_symm_apply, TimeChange.steep_symm_apply,
      min_eq_left (by linarith), min_eq_left (by linarith)]
    simp
  rw [TimeChange.normOn]
  refine Real.log_nonpos (le_trans (by positivity) (le_max_left _ _)) (max_le ?_ ?_)
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- `double` doubles distances and halves them back, so its windowed norm is at
most `log 2`. -/
theorem TimeChange.normOn_double_le :
    TimeChange.normOn (0 : ℝ) 1 TimeChange.double ≤ Real.log 2 := by
  have h1 : TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double ≤ 2 := by
    refine csInf_le' ?_
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [TimeChange.double_apply, TimeChange.double_apply, Real.dist_eq, Real.dist_eq,
      show (2 : ℝ) * x - 2 * y = 2 * (x - y) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double⁻¹ ≤ 2 := by
    refine csInf_le' ?_
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [TimeChange.double_symm_apply, TimeChange.double_symm_apply, Real.dist_eq, Real.dist_eq,
      show x / 2 - y / 2 = (x - y) / 2 by ring, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : (0 : ℝ) ≤ |x - y| := abs_nonneg _
    push_cast
    nlinarith
  have hmax : max ((TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double : ℝ))
      ((TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double⁻¹ : ℝ)) ≤ 2 :=
    max_le (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hnn : (0 : ℝ) ≤ max ((TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double : ℝ))
      ((TimeChange.lipConstOn (0 : ℝ) 1 TimeChange.double⁻¹ : ℝ)) :=
    le_trans (by positivity) (le_max_left _ _)
  rw [TimeChange.normOn]
  rcases eq_or_lt_of_le hnn with h | h
  · rw [← h, Real.log_zero]
    exact le_of_lt (Real.log_pos (by norm_num))
  · exact Real.log_le_log h hmax

/-- The composite `steep * double` sends `1/2` to `1` and `1` to `101`, both of
which lie in the window, so every constant admissible on the window is at least
`200`. This is the whole counterexample: the outer factor is measured on the
image of the window, which the windowed norm does not see. -/
theorem TimeChange.le_normOn_steep_mul_double :
    Real.log 200 ≤ TimeChange.normOn (0 : ℝ) 1 (TimeChange.steep * TimeChange.double) := by
  have happ : ∀ x : ℝ, (TimeChange.steep * TimeChange.double).toOrderIso x
      = max (2 * x) (100 * (2 * x) - 99) := fun _ => rfl
  have h200 : (200 : ℝ≥0) ≤ TimeChange.lipConstOn (0 : ℝ) 1
      (TimeChange.steep * TimeChange.double) := by
    obtain ⟨C, hC⟩ := (TimeChange.steep * TimeChange.double).lipschitz
    refine le_csInf ⟨C, hC.lipschitzOnWith⟩ fun K hK => ?_
    have hm1 : (1 / 2 : ℝ) ∈ exhaustion (0 : ℝ) 1 := mem_exhaustion_real_iff.2 (by norm_num)
    have hm2 : (1 : ℝ) ∈ exhaustion (0 : ℝ) 1 := mem_exhaustion_real_iff.2 (by norm_num)
    have h := (lipschitzOnWith_iff_dist_le_mul.1 hK) (1 / 2 : ℝ) hm1 (1 : ℝ) hm2
    rw [happ, happ, Real.dist_eq, Real.dist_eq] at h
    norm_num at h
    have h' : (200 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast h'
  have hle : (200 : ℝ) ≤ max ((TimeChange.lipConstOn (0 : ℝ) 1
      (TimeChange.steep * TimeChange.double) : ℝ))
      ((TimeChange.lipConstOn (0 : ℝ) 1 (TimeChange.steep * TimeChange.double)⁻¹ : ℝ)) :=
    le_trans (by exact_mod_cast h200) (le_max_left _ _)
  rw [TimeChange.normOn]
  exact Real.log_le_log (by norm_num) hle

/-- **The windowed norm is not a length function.** Measuring the Lipschitz
constants on `exhaustion t₀ m` alone destroys subadditivity, because the inner
factor of a composite need not map the window into itself, and outside it the
outer factor is unconstrained.

The counterexample lives on `ι = ℝ` with `t₀ = 0` and `m = 1`, so
`exhaustion 0 1 = [-1,1]`. Let `l'` be `x ↦ 2 * x` and let `l` be the piecewise
linear order isomorphism that is the identity on `Set.Iic 1` and has slope `100`
on `Set.Ici 1`. Then `l` is the identity on `[-1,1]` and so is `l⁻¹`, whence
`normOn 0 1 l = log 1 = 0`, and `normOn 0 1 l' = log 2`. But
`(l * l') x = l (2 * x)` sends `1/2` to `1` and `1` to `101`, so every admissible
constant on `[-1,1]` is at least `200` and `normOn 0 1 (l * l') ≥ log 200`.
Since `log 200 > log 2 = normOn 0 1 l + normOn 0 1 l'`, the inequality fails, and
it fails by an amount that the outer factor's behaviour outside the window can
make arbitrarily large.

Milestone 4 therefore builds its metric on `TimeChange.norm`, as Billingsley
does: his `d°ₘ` truncates the *paths* to the window and measures the time change
globally. -/
theorem TimeChange.not_normOn_mul_le :
    ¬ ∀ (ι : Type) (_ : LinearOrder ι) (_ : MetricSpace ι) (_ : OrderTopology ι)
        (_ : AdditiveDist ι) (_ : ProperSpace ι) (t₀ : ι) (m : ℕ) (l l' : TimeChange ι),
        TimeChange.normOn t₀ m (l * l') ≤
          TimeChange.normOn t₀ m l + TimeChange.normOn t₀ m l' := by
  intro hcon
  have key := hcon ℝ inferInstance inferInstance inferInstance inferInstance inferInstance
    0 1 TimeChange.steep TimeChange.double
  have hlog2 : Real.log 200 ≤ Real.log 2 := by
    have h1 : TimeChange.normOn (0 : ℝ) 1 TimeChange.steep ≤ 0 :=
      TimeChange.normOn_steep_le
    have h2 : TimeChange.normOn (0 : ℝ) 1 TimeChange.double ≤ Real.log 2 :=
      TimeChange.normOn_double_le
    have h3 : Real.log 200 ≤ TimeChange.normOn (0 : ℝ) 1
        (TimeChange.steep * TimeChange.double) :=
      TimeChange.le_normOn_steep_mul_double
    linarith
  have : Real.log 2 < Real.log 200 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

omit [OrderTopology ι] [ProperSpace ι] in
/-- A time change of small norm moves the points of `exhaustion t₀ m` little.
This is the estimate that makes the metric separate points.

It needs the time change to **fix the base point**, and without that hypothesis
it is false: a translation of `ℝ` is an order isomorphism with `lipConst = 1` in
both directions, so its norm is `0`, while it moves every point by the same
arbitrary amount.  Billingsley gets the anchor for free, because his `Λ` consists
of the increasing homeomorphisms of `[0,∞)` onto itself and they all fix `0`; on
a two sided index it has to be imposed.  The time changes fixing `t₀` are a
subgroup, so nothing else in Milestones 3 and 4 changes.

It needs neither the order topology nor properness, and in particular not the
compactness of `exhaustion t₀ m`: the window enters only through the bound
`dist t₀ t ≤ m`.  What it does need, and it is the first place in Milestone 3
where this happens, is `AdditiveDist`, through `dist_eq_abs_sub_of_sameSide`. -/
theorem TimeChange.dist_le_of_norm_le (t₀ : ι) (m : ℕ) {l : TimeChange ι} {γ : ℝ}
    (h₀ : l.toOrderIso t₀ = t₀) (h : l.norm ≤ γ) {t : ι} (ht : t ∈ exhaustion t₀ m) :
    dist (l.toOrderIso t) t ≤ (Real.exp γ - 1) * (2 * m) := by
  have hγ : 0 ≤ γ := (TimeChange.norm_nonneg l).trans h
  have hE : (1 : ℝ) ≤ Real.exp γ := Real.one_le_exp hγ
  -- both Lipschitz constants are at most `exp γ`; this is `norm λ ≤ γ` undone
  have hmax : max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ) ≤ Real.exp γ := by
    rcases subsingleton_or_nontrivial ι with _ | _
    · rw [TimeChange.lipConst_of_subsingleton, TimeChange.lipConst_of_subsingleton]
      simpa using le_trans zero_le_one hE
    · have h1 : (1 : ℝ) ≤ max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ) := by
        exact_mod_cast TimeChange.one_le_max_lipConst l
      exact (Real.log_le_iff_le_exp (by linarith)).1 h
  have hL : (l.lipConst : ℝ) ≤ Real.exp γ := (le_max_left _ _).trans hmax
  have hLi : ((l⁻¹).lipConst : ℝ) ≤ Real.exp γ := (le_max_right _ _).trans hmax
  -- the image of `t` is squeezed between `e^{-γ}` and `e^{γ}` times its distance
  have hd' : dist t₀ (l.toOrderIso t) ≤ Real.exp γ * dist t₀ t := by
    have h1 := l.lipschitzWith_lipConst.dist_le_mul t₀ t
    rw [h₀] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
  have hd : dist t₀ t ≤ Real.exp γ * dist t₀ (l.toOrderIso t) := by
    have hinv : (l⁻¹).toOrderIso = l.toOrderIso.symm := rfl
    have h1 := (l⁻¹).lipschitzWith_lipConst.dist_le_mul (l.toOrderIso t₀) (l.toOrderIso t)
    rw [hinv] at h1
    simp only [OrderIso.symm_apply_apply] at h1
    rw [h₀] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hLi dist_nonneg)
  -- `t` and its image lie on the same side of `t₀`, so the metric is a difference
  have hside : (t₀ ≤ l.toOrderIso t ∧ t₀ ≤ t) ∨ (l.toOrderIso t ≤ t₀ ∧ t ≤ t₀) := by
    rcases le_total t₀ t with hle | hle
    · refine Or.inl ⟨?_, hle⟩
      calc t₀ = l.toOrderIso t₀ := h₀.symm
        _ ≤ l.toOrderIso t := l.toOrderIso.monotone hle
    · refine Or.inr ⟨?_, hle⟩
      calc l.toOrderIso t ≤ l.toOrderIso t₀ := l.toOrderIso.monotone hle
        _ = t₀ := h₀
  have hm : dist t₀ t ≤ (m : ℝ) := by
    rw [dist_comm]
    simpa only [exhaustion, Metric.mem_closedBall] using ht
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have habs : |dist t₀ t - dist t₀ (l.toOrderIso t)| ≤ (Real.exp γ - 1) * (m : ℝ) := by
    rcases le_total (dist t₀ (l.toOrderIso t)) (dist t₀ t) with hle | hle
    · rw [abs_of_nonneg (by linarith)]
      have hbound : (Real.exp γ - 1) * dist t₀ (l.toOrderIso t)
          ≤ (Real.exp γ - 1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left (hle.trans hm) (by linarith)
      linarith
    · rw [abs_of_nonpos (by linarith)]
      have hbound : (Real.exp γ - 1) * dist t₀ t ≤ (Real.exp γ - 1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm (by linarith)
      linarith
  have hfinal : (Real.exp γ - 1) * (m : ℝ) ≤ (Real.exp γ - 1) * (2 * m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [dist_eq_abs_sub_of_sameSide hside]
  linarith

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem TimeChange.one_toOrderIso_apply (t : ι) : (1 : TimeChange ι).toOrderIso t = t := rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem TimeChange.mul_toOrderIso_apply (l l' : TimeChange ι) (t : ι) :
    (l * l').toOrderIso t = l.toOrderIso (l'.toOrderIso t) := rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The time changes fixing the base point are a subgroup, so `norm_one`,
`norm_inv` and `norm_mul_le` restrict to it unchanged.  It is over this subgroup
that the metric below takes its infimum, because `dist_le_of_norm_le` --- the
estimate that makes the metric separate points --- is false without the
anchor. -/
def TimeChange.fixing (t₀ : ι) : Subgroup (TimeChange ι) where
  carrier := {l | l.toOrderIso t₀ = t₀}
  mul_mem' {a b} ha hb := by
    have ha' : a.toOrderIso t₀ = t₀ := ha
    have hb' : b.toOrderIso t₀ = t₀ := hb
    show (b.toOrderIso.trans a.toOrderIso) t₀ = t₀
    rw [OrderIso.trans_apply, hb', ha']
  one_mem' := rfl
  inv_mem' {a} ha := by
    have ha' : a.toOrderIso t₀ = t₀ := ha
    show a.toOrderIso.symm t₀ = t₀
    refine a.toOrderIso.injective ?_
    rw [OrderIso.apply_symm_apply, ha']

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem TimeChange.mem_fixing_iff {t₀ : ι} {l : TimeChange ι} :
    l ∈ TimeChange.fixing t₀ ↔ l.toOrderIso t₀ = t₀ := Iff.rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Càdlàg paths from `ι` to `E`. -/
structure SkorokhodSpace (ι E : Type*) [LinearOrder ι] [TopologicalSpace ι]
    [TopologicalSpace E] where
  toFun : ι → E
  isCadlag : IsCadlag toFun

@[inherit_doc] notation "D(" ι ", " E ")" => SkorokhodSpace ι E

/-- A path truncated to the window: it agrees with `f` on `exhaustion t₀ m` and
is constant on either side of it.  It is again càdlàg by
`IsCadlag.comp_monotone_continuous`, `clamp` being monotone and continuous. -/
noncomputable def SkorokhodSpace.restrictExhaustion (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    D(ι, E) where
  toFun := f.toFun ∘ clamp t₀ m
  isCadlag :=
    f.isCadlag.comp_monotone_continuous (monotone_clamp t₀ m) (continuous_clamp t₀ m)

omit [AdditiveDist ι] in
@[simp]
theorem SkorokhodSpace.restrictExhaustion_apply (t₀ : ι) (m : ℕ) (f : D(ι, E)) (t : ι) :
    (SkorokhodSpace.restrictExhaustion t₀ m f).toFun t = f.toFun (clamp t₀ m t) := rfl

omit [AdditiveDist ι] in
theorem SkorokhodSpace.restrictExhaustion_eq_self {t₀ : ι} {m : ℕ} {f : D(ι, E)} {t : ι}
    (ht : t ∈ exhaustion t₀ m) :
    (SkorokhodSpace.restrictExhaustion t₀ m f).toFun t = f.toFun t := by
  rw [SkorokhodSpace.restrictExhaustion_apply, clamp_eq_self ht]

/-- The truncated path has bounded range.  This is the one place where the
compactness of the window is spent, and it is what makes the supremum in
`distOn` a real number rather than a junk value. -/
theorem SkorokhodSpace.isBounded_range_restrictExhaustion (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    Bornology.IsBounded (Set.range (SkorokhodSpace.restrictExhaustion t₀ m f).toFun) := by
  refine (f.isCadlag.isBounded_image_of_isCompact (isCompact_exhaustion t₀ m)).subset ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨clamp t₀ m t, clamp_mem_exhaustion t₀ m t, rfl⟩

/-- The supremum defining `distOn` is over a set bounded above, so the `⨆` below
is the supremum and not `0`.  Milestone 4 asks for this explicitly, and it is
where `isBounded_range_restrictExhaustion`, hence the compactness of the window,
is used. -/
theorem SkorokhodSpace.bddAbove_range_dist_restrictExhaustion (t₀ : ι) (m : ℕ)
    (f g : D(ι, E)) (l : TimeChange ι) :
    BddAbove (Set.range fun t : ι =>
      dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun (l.toOrderIso t))
        ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t)) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1
    ((SkorokhodSpace.isBounded_range_restrictExhaustion t₀ m f).union
      (SkorokhodSpace.isBounded_range_restrictExhaustion t₀ m g))
  refine ⟨C, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hC (Or.inl ⟨l.toOrderIso t, rfl⟩) (Or.inr ⟨t, rfl⟩)

/-- Billingsley's `d°ₘ`: the paths are truncated to the window, the time change
is **not**.  The infimum runs over the time changes fixing the base point, and
the norm in it is the global `TimeChange.norm`; the windowed `normOn` is not
subadditive (`TimeChange.not_normOn_mul_le`), so a `distOn` built on it would
have no triangle inequality. -/
noncomputable def SkorokhodSpace.distOn (t₀ : ι) (m : ℕ) (f g : D(ι, E)) : ℝ :=
  ⨅ l : TimeChange.fixing t₀,
    max (TimeChange.norm (l : TimeChange ι))
      (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
          ((l : TimeChange ι).toOrderIso t))
        ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t))

omit [AdditiveDist ι] in
/-- The infimum defining `distOn` is over a set bounded below by `0`, so `ciInf_le`
applies to it. -/
theorem SkorokhodSpace.bddBelow_range_distOn (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    BddBelow (Set.range fun l : TimeChange.fixing t₀ =>
      max (TimeChange.norm (l : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] in
theorem SkorokhodSpace.distOn_nonneg (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    0 ≤ SkorokhodSpace.distOn t₀ m f g :=
  le_ciInf fun _ => le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] in
/-- Symmetry, the first axiom of the metric of Milestone 4, and the first check
that the anchored subgroup is the right index for the infimum: `λ ↦ λ⁻¹` is a
bijection of it, `TimeChange.norm_inv` leaves the norm unchanged, and the
supremum is reindexed along the bijection `λ` of the index. -/
theorem SkorokhodSpace.distOn_comm (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    SkorokhodSpace.distOn t₀ m f g = SkorokhodSpace.distOn t₀ m g f := by
  have hre : ∀ (h₁ h₂ : ι → ℝ) (e : ι → ι), Function.Surjective e →
      (∀ s, h₁ (e s) = h₂ s) → ⨆ t, h₁ t = ⨆ s, h₂ s := by
    intro h₁ h₂ e he hpt
    refine congrArg sSup ?_
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨s, rfl⟩ := he t
      exact ⟨s, (hpt s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨e s, hpt s⟩
  have main : ∀ f g : D(ι, E),
      SkorokhodSpace.distOn t₀ m g f ≤ SkorokhodSpace.distOn t₀ m f g := by
    intro f g
    refine le_ciInf fun l => ?_
    refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ m g f) l⁻¹).trans ?_
    have hnorm : TimeChange.norm ((l⁻¹ : TimeChange.fixing t₀) : TimeChange ι)
        = TimeChange.norm (l : TimeChange ι) := by
      rw [InvMemClass.coe_inv, TimeChange.norm_inv]
    have hsup : ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
          (((l⁻¹ : TimeChange.fixing t₀) : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun t)
        = ⨆ s : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
            ((l : TimeChange ι).toOrderIso s))
            ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun s) := by
      refine hre _ _ ⇑(l : TimeChange ι).toOrderIso (l : TimeChange ι).toOrderIso.surjective
        fun s => ?_
      rw [InvMemClass.coe_inv]
      show dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
          ((l : TimeChange ι).toOrderIso.symm ((l : TimeChange ι).toOrderIso s))) _ = _
      rw [OrderIso.symm_apply_apply, dist_comm]
    rw [hnorm, hsup]
  exact le_antisymm (main g f) (main f g)

omit [AdditiveDist ι] in
/-- The first of the three metric axioms.  The identity is an admissible time
change, its norm is `0`, and the supremum of the constant `0` is `0`. -/
theorem SkorokhodSpace.distOn_self (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    SkorokhodSpace.distOn t₀ m f f = 0 := by
  have : Nonempty ι := ⟨t₀⟩
  refine le_antisymm ?_ (SkorokhodSpace.distOn_nonneg t₀ m f f)
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ m f f) 1).trans ?_
  simp [TimeChange.norm_one]

omit [AdditiveDist ι] in
/-- The infimum in `distOn` is approached.  It need not be attained --- the
subgroup of anchored time changes is not compact in any sense --- so the
triangle inequality below argues with an `ε`, and this is the step that replaces
attainment. -/
theorem SkorokhodSpace.exists_lt_distOn_add (t₀ : ι) (m : ℕ) (f g : D(ι, E)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ l : TimeChange.fixing t₀,
      max (TimeChange.norm (l : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t))
        < SkorokhodSpace.distOn t₀ m f g + δ :=
  exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hδ)

/-- The triangle inequality, the last of the three axioms.  This is the second
place where the anchors have to be a **subgroup** and not merely a set: the time
change that witnesses the composite is `λ * λ'`, and it has to be admissible
again.  The `max` splits into its two halves, `TimeChange.norm_mul_le` carries
the first and the triangle inequality of `E` the second, where the middle path
is evaluated at `λ' t` --- which is why the supremum is taken over all of `ι`
and not over the window, whose image under `λ'` is not the window. -/
theorem SkorokhodSpace.distOn_triangle (t₀ : ι) (m : ℕ) (f g h : D(ι, E)) :
    SkorokhodSpace.distOn t₀ m f h
      ≤ SkorokhodSpace.distOn t₀ m f g + SkorokhodSpace.distOn t₀ m g h := by
  have hι : Nonempty ι := ⟨t₀⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ m f g (half_pos hε)
  obtain ⟨l', hl'⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ m g h (half_pos hε)
  have hS1 : ∀ s : ι,
      dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun ((l : TimeChange ι).toOrderIso s))
        ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun s)
      ≤ ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t) :=
    fun s => le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ m f g _) s
  have hS2 : ∀ s : ι,
      dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun ((l' : TimeChange ι).toOrderIso s))
        ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun s)
      ≤ ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
            ((l' : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun t) :=
    fun s => le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ m g h _) s
  have hterm :
      max (TimeChange.norm ((l * l' : TimeChange.fixing t₀) : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
            (((l * l' : TimeChange.fixing t₀) : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun t))
      ≤ (max (TimeChange.norm (l : TimeChange ι))
          (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
              ((l : TimeChange ι).toOrderIso t))
            ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun t)))
        + max (TimeChange.norm (l' : TimeChange ι))
          (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
              ((l' : TimeChange ι).toOrderIso t))
            ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun t)) := by
    refine max_le ?_ (ciSup_le fun t => ?_)
    · rw [MulMemClass.coe_mul]
      exact (TimeChange.norm_mul_le _ _).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
    · simp only [MulMemClass.coe_mul, TimeChange.mul_toOrderIso_apply]
      calc dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
              ((l : TimeChange ι).toOrderIso ((l' : TimeChange ι).toOrderIso t)))
            ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun t)
          ≤ dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
              ((l : TimeChange ι).toOrderIso ((l' : TimeChange ι).toOrderIso t)))
              ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
                ((l' : TimeChange ι).toOrderIso t))
            + dist ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun
                ((l' : TimeChange ι).toOrderIso t))
              ((SkorokhodSpace.restrictExhaustion t₀ m h).toFun t) := dist_triangle _ _ _
        _ ≤ _ := add_le_add ((hS1 _).trans (le_max_right _ _))
              ((hS2 t).trans (le_max_right _ _))
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ m f h) (l * l')).trans
    (hterm.trans ?_)
  linarith

/-- The separation, the last of the metric axioms of `distOn`: two paths at
`distOn`-distance zero have the same truncation to the window.

The proof does **not** go through the continuity points and their density.  It
uses the time change and its inverse against each other: given `ε`, a time
change `λ` with `norm λ < ε` and `dist (F (λ s)) (G s) < ε` for every `s` either
moves `t` up, and then `F (λ t)` is close to `F t` by the right continuity of
`F`, or it moves `t` down, and then `λ⁻¹` moves `t` up, `G (λ⁻¹ t)` is close to
`G t` by the right continuity of `G`, and the hypothesis read at `λ⁻¹ t` says
`dist (F t) (G (λ⁻¹ t)) < ε`.  Either way `dist (F t) (G t)` is arbitrarily
small.  That is `IsCadlag.eq_of_forall_exists_dist_le`, and it is what makes the
separation independent of the index: the classical argument needs the continuity
points to be dense, which an index of Milestone 1 need not provide. -/
theorem SkorokhodSpace.eq_of_distOn_eq_zero (t₀ : ι) (m : ℕ) (f g : D(ι, E))
    (h : SkorokhodSpace.distOn t₀ m f g = 0) :
    (SkorokhodSpace.restrictExhaustion t₀ m f).toFun
      = (SkorokhodSpace.restrictExhaustion t₀ m g).toFun := by
  have hι : Nonempty ι := ⟨t₀⟩
  -- an approximating time change for every `δ`, both of whose halves are small
  have hstep : ∀ δ > 0, ∃ l : TimeChange.fixing t₀,
      TimeChange.norm (l : TimeChange ι) < δ ∧
        ∀ s, dist ((SkorokhodSpace.restrictExhaustion t₀ m f).toFun
          ((l : TimeChange ι).toOrderIso s))
          ((SkorokhodSpace.restrictExhaustion t₀ m g).toFun s) < δ := by
    intro δ hδ
    obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ m f g hδ
    rw [h, zero_add] at hl
    refine ⟨l, (le_max_left _ _).trans_lt hl, fun s => ?_⟩
    exact lt_of_le_of_lt ((le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion
      t₀ m f g (l : TimeChange ι)) s).trans (le_max_right _ _)) hl
  -- the displacement of a point of the window is small with the norm
  have hsmall : ∀ ρ > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ ≤ η ∧ (Real.exp δ - 1) * (2 * m) < ρ := by
    intro ρ hρ η hη
    have hcont : Tendsto (fun δ : ℝ => (Real.exp δ - 1) * (2 * m)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => (Real.exp δ - 1) * (2 * m)) (𝓝 0)
          (𝓝 ((Real.exp 0 - 1) * (2 * m))) :=
        ((Real.continuous_exp.sub continuous_const).mul continuous_const).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (Real.exp δ - 1) * (2 * m) < ρ := hcont (Iio_mem_nhds hρ)
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ η :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Filter.Eventually.mono (Iio_mem_nhds hη) fun _ hx => hx.le)
    obtain ⟨δ, hδρ, hδη, hδ0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    exact ⟨δ, hδ0, hδη, hδρ⟩
  -- on the window the two truncations agree
  have hwin : ∀ t ∈ exhaustion t₀ m,
      (SkorokhodSpace.restrictExhaustion t₀ m f).toFun t
        = (SkorokhodSpace.restrictExhaustion t₀ m g).toFun t := by
    intro t ht
    refine (SkorokhodSpace.restrictExhaustion t₀ m f).isCadlag.eq_of_forall_exists_dist_le
      (SkorokhodSpace.restrictExhaustion t₀ m g).isCadlag ?_
    intro ρ hρ η hη
    obtain ⟨δ, hδ0, hδη, hδρ⟩ := hsmall ρ hρ η hη
    obtain ⟨l, hlnorm, hldist⟩ := hstep δ hδ0
    have hfix : (l : TimeChange ι).toOrderIso t₀ = t₀ := TimeChange.mem_fixing_iff.1 l.2
    by_cases hcase : t ≤ (l : TimeChange ι).toOrderIso t
    · refine ⟨(l : TimeChange ι).toOrderIso t, hcase, ?_, Or.inl ((hldist t).le.trans hδη)⟩
      exact (TimeChange.dist_le_of_norm_le t₀ m hfix hlnorm.le ht).trans_lt hδρ
    · have hinv : ((l : TimeChange ι)⁻¹).toOrderIso = (l : TimeChange ι).toOrderIso.symm := rfl
      have hts : t ≤ (l : TimeChange ι).toOrderIso.symm t := by
        have := (OrderIso.lt_iff_lt (l : TimeChange ι).toOrderIso.symm).2 (not_le.1 hcase)
        simpa using this.le
      refine ⟨(l : TimeChange ι).toOrderIso.symm t, hts, ?_, Or.inr ?_⟩
      · have hfix' : ((l : TimeChange ι)⁻¹).toOrderIso t₀ = t₀ := by
          rw [hinv]
          exact (l : TimeChange ι).toOrderIso.symm_apply_eq.2 hfix.symm
        have := TimeChange.dist_le_of_norm_le t₀ m hfix'
          (le_of_eq_of_le (TimeChange.norm_inv (l : TimeChange ι)) hlnorm.le) ht
        rw [hinv] at this
        exact this.trans_lt hδρ
      · have := hldist ((l : TimeChange ι).toOrderIso.symm t)
        rw [OrderIso.apply_symm_apply] at this
        exact this.le.trans hδη
  funext t
  have hc := hwin (clamp t₀ m t) (clamp_mem_exhaustion t₀ m t)
  simpa [SkorokhodSpace.restrictExhaustion_apply, clamp_idem] using hc

/-- The separation in the form the metric of `D(ι, E)` consumes it: a path is
determined by its truncations, since every point lies in some window.  The
metric itself is a weighted sum over the windows, and this is the only step of
its separation that is not `SkorokhodSpace.eq_of_distOn_eq_zero`. -/
theorem SkorokhodSpace.eq_of_forall_distOn_eq_zero (t₀ : ι) (f g : D(ι, E))
    (h : ∀ m : ℕ, SkorokhodSpace.distOn t₀ m f g = 0) : f.toFun = g.toFun := by
  funext t
  obtain ⟨m, hm⟩ := exists_nat_ge (dist t₀ t)
  have ht : t ∈ exhaustion t₀ m := by
    simpa [exhaustion, Metric.mem_closedBall, dist_comm t t₀] using hm
  have hc := congrFun (SkorokhodSpace.eq_of_distOn_eq_zero t₀ m f g (h m)) t
  rwa [SkorokhodSpace.restrictExhaustion_eq_self ht,
    SkorokhodSpace.restrictExhaustion_eq_self ht] at hc

/-- The metric of Milestone 4, at a base point: the windowed distances,
truncated at `1` and summed with geometric weights.  The truncation is what
makes the sum converge for every pair of paths -- `distOn` is unbounded as the
window grows -- and it costs nothing, since a metric is only ever read near
`0`. -/
noncomputable def SkorokhodSpace.totalDist (t₀ : ι) (f g : D(ι, E)) : ℝ :=
  ∑' m : ℕ, (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g)

omit [AdditiveDist ι] in
/-- The series is dominated by the geometric one, term by term. -/
theorem SkorokhodSpace.summable_totalDist (t₀ : ι) (f g : D(ι, E)) :
    Summable fun m : ℕ ↦ (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g) := by
  have hgeom : Summable fun m : ℕ ↦ (2 : ℝ)⁻¹ ^ m :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun m ↦ ?_) (fun m ↦ ?_) hgeom
  · exact mul_nonneg (by positivity)
      (le_min zero_le_one (SkorokhodSpace.distOn_nonneg t₀ m f g))
  · exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)

omit [AdditiveDist ι] in
theorem SkorokhodSpace.totalDist_self (t₀ : ι) (f : D(ι, E)) :
    SkorokhodSpace.totalDist t₀ f f = 0 := by
  have h : ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f f) = 0 := by
    intro m
    rw [SkorokhodSpace.distOn_self, min_eq_right zero_le_one, mul_zero]
  show ∑' m : ℕ, (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f f) = 0
  rw [tsum_congr h, tsum_zero]

omit [AdditiveDist ι] in
theorem SkorokhodSpace.totalDist_comm (t₀ : ι) (f g : D(ι, E)) :
    SkorokhodSpace.totalDist t₀ f g = SkorokhodSpace.totalDist t₀ g f :=
  tsum_congr fun m ↦ by rw [SkorokhodSpace.distOn_comm t₀ m f g]

/-- The triangle inequality survives the truncation: `min 1 ·` is subadditive on
the nonnegative reals, so the inequality holds term by term and the two series
are summable. -/
theorem SkorokhodSpace.totalDist_triangle (t₀ : ι) (f g h : D(ι, E)) :
    SkorokhodSpace.totalDist t₀ f h
      ≤ SkorokhodSpace.totalDist t₀ f g + SkorokhodSpace.totalDist t₀ g h := by
  have key : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b + c →
      min 1 a ≤ min 1 b + min 1 c := by
    intro a b c ha hb hc habc
    simp only [min_def]
    split_ifs <;> linarith
  simp only [SkorokhodSpace.totalDist]
  rw [← (SkorokhodSpace.summable_totalDist t₀ f g).tsum_add
    (SkorokhodSpace.summable_totalDist t₀ g h)]
  refine (SkorokhodSpace.summable_totalDist t₀ f h).tsum_le_tsum (fun m ↦ ?_)
    ((SkorokhodSpace.summable_totalDist t₀ f g).add
      (SkorokhodSpace.summable_totalDist t₀ g h))
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact key _ _ _ (SkorokhodSpace.distOn_nonneg t₀ m f h)
    (SkorokhodSpace.distOn_nonneg t₀ m f g) (SkorokhodSpace.distOn_nonneg t₀ m g h)
    (SkorokhodSpace.distOn_triangle t₀ m f g h)

/-- Separation, and the only axiom that is not a term by term computation: a
series of nonnegative terms vanishes only if every term does, so every window
distance is `0`, and `eq_of_forall_distOn_eq_zero` turns that into equality of
the paths. -/
theorem SkorokhodSpace.eq_of_totalDist_eq_zero (t₀ : ι) (f g : D(ι, E))
    (h : SkorokhodSpace.totalDist t₀ f g = 0) : f = g := by
  have hnn : ∀ m : ℕ, 0 ≤ (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g) :=
    fun m ↦ mul_nonneg (by positivity)
      (le_min zero_le_one (SkorokhodSpace.distOn_nonneg t₀ m f g))
  have hz : ∀ m : ℕ, SkorokhodSpace.distOn t₀ m f g = 0 := by
    intro m
    have hle : (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g) ≤ 0 :=
      calc (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g)
          ≤ ∑' k : ℕ, (2 : ℝ)⁻¹ ^ k * min 1 (SkorokhodSpace.distOn t₀ k f g) :=
            (SkorokhodSpace.summable_totalDist t₀ f g).le_tsum m fun j _ ↦ hnn j
        _ = 0 := h
    have hmin : min 1 (SkorokhodSpace.distOn t₀ m f g) ≤ 0 := by
      by_contra hpos
      exact absurd hle (not_le.2 (mul_pos (by positivity) (not_le.1 hpos)))
    rcases min_le_iff.1 hmin with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact le_antisymm h1 (SkorokhodSpace.distOn_nonneg t₀ m f g)
  have hfg : f.toFun = g.toFun := SkorokhodSpace.eq_of_forall_distOn_eq_zero t₀ f g hz
  obtain ⟨f', hf'⟩ := f
  obtain ⟨g', hg'⟩ := g
  have hfun : f' = g' := hfg
  subst hfun
  rfl

/-- The metric space of Milestone 4, with the base point as a parameter: the
metric carries one, since `distOn` is anchored at `t₀` twice over, through the
window `exhaustion t₀ m` and through the subgroup `TimeChange.fixing t₀`, while
`D(ι, E)` knows nothing of one.  The instance is this `def` at the distinguished
point of an index that has one, which is `0` for all four running instances. -/
@[instance_reducible]
noncomputable def SkorokhodSpace.metricSpace (t₀ : ι) : MetricSpace D(ι, E) where
  dist f g := SkorokhodSpace.totalDist t₀ f g
  dist_self := SkorokhodSpace.totalDist_self t₀
  dist_comm := SkorokhodSpace.totalDist_comm t₀
  dist_triangle := SkorokhodSpace.totalDist_triangle t₀
  eq_of_dist_eq_zero h := SkorokhodSpace.eq_of_totalDist_eq_zero t₀ _ _ h

/-- The `sorry` here is not the metric, which is `SkorokhodSpace.metricSpace`
above and carries proofs of all four axioms.  It is the base point: the ten
declarations after this line elaborate against a **parameterless** instance,
which no index supplies on its own.  Whether two base points give the same
topology is not claimed anywhere -- the subgroups `TimeChange.fixing t₀` differ
for different `t₀` -- so the placeholder stands until the ten are rewritten
against `SkorokhodSpace.metricSpace t₀`. -/
noncomputable instance : MetricSpace D(ι, E) := sorry

instance [PolishSpace E] : CompleteSpace D(ι, E) := sorry
instance [PolishSpace E] : TopologicalSpace.SeparableSpace D(ι, E) := sorry
instance [PolishSpace E] : PolishSpace D(ι, E) := sorry

/-- Evaluation is continuous exactly at the paths that do not jump at `t`. -/
theorem SkorokhodSpace.continuousAt_eval {t : ι} {f : D(ι, E)} :
    ContinuousAt (fun g : D(ι, E) => g.toFun t) f ↔
      Function.leftLim f.toFun t = f.toFun t := sorry

/-! ## Milestone 6: the Borel structure

The measurable structure on `D(ι, E)` is the Borel one of the metric above, so
it is declared here rather than assumed; everything in this section is stated
against it. -/

noncomputable instance : MeasurableSpace D(ι, E) := borel _
instance : BorelSpace D(ι, E) := ⟨rfl⟩

variable [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

theorem SkorokhodSpace.measurableEmbedding_piDense {D : Set ι} (hD : D.Countable)
    (hD' : Dense D) :
    MeasurableEmbedding (fun f : D(ι, E) => fun t : D => f.toFun t) := sorry

theorem SkorokhodSpace.borel_eq_iSup_comap_eval :
    (borel D(ι, E)) =
      ⨆ t : ι, MeasurableSpace.comap (fun f : D(ι, E) => f.toFun t) inferInstance :=
  sorry

/-! ## Milestone 7: the modulus and compactness -/

/-- The càdlàg modulus on `exhaustion t₀ m`. -/
noncomputable def SkorokhodSpace.modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) (δ : ℝ) : ℝ := sorry

theorem SkorokhodSpace.tendsto_modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    Tendsto (SkorokhodSpace.modulus t₀ m f) (𝓝[>] 0) (𝓝 0) := sorry

theorem SkorokhodSpace.isCompact_closure_iff (t₀ : ι) (A : Set D(ι, E)) :
    IsCompact (closure A) ↔ ∀ m : ℕ,
      IsCompact (closure {x | ∃ f ∈ A, ∃ t ∈ exhaustion t₀ m, f.toFun t = x}) ∧
      Tendsto (fun δ => ⨆ f ∈ A, SkorokhodSpace.modulus t₀ m f δ) (𝓝[>] 0) (𝓝 0) := sorry


section SigDump
#check @AdditiveDist
#check @exhaustion
#check @isCompact_exhaustion
#check @dist_eq_sub_of_le
#check @monotoneOn_dist_basepoint
#check @dist_eq_abs_sub_of_sameSide
#check @instAdditiveDistSubtype
#check @Real.instAdditiveDist
#check @mem_exhaustion_self
#check @ordConnected_exhaustion
#check @exhaustionMin
#check @isLeast_exhaustionMin
#check @exhaustionMax
#check @isGreatest_exhaustionMax
#check @clamp
#check @monotone_clamp
#check @continuous_clamp
#check @clamp_mem_exhaustion
#check @clamp_eq_self
#check @clamp_idem
#check @exists_orderIso_isometry_real
#check @Function.RightContinuous
#check @IsCadlag
#check @leftJumpSet
#check @largeLeftJumpSet
#check @IsCadlag.tendsto_leftLim
#check @IsCadlag.dist_leftLim_le_of_Ioo_subset
#check @IsCadlag.eventually_dist_leftLim_lt
#check @IsCadlag.finite_largeLeftJumpSet_inter
#check @countable_leftJumpSet
#check @IsCadlag.continuousAt_iff_notMem_leftJumpSet
#check @IsCadlag.continuous_iff_leftJumpSet_eq_empty
#check @IsCadlag.eq_of_forall_exists_dist_le
#check @IsCadlag.measurable
#check @IsCadlag.eq_of_eqOn_dense
#check @IsCadlag.comp_monotone_continuous
#check @IsCadlag.isBounded_image_of_isCompact
#check @TimeChange
#check @TimeChange.ext
#check @TimeChange.exists_lipschitzWith_trans
#check @TimeChange.lipConst
#check @TimeChange.lipConstOn
#check @TimeChange.lipschitzWith_lipConst
#check @TimeChange.lipConst_of_subsingleton
#check @TimeChange.lipConst_one
#check @TimeChange.lipConst_mul_le
#check @TimeChange.norm
#check @TimeChange.normOn
#check @TimeChange.norm_inv
#check @TimeChange.normOn_inv
#check @TimeChange.normOn_one
#check @TimeChange.norm_one
#check @TimeChange.one_le_max_lipConst
#check @TimeChange.norm_nonneg
#check @TimeChange.norm_mul_le
#check @strictMono_steepFun
#check @rightInverse_steepFun
#check @lipschitzWith_steepFun
#check @lipschitzWith_steepInvFun
#check @TimeChange.steep
#check @strictMono_doubleFun
#check @rightInverse_doubleFun
#check @lipschitzWith_doubleFun
#check @lipschitzWith_doubleInvFun
#check @TimeChange.double
#check @mem_exhaustion_real_iff
#check @TimeChange.normOn_steep_le
#check @TimeChange.normOn_double_le
#check @TimeChange.le_normOn_steep_mul_double
#check @TimeChange.not_normOn_mul_le
#check @TimeChange.dist_le_of_norm_le
#check @TimeChange.one_toOrderIso_apply
#check @TimeChange.mul_toOrderIso_apply
#check @TimeChange.fixing
#check @TimeChange.mem_fixing_iff
#check @SkorokhodSpace
#check @SkorokhodSpace.restrictExhaustion
#check @SkorokhodSpace.restrictExhaustion_apply
#check @SkorokhodSpace.restrictExhaustion_eq_self
#check @SkorokhodSpace.isBounded_range_restrictExhaustion
#check @SkorokhodSpace.bddAbove_range_dist_restrictExhaustion
#check @SkorokhodSpace.distOn
#check @SkorokhodSpace.bddBelow_range_distOn
#check @SkorokhodSpace.distOn_nonneg
#check @SkorokhodSpace.distOn_comm
#check @SkorokhodSpace.distOn_self
#check @SkorokhodSpace.exists_lt_distOn_add
#check @SkorokhodSpace.distOn_triangle
#check @SkorokhodSpace.eq_of_distOn_eq_zero
#check @SkorokhodSpace.eq_of_forall_distOn_eq_zero
#check @SkorokhodSpace.totalDist
#check @SkorokhodSpace.summable_totalDist
#check @SkorokhodSpace.totalDist_self
#check @SkorokhodSpace.totalDist_comm
#check @SkorokhodSpace.totalDist_triangle
#check @SkorokhodSpace.eq_of_totalDist_eq_zero
#check @SkorokhodSpace.metricSpace
#check @SkorokhodSpace.continuousAt_eval
#check @SkorokhodSpace.measurableEmbedding_piDense
#check @SkorokhodSpace.borel_eq_iSup_comap_eval
#check @SkorokhodSpace.modulus
#check @SkorokhodSpace.tendsto_modulus
#check @SkorokhodSpace.isCompact_closure_iff
end SigDump
