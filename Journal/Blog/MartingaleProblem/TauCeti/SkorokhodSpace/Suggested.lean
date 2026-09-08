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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Suggested signatures for the Skorokhod space roadmap

Prototypes only. Names and argument orders are suggestions; the statements are
the commitments. `sorry` marks a statement whose proof is the work, never an
empty proposition.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-08.  Every declaration elaborates; the `sorry`s are the statements' own
proofs, which is what this file is for.  There are seven of them: five, plus the
two commitments of Milestone 5 that were withdrawn on 2026-09-08 and are back
because the metric they were false for is no longer the instance.

**`SkorokhodSpace.instMetricSpace` is the integral metric**, since the
twenty-first run of 2026-09-08: it is `SkorokhodSpace.metricSpaceInt basePoint`,
and `SkorokhodSpace.dist_eq` identifies `dist f g` with `intDist basePoint f g`
by `rfl`.  Its four axioms are proved.  Three of them are the corresponding
statement about `SkorokhodSpace.distWith` held at a fixed radius and then
integrated --- `distWith_self`, `distWith_inv`, `distWith_triangle`, then
`intWith_self`, `intWith_inv`, `intWith_triangle`, then `intDist_self`,
`intDist_comm`, `intDist_triangle` --- and the fourth is not, because an infimum
equal to `0` names no radius at all: it yields a sequence of time changes, whose
integrands are summable, hence finite at almost every radius, and
`SkorokhodSpace.eq_of_intDist_eq_zero` runs the fixed radius criterion
`eq_restrictExhaustion_of_forall_exists` at the radii that survive.
`[SecondCountableTopology E]` is the whole price of the integral form, and it is
carried on the instance rather than as a section variable, so that Milestones 6
and 7 draw it from their `[PolishSpace E]`.

Moving the instance was not a rename, and the price is
`SkorokhodSpace.totalTopology`: the two refutation statements of Milestone 5 are
theorems about the **summed** metric and would be false of the instance, so they
name their topology instead of reading it off the instance.  With that,
`CompleteSpace`, `SeparableSpace` and `PolishSpace` for `D(ι, E)` are commitments
again; `SkorokhodSpace.instPolishSpace` owes nothing of its own and is
`inferInstance`, so the two `sorry`s of Milestone 5 are the two the milestone
really owes.

The rung of the completeness proof that the change of metric cost is proved with
it: `SkorokhodSpace.ae_summable_min_one_distWith`.  A small `intDist` is small at
no *named* radius --- that is what the sum got wrong and the integral gets right
--- but a **summable** cost in `intWith` is a summable cost in the window
distance at almost every radius, and a completeness proof may choose its radius.
Everything else Billingsley's argument needs was already proved and is
independent of which metric is the instance.

**The summed metric of the old Milestone 4 is not a Skorokhod metric, and this is
proved here.**
`SkorokhodSpace.dist_exhaustionMax_le_distOn` says that `distOn t₀ m` contains
the undamped number `dist (f b) (g b)` at the window endpoint `b`, for every
admissible time change, because far out on the right the two `clamp`s agree
whatever the time change does.  `SkorokhodSpace.continuous_eval_exhaustionMax`
turns that into the continuity of evaluation at `b`, and
`SkorokhodSpace.exists_jump_continuousAt_eval` exhibits a path of `D(ℝ, ℝ)` that
jumps at `1` and at which evaluation at `1` is continuous nonetheless.  Three
`sorry`s went out with that finding rather than being proved --- `CompleteSpace`,
`SeparableSpace` and the characterisation of the continuity points of
evaluation --- because the first and the third are **false** as they stood; the
first two are back, against the integral metric, and the third stays out.  The
diagnosis, the Cauchy sequence without a limit, and the repair (integrate over
the window radius instead of summing over integer radii, which is what
Ethier--Kurtz do and why they do it) are at the head of Milestone 5 below.
`SkorokhodSpace.distOn` itself survives the repair: it is Ethier--Kurtz's
`d(x, y, λ, u)` and everything proved about it stands.  So do the two lemmas of
Milestone 2 that the corrected completeness argument needs and that the same run
proved: `IsCadlag.of_forall_eventuallyEq`, that being càdlàg is a local
property, and `IsCadlag.of_tendstoUniformlyOn_exhaustion`, that uniform
convergence on every window is enough --- which is the shape the estimate there
actually has.

Since 2026-09-08 the **base point is a typeclass**, `BasePoint`, and with it the
parameterless `MetricSpace D(ι, E)` is a theorem: `SkorokhodSpace.instMetricSpace`
depends on `propext`, `Classical.choice` and `Quot.sound` alone.
`SkorokhodSpace.dist_eq` is its interface, by `rfl`.  Two more `sorry`s went with
it.  (It read `SkorokhodSpace.metricSpace basePoint` when it was written and
reads `SkorokhodSpace.metricSpaceInt basePoint` since; what `BasePoint` supplies
is the same either way.)
And `SkorokhodSpace.modulus` is written out instead of being `sorry` as a
*definition*: `IsSubdivision`, `subdivisionOsc`, `modulus`, with `modulus_mono`
and `modulus_eq_zero_of_exhaustion_subsingleton` proved.  It is `ℝ≥0∞` valued
and the roadmap said `ℝ`; the reason is at the declaration, and it is the empty
subdivision set at large `δ`, which over `ℝ` is a junk `0` that would refute the
monotonicity.

The same run proved `IsCadlag.of_tendstoUniformly`, the first rung of the
completeness of Milestone 5: the uniform limit of càdlàg paths is càdlàg, which
is where the limit path of a Cauchy sequence in `D(ι, E)` is caught.  It belongs
to Milestone 2 and is proved there, out of Mathlib's
`TendstoUniformly.tendsto_of_eventually_tendsto` alone.

The run after it added **the infinite composition of time changes**, which is the
rung that argument hung on: `TimeChange.exists_tendsto_of_summable_norm` and its
quantitative form `TimeChange.exists_tendsto_norm_tail_le`.  The point that is
more than a convergence argument there is the *surjectivity* of the limit, and it
is obtained by running the same estimate on the inverses; the reasoning is at the
declaration.  Those two, together with `min_one_distOn_le`,
`distOn_le_of_two_pow_mul_lt_one` and `totalDist_le_sum_add` --- the passage
between the metric and its windows in both directions --- are the rungs of the
completeness argument, and they are **not** lost with the instance they were
built for: they are statements about `TimeChange` and about `distOn`, and both
survive the repair of the metric unchanged.  What the third run of 2026-09-08
found is that the missing rung, the compatibility of the window limits, is
missing because there is nothing there: the window endpoints obstruct it, and the
obstruction is `SkorokhodSpace.dist_exhaustionMax_le_distOn`.

Since 2026-09-08, twenty-second run, the **assembly** stands as well:
`SkorokhodSpace.tendsto_of_partialComp` builds the limit path out of the
infinite composition and delivers uniform convergence on every window, and
`SkorokhodSpace.exists_gt_summable_distWith` is what feeds it a radius --- the
good radii of `ae_summable_min_one_distWith` are unbounded, because the bad ones
are null while `Set.Ioi c` is not.  What `CompleteSpace D(ι, E)` still owes is
the passage from that locally uniform convergence back to `intDist`, and the one
case of it that is not a limit argument is the window endpoint: `distWith` clamps
the two paths separately, so above `exhaustionMax t₀ u` it reads
`r (x n A) (z A)` off the paths at one point, off by the time change.  Half of
that case is paid: `TimeChange.eq_of_gap_of_norm_lt` says that where the index has
a gap above `A` --- which is exactly when the radii with that endpoint are not a
null set --- every anchored time change of small enough norm fixes `A` outright.

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

Since 2026-09-07, seventh run, the **summed metric is assembled and proved**:
`SkorokhodSpace.totalDist t₀ f g = ∑' m, 2⁻¹ ^ m * min 1 (distOn t₀ m f g)`
with `summable_totalDist`, `totalDist_self`, `totalDist_comm`,
`totalDist_triangle` and `eq_of_totalDist_eq_zero`, and
`SkorokhodSpace.metricSpace (t₀ : ι) : MetricSpace D(ι, E)` built from them.  It
is superseded as the metric of Milestone 4 by `metricSpaceInt` and it is kept,
because the refutation that superseded it is a theorem about it and needs it to
exist: `SkorokhodSpace.totalTopology` is its topology.

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

/-- An index with a distinguished point, the origin of the exhaustion.  The
Skorokhod metric of Milestone 4 is anchored at a point twice over --- through
the window `exhaustion t₀ m` and through the subgroup `TimeChange.fixing t₀` ---
while the type `D(ι, E)` carries none, so the parameterless `MetricSpace`
instance has to read one off the index.  This class is that reading.

It is data and not a `Prop`, and that is the whole point of it: the alternative
`[Nonempty ι]` with `Classical.arbitrary ι` also produces a point, but an opaque
one, about which nothing is provable.  Under it `dist f g` on `D(ℝ, E)` could
never be identified with `totalDist 0 f g`, so not one of the acceptance
examples of Milestones 4 to 7 --- all of which name their base point, and all of
which name `0` --- could be stated, let alone checked, and the explicit `t₀` of
`SkorokhodSpace.isCompact_closure_iff` would silently be a *different* point
from the one the ambient topology is built on.  With `BasePoint` the
identification is `SkorokhodSpace.dist_eq` below, and it is `rfl`. -/
class BasePoint (α : Type*) where
  /-- The distinguished point of the index. -/
  basePoint : α

export BasePoint (basePoint)

variable {ι : Type*} [LinearOrder ι] [MetricSpace ι] [OrderTopology ι]
  [AdditiveDist ι] [ProperSpace ι]

/-- The exhaustion by closed balls around a base point.

**The radius is a real number**, and this is the correction of 2026-09-08: a
metric that sums over a countable set of radii is not a metric for `J₁`
(`SkorokhodSpace.dist_exhaustionMax_le_distOn`), so the metric of Milestone 4
integrates over the radius and the radius has to be able to run over an
interval.  The truncation `max u 0` keeps every declaration below total: a
negative radius would make the window empty, and `exhaustionMin`, `exhaustionMax`
and `clamp` are `def`s that need it inhabited.  For `0 ≤ u` it is the closed
ball, which is `exhaustion_eq_closedBall`. -/
def exhaustion (t₀ : ι) (u : ℝ) : Set ι := Metric.closedBall t₀ (max u 0)

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem exhaustion_eq_closedBall (t₀ : ι) {u : ℝ} (hu : 0 ≤ u) :
    exhaustion t₀ u = Metric.closedBall t₀ u := by
  rw [exhaustion, max_eq_left hu]

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] in
theorem isCompact_exhaustion (t₀ : ι) (u : ℝ) : IsCompact (exhaustion t₀ u) :=
  isCompact_closedBall t₀ _

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

/-- The base point of `ℝ` is `0`, as it is for all four running instances. -/
instance Real.instBasePoint : BasePoint ℝ := ⟨0⟩

/-- The other three running instances go through subtypes, and a subtype is an
index with a base point exactly when it contains the ambient one.  That is a
hypothesis and not an instance, which is the honest form: `Set.Icc (1:ℝ) 2` is
an index of Milestone 1 and has no canonical origin. -/
@[instance_reducible]
def BasePoint.ofMem {α : Type*} [BasePoint α] {s : Set α} (h : basePoint ∈ s) :
    BasePoint s := ⟨⟨basePoint, h⟩⟩

@[simp]
theorem BasePoint.coe_ofMem {α : Type*} [BasePoint α] {s : Set α} (h : basePoint ∈ s) :
    ((@basePoint s (BasePoint.ofMem h)) : α) = basePoint := rfl

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem mem_exhaustion_self (t₀ : ι) (u : ℝ) : t₀ ∈ exhaustion t₀ u :=
  Metric.mem_closedBall_self (by positivity)

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The windows around two base points are cofinal in each other: every window
around `t₀` sits inside a window around `t₁`, at the cost of enlarging the
radius by the distance of the two points.  This is the only relation between two
base points that the metric of Milestone 4 makes available, and it is what any
comparison of `SkorokhodSpace.metricSpace t₀` with `SkorokhodSpace.metricSpace
t₁` has to run on.  The comparison itself is *not* claimed here: the subgroups
`TimeChange.fixing t₀` also differ, and no argument in this file relates them. -/
theorem exhaustion_subset_exhaustion (t₀ t₁ : ι) {u : ℝ} (hu : 0 ≤ u) :
    exhaustion t₀ u ⊆ exhaustion t₁ (u + dist t₀ t₁) := by
  intro t ht
  have hd : (0 : ℝ) ≤ dist t₀ t₁ := dist_nonneg
  simp only [exhaustion, Metric.mem_closedBall, max_eq_left hu,
    max_eq_left (by linarith : (0 : ℝ) ≤ u + dist t₀ t₁)] at ht ⊢
  have h1 : dist t t₁ ≤ dist t t₀ + dist t₀ t₁ := dist_triangle _ _ _
  linarith

omit [OrderTopology ι] [ProperSpace ι] in
/-- The window is an order interval.  This is `AdditiveDist` again, and it is
what makes the clamp below land in the window: above the base point the length
function is monotone, below it the additivity is read from the other end. -/
theorem ordConnected_exhaustion (t₀ : ι) (u : ℝ) : (exhaustion t₀ u).OrdConnected := by
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

/-- The least element of the window; it exists because the window is compact and
contains the base point. -/
noncomputable def exhaustionMin (t₀ : ι) (u : ℝ) : ι :=
  ((isCompact_exhaustion t₀ u).exists_isLeast ⟨t₀, mem_exhaustion_self t₀ u⟩).choose

omit [AdditiveDist ι] in
theorem isLeast_exhaustionMin (t₀ : ι) (u : ℝ) :
    IsLeast (exhaustion t₀ u) (exhaustionMin t₀ u) :=
  ((isCompact_exhaustion t₀ u).exists_isLeast ⟨t₀, mem_exhaustion_self t₀ u⟩).choose_spec

/-- The greatest element of the window. -/
noncomputable def exhaustionMax (t₀ : ι) (u : ℝ) : ι :=
  ((isCompact_exhaustion t₀ u).exists_isGreatest ⟨t₀, mem_exhaustion_self t₀ u⟩).choose

omit [AdditiveDist ι] in
theorem isGreatest_exhaustionMax (t₀ : ι) (u : ℝ) :
    IsGreatest (exhaustion t₀ u) (exhaustionMax t₀ u) :=
  ((isCompact_exhaustion t₀ u).exists_isGreatest ⟨t₀, mem_exhaustion_self t₀ u⟩).choose_spec

/-- The clamp onto the window.  Milestone 4 composes paths with it, so that a
path restricted to `exhaustion t₀ u` is constant outside the window instead of
being undefined there. -/
noncomputable def clamp (t₀ : ι) (u : ℝ) (t : ι) : ι :=
  min (max t (exhaustionMin t₀ u)) (exhaustionMax t₀ u)

omit [AdditiveDist ι] in
theorem monotone_clamp (t₀ : ι) (u : ℝ) : Monotone (clamp t₀ u) :=
  fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

omit [AdditiveDist ι] in
theorem continuous_clamp (t₀ : ι) (u : ℝ) : Continuous (clamp t₀ u) :=
  (continuous_id.max continuous_const).min continuous_const

theorem clamp_mem_exhaustion (t₀ : ι) (u : ℝ) (t : ι) : clamp t₀ u t ∈ exhaustion t₀ u := by
  have hmin := isLeast_exhaustionMin t₀ u
  have hmax := isGreatest_exhaustionMax t₀ u
  have hle : exhaustionMin t₀ u ≤ exhaustionMax t₀ u := hmin.2 hmax.1
  refine (ordConnected_exhaustion t₀ u).out hmin.1 hmax.1 ⟨?_, min_le_right _ _⟩
  exact le_min (le_max_right _ _) hle

omit [AdditiveDist ι] in
theorem clamp_eq_self {t₀ : ι} {u : ℝ} {t : ι} (ht : t ∈ exhaustion t₀ u) :
    clamp t₀ u t = t := by
  rw [clamp, max_eq_left ((isLeast_exhaustionMin t₀ u).2 ht),
    min_eq_left ((isGreatest_exhaustionMax t₀ u).2 ht)]

theorem clamp_idem (t₀ : ι) (u : ℝ) (t : ι) : clamp t₀ u (clamp t₀ u t) = clamp t₀ u t :=
  clamp_eq_self (clamp_mem_exhaustion t₀ u t)

omit [AdditiveDist ι] in
/-- Above the window the clamp is the greatest point of the window.  Innocent as
it looks, this is the half of the clamp that
`SkorokhodSpace.dist_exhaustionMax_le_distOn` reads, and through it the
obstruction of 2026-09-08: far out on the right *both* arguments of the supremum
in `distOn` are clamped to the same point, whatever the time change does. -/
theorem clamp_eq_exhaustionMax_of_le {t₀ : ι} {u : ℝ} {t : ι}
    (h : exhaustionMax t₀ u ≤ t) : clamp t₀ u t = exhaustionMax t₀ u := by
  rw [clamp, min_eq_right (h.trans (le_max_left _ _))]

omit [AdditiveDist ι] in
/-- And the mirror half, below the window. -/
theorem clamp_eq_exhaustionMin_of_le {t₀ : ι} {u : ℝ} {t : ι}
    (h : t ≤ exhaustionMin t₀ u) : clamp t₀ u t = exhaustionMin t₀ u := by
  rw [clamp, max_eq_right h,
    min_eq_left ((isLeast_exhaustionMin t₀ u).2 (isGreatest_exhaustionMax t₀ u).1)]

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The windows around one base point are nested.  This is the case of
`exhaustion_subset_exhaustion` that the exhaustion is named for, and it is
separate because it costs no enlargement of the radius. -/
theorem exhaustion_subset_of_le (t₀ : ι) {u u' : ℝ} (h : u ≤ u') :
    exhaustion t₀ u ⊆ exhaustion t₀ u' :=
  Metric.closedBall_subset_closedBall (max_le_max h le_rfl)

/-- Clamping to a window and then to a larger one changes nothing.  This is the
algebraic backbone of the compatibility of the window limits in Milestone 5: a
path truncated to `exhaustion t₀ u` is already truncated to every larger window,
so the truncations of a single path form a coherent family and the limits taken
window by window have a single candidate to converge to. -/
theorem clamp_clamp_of_le (t₀ : ι) {u u' : ℝ} (h : u ≤ u') (t : ι) :
    clamp t₀ u' (clamp t₀ u t) = clamp t₀ u t :=
  clamp_eq_self (exhaustion_subset_of_le t₀ h (clamp_mem_exhaustion t₀ u t))

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

/-- The set of points where the left limit differs from the value. -/
def leftJumpSet (f : ι → E) : Set ι := {x | Function.leftLim f x ≠ f x}

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
/-- **The uniform limit of càdlàg paths is càdlàg.**  This is the step at which
the completeness of `D(ι, E)` produces its limit path: Billingsley's proof
composes the time changes infinitely and obtains a sequence converging uniformly
on each window, and that its limit lies in `D(ι, E)` and not merely in the
bounded functions is this statement.

Both clauses are instances of Mathlib's
`TendstoUniformly.tendsto_of_eventually_tendsto`
(`Topology/UniformSpace/UniformConvergence.lean:625`) --- right continuity along
`𝓝[>] a` with the values `F n a`, the left limits along `𝓝[<] x` with the left
limits `Function.leftLim (F n) x`.  The two differ in exactly one place, and it
is where `CompleteSpace E` is spent: the values converge because the uniform
limit exists pointwise, while the left limits have to be shown to be a Cauchy
sequence first.  Their limit is `⊥`-safe: when `𝓝[<] x` is the bottom filter the
witness is arbitrary, and the argument is skipped rather than repaired. -/
theorem IsCadlag.of_tendstoUniformly [CompleteSpace E] {F : ℕ → ι → E} {f : ι → E}
    (hF : ∀ n, IsCadlag (F n)) (h : TendstoUniformly F f atTop) : IsCadlag f where
  right_continuous a :=
    h.tendsto_of_eventually_tendsto
      (Eventually.of_forall fun n => (hF n).right_continuous a) (h.tendsto_at a)
  left_limit x := by
    rcases eq_or_neBot (𝓝[<] x) with hx | hx
    · exact ⟨f x, by simp [hx]⟩
    · -- the uniform estimate, in the form the two limits below consume
      have huc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, dist (F n t) (f t) < ε := by
        intro ε hε
        obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 h ε hε)
        exact ⟨N, fun n hn t => by simpa [dist_comm] using hN n hn t⟩
      have hcauchy : CauchySeq fun n => Function.leftLim (F n) x := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨N, hN⟩ := huc (ε / 4) (by linarith)
        refine ⟨N, fun n hn m hm => ?_⟩
        have hlim : Tendsto (fun t => dist (F n t) (F m t)) (𝓝[<] x)
            (𝓝 (dist (Function.leftLim (F n) x) (Function.leftLim (F m) x))) :=
          ((hF n).tendsto_leftLim x).dist ((hF m).tendsto_leftLim x)
        have hle : dist (Function.leftLim (F n) x) (Function.leftLim (F m) x) ≤ ε / 2 := by
          refine le_of_tendsto hlim (Eventually.of_forall fun t => ?_)
          have h1 := hN n hn t
          have h2 := hN m hm t
          have := dist_triangle (F n t) (f t) (F m t)
          rw [dist_comm (f t) (F m t)] at this
          linarith
        linarith
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
      exact ⟨l, h.tendsto_of_eventually_tendsto
        (Eventually.of_forall fun n => (hF n).tendsto_leftLim x) hl⟩

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- **Being càdlàg is local.**  A function that agrees near every point with
*some* càdlàg function is càdlàg.  Both clauses of `IsCadlag` are statements
about `𝓝[>] a` and `𝓝[<] x`, and both filters lie below `𝓝` of their point, so
the whole content is `Filter.Tendsto.congr'`.

This is what `IsCadlag.of_tendstoUniformly` needs beside it in the completeness
argument of Milestone 5: the estimate there holds on windows and not on all of
`ι`, so the limit path is a *locally* uniform limit, and it is caught window by
window --- as `f ∘ clamp t₀ m`, which *is* a global uniform limit --- and then
assembled here, every point lying in the interior of a window. -/
theorem IsCadlag.of_forall_eventuallyEq {f : ι → E}
    (h : ∀ x : ι, ∃ g : ι → E, IsCadlag g ∧ f =ᶠ[𝓝 x] g) : IsCadlag f where
  right_continuous a := by
    obtain ⟨g, hg, hfg⟩ := h a
    have hev : f =ᶠ[𝓝[>] a] g := hfg.filter_mono nhdsWithin_le_nhds
    show Tendsto f (𝓝[Set.Ioi a] a) (𝓝 (f a))
    rw [hfg.eq_of_nhds]
    exact Filter.Tendsto.congr' hev.symm (hg.right_continuous a)
  left_limit x := by
    obtain ⟨g, hg, hfg⟩ := h x
    obtain ⟨l, hl⟩ := hg.left_limit x
    exact ⟨l, Filter.Tendsto.congr' (hfg.filter_mono nhdsWithin_le_nhds).symm hl⟩

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

/-- The form the completeness argument of Milestone 5 consumes
`IsCadlag.of_forall_eventuallyEq` in: uniform convergence **on every window** is
enough.  The passage is the clamp --- `F n ∘ clamp t₀ m` converges uniformly on
all of `ι`, because `clamp` lands in the window --- and the localisation is that
every point lies in the open ball of some integer radius. -/
theorem IsCadlag.of_tendstoUniformlyOn_exhaustion [CompleteSpace E] (t₀ : ι)
    {F : ℕ → ι → E} {f : ι → E} (hF : ∀ n, IsCadlag (F n))
    (h : ∀ m : ℕ, TendstoUniformlyOn F f atTop (exhaustion t₀ m)) : IsCadlag f := by
  refine IsCadlag.of_forall_eventuallyEq fun x => ?_
  obtain ⟨m, hm⟩ := exists_nat_gt (dist x t₀)
  refine ⟨f ∘ clamp t₀ m, ?_, ?_⟩
  · refine IsCadlag.of_tendstoUniformly
      (fun n => (hF n).comp_monotone_continuous (monotone_clamp t₀ m) (continuous_clamp t₀ m)) ?_
    have hpre : clamp t₀ m ⁻¹' exhaustion t₀ m = Set.univ :=
      Set.eq_univ_iff_forall.2 (clamp_mem_exhaustion t₀ m)
    have hc := (h m).comp (clamp t₀ m)
    rwa [hpre, tendstoUniformlyOn_univ] at hc
  · have hnhds : exhaustion t₀ m ∈ 𝓝 x :=
      mem_nhds_iff.2 ⟨Metric.ball t₀ m,
        Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (le_max_left _ _)),
        Metric.isOpen_ball,
        Metric.mem_ball.2 hm⟩
    filter_upwards [hnhds] with t ht
    show f t = f (clamp t₀ m t)
    rw [clamp_eq_self ht]

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

/-! ### A countable set that computes suprema of right continuous functions

This is what the integral metric of Milestone 4 needs and nothing else in the
file did: for the integrand `u ↦ ⨆ t, r (f (clamp u (λ t))) (g (clamp u t))` to
be integrable it has first to be measurable, and a supremum over the whole
index is not.  A countable **dense** set does not suffice, and the obstruction
is real: on `ι = Set.Icc (0:ℝ) 1` the set `D = ℚ ∩ [0,1)` is dense, and a right
continuous function may exceed its supremum over `D` at the point `1`, which is
approached from the left only.  What has to be added to a dense set is the set
of points that are approached from the right by nothing, and the content of
`countable_rightIsolated` is that there are only countably many of them. -/

variable (ι) in
/-- The points of the index at which nothing lies immediately to the right.
The definition is the closedness-free form `IsOpen (Set.Iic t)`, which is
equivalent to `𝓝[>] t = ⊥` and is the form both proofs below consume: it says
that `t` has an open neighbourhood not meeting `Set.Ioi t`, up to the
always-open `Set.Iio t`. -/
def rightIsolated : Set ι := {t : ι | IsOpen (Set.Iic t)}

omit [AdditiveDist ι] [ProperSpace ι] in
/-- A point which no open set separates from its right is not right isolated.
This is the direction the supremum lemma uses. -/
theorem nonempty_inter_Ioi_of_notMem_rightIsolated {t : ι} (ht : t ∉ rightIsolated ι)
    {W : Set ι} (hW : IsOpen W) (htW : t ∈ W) : (W ∩ Set.Ioi t).Nonempty := by
  rcases Set.eq_empty_or_nonempty (W ∩ Set.Ioi t) with hempty | hne
  · refine absurd ?_ ht
    have hsub : W ⊆ Set.Iic t := by
      intro x hx
      by_contra hxt
      exact (Set.eq_empty_iff_forall_notMem.1 hempty x) ⟨hx, not_le.1 hxt⟩
    have heq : Set.Iic t = Set.Iio t ∪ W := by
      refine Set.Subset.antisymm (fun x hx => ?_)
        (Set.union_subset Set.Iio_subset_Iic_self hsub)
      rcases lt_or_eq_of_le (Set.mem_Iic.1 hx) with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ htW)
    show IsOpen (Set.Iic t)
    rw [heq]
    exact isOpen_Iio.union hW
  · exact hne

omit [OrderTopology ι] [AdditiveDist ι] in
/-- **There are only countably many right isolated points.**  The proof is
intrinsic --- it does not go through the embedding of the index into `ℝ`, which
is still `exists_orderIso_isometry_real` and still a `sorry`.  For a right
isolated `t` the set `Set.Iic t` is open, so a countable basis has a member `v`
with `t ∈ v ⊆ Set.Iic t`; and that assignment is injective, because
`v s = v t` forces `s ≤ t` and `t ≤ s` at once.  Second countability is the
only hypothesis, and the index has it from `ProperSpace`. -/
theorem countable_rightIsolated : (rightIsolated ι).Countable := by
  have hbasis := TopologicalSpace.isBasis_countableBasis ι
  have : Countable (TopologicalSpace.countableBasis ι) :=
    (TopologicalSpace.countable_countableBasis ι).to_subtype
  rw [← Set.countable_coe_iff]
  have key : ∀ t : rightIsolated ι, ∃ v : TopologicalSpace.countableBasis ι,
      (t : ι) ∈ (v : Set ι) ∧ (v : Set ι) ⊆ Set.Iic (t : ι) := by
    intro t
    obtain ⟨v, hv, htv, hsub⟩ :=
      hbasis.exists_subset_of_mem_open (Set.mem_Iic.2 le_rfl) t.2
    exact ⟨⟨v, hv⟩, htv, hsub⟩
  choose φ hmem hsub using key
  refine Function.Injective.countable (f := φ) fun s t hst => ?_
  have h1 : (s : ι) ≤ (t : ι) := Set.mem_Iic.1 (hsub t (hst ▸ hmem s))
  have h2 : (t : ι) ≤ (s : ι) := Set.mem_Iic.1 (hsub s (hst.symm ▸ hmem t))
  exact Subtype.ext (le_antisymm h1 h2)

omit [AdditiveDist ι] in
/-- **One countable set computes the supremum of every right continuous
function on the index.**  It is a countable dense set together with the
countably many right isolated points, and it is what makes the integrand of the
metric of Milestone 4 measurable: the supremum over the index is a supremum
over a countable family, hence measurable in the window radius as soon as each
member is.

The set does not depend on the function, which is the whole point --- a
supremum-approximating sequence would depend on it, and a different countable
set for every radius computes nothing. -/
theorem exists_countable_ciSup_eq [Nonempty ι] :
    ∃ C : Set ι, C.Countable ∧ C.Nonempty ∧
      ∀ h : ι → ℝ, Function.RightContinuous h → BddAbove (Set.range h) →
        ⨆ t : ι, h t = ⨆ t : C, h (t : ι) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  refine ⟨D ∪ rightIsolated ι, hDc.union countable_rightIsolated,
    (hDd.nonempty).mono Set.subset_union_left, fun h hrc hbdd => ?_⟩
  set C : Set ι := D ∪ rightIsolated ι with hC
  have hCne : C.Nonempty := (hDd.nonempty).mono Set.subset_union_left
  have : Nonempty C := hCne.to_subtype
  have hbddC : BddAbove (Set.range fun t : C => h (t : ι)) :=
    hbdd.mono (by rintro _ ⟨t, rfl⟩; exact ⟨(t : ι), rfl⟩)
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun t => le_ciSup hbdd (t : ι))
  by_contra hcon
  have hlt : (⨆ s : C, h (s : ι)) < h t := not_le.1 hcon
  by_cases hti : t ∈ rightIsolated ι
  · exact absurd (le_ciSup hbddC (⟨t, Or.inr hti⟩ : C)) (not_le.2 hlt)
  -- `h` stays above the supremum just to the right of `t`, and there the
  -- dense set has a point
  have hIoi : h ⁻¹' Set.Ioi (⨆ t : C, h (t : ι)) ∈ 𝓝[>] t :=
    hrc t (Ioi_mem_nhds hlt)
  obtain ⟨W, hW, htW, hWsub⟩ := mem_nhdsWithin.1 hIoi
  obtain ⟨x, hx⟩ := nonempty_inter_Ioi_of_notMem_rightIsolated hti hW htW
  obtain ⟨d, hdD, hdW⟩ :=
    hDd.exists_mem_open (hW.inter isOpen_Ioi) ⟨x, hx⟩
  have hdmem : d ∈ C := Or.inl hdD
  have : (⨆ t : C, h (t : ι)) < h d := hWsub ⟨hdW.1, hdW.2⟩
  exact absurd (le_ciSup hbddC (⟨d, hdmem⟩ : C)) (not_le.2 this)

/-! ## Milestones 3 and 4: time changes and the metric -/

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

/-- The least Lipschitz constant. Mathlib carries no least Lipschitz constant:
`LipschitzWith (K : ℝ≥0) (f : α → β)`
(`Mathlib/Topology/EMetricSpace/Lipschitz.lean`) is a `Prop`, and
`LipschitzWith.const` there is the theorem that a constant map is `0`-Lipschitz,
not a constant attached to a map. -/
noncomputable def TimeChange.lipConst (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzWith K l.toOrderIso}

/-- The same constant computed on `exhaustion t₀ m` only. -/
noncomputable def TimeChange.lipConstOn (t₀ : ι) (u : ℝ) (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzOnWith K l.toOrderIso (exhaustion t₀ u)}

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

/-- `log` of the larger of the two Lipschitz constants. This is Billingsley's
`‖λ‖`, and it is a **global** quantity: the windowed `normOn` below is not a
length function, see `TimeChange.not_normOn_mul_le`. -/
noncomputable def TimeChange.norm (l : TimeChange ι) : ℝ :=
  Real.log (max l.lipConst l⁻¹.lipConst)

/-- The same, computed on `exhaustion t₀ m`. It is a lower bound for `norm` and
nothing more; the metric of Milestone 4 uses `norm`. -/
noncomputable def TimeChange.normOn (t₀ : ι) (u : ℝ) (l : TimeChange ι) : ℝ :=
  Real.log (max (TimeChange.lipConstOn t₀ u l) (TimeChange.lipConstOn t₀ u l⁻¹))

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.norm_inv (l : TimeChange ι) : (l⁻¹).norm = l.norm := by
  rw [TimeChange.norm, TimeChange.norm, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.normOn_inv (t₀ : ι) (u : ℝ) (l : TimeChange ι) :
    TimeChange.normOn t₀ u l⁻¹ = TimeChange.normOn t₀ u l := by
  rw [TimeChange.normOn, TimeChange.normOn, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The two cases the proof has to distinguish, and they are the reason the
statement is true at all: on an `exhaustion t₀ u` with two distinct points the
set of admissible constants for the identity is `Set.Ici 1`, so `lipConstOn` is
`1` and its logarithm is `0`; on a one point exhaustion -- `u = 0` in a discrete
index -- every constant is admissible, `lipConstOn` is `0`, and `Real.log 0 = 0`
by Mathlib's convention.  The junk value of `Real.log` is what carries the
degenerate case, which is worth saying out loud rather than leaving to the
reader. -/
theorem TimeChange.normOn_one (t₀ : ι) (u : ℝ) :
    TimeChange.normOn t₀ u (1 : TimeChange ι) = 0 := by
  have hone : ∀ t : ι, (1 : TimeChange ι).toOrderIso t = t := fun _ => rfl
  have key : TimeChange.lipConstOn t₀ u (1 : TimeChange ι) = 0 ∨
      TimeChange.lipConstOn t₀ u (1 : TimeChange ι) = 1 := by
    rw [TimeChange.lipConstOn]
    by_cases hs : (exhaustion t₀ u).Subsingleton
    · refine Or.inl (le_antisymm (csInf_le' ?_) zero_le)
      show LipschitzOnWith (0 : ℝ≥0) ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ u)
      intro a ha b hb
      simp [hone, hs ha hb]
    · obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hs
      have hmem : LipschitzOnWith 1 ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ u) := by
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
  simp only [exhaustion, Metric.mem_closedBall, Real.dist_eq, sub_zero,
    max_eq_left (zero_le_one' ℝ)]
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
        (_ : AdditiveDist ι) (_ : ProperSpace ι) (t₀ : ι) (u : ℝ) (l l' : TimeChange ι),
        TimeChange.normOn t₀ u (l * l') ≤
          TimeChange.normOn t₀ u l + TimeChange.normOn t₀ u l' := by
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
theorem TimeChange.dist_le_of_norm_le (t₀ : ι) {u : ℝ} (hu : 0 ≤ u) {l : TimeChange ι}
    {γ : ℝ} (h₀ : l.toOrderIso t₀ = t₀) (h : l.norm ≤ γ) {t : ι} (ht : t ∈ exhaustion t₀ u) :
    dist (l.toOrderIso t) t ≤ (Real.exp γ - 1) * (2 * u) := by
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
  have hm : dist t₀ t ≤ (u : ℝ) := by
    rw [dist_comm]
    simpa only [exhaustion, Metric.mem_closedBall, max_eq_left hu] using ht
  have hm0 : (0 : ℝ) ≤ (u : ℝ) := hu
  have habs : |dist t₀ t - dist t₀ (l.toOrderIso t)| ≤ (Real.exp γ - 1) * (u : ℝ) := by
    rcases le_total (dist t₀ (l.toOrderIso t)) (dist t₀ t) with hle | hle
    · rw [abs_of_nonneg (by linarith)]
      have hbound : (Real.exp γ - 1) * dist t₀ (l.toOrderIso t)
          ≤ (Real.exp γ - 1) * (u : ℝ) :=
        mul_le_mul_of_nonneg_left (hle.trans hm) (by linarith)
      linarith
    · rw [abs_of_nonpos (by linarith)]
      have hbound : (Real.exp γ - 1) * dist t₀ t ≤ (Real.exp γ - 1) * (u : ℝ) :=
        mul_le_mul_of_nonneg_left hm (by linarith)
      linarith
  have hfinal : (Real.exp γ - 1) * (u : ℝ) ≤ (Real.exp γ - 1) * (2 * u) :=
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

/-! ### The infinite composition of time changes

This is the second of the three named steps of `CompleteSpace D(ι, E)` in
Milestone 5.  Billingsley composes infinitely many time changes along the
exhaustion; what follows is that composition, and the point where it is more than
a convergence argument is the **surjectivity** of the limit.  A pointwise limit of
order isomorphisms is monotone and injective for free, but nothing forces it onto
`ι`.  The device that supplies it here is to run the *same* argument on the
inverses: `μ n ⁻¹` satisfies the same summable estimate, because
`(μ n * l n)⁻¹ = (l n)⁻¹ * μ n ⁻¹` moves a point by exactly the displacement of
`l n ⁻¹`, so it has a limit `M` as well, and `μ n (μ n ⁻¹ t) = t` passes to the
limit through the uniform Lipschitz bound.  The limit is therefore a bijection
with a named inverse, and not merely an embedding. -/

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The least Lipschitz constant is at most the exponential of the norm.  This is
`TimeChange.norm` read forwards rather than backwards, and it is what turns the
length function of Milestone 3 into a Lipschitz bound uniform along a composition
whose norms are summable. -/
theorem TimeChange.lipConst_le_exp_norm (l : TimeChange ι) :
    (l.lipConst : ℝ) ≤ Real.exp l.norm := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · rw [TimeChange.lipConst_of_subsingleton]
    simpa using (Real.exp_pos l.norm).le
  · have h1 : (1 : ℝ) ≤ max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ) := by
      exact_mod_cast TimeChange.one_le_max_lipConst l
    rw [TimeChange.norm, Real.exp_log (by linarith)]
    exact le_max_left _ _

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The estimate `lipConst_le_exp_norm` in the form the composition consumes it. -/
theorem TimeChange.dist_le_exp_norm_mul (l : TimeChange ι) (s t : ι) :
    dist (l.toOrderIso s) (l.toOrderIso t) ≤ Real.exp l.norm * dist s t :=
  (l.lipschitzWith_lipConst.dist_le_mul s t).trans
    (mul_le_mul_of_nonneg_right l.lipConst_le_exp_norm dist_nonneg)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The converse of `lipConst_le_exp_norm`: two Lipschitz bounds with the same
constant `exp γ`, one for `l` and one for `l⁻¹`, bound the norm by `γ`.  The
degenerate branch is the subsingleton index, where `lipConst` is `0` and
`Real.log 0 = 0 ≤ γ` carries the statement. -/
theorem TimeChange.norm_le_of_lipschitzWith {l : TimeChange ι} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : LipschitzWith (Real.exp γ).toNNReal l.toOrderIso)
    (h' : LipschitzWith (Real.exp γ).toNNReal l⁻¹.toOrderIso) :
    l.norm ≤ γ := by
  have hK : (((Real.exp γ).toNNReal : ℝ≥0) : ℝ) = Real.exp γ :=
    Real.coe_toNNReal _ (Real.exp_pos γ).le
  have hb : ∀ m : TimeChange ι, LipschitzWith (Real.exp γ).toNNReal m.toOrderIso →
      (m.lipConst : ℝ) ≤ Real.exp γ := by
    intro m hm
    have hle : m.lipConst ≤ (Real.exp γ).toNNReal := csInf_le' hm
    calc (m.lipConst : ℝ) ≤ (((Real.exp γ).toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast hle
      _ = Real.exp γ := hK
  have hmax : max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ) ≤ Real.exp γ :=
    max_le (hb l h) (hb l⁻¹ h')
  rw [TimeChange.norm]
  rcases lt_or_ge (0 : ℝ) (max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ)) with hpos | hz
  · calc Real.log (max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ))
        ≤ Real.log (Real.exp γ) := Real.log_le_log hpos hmax
      _ = γ := Real.log_exp γ
  · have hzero : max (l.lipConst : ℝ) ((l⁻¹).lipConst : ℝ) = 0 :=
      le_antisymm hz (le_max_of_le_left (NNReal.coe_nonneg _))
    rw [hzero, Real.log_zero]
    exact hγ

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The partial compositions `l 0 ∘ l 1 ∘ ⋯ ∘ l (n-1)`.  The order matters and it
is this one: `partialComp l (n + 1) = partialComp l n * l n` appends the new time
change on the **inside**, so that `partialComp l (n+1) t` differs from
`partialComp l n t` by the displacement of `l n` alone, magnified by the Lipschitz
constant of the already assembled prefix.  Appending on the outside would leave
the displacement to be estimated on the moving image of `t` instead. -/
def TimeChange.partialComp (l : ℕ → TimeChange ι) : ℕ → TimeChange ι
  | 0 => 1
  | n + 1 => TimeChange.partialComp l n * l n

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem TimeChange.partialComp_zero (l : ℕ → TimeChange ι) :
    TimeChange.partialComp l 0 = 1 := rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
@[simp]
theorem TimeChange.partialComp_succ (l : ℕ → TimeChange ι) (n : ℕ) :
    TimeChange.partialComp l (n + 1) = TimeChange.partialComp l n * l n := rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The anchors are a subgroup, so the composition stays anchored. -/
theorem TimeChange.partialComp_mem_fixing {t₀ : ι} {l : ℕ → TimeChange ι}
    (hl : ∀ n, l n ∈ TimeChange.fixing t₀) (n : ℕ) :
    TimeChange.partialComp l n ∈ TimeChange.fixing t₀ := by
  induction n with
  | zero => exact (TimeChange.fixing t₀).one_mem
  | succ n ih => exact (TimeChange.fixing t₀).mul_mem ih (hl n)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The norm is a length function, so it is subadditive along the composition.
This is the only place where `TimeChange.norm_mul_le` is spent, and it is why the
norm of Milestone 3 had to be the global one. -/
theorem TimeChange.norm_partialComp_le (l : ℕ → TimeChange ι) (n : ℕ) :
    (TimeChange.partialComp l n).norm ≤ ∑ i ∈ Finset.range n, (l i).norm := by
  induction n with
  | zero => simpa using TimeChange.norm_one.le
  | succ n ih =>
      rw [TimeChange.partialComp_succ, Finset.sum_range_succ]
      exact (TimeChange.norm_mul_le _ _).trans (add_le_add ih le_rfl)

/-- **The infinite composition.**  If the norms of `l 0, l 1, …` are dominated by
a summable `γ`, then the partial compositions converge pointwise to a time change
`L`, again anchored at `t₀`, and `L` obeys the same bound `‖L‖ ≤ ∑' γ` that the
partial compositions do.

Three ingredients, and each is needed for a different reason.  The uniform bound
`‖partialComp l n‖ ≤ ∑' γ` makes every partial composition `exp (∑' γ)`-Lipschitz,
which is what converts a displacement of `l n` into a displacement of the whole
prefix.  `TimeChange.dist_le_of_norm_le` converts `‖l n‖ ≤ γ n` into that
displacement on a window, and `Real.exp x - 1 ≤ x * exp x` makes the resulting
bound summable rather than merely null.  Properness of `ι` supplies the limit;
this is the one statement of Milestones 3 to 5 that consumes it for something
other than the compactness of a window.

The inverse limit `M` is constructed alongside and is the whole content of the
surjectivity: without it `L` is an order embedding with closed image and there is
no argument in this generality that its image is all of `ι` --- the index is not
assumed connected, and on a disconnected index the image of a monotone continuous
map need not be cofinal in the gaps. -/
theorem TimeChange.exists_tendsto_of_summable_norm (t₀ : ι) (l : ℕ → TimeChange ι)
    (hl : ∀ n, l n ∈ TimeChange.fixing t₀) (γ : ℕ → ℝ)
    (hγ : ∀ n, (l n).norm ≤ γ n) (hs : Summable γ) :
    ∃ L : TimeChange ι, L ∈ TimeChange.fixing t₀ ∧ L.norm ≤ ∑' i, γ i ∧
      ∀ t : ι, Tendsto (fun n => (TimeChange.partialComp l n).toOrderIso t) atTop
        (𝓝 (L.toOrderIso t)) := by
  classical
  have hγ0 : ∀ n, 0 ≤ γ n := fun n => (TimeChange.norm_nonneg (l n)).trans (hγ n)
  have hγΓ : ∀ n, γ n ≤ ∑' i, γ i := fun n => hs.le_tsum n fun j _ => hγ0 j
  have hΓ0 : (0 : ℝ) ≤ ∑' i, γ i := (hγ0 0).trans (hγΓ 0)
  have hpcfix : ∀ n, TimeChange.partialComp l n ∈ TimeChange.fixing t₀ :=
    TimeChange.partialComp_mem_fixing hl
  have hpcnorm : ∀ n, (TimeChange.partialComp l n).norm ≤ ∑' i, γ i := by
    intro n
    refine (TimeChange.norm_partialComp_le l n).trans ?_
    exact (Finset.sum_le_sum fun i _ => hγ i).trans
      (Summable.sum_le_tsum _ (fun j _ => hγ0 j) hs)
  have hexp1 : ∀ x : ℝ, Real.exp x - 1 ≤ x * Real.exp x := by
    intro x
    have h := Real.add_one_le_exp (-x)
    have h2 : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    nlinarith
  have hlipfwd : ∀ (n : ℕ) (s t : ι),
      dist ((TimeChange.partialComp l n).toOrderIso s)
        ((TimeChange.partialComp l n).toOrderIso t) ≤ Real.exp (∑' i, γ i) * dist s t := by
    intro n s t
    exact (TimeChange.dist_le_exp_norm_mul _ s t).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hpcnorm n)) dist_nonneg)
  have hlipbwd : ∀ (n : ℕ) (s t : ι),
      dist ((TimeChange.partialComp l n)⁻¹.toOrderIso s)
        ((TimeChange.partialComp l n)⁻¹.toOrderIso t) ≤ Real.exp (∑' i, γ i) * dist s t := by
    intro n s t
    refine (TimeChange.dist_le_exp_norm_mul _ s t).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) dist_nonneg)
    rw [TimeChange.norm_inv]
    exact hpcnorm n
  have hmem : ∀ t : ι, ∃ m : ℕ, t ∈ exhaustion t₀ m := by
    intro t
    obtain ⟨m, hm⟩ := exists_nat_ge (dist t₀ t)
    exact ⟨m, by simpa [exhaustion, Metric.mem_closedBall, dist_comm t t₀] using hm⟩
  -- the forward step estimate, summable in `n` and uniform on the window
  have hstep : ∀ (m : ℕ) (t : ι), t ∈ exhaustion t₀ m → ∀ n : ℕ,
      dist ((TimeChange.partialComp l n).toOrderIso t)
        ((TimeChange.partialComp l (n + 1)).toOrderIso t)
        ≤ (Real.exp (∑' i, γ i) * (Real.exp (∑' i, γ i) * (2 * m))) * γ n := by
    intro m t ht n
    have hmove : dist ((l n).toOrderIso t) t ≤ (Real.exp (γ n) - 1) * (2 * m) :=
      TimeChange.dist_le_of_norm_le t₀ (m.cast_nonneg)
        (TimeChange.mem_fixing_iff.1 (hl n)) (hγ n) ht
    have h1 : Real.exp (γ n) - 1 ≤ γ n * Real.exp (∑' i, γ i) :=
      (hexp1 (γ n)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hγΓ n)) (hγ0 n))
    have h2 : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
    have hmove' : dist ((l n).toOrderIso t) t
        ≤ (Real.exp (∑' i, γ i) * (2 * m)) * γ n := by
      refine hmove.trans ?_
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    have heq : (TimeChange.partialComp l (n + 1)).toOrderIso t
        = (TimeChange.partialComp l n).toOrderIso ((l n).toOrderIso t) := rfl
    rw [heq]
    calc dist ((TimeChange.partialComp l n).toOrderIso t)
          ((TimeChange.partialComp l n).toOrderIso ((l n).toOrderIso t))
        ≤ Real.exp (∑' i, γ i) * dist t ((l n).toOrderIso t) := hlipfwd n _ _
      _ ≤ Real.exp (∑' i, γ i) * ((Real.exp (∑' i, γ i) * (2 * m)) * γ n) := by
          rw [dist_comm t]
          exact mul_le_mul_of_nonneg_left hmove' (Real.exp_pos _).le
      _ = (Real.exp (∑' i, γ i) * (Real.exp (∑' i, γ i) * (2 * m))) * γ n := by ring
  -- and the same for the inverses, on the enlarged window the prefix cannot leave
  have hstepinv : ∀ (m : ℕ) (t : ι), t ∈ exhaustion t₀ m → ∀ n : ℕ,
      dist ((TimeChange.partialComp l n)⁻¹.toOrderIso t)
        ((TimeChange.partialComp l (n + 1))⁻¹.toOrderIso t)
        ≤ (Real.exp (∑' i, γ i) * (2 * (⌈Real.exp (∑' i, γ i) * m⌉₊ : ℕ))) * γ n := by
    intro m t ht n
    have hufix : (TimeChange.partialComp l n)⁻¹.toOrderIso t₀ = t₀ :=
      TimeChange.mem_fixing_iff.1 ((TimeChange.fixing t₀).inv_mem (hpcfix n))
    have humem : (TimeChange.partialComp l n)⁻¹.toOrderIso t
        ∈ exhaustion t₀ ⌈Real.exp (∑' i, γ i) * m⌉₊ := by
      have htm : dist t₀ t ≤ (m : ℝ) := by
        rw [dist_comm]
        simpa [exhaustion, Metric.mem_closedBall] using ht
      have hd : dist t₀ ((TimeChange.partialComp l n)⁻¹.toOrderIso t)
          ≤ Real.exp (∑' i, γ i) * dist t₀ t := by
        nth_rewrite 1 [← hufix]
        exact hlipbwd n t₀ t
      have hd' : dist t₀ ((TimeChange.partialComp l n)⁻¹.toOrderIso t)
          ≤ Real.exp (∑' i, γ i) * m :=
        hd.trans (mul_le_mul_of_nonneg_left htm (Real.exp_pos _).le)
      have hceil : Real.exp (∑' i, γ i) * m ≤ (⌈Real.exp (∑' i, γ i) * m⌉₊ : ℝ) :=
        Nat.le_ceil _
      simpa [exhaustion, Metric.mem_closedBall,
        dist_comm ((TimeChange.partialComp l n)⁻¹.toOrderIso t) t₀] using hd'.trans hceil
    have heq : (TimeChange.partialComp l (n + 1))⁻¹.toOrderIso t
        = (l n)⁻¹.toOrderIso ((TimeChange.partialComp l n)⁻¹.toOrderIso t) := by
      show ((TimeChange.partialComp l n * l n)⁻¹).toOrderIso t = _
      rw [mul_inv_rev]
      rfl
    rw [heq, dist_comm]
    have hmove : dist ((l n)⁻¹.toOrderIso ((TimeChange.partialComp l n)⁻¹.toOrderIso t))
        ((TimeChange.partialComp l n)⁻¹.toOrderIso t)
        ≤ (Real.exp (γ n) - 1) * (2 * (⌈Real.exp (∑' i, γ i) * m⌉₊ : ℕ)) := by
      refine TimeChange.dist_le_of_norm_le t₀ (Nat.cast_nonneg _)
        (TimeChange.mem_fixing_iff.1 ((TimeChange.fixing t₀).inv_mem (hl n))) ?_ humem
      rw [TimeChange.norm_inv]
      exact hγ n
    refine hmove.trans ?_
    have h1 : Real.exp (γ n) - 1 ≤ γ n * Real.exp (∑' i, γ i) :=
      (hexp1 (γ n)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hγΓ n)) (hγ0 n))
    have h2 : (0 : ℝ) ≤ 2 * ((⌈Real.exp (∑' i, γ i) * m⌉₊ : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  -- the two limits
  have hcvgfwd : ∀ t : ι, ∃ y, Tendsto (fun n => (TimeChange.partialComp l n).toOrderIso t)
      atTop (𝓝 y) := by
    intro t
    obtain ⟨m, ht⟩ := hmem t
    exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable _ (hstep m t ht) (hs.mul_left _))
  have hcvgbwd : ∀ t : ι, ∃ y, Tendsto (fun n => (TimeChange.partialComp l n)⁻¹.toOrderIso t)
      atTop (𝓝 y) := by
    intro t
    obtain ⟨m, ht⟩ := hmem t
    exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable _ (hstepinv m t ht) (hs.mul_left _))
  choose L hL using hcvgfwd
  choose M hM using hcvgbwd
  have hmonoL : Monotone L := fun s t hst =>
    le_of_tendsto_of_tendsto' (hL s) (hL t) fun n =>
      (TimeChange.partialComp l n).toOrderIso.monotone hst
  have hmonoM : Monotone M := fun s t hst =>
    le_of_tendsto_of_tendsto' (hM s) (hM t) fun n =>
      (TimeChange.partialComp l n)⁻¹.toOrderIso.monotone hst
  have hlipL : ∀ s t : ι, dist (L s) (L t) ≤ Real.exp (∑' i, γ i) * dist s t := fun s t =>
    le_of_tendsto ((hL s).dist (hL t)) (Eventually.of_forall fun n => hlipfwd n s t)
  have hlipM : ∀ s t : ι, dist (M s) (M t) ≤ Real.exp (∑' i, γ i) * dist s t := fun s t =>
    le_of_tendsto ((hM s).dist (hM t)) (Eventually.of_forall fun n => hlipbwd n s t)
  -- the two inverse relations, and this is the surjectivity
  have hLM : ∀ t : ι, L (M t) = t := by
    intro t
    have hid : ∀ n : ℕ, (TimeChange.partialComp l n).toOrderIso
        ((TimeChange.partialComp l n)⁻¹.toOrderIso t) = t := fun n =>
      OrderIso.apply_symm_apply _ _
    have hbd : ∀ n : ℕ, dist t (L (M t)) ≤
        Real.exp (∑' i, γ i) * dist ((TimeChange.partialComp l n)⁻¹.toOrderIso t) (M t)
          + dist ((TimeChange.partialComp l n).toOrderIso (M t)) (L (M t)) := by
      intro n
      calc dist t (L (M t))
          = dist ((TimeChange.partialComp l n).toOrderIso
              ((TimeChange.partialComp l n)⁻¹.toOrderIso t)) (L (M t)) := by rw [hid n]
        _ ≤ dist ((TimeChange.partialComp l n).toOrderIso
              ((TimeChange.partialComp l n)⁻¹.toOrderIso t))
              ((TimeChange.partialComp l n).toOrderIso (M t))
            + dist ((TimeChange.partialComp l n).toOrderIso (M t)) (L (M t)) :=
            dist_triangle _ _ _
        _ ≤ _ := add_le_add (hlipfwd n _ _) le_rfl
    have ha : Tendsto (fun n => dist ((TimeChange.partialComp l n)⁻¹.toOrderIso t) (M t))
        atTop (𝓝 0) := by
      simpa using (hM t).dist (tendsto_const_nhds (x := M t) (f := (atTop : Filter ℕ)))
    have hb : Tendsto (fun n => dist ((TimeChange.partialComp l n).toOrderIso (M t)) (L (M t)))
        atTop (𝓝 0) := by
      simpa using (hL (M t)).dist (tendsto_const_nhds (x := L (M t)) (f := (atTop : Filter ℕ)))
    have hzero : dist t (L (M t)) ≤ 0 := by
      have htend := (ha.const_mul (Real.exp (∑' i, γ i))).add hb
      exact ge_of_tendsto (by simpa using htend) (Eventually.of_forall hbd)
    exact (dist_le_zero.1 hzero).symm
  have hML : ∀ t : ι, M (L t) = t := by
    intro t
    have hid : ∀ n : ℕ, (TimeChange.partialComp l n)⁻¹.toOrderIso
        ((TimeChange.partialComp l n).toOrderIso t) = t := fun n =>
      OrderIso.symm_apply_apply _ _
    have hbd : ∀ n : ℕ, dist t (M (L t)) ≤
        Real.exp (∑' i, γ i) * dist ((TimeChange.partialComp l n).toOrderIso t) (L t)
          + dist ((TimeChange.partialComp l n)⁻¹.toOrderIso (L t)) (M (L t)) := by
      intro n
      calc dist t (M (L t))
          = dist ((TimeChange.partialComp l n)⁻¹.toOrderIso
              ((TimeChange.partialComp l n).toOrderIso t)) (M (L t)) := by rw [hid n]
        _ ≤ dist ((TimeChange.partialComp l n)⁻¹.toOrderIso
              ((TimeChange.partialComp l n).toOrderIso t))
              ((TimeChange.partialComp l n)⁻¹.toOrderIso (L t))
            + dist ((TimeChange.partialComp l n)⁻¹.toOrderIso (L t)) (M (L t)) :=
            dist_triangle _ _ _
        _ ≤ _ := add_le_add (hlipbwd n _ _) le_rfl
    have ha : Tendsto (fun n => dist ((TimeChange.partialComp l n).toOrderIso t) (L t))
        atTop (𝓝 0) := by
      simpa using (hL t).dist (tendsto_const_nhds (x := L t) (f := (atTop : Filter ℕ)))
    have hb : Tendsto (fun n => dist ((TimeChange.partialComp l n)⁻¹.toOrderIso (L t)) (M (L t)))
        atTop (𝓝 0) := by
      simpa using (hM (L t)).dist (tendsto_const_nhds (x := M (L t)) (f := (atTop : Filter ℕ)))
    have hzero : dist t (M (L t)) ≤ 0 := by
      have htend := (ha.const_mul (Real.exp (∑' i, γ i))).add hb
      exact ge_of_tendsto (by simpa using htend) (Eventually.of_forall hbd)
    exact (dist_le_zero.1 hzero).symm
  -- assembling the limit into a time change
  have hKco : (((Real.exp (∑' i, γ i)).toNNReal : ℝ≥0) : ℝ) = Real.exp (∑' i, γ i) :=
    Real.coe_toNNReal _ (Real.exp_pos _).le
  have hLlip : LipschitzWith (Real.exp (∑' i, γ i)).toNNReal L :=
    LipschitzWith.of_dist_le_mul fun x y => by rw [hKco]; exact hlipL x y
  have hMlip : LipschitzWith (Real.exp (∑' i, γ i)).toNNReal M :=
    LipschitzWith.of_dist_le_mul fun x y => by rw [hKco]; exact hlipM x y
  have hrel : ∀ a b : ι, L a ≤ L b ↔ a ≤ b := by
    intro a b
    refine ⟨fun h => ?_, fun h => hmonoL h⟩
    have := hmonoM h
    rwa [hML a, hML b] at this
  refine ⟨{ toOrderIso := { toEquiv := ⟨L, M, hML, hLM⟩, map_rel_iff' := fun {a b} => hrel a b },
            lipschitz := ⟨_, hLlip⟩,
            lipschitz_symm := ⟨_, hMlip⟩ }, ?_, ?_, fun t => hL t⟩
  · show L t₀ = t₀
    refine tendsto_nhds_unique (hL t₀) ?_
    have : ∀ n : ℕ, (TimeChange.partialComp l n).toOrderIso t₀ = t₀ := fun n =>
      TimeChange.mem_fixing_iff.1 (hpcfix n)
    simp [this]
  · exact TimeChange.norm_le_of_lipschitzWith hΓ0 hLlip hMlip

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The composition splits at any stage into its first `n` factors and the rest.
This is what turns the limit above into a **tail** estimate, and the tail estimate
is what a convergence proof in `D(ι, E)` reads: after `n` steps the part of the
limit time change still to be performed is `(partialComp l n)⁻¹ * L`. -/
theorem TimeChange.partialComp_add (l : ℕ → TimeChange ι) (n k : ℕ) :
    TimeChange.partialComp l (n + k)
      = TimeChange.partialComp l n * TimeChange.partialComp (fun i => l (n + i)) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      show TimeChange.partialComp l (n + k + 1) = _
      simp only [TimeChange.partialComp_succ]
      rw [ih, mul_assoc]

/-- The infinite composition **with a rate**: the norm of what the first `n`
factors have left undone is at most the tail `∑' i, γ (n + i)` of the dominating
series.  Without it `exists_tendsto_of_summable_norm` only says that a limit
exists, which is not enough to see that a Cauchy sequence of paths converges *to
it*; with it the `n`-th approximation is quantitatively close.

The proof runs the existence theorem once more on each shifted sequence and
identifies `L` with `partialComp l n * (the shifted limit)` by uniqueness of
limits: `partialComp l (n + k) = partialComp l n * partialComp (l ∘ (n + ·)) k` is
a tail of the original sequence, so both sides converge to the same point. -/
theorem TimeChange.exists_tendsto_norm_tail_le (t₀ : ι) (l : ℕ → TimeChange ι)
    (hl : ∀ n, l n ∈ TimeChange.fixing t₀) (γ : ℕ → ℝ)
    (hγ : ∀ n, (l n).norm ≤ γ n) (hs : Summable γ) :
    ∃ L : TimeChange ι, L ∈ TimeChange.fixing t₀ ∧
      (∀ n : ℕ, ((TimeChange.partialComp l n)⁻¹ * L).norm ≤ ∑' i, γ (n + i)) ∧
      ∀ t : ι, Tendsto (fun n => (TimeChange.partialComp l n).toOrderIso t) atTop
        (𝓝 (L.toOrderIso t)) := by
  obtain ⟨L, hLfix, -, hLconv⟩ :=
    TimeChange.exists_tendsto_of_summable_norm t₀ l hl γ hγ hs
  have hshift : ∀ n : ℕ, ∃ N : TimeChange ι, N ∈ TimeChange.fixing t₀ ∧
      N.norm ≤ ∑' i, γ (n + i) ∧
      ∀ t : ι, Tendsto (fun k => (TimeChange.partialComp (fun i => l (n + i)) k).toOrderIso t)
        atTop (𝓝 (N.toOrderIso t)) := fun n =>
    TimeChange.exists_tendsto_of_summable_norm t₀ (fun i => l (n + i))
      (fun i => hl (n + i)) (fun i => γ (n + i)) (fun i => hγ (n + i))
      (hs.comp_injective (add_right_injective n))
  choose N _ hNnorm hNconv using hshift
  refine ⟨L, hLfix, fun n => ?_, hLconv⟩
  have key : L = TimeChange.partialComp l n * N n := by
    refine TimeChange.ext (DFunLike.ext _ _ fun t => ?_)
    have h1 : Tendsto (fun k => (TimeChange.partialComp l (n + k)).toOrderIso t) atTop
        (𝓝 (L.toOrderIso t)) := by
      have h := (hLconv t).comp (tendsto_add_atTop_nat n)
      simpa [Function.comp_def, Nat.add_comm] using h
    have h2 : Tendsto (fun k => (TimeChange.partialComp l (n + k)).toOrderIso t) atTop
        (𝓝 ((TimeChange.partialComp l n * N n).toOrderIso t)) := by
      have hc : Continuous ⇑(TimeChange.partialComp l n).toOrderIso :=
        (TimeChange.partialComp l n).lipschitzWith_lipConst.continuous
      refine Filter.Tendsto.congr (fun k => ?_)
        ((hc.tendsto ((N n).toOrderIso t)).comp (hNconv n t))
      show (TimeChange.partialComp l n).toOrderIso
        ((TimeChange.partialComp (fun i => l (n + i)) k).toOrderIso t) = _
      rw [TimeChange.partialComp_add]
      rfl
    exact tendsto_nhds_unique h1 h2
  rw [key, inv_mul_cancel_left]
  exact hNnorm n

/-- Càdlàg paths from `ι` to `E`. -/
structure SkorokhodSpace (ι E : Type*) [LinearOrder ι] [TopologicalSpace ι]
    [TopologicalSpace E] where
  toFun : ι → E
  isCadlag : IsCadlag toFun

@[inherit_doc] notation "D(" ι ", " E ")" => SkorokhodSpace ι E

/-- A path truncated to the window: it agrees with `f` on `exhaustion t₀ m` and
is constant on either side of it.  It is again càdlàg by
`IsCadlag.comp_monotone_continuous`, `clamp` being monotone and continuous. -/
noncomputable def SkorokhodSpace.restrictExhaustion (t₀ : ι) (u : ℝ) (f : D(ι, E)) :
    D(ι, E) where
  toFun := f.toFun ∘ clamp t₀ u
  isCadlag :=
    f.isCadlag.comp_monotone_continuous (monotone_clamp t₀ u) (continuous_clamp t₀ u)

omit [AdditiveDist ι] in
@[simp]
theorem SkorokhodSpace.restrictExhaustion_apply (t₀ : ι) (u : ℝ) (f : D(ι, E)) (t : ι) :
    (SkorokhodSpace.restrictExhaustion t₀ u f).toFun t = f.toFun (clamp t₀ u t) := rfl

omit [AdditiveDist ι] in
theorem SkorokhodSpace.restrictExhaustion_eq_self {t₀ : ι} {u : ℝ} {f : D(ι, E)} {t : ι}
    (ht : t ∈ exhaustion t₀ u) :
    (SkorokhodSpace.restrictExhaustion t₀ u f).toFun t = f.toFun t := by
  rw [SkorokhodSpace.restrictExhaustion_apply, clamp_eq_self ht]

/-- Truncating to a large window and then to a small one is truncating to the
small one.  Stated on `toFun` rather than on `D(ι, E)`, in the style of the
separation lemmas of Milestone 4, because `SkorokhodSpace` carries no `ext`
lemma.  This is the coherence that
`SkorokhodSpace.exists_restrictExhaustion_limit` of Milestone 5 will read: the
truncations of one path to the successive windows determine each other in the
one direction that a limit argument needs, and the family of window limits has to
be checked against exactly this. -/
theorem SkorokhodSpace.restrictExhaustion_restrictExhaustion (t₀ : ι) {u u' : ℝ}
    (h : u ≤ u') (f : D(ι, E)) :
    (SkorokhodSpace.restrictExhaustion t₀ u
        (SkorokhodSpace.restrictExhaustion t₀ u' f)).toFun
      = (SkorokhodSpace.restrictExhaustion t₀ u f).toFun := by
  funext t
  simp only [SkorokhodSpace.restrictExhaustion_apply]
  rw [clamp_clamp_of_le t₀ h]

/-- The truncated path has bounded range.  This is the one place where the
compactness of the window is spent, and it is what makes the supremum in
`distOn` a real number rather than a junk value. -/
theorem SkorokhodSpace.isBounded_range_restrictExhaustion (t₀ : ι) (u : ℝ) (f : D(ι, E)) :
    Bornology.IsBounded (Set.range (SkorokhodSpace.restrictExhaustion t₀ u f).toFun) := by
  refine (f.isCadlag.isBounded_image_of_isCompact (isCompact_exhaustion t₀ u)).subset ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨clamp t₀ u t, clamp_mem_exhaustion t₀ u t, rfl⟩

/-- The supremum defining `distOn` is over a set bounded above, so the `⨆` below
is the supremum and not `0`.  Milestone 4 asks for this explicitly, and it is
where `isBounded_range_restrictExhaustion`, hence the compactness of the window,
is used. -/
theorem SkorokhodSpace.bddAbove_range_dist_restrictExhaustion (t₀ : ι) (u : ℝ)
    (f g : D(ι, E)) (l : TimeChange ι) :
    BddAbove (Set.range fun t : ι =>
      dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun (l.toOrderIso t))
        ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t)) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1
    ((SkorokhodSpace.isBounded_range_restrictExhaustion t₀ u f).union
      (SkorokhodSpace.isBounded_range_restrictExhaustion t₀ u g))
  refine ⟨C, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hC (Or.inl ⟨l.toOrderIso t, rfl⟩) (Or.inr ⟨t, rfl⟩)

/-- Billingsley's `d°ₘ`: the paths are truncated to the window, the time change
is **not**.  The infimum runs over the time changes fixing the base point, and
the norm in it is the global `TimeChange.norm`; the windowed `normOn` is not
subadditive (`TimeChange.not_normOn_mul_le`), so a `distOn` built on it would
have no triangle inequality. -/
noncomputable def SkorokhodSpace.distOn (t₀ : ι) (u : ℝ) (f g : D(ι, E)) : ℝ :=
  ⨅ l : TimeChange.fixing t₀,
    max (TimeChange.norm (l : TimeChange ι))
      (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
          ((l : TimeChange ι).toOrderIso t))
        ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t))

omit [AdditiveDist ι] in
/-- The infimum defining `distOn` is over a set bounded below by `0`, so `ciInf_le`
applies to it. -/
theorem SkorokhodSpace.bddBelow_range_distOn (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    BddBelow (Set.range fun l : TimeChange.fixing t₀ =>
      max (TimeChange.norm (l : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] in
theorem SkorokhodSpace.distOn_nonneg (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    0 ≤ SkorokhodSpace.distOn t₀ u f g :=
  le_ciInf fun _ => le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] in
/-- Symmetry, the first axiom of the metric of Milestone 4, and the first check
that the anchored subgroup is the right index for the infimum: `λ ↦ λ⁻¹` is a
bijection of it, `TimeChange.norm_inv` leaves the norm unchanged, and the
supremum is reindexed along the bijection `λ` of the index. -/
theorem SkorokhodSpace.distOn_comm (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    SkorokhodSpace.distOn t₀ u f g = SkorokhodSpace.distOn t₀ u g f := by
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
      SkorokhodSpace.distOn t₀ u g f ≤ SkorokhodSpace.distOn t₀ u f g := by
    intro f g
    refine le_ciInf fun l => ?_
    refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ u g f) l⁻¹).trans ?_
    have hnorm : TimeChange.norm ((l⁻¹ : TimeChange.fixing t₀) : TimeChange ι)
        = TimeChange.norm (l : TimeChange ι) := by
      rw [InvMemClass.coe_inv, TimeChange.norm_inv]
    have hsup : ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
          (((l⁻¹ : TimeChange.fixing t₀) : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun t)
        = ⨆ s : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            ((l : TimeChange ι).toOrderIso s))
            ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun s) := by
      refine hre _ _ ⇑(l : TimeChange ι).toOrderIso (l : TimeChange ι).toOrderIso.surjective
        fun s => ?_
      rw [InvMemClass.coe_inv]
      show dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
          ((l : TimeChange ι).toOrderIso.symm ((l : TimeChange ι).toOrderIso s))) _ = _
      rw [OrderIso.symm_apply_apply, dist_comm]
    rw [hnorm, hsup]
  exact le_antisymm (main g f) (main f g)

omit [AdditiveDist ι] in
/-- The first of the three metric axioms.  The identity is an admissible time
change, its norm is `0`, and the supremum of the constant `0` is `0`. -/
theorem SkorokhodSpace.distOn_self (t₀ : ι) (u : ℝ) (f : D(ι, E)) :
    SkorokhodSpace.distOn t₀ u f f = 0 := by
  have : Nonempty ι := ⟨t₀⟩
  refine le_antisymm ?_ (SkorokhodSpace.distOn_nonneg t₀ u f f)
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ u f f) 1).trans ?_
  simp [TimeChange.norm_one]

/-! ### The window endpoints are read off `distOn`

The two statements that follow are the **obstruction of 2026-09-08**, and they
are the reason Milestone 5 carries no `CompleteSpace` instance any more.

`distOn t₀ u` truncates the two paths with `clamp t₀ u` and lets the time change
`l` range over all of `TimeChange.fixing t₀`.  Take `t` beyond both
`exhaustionMax t₀ u` and `l⁻¹ (exhaustionMax t₀ u)`.  Then `clamp t₀ u t` and
`clamp t₀ u (l t)` are *both* `exhaustionMax t₀ u`, so the supremum in `distOn`
contains the plain number `dist (f b) (g b)` --- and it does so for **every**
`l`, so the infimum cannot get below it.

The consequence is `SkorokhodSpace.continuous_eval_exhaustionMax`: evaluation at
a window endpoint is continuous for the metric of Milestone 4, at every path,
jump or no jump.  For the Skorokhod topology it is continuous exactly at the
paths that do not jump there, so the metric of Milestone 4 is **not** a
Skorokhod metric, and `SkorokhodSpace.exists_jump_continuousAt_eval` says so in
one concrete instance.  Ethier--Kurtz avoid this by integrating over the window
radius rather than summing over integer radii; the bad radii of a pair of paths
are countably many, hence Lebesgue null, and the integral does not see them. -/

/-- **The right window endpoint is a lower bound for `distOn`.**  No time change
can separate the two paths at `exhaustionMax t₀ u`, because every `t` far enough
to the right has both `clamp t₀ u t` and `clamp t₀ u (l t)` equal to it. -/
theorem SkorokhodSpace.dist_exhaustionMax_le_distOn (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    dist (f.toFun (exhaustionMax t₀ u)) (g.toFun (exhaustionMax t₀ u))
      ≤ SkorokhodSpace.distOn t₀ u f g := by
  refine le_ciInf fun l => le_trans ?_ (le_max_right _ _)
  obtain ⟨t, h1, h2⟩ : ∃ t : ι, clamp t₀ u t = exhaustionMax t₀ u ∧
      clamp t₀ u ((l : TimeChange ι).toOrderIso t) = exhaustionMax t₀ u := by
    refine ⟨max ((l : TimeChange ι).toOrderIso.symm (exhaustionMax t₀ u))
        (exhaustionMax t₀ u), clamp_eq_exhaustionMax_of_le (le_max_right _ _),
      clamp_eq_exhaustionMax_of_le ?_⟩
    have h := (l : TimeChange ι).toOrderIso.monotone
      (le_max_left ((l : TimeChange ι).toOrderIso.symm (exhaustionMax t₀ u))
        (exhaustionMax t₀ u))
    rwa [OrderIso.apply_symm_apply] at h
  refine le_trans (le_of_eq ?_)
    (le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g
      (l : TimeChange ι)) t)
  rw [SkorokhodSpace.restrictExhaustion_apply, SkorokhodSpace.restrictExhaustion_apply, h1, h2]

/-- The mirror statement at the left window endpoint. -/
theorem SkorokhodSpace.dist_exhaustionMin_le_distOn (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    dist (f.toFun (exhaustionMin t₀ u)) (g.toFun (exhaustionMin t₀ u))
      ≤ SkorokhodSpace.distOn t₀ u f g := by
  refine le_ciInf fun l => le_trans ?_ (le_max_right _ _)
  obtain ⟨t, h1, h2⟩ : ∃ t : ι, clamp t₀ u t = exhaustionMin t₀ u ∧
      clamp t₀ u ((l : TimeChange ι).toOrderIso t) = exhaustionMin t₀ u := by
    refine ⟨min ((l : TimeChange ι).toOrderIso.symm (exhaustionMin t₀ u))
        (exhaustionMin t₀ u), clamp_eq_exhaustionMin_of_le (min_le_right _ _),
      clamp_eq_exhaustionMin_of_le ?_⟩
    have h := (l : TimeChange ι).toOrderIso.monotone
      (min_le_left ((l : TimeChange ι).toOrderIso.symm (exhaustionMin t₀ u))
        (exhaustionMin t₀ u))
    rwa [OrderIso.apply_symm_apply] at h
  refine le_trans (le_of_eq ?_)
    (le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g
      (l : TimeChange ι)) t)
  rw [SkorokhodSpace.restrictExhaustion_apply, SkorokhodSpace.restrictExhaustion_apply, h1, h2]

omit [AdditiveDist ι] in
/-- The infimum in `distOn` is approached.  It need not be attained --- the
subgroup of anchored time changes is not compact in any sense --- so the
triangle inequality below argues with an `ε`, and this is the step that replaces
attainment. -/
theorem SkorokhodSpace.exists_lt_distOn_add (t₀ : ι) (u : ℝ) (f g : D(ι, E)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ l : TimeChange.fixing t₀,
      max (TimeChange.norm (l : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t))
        < SkorokhodSpace.distOn t₀ u f g + δ :=
  exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hδ)

/-- The triangle inequality, the last of the three axioms.  This is the second
place where the anchors have to be a **subgroup** and not merely a set: the time
change that witnesses the composite is `λ * λ'`, and it has to be admissible
again.  The `max` splits into its two halves, `TimeChange.norm_mul_le` carries
the first and the triangle inequality of `E` the second, where the middle path
is evaluated at `λ' t` --- which is why the supremum is taken over all of `ι`
and not over the window, whose image under `λ'` is not the window. -/
theorem SkorokhodSpace.distOn_triangle (t₀ : ι) (u : ℝ) (f g h : D(ι, E)) :
    SkorokhodSpace.distOn t₀ u f h
      ≤ SkorokhodSpace.distOn t₀ u f g + SkorokhodSpace.distOn t₀ u g h := by
  have hι : Nonempty ι := ⟨t₀⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ u f g (half_pos hε)
  obtain ⟨l', hl'⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ u g h (half_pos hε)
  have hS1 : ∀ s : ι,
      dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun ((l : TimeChange ι).toOrderIso s))
        ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun s)
      ≤ ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            ((l : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t) :=
    fun s => le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g _) s
  have hS2 : ∀ s : ι,
      dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun ((l' : TimeChange ι).toOrderIso s))
        ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun s)
      ≤ ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
            ((l' : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t) :=
    fun s => le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u g h _) s
  have hterm :
      max (TimeChange.norm ((l * l' : TimeChange.fixing t₀) : TimeChange ι))
        (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            (((l * l' : TimeChange.fixing t₀) : TimeChange ι).toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t))
      ≤ (max (TimeChange.norm (l : TimeChange ι))
          (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
              ((l : TimeChange ι).toOrderIso t))
            ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t)))
        + max (TimeChange.norm (l' : TimeChange ι))
          (⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
              ((l' : TimeChange ι).toOrderIso t))
            ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t)) := by
    refine max_le ?_ (ciSup_le fun t => ?_)
    · rw [MulMemClass.coe_mul]
      exact (TimeChange.norm_mul_le _ _).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
    · simp only [MulMemClass.coe_mul, TimeChange.mul_toOrderIso_apply]
      calc dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
              ((l : TimeChange ι).toOrderIso ((l' : TimeChange ι).toOrderIso t)))
            ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t)
          ≤ dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
              ((l : TimeChange ι).toOrderIso ((l' : TimeChange ι).toOrderIso t)))
              ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
                ((l' : TimeChange ι).toOrderIso t))
            + dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
                ((l' : TimeChange ι).toOrderIso t))
              ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t) := dist_triangle _ _ _
        _ ≤ _ := add_le_add ((hS1 _).trans (le_max_right _ _))
              ((hS2 t).trans (le_max_right _ _))
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_distOn t₀ u f h) (l * l')).trans
    (hterm.trans ?_)
  linarith

/-- **The separation criterion at a fixed window radius**, and the shape both
metrics read it in: if for every `δ` there is an anchored time change of norm
below `δ` that carries the one truncation to within `δ` of the other, uniformly
in the index, then the two truncations are equal.  `distOn` supplies the
hypothesis by unwinding its infimum (`eq_of_distOn_eq_zero` below), and `intDist`
supplies it at those radii at which its integrand is small along the minimising
sequence (`eq_of_intDist_eq_zero` of Milestone 4).  Keeping the criterion
separate is what lets the integral metric use it at **one** radius at a time,
which is all an integral ever gives.

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
theorem SkorokhodSpace.eq_restrictExhaustion_of_forall_exists (t₀ : ι) {u : ℝ} (hu : 0 ≤ u)
    (f g : D(ι, E))
    (hstep : ∀ δ > 0, ∃ l : TimeChange.fixing t₀,
      TimeChange.norm (l : TimeChange ι) < δ ∧
        ∀ s, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
          ((l : TimeChange ι).toOrderIso s))
          ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun s) < δ) :
    (SkorokhodSpace.restrictExhaustion t₀ u f).toFun
      = (SkorokhodSpace.restrictExhaustion t₀ u g).toFun := by
  -- the displacement of a point of the window is small with the norm
  have hsmall : ∀ ρ > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ ≤ η ∧ (Real.exp δ - 1) * (2 * u) < ρ := by
    intro ρ hρ η hη
    have hcont : Tendsto (fun δ : ℝ => (Real.exp δ - 1) * (2 * u)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => (Real.exp δ - 1) * (2 * u)) (𝓝 0)
          (𝓝 ((Real.exp 0 - 1) * (2 * u))) :=
        ((Real.continuous_exp.sub continuous_const).mul continuous_const).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (Real.exp δ - 1) * (2 * u) < ρ := hcont (Iio_mem_nhds hρ)
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ η :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Filter.Eventually.mono (Iio_mem_nhds hη) fun _ hx => hx.le)
    obtain ⟨δ, hδρ, hδη, hδ0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    exact ⟨δ, hδ0, hδη, hδρ⟩
  -- on the window the two truncations agree
  have hwin : ∀ t ∈ exhaustion t₀ u,
      (SkorokhodSpace.restrictExhaustion t₀ u f).toFun t
        = (SkorokhodSpace.restrictExhaustion t₀ u g).toFun t := by
    intro t ht
    refine (SkorokhodSpace.restrictExhaustion t₀ u f).isCadlag.eq_of_forall_exists_dist_le
      (SkorokhodSpace.restrictExhaustion t₀ u g).isCadlag ?_
    intro ρ hρ η hη
    obtain ⟨δ, hδ0, hδη, hδρ⟩ := hsmall ρ hρ η hη
    obtain ⟨l, hlnorm, hldist⟩ := hstep δ hδ0
    have hfix : (l : TimeChange ι).toOrderIso t₀ = t₀ := TimeChange.mem_fixing_iff.1 l.2
    by_cases hcase : t ≤ (l : TimeChange ι).toOrderIso t
    · refine ⟨(l : TimeChange ι).toOrderIso t, hcase, ?_, Or.inl ((hldist t).le.trans hδη)⟩
      exact (TimeChange.dist_le_of_norm_le t₀ hu hfix hlnorm.le ht).trans_lt hδρ
    · have hinv : ((l : TimeChange ι)⁻¹).toOrderIso = (l : TimeChange ι).toOrderIso.symm := rfl
      have hts : t ≤ (l : TimeChange ι).toOrderIso.symm t := by
        have := (OrderIso.lt_iff_lt (l : TimeChange ι).toOrderIso.symm).2 (not_le.1 hcase)
        simpa using this.le
      refine ⟨(l : TimeChange ι).toOrderIso.symm t, hts, ?_, Or.inr ?_⟩
      · have hfix' : ((l : TimeChange ι)⁻¹).toOrderIso t₀ = t₀ := by
          rw [hinv]
          exact (l : TimeChange ι).toOrderIso.symm_apply_eq.2 hfix.symm
        have := TimeChange.dist_le_of_norm_le t₀ hu hfix'
          (le_of_eq_of_le (TimeChange.norm_inv (l : TimeChange ι)) hlnorm.le) ht
        rw [hinv] at this
        exact this.trans_lt hδρ
      · have := hldist ((l : TimeChange ι).toOrderIso.symm t)
        rw [OrderIso.apply_symm_apply] at this
        exact this.le.trans hδη
  funext t
  have hc := hwin (clamp t₀ u t) (clamp_mem_exhaustion t₀ u t)
  simpa [SkorokhodSpace.restrictExhaustion_apply, clamp_idem] using hc

/-- The separation, the last of the metric axioms of `distOn`: two paths at
`distOn`-distance zero have the same truncation to the window.  The infimum is
unwound by `exists_lt_distOn_add`, and the supremum inside it is what turns the
`distOn`-estimate into the pointwise estimate the criterion asks for. -/
theorem SkorokhodSpace.eq_of_distOn_eq_zero (t₀ : ι) {u : ℝ} (hu : 0 ≤ u) (f g : D(ι, E))
    (h : SkorokhodSpace.distOn t₀ u f g = 0) :
    (SkorokhodSpace.restrictExhaustion t₀ u f).toFun
      = (SkorokhodSpace.restrictExhaustion t₀ u g).toFun := by
  refine SkorokhodSpace.eq_restrictExhaustion_of_forall_exists t₀ hu f g fun δ hδ => ?_
  obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_distOn_add t₀ u f g hδ
  rw [h, zero_add] at hl
  refine ⟨l, (le_max_left _ _).trans_lt hl, fun s => ?_⟩
  exact lt_of_le_of_lt ((le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion
    t₀ u f g (l : TimeChange ι)) s).trans (le_max_right _ _)) hl

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
  have hc := congrFun (SkorokhodSpace.eq_of_distOn_eq_zero t₀ (Nat.cast_nonneg m) f g (h m)) t
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

omit [AdditiveDist ι] in
/-- Each window distance is dominated by the metric, at the price of the
geometric weight of its window.  This is the direction a completeness proof reads
first: a Cauchy sequence for the metric is Cauchy for every `distOn t₀ m`, and
`distOn` is what produces the time changes. -/
theorem SkorokhodSpace.min_one_distOn_le (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    min 1 (SkorokhodSpace.distOn t₀ m f g) ≤ 2 ^ m * SkorokhodSpace.totalDist t₀ f g := by
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ)⁻¹ ^ k * min 1 (SkorokhodSpace.distOn t₀ k f g) :=
    fun k => mul_nonneg (by positivity)
      (le_min zero_le_one (SkorokhodSpace.distOn_nonneg t₀ k f g))
  have hle : (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g)
      ≤ SkorokhodSpace.totalDist t₀ f g :=
    (SkorokhodSpace.summable_totalDist t₀ f g).le_tsum m fun j _ => hnn j
  have hid : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
    rw [← mul_pow]; norm_num
  calc min 1 (SkorokhodSpace.distOn t₀ m f g)
      = 2 ^ m * ((2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g)) := by
        rw [← mul_assoc, hid, one_mul]
    _ ≤ 2 ^ m * SkorokhodSpace.totalDist t₀ f g :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- The obstruction in the form the metric consumes it: the value of a path at a
window endpoint is determined by the metric, up to the geometric weight of the
window.  This is `SkorokhodSpace.dist_exhaustionMax_le_distOn` and
`SkorokhodSpace.min_one_distOn_le` composed, and it is one step away from the
continuity of evaluation there. -/
theorem SkorokhodSpace.min_one_dist_exhaustionMax_le (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    min 1 (dist (f.toFun (exhaustionMax t₀ m)) (g.toFun (exhaustionMax t₀ m)))
      ≤ 2 ^ m * SkorokhodSpace.totalDist t₀ f g :=
  le_trans (min_le_min le_rfl (SkorokhodSpace.dist_exhaustionMax_le_distOn t₀ m f g))
    (SkorokhodSpace.min_one_distOn_le t₀ m f g)

omit [AdditiveDist ι] in
/-- The same estimate without the truncation, on the range where the truncation
is inactive.  The hypothesis is not a defect: `distOn` is genuinely unbounded as
the window grows, so no bound of this shape can hold for all pairs at once, and a
completeness proof only ever uses it for pairs already close in the metric. -/
theorem SkorokhodSpace.distOn_le_of_two_pow_mul_lt_one (t₀ : ι) (m : ℕ) (f g : D(ι, E))
    (h : 2 ^ m * SkorokhodSpace.totalDist t₀ f g < 1) :
    SkorokhodSpace.distOn t₀ m f g ≤ 2 ^ m * SkorokhodSpace.totalDist t₀ f g := by
  have hmin := SkorokhodSpace.min_one_distOn_le t₀ m f g
  rcases min_cases 1 (SkorokhodSpace.distOn t₀ m f g) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hmin; linarith
  · rw [he] at hmin; exact hmin

omit [AdditiveDist ι] in
/-- And the converse direction, which a completeness proof reads last: the metric
is recovered from finitely many windows up to a geometric error, so a sequence
that converges in every `distOn t₀ m` converges in the metric.  The tail is
estimated by the truncation alone, which is what the `min 1` in `totalDist` is
for. -/
theorem SkorokhodSpace.totalDist_le_sum_add (t₀ : ι) (M : ℕ) (f g : D(ι, E)) :
    SkorokhodSpace.totalDist t₀ f g
      ≤ (∑ m ∈ Finset.range M, (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g))
        + 2 * (2 : ℝ)⁻¹ ^ M := by
  have hsum := SkorokhodSpace.summable_totalDist t₀ f g
  have hsplit := hsum.sum_add_tsum_nat_add M
  have hgeom : Summable fun i : ℕ => (2 : ℝ)⁻¹ ^ i :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbd : ∀ i : ℕ, (2 : ℝ)⁻¹ ^ (i + M) * min 1 (SkorokhodSpace.distOn t₀ ((i + M : ℕ) : ℝ) f g)
      ≤ (2 : ℝ)⁻¹ ^ M * (2 : ℝ)⁻¹ ^ i := by
    intro i
    have h1 : min 1 (SkorokhodSpace.distOn t₀ ((i + M : ℕ) : ℝ) f g) ≤ 1 := min_le_left _ _
    have h2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (i + M) := by positivity
    calc (2 : ℝ)⁻¹ ^ (i + M) * min 1 (SkorokhodSpace.distOn t₀ ((i + M : ℕ) : ℝ) f g)
        ≤ (2 : ℝ)⁻¹ ^ (i + M) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = (2 : ℝ)⁻¹ ^ M * (2 : ℝ)⁻¹ ^ i := by rw [mul_one, pow_add]; ring
  have htail : ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + M) * min 1 (SkorokhodSpace.distOn t₀ ((i + M : ℕ) : ℝ) f g)
      ≤ 2 * (2 : ℝ)⁻¹ ^ M := by
    calc ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + M) * min 1 (SkorokhodSpace.distOn t₀ ((i + M : ℕ) : ℝ) f g)
        ≤ ∑' i : ℕ, (2 : ℝ)⁻¹ ^ M * (2 : ℝ)⁻¹ ^ i :=
          (hsum.comp_injective (add_left_injective M)).tsum_le_tsum hbd (hgeom.mul_left _)
      _ = (2 : ℝ)⁻¹ ^ M * ∑' i : ℕ, (2 : ℝ)⁻¹ ^ i := hgeom.tsum_mul_left _
      _ = 2 * (2 : ℝ)⁻¹ ^ M := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
          ring
  show ∑' m : ℕ, (2 : ℝ)⁻¹ ^ m * min 1 (SkorokhodSpace.distOn t₀ m f g) ≤ _
  rw [← hsplit]
  exact add_le_add le_rfl htail

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

/-- The topology of the summed metric, named.  Until the twenty-first run of
2026-09-08 the `MetricSpace D(ι, E)` instance *was* `SkorokhodSpace.metricSpace
basePoint`, so the two refutation statements of Milestone 5 could read their
topology off the instance and say `Continuous`.  The instance is now the integral
metric `SkorokhodSpace.metricSpaceInt`, for which the first of those two is
false; so they have to name the topology they are about, and this is the name.
Naming it is what keeps the refutation a refutation instead of turning it, by the
mere move of an instance, into a claim about `intDist`. -/
@[instance_reducible]
noncomputable def SkorokhodSpace.totalTopology (t₀ : ι) : TopologicalSpace D(ι, E) :=
  (SkorokhodSpace.metricSpace (E := E) t₀).toUniformSpace.toTopologicalSpace

variable [BasePoint ι]

/-! ### The metric of Milestone 4 is an integral over the window radius

`SkorokhodSpace.totalDist` below sums `min 1 (distOn t₀ m f g)` over the integer
radii, and the eighteenth run of 2026-09-08 showed that this is not a metric for
`J₁`: `SkorokhodSpace.dist_exhaustionMax_le_distOn` makes every window endpoint a
point of continuity of the evaluation, which the Skorokhod topology does not
have.  The repair is Ethier--Kurtz's: keep `distOn`'s integrand, let the radius
run over `Set.Ioi 0`, and integrate against `exp (-u)`.  The radii at which a
given pair of paths misbehaves are countably many, hence Lebesgue null, and the
integral does not see them.

The infimum over the time change stands **outside** the integral, which is what
makes the integrand measurable at all: for one time change at a time the
supremum over the index is a supremum over the countable set of
`exists_countable_ciSup_eq`, while an infimum over the uncountable family of
time changes inside the integral would be measurable for no stated reason. -/

/-- Ethier--Kurtz's `d(x, y, λ, u)`: the windowed supremum for **one** time
change, before the infimum and before the truncation at `1`.  It is the
integrand of `SkorokhodSpace.intDist` and the inner term of
`SkorokhodSpace.distOn`, which is `distOn_eq_iInf_distWith`. -/
noncomputable def SkorokhodSpace.distWith (t₀ : ι) (u : ℝ) (l : TimeChange ι)
    (f g : D(ι, E)) : ℝ :=
  ⨆ t : ι, dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun (l.toOrderIso t))
    ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t)

omit [AdditiveDist ι] [BasePoint ι] in
@[simp]
theorem SkorokhodSpace.distOn_eq_iInf_distWith (t₀ : ι) (u : ℝ) (f g : D(ι, E)) :
    SkorokhodSpace.distOn t₀ u f g =
      ⨅ l : TimeChange.fixing t₀, max (TimeChange.norm (l : TimeChange ι))
        (SkorokhodSpace.distWith t₀ u (l : TimeChange ι) f g) := rfl

omit [AdditiveDist ι] [BasePoint ι] in
/-- The integrand of `distWith` is right continuous in the index, which is what
`exists_countable_ciSup_eq` consumes.  Both halves are càdlàg --- the left one
because a càdlàg path composed with an order isomorphism is càdlàg
(`IsCadlag.comp_monotone_continuous`, the order isomorphism being monotone and,
in the order topology, continuous). -/
theorem SkorokhodSpace.rightContinuous_dist_restrictExhaustion (t₀ : ι) (u : ℝ)
    (l : TimeChange ι) (f g : D(ι, E)) :
    Function.RightContinuous fun t : ι =>
      dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun (l.toOrderIso t))
        ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun t) := by
  have hcomp : IsCadlag ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun ∘ l.toOrderIso) :=
    (SkorokhodSpace.restrictExhaustion t₀ u f).isCadlag.comp_monotone_continuous
      l.toOrderIso.monotone l.toOrderIso.continuous
  intro a
  exact (hcomp.right_continuous a).dist
    ((SkorokhodSpace.restrictExhaustion t₀ u g).isCadlag.right_continuous a)

omit [AdditiveDist ι] [BasePoint ι] in
/-- The greatest point of the window grows with the radius. -/
theorem monotone_exhaustionMax (t₀ : ι) : Monotone (exhaustionMax t₀) := fun _ _ h =>
  (isGreatest_exhaustionMax t₀ _).2
    (exhaustion_subset_of_le t₀ h (isGreatest_exhaustionMax t₀ _).1)

omit [AdditiveDist ι] [BasePoint ι] in
/-- And the least point falls. -/
theorem antitone_exhaustionMin (t₀ : ι) : Antitone (exhaustionMin t₀) := fun _ _ h =>
  (isLeast_exhaustionMin t₀ _).2 (exhaustion_subset_of_le t₀ h (isLeast_exhaustionMin t₀ _).1)

omit [AdditiveDist ι] [BasePoint ι] in
/-- The clamp is measurable in the radius, for each fixed point of the index.
Monotonicity in the radius is all it is: `exhaustionMax` rises, `exhaustionMin`
falls, and both are measurable because a monotone map into a second countable
linear order is. -/
theorem measurable_clamp [MeasurableSpace ι] [BorelSpace ι] (t₀ : ι) (s : ι) :
    Measurable fun u : ℝ => clamp t₀ u s :=
  (measurable_const.max (antitone_exhaustionMin t₀).measurable).min
    (monotone_exhaustionMax t₀).measurable

omit [BasePoint ι] in
/-- **The integrand of the metric is measurable in the window radius.**  This is
the one obligation the integral shape of Milestone 4 adds, and it is discharged
here: the supremum over the index is, by `exists_countable_ciSup_eq`, a
supremum over a *fixed* countable set, so `Measurable.iSup` applies, and each
member of that family is a distance between two càdlàg paths read at a clamp
that is measurable in the radius.

The statement is about a function `ℝ → ℝ`, so the Borel structures of `ι` and of
`E` are hypotheses of the *proof* and not of the statement: they are introduced
here rather than assumed, and only `SecondCountableTopology E` remains, which is
what `Measurable.dist` needs and what no choice of σ-algebra supplies.  That is
what keeps the metric instance of Milestone 4 free of measure theory. -/
theorem SkorokhodSpace.measurable_distWith [SecondCountableTopology E]
    (t₀ : ι) (l : TimeChange ι) (f g : D(ι, E)) :
    Measurable fun u : ℝ => SkorokhodSpace.distWith t₀ u l f g := by
  let mι : MeasurableSpace ι := borel ι
  have : BorelSpace ι := ⟨rfl⟩
  let mE : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : Nonempty ι := ⟨t₀⟩
  obtain ⟨C, hCc, hCne, hC⟩ := exists_countable_ciSup_eq (ι := ι)
  have : Countable C := hCc.to_subtype
  have hrw : ∀ u : ℝ, SkorokhodSpace.distWith t₀ u l f g
      = ⨆ t : C, dist (f.toFun (clamp t₀ u (l.toOrderIso (t : ι))))
          (g.toFun (clamp t₀ u (t : ι))) := fun u =>
    hC _ (SkorokhodSpace.rightContinuous_dist_restrictExhaustion t₀ u l f g)
      (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g l)
  simp only [hrw]
  refine Measurable.iSup fun t => ?_
  exact (f.isCadlag.measurable.comp (measurable_clamp t₀ (l.toOrderIso (t : ι)))).dist
    (g.isCadlag.measurable.comp (measurable_clamp t₀ (t : ι)))

/-- The integral half of the metric of Milestone 4, for **one** time change: the
truncated windowed supremum `min 1 (distWith t₀ u l f g)` integrated over the
window radius against `exp (-u)`.  Splitting it off from `intDist` is what makes
the three metric axioms readable: each of them is one statement about `intWith`
and one about `TimeChange.norm`, joined by `max`. -/
noncomputable def SkorokhodSpace.intWith (t₀ : ι) (l : TimeChange ι) (f g : D(ι, E)) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u l f g)

/-- **The metric of Milestone 4.**  The infimum is over the time changes fixing
the base point, the first term of the `max` is the global logarithmic norm, and
the second is `intWith`, the integral over the window radius of the truncated
windowed supremum.  This is Ethier--Kurtz's `d`, and it replaces
`SkorokhodSpace.totalDist`, which is the same quantity summed over the integer
radii and, by `dist_exhaustionMax_le_distOn`, not a metric for `J₁`. -/
noncomputable def SkorokhodSpace.intDist (t₀ : ι) (f g : D(ι, E)) : ℝ :=
  ⨅ l : TimeChange.fixing t₀, max (TimeChange.norm (l : TimeChange ι))
    (SkorokhodSpace.intWith t₀ (l : TimeChange ι) f g)

omit [BasePoint ι] in
/-- The integral defining `intWith` is an integral of an integrable function:
the integrand is measurable by `measurable_distWith` and dominated by
`exp (-u)`, which is integrable on `Set.Ioi 0`.  Without this the integral
would be the junk value `0` and `intDist` would collapse to
`⨅ l, TimeChange.norm l = 0`. -/
theorem SkorokhodSpace.integrableOn_intDist [SecondCountableTopology E]
    (t₀ : ι) (l : TimeChange ι) (f g : D(ι, E)) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u l f g))
      (Set.Ioi (0 : ℝ)) := by
  refine MeasureTheory.Integrable.mono' (integrableOn_exp_neg_Ioi 0)
    (((Real.measurable_exp.comp measurable_neg).mul
      (measurable_const.min
        (SkorokhodSpace.measurable_distWith t₀ l f g))).aestronglyMeasurable.restrict) ?_
  filter_upwards with u
  have h0 : (0 : ℝ) ≤ min 1 (SkorokhodSpace.distWith t₀ u l f g) := by
    refine le_min zero_le_one (le_ciSup_of_le
      (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g l) t₀ dist_nonneg)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u l f g)
      ≤ Real.exp (-u) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
    _ = Real.exp (-u) := mul_one _

/-! ### The metric axioms of `intDist`

Each of the three axioms splits along the `max` into a statement about
`TimeChange.norm` --- which is the one of `TimeChange`, proved in Milestone 3 ---
and a statement about `intWith`, which is the corresponding statement about
`distWith` held at a fixed radius and then integrated.  The radius is a
spectator throughout: `distWith_self`, `distWith_inv` and `distWith_triangle`
are the three statements about the windowed supremum, and `intWith_self`,
`intWith_inv` and `intWith_triangle` carry them under the integral.

The triangle inequality is the only one that spends `integrableOn_intDist`, and
it spends it twice, for `MeasureTheory.integral_add` and for
`MeasureTheory.integral_mono`; without integrability the integral is the junk
value `0`, for which the inequality is false in the direction that matters --- a
non-integrable *left* summand would read as `0` and let the right hand side be
anything.  That is why `[SecondCountableTopology E]` appears on the triangle
inequality and on nothing else here. -/

omit [BasePoint ι] in
/-- The windowed supremum is nonnegative: it is a supremum over a nonempty
family of distances, and `bddAbove_range_dist_restrictExhaustion` is what makes
it the supremum rather than the junk value. -/
theorem SkorokhodSpace.distWith_nonneg (t₀ : ι) (u : ℝ) (l : TimeChange ι) (f g : D(ι, E)) :
    0 ≤ SkorokhodSpace.distWith t₀ u l f g :=
  le_ciSup_of_le (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g l) t₀
    dist_nonneg

omit [AdditiveDist ι] [BasePoint ι] in
/-- The identity time change leaves nothing to measure. -/
theorem SkorokhodSpace.distWith_self (t₀ : ι) (u : ℝ) (f : D(ι, E)) :
    SkorokhodSpace.distWith t₀ u 1 f f = 0 := by
  have : Nonempty ι := ⟨t₀⟩
  simp [SkorokhodSpace.distWith, TimeChange.one_toOrderIso_apply]

/-- A supremum is unchanged when its index is permuted, and this is the shape in
which `distWith_inv` needs it: the two families are indexed by the same type and
agree after the substitution `t = e s`. -/
theorem SkorokhodSpace.ciSup_reindex {α : Type*} {h₁ h₂ : α → ℝ} (e : α → α)
    (he : Function.Surjective e) (hpt : ∀ s, h₁ (e s) = h₂ s) : ⨆ t, h₁ t = ⨆ s, h₂ s := by
  refine congrArg sSup ?_
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := he t
    exact ⟨s, (hpt s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨e s, hpt s⟩

omit [AdditiveDist ι] [BasePoint ι] in
/-- Symmetry at a fixed radius: reading the pair the other way round and
inverting the time change gives the same windowed supremum.  The reindexing is
along `l` itself, which is a bijection of the index. -/
theorem SkorokhodSpace.distWith_inv (t₀ : ι) (u : ℝ) (l : TimeChange ι) (f g : D(ι, E)) :
    SkorokhodSpace.distWith t₀ u l⁻¹ g f = SkorokhodSpace.distWith t₀ u l f g := by
  refine SkorokhodSpace.ciSup_reindex (⇑l.toOrderIso) l.toOrderIso.surjective fun s => ?_
  show dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun
      (l.toOrderIso.symm (l.toOrderIso s)))
      ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun (l.toOrderIso s)) = _
  rw [OrderIso.symm_apply_apply, dist_comm]

omit [BasePoint ι] in
/-- The triangle inequality at a fixed radius, with `l * l'` as the composite
time change.  This is the step that needs the anchors to form a **subgroup**,
and the middle path is read at `l' t`, which is why the supremum runs over all
of the index and not over the window. -/
theorem SkorokhodSpace.distWith_triangle (t₀ : ι) (u : ℝ) (l l' : TimeChange ι)
    (f g h : D(ι, E)) :
    SkorokhodSpace.distWith t₀ u (l * l') f h
      ≤ SkorokhodSpace.distWith t₀ u l f g + SkorokhodSpace.distWith t₀ u l' g h := by
  have : Nonempty ι := ⟨t₀⟩
  refine ciSup_le fun t => ?_
  simp only [TimeChange.mul_toOrderIso_apply]
  calc dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
          (l.toOrderIso (l'.toOrderIso t)))
        ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t)
      ≤ dist ((SkorokhodSpace.restrictExhaustion t₀ u f).toFun
            (l.toOrderIso (l'.toOrderIso t)))
          ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun (l'.toOrderIso t))
        + dist ((SkorokhodSpace.restrictExhaustion t₀ u g).toFun (l'.toOrderIso t))
          ((SkorokhodSpace.restrictExhaustion t₀ u h).toFun t) := dist_triangle _ _ _
    _ ≤ _ := add_le_add
        (le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g l)
          (l'.toOrderIso t))
        (le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u g h l') t)

omit [BasePoint ι] in
/-- The integral of a nonnegative integrand. -/
theorem SkorokhodSpace.intWith_nonneg (t₀ : ι) (l : TimeChange ι) (f g : D(ι, E)) :
    0 ≤ SkorokhodSpace.intWith t₀ l f g :=
  MeasureTheory.integral_nonneg fun u =>
    mul_nonneg (Real.exp_pos _).le
      (le_min zero_le_one (SkorokhodSpace.distWith_nonneg t₀ u l f g))

omit [AdditiveDist ι] [BasePoint ι] in
/-- `distWith_self` under the integral: the integrand vanishes identically, so
no integrability is spent here. -/
theorem SkorokhodSpace.intWith_self (t₀ : ι) (f : D(ι, E)) :
    SkorokhodSpace.intWith t₀ 1 f f = 0 := by
  have h : ∀ u : ℝ, Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u 1 f f) = 0 := fun u => by
    rw [SkorokhodSpace.distWith_self, min_eq_right zero_le_one, mul_zero]
  simp [SkorokhodSpace.intWith, h]

omit [AdditiveDist ι] [BasePoint ι] in
/-- `distWith_inv` under the integral, radius by radius. -/
theorem SkorokhodSpace.intWith_inv (t₀ : ι) (l : TimeChange ι) (f g : D(ι, E)) :
    SkorokhodSpace.intWith t₀ l⁻¹ g f = SkorokhodSpace.intWith t₀ l f g := by
  simp only [SkorokhodSpace.intWith, SkorokhodSpace.distWith_inv]

omit [BasePoint ι] in
/-- `distWith_triangle` under the integral.  Two things happen at once: `min 1 ·`
is subadditive on the nonnegative reals, which is the same computation as in
`totalDist_triangle`, and the integral is additive, which is
`integrableOn_intDist` twice over. -/
theorem SkorokhodSpace.intWith_triangle [SecondCountableTopology E] (t₀ : ι)
    (l l' : TimeChange ι) (f g h : D(ι, E)) :
    SkorokhodSpace.intWith t₀ (l * l') f h
      ≤ SkorokhodSpace.intWith t₀ l f g + SkorokhodSpace.intWith t₀ l' g h := by
  have hsub : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b + c →
      min 1 a ≤ min 1 b + min 1 c := by
    intro a b c ha hb hc habc
    simp only [min_def]
    split_ifs <;> linarith
  rw [SkorokhodSpace.intWith, SkorokhodSpace.intWith, SkorokhodSpace.intWith,
    ← MeasureTheory.integral_add (SkorokhodSpace.integrableOn_intDist t₀ l f g)
      (SkorokhodSpace.integrableOn_intDist t₀ l' g h)]
  refine MeasureTheory.integral_mono (SkorokhodSpace.integrableOn_intDist t₀ (l * l') f h)
    ((SkorokhodSpace.integrableOn_intDist t₀ l f g).add
      (SkorokhodSpace.integrableOn_intDist t₀ l' g h)) fun u => ?_
  have key : min 1 (SkorokhodSpace.distWith t₀ u (l * l') f h)
      ≤ min 1 (SkorokhodSpace.distWith t₀ u l f g)
        + min 1 (SkorokhodSpace.distWith t₀ u l' g h) :=
    hsub _ _ _ (SkorokhodSpace.distWith_nonneg t₀ u (l * l') f h)
      (SkorokhodSpace.distWith_nonneg t₀ u l f g)
      (SkorokhodSpace.distWith_nonneg t₀ u l' g h)
      (SkorokhodSpace.distWith_triangle t₀ u l l' f g h)
  calc Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u (l * l') f h)
      ≤ Real.exp (-u) * (min 1 (SkorokhodSpace.distWith t₀ u l f g)
          + min 1 (SkorokhodSpace.distWith t₀ u l' g h)) :=
        mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = _ := by ring

omit [AdditiveDist ι] [BasePoint ι] in
/-- The infimum defining `intDist` is over a set bounded below by `0`. -/
theorem SkorokhodSpace.bddBelow_range_intDist (t₀ : ι) (f g : D(ι, E)) :
    BddBelow (Set.range fun l : TimeChange.fixing t₀ =>
      max (TimeChange.norm (l : TimeChange ι))
        (SkorokhodSpace.intWith t₀ (l : TimeChange ι) f g)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] [BasePoint ι] in
theorem SkorokhodSpace.intDist_nonneg (t₀ : ι) (f g : D(ι, E)) :
    0 ≤ SkorokhodSpace.intDist t₀ f g :=
  le_ciInf fun _ => le_max_of_le_left (TimeChange.norm_nonneg _)

omit [AdditiveDist ι] [BasePoint ι] in
/-- **The first axiom.**  The identity is an admissible time change, its norm is
`0`, and `intWith_self` kills the integral. -/
theorem SkorokhodSpace.intDist_self (t₀ : ι) (f : D(ι, E)) :
    SkorokhodSpace.intDist t₀ f f = 0 := by
  refine le_antisymm ?_ (SkorokhodSpace.intDist_nonneg t₀ f f)
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_intDist t₀ f f) 1).trans ?_
  simp [OneMemClass.coe_one, TimeChange.norm_one, SkorokhodSpace.intWith_self]

omit [AdditiveDist ι] [BasePoint ι] in
/-- **The second axiom.**  `λ ↦ λ⁻¹` is a bijection of the anchored subgroup,
`TimeChange.norm_inv` leaves the first half of the `max` unchanged and
`intWith_inv` the second, so the two infima are over the same set. -/
theorem SkorokhodSpace.intDist_comm (t₀ : ι) (f g : D(ι, E)) :
    SkorokhodSpace.intDist t₀ f g = SkorokhodSpace.intDist t₀ g f := by
  have main : ∀ f g : D(ι, E),
      SkorokhodSpace.intDist t₀ g f ≤ SkorokhodSpace.intDist t₀ f g := by
    intro f g
    refine le_ciInf fun l => ?_
    refine (ciInf_le (SkorokhodSpace.bddBelow_range_intDist t₀ g f) l⁻¹).trans (le_of_eq ?_)
    rw [InvMemClass.coe_inv, TimeChange.norm_inv, SkorokhodSpace.intWith_inv]
  exact le_antisymm (main g f) (main f g)

omit [AdditiveDist ι] [BasePoint ι] in
/-- The infimum in `intDist` is approached; it need not be attained, so the
triangle inequality argues with an `ε`. -/
theorem SkorokhodSpace.exists_lt_intDist_add (t₀ : ι) (f g : D(ι, E)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ l : TimeChange.fixing t₀,
      max (TimeChange.norm (l : TimeChange ι))
        (SkorokhodSpace.intWith t₀ (l : TimeChange ι) f g)
        < SkorokhodSpace.intDist t₀ f g + δ :=
  exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hδ)

omit [BasePoint ι] in
/-- **The third axiom.**  The witness for the composite pair is `λ * λ'`, which
is admissible because the anchors are a subgroup; `TimeChange.norm_mul_le`
carries the first half of the `max` and `intWith_triangle` the second. -/
theorem SkorokhodSpace.intDist_triangle [SecondCountableTopology E] (t₀ : ι)
    (f g h : D(ι, E)) :
    SkorokhodSpace.intDist t₀ f h
      ≤ SkorokhodSpace.intDist t₀ f g + SkorokhodSpace.intDist t₀ g h := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_intDist_add t₀ f g (half_pos hε)
  obtain ⟨l', hl'⟩ := SkorokhodSpace.exists_lt_intDist_add t₀ g h (half_pos hε)
  have hterm :
      max (TimeChange.norm ((l * l' : TimeChange.fixing t₀) : TimeChange ι))
        (SkorokhodSpace.intWith t₀ ((l * l' : TimeChange.fixing t₀) : TimeChange ι) f h)
      ≤ (max (TimeChange.norm (l : TimeChange ι))
            (SkorokhodSpace.intWith t₀ (l : TimeChange ι) f g))
        + max (TimeChange.norm (l' : TimeChange ι))
            (SkorokhodSpace.intWith t₀ (l' : TimeChange ι) g h) := by
    rw [MulMemClass.coe_mul]
    refine max_le ?_ ?_
    · exact (TimeChange.norm_mul_le _ _).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact (SkorokhodSpace.intWith_triangle t₀ _ _ f g h).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _))
  refine (ciInf_le (SkorokhodSpace.bddBelow_range_intDist t₀ f h) (l * l')).trans
    (hterm.trans ?_)
  linarith

omit [BasePoint ι] in
/-- **The fourth axiom, and the only one that is not the corresponding statement
about `distWith` integrated.**  The infimum being `0` does not produce a single
time change that works at every radius; it produces a *sequence* of them, and
the radius at which a given member of that sequence is good is not known.

The argument is therefore the one an integral always forces.  Choose `l n` with
`‖l n‖ < 2⁻ⁿ` and `intWith t₀ (l n) f g < 2⁻ⁿ`.  The sum of the integrands over
`n` has finite integral --- `lintegral_tsum` and a geometric series --- hence is
finite at almost every radius, so at almost every radius its terms tend to `0`,
so at almost every radius `distWith t₀ u (l n) f g → 0` and
`eq_restrictExhaustion_of_forall_exists` applies **there**.  A set of full
measure in `Set.Ioi 0` is unbounded, and every point of the index lies in the
window of a large enough radius, so the two paths agree everywhere.

This is where the difference to `totalDist` is paid for and where it pays: the
summed metric had `eq_of_forall_distOn_eq_zero`, one radius at a time and every
radius available, while the integral gives no single radius at all and has to
take what is left after a null set is removed.  It is the same trade that makes
the integral metric a `J₁` metric and the sum not one. -/
theorem SkorokhodSpace.eq_of_intDist_eq_zero [SecondCountableTopology E] (t₀ : ι)
    (f g : D(ι, E)) (h : SkorokhodSpace.intDist t₀ f g = 0) : f = g := by
  -- the minimising sequence, with a summable bound on both halves of the `max`
  have hchoice : ∀ n : ℕ, ∃ l : TimeChange.fixing t₀,
      TimeChange.norm (l : TimeChange ι) < (2 : ℝ)⁻¹ ^ n ∧
        SkorokhodSpace.intWith t₀ (l : TimeChange ι) f g < (2 : ℝ)⁻¹ ^ n := by
    intro n
    obtain ⟨l, hl⟩ := SkorokhodSpace.exists_lt_intDist_add t₀ f g
      (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity)
    rw [h, zero_add] at hl
    exact ⟨l, (le_max_left _ _).trans_lt hl, (le_max_right _ _).trans_lt hl⟩
  choose l hlnorm hlint using hchoice
  have hnn : ∀ (n : ℕ) (u : ℝ), 0 ≤ Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g) := fun n u =>
    mul_nonneg (Real.exp_pos _).le
      (le_min zero_le_one (SkorokhodSpace.distWith_nonneg t₀ u (l n : TimeChange ι) f g))
  have hmeas : ∀ n : ℕ, Measurable fun u : ℝ => Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g) := fun n =>
    (Real.measurable_exp.comp measurable_neg).mul
      (measurable_const.min (SkorokhodSpace.measurable_distWith t₀ (l n : TimeChange ι) f g))
  -- the series of the integrands has finite integral
  have hfin : ∫⁻ u in Set.Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g)) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun n => ((hmeas n).ennreal_ofReal).aemeasurable]
    have hterm : ∀ n : ℕ, ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g))
        ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) := by
      intro n
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (SkorokhodSpace.integrableOn_intDist t₀ (l n : TimeChange ι) f g)
        (Filter.Eventually.of_forall (hnn n))]
      exact ENNReal.ofReal_le_ofReal (hlint n).le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  -- hence it is finite at almost every radius
  have hmtsum : Measurable fun u : ℝ => ∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g)) := by
    simp only [ENNReal.tsum_eq_iSup_sum]
    exact Measurable.iSup fun s =>
      Finset.measurable_sum s fun n _ => (hmeas n).ennreal_ofReal
  have hae : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g))) ≠ ⊤ :=
    (MeasureTheory.ae_lt_top hmtsum hfin).mono fun _ hu => hu.ne
  -- and at every such radius the separation criterion applies
  have hcrit : ∀ u : ℝ, 0 ≤ u →
      (∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g))) ≠ ⊤ →
      (SkorokhodSpace.restrictExhaustion t₀ u f).toFun
        = (SkorokhodSpace.restrictExhaustion t₀ u g).toFun := by
    intro u hu hufin
    refine SkorokhodSpace.eq_restrictExhaustion_of_forall_exists t₀ hu f g fun δ hδ => ?_
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g))) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hufin
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-u) * min δ 1) :=
      ENNReal.ofReal_pos.2 (by positivity)
    have h1 : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g))
        < ENNReal.ofReal (Real.exp (-u) * min δ 1) := htend.eventually (gt_mem_nhds hpos)
    have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ)⁻¹ ^ n < δ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds hδ)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have hlt : Real.exp (-u) * min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g)
        < Real.exp (-u) * min δ 1 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn1
    have hmin : min 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g) < min δ 1 :=
      lt_of_mul_lt_mul_left hlt (Real.exp_pos _).le
    have hdist : SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g < δ := by
      rcases min_cases 1 (SkorokhodSpace.distWith t₀ u (l n : TimeChange ι) f g) with
        ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hmin
        exact absurd hmin (not_lt.2 (min_le_right _ _))
      · rw [he] at hmin
        exact hmin.trans_le (min_le_left _ _)
    exact ⟨l n, (hlnorm n).trans hn2, fun s =>
      lt_of_le_of_lt (le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g
        (l n : TimeChange ι)) s) hdist⟩
  -- a set of full measure in `Set.Ioi 0` reaches beyond every point of the index
  have hfun : f.toFun = g.toFun := by
    funext t
    have hr0 : (0 : ℝ) ≤ max (dist t₀ t) 0 := le_max_right _ _
    have hmono : MeasureTheory.volume.restrict (Set.Ioi (max (dist t₀ t) 0))
        ≤ MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi hr0) le_rfl
    have hne : (MeasureTheory.ae
        (MeasureTheory.volume.restrict (Set.Ioi (max (dist t₀ t) 0)))).NeBot := by
      refine MeasureTheory.ae_neBot.2 ?_
      simp [MeasureTheory.Measure.restrict_eq_zero, Real.volume_Ioi]
    obtain ⟨u, hufin, hur⟩ := ((hae.filter_mono (MeasureTheory.ae_mono hmono)).and
      (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)).exists
    have hru : max (dist t₀ t) 0 < u := hur
    have hu0 : (0 : ℝ) ≤ u := hr0.trans hru.le
    have ht : t ∈ exhaustion t₀ u := by
      have hdt : dist t₀ t ≤ u := (le_max_left _ _).trans hru.le
      simpa [exhaustion, Metric.mem_closedBall, dist_comm t t₀, max_eq_left hu0] using hdt
    have hc := congrFun (hcrit u hu0 hufin) t
    rwa [SkorokhodSpace.restrictExhaustion_eq_self ht,
      SkorokhodSpace.restrictExhaustion_eq_self ht] at hc
  obtain ⟨f', hf'⟩ := f
  obtain ⟨g', hg'⟩ := g
  have hfg : f' = g' := hfun
  subst hfg
  rfl

/-- **The metric space of Milestone 4, at a base point, for the integral
metric.**  All four axioms are proved above, so this is a `MetricSpace` and not a
claim, and since the twenty-first run of 2026-09-08 it is also *the* instance:
`SkorokhodSpace.instMetricSpace` is this at `basePoint`.

The move was not a rename, and what it cost is the two declarations of Milestone 5
below.  `continuous_eval_exhaustionMax` and `exists_jump_continuousAt_eval` used
to read their topology off the instance and are theorems about the **summed**
metric, false for this one; they now name their topology,
`SkorokhodSpace.totalTopology`, so that moving the instance does not silently
turn the refutation of `totalDist` into a claim about `intDist`.

`[SecondCountableTopology E]` is the price of the integral, and it is charged
exactly once: the triangle inequality and the separation both read
`integrableOn_intDist`, whose integrand is measurable only because
`Measurable.dist` is available.  Nothing else in the file needs it. -/
@[instance_reducible]
noncomputable def SkorokhodSpace.metricSpaceInt [SecondCountableTopology E] (t₀ : ι) :
    MetricSpace D(ι, E) where
  dist f g := SkorokhodSpace.intDist t₀ f g
  dist_self := SkorokhodSpace.intDist_self t₀
  dist_comm := SkorokhodSpace.intDist_comm t₀
  dist_triangle := SkorokhodSpace.intDist_triangle t₀
  eq_of_dist_eq_zero h := SkorokhodSpace.eq_of_intDist_eq_zero t₀ _ _ h

/-- The parameterless instance, and since the twenty-first run of 2026-09-08 it is
the **integral** metric at the distinguished point of the index.  What was missing
here was never an axiom --- all four of `metricSpaceInt` are proved above --- but
the base point, and `BasePoint` is where it comes from.

The alternative, `[Nonempty ι]` with `Classical.arbitrary ι`, was rejected: it
produces a point about which nothing is provable, so `dist` on `D(ℝ, E)` could
not be identified with `intDist 0`, and every acceptance example of the following
milestones names its base point.  See the class for the argument.

Whether two base points give the same topology is still not claimed, and it is
deliberately not stated as a `sorry` either: the windows are cofinal in each
other (`exhaustion_subset_exhaustion` of Milestone 1), but the subgroups
`TimeChange.fixing t₀` are not conjugate by anything of small norm --- the
translation that carries `t₁` back to `t₀` has norm `0` and yet displaces the
paths --- so the statement is open in both directions and would be a claim, not
a commitment.  Everything below that mentions the topology of `D(ι, E)`
therefore reads its base point from the instance, and not from a parameter.

`[SecondCountableTopology E]` rides along, and it is the whole price of the
integral form: it is the hypothesis of `Measurable.dist`, through
`integrableOn_intDist`, and nothing else in the file asks for it.  It is carried
on the declaration rather than as a section variable, so that Milestone 6 and
Milestone 7 draw it from their `[PolishSpace E]`, which extends it. -/
noncomputable instance SkorokhodSpace.instMetricSpace [SecondCountableTopology E] :
    MetricSpace D(ι, E) :=
  SkorokhodSpace.metricSpaceInt (basePoint : ι)

/-- The metric is `SkorokhodSpace.intDist` at the base point, by definition.  This
is the lemma that `Classical.arbitrary` could not have: it is what lets an
acceptance example on `D(ℝ, E)` compute with `intDist 0`. -/
@[simp]
theorem SkorokhodSpace.dist_eq [SecondCountableTopology E] (f g : D(ι, E)) :
    dist f g = SkorokhodSpace.intDist (basePoint : ι) f g := rfl

/-! ## Milestone 5: completeness, separability, Polishness

**The three commitments of this section --- `CompleteSpace`, `SeparableSpace` and
`PolishSpace` for `D(ι, E)` --- were withdrawn on 2026-09-08 and are back, and
the two events are one event: they were false for the summed metric, and the
instance is now the integral one.**  They stand below as statements whose proofs
are the work.  What stands beside them is the refutation of the summed metric,
proved rather than asserted, and it is what forced the change; it is stated for
`SkorokhodSpace.totalTopology` and says nothing about the instance.

`SkorokhodSpace.dist_exhaustionMax_le_distOn` shows that `distOn t₀ m` sees the
values of the two paths at `exhaustionMax t₀ m` undamped by any time change, and
`SkorokhodSpace.continuous_eval_exhaustionMax` turns that into the continuity of
evaluation at that point.  For `ι = ℝ` and `t₀ = 0` the window endpoints are the
integers, so convergence in the metric of Milestone 4 forces pointwise
convergence at every integer time, which the Skorokhod topology does not.
`SkorokhodSpace.exists_jump_continuousAt_eval` exhibits a path that jumps at
`1` and at which evaluation at `1` is nevertheless continuous.

Completeness fails with it, and the witness is the classical one: with
`x n := fun t => if t < 1 + 1/(n+1) then 1 else 0` in `D(ℝ, ℝ)`, the sequence is
Cauchy --- a piecewise linear time change fixing `0`, the identity outside
`[1/2, 2]`, carrying `1 + 1/(k+1)` to `1 + 1/(n+1)`, has norm tending to `0` and
makes every windowed supremum vanish --- while no `w ∈ D(ℝ, ℝ)` can be its
limit: `dist (x n 1) (w 1) ≤ distOn 0 1 (x n) w` forces `w 1 = 1`, so the jump of
`w` sits strictly right of `1`, while the time changes of the second window would
have to carry it to `1 + 1/(n+1) → 1` with norms tending to `0`.

The repair was not a proof but a definition, and it is Milestone 4's: the metric
integrates over the window radius, `∫ u in Ioi 0, exp (-u) * min 1 (…)`, instead
of summing over integer radii.  The set of radii at which a given pair of paths
jumps is countable, hence Lebesgue null, and the integral does not see it; that
is exactly why Ethier--Kurtz write an integral and Billingsley a ramp function.
`SkorokhodSpace.distOn` itself survived the repair unchanged apart from the
radius becoming real --- it is Ethier--Kurtz's `d(x, y, λ, u)` --- and so did
everything proved about it. -/

omit [BasePoint ι] in
/-- **For the summed metric, evaluation at a window endpoint is continuous, jump
or no jump.**  This is `SkorokhodSpace.min_one_dist_exhaustionMax_le` read as a
modulus of continuity: `2 ^ m * totalDist t₀ f g < 1` already forces
`dist (f b) (g b) ≤ 2 ^ m * totalDist t₀ f g`.

The topology is named --- `SkorokhodSpace.totalTopology t₀`, the topology of
`SkorokhodSpace.metricSpace t₀` --- and that is the point of the statement, not a
formality.  The `MetricSpace D(ι, E)` instance is the integral metric of
Milestone 4, for which this is false; stated against the instance, the theorem
would assert of `intDist` exactly what disqualified `totalDist`.

For the Skorokhod topology the corresponding statement is an equivalence ---
evaluation at `t` is continuous at `f` exactly when `Function.leftLim f t = f t`
--- and that equivalence stood here as a `sorry` until 2026-09-08.  It is false
for the summed metric, and `SkorokhodSpace.exists_jump_continuousAt_eval` is the
counterexample. -/
theorem SkorokhodSpace.continuous_eval_exhaustionMax (t₀ : ι) (m : ℕ) :
    Continuous[SkorokhodSpace.totalTopology (E := E) t₀, inferInstance]
      fun f : D(ι, E) => f.toFun (exhaustionMax t₀ m) := by
  let _ : MetricSpace D(ι, E) := SkorokhodSpace.metricSpace t₀
  show Continuous fun f : D(ι, E) => f.toFun (exhaustionMax t₀ m)
  rw [Metric.continuous_iff]
  intro f ε hε
  refine ⟨min ε 1 / 2 ^ m, by positivity, fun g hg => ?_⟩
  have hkey := SkorokhodSpace.min_one_dist_exhaustionMax_le t₀ m g f
  have hdist : SkorokhodSpace.totalDist t₀ g f = dist g f := rfl
  rw [hdist] at hkey
  have hlt : 2 ^ m * dist g f < min ε 1 := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have := mul_lt_mul_of_pos_left hg h2
    rwa [mul_div_cancel₀ _ (ne_of_gt h2)] at this
  have hmin := lt_of_le_of_lt hkey hlt
  rcases min_cases 1 (dist (g.toFun (exhaustionMax t₀ m))
      (f.toFun (exhaustionMax t₀ m))) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hmin
    exact absurd (hmin.trans_le (min_le_right ε 1)) (lt_irrefl 1)
  · rw [he] at hmin
    exact hmin.trans_le (min_le_left _ _)

/-- The greatest point of the window `exhaustion 0 m` of `ℝ` is `m`.  Needed to
read the counterexample below off `continuous_eval_exhaustionMax`, whose window
endpoint is opaque in general and is an integer here. -/
theorem exhaustionMax_real (u : ℝ) : exhaustionMax (0 : ℝ) u = max u 0 := by
  refine IsGreatest.unique (isGreatest_exhaustionMax (0 : ℝ) u) ?_
  have hset : exhaustion (0 : ℝ) u = Set.Icc (-max u 0) (max u 0) := by
    simp [exhaustion, Real.closedBall_eq_Icc]
  rw [hset]
  exact isGreatest_Icc (by linarith [le_max_right u (0 : ℝ)])

/-- The unit step at `1`, the simplest path of `D(ℝ, ℝ)` with a jump. -/
noncomputable def SkorokhodSpace.step : D(ℝ, ℝ) where
  toFun t := if (1 : ℝ) ≤ t then 1 else 0
  isCadlag := by
    constructor
    · intro a
      show Filter.Tendsto (fun t => if (1 : ℝ) ≤ t then (1 : ℝ) else 0) (𝓝[Set.Ioi a] a)
        (𝓝 (if (1 : ℝ) ≤ a then (1 : ℝ) else 0))
      rcases lt_or_ge a 1 with ha | ha
      · rw [if_neg (not_le.2 ha)]
        refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds ha)] with t ht
        rw [if_neg (not_le.2 ht)]
      · have ha' : (1 : ℝ) ≤ a := ha
        rw [if_pos ha']
        refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_Ioi] at ht
        rw [if_pos (ha'.trans ht.le)]
    · intro x
      rcases lt_or_ge 1 x with hx | hx
      · refine ⟨1, Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))⟩
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Ioi_mem_nhds hx)] with t ht
        rw [if_pos (le_of_lt ht)]
      · have hx' : x ≤ 1 := hx
        refine ⟨0, Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))⟩
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_Iio] at ht
        rw [if_neg (not_le.2 (ht.trans_le hx'))]

theorem SkorokhodSpace.step_apply (t : ℝ) :
    SkorokhodSpace.step.toFun t = if (1 : ℝ) ≤ t then 1 else 0 := rfl

theorem SkorokhodSpace.leftLim_step : Function.leftLim SkorokhodSpace.step.toFun 1 = 0 := by
  refine leftLim_eq_of_tendsto ?_
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_Iio] at ht
  rw [SkorokhodSpace.step_apply, if_neg (not_le.2 ht)]

/-- **The refutation.**  `SkorokhodSpace.step` jumps at `1`, and for the summed
metric of Milestone 4 evaluation at `1` is continuous at it --- because `1` is the
greatest point of the window `exhaustion 0 1` of `ℝ`, and
`SkorokhodSpace.continuous_eval_exhaustionMax` makes evaluation there continuous
everywhere.  The equivalence that Milestone 6 used to claim,
`ContinuousAt (· t) f ↔ Function.leftLim f t = f t`, therefore fails in its
forward direction, and it fails for the same reason completeness does.

The topology is `SkorokhodSpace.totalTopology (0 : ℝ)` and is named for the same
reason as in the previous declaration: this is a statement about the metric that
was *replaced*, and it is the reason it was replaced. -/
theorem SkorokhodSpace.exists_jump_continuousAt_eval :
    ∃ f : D(ℝ, ℝ), Function.leftLim f.toFun 1 ≠ f.toFun 1 ∧
      @ContinuousAt _ _ (SkorokhodSpace.totalTopology (E := ℝ) (0 : ℝ)) _
        (fun g : D(ℝ, ℝ) => g.toFun 1) f := by
  refine ⟨SkorokhodSpace.step, ?_, ?_⟩
  · rw [SkorokhodSpace.leftLim_step, SkorokhodSpace.step_apply, if_pos le_rfl]
    norm_num
  · have h := SkorokhodSpace.continuous_eval_exhaustionMax (ι := ℝ) (E := ℝ) 0 1
    have hb : exhaustionMax (0 : ℝ) ((1 : ℕ) : ℝ) = (1 : ℝ) := by
      rw [exhaustionMax_real]
      norm_num
    rw [hb] at h
    exact @Continuous.continuousAt _ _ (SkorokhodSpace.totalTopology (E := ℝ) (0 : ℝ)) _ _ _ h

omit [BasePoint ι] in
/-- **The one rung at which the integral metric and the summed one part company.**

For the summed metric the passage from the metric to a window is
`SkorokhodSpace.min_one_distOn_le`, and it holds at *every* window: each integer
radius carries its own geometric weight in the sum, so a small `totalDist` is a
small `distOn` at each radius separately.  The integral has no such weights, and
a small `intDist` says nothing at any *named* radius --- which is exactly why it
is a Skorokhod metric and the sum is not.

What survives, and it is enough, is this: if the time changes `l n` compare the
pairs `x n`, `y n` at a summable cost `γ n` in `intWith`, then at **almost every**
radius the truncated window distances are themselves summable in `n`.  A
completeness proof needs a summable rate at one radius at a time and may choose
the radius, so it may choose one of these; that is the whole adaptation.  The
argument is the one `SkorokhodSpace.eq_of_intDist_eq_zero` runs with `γ n = 2⁻ⁿ`,
factored out and stated with a general summable `γ`: `lintegral_tsum` makes the
series of integrands integrable, `MeasureTheory.ae_lt_top` makes it finite almost
everywhere, and at a radius where it is finite `ENNReal.tsum_coe_ne_top_iff_summable`
turns the finiteness back into summability over `ℝ`.

The factor `Real.exp (-u)` divides out because it does not depend on `n`; that is
`summable_mul_left_iff`, and it is why the weight of the integral costs nothing
here while the weight `2⁻ᵐ` of the sum was what made the sum too strong. -/
theorem SkorokhodSpace.ae_summable_min_one_distWith [SecondCountableTopology E]
    (t₀ : ι) (l : ℕ → TimeChange ι) (x y : ℕ → D(ι, E)) (γ : ℕ → ℝ)
    (hγ : Summable γ) (hle : ∀ n, SkorokhodSpace.intWith t₀ (l n) (x n) (y n) ≤ γ n) :
    ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Summable fun n : ℕ => min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)) := by
  have hnn : ∀ (n : ℕ) (u : ℝ), 0 ≤ Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)) := fun n u =>
    mul_nonneg (Real.exp_pos _).le
      (le_min zero_le_one (SkorokhodSpace.distWith_nonneg t₀ u (l n) (x n) (y n)))
  have hmeas : ∀ n : ℕ, Measurable fun u : ℝ => Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)) := fun n =>
    (Real.measurable_exp.comp measurable_neg).mul
      (measurable_const.min (SkorokhodSpace.measurable_distWith t₀ (l n) (x n) (y n)))
  have hγ0 : ∀ n, 0 ≤ γ n := fun n =>
    (SkorokhodSpace.intWith_nonneg t₀ (l n) (x n) (y n)).trans (hle n)
  have hfin : ∫⁻ u in Set.Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun n => ((hmeas n).ennreal_ofReal).aemeasurable]
    have hterm : ∀ n : ℕ, ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u) *
        min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)))
        ≤ ENNReal.ofReal (γ n) := by
      intro n
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (SkorokhodSpace.integrableOn_intDist t₀ (l n) (x n) (y n))
        (Filter.Eventually.of_forall (hnn n))]
      exact ENNReal.ofReal_le_ofReal (hle n)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [← ENNReal.ofReal_tsum_of_nonneg hγ0 hγ]
    exact ENNReal.ofReal_ne_top
  have hmtsum : Measurable fun u : ℝ => ∑' n : ℕ, ENNReal.ofReal (Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n))) := by
    simp only [ENNReal.tsum_eq_iSup_sum]
    exact Measurable.iSup fun s =>
      Finset.measurable_sum s fun n _ => (hmeas n).ennreal_ofReal
  refine (MeasureTheory.ae_lt_top hmtsum hfin).mono fun u hu => ?_
  have hnnreal : Summable fun n : ℕ => Real.toNNReal (Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n))) :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 hu.ne
  have hsum : Summable fun n : ℕ => Real.exp (-u) *
      min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)) :=
    (NNReal.summable_coe.2 hnnreal).congr fun n => Real.coe_toNNReal _ (hnn n u)
  exact (summable_mul_left_iff (Real.exp_pos (-u)).ne').1 hsum

/-- Undoing the truncation at `1`.  `ae_summable_min_one_distWith` delivers the
summability of `min 1 aₙ`, and the assembly below needs it for `aₙ` itself,
because the increments it estimates are bounded by `distWith` and not by its
truncation.  It costs nothing: a summable sequence tends to `0`, so `min 1 aₙ`
is eventually `aₙ`, and summability does not see a finite prefix. -/
theorem summable_of_summable_min_one {a : ℕ → ℝ}
    (h : Summable fun n => min 1 (a n)) : Summable a := by
  have hev : ∀ᶠ n in Filter.atTop, min 1 (a n) < 1 :=
    h.tendsto_atTop_zero.eventually_lt_const one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  rw [← summable_nat_add_iff N]
  refine ((summable_nat_add_iff N).2 h).congr fun n => ?_
  have hlt := hN (n + N) (Nat.le_add_left N n)
  rcases lt_or_ge (a (n + N)) 1 with hax | hax
  · exact min_eq_right hax.le
  · rw [min_eq_left hax] at hlt
    exact absurd hlt (lt_irrefl 1)

omit [BasePoint ι] in
/-- One term of the supremum that defines `distWith` lies below it.  This is the
form in which the assembly reads the window pseudodistance off a single pair of
points, and it is `le_ciSup` against
`bddAbove_range_dist_restrictExhaustion`. -/
theorem SkorokhodSpace.dist_le_distWith (t₀ : ι) (u : ℝ) (l : TimeChange ι)
    (f g : D(ι, E)) (t : ι) :
    dist (f.toFun (clamp t₀ u (l.toOrderIso t))) (g.toFun (clamp t₀ u t))
      ≤ SkorokhodSpace.distWith t₀ u l f g :=
  le_ciSup (SkorokhodSpace.bddAbove_range_dist_restrictExhaustion t₀ u f g l) t

omit [BasePoint ι] in
/-- **Good radii are unbounded.**  `ae_summable_min_one_distWith` says that the
window distances are summable at almost every radius; the assembly needs one
such radius above *every* bound, because it has to control a window large
enough to contain the images of `exhaustion t₀ m` under all the time changes at
once.  It gets one because the bad radii form a null set while `Set.Ioi c` has
infinite measure. -/
theorem SkorokhodSpace.exists_gt_summable_distWith [SecondCountableTopology E]
    (t₀ : ι) (l : ℕ → TimeChange ι) (x y : ℕ → D(ι, E)) (γ : ℕ → ℝ)
    (hγ : Summable γ) (hle : ∀ n, SkorokhodSpace.intWith t₀ (l n) (x n) (y n) ≤ γ n)
    (c : ℝ) :
    ∃ u : ℝ, c < u ∧ 0 < u ∧
      Summable fun n : ℕ => SkorokhodSpace.distWith t₀ u (l n) (x n) (y n) := by
  have hae := SkorokhodSpace.ae_summable_min_one_distWith t₀ l x y γ hγ hle
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hae
  by_contra hcon
  have hsub : Set.Ioi (max c 0) ⊆ {u : ℝ | ¬ (u ∈ Set.Ioi (0 : ℝ) →
      Summable fun n : ℕ => min 1 (SkorokhodSpace.distWith t₀ u (l n) (x n) (y n)))} := by
    intro v hv
    simp only [Set.mem_ofPred_eq]
    intro hmem
    have hv0 : (0 : ℝ) < v := lt_of_le_of_lt (le_max_right _ _) hv
    exact hcon ⟨v, lt_of_le_of_lt (le_max_left _ _) hv, hv0,
      summable_of_summable_min_one (hmem (Set.mem_Ioi.2 hv0))⟩
  have hmono := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  rw [MeasureTheory.ae_iff.1 hae, Real.volume_Ioi] at hmono
  simp at hmono

omit [BasePoint ι] in
/-- **The assembly**, the last rung of `CompleteSpace D(ι, E)` and the one the
README of Milestone 5 names `tendsto_of_partialComp`.

The data is a sequence of paths `x` together with time changes `l n` whose norms
and whose windowed costs are both dominated by a summable `γ` --- exactly what
`SkorokhodSpace.exists_lt_intDist_add` produces from a Cauchy sequence whose
consecutive distances are summable.  The conclusion is the limit path `z` and the
single time change `L` of `TimeChange.exists_tendsto_norm_tail_le`, together with
the statement that the reparametrised paths `x n ∘ (Pₙ⁻¹ L)` converge to `z`
**uniformly on every window**, `Pₙ` being the `n`-th partial composition.

Three things carry it.  The recursion `κ n = l n * κ (n+1)` for
`κ n = Pₙ⁻¹ * L` turns the increment `dist (x n (κ n t)) (x (n+1) (κ (n+1) t))`
into `dist (x n (l n s)) (x (n+1) s)` with `s = κ (n+1) t`, which is one term of
`distWith`.  The uniform norm bound `‖κ n‖ ≤ ∑' γ` keeps `s` and `l n s` inside
the window of radius `exp (∑' γ) * m` whenever `t` lies in the window of radius
`m`, so the same `distWith` bounds the increment for every `t` of that window at
once.  And `exists_gt_summable_distWith` supplies, above that radius, one at
which the `distWith` are summable in `n`; `cauchySeq_of_dist_le_of_summable`
then gives the limit pointwise and `dist_le_tsum_of_dist_le_of_tendsto` gives it
uniformly, with the tail of the series as the rate. -/
theorem SkorokhodSpace.tendsto_of_partialComp [SecondCountableTopology E]
    [CompleteSpace E] (t₀ : ι) (x : ℕ → D(ι, E)) (l : ℕ → TimeChange ι)
    (hl : ∀ n, l n ∈ TimeChange.fixing t₀) (γ : ℕ → ℝ) (hγ : Summable γ)
    (hnorm : ∀ n, (l n).norm ≤ γ n)
    (hint : ∀ n, SkorokhodSpace.intWith t₀ (l n) (x n) (x (n + 1)) ≤ γ n) :
    ∃ (z : D(ι, E)) (L : TimeChange ι), L ∈ TimeChange.fixing t₀ ∧
      (∀ n : ℕ, ((TimeChange.partialComp l n)⁻¹ * L).norm ≤ ∑' i, γ (n + i)) ∧
      ∀ m : ℕ, TendstoUniformlyOn
        (fun (n : ℕ) (t : ι) =>
          (x n).toFun (((TimeChange.partialComp l n)⁻¹ * L).toOrderIso t))
        z.toFun Filter.atTop (exhaustion t₀ m) := by
  classical
  have hγ0 : ∀ n, 0 ≤ γ n := fun n => (TimeChange.norm_nonneg (l n)).trans (hnorm n)
  obtain ⟨L, hLfix, hLtail, -⟩ :=
    TimeChange.exists_tendsto_norm_tail_le t₀ l hl γ hnorm hγ
  set κ : ℕ → TimeChange ι := fun n => (TimeChange.partialComp l n)⁻¹ * L with hκdef
  have hκfix : ∀ n, κ n ∈ TimeChange.fixing t₀ := fun n =>
    (TimeChange.fixing t₀).mul_mem
      ((TimeChange.fixing t₀).inv_mem (TimeChange.partialComp_mem_fixing hl n)) hLfix
  have hrec : ∀ n, κ n = l n * κ (n + 1) := by
    intro n
    simp only [hκdef, TimeChange.partialComp_succ, mul_inv_rev]
    group
  -- the tails of `γ` are below its sum, so all the `κ n` share one Lipschitz bound
  have hΓ0 : (0 : ℝ) ≤ ∑' i, γ i := tsum_nonneg hγ0
  have hTle : ∀ n : ℕ, (∑' i, γ (n + i)) ≤ ∑' i, γ i := by
    intro n
    have hcomm : (∑' i, γ (n + i)) = ∑' i, γ (i + n) := by
      simp only [Nat.add_comm]
    have hsplit := hγ.sum_add_tsum_nat_add (f := γ) n
    have hnn : 0 ≤ ∑ i ∈ Finset.range n, γ i := Finset.sum_nonneg fun i _ => hγ0 i
    rw [hcomm]
    linarith
  have hκnorm : ∀ n, (κ n).norm ≤ ∑' i, γ i := fun n => (hLtail n).trans (hTle n)
  -- the image of a window under any `κ n` sits inside the window blown up by `exp (∑' γ)`
  have hwin : ∀ (m : ℕ) (t : ι), t ∈ exhaustion t₀ (m : ℝ) → ∀ n : ℕ,
      dist ((κ n).toOrderIso t) t₀ ≤ Real.exp (∑' i, γ i) * m := by
    intro m t ht n
    have h₀ : (κ n).toOrderIso t₀ = t₀ := hκfix n
    have hd := TimeChange.dist_le_exp_norm_mul (κ n) t₀ t
    rw [h₀] at hd
    have hdt : dist t₀ t ≤ (m : ℝ) := by
      have := ht
      simp only [exhaustion, Metric.mem_closedBall] at this
      rw [dist_comm]
      exact this.trans (max_le le_rfl (Nat.cast_nonneg m))
    rw [dist_comm]
    refine hd.trans ?_
    exact mul_le_mul (Real.exp_le_exp.2 (hκnorm n)) hdt dist_nonneg (Real.exp_pos _).le
  -- one good radius per window, above the blown up radius
  have hgood : ∀ m : ℕ, ∃ u : ℝ, Real.exp (∑' i, γ i) * m < u ∧ 0 < u ∧
      Summable fun n : ℕ => SkorokhodSpace.distWith t₀ u (l n) (x n) (x (n + 1)) := fun m =>
    SkorokhodSpace.exists_gt_summable_distWith t₀ l x (fun n => x (n + 1)) γ hγ hint _
  choose u hu hu0 husum using hgood
  set Z : ℕ → ι → E := fun n t => (x n).toFun ((κ n).toOrderIso t) with hZdef
  have hZcadlag : ∀ n, IsCadlag (Z n) := fun n =>
    (x n).isCadlag.comp_monotone_continuous (κ n).toOrderIso.monotone
      (κ n).toOrderIso.continuous
  -- the increment on a window is one term of `distWith` at the good radius
  have hstep : ∀ (m : ℕ) (t : ι), t ∈ exhaustion t₀ (m : ℝ) → ∀ n : ℕ,
      dist (Z n t) (Z (n + 1) t)
        ≤ SkorokhodSpace.distWith t₀ (u m) (l n) (x n) (x (n + 1)) := by
    intro m t ht n
    have hmem : ∀ k : ℕ, (κ k).toOrderIso t ∈ exhaustion t₀ (u m) := by
      intro k
      simp only [exhaustion, Metric.mem_closedBall]
      exact (hwin m t ht k).trans (le_max_of_le_left (hu m).le)
    have hkey : (κ n).toOrderIso t = (l n).toOrderIso ((κ (n + 1)).toOrderIso t) := by
      conv_lhs => rw [hrec n]
      rfl
    have h₁ : clamp t₀ (u m) ((l n).toOrderIso ((κ (n + 1)).toOrderIso t))
        = (l n).toOrderIso ((κ (n + 1)).toOrderIso t) := by
      rw [← hkey]
      exact clamp_eq_self (hmem n)
    have h₂ : clamp t₀ (u m) ((κ (n + 1)).toOrderIso t) = (κ (n + 1)).toOrderIso t :=
      clamp_eq_self (hmem (n + 1))
    have hbound := SkorokhodSpace.dist_le_distWith t₀ (u m) (l n) (x n) (x (n + 1))
      ((κ (n + 1)).toOrderIso t)
    rw [h₁, h₂] at hbound
    simpa only [hZdef, hkey] using hbound
  -- pointwise convergence, then the limit path
  have hpt : ∀ t : ι, ∃ e : E, Filter.Tendsto (fun n => Z n t) Filter.atTop (𝓝 e) := by
    intro t
    obtain ⟨m, hm⟩ := exists_nat_ge (dist t t₀)
    have ht : t ∈ exhaustion t₀ (m : ℝ) := by
      simp only [exhaustion, Metric.mem_closedBall]
      exact hm.trans (le_max_left _ _)
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable
      (fun n => SkorokhodSpace.distWith t₀ (u m) (l n) (x n) (x (n + 1)))
      (fun n => hstep m t ht n) (husum m))
  choose zf hzf using hpt
  have hunif : ∀ m : ℕ,
      TendstoUniformlyOn Z zf Filter.atTop (exhaustion t₀ (m : ℝ)) := by
    intro m
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htail : Filter.Tendsto
        (fun n : ℕ => ∑' k : ℕ,
          SkorokhodSpace.distWith t₀ (u m) (l (n + k)) (x (n + k)) (x (n + k + 1)))
        Filter.atTop (𝓝 0) := by
      have h := tendsto_sum_nat_add
        (fun i : ℕ => SkorokhodSpace.distWith t₀ (u m) (l i) (x i) (x (i + 1)))
      simpa only [Nat.add_comm] using h
    filter_upwards [htail.eventually (gt_mem_nhds hε)] with n hn t ht
    have hle := dist_le_tsum_of_dist_le_of_tendsto
      (fun k => SkorokhodSpace.distWith t₀ (u m) (l k) (x k) (x (k + 1)))
      (fun k => hstep m t ht k) (husum m) (hzf t) n
    rw [dist_comm]
    exact lt_of_le_of_lt hle hn
  refine ⟨⟨zf, IsCadlag.of_tendstoUniformlyOn_exhaustion t₀ hZcadlag hunif⟩, L, hLfix,
    hLtail, fun m => hunif m⟩

omit [OrderTopology ι] [ProperSpace ι] [BasePoint ι] in
/-- **A gap above a point pins every small time change down at it.**

This is the first rung of what is left of `CompleteSpace D(ι, E)` after
`SkorokhodSpace.tendsto_of_partialComp`, and it settles the one case of that
step which is not a limit argument.  Passing from locally uniform convergence
back to `intDist` compares `x n` with `z` at `exhaustionMax t₀ u`, the greatest
point of the window, because `clamp` sends everything above it there; the
comparison is off by the time change, so it needs `z` to be continuous at that
point --- unless the time change fixes it.

The radii at which `exhaustionMax t₀ u` is a *fixed* point of the index form a
level set of a monotone map, and such a set has positive measure only when the
index has a gap above that point.  Where there is a gap of width `δ`, this lemma
applies: a time change anchored at `t₀` moves no point of the window by more than
`(exp ‖λ‖ - 1) · 2u`, and its inverse moves it no further, so once that quantity
is below `δ` neither `λ A` nor `λ⁻¹ A` can clear the gap, and both orderings
`λ A < A` and `A < λ A` are excluded. -/
theorem TimeChange.eq_of_gap_of_norm_lt (t₀ : ι) {u : ℝ} (hu : 0 ≤ u) {A : ι}
    (hA : A ∈ exhaustion t₀ u) {δ : ℝ}
    (hgap : ∀ t : ι, A < t → δ ≤ dist A t) {l : TimeChange ι}
    (h₀ : l.toOrderIso t₀ = t₀) (h : (Real.exp l.norm - 1) * (2 * u) < δ) :
    l.toOrderIso A = A := by
  have hfix : l ∈ TimeChange.fixing t₀ := h₀
  have hinv : (l⁻¹).toOrderIso t₀ = t₀ := (TimeChange.fixing t₀).inv_mem hfix
  have hd1 : dist (l.toOrderIso A) A ≤ (Real.exp l.norm - 1) * (2 * u) :=
    TimeChange.dist_le_of_norm_le t₀ hu h₀ le_rfl hA
  have hd2 : dist ((l⁻¹).toOrderIso A) A ≤ (Real.exp l.norm - 1) * (2 * u) :=
    TimeChange.dist_le_of_norm_le t₀ hu hinv (TimeChange.norm_inv l).le hA
  rcases lt_trichotomy (l.toOrderIso A) A with hlt | heq | hgt
  · have hlt' : A < (l⁻¹).toOrderIso A := by
      have hs := l.toOrderIso.symm.strictMono hlt
      show A < l.toOrderIso.symm A
      simpa using hs
    have hge := hgap _ hlt'
    rw [dist_comm] at hd2
    linarith
  · exact heq
  · have hge := hgap _ hgt
    rw [dist_comm] at hd1
    linarith

/-- **Completeness**, and it is a commitment again: it was withdrawn on 2026-09-08
because it is false for the summed metric, and the instance is now the integral
one, for which the counterexample --- a jump marching down onto a window endpoint
--- is not one, because a single radius is a Lebesgue null set.

The proof is Billingsley's, and its rungs are proved and stand above, all of them
independent of which of the two metrics is the instance.
`SkorokhodSpace.exists_lt_intDist_add` produces, from a Cauchy sequence, one time
change per step with summable norms; `TimeChange.exists_tendsto_of_summable_norm`
composes them into a single time change and
`TimeChange.exists_tendsto_norm_tail_le` says how far the `n`-th partial
composition still is from it; `IsCadlag.of_tendstoUniformlyOn_exhaustion` catches
the limit path, uniform convergence on every window being enough because being
càdlàg is local (`IsCadlag.of_forall_eventuallyEq`).  What the integral form adds
over the summed one, and it is the whole difference, is the step from
`intDist (x n) (x k) < ε` to a windowed estimate: it holds not at every radius
but at almost every radius, which is what `SkorokhodSpace.eq_of_intDist_eq_zero`
already does for the separation axiom and what a completeness proof does again
with `ε` in place of `0`.

Anything below that uses this instance depends on `sorryAx` until it is proved;
that is what a `sorry` in an `instance` costs, and it is why the three
declarations here are the three the milestone owes and not one more. -/
instance SkorokhodSpace.instCompleteSpace [SecondCountableTopology E] [CompleteSpace E] :
    CompleteSpace D(ι, E) := sorry

/-- **Separability**: the step paths with finitely many jumps, the jump times in a
countable dense subset of `ι` and the values in a countable dense subset of `E`,
are dense in `D(ι, E)`.  They are countable because `ι` is proper, hence
separable, and each window meets only finitely many of the jump times of a given
path (`countable_leftJumpSet` of Milestone 2, with `isCompact_exhaustion`).

`[SeparableSpace E]` is the hypothesis, not `[PolishSpace E]`: the approximation
of a càdlàg path by a step path uses the right limits and the compactness of the
window, and completeness of `E` occurs in it nowhere. -/
instance SkorokhodSpace.instSeparableSpace [SecondCountableTopology E]
    [TopologicalSpace.SeparableSpace E] : TopologicalSpace.SeparableSpace D(ι, E) := sorry

/-- **Polishness**, and it owes nothing of its own: Mathlib builds `PolishSpace`
out of a separable topology and a completely metrizable one, and
`SkorokhodSpace.instMetricSpace` together with the two instances above is exactly
that.  It is `fact:PSpolish` of the manuscript for the `J₁` topology, and it is
what `rem:EKrelcompact` consumes. -/
instance SkorokhodSpace.instPolishSpace [PolishSpace E] [CompleteSpace E] :
    PolishSpace D(ι, E) := inferInstance

/-! ## Milestone 6: the Borel structure

The measurable structure on `D(ι, E)` is the Borel one of the metric above, so
it is declared here rather than assumed; everything in this section is stated
against it.  `[PolishSpace E]` comes first because it is what supplies the
`[SecondCountableTopology E]` of `SkorokhodSpace.instMetricSpace`, and without a
metric on `D(ι, E)` there is no Borel structure to declare. -/

variable [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

noncomputable instance : MeasurableSpace D(ι, E) := borel _
instance : BorelSpace D(ι, E) := ⟨rfl⟩

theorem SkorokhodSpace.measurableEmbedding_piDense {D : Set ι} (hD : D.Countable)
    (hD' : Dense D) :
    MeasurableEmbedding (fun f : D(ι, E) => fun t : D => f.toFun t) := sorry

theorem SkorokhodSpace.borel_eq_iSup_comap_eval :
    (borel D(ι, E)) =
      ⨆ t : ι, MeasurableSpace.comap (fun f : D(ι, E) => f.toFun t) inferInstance :=
  sorry

/-! ## Milestone 7: the modulus and compactness

`SkorokhodSpace.modulus` was `sorry` as a **definition** until 2026-09-08, which
made every statement about it a statement about `sorryAx` --- the same trap as a
statement whose body is `True`.  It is now written out, and two deviations from
the roadmap's wording were forced by that writing; both are recorded at the
declarations themselves.  The first is the value type: the modulus is `ℝ≥0∞` and
not `ℝ`.  The second is that the subdivision predicate is named and separate, so
that the infimum ranges over a `Prop` and needs no `BddBelow`. -/

omit [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
/-- A `δ`-sparse subdivision of the window `exhaustion t₀ m`: a strictly
monotone `t : Fin (n + 1) → ι` running from the least to the greatest point of
the window, all of whose consecutive gaps exceed `δ`.  This is Billingsley's
condition `min i, (t i - t (i-1)) > δ` verbatim, and the `>` is strict on
purpose: it is what makes the one jump of a step function cost nothing, since
the jump time may be used as a subdivision point. -/
def SkorokhodSpace.IsSubdivision (t₀ : ι) (u : ℝ) (δ : ℝ) {n : ℕ}
    (t : Fin (n + 1) → ι) : Prop :=
  StrictMono t ∧ t 0 = exhaustionMin t₀ u ∧ t (Fin.last n) = exhaustionMax t₀ u ∧
    ∀ i : Fin n, δ < dist (t i.castSucc) (t i.succ)

omit [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
/-- The oscillation of `f` over the half open cells of a subdivision, measured
from the left endpoint of each cell.  The cells are `Set.Ico` and not
`Set.Icc`: the jump of a càdlàg path sits at the left endpoint of the *next*
cell, and a modulus that saw it from the previous one would not tend to `0` for
any step function. -/
noncomputable def SkorokhodSpace.subdivisionOsc (f : D(ι, E)) {n : ℕ}
    (t : Fin (n + 1) → ι) : ℝ≥0∞ :=
  ⨆ i : Fin n, ⨆ s ∈ Set.Ico (t i.castSucc) (t i.succ),
    edist (f.toFun s) (f.toFun (t i.castSucc))

omit [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
/-- The càdlàg modulus on `exhaustion t₀ u`, Billingsley's `w'`: the least
oscillation achievable by a `δ`-sparse subdivision of the window.

**It is `ℝ≥0∞` valued, and the roadmap said `ℝ`.**  The reason is the empty
case, and it is not cosmetic.  Once `δ` reaches the diameter of the window
there is no `δ`-sparse subdivision at all --- not even the trivial one from the
least to the greatest point --- so the infimum is over the empty set.  In `ℝ`
that is the junk value `0`, and `modulus` would then be `0` for all large `δ`,
which destroys the monotonicity in `δ` that Milestone 7 asks for and would make
`tendsto_modulus` say nothing.  In `ℝ≥0∞` it is `⊤`, which is the classical
convention and makes `SkorokhodSpace.modulus_mono` a theorem.  The same choice
pays a second time in `isCompact_closure_iff`, where `⨆ f ∈ A, modulus …` over
an unbounded family would again be a junk `0` in `ℝ`. -/
noncomputable def SkorokhodSpace.modulus (t₀ : ι) (u : ℝ) (f : D(ι, E)) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ⨅ t : Fin (n + 1) → ι, ⨅ _ : SkorokhodSpace.IsSubdivision t₀ u δ t,
    SkorokhodSpace.subdivisionOsc f t

omit [AdditiveDist ι] [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
/-- The modulus is monotone in `δ`: a `δ₂`-sparse subdivision is `δ₁`-sparse for
every smaller `δ₁`, so the infimum defining `modulus δ₁` runs over a larger set.
This is the item of Milestone 7 that the `ℝ≥0∞` valuation buys; over `ℝ` it is
false, by the junk value at large `δ`. -/
theorem SkorokhodSpace.modulus_mono (t₀ : ι) (u : ℝ) (f : D(ι, E)) :
    Monotone (SkorokhodSpace.modulus t₀ u f) := by
  intro δ₁ δ₂ h
  refine le_iInf fun n => le_iInf fun t => le_iInf fun ht => ?_
  exact iInf_le_of_le n (iInf_le_of_le t (iInf_le_of_le
    ⟨ht.1, ht.2.1, ht.2.2.1, fun i => lt_of_le_of_lt h (ht.2.2.2 i)⟩ le_rfl))

omit [AdditiveDist ι] [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
/-- The degenerate window of Milestone 4's fourth acceptance example: when the
window is a single point the empty subdivision `n = 0` is admissible for every
`δ`, and it has no cells, so the modulus is `0`.  This is the one value of
`modulus` that is available before `tendsto_modulus`, and it is what fixes the
orientation of the definition: with `Set.Icc` cells, or with the oscillation
taken between the subdivision points rather than inside the cells, the empty
subdivision would not be admissible and this would fail. -/
theorem SkorokhodSpace.modulus_eq_zero_of_exhaustion_subsingleton (t₀ : ι) (u : ℝ)
    (f : D(ι, E)) (δ : ℝ) (h : exhaustionMin t₀ u = exhaustionMax t₀ u) :
    SkorokhodSpace.modulus t₀ u f δ = 0 := by
  refine le_antisymm ?_ (by simp)
  have hsm : StrictMono (fun _ : Fin (0 + 1) => exhaustionMin t₀ u) := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have hab' : (a : ℕ) < (b : ℕ) := hab
    omega
  refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => exhaustionMin t₀ u)
    (iInf_le_of_le ⟨hsm, rfl, h, fun i => i.elim0⟩ ?_))
  simp [SkorokhodSpace.subdivisionOsc]

omit [MeasurableSpace E] [BorelSpace E] [PolishSpace E] [BasePoint ι] in
theorem SkorokhodSpace.tendsto_modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    Tendsto (SkorokhodSpace.modulus t₀ m f) (𝓝[>] 0) (𝓝 0) := sorry

/-- The compactness criterion.  The base point is the one of the instance and
not a parameter: the left hand side speaks of the topology of `D(ι, E)`, which
is `SkorokhodSpace.metricSpaceInt basePoint`, and a `t₀` free to differ from it
would make the two sides speak of two different spaces.  This is the correction
that `BasePoint` forced, and it is the reason the class carries data. -/
theorem SkorokhodSpace.isCompact_closure_iff (A : Set D(ι, E)) :
    IsCompact (closure A) ↔ ∀ m : ℕ,
      IsCompact (closure {x | ∃ f ∈ A, ∃ t ∈ exhaustion (basePoint : ι) m, f.toFun t = x}) ∧
      Tendsto (fun δ => ⨆ f ∈ A, SkorokhodSpace.modulus (basePoint : ι) m f δ)
        (𝓝[>] 0) (𝓝 0) := sorry

