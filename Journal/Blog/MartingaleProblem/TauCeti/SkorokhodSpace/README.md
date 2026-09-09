# The Skorokhod space

The space of càdlàg paths with the `J₁` topology. The string `cadlag` does not occur in
Mathlib, and neither does the space. What Mathlib does have, and what is **not**
to be rebuilt:

* `Mathlib/Topology/Order/LeftRightLim.lean`: `Function.leftLim` and
  `Function.rightLim`, defined for `f : α → β` with `[LinearOrder α]` and
  `[TopologicalSpace β]`, together with the part of the one-sided-limit API that
  holds for an arbitrary `f`. That part is what every statement about left
  limits below is to be phrased through, and it is exactly:
  `tendsto_leftLim_of_tendsto` and `tendsto_rightLim_of_tendsto`, whose
  hypothesis is `∃ y, Tendsto f (𝓝[<] a) (𝓝 y)` and hence literally the
  `left_limit` field of `IsCadlag`; `ContinuousWithinAt.leftLim_eq` and
  `ContinuousWithinAt.rightLim_eq`, which give `leftLim f a = f a` from
  one-sided continuity; `leftLim_eq_of_tendsto`, `rightLim_eq_of_tendsto`,
  `leftLim_eq_of_eq_bot`, `leftLim_eq_of_not_tendsto`, `leftLim_eq_of_isBot`,
  `rightLim_eq_of_isTop`; and `mapClusterPt_leftLim`, `mapClusterPt_rightLim`.
  Each of these asks `[LinearOrder α] [TopologicalSpace α] [OrderTopology α]`,
  and the four `_eq_` ones additionally `[T2Space β]`.

  The names `tendsto_leftLim`, `tendsto_rightLim`, `tendsto_leftLim_within`,
  `continuousWithinAt_Iio_iff_leftLim_eq`,
  `continuousWithinAt_Ioi_iff_rightLim_eq` and
  `continuousAt_iff_leftLim_eq_rightLim` are in the namespaces `Monotone` and
  `Antitone` of that file, carry a monotonicity hypothesis on `f` by `include`,
  and ask `[ConditionallyCompleteLinearOrder β] [OrderTopology β]` of the
  codomain. A càdlàg path into a metric space satisfies none of that, so none of
  them applies here, and this roadmap uses none of them.
* `Monotone.countable_not_continuousAt`, the monotone case of the countability
  of the jump set, in `Mathlib/Topology/Order/Monotone.lean`, together with
  `MonotoneOn.countable_not_continuousWithinAt_Ioi`,
  `MonotoneOn.countable_not_continuousWithinAt_Iio` and
  `MonotoneOn.countable_not_continuousWithinAt`.
* `MeasureTheory.StieltjesFunction` in
  `Mathlib/MeasureTheory/Measure/Stieltjes.lean`: a bundled monotone right
  continuous function, with `right_continuous` and `rightLim_eq`. It is the
  precedent for how a right continuity condition is bundled in Mathlib, and
  `IsCadlag` below should read like it. Its field states right continuity as
  `ContinuousWithinAt f (Ici x) x`; `Function.RightContinuous` below uses `Ioi`,
  and `continuousWithinAt_Ioi_iff_Ici` is the bridge, the same one the proof of
  `StieltjesFunction.rightLim_eq` takes.
* Prokhorov's theorem, tightness and the Lévy–Prokhorov metric in
  `Mathlib/MeasureTheory/Measure/`, used in Milestone 8.
* `orderTopology_of_ordConnected` in `Mathlib/Topology/Order/Basic.lean`,
  `ProperSpace.of_isClosed`, and `Subgroup.isClosed_of_discrete` in
  `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean`, whose additive form is
  what the lattice instance of Milestone 1 needs.

This roadmap depends on the roadmap **WeakConvergence** for separating and
convergence determining classes (Milestone 1 there) and for the Skorokhod
representation theorem (Milestone 3 there).

The time index is a linear order carrying a metric that induces the order
topology, is additive along the order, and has compact closed balls. That
hypothesis is equivalent to being a closed subset of `ℝ` (Milestone 1), and
stating it as a class rather than fixing `[0,1]` or `[0,∞)` is what makes the
four cases `ℝ`, `[0,∞)`, `[0,T]` and `h • ℤ` — and every closed subset of them —
instances of one development.

**Prior art, cited and not presupposed.** The repository
`RemyDegenne/brownian-motion` (Apache-2.0) contains a development of càdlàg
paths in `BrownianMotion/StochasticIntegral/Cadlag.lean`. It is named here as a
source that an implementer may consult and, the licence permitting, draw on with
its copyright header preserved — **not** as the specification. Every milestone
below states what is wanted in full and is to be reviewed on its own terms; a
declaration that agrees with that file is welcome, and one that improves on it
is more welcome. Nothing here should be accepted merely because it matches the
external material.

## Milestone 1: the index typeclass

```
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u
```

* Instances for `ℝ`, `ℤ`, `ℕ`, and `NNReal`.
* The instance for a subtype: any `s : Set α` with `[AdditiveDist α]` inherits
  `AdditiveDist s`, definitionally. Two points where this does not carry as far
  as it looks, both to be settled here rather than met later:
  * The subtype instance does not fire through a `SetLike` hull. `AdditiveDist
    (AddSubgroup.zmultiples h)` does not resolve, while
    `AdditiveDist ((AddSubgroup.zmultiples h : Set ℝ))` does. Provide the
    instance for a `SetLike` carrier, or state once which of the two forms every
    later declaration uses.
  * A discrete subset is not order-connected, so
    `orderTopology_of_ordConnected` does not apply to `h • ℤ`, and
    `OrderTopology.of_discreteTopology` asks for `PredOrder` and `SuccOrder`,
    which the subtype does not carry. Supply `PredOrder` and `SuccOrder` for a
    discrete `AdditiveDist` subtype, or `LocallyFiniteOrder`, which feeds the
    second instance of the same file,
    `OrderTopology.of_linearLocallyFinite [LinearOrder α] [LocallyFiniteOrder α]
    [DiscreteTopology α]`, or the `OrderTopology` instance directly. Both
    instances are in `Mathlib/Topology/Instances/Discrete.lean`.
* `lengthCoord`, **written and proved 2026-09-08**: the coordinate of the index,
  `lengthCoord t₀ t = if t₀ ≤ t then dist t₀ t else -dist t₀ t`. Its increment
  along the order is the distance itself, with no absolute value
  (`sub_lengthCoord_of_le`), from which `strictMono_lengthCoord`,
  `isometry_lengthCoord` and `lengthCoord_self` follow. The coordinate is
  written out rather than being read off the existence statement below, because
  a construction of a time change needs a *named* coordinate: the order
  isomorphism produced by an existential is opaque, and no explicit time change
  can be written against it. This is the same reason `BasePoint` is data.
* `exists_orderIso_isometry_real`, **proved 2026-09-08**: a linear order with a
  metric additive along the order is order isomorphic and isometric to a closed
  subset of `ℝ`, namely the range of `lengthCoord`. It is `lengthCoord` together
  with `StrictMono.orderIso` and `Isometry.isClosedEmbedding`. **The order
  topology is not used**, and the statement is `omit [OrderTopology ι]`:
  `AdditiveDist` makes the coordinate an isometry, `MetricSpace` rather than
  `PseudoMetricSpace` makes it strictly monotone, and `ProperSpace` makes its
  range closed — through `complete_of_proper`, so what is used is completeness
  and not properness itself. The empty index is a case of its own and takes
  `s = ∅`, since with no point there is no base point to take the coordinate
  around.
* The four running instances `ℝ`, `Set.Ici (0:ℝ)`, `Set.Icc (0:ℝ) T`,
  `AddSubgroup.zmultiples (h : ℝ)` carry
  `[LinearOrder] [MetricSpace] [OrderTopology] [AdditiveDist] [ProperSpace]`.
  `ProperSpace` for a closed subset follows from `ProperSpace.of_isClosed`, and
  for `AddSubgroup.zmultiples h` from `AddSubgroup.isClosed_of_discrete`;
  `OrderTopology` for an order-connected subset follows from the existing
  instance, and for a discrete subset from the two items above. As standalone
  types `ℝ` and `ℤ` carry all five instances already. `Real.instAdditiveDist`
  is written and proved (2026-09-07) — three `abs_of_nonpos` and a `ring` on
  `Real.dist_eq` —, because `TimeChange.not_normOn_mul_le` of Milestone 3
  instantiates its refutation at `ℝ` and cannot do so without it. The other
  three follow from it through `instAdditiveDistSubtype`.
* `dist_eq_sub_of_le` and `monotoneOn_dist_basepoint`: for `t₀ ≤ s ≤ t`,
  `dist s t = dist t₀ t - dist t₀ s`, and `t ↦ dist t₀ t` is monotone on
  `Set.Ici t₀`. This is the step from which the embedding above follows. Both
  are proved (2026-09-06), and both need `AdditiveDist` alone: neither the order
  topology nor properness enters.
* `dist_eq_abs_sub_of_sameSide`: for `s` and `t` on one side of `t₀` — both
  above it or both below it — `dist s t = |dist t₀ t - dist t₀ s|`. This is the
  two sided form of the previous item, and it is the form the estimate of
  Milestone 3 consumes, where the two points compared are `t` and its image
  under a time change fixing `t₀`, so that only their common position relative
  to `t₀` is known. The hypothesis is necessary: on `ℝ` with `t₀ = 0`, `s = -1`
  and `t = 1` the left hand side is `2` and the right hand side is `0`. Proved
  (2026-09-07), again from `AdditiveDist` alone.
* `exhaustion`: fixing a base point `t₀`, the sets `B u = closedBall t₀ u` are
  compact — `isCompact_exhaustion`, proved on 2026-09-06 from
  `isCompact_closedBall`, which is `ProperSpace` alone —, increasing, cover the
  index, and each is a linear order with a least
  and a greatest element. Define the clamp
  `clamp m t = min (max t (B m).min) (B m).max` and prove it is monotone,
  continuous, idempotent, and the identity on `B m`. All of this is written and
  proved (2026-09-07): `mem_exhaustion_self`, `exhaustionMin` and
  `exhaustionMax` with their `isLeast`/`isGreatest` characterisations from
  `IsCompact.exists_isLeast` and `IsCompact.exists_isGreatest`
  (`Topology/Order/Compact.lean:148` and `:160`, both under the
  `Closed{Iic,Ici}Topology` that `OrderTopology` supplies), then `clamp`,
  `monotone_clamp`, `continuous_clamp`, `clamp_mem_exhaustion`,
  `clamp_eq_self` and `clamp_idem`.

  **The radius is a real number** (2026-09-08), because the metric of
  Milestone 4 integrates over it and a countable set of radii is not enough:
  `SkorokhodSpace.dist_exhaustionMax_le_distOn`. The definition is
  `closedBall t₀ (max u 0)` and not `closedBall t₀ u`, so that `exhaustionMin`,
  `exhaustionMax` and `clamp` stay total — a negative radius would empty the
  window and they are `def`s that need it inhabited. For `0 ≤ u` the two agree,
  which is `exhaustion_eq_closedBall`, and `0 ≤ u` is a hypothesis of exactly
  those statements that would otherwise be false at a negative radius:
  `TimeChange.dist_le_of_norm_le`, `exhaustion_subset_exhaustion` and
  `SkorokhodSpace.eq_of_distOn_eq_zero`.
* `monotone_exhaustionMax` and `antitone_exhaustionMin`: the window endpoints
  move monotonically with the radius. Proved (2026-09-08), and they are what
  makes `measurable_clamp` — the clamp is measurable in the radius, for each
  fixed point of the index — a two line consequence of `Monotone.measurable`.
  This is the only place where the index carries a measurable structure, and it
  is a hypothesis of those statements and not of the milestone.
* `rightIsolated ι = {t | IsOpen (Set.Iic t)}`, the points approached from the
  right by nothing, and `countable_rightIsolated`: **there are countably many
  of them.** Proved (2026-09-08), and the proof is intrinsic — it does not go
  through the embedding of the index into `ℝ`, which is
  `exists_orderIso_isometry_real`, proved later the same day and not used here.
  For a right isolated `t` the
  set `Set.Iic t` is open, so a countable basis has a member `v` with
  `t ∈ v ⊆ Set.Iic t`, and `v s = v t` forces `s ≤ t` and `t ≤ s` at once. The
  hypothesis is second countability, which the index has from `ProperSpace`.
* `exists_countable_ciSup_eq`: **one countable set computes the supremum of
  every right continuous real function on the index.** Proved (2026-09-08). It
  is a countable dense set together with `rightIsolated ι`, and the second
  summand is not decoration: on `ι = Set.Icc (0:ℝ) 1` the dense set
  `ℚ ∩ [0,1)` misses the point `1`, which is approached from the left only, and
  a right continuous function may exceed its supremum over that set there. The
  set does not depend on the function, which is the whole point — a
  supremum-approximating sequence would, and a different countable set for
  every window radius computes nothing. This is what discharges the
  measurability obligation of Milestone 4.
* `ordConnected_exhaustion`: the window is an order interval. This is the step
  the clamp actually needs — being between the least and the greatest element
  of a set does not put a point in the set unless the set is order convex — and
  it is `AdditiveDist` again: above the base point `monotoneOn_dist_basepoint`
  gives it, below the base point the additivity is read from the other end.
  Proved (2026-09-07). It needs neither the order topology nor properness.
* Independence of the base point: two base points give exhaustions each of which
  refines the other after finitely many steps.
  `exhaustion_subset_exhaustion : exhaustion t₀ u ⊆ exhaustion t₁ (u + dist t₀ t₁)`
  for `0 ≤ u`, proved (2026-09-08) from the triangle inequality alone, needing
  neither the order nor `AdditiveDist` nor properness. The ceiling that stood
  here while the radius was an integer is gone with the integer. This is the whole of what
  relates two base points; the subgroups `TimeChange.fixing t₀` of Milestone 3
  are a second anchoring and are not related by it.
* ```
  class BasePoint (α : Type*) where
    basePoint : α
  ```
  the index with a distinguished point, and the origin of the exhaustion.
  Written (2026-09-08), with `Real.instBasePoint : BasePoint ℝ := ⟨0⟩` and
  `BasePoint.ofMem : basePoint ∈ s → BasePoint s` for the other three running
  instances, which is a `def` and not an instance: `Set.Icc (1:ℝ) 2` is an index
  of this milestone and has no canonical origin.

  It is data, and the alternative — `[Nonempty ι]` with `Classical.arbitrary ι` —
  is rejected on a named ground. The metric of Milestone 4 is anchored at a
  point twice over, through `exhaustion t₀ m` and through `TimeChange.fixing t₀`,
  while the type `D ι E` carries none, so the parameterless instance has to read
  one off the index; `Classical.arbitrary` reads an opaque one. Under it
  `dist f g` on `D(ℝ, E)` cannot be identified with `totalDist 0 f g`, so not
  one of the acceptance examples of Milestones 4 to 7 — all of which name their
  base point, and all of which name `0` — can be stated, let alone checked. With
  `BasePoint` the identification is `SkorokhodSpace.dist_eq`, and it is `rfl`.

**Acceptance examples.**

* **The four running instances, computed.** On `ι = ℝ` with `t₀ = 0`,
  `B m = Set.Icc (-m) m`, `exhaustionMin = -m`, `exhaustionMax = m` and
  `clamp m = fun t ↦ min (max t (-m)) m`. On
  `ι = AddSubgroup.zmultiples (1 : ℝ)` with `t₀ = 0`, `B m` is the finite set
  `{-⌊m⌋, …, ⌊m⌋}` and `clamp` is the same formula; `isCompact_exhaustion` here
  is compactness of a finite set, so the milestone's exhaustion machinery must
  not silently assume an interval. On `ι = Set.Icc (0:ℝ) T` with `t₀ = 0`,
  `B m = Set.Icc 0 (min m T)` and `clamp m = id` as soon as `T ≤ m`, which is
  the degenerate case every later induction over `m` has to survive.
* **A metric that is not `AdditiveDist`.** Put `dist x y = min 1 |x - y|` on
  `ℝ`. This is a metric inducing the order topology, and it is not additive:
  `dist 0 3 = 1` while `dist 0 2 + dist 2 3 = 2`. `AdditiveDist.orderIso_isometry_real`
  fails on it for the same reason — a bounded metric admits no isometry onto an
  unbounded closed subset of `ℝ` — so the class is not decoration, and the
  embedding theorem is where it is spent.
* **`dist_eq_abs_sub_of_sameSide` needs its hypothesis.** On `ℝ` with `t₀ = 0`,
  `s = -1`, `t = 1`: the left hand side is `2` and
  `|dist 0 1 - dist 0 (-1)| = 0`. Any proof that drops the same-side clause is
  refuted here, and this is why Milestone 3 anchors its time changes at `t₀`.
* **A window that is not an interval of `ℝ`.** `ι = Set.Icc (0:ℝ) 1 ∪ {2}`, a
  closed subset of `ℝ` and hence an instance. With `t₀ = 0` and `m = 3/2`,
  `B m = Set.Icc 0 1`, so `exhaustionMax = 1` and `clamp (3/2) 2 = 1`. That the
  value lands in `B m` again is `ordConnected_exhaustion` and not the formula:
  on the three point order `{0 < 1 < 2}` with `dist 0 1 = 2`, `dist 1 2 = 1`,
  `dist 0 2 = 1` — a metric, `2 ≤ 1 + 1` — the ball `B 1` around `t₀ = 0` is
  `{0, 2}`, which is not order convex, and `clamp 1 1 = min (max 1 0) 2 = 1`
  leaves the window. That metric is not `AdditiveDist`, which is exactly the
  point: order convexity of the windows is a theorem about the class, not about
  `clamp`.

From Milestone 3 on, `ι` denotes an index with these instances and `E` a Polish
space with metric `r`. Milestones 2 and 8 are the exceptions and state their
own, weaker hypotheses item by item. In Milestone 2 the càdlàg predicate and
the jump theory are about functions, not about the space, and neither uses the
metric on `ι`. In Milestone 8 the completeness of `E` is used by the two points
that run Prokhorov backwards and by nothing else.

## Milestone 2: càdlàg functions

Milestone 1 fixes the index of the **space**, and this milestone does not need
it. The predicate, its connection to `Function.leftLim`, and the jump theory
live at three different strengths, and each item below names its own, so that a
later reader can tell which instances a statement actually consumes.

* **(A)** `[Preorder ι] [TopologicalSpace ι] [TopologicalSpace E]`. This is what
  `RemyDegenne/brownian-motion` uses for `IsCadlag`, and it carries the
  predicate together with all of its closure properties. It does **not** carry
  `Function.leftLim`, which is defined only for a `LinearOrder`.
* **(A′)** `[LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]`. This is the
  weakest bundle under which `Function.leftLim` and `Function.rightLim` exist and
  the root-namespace lemmas of `Mathlib/Topology/Order/LeftRightLim.lean` apply.
  It is what connects the structure `IsCadlag` to those two functions, and it
  needs no dense subset of `ι`.
* **(B)** `[LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]` together with
  a countable dense `D ⊆ ι` such that every non-maximal point is a limit of
  points of `D` from the right. This is the index bundle the manuscript calls
  (T2b), and it is what the jump theory consumes. Two of the items below add
  σ-compactness of `ι` on top of it, and say so.

(B) and the index of Milestone 1 are **incomparable**, and this is worth
recording once because a formalizer meets it immediately.
`AddSubgroup.zmultiples h` carries every instance of Milestone 1 and fails the
right approximation clause of (B), since `Set.Ioo t (t + h) = ∅`. Nothing is
lost: on a discrete linear order `𝓝[<] x` and `𝓝[>] x` are both `⊥`, so
`IsCadlag` holds for every function, `Function.leftLim f x = f x` by the
definition in `Mathlib/Topology/Order/LeftRightLim.lean`, `leftJumpSet f = ∅`,
and each of the statements below is trivially true. The other three running
instances `ℝ`, `Set.Ici (0:ℝ)` and `Set.Icc (0:ℝ) T` satisfy (B), with `D` the
rational points. So the two statements that really consume (B) --- the
measurability and the determination by a right dense set --- are to be proved
under it and instantiated for those three; the discrete index gets its own one
line instance and no exhaustion argument. The jump theory needs none of this and
stands under (A′), which the discrete index does satisfy: there the three
statements are true and not merely instantiable. The metric on `ι` is first used
in Milestone 3, and no
statement of this milestone uses it: `largeLeftJumpSet` measures with `dist` on
`E`.

Under (A), for `f : ι → E`:

* `Function.RightContinuous f`, defined as `∀ a, ContinuousWithinAt f (Set.Ioi a) a`.
* `IsCadlag f`, a structure with fields `right_continuous` and
  `left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)`.
* Basic closure properties: constants, compositions with continuous maps, sums
  and products in a topological ring, pointwise limits that are uniform on
  compacts, and the restriction of a càdlàg function to a subinterval.
* `IsCadlag` for a continuous map.

Under (A′):

* `IsCadlag.tendsto_leftLim`, `Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x))`,
  which is `tendsto_leftLim_of_tendsto` applied to the `left_limit` field, and
  `IsCadlag.rightLim_eq`, `Function.rightLim f x = f x`, which is
  `ContinuousWithinAt.rightLim_eq` applied to the `right_continuous` field
  through `continuousWithinAt_Ioi_iff_Ici`; the second adds `[T2Space E]`. These
  connect the structure to `Function.leftLim` and `Function.rightLim` so that
  the existing API applies; every later statement about left limits uses those
  names, not a new one. `IsCadlag.tendsto_leftLim` is proved (2026-09-07), and
  it is unconditional: `tendsto_leftLim_of_tendsto` covers the degenerate case
  `𝓝[<] x = ⊥` itself, so no hypothesis on the point is needed.
* The identity `Function.leftLim f x = f x` at continuity points, from
  `ContinuousWithinAt.leftLim_eq` applied to the restriction of continuity at
  `x` to `Iic x`, with `[T2Space E]`.
* `IsCadlag.comp_monotone_continuous`: `f ∘ g` is càdlàg for càdlàg `f` and
  monotone continuous `g : ι → ι`. This is what puts
  `SkorokhodSpace.restrictExhaustion` of Milestone 4 back into the space, `clamp`
  being monotone and continuous. Proved (2026-09-07). Both fields use the
  monotonicity, and differently. On the right, `g` maps `Set.Ioi a` into
  `Set.Ici (g a)`, which is where the right continuity of `f` is read, through
  `continuousWithinAt_Ioi_iff_Ici`. On the left the proof splits: either `g` is
  already constant to the left of `x`, and then so is `f ∘ g` on the whole
  interval between the two equal values, or `g y < g x` for every `y < x`, and
  then `g` tends to `g x` from strictly below, so the left limit of `f` at `g x`
  is the left limit of `f ∘ g` at `x`. The first branch is the only place in
  this milestone that uses the order topology, through `Ioo_mem_nhdsLT`.
* `IsCadlag.isBounded_image_of_isCompact`: the image of a compact set under a
  càdlàg map into a pseudometric space is bounded. Proved (2026-09-07), and the
  proof is where the bundle of this item was found to be wrong. It needs the
  **linear** order and nothing else of (A′) --- not the order topology ---
  because it splits a neighbourhood of a point into its two one sided halves by
  `nhdsLT_sup_nhdsGE`, `𝓝[<] x ⊔ 𝓝[≥] x = 𝓝 x`, which is `Iio x ∪ Ici x = univ`
  and holds under `[TopologicalSpace ι] [LinearOrder ι]` alone; the two fields
  of `IsCadlag` then bound `f` on each half.

  Under (A) the statement is **false**, so this item cannot stay there. Take
  `ι = ℕ ∪ {ω}` with the one point compactification of the discrete topology on
  `ℕ`, ordered so that `ℕ` carries its usual order and `ω` is incomparable to
  everything. Every point of `ℕ` is isolated and `Set.Iio ω = Set.Ioi ω = ∅`, so
  `𝓝[<] x` and `𝓝[>] x` are `⊥` at every `x` and **every** `f : ι → ℝ` is
  càdlàg; `ι` is compact; and `f n = n` has unbounded image. What fails is
  exactly the split above: `ω` has neighbourhoods containing cofinitely much of
  `ℕ`, and neither field of `IsCadlag` says anything there.

Still under (A′), with `E` a pseudometric space --- the jump theory does **not**
need (B), and this is a correction of 2026-09-07, found by writing the proofs:

* Jump sets: `leftJumpSet f = {x | f⁻ x ≠ f x}` and, for `ε > 0`,
  `largeLeftJumpSet f ε = {x | ε ≤ dist (f⁻ x) (f x)}`. That
  `largeLeftJumpSet f ε` has no accumulation point, hence meets every compact
  set in a finite set, is (A′) alone. Proved (2026-09-07) in the pointwise form
  `IsCadlag.eventually_dist_leftLim_lt`, which is the sharp one: *every* point
  `x` of the index --- not only a point outside the set --- has a neighbourhood
  on which `x` itself is the only possible jump of size `ε`. The point itself
  cannot be excluded, since a càdlàg function may jump at any single point, and
  it need not be, because a set that meets a neighbourhood of each point of the
  index in at most one point already meets every compact set in a finite set:
  that is `IsCadlag.finite_largeLeftJumpSet_inter`, through
  `IsCompact.elim_nhds_subcover`.

  The proof is two sided and needs one statement the roadmap did not name,
  `IsCadlag.dist_leftLim_le_of_Ioo_subset`: if `f` stays `r`-close to a point
  `c` of `E` on `Set.Ioo a y` and at `y`, its jump at `y` is at most `2r`. It is
  applied twice --- to the left of `x` with `c` the left limit there, to the
  right with `c` the value there --- and the two intervals come from
  `mem_nhdsLT_iff_exists_Ioo_subset'` and `mem_nhdsGE_iff_exists_Ico_subset'`,
  which is where the order topology enters; `nhdsLT_sup_nhdsGE` glues the two
  halves. The degenerate cases carry no content: where `𝓝[<] y = ⊥` the left
  limit *is* the value, by `leftLim_eq_of_eq_bot`, so there is no jump there.
* The characterization of continuity of a càdlàg map as `leftJumpSet f = ∅`.
  Proved (2026-09-07) as `IsCadlag.continuousAt_iff_notMem_leftJumpSet`, with
  the global form `IsCadlag.continuous_iff_leftJumpSet_eq_empty`. Forwards it is
  `ContinuousWithinAt.leftLim_eq` on the restriction of continuity to
  `Set.Iic x`; backwards `IsCadlag.tendsto_leftLim` rewritten along `f⁻ x = f x`
  gives convergence along `𝓝[<] x`, which together with the `right_continuous`
  field and `nhdsLT_sup_nhdsGE` is continuity at `x`.
* `leftJumpSet f` is countable. This adds **σ-compactness of `ι`** to (A′), to
  turn local finiteness into countability along a countable exhaustion; every
  index of Milestone 1 has it, since closed balls are compact. Proved
  (2026-09-07) as `countable_leftJumpSet`, decomposing over the jump size into
  the sets `largeLeftJumpSet f (1 / (n + 1))`. The monotone case
  is `Monotone.countable_not_continuousAt`, which lives in
  `Mathlib/Topology/Order/Monotone.lean` and not in
  `Mathlib/Topology/Order/LeftRightLim.lean`, where only the module comment
  names it; the càdlàg case does not follow from it.

* `IsCadlag.measurable`: a càdlàg map is Borel measurable. Proved (2026-09-07),
  and the bundle of this item is a second correction of the same day: it stood
  under (B) with `E` Polish, to be proved by approximation with right continuous
  step functions along `D`, and it needs neither. Continuity off the jump set is
  `IsCadlag.continuousAt_iff_notMem_leftJumpSet`, the jump set is countable by
  `countable_leftJumpSet`, and a map continuous off a countable set is
  measurable by `measurable_of_countable_not_continuousAt`
  (`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:509`); its
  `MeasurableSingletonClass ι` is free from `T1Space` through
  `OpensMeasurableSpace.toMeasurableSingletonClass` (`ibid.:351`). So the
  hypotheses are those of `countable_leftJumpSet` --- the linear order, the
  order topology, σ-compactness --- plus the Borel structures on index and
  state. The step function route would have needed a linear structure on `E`
  that the milestone nowhere else asks for.

  None of these four items uses the countable dense set of (B) or its right
  approximation clause. They stood under (B) from 2026-08-29 to 2026-09-07, and
  the proofs do not bear that out. What (B) is genuinely for is one of the two
  items below, `IsCadlag.eq_of_eqOn_dense`; the other,
  `IsCadlag.eq_of_forall_exists_dist_le`, is again (A′) and is listed there only
  because Milestone 4 consumes it next to it.

Under (B), with `E` a pseudometric space:

* `IsCadlag.eq_of_forall_exists_dist_le`, still under (A′) and stated here
  because it is a statement about càdlàg maps and nothing else: two of them
  agree at `t` as soon as, arbitrarily close to `t` and **on its right**, one of
  them may be evaluated against the other's value at `t` with arbitrarily small
  error --- formally, for all `ρ, η > 0` there is an `s ≥ t` with
  `dist s t < ρ` and `dist (F s) (G t) ≤ η` or `dist (F t) (G s) ≤ η`. Proved
  (2026-09-07); it uses the two `right_continuous` fields and nothing else, not
  even the order topology. The disjunction is not a weakening for convenience:
  it is exactly what the separation of `SkorokhodSpace.distOn` in Milestone 4
  delivers, and it is what lets that separation avoid the density of the
  continuity points, which an index of Milestone 1 need not provide.
* `IsCadlag.eq_of_eqOn_dense`: a càdlàg map is determined by its restriction to
  a set that is dense **from the right**. The hypothesis is, for every `t ∈ ι`,
  that either `t ∈ D` or `(𝓝[D ∩ Set.Ioi t] t).NeBot`, and it implies `Dense D`.
  This is right continuity together with the clause of (B) that every
  non-maximal point is approximable from the right, and it is the sharpest use
  of that clause anywhere in this roadmap. This is the statement Milestone 6
  turns into a measurable embedding. Proved, and it needs neither the order
  topology nor `AdditiveDist` nor properness.

  Bare density is not enough, and (B) is not enough either; both gaps were found
  by writing the proof, on 2026-09-06. Under bare density the point `1` of
  `ι = [0,1] ∪ {2}` — allowed by Milestone 1, which pins `ι` down to a closed
  subset of `ℝ` and not to an interval — is right isolated without being
  isolated, so `D = ([0,1) ∩ ℚ) ∪ {2}` is dense while `f = 0` and
  `g = ` the indicator of `{1}` are both càdlàg, agree on `D` and differ at `1`.
  Under (B) that example is excluded, but a **maximal** point is not: on
  `ι = [0,1]` with `D = [0,1) ∩ ℚ`, right continuity at `1` is vacuous because
  `𝓝[>] 1 = ⊥`, and the same two functions separate. A maximal element must lie
  in `D`, which is what the disjunction above says and what Billingsley requires
  of the dense set in `D[0,1]`.
* `IsCadlag.of_tendstoUniformly`: the uniform limit of càdlàg paths is càdlàg,
  under `[CompleteSpace E]`. Proved (2026-09-08). It is the step at which
  `CompleteSpace (D ι E)` of Milestone 5 produces its limit path: the composed
  time changes give a sequence converging uniformly on each window, and that its
  limit lies in `D ι E` and not merely in the bounded functions is this
  statement. Both clauses come from Mathlib's
  `TendstoUniformly.tendsto_of_eventually_tendsto`
  (`Topology/UniformSpace/UniformConvergence.lean:625`) — right continuity along
  `𝓝[>] a` with the values `F n a`, the left limits along `𝓝[<] x` with the left
  limits `Function.leftLim (F n) x`. The two differ in one place, and it is
  where the completeness of `E` is spent: the values converge because the
  uniform limit exists pointwise, the left limits have to be shown Cauchy first,
  from the uniform estimate read through `Filter.Tendsto.dist` and
  `le_of_tendsto`. The degenerate filter `𝓝[<] x = ⊥` is a separate branch with
  an arbitrary witness. The proof uses neither `AdditiveDist` nor `ProperSpace`,
  and nothing of bundle (B).
* `IsCadlag.of_forall_eventuallyEq`: **being càdlàg is local.** A function that
  agrees on a neighbourhood of every point with *some* càdlàg function is càdlàg.
  Proved (2026-09-08), and the whole content is `Filter.Tendsto.congr'`: both
  clauses of `IsCadlag` speak of `𝓝[>] a` and `𝓝[<] x`, and both filters lie
  below `𝓝` of their point. It uses neither the order topology, nor
  `AdditiveDist`, nor `ProperSpace`.
* `IsCadlag.of_tendstoUniformlyOn_exhaustion`: uniform convergence **on every
  window** is enough — if every `F n` is càdlàg and `F n → f` uniformly on
  `exhaustion t₀ m` for every `m`, then `f` is càdlàg. Proved (2026-09-08). The
  passage is the clamp: `F n ∘ clamp t₀ m` converges uniformly on all of `ι`,
  because `clamp` lands in the window, so `of_tendstoUniformly` applies to it;
  and `f` agrees with `f ∘ clamp t₀ m` on the window, which is a neighbourhood of
  each of its interior points, so `of_forall_eventuallyEq` assembles the two.
  This is what Milestone 5 actually consumes, since its estimate is windowed and
  never global.
* `IsCadlag.exists_subdivision`: **the structure theorem, and the rung
  Milestones 5 and 7 share.** For `f` càdlàg, `a ≤ b`, `Set.Icc a b` compact and
  `ε > 0` there are `n` and a strictly monotone `t : Fin (n+1) → ι` from `a` to
  `b` with `dist (f x) (f (t i.castSucc)) ≤ ε` for every `x` in every cell
  `Set.Ico (t i.castSucc) (t i.succ)`. Proved (2026-09-08). The proof is a least
  upper bound argument and **not** an induction, because the cells cannot be
  chosen in advance: their lengths are dictated by the jumps of `f` and may
  shrink to `0`. Let `S` be the set of endpoints reachable by such a subdivision
  and `c` the greatest point of `closure S`; the left limit at `c` puts `c` in
  `S` and right continuity at `c` would push past it if `c < b`. Compactness of
  the window is a **hypothesis** and not `ProperSpace ι`, so the statement also
  serves an index whose closed balls are not compact; `AdditiveDist` and the
  metric of the index do not enter. `exists_snoc_subdivision` is the one
  combinatorial step, `Fin.snoc`, with no càdlàg hypothesis and no topology.
* `stepRetract t`, the retraction of the index onto the range of a finite tuple
  — every point goes to the greatest entry below it, and to `t 0` if there is
  none — with `stepRetract_eq_of_forall_le`, `stepRetract_eq_first` and
  `stepRetract_mem_range`. Written and proved (2026-09-08). The step path of
  Milestone 5 is `f ∘ stepRetract t`, built as a composition rather than a case
  distinction so that the càdlàg proof is one lemma about the retraction alone.
* `IsCadlag.of_eventually_const`: a map constant on a right neighbourhood of
  every point and on a left neighbourhood of every point is càdlàg. Proved
  (2026-09-08). The degenerate cases need no separate treatment: at a greatest
  element `𝓝[>] x = ⊥` and at a least one `𝓝[<] x = ⊥`.
* `eventually_stepRetract_eq_nhdsGT` and
  `exists_eventually_stepRetract_eq_nhdsLT`: the retraction is locally constant,
  to the right and to the left. Proved (2026-09-08), through the greatest index
  with `t i ≤ x` and the greatest with `t i < x` respectively.
* `isCadlag_comp_stepRetract`: **the step path is càdlàg, and the path it is
  read off need not be.** Proved (2026-09-08). It rests on the local constancy
  of the retraction alone, which is why the hypothesis is absent rather than
  unused.
* `finite_range_comp_stepRetract`: the step path takes finitely many values.
  Proved (2026-09-08). This is what the counting of Milestone 5 needs, and it is
  the only reason the retraction runs over a `Finset`.
* `dist_comp_stepRetract_le`: on `Set.Icc (t 0) (t (Fin.last n))` the step path
  is uniformly `ε`-close to its path when the cells carry `ε`. Proved
  (2026-09-08), and the tuple need **not** be strictly monotone: the retraction
  reads the greatest index out of a `Finset`, so a repeated entry changes which
  value is taken but not that it is taken inside a cell of the hypothesis.

**Acceptance examples.**

* **The single step, and its mirror image.** `ι = ℝ`, `E = ℝ`,
  `f = Set.indicator (Set.Ici 1) 1`. Then `IsCadlag f`,
  `Function.leftLim f 1 = 0 ≠ 1 = f 1`, `leftJumpSet f = {1}`, and
  `largeLeftJumpSet f ε = {1}` for `ε ≤ 1` and `∅` beyond. The mirror
  `g = Set.indicator (Set.Iic 1) 1` must **not** satisfy `IsCadlag`: it is left
  continuous with right limits. A predicate that swapped `Set.Ioi` for
  `Set.Iio` in `Function.RightContinuous`, or that asked for right limits
  instead of left ones, accepts `g` and rejects `f`, so this pair pins the
  orientation of the whole milestone.
* **Jumps accumulating from the right.** `ι = ℝ`, `E = ℝ`,
  `f = ∑' n, 2⁻¹ ^ n * Set.indicator (Set.Ici (1 / (n + 1))) 1`. This is càdlàg,
  including at `0`, where the left limit is `0` and right continuity holds
  because the tail mass beyond `1/(n+1)` is `2⁻¹ ^ n`. Its `leftJumpSet` is
  infinite and **has** the accumulation point `0`, while each
  `largeLeftJumpSet f ε` is finite. So `countable_leftJumpSet` cannot be proved
  by showing that `leftJumpSet` has no accumulation point; the decomposition
  over `ε` is not a convenience. This is also the path on which
  `tendsto_modulus` of Milestone 7 is not a statement about finitely many jumps.
* **The discrete index, where everything is trivially true.**
  `ι = AddSubgroup.zmultiples (1 : ℝ)`. Every `f : ι → E` is càdlàg,
  `Function.leftLim f x = f x`, `leftJumpSet f = ∅`, and both statements under
  (B) hold vacuously. The acceptance test is that the instantiation goes through
  without an exhaustion argument, since (B) itself fails here —
  `Set.Ioo t (t+1) = ∅`. The three jump statements are not vacuous here but
  simply true, since they stand under (A′), which this index does satisfy.
* **The two witnesses already in the text, as tests of the bundles.**
  `ι = ℕ ∪ {ω}` with `ω` incomparable refutes
  `IsCadlag.isBounded_image_of_isCompact` under (A), so an implementer who
  states that item under `[Preorder ι]` fails on it; and the pair `f = 0`,
  `g = Set.indicator {1} 1` on `ι = Set.Icc (0:ℝ) 1` with
  `D = Set.Ico (0:ℝ) 1 ∩ ℚ` refutes `IsCadlag.eq_of_eqOn_dense` when the maximal
  point is left out of `D`.

## Milestone 3: time changes

* `TimeChange ι`, the type of bi-Lipschitz order isomorphisms `λ : ι ≃o ι`.
  Give it a group structure. Done on 2026-09-06: multiplication is composition
  of functions, `l * l' = l ∘ l'`, the unit is `OrderIso.refl` and the inverse
  is `OrderIso.symm`; the two Lipschitz fields close under it through
  `LipschitzWith.comp` and `OrderIso.symm_trans`, and the axioms are
  `TimeChange.ext rfl` — the extensionality lemma holds because the other two
  fields of the structure are propositions.
* `TimeChange.exists_of_lengthCoord`, **proved 2026-09-08**: time changes are
  built in the coordinate of Milestone 1. A strictly monotone `φ : ℝ → ℝ` with
  `φ 0 = 0`, bi-Lipschitz with the two constants `exp γ`, and mapping the range
  of `lengthCoord t₀` **onto itself**, yields a time change fixing `t₀`, of norm
  at most `γ`, whose coordinate is `φ`. Until it was written nothing in the file
  constructed a time change on a general index: `TimeChange.steep` and
  `TimeChange.double` are written on `ℝ`. The two surjectivity hypotheses are
  the obstruction and not an artefact of the statement, and this is what they
  say: for `ι = h • ℤ` the range of the coordinate is `h • ℤ` and the only
  admissible `φ` is the identity, so that index has no time change but the
  trivial one. Every construction of a time change on a general index is
  therefore a statement about the range of the coordinate, and the lemma is the
  place where that becomes visible.
* `TimeChange.lipConst λ = sInf {K : ℝ≥0 | LipschitzWith K λ}`, the least
  Lipschitz constant, and `TimeChange.norm λ = log (max (lipConst λ) (lipConst λ⁻¹))`,
  with `TimeChange.lipConstOn m λ` and `TimeChange.normOn m λ` the same computed
  on `B m` through `LipschitzOnWith`. Mathlib carries no least Lipschitz
  constant: `LipschitzWith (K : ℝ≥0) (f : α → β)` in
  `Mathlib/Topology/EMetricSpace/Lipschitz.lean` is a `Prop`, and
  `LipschitzWith.const` there is the theorem that a constant map is `0`-Lipschitz,
  not a constant attached to a map. `lipConst` is therefore part of this
  milestone, together with `LipschitzWith (lipConst λ) λ`: the infimum is
  attained because `ι` is a metric space, so `edist s t ≠ ∞`, and the inequality
  `edist (λ s) (λ t) ≤ K * edist s t` passes to the infimum over `K` in
  `ℝ≥0∞`. With it `lipConst_one`, `lipConst_le_iff` and the submultiplicativity
  `lipConst (λ * μ) ≤ lipConst λ * lipConst μ` from `LipschitzWith.comp`. All of
  this is proved (2026-09-07): `lipschitzWith_lipConst` is the attainment, over
  `ENNReal.div_le_iff_le_mul` and `le_csInf`; `lipConst_one` needs
  `[Nontrivial ι]` and is `1`, and `lipConst_of_subsingleton` is the other case,
  where every constant is admissible and the least one is `0`;
  `lipConst_mul_le` is `csInf_le'` applied to `LipschitzWith.comp` of the two
  attained constants, through `OrderIso.coe_trans`.
* `TimeChange.norm_one`, `TimeChange.norm_inv` (`norm λ⁻¹ = norm λ`) and
  `TimeChange.norm_mul_le` (`norm (λ * μ) ≤ norm λ + norm μ`): the norm is a
  length function. All three are proved (2026-09-07). `norm_inv` is `inv_inv`
  and `max_comm`; `norm_one` and `norm_mul_le` split on
  `subsingleton_or_nontrivial ι`, because on a subsingleton index every constant
  is admissible, every `lipConst` is `0`, and it is the junk value
  `Real.log 0 = 0` that carries the statement. On a nontrivial index the step
  that makes the logarithm well behaved is `one_le_max_lipConst`,
  `1 ≤ max (lipConst λ) (lipConst λ⁻¹)`: the two constants multiply to at least
  `lipConst 1 = 1`, hence so does the square of their maximum. The same step
  gives `TimeChange.norm_nonneg`, `0 ≤ norm λ`, also proved, which is what makes
  the `max` in the `distOn` of Milestone 4 the intended quantity.
* **The windowed norm is not a length function**, and `normOn_mul_le` is
  therefore *not* part of this milestone: it is false. `not_normOn_mul_le`
  states the refutation. On `ι = ℝ` with `t₀ = 0` and `m = 1`, so `B 1 = [-1,1]`,
  take `λ' = (2 • ·)` and let `λ` be the piecewise linear order isomorphism that
  is the identity on `Iic 1` and has slope `100` on `Ici 1`. Then `λ` and `λ⁻¹`
  are the identity on `B 1`, so `normOn 0 1 λ = 0`, and `normOn 0 1 λ' = log 2`;
  but `(λ * λ') x = λ (2 * x)` carries `1/2` to `1` and `1` to `101`, so
  `normOn 0 1 (λ * λ') ≥ log 200`. The reason is structural and not an artefact
  of the example: the inner factor of a composite need not map the window into
  itself, and outside the window the outer factor is unconstrained, so the
  failure can be made arbitrarily large. Milestone 4 therefore measures time
  changes with the **global** `norm`, exactly as Billingsley does — his `d°ₘ`
  truncates the *paths* to the window and leaves the time change untruncated.
  Proved (2026-09-07), so the choice Milestone 4 makes rests on a theorem. The
  two witnesses are part of this milestone: `TimeChange.steep`, the piecewise
  linear map above, written as `x ↦ max x (100 * x - 99)` with inverse
  `y ↦ min y ((y + 99) / 100)`, and `TimeChange.double`, `x ↦ 2 * x` with
  inverse `y ↦ y / 2`. Writing them as a `max` resp. a `min` of two affine maps
  rather than with an `if` is what makes them cheap: `max_lt_max` gives strict
  monotonicity, `LipschitzWith.max` and `LipschitzWith.min` the two Lipschitz
  bounds, and the inverse is again of the same shape, so
  `StrictMono.orderIsoOfRightInverse` applies with no case analysis beyond the
  single `rcases le_total y 1` of the right inverse identity. The three
  estimates are stated separately — `normOn_steep_le`, `normOn_double_le`,
  `le_normOn_steep_mul_double` — and only the last needs the infimum from below,
  through `le_csInf` on the two points `1/2` and `1` of the window.
  What survives of the windowed norm is `normOn_inv` and `normOn_one`, both
  proved (2026-09-06 and 2026-09-07); `normOn_one` holds for two reasons and
  needs the case distinction: if `B m` has two distinct points the set of
  admissible constants of the identity is `Set.Ici 1`, so `lipConstOn = 1` and
  `log 1 = 0`; if `B m` is a single point — `m = 0` in a discrete index — every
  constant is admissible, `lipConstOn = 0`, and it is again the junk value
  `Real.log 0 = 0` that carries the statement.
* `TimeChange.dist_le_of_norm_le`: for a time change **fixing the base point**,
  `λ t₀ = t₀`, and `t ∈ B m`, `norm λ ≤ γ` implies
  `dist (λ t) t ≤ (exp γ - 1) * (2 * m)`, so a time change of small norm moves
  points of `B m` little. This is the estimate that makes the metric of
  Milestone 4 separate points. The anchor `λ t₀ = t₀` is not decoration: without
  it the statement is false, because a translation of `ℝ` is an order
  isomorphism with `lipConst = 1` in both directions, hence of norm `0`, and it
  moves every point by the same arbitrary amount, while the bound at `γ = 0` is
  `0`. Billingsley gets the anchor for free — his `Λ` consists of the increasing
  homeomorphisms of `[0,∞)` onto itself and they all fix `0` — and on a two
  sided index it has to be imposed. The time changes fixing `t₀` form a
  subgroup, so `norm_one`, `norm_inv` and `norm_mul_le` restrict to it unchanged.
  Proved (2026-09-07). The anchor and the order isomorphism put `t` and `λ t` on
  one side of `t₀`, so `dist_eq_abs_sub_of_sameSide` of Milestone 1 turns the
  left hand side into `|dist t₀ (λ t) - dist t₀ t|`; `lipschitzWith_lipConst`,
  applied to `λ` and to `λ⁻¹` and read through `log (max …) ≤ γ`, squeezes
  `dist t₀ (λ t)` between `e^{-γ}` and `e^{γ}` times `dist t₀ t`, and
  `dist t₀ t ≤ m` closes it. The bound obtained is `(exp γ - 1) * m`, half of
  what is claimed. The statement needs neither `OrderTopology` nor
  `ProperSpace`, and in particular not the compactness of `B m`: the window
  enters only through `dist t₀ t ≤ m`. It is the first statement of this
  milestone that uses `AdditiveDist` at all, and so the first check that
  Milestone 1 carries the right class.
* `TimeChange.fixing t₀`, the time changes with `λ t₀ = t₀`, as a
  `Subgroup (TimeChange ι)`. This is the index of the infimum of Milestone 4,
  and it is a subgroup precisely so that `norm_one`, `norm_inv` and
  `norm_mul_le` restrict to it unchanged --- the three metric axioms are read
  off them there. Written and proved (2026-09-07), with
  `TimeChange.mem_fixing_iff` as its `Iff.rfl` interface.
* For the index `ℝ`, the identification of `norm` with Billingsley's
  `sup_{s < t} |log ((λ t - λ s) / (t - s))|`.

**Acceptance examples.**

* **The dilations of `ℝ`, computed.** For `c > 0` and `λ = (c • ·)` one has
  `lipConst λ = c`, `lipConst λ⁻¹ = c⁻¹` and hence
  `TimeChange.norm λ = |Real.log c|`. In particular `norm double = Real.log 2`,
  `norm 1 = 0`, and `norm λ⁻¹ = norm λ` is `|log c⁻¹| = |log c|`. The dilations
  form a one parameter subgroup on which `norm_mul_le` is an equality, so they
  are the instance on which the length function can be read off in closed form
  and compared with Billingsley's `sup_{s<t} |log ((λ t - λ s)/(t - s))|`.
* **`steep * double` on `B 1`**, which is `not_normOn_mul_le` run as a
  computation: `normOn 0 1 steep = 0` and `normOn 0 1 double = Real.log 2`,
  while `normOn 0 1 (steep * double) ≥ Real.log 200`. A `distOn` built on
  `normOn` therefore has no triangle inequality, and Milestone 4 must use the
  global `norm`. The witnesses are `TimeChange.steep = fun x ↦ max x (100*x-99)`
  and `TimeChange.double = fun x ↦ 2 * x`.
* **The translations, which is why `fixing t₀` exists.** On `ι = ℝ`,
  `λ = (· + a)` is an order isomorphism with `lipConst λ = lipConst λ⁻¹ = 1`,
  hence `norm λ = 0`, and it moves every point by `|a|`. So
  `dist_le_of_norm_le` is false without the anchor `λ t₀ = t₀`, at `γ = 0`
  already, and the metric of Milestone 4 would not separate points. On
  `ι = Set.Ici (0:ℝ)` there are no translations, which is why Billingsley never
  meets this.
* **A subsingleton index.** `ι = Set.Icc (0:ℝ) 0`. Every constant is an
  admissible Lipschitz constant, so `lipConst λ = 0` for the only time change
  and `norm λ = Real.log 0 = 0` by the junk value. `norm_one`, `norm_mul_le` and
  `normOn_one` must all still hold here, which is why each of them splits on
  `subsingleton_or_nontrivial ι`. A proof that argues `1 ≤ lipConst` outright is
  wrong on this index.

## Milestone 4: the space and its metric

* `SkorokhodSpace ι E`, notation `D ι E`, the type of càdlàg maps `ι → E`,
  as a structure bundling `toFun` with `isCadlag`.
* `SkorokhodSpace.restrictExhaustion t₀ m f = f ∘ clamp t₀ m`, a path constant
  outside `B m`. Written and proved to be càdlàg again (2026-09-07), from
  `IsCadlag.comp_monotone_continuous` of Milestone 2 on `monotone_clamp` and
  `continuous_clamp` of Milestone 1, with `restrictExhaustion_apply` and
  `restrictExhaustion_eq_self` --- it agrees with `f` on `B m` --- as its
  interface.
* The localized distances
  ```
  distOn u f g = ⨅ λ, max (TimeChange.norm λ)
                          (⨆ t, r (restrictExhaustion u f (λ t)) (restrictExhaustion u g t))
  dist f g     = ⨅ λ, max (TimeChange.norm λ)
                          (∫ u in Ioi 0, Real.exp (-u) *
                             min 1 (⨆ t, r (restrictExhaustion u f (λ t))
                                            (restrictExhaustion u g t)))
  ```
  **The window radius `u` is a real number and the metric integrates over it.**
  It is Ethier–Kurtz's `d(x, y, λ, u)` and their `d`, and the reason it is not a
  weighted sum over integer radii is a theorem of 2026-09-08:
  `SkorokhodSpace.dist_exhaustionMax_le_distOn` says that
  `r (f b) (g b) ≤ distOn u f g` for `b = exhaustionMax t₀ u`, for **every**
  admissible time change, because a `t` beyond both `b` and `λ⁻¹ b` has
  `clamp u t = clamp u (λ t) = b`, so the supremum contains that number and the
  infimum cannot get below it. A sum over a fixed countable set of radii
  therefore forces pointwise convergence at every window endpoint, which the `J₁`
  topology does not have, and with it the space is not complete: the first
  acceptance example below is the witness. The integral does not see the
  endpoints, because the radii at which a given pair of paths jumps are countably
  many and hence Lebesgue null. Billingsley's alternative, a continuous ramp in
  place of the clamp, is not available here — it multiplies path values by
  scalars, and `E` is a metric space with no linear structure.

  The obligation this shape adds, and it is the only one: for fixed `f`, `g` and
  `λ` the integrand `u ↦ ⨆ t, r (f (clamp u (λ t))) (g (clamp u t))` is Borel
  measurable. This is why the infimum over `λ` stands **outside** the integral and
  not inside it, as it does in `distOn`: outside, measurability is needed for one
  time change at a time; inside, the integrand would be an infimum over an
  uncountable family.

  The obligation is discharged (2026-09-08). `SkorokhodSpace.distWith t₀ u λ f g`
  is that supremum, `SkorokhodSpace.distOn_eq_iInf_distWith` says `distOn` is the
  infimum of `max ‖λ‖ ·` over it — by `rfl` — and
  `SkorokhodSpace.measurable_distWith` is the measurability. It runs on three
  proved items: `SkorokhodSpace.rightContinuous_dist_restrictExhaustion`, that
  the integrand is right continuous in the index; `exists_countable_ciSup_eq` of
  Milestone 1, which turns that supremum into a supremum over a countable set
  fixed once and for all; and `measurable_clamp`, that the clamp is measurable
  in the radius. **A countable dense subset of `ι` does not suffice** and the
  earlier wording of this bullet was wrong about that: a right continuous
  function may exceed its supremum over a dense set at a point approached from
  the left only, and what has to be added is `rightIsolated ι`, which
  `countable_rightIsolated` shows to be countable.

  `SkorokhodSpace.intDist` is the metric itself, and
  `SkorokhodSpace.integrableOn_intDist` says its integrand is integrable on
  `Set.Ioi 0`: measurable by the above and dominated by `exp (-u)`, which is
  `integrableOn_exp_neg_Ioi`. Without it the integral would be the junk value
  `0` and `intDist` would collapse to `⨅ λ, ‖λ‖ = 0`.

  **The four metric axioms of `intDist` are theorems (2026-09-08), and
  `SkorokhodSpace.metricSpaceInt (t₀ : ι) : MetricSpace D(ι, E)` is built from
  them.** Each of the three algebraic ones is one statement about
  `TimeChange.norm`, proved in Milestone 3, and one about `intWith` --- where
  `SkorokhodSpace.intWith t₀ λ f g` is the integral for a single time change,
  split off from `intDist` for exactly this purpose --- and each statement about
  `intWith` is the corresponding statement about `distWith`, held at a fixed
  radius and then integrated: `SkorokhodSpace.distWith_self` gives
  `intWith_self` gives `intDist_self`; `SkorokhodSpace.distWith_inv`, the
  reindexing of the supremum along `λ` itself, gives `intWith_inv` gives
  `intDist_comm`; `SkorokhodSpace.distWith_triangle`, with `λ * λ'` as the
  composite, gives `intWith_triangle` gives `intDist_triangle`. The triangle
  inequality is the one place where `SkorokhodSpace.integrableOn_intDist` is
  spent, and it is spent twice, for `MeasureTheory.integral_add` and for
  `MeasureTheory.integral_mono`; without integrability the integral is the junk
  value `0`, and a junk *left* summand would make the inequality false.

  **The separation is not of that shape, and this is the one point at which the
  integral costs something the sum did not.** `SkorokhodSpace.eq_of_intDist_eq_zero`
  cannot name a radius: an infimum equal to `0` produces a *sequence* `λ n` of
  time changes, and no radius at which a given `λ n` is good.  What it produces
  instead is `‖λ n‖ < 2⁻ⁿ` together with `intWith t₀ (λ n) f g < 2⁻ⁿ`, whence
  `MeasureTheory.lintegral_tsum` and a geometric series make
  `∑' n, ENNReal.ofReal (exp (-u) * min 1 (distWith t₀ u (λ n) f g))` integrable
  over `Set.Ioi 0`, hence finite at almost every radius, hence with terms tending
  to `0` at almost every radius. At each such radius
  `SkorokhodSpace.eq_restrictExhaustion_of_forall_exists` applies, and a set of
  full measure in `Set.Ioi 0` reaches beyond every point of the index, so the two
  paths agree everywhere. `eq_restrictExhaustion_of_forall_exists` is the
  separation criterion at a **fixed** radius, factored out of
  `SkorokhodSpace.eq_of_distOn_eq_zero`, which now derives its hypothesis by
  unwinding its own infimum; both metrics read the same criterion.

  `[SecondCountableTopology E]` is the whole price of the integral shape, and it
  is charged on `intWith_triangle`, `intDist_triangle`, `eq_of_intDist_eq_zero`
  and `metricSpaceInt` and nowhere else: it is the hypothesis of
  `Measurable.dist`, and no choice of σ-algebra supplies it. The Borel
  structures of `ι` and of `E` are **not** hypotheses.
  `SkorokhodSpace.measurable_distWith` and `SkorokhodSpace.integrableOn_intDist`
  are statements about functions `ℝ → ℝ`, so they introduce `borel ι` and
  `borel E` in their proofs instead of assuming them, and the metric of
  Milestone 4 therefore carries no measure theory in its signature.

  **`SkorokhodSpace.instMetricSpace` is `metricSpaceInt (basePoint : ι)`**
  (2026-09-08). The move was a statement about the refutation of Milestone 5 and
  not a rename: `SkorokhodSpace.continuous_eval_exhaustionMax` and
  `SkorokhodSpace.exists_jump_continuousAt_eval` used to be stated for the
  topology of the *instance* and are theorems about the **summed** metric — the
  first is false for `intDist`, which is the entire point of replacing the sum.
  They therefore name their topology, and the name is
  `SkorokhodSpace.totalTopology t₀`, the topology of `SkorokhodSpace.metricSpace
  t₀`; the summed metric is kept for exactly that reason and for no other.
  `SkorokhodSpace.dist_eq` identifies `dist f g` with `intDist basePoint f g`, by
  `rfl`, and `[SecondCountableTopology E]` is carried on the instance rather than
  as a section variable, so that Milestones 6 and 7 draw it from `PolishSpace E`,
  which extends it.

  The infimum runs over the time changes fixing the base point, `TimeChange.fixing t₀`
  of Milestone 3, and the norm in it is the **global**
  `TimeChange.norm`, not `normOn m`: only the paths are localized to `B m`, the
  time change is not. This is Billingsley's `d°ₘ` verbatim, and it is forced —
  the windowed norm is not subadditive (`not_normOn_mul_le`, Milestone 3), so a
  `distOn` built on it would have no triangle inequality.

  `distOn` is written (2026-09-07), and the two boundedness conditions it needs
  in order to be the intended quantity are theorems:
  `SkorokhodSpace.bddAbove_range_dist_restrictExhaustion`, so that the supremum
  is the supremum and not the junk value `0`, and
  `SkorokhodSpace.bddBelow_range_distOn`, so that `ciInf_le` applies to the
  infimum. The first runs over
  `SkorokhodSpace.isBounded_range_restrictExhaustion` — the truncated path has
  bounded range, because its range is contained in the image of the compact
  window — and this is the **only** place in Milestones 3 and 4 where the
  compactness of `B m` is used at all. The second is `TimeChange.norm_nonneg`.

  The supremum is taken over all of `ι` and not over `B m`. The two agree,
  because both paths are constant outside the window, and quantifying over `ι`
  is what makes the reindexing in `distOn_comm` a bijection of the index rather
  than of a subset that the time change need not preserve.
* `SkorokhodSpace.metricSpace (t₀ : ι) : MetricSpace D(ι, E)`: symmetry from
  `TimeChange.norm_inv`, the triangle
  inequality from `TimeChange.norm_mul_le`, and separation from
  `TimeChange.dist_le_of_norm_le` together with right continuity.

  It is written and proved (2026-09-07). The metric itself is
  `SkorokhodSpace.totalDist t₀ f g = ∑' m, 2⁻¹ ^ m * min 1 (distOn t₀ m f g)`,
  and the four fields come from four theorems about it:
  `SkorokhodSpace.totalDist_self`, `SkorokhodSpace.totalDist_comm`,
  `SkorokhodSpace.totalDist_triangle` and
  `SkorokhodSpace.eq_of_totalDist_eq_zero`. All four are term by term, and
  `SkorokhodSpace.summable_totalDist` --- the series is dominated by the
  geometric one, since `min 1 ·` is at most `1` --- is what lets them be:
  the triangle inequality is `Summable.tsum_le_tsum` against
  `Summable.tsum_add`, on the subadditivity of `min 1 ·` on the nonnegative
  reals, and the separation is `Summable.le_tsum`, a series of nonnegative terms
  vanishing only if every term does. The truncation at `1` is not cosmetic:
  `distOn t₀ m f g` grows with the window and is unbounded in `m`, so the
  weighted series would not converge without it. Only the triangle inequality
  and the separation read `AdditiveDist ι`, the first three windowless axioms do
  not; the linter has confirmed that.

  It carries the base point as a parameter and is a `def`, not an instance:
  `distOn` is anchored at `t₀` twice over, through the window `exhaustion t₀ m`
  and through the subgroup `TimeChange.fixing t₀`, while the type `D ι E` knows
  nothing of a base point. The instance is the one at the distinguished point of
  an index that has one, which is `0` for all four running instances of
  Milestone 1.
* The parameterless instance `MetricSpace D(ι, E)`, written and proved
  (2026-09-08): it is `SkorokhodSpace.metricSpace basePoint`, with
  `BasePoint ι` of Milestone 1 supplying the point. Its interface is
  `SkorokhodSpace.dist_eq : dist f g = SkorokhodSpace.totalDist basePoint f g`,
  which holds by `rfl`, and it is what every statement below that mentions the
  topology of `D ι E` reads. Everything from here on takes its base point from
  the instance and not from a parameter, since a free `t₀` beside a fixed
  ambient topology would let a statement speak of two spaces at once.
  `SkorokhodSpace.distOn_nonneg`, `SkorokhodSpace.distOn_self`,
  `SkorokhodSpace.distOn_comm` and `SkorokhodSpace.distOn_triangle` are proved
  (2026-09-07), and so is the separation: `SkorokhodSpace.eq_of_distOn_eq_zero`
  --- `distOn t₀ m f g = 0` forces the two truncations to the window to be equal
  --- with `SkorokhodSpace.eq_of_forall_distOn_eq_zero` for the passage from all
  windows to the paths themselves, since every point lies in some window. **All
  four axioms of `distOn` are theorems.** Symmetry and the
  triangle inequality are the two that read the subgroup structure of
  Milestone 3, and they read it from the two sides. Symmetry: `λ ↦ λ⁻¹` is a
  bijection of `TimeChange.fixing t₀`, `norm_inv` leaves the norm unchanged, and
  the supremum is reindexed along the bijection `λ` of `ι`, which turns
  `dist (f (λ t)) (g t)` into `dist (g (λ⁻¹ s)) (f s)` term by term. Triangle:
  the witness for the composite is `λ * λ'`, which has to be admissible again,
  and the `max` splits, `norm_mul_le` carrying one half and the triangle
  inequality of `E` the other, with the middle path evaluated at `λ' t`. The
  infimum is not attained, so the argument runs with an `ε` and
  `SkorokhodSpace.exists_lt_distOn_add`, which is `exists_lt_of_ciInf_lt` on
  `bddBelow_range_distOn`.

  The separation does **not** go through the continuity points and their
  density, and this is a correction of 2026-09-07 to the received proof. The
  classical argument reads `g = f` at the continuity points of `f` and then
  invokes their density, which is a statement about the index: for an index of
  Milestone 1 --- a closed subset of `ℝ`, not an interval --- the continuity
  points need not be dense from the right, so that step is not available at this
  strength. What replaces it is `IsCadlag.eq_of_forall_exists_dist_le` of
  Milestone 2, used with the time change and its inverse played against each
  other. Given `ε`, a `λ` with `norm λ < ε` and `dist (F (λ s)) (G s) < ε` for
  every `s` either moves `t` **up**, and then `F (λ t)` is close to `F t` by the
  right continuity of `F`, or it moves `t` down, in which case `λ⁻¹` moves `t`
  up, `G (λ⁻¹ t)` is close to `G t` by the right continuity of `G`, and the
  hypothesis read at `λ⁻¹ t` is `dist (F t) (G (λ⁻¹ t)) < ε`. Both branches
  approach `t` from the right, which is the only side either path controls, and
  neither uses anything about the index beyond `TimeChange.dist_le_of_norm_le`.
* `SkorokhodSpace.tendsto_iff`: `f n → f` if and only if for every `m` there are
  time changes `λ n` fixing the base point with `norm (λ n) → 0` and
  `sup_{t ∈ B m} r (f n (λ n t)) (f t) → 0`.
* `SkorokhodSpace.tendsto_of_tendsto_uniformly`: uniform convergence on compact
  sets implies convergence in `D ι E`; and the converse when the limit is
  continuous.
* Evaluation: `SkorokhodSpace.continuousAt_eval` — `f ↦ f t` is continuous at
  every `f` with `f⁻ t = f t`, and discontinuous at every other `f`. The second
  half is what pins the metric down to `J₁`, and it is what fails for a metric
  summed over a fixed countable set of radii:
  `SkorokhodSpace.continuous_eval_exhaustionMax` and
  `SkorokhodSpace.exists_jump_continuousAt_eval` are the proof of that failure,
  and the reason the metric above is an integral.

**Acceptance examples.**

* **The sliding step: the metric is not the uniform metric, and it is not summed
  over the integers either.** `ι = ℝ`, `E = ℝ`, `t₀ = 0`,
  `f = Set.indicator (Set.Ici 1) 1` and
  `g ε = Set.indicator (Set.Ici (1 + ε)) 1` for `ε > 0`. The uniform distance
  is `1` for every `ε`, while `distOn u f (g ε) ≤ Real.log (1 + ε)` for
  `1 + ε ≤ u`, witnessed by the piecewise linear time change fixing `0` that carries
  `1 + ε` to `1` and is affine on `[0, 1+ε]` and a translation beyond. So
  `dist f (g ε) → 0` as `ε → 0`. This is the defining property of the `J₁`
  topology, the one thing a wrong definition of `distOn` — the uniform metric,
  or an infimum over all order isomorphisms without the norm term — gets wrong,
  and the pair every later statement about `D ι E` is calibrated against.

  It is also the pair that **detected** the defect of 2026-09-08, and it detects
  it at the radius `u = 1`: there `b = exhaustionMax 0 1 = 1`, `f 1 = 1` and
  `g ε 1 = 0`, so `1 ≤ distOn 1 f (g ε)` by
  `SkorokhodSpace.dist_exhaustionMax_le_distOn`, whatever `ε` is. A metric
  summing `min 1 (distOn m f g)` over `m : ℕ` is therefore at least `1/2` on this
  pair for every `ε`, and the example is false for it. The bad radii here are
  the single point `u = 1`, of Lebesgue measure zero, so the integral above is
  unaffected — which is the whole content of the repair.
* **Evaluation at the jump, which is the manuscript's `ex:atomicdiscontinuity`.**
  With `f` and `g (1/n)` as above, `g (1/n) → f` in `D ℝ ℝ` while
  `eval 1 (g (1/n)) = 0` and `eval 1 f = 1`. So `continuousAt_eval` must be
  false at `f`, and `f⁻ 1 = 0 ≠ 1 = f 1` is exactly its criterion; at any
  `t ≠ 1` the same map is continuous at `f`. The manuscript reads this as the
  failure of hypothesis `(C3a)` for a clock with an atom at `1`.

  `SkorokhodSpace.exists_jump_continuousAt_eval` is the same example run against
  the summed metric, where it comes out the wrong way: evaluation at `1` is
  continuous there at `SkorokhodSpace.step`, jump and all.
* **The two jumps that cannot merge.** `f n = Set.indicator (Set.Ici 1) 1 +
  Set.indicator (Set.Ici (1 + 1/n)) 1`. Pointwise `f n → 2 • Set.indicator
  (Set.Ici 1) 1`, and in `D ℝ ℝ` it does **not** converge: a time change of
  small norm moves `1` and `1 + 1/n` by little, so the image path still has two
  jumps of height `1` while the candidate limit has one of height `2`: for every
  càdlàg `h` and every `m ≥ 2`, `1/2 ≤ liminf n, distOn m (f n) h`, so no
  subsequence converges. This is the
  standard witness that `J₁` is not the topology of pointwise convergence, and
  it reappears in Milestone 7 as a family without compact closure.
* **The degenerate window.** `ι = Set.Icc (0:ℝ) 0`, or a discrete index at small
  radius: `B u` is a single point, every `distOn u f g` is
  `min over the trivial group of max 0 (r (f t₀) (g t₀))`, and `dist f g` is
  `∫ u in Ioi 0, exp (-u) * min 1 (that)`, which is that number truncated at `1`.
  The metric axioms must all hold there, which is where the junk values of
  Milestone 3 are consumed.

## Milestone 5: completeness and separability

All three declarations of this milestone stand in `Suggested.lean` again since
2026-09-08, against the instance `SkorokhodSpace.instMetricSpace`, which is the
integral metric: `SkorokhodSpace.instCompleteSpace`,
`SkorokhodSpace.instSeparableSpace` and `SkorokhodSpace.instPolishSpace`. They
were withdrawn earlier the same day and the reason was the summed metric, for
which the first is false; the refutation stays and is stated for
`SkorokhodSpace.totalTopology`, which names that metric and not the instance.
All three are **proved** since 2026-09-09: the first on 2026-09-08, the second
on 2026-09-09, and the third by `inferInstance` from the two.

The second and third carry a hypothesis on the index,
`SkorokhodSpace.HasCountableCore ι`. That is not a convenience:
`SkorokhodSpace.not_separableSpace_of_rigid`, proved 2026-09-09, shows that
`D ι E` is not separable for every index this file admits, and the witness is
the middle thirds Cantor set. The milestone therefore owes the class its
instances as well, and two of the three are proved —
`Real.instHasCountableCore` and `SkorokhodSpace.hasCountableCore_of_countable`,
both 2026-09-09. What is left of the milestone is the third instance,
`Set.Icc (0 : ℝ) 1`, and nothing rests on it.

* `CompleteSpace (D ι E)`, **proved 2026-09-08**: for a Cauchy sequence extract a
  subsequence whose consecutive distances are summable, compose the time changes,
  and use completeness of `E` together with `TimeChange.norm_mul_le` to see that
  the composed time changes converge. The statement rests on eight named items,
  all of them proved:
  * `SkorokhodSpace.min_one_distOn_le` and
    `SkorokhodSpace.distOn_le_of_two_pow_mul_lt_one`, the passage from the metric
    to the window pseudodistance: `min 1 (distOn t₀ m f g) ≤ 2 ^ m * totalDist t₀ f g`,
    and the same without the truncation for pairs with `2 ^ m * totalDist < 1`.
    The hypothesis of the second is not a defect — `distOn` is unbounded as the
    window grows, so no bound of that shape holds for all pairs — and a Cauchy
    sequence supplies it for all but finitely many indices (2026-09-08). These
    two are stated for `totalDist`, the summed metric, and the instance is the
    integral one, so this rung is the one that had to be rewritten: from
    `intDist t₀ f g < ε` no single radius is small, because the integral carries
    no weight at any named radius — which is exactly what makes it a Skorokhod
    metric and the sum not one.
  * `SkorokhodSpace.ae_summable_min_one_distWith`, the rewritten rung, proved
    2026-09-08. If the time changes `l n` compare the pairs `x n`, `y n` at a
    summable cost `γ n` in `intWith`, then at **almost every** radius `u` the
    truncated window distances `min 1 (distWith t₀ u (l n) (x n) (y n))` are
    summable in `n`. A completeness proof needs a summable rate at one radius at
    a time and is free to choose the radius, so it chooses one of these; that is
    the entire adaptation of Billingsley's argument to the integral form. The
    proof is the one `SkorokhodSpace.eq_of_intDist_eq_zero` runs with
    `γ n = 2⁻ⁿ`, factored out for a general summable `γ`:
    `MeasureTheory.lintegral_tsum` makes the series of integrands integrable,
    `MeasureTheory.ae_lt_top` makes it finite almost everywhere, and
    `ENNReal.tsum_coe_ne_top_iff_summable` turns that finiteness back into
    summability over `ℝ`. The weight `Real.exp (-u)` divides out by
    `summable_mul_left_iff`, since it does not depend on `n`; the weight `2⁻ᵐ` of
    the sum could not, and that asymmetry is the whole difference between the two
    metrics for this proof.
  * `SkorokhodSpace.exists_lt_distOn_add`, the approximate minimiser that turns
    a small `distOn` into an actual time change (2026-09-06).
  * `TimeChange.exists_tendsto_of_summable_norm` and
    `TimeChange.exists_tendsto_norm_tail_le`, the infinite composition: if
    `‖l n‖ ≤ γ n` with `γ` summable and every `l n` fixes `t₀`, the partial
    compositions `TimeChange.partialComp l n = l 0 ∘ ⋯ ∘ l (n-1)` converge
    pointwise to a time change `L` fixing `t₀` with `‖L‖ ≤ ∑' γ`, and after `n`
    steps what is left undone satisfies `‖(partialComp l n)⁻¹ * L‖ ≤ ∑' i, γ (n + i)`
    (2026-09-08). The step that is more than a convergence argument is the
    **surjectivity** of `L`: a pointwise limit of order isomorphisms is monotone
    and injective for free, but on an index that is not assumed connected nothing
    forces its image to be all of `ι`. It is obtained by running the same
    estimate on the inverses — `(partialComp l n * l n)⁻¹ = (l n)⁻¹ * (partialComp l n)⁻¹`
    displaces a point by exactly the displacement of `(l n)⁻¹`, on the window
    enlarged by the uniform Lipschitz constant `exp (∑' γ)` — so that the inverse
    limit `M` exists and `partialComp l n ((partialComp l n)⁻¹ t) = t` passes to
    the limit. The supporting items are `TimeChange.lipConst_le_exp_norm`,
    `TimeChange.norm_le_of_lipschitzWith`, `TimeChange.norm_partialComp_le` and
    `TimeChange.partialComp_add`.
  * `IsCadlag.of_tendstoUniformly`, which catches the limit path (2026-09-08).
  * `SkorokhodSpace.tendsto_of_partialComp`, the assembly, **proved 2026-09-08**.
    From a sequence `x n` and time changes `l n` anchored at `t₀` whose norms and
    whose `intWith` costs are both dominated by a summable `γ` — which is what
    `SkorokhodSpace.exists_lt_intDist_add` produces from a Cauchy sequence with
    summable consecutive distances — it produces the limit path `z`, the single
    time change `L` of `exists_tendsto_norm_tail_le`, and the convergence of
    `x n ∘ κ n`, `κ n = (partialComp l n)⁻¹ * L`, to `z` **uniformly on every
    window**. Three things carry it. The recursion `κ n = l n * κ (n+1)` turns
    the increment `r (x n (κ n t)) (x (n+1) (κ (n+1) t))` into
    `r (x n (l n s)) (x (n+1) s)` with `s = κ (n+1) t`, which is one term of
    `distWith`. The uniform bound `‖κ n‖ ≤ ∑' γ` keeps both `s` and `l n s`
    inside the window of radius `exp (∑' γ) · m` whenever `t` lies in the window
    of radius `m`, so one `distWith` bounds the increment for the whole window at
    once. And `SkorokhodSpace.exists_gt_summable_distWith` supplies, above that
    radius, a radius at which those `distWith` are summable in `n` — the good
    radii are unbounded because the bad ones are null and `Set.Ioi c` has
    infinite measure. Then `cauchySeq_of_dist_le_of_summable` gives the limit
    pointwise and `dist_le_tsum_of_dist_le_of_tendsto` gives it uniformly, with
    the tail of the series as the rate. That `z` is càdlàg is
    `IsCadlag.of_tendstoUniformlyOn_exhaustion` of Milestone 2: uniform
    convergence on every window suffices, since `x n ∘ κ n ∘ clamp u` converges
    uniformly on all of `ι` and every point lies in the interior of some window.
    Two small items go with it: `summable_of_summable_min_one`, which undoes the
    truncation at `1` that `ae_summable_min_one_distWith` leaves behind, and
    `SkorokhodSpace.dist_le_distWith`, one term of the supremum.
  * `SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp`, **proved
    2026-09-08**: locally uniform convergence of `x n ∘ κ n` to `z`, together with
    `‖κ n‖ → 0`, gives `intDist t₀ (x n) z → 0`. It is not a repetition of the
    assembly: `distWith t₀ u (κ n) (x n) z` clamps the two paths **separately**,
    `x n` at `κ n t` and `z` at `t`, so on the part of the index above
    `A = exhaustionMax t₀ u` both readings collapse onto `A` and the term becomes
    `r (x n A) (z A)` — a comparison of the two paths at one point, off by the
    time change. Three items carry it.
    * `SkorokhodSpace.distWith_le_of_oscillation`: `distWith t₀ u l f g ≤ 3ε` as
      soon as `r (f (l s)) (g s) ≤ ε` on `l⁻¹` of the window and the oscillation
      of `g` between each window endpoint and its `l`-preimage is at most `ε`.
      Its combinatorial half is `min_max_pair_cases` — the two clamps of one
      point either agree, or both lie between the two upper window ends, or both
      between the two lower ones — and its metric half is
      `dist_le_dist_of_mem_uIcc`, which is `AdditiveDist` alone. It needs neither
      `0 ≤ u` nor `l t₀ = t₀`.
    * `SkorokhodSpace.tendsto_distWith_of_tendstoUniformlyOn`, the statement at
      one radius. It carries a **disjunction at each window endpoint**: either
      the index has a gap there, and then `TimeChange.eq_of_gap_of_norm_lt` and
      its mirror `TimeChange.eq_of_gap_below_of_norm_lt` (both proved 2026-09-08,
      and neither needs `OrderTopology ι` or `ProperSpace ι`) say that every time
      change anchored at `t₀` whose displacement `(exp ‖λ‖ - 1) · 2u` on the
      window is below the gap width fixes the endpoint outright, so the
      oscillation hypothesis is vacuous; or `z` is continuous at the endpoint,
      and then the oscillation dies with the displacement.
    * `SkorokhodSpace.tendsto_intWith_of_ae_tendsto_distWith`, dominated
      convergence over the radius against `exp (-u)`.

    The dichotomy that closes it is **not** the one this milestone carried until
    2026-09-08, and the correction is a finding of that day. It read "either the
    level set `{u : exhaustionMax t₀ u = A}` is null, and then that radius is
    discarded with the null set", and that is no argument: a union of null level
    sets need not be null. What is true is that a radius **without** a gap above
    its window edge determines that edge —
    `exhaustionMax_lt_exhaustionMax_of_no_gap`, the window then grows strictly —
    so `countable_radius_exhaustionMax` makes the radii at which the edge is
    moreover a jump of `z` countable, the jump set of a càdlàg path being
    countable (`countable_leftJumpSet` of Milestone 2). Off that countable, hence
    Lebesgue null, set one of the two disjuncts holds at every radius. No
    compactness is spent, and the sentence that produced the gap width from
    compactness is gone with it.

    And the lower window edge is **not** free, which this milestone also assumed.
    Right continuity of `z` at `exhaustionMin t₀ u` would settle it only if the
    time changes moved that point to the right, and nothing makes them: `κ n⁻¹`
    may carry it either way, and `Set.uIcc` is the interval in both directions.
    The mirror is therefore run in full —
    `TimeChange.eq_of_gap_below_of_norm_lt`,
    `exhaustionMin_lt_exhaustionMin_of_no_gap`,
    `countable_radius_exhaustionMin` — and what is used at the lower edge is
    `ContinuousAt`, not right continuity.
  * `SkorokhodSpace.instCompleteSpace`, **proved 2026-09-08**, is the composition
    of the two assemblies. `Metric.complete_of_convergent_controlled_sequences`
    with `B n = 2⁻⁽ⁿ⁺¹⁾` is what supplies a sequence whose consecutive distances
    are summable — an arbitrary Cauchy sequence supplies no rate, and both
    assemblies need one — `SkorokhodSpace.exists_lt_intDist_add` turns those
    distances into time changes with `‖l n‖ ≤ 2⁻ⁿ` and
    `intWith t₀ (l n) (y n) (y (n+1)) ≤ 2⁻ⁿ`, `tendsto_of_partialComp` produces
    `z` and `L`, and `tendsto_intDist_of_tendsto_of_partialComp` reads
    `dist (y n) z → 0` off them. The norms `‖(partialComp l n)⁻¹ * L‖` go to `0`
    because they are below the tails `∑' i, 2⁻⁽ⁿ⁺ⁱ⁾`.
  * The route through the truncations — a limit per window, glued along
    `SkorokhodSpace.restrictExhaustion_restrictExhaustion` — is **not** the route,
    and this is the correction of 2026-09-08. It fails at the window endpoints and
    not for a technical reason: `SkorokhodSpace.dist_exhaustionMax_le_distOn` shows
    that `distOn u` reads `r (f b) (g b)` at `b = exhaustionMax t₀ u` off the
    paths directly, so a limit in `distOn u` has to match the sequence pointwise
    at `b`, and the `J₁` limit of a sequence need not. The coherence
    `restrictExhaustion_restrictExhaustion` is proved (2026-09-08) and stays; what
    it does not do is produce a limit.
* `SkorokhodSpace.not_separableSpace_of_rigid`, **proved 2026-09-09**, and it is
  what fixes the shape of everything below it: if `ι` is uncountable and the
  only time change fixing the base point of norm below some `c > 0` is the
  identity, then `D ι E` is **not separable** for any `E` with two points. The
  mechanism is `SkorokhodSpace.stepAt x a b`, the path taking `a` from `x` on
  and `b` strictly below, càdlàg by `IsCadlag.of_eventually_const`; two of them
  differ by `dist a b` at `min x y` for the identity time change
  (`SkorokhodSpace.dist_le_distWith_stepAt`), hence by
  `exp (-dist t₀ (min x y)) * min 1 (dist a b)` in `intWith`
  (`SkorokhodSpace.le_intWith_stepAt`) and, `hrigid` disposing of the other time
  changes, in the metric (`SkorokhodSpace.le_intDist_stepAt`). An uncountable
  index has an uncountable closed ball, and an uncountable uniformly separated
  family admits no countable dense set.

  The witness for the hypotheses is the **middle thirds Cantor set**: closed in
  `ℝ`, hence carrying `LinearOrder`, `MetricSpace`, `OrderTopology`,
  `AdditiveDist` by `instAdditiveDistSubtype` and `ProperSpace` by compactness,
  and uncountable. Its gaps have the lengths `3 ^ (-n)`, an order isomorphism
  carries gaps to gaps, and a bi-Lipschitz one with both constants below `3`
  cannot change a gap length, the ratio of two distinct ones being at least `3`;
  so it fixes the unique gap of length `1/3`, by induction along the order every
  gap, hence every gap endpoint, hence — the endpoints being dense —
  everything. Every non-identity time change has norm at least `log 3`. **That
  computation is on paper and not in Lean**, which is why the theorem carries
  `hrigid` as a hypothesis; building the Cantor set with its gap structure is
  the one thing that would make the refutation unconditional, and it is not
  needed for anything else.
* `SkorokhodSpace.HasCountableCore ι`: the class the previous item forces. It
  asks for a countable `C ⊆ ι` together with, for every finite strictly monotone
  tuple `t : Fin (n+1) → ι` and every `δ > 0`, a tuple `d` in `C` and a time
  change `l` fixing the base point with `‖l‖ ≤ δ`, `l (d i) = t i` **and
  `dist (d i) (t i) ≤ δ`**. It is the heavy half of separability isolated as a
  statement **about the index and not about the paths**, and it is a hypothesis
  and not a theorem.

  The displacement clause is the third and it was added on 2026-09-09, for the
  reason recorded at the separability below: it is the displacement and not the
  norm that bounds the measure of the radii whose window edge separates a node
  from its image, and at those radii the metric compares the two paths with no
  time change interposed. It is **not implied** by the norm clause: on an index
  with gaps the identity has norm `0` and a time change of norm `0` can carry a
  point across a whole gap, so a small norm says nothing about how far a point
  travels. Both proved instances satisfy it —
  `SkorokhodSpace.exists_rat_nodes_perturbation` takes its rationals within a
  prescribed `ζ` of the `t i`, and on a countable index `d` is `t` itself.

  **A countable dense subset of `ι` is not enough**, which is the finding of
  2026-09-08. On `ι = Set.Icc (0 : ℝ) 1` with base point `0` every time change
  is an order isomorphism of a linear order with a greatest element and
  therefore fixes `1`; the càdlàg path `f = Set.indicator {1} 1` then keeps its
  distance from every step path whose jump times avoid `1`, since such a `g` is
  constant on `[d, 1]` for its last jump time `d < 1` and its value `c` there
  has to answer both `f (l 1) = 1` and `f (l d) = 0`, so
  `distWith t₀ u l f g ≥ max |c - 1| |c| ≥ 1/2` for every `l` and every `u ≥ 1`,
  whence `intDist t₀ f g ≥ exp (-1) / 2`. A countable dense subset of
  `Set.Icc (0 : ℝ) 1` need not contain `1`; the `C` of the class does contain
  it, the one point tuple `t = ![1]` having only the identity to carry anything
  onto it.
* `Real.instHasCountableCore`, and the same for
  `AddSubgroup.zmultiples (1 : ℝ)` and for `Set.Icc (0 : ℝ) 1`: the three
  running instances of the file discharge the class. **`ℝ` is proved**
  (2026-09-09). The construction is `TimeChange.exists_of_lengthCoord` of
  Milestone 3 applied to `φ x = x + ψ x`, where `ψ` is a **sum of tents**, one
  at each rational node `d i`, of height the displacement `t i - d i` and of a
  radius `ρ` small enough that the tents neither overlap nor reach the base
  point; `C` is `ℚ`. Writing `φ` as a perturbation of the identity rather than
  as a piecewise linear interpolant is what keeps the estimate uniform in the
  number of nodes: the crude bound `∑ᵢ |t i - d i| / ρ` on the Lipschitz
  constant of `ψ`, which ignores that the tents have disjoint supports, already
  suffices, because the displacements may be shrunk after `ρ` is fixed. The
  Lipschitz constants of `φ` are then `1 + K` and `(1 - K)⁻¹`, and
  `K = 1 - exp (-δ)` makes both at most `exp δ`.

  Two points of it are not decoration, and both concern the base point. The
  separation `ε` is taken over `{0} ∪ range t` and not over `range t`
  (`exists_pos_forall_le_abs_sub` on `Option (Fin (n+1))`), because a node may
  sit arbitrarily close to `0` without being `0`; and the node of a `t i` which
  *is* `0` is `0` itself, so that the tent there has height `0`. Without the
  first the tent at that node would cover the base point and the time change
  would move it. On
  `AddSubgroup.zmultiples (1 : ℝ)` the index is countable, `C` is all of it and
  `l` is the identity; that case is
  `SkorokhodSpace.hasCountableCore_of_countable`, **proved 2026-09-09**, and it
  is stated for an arbitrary countable index because nothing about the integers
  enters it. On `Set.Icc (0 : ℝ) 1` it is the construction on `ℝ` with
  `C = (ℚ ∩ [0,1]) ∪ {0, 1}`, the two endpoints being the points no time change
  moves. In general the `C` that works is a countable dense set together with
  the boundaries of the connected components of the index read as a closed
  subset of `ℝ` through `exists_orderIso_isometry_real` of Milestone 1 — and the
  Cantor set is precisely the case where that boundary is uncountable, which is
  the refutation above seen from the other side.
* `SeparableSpace (D ι E)` under `[SkorokhodSpace.HasCountableCore ι]`, **proved
  2026-09-09**: the step paths with jump times in `C` and values in a countable
  dense subset of `E` are dense. Its analytic half is (2026-09-08):
  `SkorokhodSpace.exists_finite_range_distWith_le` gives, for every `f`, every
  `ε > 0` and every radius `M`, a `g : D ι E` with finite range and
  `distWith t₀ u 1 f g ≤ ε` for all `u ≤ M` — the approximation of a càdlàg path
  by a step path **at its own jump times**, uniform on the window, for the
  identity time change. It is `IsCadlag.exists_subdivision` of Milestone 2 read
  through `stepRetract`, the retraction of the index onto the range of a finite
  tuple. Its passage to the metric is proved too (2026-09-09):
  `SkorokhodSpace.exists_finite_range_intDist_le` gives `intDist t₀ f g ≤
  ε + exp (-M)`, over `SkorokhodSpace.intWith_le_of_forall_distWith_le`, which
  splits `Set.Ioi 0` at `M` and pays the far radii with the mass `exp (-M)` and
  the truncation at `1`. The move of the jump times is proved too (2026-09-09):
  `stepRetract_orderIso` says that `stepRetract t (l x) = l (stepRetract d x)`
  whenever `l (d i) = t i`, so the approximant read at the subdivision `t`
  becomes, after the time change, the approximant read at the subdivision `d`,
  whose points lie in `C`. It is an equality of paths and not an estimate, so it
  costs nothing beyond `‖l‖`; the values are moved into a countable dense subset
  of `E` for free, no time change being involved in that.

  The countability of the family is proved too (2026-09-09).
  `SkorokhodSpace.stepPath d v : D ι E` is the step path as a **term**, for
  arbitrary nodes `d : Fin (n+1) → ι` and values `v : Fin (n+1) → E`;
  `SkorokhodSpace.stepPathFamily C Q` is the set of those with `d` in `C` and `v`
  in `Q`, and `SkorokhodSpace.countable_stepPathFamily` says it is countable.
  The signature question is settled in favour of a second declaration:
  `stepIdx t x` is the *index* the retraction reads and `stepRetract t = t ∘
  stepIdx t` is now its definition, so the five theorems about `stepRetract` and
  its consumer stay as they are, while the values hang on `stepIdx`. Three of
  those five got **weaker hypotheses** out of the move —
  `eventually_stepRetract_eq_nhdsGT`, `exists_eventually_stepRetract_eq_nhdsLT`
  and `isCadlag_comp_stepRetract` no longer ask `StrictMono t`, since the
  retraction reads a maximum out of a `Finset` and that is insensitive to the
  enumeration — and that is what makes `stepPath` a **total** function, which the
  counting needs: the family is the range of a map out of
  `Σ n, (Fin (n+1) → C) × (Fin (n+1) → Q)` with no side condition on the data.
  The two moves are `SkorokhodSpace.distWith_one_stepPath_le` for the values and
  `SkorokhodSpace.stepPath_apply_orderIso` for the nodes.

  **What is left is the window edge, and it is analysis and not bookkeeping**
  (finding of 2026-09-09, third run). The two moves control
  `distWith t₀ u l f g` in the interior of the window at every radius and do not
  control it at the edge. For `x` beyond `B = exhaustionMax t₀ u` both readings of
  `distWith` clamp to `B`, so the term is `dist (f B) (g B)` with **no time change
  interposed** — that is `SkorokhodSpace.dist_exhaustionMax_le_distOn`, the fact
  that killed the summed metric — while `g B` is the value of the cell of `B`
  counted with the *moved* nodes, `stepIdx t (l B)` and not `stepIdx t B`. Those
  differ exactly when a node separates `B` from `l B`, and then the term is the
  jump of `f` at that node, which no `ε` makes small. There is no way round it by
  choosing the direction of the displacement: moving the nodes down makes `l B`
  fall below `B` and the same term reappears on the other side.

  The repair is the displacement clause of `HasCountableCore` together with
  `volume_radius_exhaustionMax_mem_Ico` (**proved 2026-09-09**), which bounds the
  measure of the radii whose edge falls in `Set.Ico a b` by `dist a b`; the bad
  radii for one node are those whose edge falls between `d i` and `t i`, so they
  have measure at most `∑ᵢ dist (d i) (t i) ≤ (n+1) δ`, and the integrand of
  `intWith` being bounded by `1` they cost no more than that.

  The integral half of the repair is proved too (2026-09-09):
  `SkorokhodSpace.intWith_le_of_ae_distWith_le` asks the windowed bound only *off*
  a measurable set `B` of radii and pays `B`'s measure below `M`, so the estimate
  reads `ε + β + exp (-M)`; the split of `Set.Ioc 0 M` is `Set.diff_union_inter`
  and the bad piece is bounded by `1`, the integrand being `exp (-u) * min 1 _`.
  `radius_exhaustionMax_mem_Ico_subset` is what supplies a *measurable* `B`: the
  radius set itself is only visibly contained in
  `Set.Icc (lengthCoord t₀ a) (lengthCoord t₀ b)`, `exhaustionMax` being monotone
  and nothing more, so `B` is taken to be the finite union of those intervals over
  the nodes and `δ` is chosen after the length `n` of the subdivision.

  The case distinction on the supremum is **not** a fresh one:
  `SkorokhodSpace.distWith_le_of_oscillation` already runs it, and what the
  separability has to supply are its three hypotheses.
  `SkorokhodSpace.distWith_stepPath_le` (**proved 2026-09-09**) supplies them and
  is the whole estimate at one radius, `distWith t₀ u l f (stepPath d w) ≤ 6 ε`.
  Its subdivision only has to **cover** the window: `t 0 ≤ (B M).min` and
  `(B M).max ≤ t (Fin.last n)` are inequalities since 2026-09-09, where they were
  equalities before. It costs nothing — they are read at one place, to put `l s`
  between the extreme nodes — and it is what makes the estimate applicable to the
  subdivisions `modulusBased` actually produces, which are the overshooting ones
  of `IsSubdivision`. Trimming those to the window instead is not an option: the
  trimmed first and last gaps can be arbitrarily small, and the sparseness is
  exactly what `exists_finite_grid_timeChange` needs to separate its tents.
  The uniform hypothesis costs `2 ε` — `stepIdx_orderIso` carries the values
  across the time change unchanged, then `dist_comp_stepRetract_le` and the move
  into `Q` cost `ε` each. The two oscillation hypotheses cost **nothing**: the
  step path is *constant* between a window end and its preimage, which is
  `SkorokhodSpace.stepIdx_eq_of_mem_uIcc` (2026-09-09), and the condition it asks
  of the window end `A` is a condition on the index alone — that `A` avoid every
  `Set.Ico (min (d i) (t i)) (max (d i) (t i))`, the interval spanned by a node
  and its image. Its proof is the trichotomy of `A` against `l⁻¹ A` read through
  the order isomorphism, and its combinatorial half is
  `stepIdx_congr_of_forall_notMem_Ioc`: the cell index only sees the nodes in
  `Set.Ioc` of the two points, half open on the same side `stepIdx` reads.

  `SkorokhodSpace.exists_bad_radii_set` (2026-09-09) packages the whole of this
  bookkeeping: it produces the measurable set `B` of bad radii, bounds
  `volume (Set.Ioc 0 M ∩ B)` by `(n + 1) (2 δ + (exp δ - 1) 2 M)`, and gives the
  windowed estimate off `B`. It knows nothing of where `d` came from — only the
  displacement bound `dist (d i) (t i) ≤ δ` — which is why both the separability,
  whose `d` comes from `HasCountableCore`, and the converse of Milestone 7, whose
  `d` comes from `exists_finite_grid_timeChange`, read the same theorem. Its
  measure bound counts **all** the nodes, and that is enough only where `n` is
  known before `δ` is chosen, which is the separability's situation and not the
  converse's; the sharper count, over the nodes whose coordinate interval meets
  the window, is the first item of the converse and is stated with it.

  **The two window ends are not symmetric, and that is the last finding**
  (2026-09-09, fourth run). `exhaustionMax t₀` is monotone and
  `exhaustionMin t₀` is antitone, so `Set.Ico a b` excludes exactly the sticky
  end of the first and includes the sticky end of the second: the mirror of
  `volume_radius_exhaustionMax_mem_Ico` with `exhaustionMin` in place of
  `exhaustionMax` is **false**, and on an index bounded below it fails by an
  infinite margin — the lower edge sits at the least point for every radius past
  its coordinate. `radius_exhaustionMin_mem_Ico_subset` and
  `volume_radius_exhaustionMin_mem_Ico` (**proved 2026-09-09**) therefore carry
  an extra hypothesis, and it is exactly what the application has: the edge is a
  bad radius only when the time change *moves* it, and a time change that moves
  the least point of the window puts a point of the index within `κ` below that
  point — its image or its preimage, whichever falls low. That point is outside
  the window, so the radius is at most `κ` past the coordinate of the edge, and
  the sticky tail is cut at `κ`; the bound is `dist a b + κ` and not `dist a b`.
  The other side of the same coin is the disjunction in
  `SkorokhodSpace.distWith_stepPath_le`: at the lower edge it is enough that the
  time change *fix* it, which is what an index with a gap below forces and what
  makes the bound usable there at all.

  So the budget of the assembly is: `6 ε ≤ r/4` fixes `ε` from `r`; `M` is fixed
  from `r` by `exp (-M) < r/4`; the subdivision fixes `n`; and only then is `δ`
  chosen, small enough that `δ < r/4` bounds `‖l‖` and
  `(n+1) (2 δ + (exp δ - 1) 2M) < r/4` bounds the bad radii. The order is forced
  — `n` depends on `ε` and `M`, and the bad set on `n` — and it is why the
  displacement clause of the class quantifies over `δ` after the tuple.
* `PolishSpace (D ι E)`, from the two above, and it costs nothing: Mathlib
  builds `PolishSpace` out of `SeparableSpace` and `IsCompletelyMetrizableSpace`
  (`Mathlib/Topology/MetricSpace/Polish.lean:66`), and the latter out of a
  complete metric (`MetricSpace.toIsCompletelyMetrizableSpace`,
  `Mathlib/Topology/Metrizable/CompletelyMetrizable.lean:172`), so the
  declaration is `inferInstance` and carries no proof obligation of its own
  (2026-09-08). Since 2026-09-09 it depends on nothing but `propext`,
  `Classical.choice` and `Quot.sound`, the separability under it being proved;
  it is `fact:PSpolish` for the `J₁` topology and what `rem:EKrelcompact`
  consumes.

  All three are stated for the metric of Milestone 4 as it stands there, the
  integral over the window radius. For the weighted sum over integer radii that
  `SkorokhodSpace.totalDist` computes, the first of them is **false**, and the
  sequence `x n = Set.indicator (Set.Iio (1 + 1/(n+1))) 1` in `D ℝ ℝ` is the
  witness: it is Cauchy, because the piecewise linear time change fixing `0`,
  the identity outside `[1/2, 2]`, carrying `1 + 1/(k+1)` to `1 + 1/(n+1)`, makes
  every windowed supremum vanish and has norm tending to `0`; and it has no
  limit, because `SkorokhodSpace.dist_exhaustionMax_le_distOn` at the radius `1`
  forces `w 1 = lim x n 1 = 1` for any candidate `w`, putting the jump of `w`
  strictly to the right of `1`, while the time changes of the radius `2` would
  have to carry that jump to `1 + 1/(n+1) → 1` with norms tending to `0`. Since
  `x n 1 = 1` for every `n` and the bad radius is the single point `u = 1`, the
  integral of Milestone 4 does not see it.
* `SkorokhodSpace.isClosed_range_continuous`: the continuous paths form a closed
  subspace, on which the metric induces the topology of uniform convergence on
  compact sets.

**Acceptance examples.**

* **The shrinking bump: why the norm is logarithmic.** `ι = ℝ`, `E = ℝ`,
  `x n = Set.indicator (Set.Ico (1/2) (1/2 + 1/n)) 1`. Measure the time changes
  with Billingsley's older `sup t, dist (λ t) t` instead of `TimeChange.norm`.
  Then `x n` is Cauchy: the piecewise linear `λ` carrying `1/2 + 1/n` to
  `1/2 + 1/m` and fixing `0` and `1` matches the two paths exactly and moves
  points by at most `|1/n - 1/m|`. And it has no limit: any candidate `h` would
  have `‖h‖ ≥ 1` and a bump of vanishing width, which no càdlàg function has.
  Under `TimeChange.norm` the same sequence is **not** Cauchy — that `λ`
  compresses by the factor `n/m`, so its norm is `|log (n/m)|`, which does not
  go to `0` along `m = 2n`. So `CompleteSpace (D ι E)` is a theorem about the
  logarithmic norm of Milestone 3 and false for the naive one; this is the
  instance that decides between the two definitions.
* **A Cauchy sequence that does converge, and whose pointwise limit is not the
  answer.** `f n = Set.indicator (Set.Ici (1 + 1/n)) 1` is Cauchy and converges
  in `D ℝ ℝ` to `Set.indicator (Set.Ici 1) 1`, by the sliding step example of
  Milestone 4. Its **pointwise** limit is `Set.indicator (Set.Ioi 1) 1` — the
  open ray, since `f n 1 = 0` for every `n` — and that function is not càdlàg at
  `1`. So the completeness proof cannot construct its limit pointwise, and a
  statement of `CompleteSpace (D ι E)` that did would not typecheck.
* **Separability, exhibited.** On `ι = Set.Icc (0:ℝ) 1` and `E = ℝ` the
  countable dense set is the paths `∑ i < k, q i • Set.indicator (Set.Ici (p i)) 1`
  with `p i, q i` rational. That `f = Set.indicator (Set.Ici (1/Real.sqrt 2)) 1`
  is approximated by them uses the time change and not the values: no member of
  the family agrees with `f` anywhere near the jump, and the approximation is in
  `distOn`, at cost `|log (p / (1/Real.sqrt 2))|`. That the family works at all
  is `HasCountableCore (Set.Icc (0:ℝ) 1)` with `C = (ℚ ∩ [0,1]) ∪ {0, 1}`; drop
  `1` from `C` and `Set.indicator {1} 1` is `exp (-1) / 2` away from every
  member of the family, which is the other half of this pair.
* **Separability, refuted, and it is the instance that fixes the shape of the
  statement.** `ι` the middle thirds Cantor set with base point `0`, `E = ℝ`,
  and the family `SkorokhodSpace.stepAt x 1 0` for `x ∈ ι`. It is uncountable,
  and any two of its members are at distance at least `min (log 3) (exp (-1))`:
  a non-identity time change costs `log 3`, because it would have to change a
  gap length and the ratio of two distinct gap lengths of the Cantor set is at
  least `3`, and the identity leaves the two paths `1` apart at `min x y` for
  every radius above `1`. So `D ι ℝ` is not separable, `HasCountableCore` fails,
  and a `SeparableSpace (D ι E)` stated without it would be false. The
  implication is `SkorokhodSpace.not_separableSpace_of_rigid` in Lean; the
  arithmetic of the gap lengths that discharges its `hrigid` is on paper.

## Milestone 6: the Borel structure

This is `thm:fdd`, and it is **closed since the fifth run of 2026-09-09.** It
takes Milestone 5 for granted: `SkorokhodSpace.instPolishSpace` is proved under
`HasCountableCore ι`, so `D ι E` is a standard Borel space and the second half
of the embedding — a measurable injection between standard Borel spaces is a
measurable embedding, `Measurable.measurableEmbedding` over Lusin--Souslin — is
available. That second half is the cheap one, and its injectivity is
`IsCadlag.eq_of_eqOn_dense` of Milestone 2.

**The whole content is the first item, and the manuscript says so at
`thm:fdd`:** `π_t` is *discontinuous* at every path with a jump at `t`, so the
measurability of a coordinate is a theorem and not a remark, and the acceptance
example below is the refutation of the route through continuity. The route
avoids any linear structure on `E` — `E` is a bare metric space in this file and
averaging over a window is not available — and it spends right continuity.

**It is not, as this roadmap said until 2026-09-09, a pointwise limit of
`d`-continuous functionals.** The functionals of the proof are the window
suprema `⨆ s ∈ ball t ρ ∩ Ioi t, edist (f s) y`, and they are lower
semicontinuous and *not* continuous: at the path that jumps at `t` the supremum
over the punctured right neighbourhood is the value after the jump, and an
approximating sequence whose jump sits just to the right of `t` has the value
before it inside the window. Lower semicontinuity is all the approximation
lemma gives — it moves a witness of the supremum to a nearby point, which is a
one-sided statement — and it is all that is needed, because the limit is taken
over a shrinking family and is therefore an infimum.

* `SkorokhodSpace.exists_orderIso_dist_lt_of_intDist_lt`: given `s` and `ε`
  there is a `δ`, depending on neither path, such that `intDist t₀ f g < δ`
  produces an order isomorphism `e` with `dist (e s) s < ε`,
  `dist (e.symm s) s < ε` and `dist (f s) (g (e.symm s)) < ε`. Proved
  (2026-09-09). This is what the integral metric gives in place of the
  continuity it denies, and both halves of `measurable_eval` read it. The radius
  at which the windowed supremum is small has to be **produced** and cannot be
  chosen, because `distWith` is not monotone in it; that is the same
  non-monotonicity for which Milestone 4 integrates.
* `SkorokhodSpace.continuous_eval_of_nhdsGT_eq_bot`: at a point with nothing
  immediately above it, evaluation *is* continuous. Proved (2026-09-09). Both
  displacements above are below the isolation radius, so `e t ≤ t` and
  `e.symm t ≤ t`, and the second with monotonicity gives `e.symm t = t`.
* `SkorokhodSpace.lowerSemicontinuous_iSup_edist`: `f ↦ ⨆ s ∈ ball t ρ ∩ Ioi t,
  edist (f s) y` is lower semicontinuous. Proved (2026-09-09). The supremum is
  `ℝ≥0∞` valued, as `modulus` is, so that the empty window and an unbounded
  family are both the supremum and not a junk value.
* `SkorokhodSpace.iInf_iSup_edist_eq`: at a point that is not right isolated,
  the infimum of those suprema over shrinking windows is `edist (f t) y`. Proved
  (2026-09-09). Right continuity is spent here and in both directions.
* `SkorokhodSpace.measurable_eval`: `f ↦ f t` is Borel measurable for every `t`.
  Proved (2026-09-09), by the two cases above.
* `SkorokhodSpace.measurableEmbedding_piDense`: for countable `D ⊆ ι` that is
  dense **from the right** — `∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot` — the map
  `f ↦ (fun t : D ↦ f t)` into `D → E` is a measurable embedding. Proved
  (2026-09-09). Plain density is **not** enough, and the second acceptance
  example below is the refutation; it stood here from 2026-09-07 while the Lean
  statement asked for `Dense D`, and it is the second time an acceptance example
  that was never run against its own statement caught a false commitment.
* `exists_countable_rightDense`: a countable right dense set exists. Proved
  (2026-09-09), so the hypothesis above is not vacuous. The right isolated
  points are countable — each carries a basic open set of which it is the
  greatest element — and adjoining them to a countable dense set is enough.
* `SkorokhodSpace.borel_eq_iSup_comap_eval`:
  `borel (D ι E) = ⨆ t, MeasurableSpace.comap (eval t) (borel E)`. Proved
  (2026-09-09), one inclusion from `measurable_eval` and the other from the
  embedding at a countable right dense set.
* Consequences, each stated separately: a Borel probability measure on `D ι E`
  is determined by its finite dimensional distributions along a countable dense
  set; a map into `D ι E` is measurable if and only if all its coordinates along
  such a set are; two processes with paths in `D ι E` that are modifications of
  each other induce the same law.

**Acceptance examples.**

* **Measurable but not continuous, on one path.** `f = Set.indicator (Set.Ici 1) 1`
  in `D ℝ ℝ`. `measurable_eval 1` holds, while `continuousAt_eval 1` fails at
  this `f` by the example of Milestone 4. The two items are therefore not the
  same statement, and a proof of `measurable_eval` that went through continuity
  is refuted here; the route is `eq_of_eqOn_dense` of Milestone 2 instead.
* **The maximal point must be in `D`.** On `ι = Set.Icc (0:ℝ) 1` with
  `D = Set.Ico (0:ℝ) 1 ∩ ℚ`, the paths `0` and `Set.indicator {1} 1` are both
  càdlàg and agree on `D`, so `f ↦ (fun t : D ↦ f t)` is not injective and
  `measurableEmbedding_piDense` is false for that `D`. With `D` replaced by
  `(Set.Ico (0:ℝ) 1 ∩ ℚ) ∪ {1}` it holds. This is Milestone 2's witness read as
  a statement about the σ-algebra, and it is the acceptance test for the
  hypothesis on `D`. **It caught one:** from 2026-09-07 to 2026-09-09 the Lean
  statement asked for `Dense D` and was false, with this example standing
  underneath it unread. The hypothesis is now right density,
  `∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot`, which `(Set.Ico 0 1 ∩ ℚ) ∪ {1}`
  satisfies and `Set.Ico 0 1 ∩ ℚ` does not.
* **The law of a Poisson process is fixed by rational times.** `ι = Set.Ici (0:ℝ)`,
  `E = ℝ`, `D = ℚ ∩ ι`. Two laws on `D ι ℝ` whose finite dimensional
  distributions along `D` are those of a Poisson process of rate `1` are equal,
  by `borel_eq_iSup_comap_eval` along a countable dense set. The times at which
  the process jumps are almost surely irrational, so no coordinate in `D` sees a
  jump: the example shows the conclusion does not need the coordinates to
  determine the paths pointwise, only the σ-algebra.

## Milestone 7: the modulus and compactness

* `SkorokhodSpace.IsSubdivision t₀ m δ (t : Fin (n+1) → ι)`: the subdivision
  predicate, `StrictMono t` with `t 0 ≤ (B m).min`, `(B m).max ≤ t (Fin.last n)`
  and `δ < dist (t i.castSucc) (t i.succ)` for every `i`. Written (2026-09-08),
  corrected (2026-09-09). It is a named predicate and not an existential inside
  the modulus, so that the infimum below ranges over a `Prop` and needs no
  `BddBelow`. The subdivision **covers** the window, its endpoints are not
  pinned to the window's: Ethier–Kurtz's partition of `[0,T]` (their (3.6.2))
  admits `0 = t₀ < ⋯ < t_{n-1} < T ≤ t_n`, an overshoot at the far end, and on
  a two-sided index the mirror freedom at the near end is needed too.
* `SkorokhodSpace.IsSubdivisionPinned` and `SkorokhodSpace.modulusPinned`: the
  form the two carried until 2026-09-09, with `t 0 = (B m).min` and
  `t (Fin.last n) = (B m).max`. They are kept because the refutation below is a
  theorem and a theorem needs a subject.
* `SkorokhodSpace.modulus_le_modulusPinned`: the correction only lowers the
  modulus, so every upper bound proved of the pinned form survives. Proved
  (2026-09-09).
* `SkorokhodSpace.le_modulusPinned_of_dist_exhaustionMin_le`: **the defect of the
  pinned form.** A pinned subdivision starts at `(B m).min` and its first gap
  exceeds `δ`, so every point of the window within `δ` of that edge lies in the
  first cell, whose oscillation is measured from the edge; the pinned modulus
  therefore charges, for every `δ` and undiminished, the whole jump of `f`
  between the window's left edge and any point that close to it. Proved
  (2026-09-09). Nothing like it holds at the right edge, the cells being
  `Set.Ico`; the two ends of the window are not symmetric, here as in
  `volume_radius_exhaustionMin_mem_Ico`.
* `SkorokhodSpace.not_tendsto_iSup_modulusPinned`: **`isCompact_closure_iff` with
  the pinned modulus is false.** In `D(ℝ, ℝ)` the step paths
  `stepAt (1/(n+2) - 1) 1 0` converge to `stepAt (-1) 1 0`, so
  `A = insert (stepAt (-1) 1 0) (range …)` is compact and takes only the values
  `0` and `1`; but the jump of the `n`-th path sits at distance `1/(n+2)` to the
  right of the left edge `-1` of `B 1`, so its pinned modulus at `δ` is at least
  `1` as soon as `1/(n+2) ≤ δ`, and the supremum over `A` is at least `1` for
  every `δ > 0`. Proved (2026-09-09), and it is the reason the endpoints of
  `IsSubdivision` are inequalities.
* The witness is assembled from `TimeChange.scale hc` (the scaling `x ↦ c * x`
  of `ℝ`, which fixes the base point and has `norm ≤ -Real.log c` for `c ≤ 1`),
  `exhaustionMin_real`, `clamp_real`, `clamp_real_le_iff`,
  `SkorokhodSpace.distWith_scale_stepAt_le_zero` (the scaling carries one step
  path exactly onto the other at every radius outside `Set.Ioc (1-ε) 1`),
  `SkorokhodSpace.intWith_scale_stepAt_le`, `SkorokhodSpace.intDist_stepAt_le`
  (`≤ max (-Real.log (1-ε)) (2 ε)`) and
  `SkorokhodSpace.tendsto_stepAt_shift`. All proved (2026-09-09). The bad radii
  are an interval of length `ε` and the integral metric pays exactly their
  measure — the same accounting as in `intWith_le_of_ae_distWith_le`.
* `SkorokhodSpace.subdivisionOsc f t`, the oscillation of `f` over the half open
  cells `Set.Ico (t i.castSucc) (t i.succ)`, measured from the left endpoint of
  each cell. Written (2026-09-08). The cells are `Set.Ico` and not `Set.Icc`:
  the jump of a càdlàg path sits at the left endpoint of the next cell, and a
  modulus that saw it from the previous one would not tend to `0` for any step
  function.
* `SkorokhodSpace.modulus t₀ m f δ = ⨅ n, ⨅ t, ⨅ _ : IsSubdivision t₀ m δ t,
  subdivisionOsc f t`, Billingsley's `w'`: the least oscillation achievable by a
  `δ`-sparse subdivision of the window. Written (2026-09-08), and **it is
  `ℝ≥0∞` valued**. The reason is the empty case and it is not cosmetic: once `δ`
  reaches the diameter of the window there is no `δ`-sparse subdivision at all,
  not even the trivial one from the least to the greatest point, so the infimum
  is over the empty set. Over `ℝ` that is the junk value `0`, `modulus` is then
  `0` for all large `δ`, the monotonicity below is false and `tendsto_modulus`
  says nothing. Over `ℝ≥0∞` it is `⊤`, which is the classical convention. The
  same choice pays a second time in `isCompact_closure_iff`, where
  `⨆ f ∈ A, modulus …` over an unbounded family would again be a junk `0`.
* `SkorokhodSpace.tendsto_modulus`: `modulus m f δ → 0` as `δ → 0`, for each
  fixed `f` and `m`. This is the càdlàg property in quantitative form. Proved
  (2026-09-08) out of `IsCadlag.exists_subdivision` of Milestone 2 and one
  observation: the gaps of a strictly monotone subdivision are finitely many and
  each positive, so some `δ₀ > 0` lies below all of them, and every `δ < δ₀`
  admits that same subdivision as a `δ`-sparse one.
* `modulus` is monotone in `δ` and in `m`. `SkorokhodSpace.modulus_mono`, the
  monotonicity in `δ`, is proved (2026-09-08): a `δ₂`-sparse subdivision is
  `δ₁`-sparse for every smaller `δ₁`, so the infimum runs over a larger set.
  This is the item the `ℝ≥0∞` valuation buys.
* `SkorokhodSpace.modulus_eq_zero_of_exhaustion_subsingleton`: on a one point
  window the modulus vanishes for every `δ`, since the empty subdivision `n = 0`
  is admissible and has no cells. Proved (2026-09-08). It is the one value of
  `modulus` available before `tendsto_modulus`, and it fixes the orientation of
  the definition: with `Set.Icc` cells, or with the oscillation taken between
  the subdivision points rather than inside the cells, the empty subdivision
  would not be admissible and it would fail.
* `SkorokhodSpace.exists_radius_distWith_lt`: if `intWith t₀ l f g` is below
  `exp (-(M+1)) * c` with `0 < c ≤ 1`, then *some* radius `u ∈ Set.Ioc M (M+1)`
  has `distWith t₀ u l f g < c`. Proved (2026-09-09). It is the mean value of the
  integral over a window of measure one, and the radius is **produced and not
  named**, `distWith` being non-monotone in it — that non-monotonicity is why
  Milestone 4 integrates over the radius rather than summing. Shared with
  Milestone 6, where it stood inline inside
  `exists_orderIso_dist_lt_of_intDist_lt` until it was extracted here.
* `SkorokhodSpace.exists_timeChange_distWith_lt_of_intDist_lt`: the bridge from
  the metric to a uniform estimate on a *named* window — below a threshold
  depending only on `M` and `ε`, closeness in `intDist` yields a time change of
  norm below `ε` and a radius above `M` at which the windowed supremum is below
  `ε`. Proved (2026-09-09).
* `SkorokhodSpace.edist_le_ofReal_distWith`: `distWith` read as a bound on one
  pair of values, the two clamps of `dist_le_distWith` dropping as soon as the
  point *and its image* lie in the window. Proved (2026-09-09).
* `SkorokhodSpace.isSubdivision_comp`: **the image of a subdivision is a
  subdivision.** A `δ`-sparse subdivision of `B u'`, pushed forward by a time
  change of norm at most `γ` fixing the base point, is `exp (-γ) * δ`-sparse on
  `B u` whenever `u + (exp γ - 1) * 2u ≤ u'`. Proved (2026-09-09). The
  sparseness is `TimeChange.dist_le_exp_norm_mul` read on `l⁻¹`; the covering is
  `TimeChange.dist_le_of_norm_le` applied to `l⁻¹` at the two ends of the small
  window, giving two points of the large one, and then `isLeast_exhaustionMin`
  and `isGreatest_exhaustionMax`. That argument carries the degenerate index
  without naming it: an order isomorphism fixes a least element, so where the
  index has no room the estimate is vacuous.
* `SkorokhodSpace.subdivisionOsc_comp_le`: the oscillation survives the
  transport up to `2 η`, where `η` bounds `edist (f (l x)) (g x)` on a window
  holding the nodes — once for the point inside the cell, once for its left
  endpoint. Proved (2026-09-09). The half open cells are what makes it exact:
  `l` maps `Set.Ico (t i) (t (i+1))` *onto* `Set.Ico (l (t i)) (l (t (i+1)))`.
* `SkorokhodSpace.modulus_le_of_edist_le`: the three put together —
  `modulus t₀ u f δ' ≤ subdivisionOsc g t + 2 η`. Proved (2026-09-09). This is
  the engine of the forward half: **one** subdivision of **one** nearby path
  bounds the modulus of **every** path close to it.
* `SkorokhodSpace.tendsto_iSup_modulus_of_isCompact`: **the forward half, for the
  modulus.** Compact closure gives `sup_{f ∈ A} modulus basePoint m f δ → 0`.
  Proved (2026-09-09). It is Arzelà–Ascoli's argument: total boundedness gives
  finitely many centres, `IsCadlag.exists_subdivision` gives each of them a
  subdivision of oscillation at most `ε'`, and `modulus_le_of_edist_le` carries
  it to the whole ball. The *sparseness* surviving the transport is what makes
  finitely many centres enough — one `δ` then serves all of `A`.
* Four radii appear in that proof and they are nested for a reason: the modulus
  is asked for on `B m`; the subdivision is taken on `B (m+1)`, which is the room
  the time change needs to displace the window's two ends; the nodes live there,
  so that is where the uniform estimate must hold; and the radius supplied by
  `exists_radius_distWith_lt` is above `m + 2`, because the time change must map
  `B (m+1)` *into* the window before `edist_le_ofReal_distWith` may drop its
  clamps. The one quantity fitting all four is `γ` with
  `(exp γ - 1) * (2 (m+1)) ≤ 1`.
* `exists_mem_Ico_of_strictMono`: the cells of a subdivision cover its half open
  span — every `x` with `t 0 ≤ x < t (Fin.last n)` lies in some
  `Set.Ico (t i.castSucc) (t i.succ)`. Proved (2026-09-09), for a bare
  `LinearOrder`, nothing else being used. The induction splits at the *last* node
  and not the first: the cells being `Set.Ico`, `x` either lies below the last
  node, and the shorter subdivision catches it, or it lies in the final cell;
  splitting at the first node would leave the half open final cell nameless.
* `IsCadlag.totallyBounded_image_Icc`: a càdlàg path has totally bounded image on
  a compact window. Proved (2026-09-09). It is `IsCadlag.exists_subdivision` and
  `exists_mem_Ico_of_strictMono`: off the nodes the path stays within `ε` of one
  of the finitely many node values, and the right endpoint is itself a node. Total
  boundedness and not relative compactness is the conclusion, because no
  completeness of `E` is used.
* `SkorokhodSpace.totallyBounded_values_of_isCompact`: the other conjunct of the
  forward half, that `{f t | f ∈ A, t ∈ B m}` is totally bounded. Proved
  (2026-09-09). It rests on the same total boundedness of `A` as the modulus
  half, on the previous item for each of the finitely many centres, and on
  `exists_timeChange_distWith_lt_of_intDist_lt` to carry a value of a path of the
  ball to a value of its centre. The value is read at `y` and the centre's at
  `l⁻¹ y`, which is why the centres' windows have radius `m + 1`.
* `SkorokhodSpace.isCompact_closure_values_of_isCompact`: the same under
  `CompleteSpace E`, with compact closure. Proved (2026-09-09). This is the one
  place in the criterion where the completeness of the *given* metric is used;
  `PolishSpace E` grants only that the topology comes from some complete metric,
  and that does not suffice to turn total boundedness into compact closure.
* `SkorokhodSpace.not_isCompact_closure_of_rigid`: **the converse of the criterion
  is false for a general index.** Proved (2026-09-09). If the only time change of
  norm below `c > 0` is the identity and an uncountable set `S` of jump times
  keeps its distance `η` from every window end, then the family `stepAt x a b`,
  `x ∈ S`, satisfies *both* conditions — two values, and the subdivision made of
  the two window ends with `x` between them has no oscillation at all — and is
  `r`-separated by `le_intDist_stepAt`, hence not totally bounded. The witness is
  the middle thirds Cantor set of `not_separableSpace_of_rigid`, with `S` its part
  in `Set.Icc (1/4 : ℝ) (3/4)`, `η = 1/4`, `N = 1` and `c = Real.log 3`; as there,
  the rigidity is a computation on paper and stands as a hypothesis.
* `SkorokhodSpace.dist_le_distWith_stepAt_of_exp_norm_mul_lt`,
  `SkorokhodSpace.le_intWith_stepAt_of_exp_norm_mul_lt` and
  `SkorokhodSpace.le_intDist_stepAt_of_exp_mul_lt`: **the separation of two step
  paths without a rigidity hypothesis.** If `t₀ ≤ x < y` and a time change fixing
  `t₀` has `exp ‖l‖ * dist t₀ x < dist t₀ y`, then `l⁻¹ x` still lies below `y`
  and the two paths are `dist a b` apart there; so either the time change costs
  `c` or the integral sees `exp (-dist t₀ y) * min 1 (dist a b)`. Proved
  (2026-09-09). It is the quantitative form of the fact that the metric fixes the
  base point: near `t₀` the admissible time changes are short, so what is
  preserved there is a *ratio* of distances and not a distance.
* `SkorokhodSpace.not_isCompact_closure_of_jumps_at_basePoint`: **the converse of
  the criterion is false over `ℝ` too**, for a modulus whose subdivisions may
  avoid the base point. Proved (2026-09-09), with no hypothesis left on paper.
  The family is `stepAt ((1/4)^(k+1)) a b`, its jump times accumulating at the
  base point: two values, and the subdivision `-(m+1) < (1/4)^(k+1) < m+1` is
  `δ`-sparse for every `δ < 3/4` with no oscillation at all, so both conditions
  hold; but the previous item makes it `r`-separated with
  `r = min (log 2) (exp (-1) * min 1 (dist a b))`, and an infinite `r`-separated
  set is not totally bounded.
* `SkorokhodSpace.IsSubdivisionBased`, `SkorokhodSpace.modulusBased` and
  `SkorokhodSpace.modulus_le_modulusBased`: the repair, and it is Ethier–Kurtz's
  own. Their partition of `[0,T]` begins at `0`, where the base point, the left
  end of the index and the left end of every window coincide; on a two-sided
  index those come apart and what the criterion needs is the base point **among
  the nodes**, `t₀ ∈ Set.range t`. Written (2026-09-09). It separates the two
  refutations correctly: the family just above is rejected, the cell starting at
  `t₀` being wider than `δ` and swallowing the jump, while the family of
  `not_tendsto_iSup_modulusPinned`, whose jumps march to the window's *edge*, is
  still accepted by the subdivision `-m-1 < jump < 0 < m+1`.
* `SkorokhodSpace.isCompact_closure_iff`, **over the index `ℝ` and with
  `modulusBased`**: `A ⊆ D ℝ E` has compact closure if and only if for every `m`
  the set `{f t | f ∈ A, t ∈ B m}` has compact closure in `E` and
  `lim_{δ→0} sup_{f ∈ A} modulusBased m f δ = 0`. Only the converse is index
  bound, by `not_isCompact_closure_of_rigid`, and it is stated where it is true
  rather than under a class invented to make it true. `HasCountableCore ι` would
  exclude that witness but is the class of *separability*: it yields a countable
  family of step paths, and total boundedness asks for a finite one. The window is
  the one around `basePoint` and not around a free `t₀`: the left hand side speaks
  of the topology of `D ℝ E`, which is `SkorokhodSpace.metricSpaceInt basePoint`,
  and a `t₀` free to differ from it would make the two sides speak of two spaces.
  Three forms of the modulus have been tried and two are refuted theorems of this
  file — pinned to the window's edges by `not_tendsto_iSup_modulusPinned`, free of
  the base point by `not_isCompact_closure_of_jumps_at_basePoint`.
* `IsCadlag.exists_subdivision_through`: a càdlàg subdivision of `Set.Icc a b`
  through a prescribed interior point `c`, with cell oscillation at most `ε`.
  Proved (2026-09-09). It is `IsCadlag.exists_subdivision` twice, on `[a,c]` and
  on `[c,b]`, and the two `Fin` tuples concatenated at their common endpoint —
  which is what carries the strictness of the monotonicity across the seam
  (`t₁ i ≤ t₁ (last n) = c = t₂ 0 < t₂ (j-n)`) and what makes the cell at the
  seam be `[c, t₂ 1)`, the zeroth cell of `t₂`, with no case distinction. Both
  halves of the criterion read it: the forward
  half because the argument of `tendsto_iSup_modulus_of_isCompact` transports
  through `isSubdivision_comp`, which carries a node at `t₀` to a node at `t₀`,
  and needs only its *input* to carry one; the converse because the finite net is
  built from a grid whose cell at the base point is what the refutation above
  shows must be there.
* `SkorokhodSpace.tendsto_modulusBased`: the based analogue of
  `tendsto_modulus`, out of the previous item. Proved (2026-09-09). The base
  point is admissible as the prescribed node because it lies in every window
  (`mem_exhaustion_self`), so nothing is assumed about the radius; and the extra
  node costs nothing quantitatively, the gaps of the refined subdivision being
  still finitely many and still positive.
* `SkorokhodSpace.isSubdivisionBased_comp` and
  `SkorokhodSpace.modulusBased_le_of_edist_le`: the based analogues of
  `isSubdivision_comp` and `modulus_le_of_edist_le`. Proved (2026-09-09). The
  first is the second plus one line, and that line is why the correction is
  affordable at all: the time changes over which the metric of Milestone 4 takes
  its infimum fix the base point, so a node at `t₀` goes to a node at `t₀`. Under
  an unbased metric the based modulus would not be transportable.
* `SkorokhodSpace.tendsto_iSup_modulusBased_of_isCompact`: the forward half for
  the based modulus. Proved (2026-09-09). `modulus ≤ modulusBased` runs the wrong
  way, so the estimate proved for `modulus` does not transfer and the
  Arzelà–Ascoli argument is repeated on based subdivisions; every step of it
  survives unchanged, and only its input moves from
  `IsCadlag.exists_subdivision` to `IsCadlag.exists_subdivision_through`. With
  `isCompact_closure_values_of_isCompact` this closes the forward direction of
  `isCompact_closure_iff`, and the remaining `sorry` of the file is the converse
  alone.
* `dist_first_last_eq_sum`: under `AdditiveDist ι` the gaps of a monotone tuple
  telescope, `dist (t 0) (t (Fin.last n)) = ∑ i, dist (t i.castSucc) (t i.succ)`.
  Proved (2026-09-09). Monotonicity is the real hypothesis — strictness is not
  used — and it is needed: without it `dist` is only subadditive and the identity
  becomes an inequality in the useless direction.
* `mul_le_dist_first_last` and `mul_le_dist_of_sparse`: a `δ`-sparse monotone
  tuple spans at least `n * δ`, and any two of its nodes are at least their index
  gap times `δ` apart. Proved (2026-09-09). The second is the first applied to
  the sub-tuple between the two nodes, and it is the form the converse consumes,
  where the two nodes are the extreme ones lying *inside* a window.
* `SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision`: **the bound on the number
  of nodes.** For two nodes of a `δ`-sparse subdivision that lie in the window of
  radius `u`, the gap between their indices is at most `2u / δ`. Proved
  (2026-09-09), and stated as an inequality rather than as a cardinality so that
  it carries no `Nat` division. Nothing forbids a subdivision from placing nodes
  far outside the window — `IsSubdivision` only asks that it *cover* it — and
  those nodes are not counted, which is why the statement quantifies over two
  nodes known to lie inside.
* `SkorokhodSpace.abs_sum_tent_sub_le`: **a sum of tents with separated centres
  is `2 η / r`-Lipschitz, whatever their number.** Proved (2026-09-09). This is
  *not* the estimate `exists_rat_nodes_perturbation` uses, and the difference is
  the whole reason the converse needs its own lemma: that proof bounds the sum
  term by term, `∑ᵢ |vᵢ| / r`, which grows with the number of tents, and it can
  afford to because there the height is chosen **after** the number of nodes is
  known. The converse cannot — its grid is fixed before the path is seen, so the
  height is the grid spacing and the number of nodes is whatever the path's
  subdivision has. What saves it is that the supports are disjoint: at any point
  at most one tent is nonzero, so the difference has at most **two** nonzero
  terms, one for each argument, however many tents there are. The `2` is the
  price of not knowing which argument sits in which support.
* `SkorokhodSpace.abs_sum_tent_le`: the displacement estimate going with the
  previous item — such a sum is bounded by the bound on its coefficients,
  whatever the number of tents. Proved (2026-09-09), by the same disjointness of
  the supports.
* `SkorokhodSpace.exists_finite_grid_timeChange`: **the grid of the converse,
  together with the time change onto it.** To a sparseness `δ`, a norm budget `γ`
  and a radius `u` there is **one finite** set `G ∋ 0` of reals such that every
  `δ`-sparse strictly monotone tuple carrying `0` among its nodes is moved onto
  `G` — as far as its nodes lie in `B u` — by a time change of norm at most `γ`
  which displaces no point of `ℝ` by more than `γ`. Proved (2026-09-09). The
  order of the quantifiers is the content: `G` is produced from `δ`, `γ` and `u`
  alone, before any tuple is seen, which is what a *finite* net needs and what
  `exists_rat_nodes_perturbation` — producing countably many nodes, and only
  after seeing the tuple — does not give. The construction is the same
  perturbation `x ↦ x + ψ x` as in `Real.instHasCountableCore`, with `ℚ` replaced
  by `ρ ℤ` truncated to `B (u + γ)`; the constants close in one direction, the
  tents having radius `δ / 4` and height `ρ / 2`, so `ψ` is `4 ρ / δ`-Lipschitz
  and `ρ` is chosen last, under `(1 - exp (-γ)) δ / 4`. The base point is a node
  and stays one: `0` is itself a grid point, so its tent carries the coefficient
  `0` and every other tent vanishes there — without which the time change would
  leave `TimeChange.fixing 0` and the metric of Milestone 4 would not see it,
  which is where `not_isCompact_closure_of_jumps_at_basePoint` bites.
* `SkorokhodSpace.stepPathFamilyLe`, `SkorokhodSpace.finite_stepPathFamilyLe`,
  `SkorokhodSpace.stepPath_mem_stepPathFamilyLe` and
  `SkorokhodSpace.stepPathFamilyLe_subset_stepPathFamily`: the **finite**
  analogue of `stepPathFamily` and its counting, the length being bounded by a
  prescribed `n₀`. Written and proved (2026-09-09). Without the bound on the
  length the family is an infinite union even over a single node set; what
  supplies the bound is `sub_mul_le_two_mul_of_isSubdivision`.
* The converse's proof is the finite net: for `ε` take `m` with `exp (-m) < ε`,
  then `δ` from the modulus condition, then for each path a `δ`-sparse based
  subdivision of oscillation below `ε`; its nodes are pushed onto the finite grid
  of `exists_finite_grid_timeChange` — this is where `ℝ` is used and where the
  rigid index fails — and its values onto a finite net of the value compactum.
  The approximant is `SkorokhodSpace.stepPath`, it is counted by
  `finite_stepPathFamilyLe`, the bound is
  `SkorokhodSpace.distWith_stepPath_le`, and the passage from the window to the
  integral is `SkorokhodSpace.intWith_le_of_ae_distWith_le`. The bound on the
  *number* of nodes is `SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision`. The
  grid holds the base point, and the displacement of a node is bounded by a
  fraction of its distance to the base point rather than by an absolute amount:
  that is what `le_intDist_stepAt_of_exp_mul_lt` shows to be necessary. What
  remains is the assembly, and in it the two window ends, which are
  `SkorokhodSpace.exists_bad_radii_set` and `intWith_le_of_ae_distWith_le`.
* `SkorokhodSpace.exists_bad_radii_set` **with the nodes outside the window not
  counted**: its measure bound is `(n + 1) (2 δ + (exp δ - 1) 2 M)` over the
  whole length, and `n` is unbounded over a family — `IsSubdivision` asks only
  that the subdivision cover the window, so a node may sit arbitrarily far
  outside. The count has to run over the nodes whose coordinate interval meets
  `Set.Ioc 0 M` instead, and those are bounded in number by
  `sub_mul_le_two_mul_of_isSubdivision`, uniformly over the family, once `δ` is
  fixed by the modulus condition. The far nodes contribute nothing: their
  intervals sit around their own coordinate. This is what the converse needs
  before the assembly, and the order of the choices is then `δ`, then the node
  count, then the norm budget `γ` and with it the grid spacing `ρ`.
* `SkorokhodSpace.isCompact_closure_of_compactContainment`: the sufficient form
  used in practice, over `ℝ`, where the first condition is replaced by the
  existence of a compact `K ⊆ E` with `f t ∈ K` for all `f ∈ A` and `t ∈ B m`.

**Acceptance examples.**

* **One jump costs nothing.** `f = Set.indicator (Set.Ici 1) 1` on `ι = ℝ` with
  `t₀ = 0` and `m = 2`. For `δ < 1` the subdivision `-2 < 1 < 2` has all gaps
  larger than `δ` and `f` is constant on each `Set.Ico`, so
  `modulus 2 f δ = 0`. This is the point of the `Ico` in the definition: a
  modulus built on `Set.Icc`, or one that measured oscillation across the
  subdivision points, would return `1` here and `tendsto_modulus` would be
  false for every step function.
* **Infinitely many jumps still give `tendsto_modulus`.** The accumulating path
  `f = ∑' n, 2⁻¹ ^ n * Set.indicator (Set.Ici (1/(n+1))) 1` of Milestone 2 on
  `ι = Set.Icc (0:ℝ) 1`. For `δ` small the subdivision takes the finitely many
  jump times of height at least `ε` and lumps the rest into one interval next to
  `0`, where the total variation is at most `ε`; so `modulus m f δ → 0` although
  no subdivision separates all the jumps. A proof by "finitely many jumps"
  fails on this path.
* **The two jumps that cannot merge, as a compactness test.**
  `A = {Set.indicator (Set.Ici 1) 1 + Set.indicator (Set.Ici (1 + 1/n)) 1 | n}`.
  Every value lies in the compact `{0, 1, 2}` and the family is uniformly
  bounded, so any criterion phrased on the values alone accepts it; but for
  `δ ≥ 1/n` no admissible subdivision separates the two jump times, so
  `sup f ∈ A, modulus m f δ ≥ 1` for every `δ > 0` and the closure is not
  compact — as it must not be, the sequence having no convergent subsequence
  (Milestone 4). This is the instance that makes the modulus condition
  indispensable in `isCompact_closure_iff`.
* **The jump that marches to the window's edge, and why the endpoints are not
  pinned.** `A = insert (stepAt (-1) 1 0) {stepAt (1/(n+2) - 1) 1 0 | n}` in
  `D(ℝ, ℝ)`, window `B 1 = [-1, 1]`. The sequence converges, so `A` is compact,
  and the values lie in `{0,1}`; the corrected modulus is `0` for every `δ < 1/2`
  by the subdivision `-2 < 1/(n+2) - 1 < 2`, which *undershoots* the window at
  the near end. Pin the endpoints and the same subdivision is inadmissible, the
  jump is trapped in the first cell and the supremum of the moduli is `1` for
  every `δ > 0`: `SkorokhodSpace.not_tendsto_iSup_modulusPinned`. This is the
  instance that fixes the endpoints of `IsSubdivision` as inequalities, and it is
  the mirror of the previous one — there the criterion must reject, here it must
  accept.
* **A family that does have compact closure.**
  `A = {Set.indicator (Set.Ici a) 1 | a ∈ Set.Icc 1 2}`. The values lie in
  `{0,1}` and `modulus m f δ = 0` for `δ` smaller than the distance from `a` to
  the window ends, uniformly in `a` once the window is `B m` with `m ≥ 3`; so
  both conditions hold and the closure is compact. It is: the closure is the
  continuous image of `Set.Icc 1 2` under `a ↦ Set.indicator (Set.Ici a) 1`,
  which is where the sliding step example of Milestone 4 says the map is
  continuous.
* **The same family on a rigid index, where the criterion must not be stated.**
  `A = {stepAt x 1 0 | x ∈ C ∩ Set.Icc (1/4 : ℝ) (3/4)}` with `C` the middle
  thirds Cantor set as index and base point `0`. Both conditions hold exactly as
  in the previous example — two values, and the subdivision `0 < x < 1` has no
  oscillation for `δ < 1/4` — but `a ↦ stepAt a 1 0` is not continuous here and
  cannot be: no time change of norm below `log 3` moves anything, so the family is
  uncountable and uniformly separated and its closure is not compact
  (`SkorokhodSpace.not_isCompact_closure_of_rigid`). The pair of these two
  examples is what confines `isCompact_closure_iff` to `ℝ`: the criterion sees
  only values and times, and on a rigid index that is not enough to count the
  paths.
* **The jump that marches to the base point, and why the subdivision is based.**
  `A = {stepAt ((1/4)^(k+1)) 1 0 | k}` in `D(ℝ, ℝ)` with base point `0`. Every
  value lies in `{0,1}`, and for `δ < 3/4` the subdivision `-(m+1) < (1/4)^(k+1) <
  m+1` is admissible with no oscillation, so an unbased modulus is `0` for the
  whole family and every window. The closure is nevertheless not compact: a time
  change fixing `0` moves a point by a bounded *ratio* of its distance to `0`, so
  jump times differing by the factor `4` are uniformly separated
  (`SkorokhodSpace.not_isCompact_closure_of_jumps_at_basePoint`). Demand `0`
  among the nodes and the family is rejected — the cell starting at `0` is wider
  than `δ` and carries the whole jump — while the previous example, whose jumps
  approach the window's edge and not `0`, is still accepted. These two are the
  pair that fixes the modulus of the criterion: one forbids pinning at the
  window's edges, the other forbids ignoring the base point, and no third
  condition is left.

## Milestone 8: tightness and convergence of finite dimensional distributions

Here `μ n` and `μ` are Borel probability measures on `D ι E`, with `ι` the
index of Milestone 1; the roadmap **WeakConvergence** supplies separating
classes, the Skorokhod representation theorem and the continuous mapping
theorem, and its Milestone 5 supplies the functional monotone class theorem.
Like Milestone 2, this milestone states its hypotheses on `E` item by item, in
two stages.

**(A)** `E` a separable metric space. Convergence of laws and the whole theory
of finite dimensional distributions live here. Prokhorov in the direction from
tightness to relative compactness belongs here as well:
`isCompact_closure_of_isTightMeasureSet`
(`Mathlib/MeasureTheory/Measure/Prokhorov.lean`, root namespace) asks for
`[T2Space E]` and `[BorelSpace E]` and nothing further.

**(B)** `E` Polish. Two points, and only two: the characterization of tightness
by the modulus and the reduction to real-valued paths. Both pass through
Prokhorov in the other direction, from compactness to tightness, and
`MeasureTheory.isTightMeasureSet_of_isCompact_closure` in the same file carries
`[CompleteSpace 𝓧]` and `[SecondCountableTopology 𝓧]` for it. Ethier–Kurtz
state the second, as Theorem 3.9.1, for a complete separable `E` as well.

* `SkorokhodSpace.isTightMeasureSet_iff` — stage (B). A set of laws is tight if
  and only if for every `ε > 0` and `m` there are a compact `K ⊆ E` and a
  function `δ ↦ η δ` tending to `0` with
  `μ {f | ∀ t ∈ B m, f t ∈ K} ≥ 1 - ε` and
  `μ {f | modulus m f δ ≥ η δ} ≤ ε`, uniformly over the set. Combine
  Milestone 7 with `MeasureTheory.isTightMeasureSet_of_isCompact_closure` and
  its converse `isCompact_closure_of_isTightMeasureSet`; the completeness of
  `E` is what the first of the two asks for.
* `SkorokhodSpace.tendsto_finiteDimensional_of_tendsto` — stage (A). If
  `μ n → μ` weakly then, for every finite family `t 1, ..., t k` of points at
  which the limit has no fixed discontinuity — that is
  `μ {f | f⁻ (t i) = f (t i)} = 1` — the finite dimensional distributions
  converge. The set of `t` failing this is countable. The proof runs through
  the Skorokhod representation theorem (**WeakConvergence** Milestone 3) and
  the continuous mapping theorem (Milestone 2 there), which is why separability
  suffices: Ethier–Kurtz state both, as Theorem 3.1.8 and Corollary 3.1.9, for
  a separable metric space and use the completeness in neither proof.
* `SkorokhodSpace.tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` —
  stage (A). Let `S : Set (ProbabilityMeasure (D ι E))` have compact closure,
  let every `μ n` lie in `S`, and let `T ⊆ ι` be dense and such that the finite
  dimensional distributions along every finite subset of `T` converge to those
  of `μ`. Then `μ n → μ` weakly. This is Ethier–Kurtz, Theorem 3.7.8(b), and
  the hypothesis there is relative compactness, not tightness: what the proof
  uses is a convergent subsequence and nothing else. That step is where
  separability is spent a second time: a compact set yields a convergent
  subsequence because `ProbabilityMeasure (D ι E)` is metrizable, by
  `MeasureTheory.instMetrizableSpaceProbabilityMeasure`
  (`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean:695`) applied to
  `SeparableSpace (D ι E)` of Milestone 5, which asks for a countable dense
  subset of `E` **and** for `SkorokhodSpace.HasCountableCore ι`, the second
  since 2026-09-09 and not droppable. Its ingredients, in the
  order the proof needs them: right continuity of the paths, to move the times
  of a finite family from `T` to the continuity points of the limit;
  `exists_countable_dense_continuity` below, which makes those continuity
  points dense; `borel_eq_iSup_comap_eval` of Milestone 6 in its form along a
  dense set; and `induction_on_mulSystem` (**WeakConvergence** Milestone 5) to
  pass from the integrals of the products `∏ i, f i (g (t i))`, with each `f i`
  bounded continuous, to the equality of the two laws. Products of a separating
  class, one per factor, do not enter: the law is identified on `D ι E` and not
  on a product space, and `eval t` is measurable rather than continuous there —
  the proof of Ethier–Kurtz, Proposition 3.7.1 obtains `f ∘ eval t` as a
  pointwise limit of continuous averages, which is exactly the gap.
* `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional` — stage (A).
  The same conclusion for a tight family, from the previous item and
  `isCompact_closure_of_isTightMeasureSet`.
* `SkorokhodSpace.exists_countable_dense_continuity` — stage (A). For a single
  `μ`, the set of `t` with `μ {f | f⁻ t = f t} = 1` has countable complement,
  hence contains a countable dense set.
* `SkorokhodSpace.continuous_postcomp` — stage (A). For continuous `h : E → E'` the induced
  map `SkorokhodSpace.postcomp h : D ι E → D ι E'`, `f ↦ h ∘ f`, is well defined
  and continuous; with `Measurable (postcomp h)` for `h` Borel, from Milestone 6.
  Together with `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` this is
  the continuous mapping theorem in the form the next item needs.
* `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` — stage (B). The
  reduction to
  real-valued paths. Let `S` be a set of Borel probability measures on `D ι E`
  satisfying compact containment — for every `ε > 0` and `m` a compact `K ⊆ E`
  with `μ {f | ∀ t ∈ B m, f t ∈ K} ≥ 1 - ε` for every `μ ∈ S` — and let
  `H ⊆ E →ᵇ ℝ` be dense in the topology of uniform convergence on compact sets.
  Then `S` is tight if and only if `(· .map (postcomp h)) '' S` is tight in
  `D ι ℝ` for every `h ∈ H`. The forward direction is the previous item; the
  converse is Milestone 7 applied to the modulus, which compact containment plus
  a dense `H` recovers from the real-valued moduli.

**Acceptance examples.**

* **The invariance principle, which is what the milestone is for.** This is the
  manuscript's `ex:invariance`: `E = ℝ^d`, `ι = Set.Ici (0:ℝ)`,
  `X n t = Ξ n ⌊n * t⌋` for a Markov chain `Ξ n` with one step kernel `P n`,
  each path a piecewise constant element of `D ι E`. The laws are tight by
  `isTightMeasureSet_iff`, their finite dimensional distributions converge to
  those of the limit, and
  `tendsto_of_isTight_of_tendsto_finiteDimensional` concludes weak convergence
  in `D ι E`. Every hypothesis of the milestone is instantiated once, and the
  conclusion is a statement one recognises.
* **The excluded times are not a technicality.**
  `μ n = δ (Set.indicator (Set.Ici (1 + 1/n)) 1)` and
  `μ = δ (Set.indicator (Set.Ici 1) 1)` in `D ℝ ℝ`. Then `μ n → μ` weakly, and
  the finite dimensional distributions converge at every finite family of times
  avoiding `1` and **fail** to converge at `t = 1`, where they are `δ 0` for
  every `n` and `δ 1` in the limit. So
  `tendsto_finiteDimensional_of_tendsto` must carry its hypothesis
  `μ {f | f⁻ (t i) = f (t i)} = 1`, which here holds exactly off `{1}` — a set
  that is countable, as `exists_countable_dense_continuity` claims, and not
  empty.
* **Compact containment alone is not tightness.**
  `S = {δ (Set.indicator (Set.Ici 1) 1 + Set.indicator (Set.Ici (1+1/n)) 1) | n}`.
  All paths take values in the compact `{0,1,2}`, so compact containment holds,
  and `S` is not tight, because the modulus condition of Milestone 7 fails on
  exactly this family. `isTightMeasureSet_iff` must have both clauses; the
  witness is the two jumps that cannot merge.
* **The converse of the reduction needs compact containment.** `E = ℝ`,
  `S = {δ (fun _ ↦ (n : ℝ)) | n}`, the laws of the constant paths at height `n`.
  For every bounded continuous `h : ℝ → ℝ` the image family
  `{δ (fun _ ↦ h n) | n}` lives in the compact set of constant paths with values
  in `closure (Set.range h)` and is tight; but `S` itself is not, no compact
  `K ⊆ ℝ` containing every `n`. So
  `isTightMeasureSet_iff_forall_postcomp` cannot drop the compact containment
  hypothesis, and this is the family that shows it.
