# The Skorokhod space

The space of càdlàg paths with the `J₁` topology. The space does not occur in
Mathlib. The *predicate* does: since #43352 the library carries
`Mathlib/Topology/Order/Cadlag.lean`, and Milestone 2 below is written against
it. What Mathlib does have, and what is **not** to be rebuilt:

* `Mathlib/Topology/Order/Cadlag.lean`: `IsRightContinuous` and `IsLeftContinuous`
  in the root namespace, defined as `∀ a, ContinuousWithinAt f (Set.Ioi a) a` and
  its mirror image; the structures `IsCadlag` and `IsCaglad`, whose fields are
  `isRightContinuous` and `tendsto_nhdsLT`; and the closure properties
  `Continuous.isCadlag`, `IsCadlag.const`, `IsCadlag.continuous_comp`,
  `IsCadlag.continuous_comp₂`, `IsCadlag.mul`, `IsCadlag.div'`,
  `IsCadlag.const_smul` with the corresponding `IsRightContinuous` lemmas. The
  basic section asks `[TopologicalSpace X] [Preorder X] [TopologicalSpace Y]` and
  nothing more, which is bundle (A) of Milestone 2 below. Under `[LinearOrder X]`
  and `[OrderTopology X]` come `IsCadlag.tendsto_nhdsLT_leftLim` and
  `IsCaglad.tendsto_nhdsGT_rightLim`; under `[LinearOrder X]` and
  `[PseudoMetricSpace Y]`, `IsCadlag.isLocallyBounded` and
  `isBounded_image_of_isCadlag_of_isCompact`.

  `MeasureTheory.Filtration.IsRightContinuous`
  (`Mathlib/Probability/Process/Filtration.lean:373`) is a different predicate,
  about a filtration rather than a function, and is older; the two share a name
  and nothing else.

* `Mathlib/Topology/Order/LeftRightLim.lean`: `Function.leftLim` and
  `Function.rightLim`, defined for `f : α → β` with `[LinearOrder α]` and
  `[TopologicalSpace β]`, together with the part of the one-sided-limit API that
  holds for an arbitrary `f`. That part is what every statement about left
  limits below is to be phrased through, and it is exactly:
  `tendsto_leftLim_of_tendsto` and `tendsto_rightLim_of_tendsto`, whose
  hypothesis is `∃ y, Tendsto f (𝓝[<] a) (𝓝 y)` and hence literally the
  `tendsto_nhdsLT` field of `IsCadlag`; `ContinuousWithinAt.leftLim_eq` and
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
  precedent for how a right continuity condition is bundled in Mathlib. Its
  field states right continuity as `ContinuousWithinAt f (Ici x) x`;
  `IsRightContinuous` uses `Ioi`, and `continuousWithinAt_Ioi_iff_Ici` is the
  bridge, the same one the proof of `StieltjesFunction.rightLim_eq` takes.
* Prokhorov's theorem, tightness and the Lévy–Prokhorov metric in
  `Mathlib/MeasureTheory/Measure/`, used in Milestone 8.
* `orderTopology_of_ordConnected` in `Mathlib/Topology/Order/Basic.lean`,
  `ProperSpace.of_isClosed`, and the instance that a discrete subgroup is
  closed, whose additive form is what the lattice instance of Milestone 1 needs.
  That instance carries two names: `Subgroup.isClosed_of_discrete` under
  `[T2Space G]` in `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` on
  v4.33.1, and `Subgroup.isClosed_of_discreteTopology` under the weaker
  `[T1Space G]` in `Mathlib/Topology/Algebra/OpenSubgroup.lean` afterwards, with
  the old name a deprecated alias beside it and the still more general
  `Subgroup.isClosed_of_isDiscrete` above it. The additive form is what is used
  here, and `T1` is all it consumes.

This roadmap depends on the roadmap **WeakConvergence** for separating and
convergence determining classes (Milestone 1 there), for the continuous mapping
theorem for almost everywhere continuous maps (Milestone 2 there), and for the
Skorokhod representation theorem (Milestone 3 there). Since 2026-09-18 the
dependency is an `import` and not only a citation: `Suggested.lean` of this
roadmap begins with `import TauCetiRoadmap.WeakConvergence.Suggested`, which the
submission's file order allows. Only Milestone 8 uses it.

The time index is a linear order carrying a metric that induces the order
topology, is additive along the order, and has compact closed balls. That
hypothesis is equivalent to being a closed subset of `ℝ` (Milestone 1), and
stating it as a class rather than fixing `[0,1]` or `[0,∞)` is what makes the
four cases `ℝ`, `[0,∞)`, `[0,T]` and `h • ℤ` — and every closed subset of them —
instances of one development.

**Prior art, cited and not presupposed.** The repository
`RemyDegenne/brownian-motion` (Apache-2.0) contains a development of càdlàg
paths in `BrownianMotion/StochasticIntegral/Cadlag.lean`, and its predicate is
the one that went upstream as `Mathlib/Topology/Order/Cadlag.lean` (#43352). It
is named here as a source that an implementer may consult and, the licence
permitting, draw on with its copyright header preserved — **not** as the
specification. Every milestone below states what is wanted in full and is to be
reviewed on its own terms; a declaration that agrees with that file is welcome,
and one that improves on it is more welcome. Nothing here should be accepted
merely because it matches the external material.

The same repository is the reason Milestone 2 splits into what the library
carries and what it does not: the predicate and its closure properties are
upstream, the jump theory and the structure theorem are not, and the milestone
says of each item which side it is on.

## Milestone 1: the index typeclass

```
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u
```

* Instances for `ℝ`, `ℤ`, `ℕ`, and `NNReal`.
* **The bundle at `ℝ≥0`, proved 2026-09-18.** `NNReal.instAdditiveDist` and
  `NNReal.instBasePoint` complete the bundle at the index the martingale
  problems of **MartingaleProblems** are stated over; Mathlib supplies
  `LinearOrder`, `MetricSpace`, `OrderTopology` and `ProperSpace ℝ≥0`
  (`Mathlib/Topology/MetricSpace/ProperSpace/Real.lean`). They are stated in the
  file next to the countable core, which needs them, and not here, because they
  are one bundle and are read together.

  `ℝ≥0` is not a subtype of `ℝ` for the instance search, so
  `instAdditiveDistSubtype` does not reach it and `Set.Ici (0:ℝ)` is a different
  type from the one the processes are indexed by. This is the same gap as the
  `SetLike` one above and it is settled the same way: by writing the instance.
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
* `AdditiveDist.dist_eq_sub_of_le` and
  `AdditiveDist.monotoneOn_dist_basepoint`: for `t₀ ≤ s ≤ t`,
  `dist s t = dist t₀ t - dist t₀ s`, and `t ↦ dist t₀ t` is monotone on
  `Set.Ici t₀`. This is the step from which the embedding above follows. Both
  are proved (2026-09-06), and both need `AdditiveDist` alone: neither the order
  topology nor properness enters.
* `AdditiveDist.dist_eq_abs_sub_of_sameSide`: for `s` and `t` on one side of
  `t₀` — both above it or both below it — `dist s t = |dist t₀ t - dist t₀ s|`.
  This is the
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
  (`Topology/Order/Compact.lean:146` and `:158`, both under the
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
  it is `AdditiveDist` again: above the base point
  `AdditiveDist.monotoneOn_dist_basepoint` gives it, below the base point the
  additivity is read from the other end.
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
* **`AdditiveDist.dist_eq_abs_sub_of_sameSide` needs its hypothesis.** On `ℝ`
  with `t₀ = 0`, `s = -1`, `t = 1`: the left hand side is `2` and
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

**The predicate itself is Mathlib's**, `IsCadlag` in
`Mathlib/Topology/Order/Cadlag.lean`, with fields `isRightContinuous` and
`tendsto_nhdsLT` and with `IsRightContinuous` in the root namespace under it. So
is every closure property listed under (A) below, and so are
`IsCadlag.tendsto_nhdsLT_leftLim` under (A′) and
`isBounded_image_of_isCadlag_of_isCompact` under a metric codomain. What this
milestone owes is the jump theory, the two determination theorems, the three
stability theorems under uniform convergence, and the structure theorem — none
of which the library has. The items below are marked accordingly; an item marked
**upstream** is to be used and not restated.

* **(A)** `[Preorder ι] [TopologicalSpace ι] [TopologicalSpace E]`. This is what
  `Mathlib/Topology/Order/Cadlag.lean` uses for `IsCadlag`, and it carries the
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

* **upstream** `IsRightContinuous f`, defined as
  `∀ a, ContinuousWithinAt f (Set.Ioi a) a`, and its mirror `IsLeftContinuous`.
* **upstream** `IsCadlag f`, a structure with fields `isRightContinuous` and
  `tendsto_nhdsLT : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)`, and `IsCaglad` beside
  it.
* **upstream** the closure properties: `IsCadlag.const`,
  `IsCadlag.continuous_comp`, `IsCadlag.continuous_comp₂`, `IsCadlag.mul`,
  `IsCadlag.div'`, `IsCadlag.const_smul`, with the corresponding
  `IsRightContinuous` lemmas and `Continuous.isCadlag` for a continuous map.
* The two closure properties the library does not carry: pointwise limits that
  are uniform on compacts, which is `IsCadlag.of_tendstoUniformly` and
  `IsCadlag.of_tendstoUniformlyOn_exhaustion` below, and the restriction of a
  càdlàg function to a subinterval.

Under (A′):

* **upstream** `IsCadlag.tendsto_nhdsLT_leftLim`,
  `Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x))`, which is
  `tendsto_leftLim_of_tendsto` applied to the `tendsto_nhdsLT` field, and
  `IsCadlag.rightLim_eq`, `Function.rightLim f x = f x`, which is
  `ContinuousWithinAt.rightLim_eq` applied to the `isRightContinuous` field
  through `continuousWithinAt_Ioi_iff_Ici`; the second adds `[T2Space E]` and is
  ours. These connect the structure to `Function.leftLim` and `Function.rightLim`
  so that the existing API applies; every later statement about left limits uses
  those names, not a new one. The first is unconditional:
  `tendsto_leftLim_of_tendsto` covers the degenerate case `𝓝[<] x = ⊥` itself, so
  no hypothesis on the point is needed. It was proved here on 2026-09-07 under
  the name `IsCadlag.tendsto_leftLim` and **deleted on 2026-09-18**, when the
  chain moved to `master`; the eight uses in `Suggested.lean` now read the
  library's name.
* The identity `Function.leftLim f x = f x` at continuity points, from
  `ContinuousWithinAt.leftLim_eq` applied to the restriction of continuity at
  `x` to `Iic x`, with `[T2Space E]`.
* **upstream** `IsCadlag.const`, and ours `SkorokhodSpace.const`: a constant
  function is càdlàg, over any index and into any space, and the constant path is
  a point of `D(ι, E)`. It asks nothing of either side — the right continuity is
  `continuousWithinAt_const` and the left limit is the value, whether or not
  `𝓝[<] x` is the bottom filter — and it is what keeps `D(ι, E)` from being empty
  whenever `E` is not. Its first use is as the value a path map is given **off**
  the set where the process it reads is càdlàg: `jumpPathD` of the roadmap
  **MartingaleProblems**, Milestone 6, is written that way, and a total map into
  the path space is what a random element has to be.

  The lemma was proved here on 2026-09-18 as `isCadlag_const`, the v4.33.1 stand
  in for `IsCadlag.const` (`Mathlib/Topology/Order/Cadlag.lean:115` on master),
  and **deleted the same day**, when the chain moved to `master` and the local
  predicate went with it. `SkorokhodSpace.const` stays either way — the *space*
  is ours.
* `IsCadlag.comp_monotone_continuous`: `f ∘ g` is càdlàg for càdlàg `f` and
  monotone continuous `g : α → β`, the two indices **different** since
  2026-09-18 — the proof never compares a point of the source with a point of
  the target, and what it uses of either is the order topology alone, so neither
  needs a metric and the target needs nothing of the bundle of Milestone 1.
  `IsCadlag.comp_coe_nnreal` is the case `α = ℝ≥0`, `β = ℝ`: a càdlàg path of a
  real time restricts to a càdlàg path of a nonnegative time, which is the
  bridge between the index the jump construction of **MartingaleProblems** is
  written over and the index its martingale problems are stated over. That file
  had proved the bridge by hand, out of the two one sided filter statements;
  since 2026-09-18 it does not, and the statement lives here. This is what puts
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
* **upstream** `isBounded_image_of_isCadlag_of_isCompact`: the image of a compact
  set under a càdlàg map into a pseudometric space is bounded. Proved here on
  2026-09-07 as `IsCadlag.isBounded_image_of_isCompact` and **deleted on
  2026-09-18**, with the move to `master`; the proof is where the bundle of this
  item was found to be wrong, and the library's statement agrees with the
  correction. It needs the
  **linear** order and nothing else of (A′) --- not the order topology ---
  because it splits a neighbourhood of a point into its two one sided halves by
  `nhdsLT_sup_nhdsGE`, `𝓝[<] x ⊔ 𝓝[≥] x = 𝓝 x`, which is `Iio x ∪ Ici x = univ`
  and holds under `[TopologicalSpace ι] [LinearOrder ι]` alone; the two fields
  of `IsCadlag` then bound `f` on each half.

  **Upstream as `isBounded_image_of_isCadlag_of_isCompact`**, and there under
  `[PseudoMetricSpace E]` rather than `[MetricSpace E]`, which is what the
  statement consumes: the proof goes through `IsCadlag.isLocallyBounded` and
  `isBounded_image_of_isLocallyBounded_of_isCompact`
  (`Mathlib/Topology/Compactness/Compact.lean:691`), with
  `Metric.exists_isBounded_image_of_tendsto`
  (`Mathlib/Topology/MetricSpace/Bounded.lean:274`) supplying the bound on each
  half. Both of those are older than the càdlàg file, so the weakening is
  available wherever `IsCadlag` is stated by hand. The local form
  `IsCadlag.isLocallyBounded` --- every point has a neighbourhood with bounded
  image --- is the statement to keep, the compact one being its corollary.

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
  gives convergence along `𝓝[<] x`, which together with the `isRightContinuous`
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
  (2026-09-07); it uses the two `isRightContinuous` fields and nothing else, not
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
  (`Topology/UniformSpace/UniformConvergence.lean:627`) — right continuity along
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
  `Set.Iio` in `IsRightContinuous`, or that asked for right limits
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
  `isBounded_image_of_isCadlag_of_isCompact` under (A), so an implementer who
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
  one side of `t₀`, so `AdditiveDist.dist_eq_abs_sub_of_sameSide` of Milestone 1
  turns the left hand side into `|dist t₀ (λ t) - dist t₀ t|`;
  `lipschitzWith_lipConst`,
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
* `NNReal.instHasCountableCore`, **proved 2026-09-18**: `ℝ≥0` has a countable
  core, the nonnegative rationals, and it is **inherited from `ℝ` rather than
  built again**. A time change of `ℝ` fixing `0` carries `Set.Ici 0` onto itself
  and therefore restricts (`TimeChange.toNNReal`); restriction shrinks the set a
  Lipschitz constant is tested over, so both constants and with them the norm can
  only drop (`TimeChange.lipConst_toNNReal_le`, `TimeChange.norm_toNNReal_le`),
  and the same `δ` serves. That the restricted nodes are nonnegative is a
  consequence and not an assumption: `l (d i) = t i ≥ 0` with `l 0 = 0` forces
  `d i ≥ 0`, `l` being an order isomorphism. **It is the base point clause of the
  class that makes the transport possible**; a core that did not fix the base
  point would say nothing about a half line. `TimeChange.inv_toNNReal` carries
  the second Lipschitz constant across and is `rfl` on the underlying map.

  With it `D(ℝ≥0, E)` is separable, Polish (`SkorokhodSpace.polishSpace_nnreal`)
  and standard Borel, and its Borel structure is generated by the coordinates
  (`SkorokhodSpace.borel_eq_iSup_comap_eval_nnreal`, Milestone 6). That matters
  because `ℝ≥0` is the index of **MartingaleProblems**: before this, `D(ℝ≥0, E)`
  was not an object of this development at all, and no solution of a martingale
  problem could be said to live in it.
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
  reads `ε + β + exp (-M)`; the split of `Set.Ioc 0 M` is `Set.sdiff_union_inter`
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
  (`Mathlib/Topology/MetricSpace/Polish.lean:62`), and the latter out of a
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
* `SkorokhodSpace.borel_eq_iSup_comap_eval_of_countable_rightDense`:
  `borel (D ι E) = ⨆ t ∈ D, MeasurableSpace.comap (eval t) (borel E)` for **any**
  countable right dense `D`. Proved (2026-09-19), one inclusion from
  `measurable_eval` and the other from the embedding above. The set of times is a
  parameter and not something the proof produces, and that is what carries a
  hypothesis tested only at the times of a prescribed set to the whole Borel
  structure.
* `SkorokhodSpace.borel_eq_iSup_comap_eval`:
  `borel (D ι E) = ⨆ t, MeasurableSpace.comap (eval t) (borel E)`. Proved
  (2026-09-09), the item above at the set `exists_countable_rightDense` supplies.
* `SkorokhodSpace.measurable_of_measurable_eval`: a map `G : α → D(ι, E)` is
  measurable as soon as every coordinate `a ↦ (G a) t` is. Proved (2026-09-18),
  as the identity above read as a criterion. It is the direction in which a
  process with càdlàg paths is shown to be a **random element of the path
  space**, and it is the one that spends the countable core: `measurable_eval` is
  the converse and asks nothing of the index. The first consumer is `jumpPathD`
  of the roadmap **MartingaleProblems**, Milestone 6.
* `SkorokhodSpace.evalFuns`: the finite dimensional test functions along a set of
  times `T` — products `f ↦ ∏ t ∈ s, F t (f t)` over a `Finset ι` inside `T`,
  with `F : ι → (E →ᵇ ℝ)`. Defined (2026-09-19). The index is a `Finset` and not
  a type with a `Fintype` instance, and that is what makes the family closed
  under multiplication: a family of times with repetitions is again of this shape
  only once the repeated factors have been multiplied together, which is what a
  `Finset` does for one. `E →ᵇ ℝ` being a `CommRing` is all that this asks of `E`.
* `SkorokhodSpace.isMulSystem_evalFuns`, `SkorokhodSpace.measurable_of_mem_evalFuns`
  and `SkorokhodSpace.bounded_of_mem_evalFuns`: the class is multiplicative, and
  its members are measurable and bounded. Proved (2026-09-19). These are the three
  hypotheses of `ext_of_forall_integral_eq_of_isMulSystem` (**WeakConvergence**
  Milestone 5) that do not mention a measure.
* `SkorokhodSpace.generateFromFuns_evalFuns`: along a countable right dense set of
  times the class generates the Borel structure of `D ι E`. Proved (2026-09-19),
  from the identity above followed, at each time, by `generateFromFuns_comp` and
  `generateFromFuns_setOf_continuous_bounded`: a function of one coordinate is a
  product over a singleton.
* `SkorokhodSpace.eq_of_forall_rightDense_forall_integral_evalPi_eq`: two laws on
  `D ι E` that agree in their finite dimensional distributions along a countable
  right dense set of times are equal. Proved (2026-09-19).
* `SkorokhodSpace.eq_of_forall_dense_forall_integral_evalPi_eq`: the same with the
  hypothesis on the times reduced to plain **density**, on an index that is
  densely ordered and has no greatest element. Proved (2026-09-19). A dense subset
  has a countable dense subset — `Dense.exists_countable_dense_subset`, whose
  separability hypothesis is the second countability that
  `secondCountable_of_proper` reads off the `ProperSpace ι` of Milestone 1 — and
  such an index has no right isolated point, so `nhdsGT_neBot` makes a dense set
  accumulate from the right at every point and the first branch of the right
  density condition is never used. The set of times is *not* asked to be countable
  — the hypothesis is tested on finite subsets, so a larger set is a stronger
  hypothesis.

  **Both order hypotheses are used.** Without `DenselyOrdered` the index `ℤ` is
  discrete, a dense set is everything, and the statement would be the one along
  all times; without `NoMaxOrder` the greatest element is right isolated, which is
  the gap the first branch of the general condition exists to cover and the point
  at which the counterexample of `measurableEmbedding_piDense` — `Icc (0:ℝ) 1`
  with `Ico 0 1 ∩ ℚ` — breaks. `ℝ` and `ℝ≥0` satisfy both, the second being the
  index over which **MartingaleProblems** states its path law; the consumer there
  is `eq_map_jumpPathD_of_forall_dense`.

  **Neither law is asked to be carried by a set with compact closure**, and no
  modulus of continuity appears. That is the difference between identifying two
  laws and comparing a law with a limit: the stability of the finite dimensional
  distributions to the right, Milestone 8, is what one needs when the times of
  the hypothesis and the times of the conclusion are different; here they are the
  same, and the density is spent on the Borel structure instead.
* Consequences, each stated separately: a map into `D ι E` is measurable if and
  only if all its coordinates along a countable right dense set are; two
  processes with paths in `D ι E` that are modifications of each other induce the
  same law.

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
  `lim_{δ→0} sup_{f ∈ A} modulusBased m f δ = 0`. Proved (2026-09-09), both
  halves. Only the converse is index
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
* `SkorokhodSpace.isCompact_closure_iff_nnreal`: the previous item over the index
  `ℝ≥0`. Every instance of the bundle of Milestone 1 is discharged there —
  `NNReal.instAdditiveDist`, `NNReal.instBasePoint`,
  `NNReal.instHasCountableCore` — and the hypothesis `hrigid` of
  `not_isCompact_closure_of_rigid`, that every time change fixing the base point
  of small norm is the identity, fails over `ℝ≥0`, which carries non-identity
  time changes fixing `0` of arbitrarily small norm; so the witness that confines
  the criterion over a general index excludes nothing at this one. Only the
  converse half is at stake: the forward half is already stated over an arbitrary
  index, `isCompact_closure_values_of_isCompact` and
  `tendsto_iSup_modulusBased_of_isCompact` both reading `basePoint : ι`, and
  `exhaustion`, `modulusBased`, `IsSubdivisionBased` and `stepPathFamilyLe` are
  index-generic as well. What the converse reads at `ℝ` is the finite grid and
  the time change that snaps a `δ`-sparse subdivision onto it,
  `exists_finite_grid_timeChange`, and the net built from it,
  `exists_mem_stepPathFamilyLe_intDist_le`. It is a statement about the
  criterion itself; the consumers of Milestone 8 over `ℝ≥0` do not read it, they
  read the closed embedding of Milestone 9,
  `SkorokhodSpace.isClosedEmbedding_extendNNReal`, which crosses the index once
  for all of them.

  **This item is not by itself the index crossing**, and the next one says why:
  53 declarations of this file are stated over the index `ℝ`, 2 967 lines of
  them, and the criterion is three of those. Restating the rest one by one is
  not the route.
* `SkorokhodSpace.extendNNReal`, `SkorokhodSpace.isometry_extendNNReal` and
  `SkorokhodSpace.isClosedEmbedding_extendNNReal`: **the index crossing.** A path
  on `ℝ≥0` extends to one on `ℝ` by the constant `f 0` on the negative half line,
  and that map is a closed isometric embedding of `D(ℝ≥0, E)` into `D(ℝ, E)`.
  With it every statement over `ℝ` is read at `ℝ≥0` by transport — tightness of a
  set of laws is the tightness of the image laws, a finite dimensional
  distribution at a nonnegative time is one of the image, and weak convergence
  pulls back along a closed embedding — and the 53 declarations over `ℝ` are used
  as they stand instead of restated.

  The two directions of the time change are what the proof turns on, and they are
  not symmetric: a time change of `ℝ≥0` extends to one of `ℝ` by the identity on
  the negative half line, while one of `ℝ` restricts only when it fixes `0`
  (`TimeChange.toNNReal`, with `TimeChange.norm_toNNReal_le` for the norm). The
  isometry therefore has to say that the extra freedom on the negative half line
  buys nothing, and it does not, both extended paths being constant there.

  **This is what Milestone 8 spends the index on**, and what **MartingaleProblems**
  needs of it: every convergence statement there stands over `ℝ`, and `jumpPathD`
  of that roadmap's Milestone 6 lands in `D(ℝ≥0, E)`.
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
  `isCompact_closure_iff`.
* `SkorokhodSpace.isSubdivisionBased_of_le` and
  `SkorokhodSpace.modulusBased_mono_window`: **the based modulus grows with the
  window radius.** Proved (2026-09-21). A subdivision that covers the larger
  window covers the smaller one, `exhaustionMin` being antitone and
  `exhaustionMax` monotone, so the infimum at the smaller radius runs over more
  subdivisions. It is the monotonicity that the measurability below is stated
  with, and it stands beside `modulusBased_mono`, the monotonicity in `δ`.
* `SkorokhodSpace.eventually_modulusBased_lt`,
  `SkorokhodSpace.upperSemicontinuous_iInf_modulusBased` and
  `SkorokhodSpace.measurable_iInf_modulusBased`: **the based modulus is Borel
  measurable in the path, once the window radius is given its right limit.**
  Proved (2026-09-21), and they withdraw a claim that stood twice in the file —
  that no argument for the measurability of the modulus sets is available.

  The function that is measurable is
  `fun f ↦ ⨅ u' ∈ Set.Ioi u, SkorokhodSpace.modulusBased t₀ u' f δ`, and it is
  measurable because it is upper semicontinuous;
  `UpperSemicontinuous.measurable`
  (`MeasureTheory/Constructions/BorelSpace/Order.lean:649`) does the rest. The
  semicontinuity is `SkorokhodSpace.modulusBased_le_of_edist_le` read at a fixed
  subdivision of the path in question: that estimate loses `exp (-γ)` in the
  sparseness and one unit of window radius, and only the second loss survives.
  The first does not, because a *fixed* subdivision has finitely many gaps, each
  strictly wider than `δ`, so a small enough `γ` leaves the transported
  subdivision `δ`-sparse — `eventually_modulusBased_lt` picks that `γ` by
  continuity, together with the one the window needs.

  **The countable-family route is closed, and that is why this one is taken.**
  Restricting the nodes to a countable dense set computes a strictly larger
  infimum for a path that jumps at a time outside that set: every such
  subdivision carries the jump in the interior of a cell, so its oscillation is
  bounded below by the jump, while a subdivision with a node at the jump time
  sees nothing. `SkorokhodSpace.measurable_eval` cannot be spent that way.
* `SkorokhodSpace.setOf_le_modulusBased_subset` and
  `SkorokhodSpace.setOf_le_iInf_modulusBased_subset`: **the sandwich a consumer
  reads.** Proved (2026-09-21). `{f | η ≤ modulusBased t₀ u f δ}` sits inside the
  Borel set of the previous item, which sits inside
  `{f | η ≤ modulusBased t₀ u' f δ}` for every `u' > u`. So a producer with a
  bound at one radius discharges a measurable condition at any smaller one, and
  the passage costs a step in the radius and nothing else. This is what a
  statement about an **image measure** needs, `MeasureTheory.Measure.map_apply`
  asking measurability and `MeasureTheory.Measure.le_map_apply` running the wrong
  way.
* `SkorokhodSpace.measure_map_postcomp_setOf_le_modulusBased_le` and
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le`:
  **the passage from the sample space to the image law.** Proved (2026-09-21),
  and they spend the sandwich above. For `Φ : Ω → D(ℝ≥0, E)` measurable,
  `g : E →ᵇ ℝ` and `u < u'`, a bound
  `P {ω | η ≤ modulusBased 0 u' (postcomp g (extendNNReal (Φ ω))) δ} ≤ ε` gives
  `((P.map Φ).map (postcomp g)).map extendNNReal {f | η ≤ modulusBased 0 u f δ} ≤ ε`;
  and read at `u = m`, `u' = m + 1` for every `m : ℕ` this is exactly the right
  hand side of `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff`, so the
  tightness of the image laws follows with no further hypothesis.

  The two layers are pushed forward together by
  `MeasureTheory.Measure.map_map`, which is where their measurability is spent:
  `SkorokhodSpace.measurable_postcomp` for the value change and
  `SkorokhodSpace.isometry_extendNNReal` for the index change. The two orders of
  the layers are the **same map**, `SkorokhodSpace.postcomp_extendNNReal` being
  `rfl`, so nothing is rewritten between the hypothesis and the conclusion.
* `SkorokhodSpace.measure_map_setOf_le_modulusBased_le`: **the same passage with
  no value change.** Proved (2026-09-22). For `Φ : Ω → D(ℝ≥0, E)` measurable and
  `u < u'`, a bound `P {ω | η ≤ modulusBased 0 u' (extendNNReal (Φ ω)) δ} ≤ ε`
  gives `((P.map Φ).map extendNNReal) {f | η ≤ modulusBased 0 u f δ} ≤ ε`. The
  sandwich is the one above and `MeasureTheory.Measure.map_map` composes one
  layer instead of two, so the only measurability spent is
  `SkorokhodSpace.isometry_extendNNReal`; `[MeasurableSpace E]` and
  `[BorelSpace E]` are omitted, the σ-algebra being the path space's and not
  `E`'s.

  **Both forms are needed and neither subsumes the other.** A criterion reached
  through a bounded `g : E →ᵇ ℝ` reads the post-composed one; a family whose
  modulus is controlled at the process itself — which is the case of a process
  that is **not uniformly bounded**, so that no bounded `g` carries its
  approximants — reaches tightness through
  `SkorokhodSpace.isTightMeasureSet_iff_modulusBased_nnreal` instead, and there
  a post-composition would have to be undone again. **MartingaleProblems**
  Milestone 11 consumes this one at
  `isTightMeasureSet_map_pathOfProcess_of_isApproximableMul`.
* `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le_off_finite`:
  **the same criterion with finitely many members exempted, the exempted set free
  to move with `(ε, m, η)`.** Proved (2026-09-21). The exceptions are not dropped
  from the conclusion; their hypothesis is supplied for them, a single image law
  being a finite measure on a complete second countable metric space and hence
  tight (`MeasureTheory.isTightMeasureSet_singleton`), and
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff` being an **equivalence**,
  so that it returns that member its own window at the very same `(ε, m, η)`.
  `SkorokhodSpace.modulusBased_mono` carries a bound at a window to every smaller
  one, so the minimum of the common window and the finitely many exceptional ones
  serves the whole family; `Set.Finite.exists_pos_forall_le` is what makes that
  minimum positive, and it is stated beside it. `P` is asked to be finite and not
  a probability measure, the tightness of one image law being all that is read of
  it.

  **This is what makes an estimate „from some index on" usable.** A consumer whose
  family satisfies the modulus bound only for `i` beyond a threshold depending on
  the accuracy asked — which is the shape an approximation argument produces —
  cannot use the previous item, whose exempted set would have to be the same at
  every horizon and, the horizons being infinitely many, would not stay finite.
  The equivalence undoes that, being consumed one horizon at a time.
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
* The converse's proof is the finite net, and it is proved (2026-09-09):
  `CompleteSpace D(ℝ, E)` of Milestone 5 turns total boundedness into compactness
  of the closure, and total boundedness is the finite family
  `stepPathFamilyLe G Q n₀`. The five constants are chosen in a forced order —
  the window radius `M` from the tail of the integral, the oscillation `ε`, the
  sparseness `δ` from the modulus condition at `M`, the length bound `n₀` from
  `M` and `δ`, and the displacement `γ` last, the bad radii costing `(n₀+1)`
  times it. The nodes are pushed onto the finite grid of
  `exists_finite_grid_timeChange` — this is where `ℝ` is used and where the rigid
  index fails — and the values onto a finite net of the value compactum. The
  approximant is `SkorokhodSpace.stepPath`, it is counted by
  `finite_stepPathFamilyLe`, the bound is `SkorokhodSpace.distWith_stepPath_le`,
  and the passage from the window to the integral is
  `SkorokhodSpace.intWith_le_of_ae_distWith_le`. The bound on the *number* of
  nodes is `SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision` through
  `IsSubdivisionBased.trim`. The grid holds the base point, and the displacement
  of a node is bounded by a fraction of its distance to the base point rather
  than by an absolute amount: that is what `le_intDist_stepAt_of_exp_mul_lt`
  shows to be necessary. The per-path half is
  `SkorokhodSpace.exists_mem_stepPathFamilyLe_intDist_le`; what the criterion
  itself adds is only the choice of the constants.
* `SkorokhodSpace.badRadiiPiece` and `SkorokhodSpace.badRadii`: the bad radii of
  a node and of a tuple, as **definitions** rather than as anonymous sets inside
  a proof, with `measurableSet_badRadiiPiece`,
  `mem_badRadiiPiece_of_exhaustionMax`, `mem_badRadiiPiece_of_exhaustionMin`,
  `volume_badRadiiPiece_le`, `measurableSet_badRadii` and the pointwise estimate
  `SkorokhodSpace.distWith_stepPath_le_of_notMem_badRadii`. Written and proved
  (2026-09-09). Naming the set is what lets it carry two measure estimates;
  `SkorokhodSpace.exists_bad_radii_set` is their packaging and is what Milestone
  5 consumes.
* `SkorokhodSpace.volume_badRadii_le`, the crude count `(n + 1) (2 γ + κ)`, and
  `SkorokhodSpace.volume_inter_badRadii_le_of_sparse`, the sharp one
  `(n₀ + 1) (2 γ + κ)` **free of `n`**. Both proved (2026-09-09). The sharp one
  is what the converse needs: `n` is unbounded over a family, `IsSubdivision`
  asking only that the subdivision cover the window, so a node may sit
  arbitrarily far outside; the far nodes contribute nothing, their intervals
  sitting around their own coordinate. Its pivot is
  `SkorokhodSpace.dist_le_of_inter_badRadiiPiece_nonempty` — a node whose
  interval meets `Set.Ioc 0 M` lies within `M + γ + κ` of the base point — and
  the count is `sub_mul_le_two_mul_of_isSubdivision` on that enlarged radius.
  The order of the choices is then `δ`, then `n₀`, then the norm budget `γ` and
  with it the grid spacing `ρ`.
* `SkorokhodSpace.exists_isSubdivisionBased_subdivisionOsc_lt` and
  `SkorokhodSpace.dist_le_of_subdivisionOsc_le`: the two bridges the converse
  begins with — the `iInf` unfolded, so that a bound on `modulusBased` produces a
  subdivision, and the passage from `subdivisionOsc` in `ℝ≥0∞` to the cellwise
  real estimate `distWith_stepPath_le` asks for. Both proved (2026-09-09).
* `SkorokhodSpace.IsSubdivisionBased.trim`: to a based `δ`-sparse subdivision of
  the window of radius `M`, for `1 ≤ M` and `0 < δ ≤ 1`, a based `δ`-sparse
  subdivision of the same window with all nodes in `Set.Icc (-(M+1)) (M+1)`,
  length `n'` bounded by `n' δ ≤ 2 (M+1)`, and every cell contained in a cell of
  the original. Proved (2026-09-09). This is what hands `stepPathFamilyLe` a
  tuple of bounded length. Trimming at the **window ends** is closed — the
  trimmed extreme gaps can be arbitrarily small, and sparseness is what separates
  the tents of `exists_finite_grid_timeChange` — but trimming at the fixed marks
  `±(M+1)`, a full step outside the window, is not: the trimmed edge gap is
  either the old one or at least `1`, which is where `δ ≤ 1` is spent, the
  trimmed cell is contained in the old one, and both marks lie beyond the window.
  **This is the one place where the index `ℝ` is used for its own sake**: on a
  general index the mark `M+1` is `exhaustionMin t₀ (M+1)`, whose distance to
  `exhaustionMin t₀ M` can be arbitrarily small while a node still sits strictly
  below the larger window — `ι = {-3, -1.05, -1, 0, 1} ⊆ ℝ` with `M = 1`, a
  subdivision with `t i₀ = -3` and `t (i₀+1) = -1`, trimmed first gap `0.05`.
* `SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells`: a subdivision each of
  whose cells lies inside a cell of another has at most **twice** its
  oscillation. Proved (2026-09-09). The factor is the price of moving the *left
  endpoint*, `subdivisionOsc` measuring each cell from its own, and it cannot be
  improved: a path jumping by `ε` at the left endpoint of a coarse cell and back
  at its midpoint has oscillation `ε` coarsely and `2 ε` for the refinement
  cutting at the midpoint. It is what carries the oscillation across `trim`.
* `SkorokhodSpace.exists_bad_radii_set_of_sparse`: `exists_bad_radii_set` with
  `volume_badRadii_le` replaced by `volume_inter_badRadii_le_of_sparse`, so that
  the count reads `n₀` and not the length `n`. Proved (2026-09-09). Here the
  sparseness `δ` and the displacement budget `γ` become two parameters instead of
  one, and that is the order in which the converse must choose them: `δ` first,
  the modulus condition naming it, and `γ` afterwards and as small as one likes.
* `SkorokhodSpace.exists_mem_stepPathFamilyLe_intDist_le`: **one path, one member
  of the finite family.** Given `M`, `δ`, `γ`, `ε`, a grid `G`, a value net `Q`
  and a length bound `n₀` — all fixed before the path is seen — a path whose
  based modulus at `δ` is below `ε` and whose values on `Set.Icc (-(M+1)) (M+1)`
  are within `ε` of `Q` lies within
  `max γ (12 ε + (n₀+1) (2 γ + (exp γ - 1) 2M) + exp (-M))` of a member of
  `stepPathFamilyLe G Q n₀`. Proved (2026-09-09). The time change of the estimate
  is the **inverse** of the grid's — the grid carries a node to a grid point, and
  `distWith_stepPath_le` asks for the change carrying the approximant's nodes
  back to the path's — and `TimeChange.norm_inv` is what makes that free.
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
classes and the continuous mapping theorem for almost everywhere continuous
maps (Milestone 2 there), and its Milestone 5 supplies the functional monotone
class theorem. The Skorokhod representation theorem of Milestone 3 there is
available and is used by no item of this milestone; where it was announced as
the route, at the convergence of the finite dimensional distributions, the
almost everywhere continuous mapping theorem does the work directly.
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

### The subsequence argument is not to be repeated here

**Instruction of the author, 2026-09-18.** The general principle — *tightness
plus convergence along a separating class gives weak convergence* — is proved
in the roadmap **WeakConvergence**, Milestone 1, as

```lean
theorem tendsto_of_isSeparating_of_isTightMeasureSet [PolishSpace E] [BorelSpace E]
    {Γ : Set (E → ℝ)} (hsep : IsSeparating Γ)
    (hcont : ∀ f ∈ Γ, Continuous f) (hbdd : ∀ f ∈ Γ, ∃ C, ∀ x, |f x| ≤ C)
    (htight : IsTightMeasureSet {μ n | n})
    (hconv : ∀ f ∈ Γ, Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto μ atTop (𝓝 ν)
```

Its proof is Prokhorov for the compact closure, `tendsto_subseq` for a
convergent subsequence of any subsequence, identification of the limit by `Γ`,
and `tendsto_of_subseq_tendsto` to put the sequence back together. Since the
file boundary fell on 2026-09-17, this milestone **imports** it and must not
run that argument a second time.

What remains for `fact:fddconv`(b) — Ethier–Kurtz 3.7.8(b) — is therefore
exactly the procurement of the two hypotheses at `Γ` = the finite dimensional
class on `D ι E`, and nothing else:

1. **Continuity.** The coordinate evaluations are *not* continuous on `D ι E`;
   `continuousAt_eval_of_notMem_leftJumpSet` says they are continuous exactly at
   the paths without a jump at `t`. So `Γ` is not a subclass of `C_b(D ι E)`,
   the hypothesis `hcont` is not available as stated, and the route is the
   **almost everywhere** continuous mapping theorem of **WeakConvergence**,
   Milestone 2, with the exceptional set carried by the limit law. This is what
   forces `D` to avoid the fixed discontinuities of the limit — see the
   counterexample `X n = 1_[1+1/n,∞)`, `X = 1_[1,∞)` of Milestone 4 — and it is
   why `MartingaleProblems` had to prove `map_jumpPathD_setOf_leftLim_eq`, that
   the jump law has no fixed discontinuity at all.
2. **Separation.** That the finite dimensional class over `D` is separating is
   `thm:fdd` of the manuscript, and `D` must contain every maximal element and
   every right-isolated non-isolated point (corrected 2026-09-14).

Open, and the only open point: whether `T ∩ C(ν)` is dense under the
hypotheses of the theorem. `exists_countable_dense_forall_setOf_leftLim_ne_one`
(2026-09-18) shows that density of `T` alone does not decide it.

**Stating this milestone's items so that they read as suppliers of `hcont` and
`hsep` — and not as convergence theorems of their own — is part of the work.**

* `SkorokhodSpace.isTightMeasureSet_iff` — stage (B), **proved 2026-09-19**. A
  set `S` of laws on `D(ℝ, E)` is tight if and only if, for every `ε > 0` and
  every window radius `m`, there is a compact `K ⊆ E` with
  `μ {f | ∀ t ∈ exhaustion 0 m, f t ∈ K}ᶜ ≤ ε` for every `μ ∈ S`, and for every
  level `η > 0` a radius `δ > 0` with
  `μ {f | η ≤ modulusBased 0 m f δ} ≤ ε` for every `μ ∈ S`. That is
  Ethier–Kurtz 3.7.2 at the level of laws, and it is the **only** statement of
  the file that produces tightness from something other than tightness.

  **Both halves are `isCompact_closure_iff` of Milestone 7**, which until this
  item had no consumer at all, and they spend it in opposite directions. Forward
  it is short: a compact set of paths `K` carrying all but `ε` of every measure
  satisfies the criterion of Milestone 7, and the exceptional set of each of the
  two conditions is contained in `Kᶜ`. Backward it is the construction of **one**
  set of paths out of a doubly indexed family of conditions — indexed by `n`
  through `Nat.unpair`, window radius `(n.unpair).1`, level
  `((n.unpair).2 + 1)⁻¹`, tolerance `ε * 2⁻¹ ^ (n + 2)` for each of the two
  conditions — whose exceptional set `measure_compl_iInter_le` pays for, the two
  tolerances at index `n` adding to `ε * 2⁻¹ ^ (n + 1)` and the geometric series
  to `ε` on the nose.

  The step at which a countable family of conditions becomes the **limit** the
  criterion of Milestone 7 asks for is `SkorokhodSpace.modulusBased_mono`, proved
  with it: the based modulus is monotone in `δ` for the same reason `modulus_mono`
  is, the node at the base point surviving the weakening untouched, so a bound at
  one radius is a bound at every smaller one.

  **No measurability of any of these sets is needed**:
  `{f | η ≤ modulusBased t₀ u f δ}` is an infimum over an uncountable family of
  subdivisions, and this criterion does not ask whether it is Borel. It is not
  beyond reach — the earlier version of this paragraph said it was, and
  `SkorokhodSpace.measurable_iInf_modulusBased` of Milestone 7 (2026-09-21)
  sandwiches the set between two Borel ones at neighbouring window radii. A
  Mathlib `Measure` is defined
  on every set, and that is what `isTightMeasureSet_of_forall_exists_isCompact_closure`
  — the joint between the two milestones — and `measure_compl_iInter_le` are
  stated to exploit. The completeness of `E` is inherited from Milestone 7, whose
  converse half produces a totally bounded set and needs a complete space to call
  its closure compact.
* `SkorokhodSpace.tendsto_finiteDimensional_of_tendsto` — stage (A),
  **proved 2026-09-18**. If `μ n → μ` weakly then, for every **countable** family
  `t : α → ι` of points at which the limit has no fixed discontinuity — that is
  `μ {f | f⁻ (t i) = f (t i)} = 1` — the finite dimensional distributions
  converge. The set of `t` failing this is countable, and
  `exists_countable_dense_continuity` below makes the good times dense.

  **The Skorokhod representation theorem is not used**, and this corrects what
  this item said before. The representation theorem turns weak convergence into
  almost sure convergence of representatives so as to apply the continuous
  mapping theorem pathwise; what the proof needs is the *almost everywhere*
  continuous mapping theorem, `tendsto_of_measure_setOf_not_continuousAt_eq_zero`
  (**WeakConvergence** Milestone 2), and that is portmanteau on the laws with no
  representatives at all. Separability still suffices, and completeness is still
  unused; the dependency on Milestone 3 there is gone.

  The analytic content is a statement about one path and one time and is proved
  ahead of it: `SkorokhodSpace.continuousAt_eval_of_notMem_leftJumpSet`,
  evaluation at `t` is continuous **at** every path that does not jump at `t`.
  It is `exists_orderIso_dist_lt_of_intDist_lt` of Milestone 6 read at the single
  point `t` and composed with the continuity of the limit path, and it is where
  the second estimate of that lemma — that `e.symm t` is near `t`, not only that
  `e t` is — is spent. **Only this direction holds**: where `𝓝[>] t = ⊥`,
  `continuous_eval_of_nhdsGT_eq_bot` makes evaluation continuous outright, jump
  or no jump.

  `SkorokhodSpace.continuousAt_evalPi_of_forall_notMem_leftJumpSet` and
  `SkorokhodSpace.measurable_evalPi` carry it to a family of times, the first for
  an arbitrary index by `continuousAt_pi` and the second for an arbitrary index
  by `measurable_pi_lambda`. The countability of `α` is spent in exactly one
  step, the union of the exceptional sets of the coordinates; the target
  `α → E` needs no metric, only `Pi.borelSpace`
  (`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`), which asks for a
  countable index and for nothing else. `measurable_pi_lambda` is the name on
  `v4.33.1`; on master it is a deprecated alias of `Measurable.of_eval`
  (deprecated 2026-08-20), which `v4.33.1` does not have, so the two versions
  have no common spelling here.
* `SkorokhodSpace.tendsto_integral_evalPi_of_tendsto` — stage (A), **proved
  2026-09-19**. The same read as a convergence of **integrals**, which is the
  form in which the finite dimensional distributions are compared throughout this
  milestone: if `μ n → ν` weakly and `ν` charges no jump at any of the finitely
  many `t i`, then `∫ ∏ i, F i (f (t i)) dμ n → ∫ ∏ i, F i (f (t i)) dν` for
  every finite family of bounded continuous `F i`.

  **The integrand is not continuous on `D(ι, E)`**, evaluation at `t i` being
  continuous only at the paths that do not jump there, so this is not weak
  convergence tested against a bounded continuous function and
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
  (`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:365`) does not apply to
  it directly. The laws are therefore pushed forward to `κ → E`, where the
  integrand **is** bounded continuous — the product of the `F i` composed with
  the coordinate projections, by `BoundedContinuousFunction.compContinuous`
  (`Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:334`) and
  `continuous_apply`, the factors multiplied in the `CommRing` of `E →ᵇ ℝ` —, the
  item above carries the convergence to the image laws, and `integral_map` brings
  the two integrals back.

  The index is a `Fintype` and not merely `Countable`, the integrand being a
  finite product; the item above is the countable statement and is not weakened
  by this one. This is the fourth link of the chain of EK 3.7.8(b) below, the one
  that compares the sequence with its own subsequential limit.
* `SkorokhodSpace.tendstoInDistribution_evalPi` and
  `SkorokhodSpace.tendstoInDistribution_eval` — stage (A),
  **proved 2026-09-18**. The same for random variables, on Mathlib's
  `MeasureTheory.TendstoInDistribution`: path valued variables converging in
  distribution have their marginals at such times converging in distribution.
  The second is the form the convergence hypothesis (a) of `mpSolution_of_tendsto`
  (**MartingaleProblems** Milestone 10) is read in, a bounded continuous function
  of the value composing with it by Mathlib's
  `TendstoInDistribution.continuous_comp`. The two also instantiate the image
  measures that the theorem above leaves as data, so that form is not vacuous.
* `SkorokhodSpace.tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` —
  stage (A), **proved 2026-09-19**. Let `S : Set (ProbabilityMeasure (D ι E))` have compact closure,
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

  The first of those ingredients is the one to watch, and it asks more than the
  density of `T`. The finite dimensional distributions of the sequence converge
  along `T` by hypothesis, and those of a subsequential limit `ν` converge at
  the continuity times of `ν` by the item above; the two are therefore compared
  at the times lying in **both**, and what identifies `ν` is that those times are
  dense. Density of `T` alone does not give it, and that is not a caution but a
  theorem: `SkorokhodSpace.exists_countable_dense_forall_setOf_leftLim_ne_one`
  below exhibits a law and a countable dense `T` with **no** time of `T` a
  continuity time of the law. What closes the step is
  the uniform control of the oscillation that relative compactness carries —
  Milestone 7, through the item below — by which the limit along `T` and the
  limit of the subsequence may be interchanged; density of `T` is what makes the
  times of a finite family approachable from the right, and the oscillation bound
  is what makes the approach uniform in the sequence. Both are spent, and neither
  replaces the other.

  **How the theorem is proved, named.** The identification of the subsequential
  limit is `SkorokhodSpace.eq_of_forall_exists_mem_Ico_dist_integral_evalPi_le`
  below: it asks only that for every finite family of times and test functions,
  every `ε > 0` and every reach `η > 0` there be times within `η` to the right at
  which `μ` and `ν` differ by at most `ε`. The remainder is a single estimate,
  `SkorokhodSpace.exists_times_mem_Ico_dist_integral_evalPi_le_of_tendsto` below,
  and the pieces it is assembled from are
  `exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure` for a compact
  set of paths carrying the whole family up to `ε₀`,
  `exists_times_forall_dist_integral_evalPi_le_of_measure_compl_le` for the
  displacement, the hypothesis along `T` for the passage to the limit in `n`, and
  the same displacement estimate **uniformly in the sequence**. At the level of
  the bad times the uniform statement is
  `SkorokhodSpace.exists_time_liminf_measure_setOf_exists_edist_lt`, whose
  conclusion is a `liminf` and so a time good along a *subsequence* — enough
  here, a subsequence of a subsequence being one. Lifted from the bad times to
  the integrals it is
  `SkorokhodSpace.exists_times_frequently_dist_integral_evalPi_le_of_isCompact_closure`
  below, which is
  `exists_times_forall_dist_integral_evalPi_le_of_isCompact_closure` with the
  single law replaced by the sequence, the coordinates read at a **common shift**
  so that one subsequence serves them all; in the form a tight family is reached
  in, it is
  `SkorokhodSpace.exists_times_frequently_dist_integral_evalPi_le_of_measure_compl_le`.

  **The assembly is a chain of five terms and two pivots.** In this paragraph `μ`
  is the law the sequence is to converge to and `ν` a subsequential limit; in the
  statements below the two are called `ν` and `ρ`. The reason it is not three is that
  the times of `T` are of no use to `ν` and the continuity times of `ν` are of no
  use to the hypothesis: weak convergence `μ nₖ → ν` yields the finite
  dimensional distributions of `ν` only at times it does not charge with a jump
  (`SkorokhodSpace.tendsto_finiteDimensional_of_tendsto`), while the hypothesis
  yields those of `μ` only at times of `T`, and
  `SkorokhodSpace.exists_countable_dense_forall_setOf_leftLim_ne_one` exhibits a
  law and a countable dense `T` sharing **no** such time. Both families of times
  have therefore to be reached by displacement, and from a common place. The
  order in which the constants are produced is forced:

  1. `exists_times_forall_dist_integral_evalPi_le_of_measure_compl_le` on `ν`
     alone, at the prescribed times `t` with reach `η/2`: times `s_ν` and a span
     `δ_ν`;
  2. `exists_times_frequently_dist_integral_evalPi_le_of_measure_compl_le` on the
     sequence, at the prescribed times `s_ν` with reach at most `δ_ν`: times `s`
     and a span `δ`, and a set of `n` that is frequent;
  3. a time family `u ∈ T` inside `[s i, s i + min δ δ_ν')`, by density of `T`;
  4. a time family `u'` in the same window at which `ν` has no fixed
     discontinuity, by `SkorokhodSpace.exists_countable_dense_continuity`, whose
     set of such times is countable and **dense**, so it meets any window.

  The estimate at the times `u` — which are the times the identification is
  applied at — is then

      |∫ ∏ F i (f (u i)) dμ − ∫ ∏ F i (f (u i)) dν|
        ≤ |∫ … dμ − ∫ … dμ n|            (→ 0, u ∈ T, the hypothesis)
        + |∫ … dμ n − ∫ ∏ F i (f (s i)) dμ n|    (≤ ε/4, frequently in n)
        + |∫ ∏ F i (f (s i)) dμ n − ∫ ∏ F i (f (u' i)) dμ n|  (≤ ε/4, same n)
        + |∫ ∏ F i (f (u' i)) dμ n − ∫ ∏ F i (f (u' i)) dν|   (→ 0, u' a
                                                   continuity time of ν)
        + |∫ ∏ F i (f (u' i)) dν − ∫ ∏ F i (f (u i)) dν|      (≤ ε/2, both
                                                   times in ν's own span,
                                                   pivoted at `s_ν`),

  the second and third terms pivoting at `s` and the last at `s_ν`. The first
  term is the hypothesis along `T`; the second and third are
  `exists_times_frequently_dist_integral_evalPi_le_of_measure_compl_le`; the
  fourth is `SkorokhodSpace.tendsto_integral_evalPi_of_tendsto` above; the fifth
  is `exists_times_forall_dist_integral_evalPi_le_of_measure_compl_le` on `ν`.
  **`μ`, the limit whose existence is to be shown, is asked for nothing beyond
  the hypothesis** — it appears in the first term only, and needs neither a
  carrier of small complement nor a continuity time; the displacement is spent on
  `ν`, which lies in `closure S` and is therefore covered by the compact set.
  What the step costs beyond its ingredients is the bookkeeping of the four
  windows and the production of one `n` at which the second, third and fourth
  terms hold together — `Filter.Frequently.and_eventually`, the second holding
  frequently and the first and third eventually.

  **The compact set is to be asked of `closure S` and not of `S`.** The
  conclusion of `exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure`
  is `∀ μ ∈ S, μ Kᶜ ≤ ε` and says nothing about the subsequential limit `ν`,
  which is the second of the two laws to be compared. Applying it to `closure S`
  — its hypothesis being `closure_closure` read on the one at hand — covers `ν`
  as well, and the portmanteau detour through `limsup μₙ K ≤ ν K` is not needed.
  It is the same move by which the item above passes from `A` to `closure A`.

  **In what sense the oscillation bound is uniform, and in what sense it is
  not.** It is not a uniform right modulus at a fixed time: to a compact set `K`
  of paths, a time `t` and an `ε > 0` there need be **no** `δ > 0` with
  `dist (f s) (f t) ≤ ε` for all `f ∈ K` and all `s ∈ [t, t + δ)`. That is
  `SkorokhodSpace.exists_isCompact_forall_exists_one_le_dist` and, on Mathlib's
  predicate, `SkorokhodSpace.exists_isCompact_not_equicontinuousWithinAt`. The
  defect is one of uniformity alone — a single path has the property by right
  continuity (`IsRightContinuous.exists_forall_dist_le`) and a finite family has
  it by `SkorokhodSpace.equicontinuousWithinAt_of_finite` — and compactness in
  `D(ℝ, E)` does not bridge the two, because the metric of Milestone 4 lets a
  time change carry a jump across a fixed time at vanishing cost.

  What the modulus does give uniformly is the **number of cells**: trimmed to
  the marks `± (M + 1)`, a `δ`-sparse subdivision of the window of radius `M`
  has at most `2(M+1)/δ` of them whatever the path — that is
  `SkorokhodSpace.forall_exists_isSubdivisionBased_of_iSup_lt` below — so the
  times at which one path oscillates by more than `ε` to the right over a span
  `δ'` lie in that many intervals of length `δ'` and hence in a set of Lebesgue
  measure at most `(2(M+1)/δ + 1) · δ'`. The interchange
  of the two limits is therefore to be made in measure over the time variable
  and not pathwise: the bound on the bad times is uniform over `K`, and it is
  the bound that survives.
* `SkorokhodSpace.exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure`
  — stage (A), **proved 2026-09-18**. For `S : Set (ProbabilityMeasure (D ℝ E))`
  with compact closure and for `ε > 0` there is a compact `K ⊆ D(ℝ, E)` with
  `μ Kᶜ ≤ ε` for every `μ ∈ S`, and the modulus
  `SkorokhodSpace.modulusBased 0 m` tends to `0` uniformly over `K`.

  This is the step from compactness **of a set of measures** to compactness **of
  a set of paths**, and it is what `SkorokhodSpace.isCompact_closure_iff` of
  Milestone 7 needs as its input: that criterion speaks of a set of paths and the
  theorem above hypothesises a set of measures, so the oscillation bound is not
  available to it directly. The bridge is Prokhorov's converse half,
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure`
  (`Mathlib/MeasureTheory/Measure/Prokhorov.lean:634`), which asks for a second
  countable complete metric space; `SkorokhodSpace.instCompleteSpace` and
  `SkorokhodSpace.instSeparableSpace` of Milestone 5 supply both, the second
  countability being separability read through the metric. It is this item, and
  not the criterion of Milestone 7 by itself, that the theorem above spends.

  The hypotheses on `E` are `SecondCountableTopology` and `CompleteSpace` and no
  more. `PolishSpace E` is **not** among them, and the difference is not
  cosmetic: Polishness is second countability together with completeness of
  *some* compatible metric, while the two instances of Milestone 5 and the proof
  use the metric they are handed.
* `SkorokhodSpace.exists_countable_dense_forall_setOf_leftLim_ne_one` — stage
  (A), **proved 2026-09-18**. There are a probability measure `ν` on `D(ℝ, ℝ)`
  and a countable dense `T ⊆ ℝ` such that
  `ν {f | f⁻ t = f t} ≠ 1` for every `t ∈ T`. Read against
  `SkorokhodSpace.exists_countable_dense_continuity`, which gives a countable
  dense set of continuity times for *any* law: both sets are countable and dense,
  and they can be disjoint. This is what forbids the proof of the theorem above
  from comparing the two families of finite dimensional distributions on `T`
  itself.

  The law is `SkorokhodSpace.denseJumpLaw`, the countable mixture
  `∑ₙ 2⁻ⁿ⁻¹ δ` of the unit steps `SkorokhodSpace.ratStep n = stepAt qₙ 1 0` at
  the rationals, and `T` is the range of `ℚ → ℝ`. The mixture, rather than a
  single path with a jump at every rational, is what makes it cheap: a single
  such path costs a càdlàg proof for a uniformly convergent series, while the
  mixture costs `SkorokhodSpace.stepAt` of Milestone 5,
  `SkorokhodSpace.leftLim_stepAt` — the left limit of a step at its own jump time
  is the lower value — and `ENNReal.tsum_geometric_add_one`. Each rational
  carries mass `2⁻ⁿ⁻¹ > 0`, which is all the argument asks.

  **What it does not say** is that the theorem above fails. The law is not
  exhibited as a subsequential limit of anything and the hypotheses of the
  theorem are not in play; the witness speaks about one implication inside a
  proof, not about the statement.
* `SkorokhodSpace.exists_isCompact_forall_exists_one_le_dist` — stage (A),
  **proved 2026-09-18**. There are a compact `K ⊆ D(ℝ, ℝ)` — over which the
  modulus of Milestone 7 therefore tends to `0` uniformly, by
  `SkorokhodSpace.isCompact_closure_iff` — and a time `t` such that for
  **every** `δ > 0` some `f ∈ K` and some `s ∈ [t, t + δ)` have
  `1 ≤ dist (f s) (f t)`.

  The set is the one of `SkorokhodSpace.tendsto_stepAt_shift`: the steps with
  jump time `1/(n+2) - 1` together with their limit, the step at `-1`, compact
  as a convergent sequence with its limit by `Filter.Tendsto.isCompact_insert_range`
  (`Mathlib/Topology/Compactness/Compact.lean:640`). At
  `t = -1` the `n`-th path is `0` at `t` and `1` at its own jump time, which
  lies in `[t, t + δ)` as soon as `1/(n+2) < δ`. The modulus condition is read
  off the criterion of Milestone 7 and not proved again.

  This is what fixes the sense in which the oscillation bound is uniform: it is
  uniform over the *radii of the subdivision* and not over the *paths at a fixed
  time*. A proof of the theorem above may not take a `δ` that serves all of `K`
  at once.
* `SkorokhodSpace.exists_isCompact_not_equicontinuousWithinAt` — stage (A),
  **proved 2026-09-18**. The same on Mathlib's predicate: there are a compact
  `K ⊆ D(ℝ, ℝ)` and a time `t` with
  `¬ EquicontinuousWithinAt (fun f : K => f.toFun) (Set.Ici t) t`. It is the
  previous item read through `Metric.mem_nhdsWithin_iff` and
  `Metric.dist_mem_uniformity`, and it is stated so that the negative result and
  the two positive ones below live on one predicate.
* `IsRightContinuous.exists_forall_dist_le` — stage (A), **proved 2026-09-18**.
  For a right continuous `f : ℝ → E`, a time `t` and `ε > 0` there is `δ > 0`
  with `dist (f s) (f t) ≤ ε` for every `s ∈ [t, t + δ)`. It asks nothing beyond
  right continuity; `t` itself is covered separately, `Set.Ico t (t + δ)`
  containing it while `Set.Ioi t` does not.
* `SkorokhodSpace.equicontinuousWithinAt_of_finite` — stage (A), **proved
  2026-09-18**. A finite `K ⊆ D(ℝ, E)` is equicontinuous within `Set.Ici t` at
  every `t`, by `equicontinuousWithinAt_finite`
  (`Mathlib/Topology/UniformSpace/Equicontinuity.lean:254`) and
  `continuousWithinAt_Ioi_iff_Ici`
  (`Mathlib/Topology/Order/LeftRight.lean:79`), which passes from the right
  continuity of `IsCadlag`, stated on `Set.Ioi t`, to the `Set.Ici t` the
  predicate asks for.

  Read with the two refutations above: the obstruction is neither the paths nor
  the time, it is the passage from a finite family to a compact one.
* `SkorokhodSpace.exists_isSubdivisionBased_of_modulusBased_lt` — stage (A),
  **proved 2026-09-18**. For `1 ≤ M`, `0 < δ ≤ 1` and a path `f` with
  `modulusBased 0 M f δ < c` there is a based subdivision `s` with all nodes in
  `[-(M+1), M+1]`, with `(n : ℝ) * δ ≤ 2 * (M + 1)`, and with
  `subdivisionOsc f s ≤ 2 * c`. It is
  `SkorokhodSpace.exists_isSubdivisionBased_subdivisionOsc_lt` followed by
  `SkorokhodSpace.IsSubdivisionBased.trim`, and the factor `2` is the one of
  `SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells`, which its own docstring
  shows to be attained.

  The third conjunct is the point: it is a bound in `M` and `δ` and **not in the
  path**.
* `SkorokhodSpace.forall_exists_isSubdivisionBased_of_iSup_lt` — stage (A),
  **proved 2026-09-18**. The same for every `f` of a set `K` whose supremum of
  based moduli is below `c`, which is what the item above the refutations
  produces at every small enough `δ`. This is the uniformity that survives: the
  **number** of cells is one bound for all of `K`, while their **placement** is
  not, by `SkorokhodSpace.exists_isCompact_forall_exists_one_le_dist`. A proof
  wanting uniformity over `K` is to be phrased in the count.
* `SkorokhodSpace.exists_measure_le_forall_edist_le` — stage (A), **proved
  2026-09-18**. For a path with `modulusBased 0 M f δ < c` there are a length
  `n` with `(n : ℝ) * δ ≤ 2 * (M + 1)` and a set `B ⊆ ℝ` of Lebesgue measure at
  most `(n + 1) * δ'` such that `edist (f s) (f t) ≤ 4 * c` for every
  `t ∈ [-M, M) \ B` and every `s ∈ [t, t + δ')`.

  `B` is the union of `[sₖ - δ', sₖ)` over the nodes; off it, `t` and every such
  `s` lie in **one** cell, by `exists_mem_Ico_of_strictMono` for `t` and because
  a node in `(t, s]` would put `t` into `B`. The factor `4` is the cellwise
  bound `2 * c` twice and the triangle inequality, the cell being measured from
  its left endpoint. **`δ'` is not assumed positive**: for `δ' ≤ 0` both `B` and
  the spans are empty, and no step of the proof asks for more.
* `SkorokhodSpace.forall_exists_measure_le_forall_edist_le` — stage (A),
  **proved 2026-09-18**. The same for every path of a `K` whose supremum of
  based moduli is below `c`, with **one** measure bound for all of `K`. This is
  the statement the interchange of the two limits is to be made in: the bad
  times cannot be made empty — that is the refutation above — and they can be
  made of small measure, uniformly.
* `SkorokhodSpace.measurable_uncurry_eval` — stage (A), **proved 2026-09-18**.
  Evaluation is measurable in the pair, `Measurable fun p : ℝ × D(ℝ, E) ↦ p.2 p.1`,
  and not merely in the path. The approximation is the dyadic one from the
  right, `⌈t 2ⁿ⌉ / 2ⁿ`: it has countable range, so each approximant is
  measurable by `measurable_from_prod_countable_left` over
  `SkorokhodSpace.measurable_eval`, the paths being right continuous the
  approximants converge pointwise, and `measurable_of_tendsto_metrizable`
  closes it.

  **This is where the metrizability of `E` is spent**, and it cannot be
  dropped: a pointwise limit of measurable maps into a bare measurable space
  need not be measurable. Metrizability and separability, that is: the
  completeness in the `[PolishSpace E]` of the signature is the one that comes
  with the Borel σ-algebra on `D(ι, E)` and is spent by no step, which is why
  this item and the five below it are stage (A) like their neighbours. It is the
  same boundary that
  `measurable_uncurry_min_of_rightContinuous` records in
  **MartingaleProblems**, where the `E` valued process is deliberately not
  claimed to be jointly measurable over an arbitrary σ-algebra; here `E` is
  Polish and the claim is available. Without it no statement below can be
  integrated over the time variable.
* `SkorokhodSpace.measurableSet_setOf_exists_edist_lt` — stage (A), **proved
  2026-09-18**. The event that the right oscillation over `[t, t + δ')` exceeds
  `a` is measurable in the pair `(t, f)`. The existential over a real time is
  replaced by a countable one over the rationals, and that replacement **is**
  the right continuity of the paths: at `s = t` the distance is `0`, so a
  witness lies strictly to the right of `t`, and the values just to the right of
  a witness are again witnesses. `δ'` is again not assumed positive.
* `SkorokhodSpace.lintegral_measure_setOf_exists_edist_lt_le` — stage (A),
  **proved 2026-09-18**. For a law `μ` carried by a `K` whose supremum of based
  moduli at `δ` is below `c`, the integral over the window of
  `μ {f | ∃ s ∈ [t, t + δ'), 4 c < edist (f s) (f t)}` is at most
  `(⌈2 (M + 1) / δ⌉ + 1) δ'`.

  This is Tonelli, in the form `Measure.prod_apply` and
  `Measure.prod_apply_symm`: the integral is the product measure of the pair
  event, and read the other way round it is the average over paths of the
  Lebesgue measure of that path's bad times, which
  `forall_exists_measure_le_forall_edist_le` bounds. The bound survives the
  average because the **length** of the subdivision is bounded in `M` and `δ`
  alone.
* `SkorokhodSpace.mul_volume_setOf_le_measure_setOf_exists_edist_lt` — stage (A),
  **proved 2026-09-18**. Markov on the times: `β` times the Lebesgue measure of
  the times of the window at which the law charges a large right oscillation
  with probability at least `β` is at most the same constant. Written without a
  division, so that it asks nothing of `β`.
* `exists_mem_Ico_lt_of_setLIntegral_le'` and
  `exists_mem_Ico_lt_of_setLIntegral_le` — stage (A), **proved 2026-09-18**. If
  `∫⁻ t in [u, v), F t ≤ C` and `C < β * (v - u)` then some `t` of the window has
  `F t < β`; the second is the symmetric window `[-M, M)`, which is the shape the
  bound below comes in. It is Markov read by contradiction, it mentions neither
  the path space nor a law, and it is the step that turns a statement about the
  measure of the bad times into a statement about **one** time.
* `exists_mem_Ico_lt_of_setLIntegral_le_of_subset` — stage (A), **proved
  2026-09-18**. The same on a *subwindow* `[u, v) ⊆ [-M, M)`, the integrand being
  non-negative so that `lintegral_mono_set` carries the bound down. This is what
  turns one good time into a good time **near a prescribed one**: the bound below
  is proportional to the span `δ'`, and the span is free, so it may be made small
  against any subwindow one likes.
* `SkorokhodSpace.exists_time_measure_setOf_exists_edist_lt` — stage (A),
  **proved 2026-09-18**. The time itself, for one law: under the hypothesis
  above and for `δ'` small enough that `(⌈2 (M + 1) / δ⌉ + 1) δ' < β * (2 M)`
  there is a `t ∈ [-M, M)` at which the law charges a large right oscillation
  with probability less than `β`. This is what
  `exists_isCompact_forall_exists_one_le_dist` leaves open: not every time is
  good, and one is.
* `SkorokhodSpace.exists_time_mem_Ico_measure_setOf_exists_edist_lt` and
  `SkorokhodSpace.exists_times_forall_measure_setOf_exists_edist_lt` — stage (A),
  **proved 2026-09-18**. The good time inside a *prescribed subwindow*, and then
  a whole family of them: to `t : κ → ℝ` with every `[t i, t i + η)` inside
  `[-M, M)` and to `δ'` small enough that
  `(⌈2 (M + 1) / δ⌉ + 1) δ' < β η`, there are `s i ∈ [t i, t i + η)` at each of
  which the law charges a large right oscillation with probability less than `β`.

  The index `κ` is arbitrary and carries no structure: the times are chosen
  independently of one another, the bound holding on every subwindow at once.
  What the coordinates share is the span `δ'` and the level `β`, and that is the
  whole content of the single hypothesis.
* `SkorokhodSpace.exists_time_mem_Ico_forall_measure_setOf_exists_edist_lt` —
  stage (A), **proved 2026-09-18**. One good time serving **finitely many laws at
  once**: to a `Finset` of laws all carried by `K` and to `δ'` small enough that
  `#s · (⌈2 (M + 1) / δ⌉ + 1) δ' < β (v − u)`, there is a time of the subwindow at
  which every law of the set charges a large right oscillation with probability
  less than `β`. It is the bound summed over the set and then the argument above.

  **The finiteness is the whole hypothesis, and it is sharp in the following
  sense.** The price is the factor `#s`, paid by making the span smaller; over an
  infinite index the sum of the bounds is infinite and no span is small enough.
  That is not an artefact of this proof — a time good for every member of a
  sequence at once need not exist, for the reason recorded at the item below.
  Two laws are the case that identifying a law by its finite dimensional
  distributions along a dense set of times needs, and for two the factor is `2`.
* `SkorokhodSpace.exists_time_liminf_measure_setOf_exists_edist_lt` — stage (A),
  **proved 2026-09-18**. The time for a whole **sequence** of laws, all carried
  by the same `K`, and the conclusion carries a `liminf`:
  `liminf (fun n ↦ μ n {f | ∃ s ∈ [t, t + δ'), 4 c < edist (f s) (f t)}) < β`.
  The bound of the item above holds for every member with the same constants,
  and Fatou's lemma `lintegral_liminf_le` carries it to the `liminf` of the
  integrands.

  **The `liminf` is not a weakening that a later proof may repair.** A time good
  for *every* member of the sequence at once need not exist: each law's bad
  times are of small measure, and their union over the sequence may cover the
  window. The inequality that would be needed is `∫ liminf`'s mirror,
  `∫ limsup ≤ limsup ∫`, and it is false; Mathlib's reverse Fatou
  `limsup_lintegral_le` states the converse, `limsup ∫ ≤ ∫ limsup`, and is of no
  use here. What the interchange of the two limits may spend is therefore a time
  good along a **subsequence** — which is what an argument comparing
  subsequential limits has at its disposal in any case.
* `setLIntegral_Ico_const_add` — stage (A), **proved 2026-09-19**. A Lebesgue
  integral over a window is unchanged when the window and the integrand are
  translated together: `∫⁻ r in [b, c), g (a + r) = ∫⁻ u in [a + b, a + c), g u`.
  It is `measurePreserving_add_left` on `volume`, the `to_additive` of
  `measurePreserving_mul_left` (`Mathlib/MeasureTheory/Group/Measure.lean:86`),
  read through `MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage`
  (`Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean:125`), the interval being
  carried along by `Set.preimage`. It names neither the path space nor a law and
  is here only because the item below needs the windows of finitely many
  coordinates to be read as one.
* `SkorokhodSpace.exists_times_frequently_forall_measure_setOf_exists_edist_lt` —
  stage (A), **proved 2026-09-19**. Good times for a finite family of prescribed
  times **and** a whole sequence of laws at once: to `t : κ → ℝ` over a finite
  `κ`, each carrying `[t i, t i + η)` inside `[-M, M)`, there is a family `s`
  with `s i ∈ [t i, t i + η)` at which, **frequently in `n`**, every coordinate
  of the `n`-th law charges a large right oscillation with probability less
  than `β`.

  **The times are chosen by a common shift, and that is what makes the statement
  possible at all.** `exists_times_forall_measure_setOf_exists_edist_lt` chooses
  the coordinates independently of one another, which for a *single* law costs
  nothing; for a sequence it would produce one subsequence per coordinate, and
  finitely many subsequences obtained that way have no reason to meet. What is
  looked for instead is `s i = t i + r` with **one** `r ∈ [0, η)`: the bad sets
  of the coordinates are then read at a single point, the sum over `κ` of their
  measures is a function of `r` alone, and its integral over `[0, η)` is `#κ`
  times the bound of `lintegral_measure_setOf_exists_edist_lt_le` — by
  `setLIntegral_Ico_const_add`, each summand's integral being an integral over
  that coordinate's own window. That is where the factor `Fintype.card κ` of the
  hypothesis comes from, and it is paid, as everywhere in this section, by making
  the span `δ'` smaller. Fatou then gives one `r` at which the `liminf` of the
  sums is below `β`, and `frequently_lt_of_liminf_lt` reads it.

  **The order of the two quantifiers is fixed by the proof and is not free.** The
  span `δ'` is a parameter of the statement and is chosen before anything else,
  the `liminf` sitting at the shift `r` alone; a span depending on `n` would not
  survive the passage to the subsequence, the bad sets being defined in terms of
  it.

  The finiteness of `κ` is essential here, unlike in
  `exists_times_forall_measure_setOf_exists_edist_lt`, where the index is
  arbitrary: over an infinite index the sum of the bounds is infinite and no span
  is small enough.
* `SkorokhodSpace.integral_abs_sub_eval_le_of_forall_dist_le` and
  `SkorokhodSpace.dist_integral_eval_le_of_forall_dist_le` — stage (A),
  **proved 2026-09-18**. The passage from the bad times to the one dimensional
  distributions. For a law `μ` carried by `K`, a bounded continuous `F : E →ᵇ ℝ`,
  a time `t` and a time `t'` of the span `[t, t + δ')`:
  `∫ |F (f t') − F (f t)| dμ ≤ ε + 2 ‖F‖ · μ (bad t)`,
  with `bad t` the set of the item above and `ε` a modulus of `F` at the scale
  `a`, asked only of a set `S` holding the values of the paths of `K` over the
  span. The second is the difference of the two integrals, one
  `abs_integral_le_integral_abs` away.

  The proof decomposes `∫ |F (f t') − F (f t)|` over `bad t` and its complement,
  by `integral_mono_ae` against
  `fun f ↦ ε + (bad t).indicator (fun _ ↦ 2 ‖F‖) f`. Off `bad t` the witness is
  `t'` itself: were `edist (f t') (f t)` above `a`, the path would be in
  `bad t`. Both halves are spent, and neither can be dropped — the bad set
  cannot be made empty, by
  `SkorokhodSpace.exists_isCompact_forall_exists_one_le_dist`, and its measure
  alone would not control a test function of unbounded oscillation.

  **The `L¹` statement is the primitive and the difference of the integrals the
  corollary**, and the order matters for what comes after. A bound on
  `|∫ F (f t') dμ − ∫ F (f t) dμ|` says nothing about a *product* of such
  differences: the telescope of the item below moves one coordinate at a time and
  multiplies by the remaining factors **before** integrating, so what it can spend
  is `∫ |F i (f (t' i)) − F i (f (t i))| dμ` and not the difference of the two
  one dimensional integrals.
* `abs_prod_sub_prod_le` — stage (A), **proved 2026-09-18**. The telescope for a
  finite product of reals: if every factor of either family is bounded by
  `C ≥ 1`, then `|∏ a i − ∏ b i| ≤ C ^ #s · ∑ |a i − b i|`. The induction replaces
  one factor at a time,
  `a j ∏ a − b j ∏ b = (a j − b j) ∏ a + b j (∏ a − ∏ b)`, and `1 ≤ C` is what
  lets the two powers of `C` that arise be written with the larger exponent. It
  names neither the path space nor a measure.
* `SkorokhodSpace.dist_integral_evalPi_le_of_forall_dist_le` — stage (A),
  **proved 2026-09-18**. The estimate for a finite family of times and of test
  functions: to `t t' : κ → ℝ` with `t' i ∈ [t i, t i + δ')` and to
  `F : κ → (E →ᵇ ℝ)` all bounded by `C ≥ 1`,
  `|∫ ∏ F i (f (t' i)) dμ − ∫ ∏ F i (f (t i)) dμ| ≤ C ^ #κ ∑ (ε + 2 C μ (bad (t i)))`.
  It is the telescope under the integral sign and then the `L¹` estimate in each
  coordinate. The bad sets of the coordinates are different sets, one per `t i`,
  and each is paid for separately; what the coordinates share is the span `δ'` and
  the scale `a`.
* `exists_forall_dist_le_of_isCompact_closure` — stage (A), **proved
  2026-09-18**. A modulus on a set with compact closure: for `S ⊆ E` with
  `IsCompact (closure S)`, a bounded continuous `F` and `ε > 0` there is a scale
  `a > 0` at which `ε` is a modulus of `F` on `S`. It is
  `IsCompact.uniformContinuousOn_of_continuous` and nothing else, and it names
  neither the path space nor a law.
* `exists_forall_mem_dist_le_of_isCompact_closure` — stage (A), **proved
  2026-09-18**. The same scale for every `F i` with `i` in a finite set, by taking
  the smaller of the two scales at each step of an induction over the set. The
  index type is arbitrary and the finiteness sits in the `Finset`, so the
  statement asks nothing of `κ`; read at `Finset.univ` over a `Fintype` it is the
  form the finite dimensional estimate wants.
* `SkorokhodSpace.exists_time_forall_dist_integral_eval_le` and
  `SkorokhodSpace.exists_time_frequently_dist_integral_eval_le` — stage (A),
  **proved 2026-09-18**. The two times above read through that estimate: at the
  time of the window, and for every time of the span `δ'` to its right, the
  integral of `F` moves by at most `ε + 2 ‖F‖ β`. For a sequence of laws the
  conclusion is again along a **subsequence**, `frequently_lt_of_liminf_lt`
  reading the `liminf`. The window of the values is `[-M, M + δ']` and not
  `[-M, M]`, the time being produced in `[-M, M)` and the span reaching beyond
  it.
* `SkorokhodSpace.exists_time_forall_dist_integral_eval_le_of_isCompact_closure`
  — stage (A), **proved 2026-09-18**. The modulus discharged, and the statement
  in the form the interchange wants it: for `A ⊆ D(ℝ, E)` with compact closure,
  a law `μ` with `μ Aᶜ = 0`, a bounded continuous `F` and `ε > 0`, there are a
  span `δ' > 0` and a time `t ∈ [-m, m)` with
  `|∫ F (f t') dμ − ∫ F (f t) dμ| ≤ ε` for every `t' ∈ [t, t + δ')`.

  **Nothing is asked of `F` beyond boundedness and continuity**, and that
  settles a question the two items above leave open. A bounded continuous
  function on a metric space need not be uniformly continuous, so a modulus is
  not to be had from `F` alone; it is had from the paths. The first conjunct of
  `SkorokhodSpace.isCompact_closure_iff` says that the values of a relatively
  compact set of paths over a bounded window lie in a set with compact closure,
  and a continuous function is uniformly continuous there. So the interchange is
  a statement of stage (A) with the test class the milestone already uses, and
  the completeness of `E` enters through that criterion alone.

  The four constants are chosen in the order the proof forces, and the order is
  not free: the scale `a` of the modulus from the compactness of the values over
  `[-(m+1), m+1]`; then the radius `δ` of the subdivision, so that the modulus of
  the paths stays below `a / 4`; then the level `β = ε / (4 (‖F‖ + 1))`, so that
  the bad set costs at most `ε / 2`; and the span `δ'` last, because the bound on
  the bad times is `(⌈2 (m + 1) / δ⌉ + 1) δ'` and only `δ'` is still free. The
  two windows differ — `m` for the modulus and `m + 1` for the values — since the
  span reaches `δ' ≤ 1` beyond the window in which the time is produced.
* `SkorokhodSpace.exists_times_forall_dist_integral_evalPi_le_of_isCompact_closure`
  — stage (A), **proved 2026-09-18**. The same for the finite dimensional
  distributions, and with the times **near prescribed ones**: for `A ⊆ D(ℝ, E)`
  with compact closure, a law `μ` with `μ Aᶜ = 0`, a finite family
  `F : κ → (E →ᵇ ℝ)`, prescribed times `t : κ → ℝ` of the window `[-m, m − 1)`, a
  reach `η ∈ (0, 1]` and an `ε > 0`, there are times `s i ∈ [t i, t i + η)` and a
  span `δ' > 0` with
  `|∫ ∏ F i (f (s' i)) dμ − ∫ ∏ F i (f (s i)) dμ| ≤ ε`
  for every family `s' i ∈ [s i, s i + δ')`.

  **The prescribed times are not themselves good, and cannot be made so.** The
  estimate is available at a time only where the law charges a large right
  oscillation with small probability, and the bound on the bad times is a bound
  in *Lebesgue measure*: it produces good times densely and not everywhere. What
  holds is therefore the statement with the times moved to the right by less than
  `η` — which is exactly what approximating a finite family from the right along a
  dense set of times asks for, and what the density of `T` is spent on in the item
  `tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` above.

  The constants are chosen in the order the proof forces: the common norm bound
  `C = 1 + ∑ ‖F i‖`, then `Dc = C ^ #κ (#κ + 1)`, which is what the telescope
  costs, then the scale `a` of the modulus at the level `ε / (2 Dc)`, then the
  radius `δ` of the subdivision, then the level `b = ε / (4 Dc C)` of the bad
  sets, and the span `δ'` last, only it being still free once the reach `η` is
  given. The window of the values is `[-m, m + 1]`, the times running to
  `(m − 1) + η + δ' ≤ m + 1`. The empty `κ` is not excluded: both products are the
  empty product `1`, and the factor `#κ + 1` in `Dc` is what keeps the last step
  free of a division by `#κ`.

  **What this item is *not* for.** Identifying two laws that agree along a dense
  set of times does not go through it, and asks neither for compact closure nor
  for a modulus: that is
  `SkorokhodSpace.eq_of_forall_dense_forall_integral_evalPi_eq` of Milestone 6,
  and it spends the density on the Borel structure instead. What this item
  answers is the question in which the times of the hypothesis and the times of
  the conclusion are *different* — comparing a subsequential limit with the
  convergence along `T`, which is EK 3.7.8(b).
* `MeasureTheory.abs_integral_sub_integral_smul_restrict_le` — **proved
  2026-09-19**, and general measure theory: for a probability measure `μ`, a
  measurable `A` with `(μ Aᶜ).toReal ≤ ε₀ < 1`, and a measurable `g` with
  `|g| ≤ C`, conditioning on `A` moves the integral by at most `2 C ε₀`,
  `|∫ g dμ − ∫ g d((μ A)⁻¹ • μ.restrict A)| ≤ 2 C ε₀`.

  **The bound carries no division.** With `p = (μ A).toReal` and
  `q = (μ Aᶜ).toReal` the difference is `∫_{Aᶜ} g dμ − (p⁻¹ − 1) ∫_A g dμ`. The
  first term is at most `C q`; in the second the factor `p⁻¹ − 1` grows without
  bound as `p` falls, but the integral it multiplies falls with it, `|∫_A g dμ|
  ≤ C p`, and the product is `(p⁻¹ − 1)(C p) = C (1 − p) = C q` **exactly**. The
  two halves are equal, and the naive `2 C ε₀ / (1 − ε₀)` is not what comes out.
  `ε₀ < 1` is spent on the positivity of `μ A` and on nothing else; `0 ≤ ε₀` and
  `0 ≤ C` are consequences and not hypotheses.

  The library's bundled counterpart is `MeasureTheory.FiniteMeasure.normalize`
  (`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`), which
  `toMeasure_normalize_eq_of_nonzero` identifies with this same measure; the
  plain `Measure` form is the one stated because every consumer here speaks of
  `Measure`.
* `SkorokhodSpace.exists_times_forall_dist_integral_evalPi_le_of_measure_compl_le`
  — stage (A), **proved 2026-09-19**. The previous estimate under
  `μ Aᶜ ≤ ENNReal.ofReal ε₀` with `0 ≤ ε₀ < 1` in place of `μ Aᶜ = 0`, with the
  same conclusion `≤ ε` under `8 (∏ i, ‖F i‖) ε₀ ≤ ε`.

  **This is where the chain joins what tightness gives.** Every statement of the
  oscillation chain above hypothesises `μ Aᶜ = 0`, while
  `exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure` — the only
  bridge from a compact set of *measures* to a compact set of *paths* — concludes
  `μ Kᶜ ≤ ε` for a given positive `ε`, and for `ε = 0` gives nothing: a tight law
  on `D(ℝ, E)` has in general no relatively compact carrier of full measure.
  Without this item not one statement of the chain applies to the members of a
  tight family, which is what the chain was built for, and EK 3.7.8(b) is its
  only consumer.

  **The chain is not rewritten.** The estimate is bought where it already holds,
  for the law conditioned on `B = closure A`, and carried back by
  `MeasureTheory.abs_integral_sub_integral_smul_restrict_le` — one comparison,
  used twice, once at each of the two families of times. The closure and not `A`
  itself, because conditioning needs a measurable set while `A` is only assumed
  to have compact closure; passing to it costs nothing, since
  `μ (closure A)ᶜ ≤ μ Aᶜ` and `closure (closure A) = closure A`. The hypothesis
  `8 (∏ i, ‖F i‖) ε₀ ≤ ε` divides `ε`: half to the conditional law, half to the
  two comparisons at `2 (∏ i, ‖F i‖) ε₀` each, the product of the norms being the
  bound on the integrand. A consumer holds `ε` and the test functions fixed and
  takes `ε₀` from tightness, so the hypothesis constrains the compact set it asks
  for and not `ε`. It is **not** a statement that `ε₀` may be dropped: at `ε₀`
  comparable to `ε` it says nothing, and it should not, a law being free to put
  mass `ε₀` on paths of arbitrarily wild oscillation.
* `SkorokhodSpace.exists_times_frequently_dist_integral_evalPi_le_of_isCompact_closure`
  — stage (A), **proved 2026-09-19**. The displacement estimate **uniformly in a
  sequence of laws**: for `A ⊆ D(ℝ, E)` with compact closure, a sequence `μ n` of
  laws with `μ n Aᶜ = 0`, a finite family `F : κ → (E →ᵇ ℝ)`, prescribed times
  `t : κ → ℝ` of the window `[-m, m − 1)`, a reach `η ∈ (0, 1]` and an `ε > 0`,
  there are times `s i ∈ [t i, t i + η)` and a span `δ' > 0` such that **for
  infinitely many `n`** and every family `s' i ∈ [s i, s i + δ')`,
  `|∫ ∏ F i (f (s' i)) dμ n − ∫ ∏ F i (f (s i)) dμ n| ≤ ε`.

  Nothing is asked of the `F i` beyond boundedness and continuity, and nothing of
  the modulus: it is discharged from the compactness of the closure of the values
  over a bounded window, exactly as in the single law version.

  **This is the piece EK 3.7.8(b) needs that the single law version does not
  supply.** There the times of the hypothesis and the times of the conclusion are
  different, and the displacement from one to the other has to be paid uniformly
  in the sequence, the sequence being what the limit is taken along; a
  displacement bought for each `μ n` separately, at times depending on `n`,
  compares nothing. The times here do not depend on `n`, and what does is the set
  of `n` at which the bound holds.

  **The conclusion is `∃ᶠ` and not `∀`, and that is not a weakening to be
  repaired.** A time good for every member of a sequence at once need not exist:
  each law's bad times are of small Lebesgue measure but their union over the
  sequence may cover the window, and the inequality that would be needed,
  `∫ limsup ≤ limsup ∫`, is false — Mathlib's `limsup_lintegral_le` states the
  converse. The `liminf` form at the level of the bad times,
  `SkorokhodSpace.exists_time_liminf_measure_setOf_exists_edist_lt`, is what this
  item lifts, and a time good along a subsequence is what the consumer has at its
  disposal anyway, being an argument about subsequential limits. The finite
  version with `∀` is `exists_time_mem_Ico_forall_measure_setOf_exists_edist_lt`,
  and the factor it pays is the cardinality.

  The constants are those of
  `exists_times_forall_dist_integral_evalPi_le_of_isCompact_closure` and are not
  chosen afresh: they depend on `A`, `F`, `m`, `η` and `ε` and on no law, which is
  what makes the uniform statement possible at all. **Only the span differs**, and
  it carries the extra factor `#κ + 1` — the price of the common shift of
  `exists_times_frequently_forall_measure_setOf_exists_edist_lt`. Since the span
  is the last constant chosen and is free, the passage from one law to a sequence
  costs nothing else. The span is fixed before the time, the `liminf` sitting at
  the shift alone.
* `SkorokhodSpace.exists_times_frequently_dist_integral_evalPi_le_of_measure_compl_le`
  — stage (A), **proved 2026-09-19**. The same under a bound `μ n Aᶜ ≤ ε₀` on the
  missing mass in place of a carrier of full measure, and **this is the form in
  which a tight family is reached**: what
  `exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure` delivers for a
  relatively compact family is `μ Kᶜ ≤ ε₀` for a given positive `ε₀` and for
  `ε₀ = 0` nothing, so without this step the uniform estimate applies to no member
  of such a family.

  The passage is that of
  `exists_times_forall_dist_integral_evalPi_le_of_measure_compl_le`, made for each
  member of the sequence: the estimate is bought for the conditional laws
  `(μ n (closure A))⁻¹ • (μ n).restrict (closure A)` and carried back by
  `MeasureTheory.abs_integral_sub_integral_smul_restrict_le`. The comparison is
  made **inside** the `∃ᶠ`, at the one `n` the frequently bound names, so the
  conditioning costs nothing in the quantifier: the times and the span are those
  of the conditional sequence and are independent of `n`. The hypothesis
  `8 (∏ i, ‖F i‖) ε₀ ≤ ε` divides `ε` as in the single law version.
* `SkorokhodSpace.tendsto_integral_evalPi_of_forall_tendsto_nhdsGE` — stage (A),
  **proved 2026-09-19**. The finite dimensional distributions of a law on
  `D(ℝ, E)` are right continuous in the times: if `s k i → t i` within
  `[t i, ∞)` for each `i` of a finite family, then
  `∫ ∏ i, F i (f (s k i)) dμ → ∫ ∏ i, F i (f (t i)) dμ`.

  Dominated convergence with the constant bound `∏ i, ‖F i‖`, integrable because
  the measure is finite; pointwise it is right continuity of the path at each
  coordinate, `continuousWithinAt_Ioi_iff_Ici` turning Mathlib's
  `IsRightContinuous` — stated on `Set.Ioi` — into the form on `Set.Ici` that a
  family of times allowed to sit at `t i` needs, and then `tendsto_finsetProd`.
  The filter is `𝓝[≥] (t i)` and not `𝓝[>] (t i)` because the good times of the
  oscillation chain lie in `Set.Ico (t i) (t i + η)`, which contains `t i`.
  Nothing holds with the times approached from the left: a path is free to jump
  at `t i`.
* `SkorokhodSpace.integral_evalPi_eq_of_forall_exists_mem_Ico` — stage (A),
  **proved 2026-09-19**. If for every `ε > 0` and every `η > 0` there are times
  `u i ∈ [t i, t i + η)` with
  `|∫ ∏ i, F i (f (u i)) dμ − ∫ ∏ i, F i (f (u i)) dν| ≤ ε`, then the two finite
  dimensional integrals at the times `t` themselves are **equal**.

  **The times are allowed to move with `ε`, and that is the whole point.** The
  oscillation chain buys its estimate one `ε` at a time and places the good times
  where the bad times leave room; it can promise neither a time independent of
  `ε` nor the prescribed time itself, and
  `exists_times_forall_dist_integral_evalPi_le_of_isCompact_closure` says so in
  its own statement. Reading its output at `ε = η = 1/(k+1)` gives a sequence of
  families converging to `t` from the right at which the two laws differ by
  `1/(k+1)`, and the right continuity above carries both sides to the limit. No
  compactness, no modulus and no density enter; only right continuity of the
  paths and the finiteness of the two measures.
* `SkorokhodSpace.eq_of_forall_exists_mem_Ico_dist_integral_evalPi_le` — stage
  (A), **proved 2026-09-19**. Two laws on `D(ℝ, E)` that can be matched
  arbitrarily well at times arbitrarily close on the right to *any* prescribed
  ones are equal. This is the previous item at every finite family of times,
  followed by `SkorokhodSpace.eq_of_forall_dense_forall_integral_evalPi_eq` of
  Milestone 6 along `Set.univ`: the previous item gives the finite dimensional
  distributions at all times, so no density has to be arranged and none is lost.

  **This is the reduction of EK 3.7.8(b), and it says what remains of that
  theorem.** Comparing a subsequential limit `ν` with the limit `μ` along `T` may
  not be done at the times of `T`, by
  `SkorokhodSpace.exists_countable_dense_forall_setOf_leftLim_ne_one`; the
  oscillation bound moves the times to the right at a cost the compactness
  controls, and produces exactly this hypothesis. What this item removes from the
  remainder is the bookkeeping of the moving times — the estimate no longer has
  to be arranged at a fixed family of times, and the statement it has to be
  arranged for is a single inequality.
* `SkorokhodSpace.exists_times_mem_Ico_dist_integral_evalPi_le_of_tendsto` —
  stage (A), **proved 2026-09-19**. The estimate of EK 3.7.8(b): for a relatively
  compact `S`, a sequence in it converging weakly to `ρ`, a law `ν` whose finite
  dimensional distributions along a dense `T` are the limits of those of the
  sequence, a finite family `F` with prescribed times `t`, an `ε > 0` and a reach
  `η > 0`, there are times `u i ∈ [t i, t i + η)` at which the finite dimensional
  integrals of `ν` and of `ρ` differ by at most `ε`. It is the five term chain
  described at the theorem above, and it is what that theorem's hypothesis asks
  for, verbatim.

  Two things that a reader will look for. The window `[-m, m − 1)` that the
  displacement estimates ask of the prescribed times is **produced**, not
  hypothesised: `κ` being finite, `m = (sup ⌈|t i|⌉) + 2` serves, and the empty
  `κ` is not a special case. And the span `w` inside which the two time families
  `u` and `u'` are chosen is **one for all coordinates** — the least of `δ`, of
  what is left of `δ_ρ` after `s i` has moved away from `sρ i`, and of what is
  left of `η` after `s i` has moved away from `t i`, obtained as the minimum of a
  `Finset` of positive reals to which `δ` is added so that it is nonempty when
  `κ` is not.
* `SkorokhodSpace.eq_of_tendsto_of_forall_tendsto_integral_evalPi` — stage (A),
  **proved 2026-09-19**. A weak limit `ρ` of the sequence itself is the law `ν`
  whose finite dimensional distributions along `T` the sequence approaches. It is
  the item above at every finite family, closed by the reduction, and then
  `ProbabilityMeasure.toMeasure_injective`
  (`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:146`) to state it in
  `ProbabilityMeasure`, which is where the theorem wants it.

  **The `Fintype` instance is passed by name and not found by instance search.**
  The reduction quantifies over `(_ : Fintype κ)` *explicitly*, so what it hands
  over is a hypothesis and not an instance; a `haveI` introduces a **second**
  one, and under two instances the two products `∏ i, …` are no longer the same
  term — not for `exact`, and not for `linarith`'s atoms either. Naming the
  instance binder of the item above and passing it is the whole fix.
* `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional` — stage (A),
  **proved 2026-09-19**. The same conclusion for a tight sequence, from the
  previous item and `isCompact_closure_of_isTightMeasureSet`
  (`Mathlib/MeasureTheory/Measure/Prokhorov.lean:530`). That lemma asks of the
  path space `[T2Space]` and `[BorelSpace]` and nothing further, so this step
  adds no hypothesis on `E`: the bundle is the previous item's, and it is spent
  on Prokhorov's *converse* half inside
  `exists_isCompact_tendsto_iSup_modulusBased_of_isCompact_closure`. The set is
  the range of the sequence, which is the form both the hypothesis and
  `fact:relcompact` are reached in; for a tight family of which the sequence is
  a part, the previous item with `S` that family is the statement.
* `SkorokhodSpace.tendstoInDistribution_of_isTight_of_tendsto_finiteDimensional`
  — stage (A), **proved 2026-09-19**. The previous item for random variables, on
  Mathlib's `MeasureTheory.TendstoInDistribution`: path valued `X n` whose laws
  are tight and whose finite dimensional distributions along a dense `T`
  converge to those of `Z` converge to `Z` in distribution. `Measure.map` and
  `integral_map` carry the one form to the other, and the finite product of the
  test functions is measurable and not continuous, being
  `SkorokhodSpace.measurable_eval` at each time followed by the bounded
  continuous factor.
* `SkorokhodSpace.tendstoInDistribution_eval_of_isTight_of_tendsto_finiteDimensional`
  — stage (A), **proved 2026-09-19**. **The marginal at a time that need not lie
  in `T`**, and this is the milestone as a supplier for Milestone 10 of the
  roadmap **MartingaleProblems**. Hypothesis (a) of `mpSolution_of_tendsto` is
  convergence in distribution of the value at *each* time of the index set it
  runs over; what an approximating family delivers is convergence of the finite
  dimensional distributions along **one** dense set of times. The two are not
  the same statement, and the gap is not cosmetic:
  `exists_countable_dense_forall_setOf_leftLim_ne_one` exhibits a law and a
  countable dense `T` no time of which is a continuity time of the law, so a
  time of the index set may stand in no useful relation to `T` whatever. What
  closes it is the weak convergence on the path space, which is a statement
  about no particular time, read back at a single time by
  `tendstoInDistribution_eval`; the times at which that reading is available are
  dense by `exists_countable_dense_continuity` and cocountable by
  `countable_setOf_measure_leftJump_ne_zero`.

  **The index of these three is `ℝ` and not the `ι` of Milestone 1**, and that is
  inherited: the compactness criterion `isCompact_closure_iff` of Milestone 7,
  through which every one of them passes, is stated over `D(ℝ, E)`. What confines
  *that* to `ℝ` is the converse half and the rigid-index witness
  `not_isCompact_closure_of_rigid` — the criterion is false over the Cantor set
  as index. That witness carries the hypothesis `hrigid`, that every time change
  fixing the base point of small norm is the identity, and what discharges it at
  the Cantor set is the factor `3` between scales.

  It matters for a reader of **MartingaleProblems**, whose path map `jumpPathD`
  lands in `D(ℝ≥0, E)`: `tendstoInDistribution_eval` is index-generic and applies
  there, these three are stated over `ℝ` and do not. That is the one place where
  the chain from tightness to hypothesis (a) of `mpSolution_of_tendsto` parts,
  and it parts at an index and not at a statement. What joins the two is
  `SkorokhodSpace.isClosedEmbedding_extendNNReal` of Milestone 7, along which
  every statement over `ℝ` is read at `ℝ≥0`; 53 declarations of this file stand
  over the index `ℝ`, so the crossing is made once and not repeated.
* `SkorokhodSpace.exists_countable_dense_continuity` — stage (A). For a single
  probability measure `μ` the times `t` with `μ {f | f⁻ t = f t} = 1` contain a
  countable dense set. The countability half is
  `SkorokhodSpace.countable_setOf_measure_leftJump_ne_zero`, for any finite
  `μ`: the set of `t` with `μ {f | t ∈ leftJumpSet f} ≠ 0` is countable. The
  density half is Baire, and it asks **nothing of the index beyond the bundle of
  Milestone 1**. That is worth saying because it looks as though it should ask
  for an index without isolated points: an isolated point carries no jump, since
  where `𝓝[<] t = ⊥` the left limit *is* the value, so such a `t` is not in the
  exceptional set at all and the Baire argument never meets it.

  The engine is `SkorokhodSpace.finite_setOf_le_measure_largeLeftJump`: for
  `ε > 0`, `c ≠ 0` and compact `K` the times `t ∈ K` with
  `c ≤ μ {f | t ∈ largeLeftJumpSet f ε}` are finitely many. Its proof reads an
  infinite such family as a sequence of distinct times, applies continuity from
  above to the tails `⋃ k ≥ n, A k` — the finiteness of `μ` is spent exactly
  here — and obtains a *single* path with infinitely many `ε`-jumps in `K`,
  which `IsCadlag.finite_largeLeftJumpSet_inter` forbids. **No jump is
  counted.** The classical argument integrates the number of `ε`-jumps in the
  window against `μ` and therefore needs `{f | (largeLeftJumpSet f ε ∩ K).ncard
  ≤ M}` to be measurable, which the coordinates do not give; this one needs
  `measure_mono` and nothing else.

  The measurability it does need is
  `SkorokhodSpace.measurableSet_largeLeftJump` and
  `SkorokhodSpace.measurableSet_leftJump`, and both rest on
  `SkorokhodSpace.measurable_leftLim_eval` — the left limit at a fixed time is a
  pointwise limit of evaluations along a sequence increasing to `t`, which
  exists because the index is first countable, and is the value itself where
  `𝓝[<] t = ⊥`. The decomposition of the jump event over the jump size is
  `SkorokhodSpace.setOf_mem_leftJumpSet_eq_iUnion`.
* `SkorokhodSpace.continuous_postcomp` — stage (A). For continuous `h : E → E'` the induced
  map `SkorokhodSpace.postcomp h : D ι E → D ι E'`, `f ↦ h ∘ f`, is well defined
  and continuous; with `SkorokhodSpace.measurable_postcomp`, from Milestone 6.
  Together with `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` this is
  the continuous mapping theorem in the form the next item needs.

  **The map and its measurability are proved, 2026-09-19.**
  `SkorokhodSpace.postcomp` takes a bundled `C(E, E')`, because its consumers —
  `MeasureTheory.Measure.map (postcomp h)` and `Continuous (postcomp h)` — want
  a map of one argument, and a bounded continuous test function reaches it
  through `BoundedContinuousFunction.toContinuousMap`. Well definedness is
  **Mathlib's** `IsCadlag.continuous_comp`
  (`Mathlib/Topology/Order/Cadlag.lean:119`) and is not restated here;
  `SkorokhodSpace.measurable_postcomp` is
  `SkorokhodSpace.measurable_of_measurable_eval` applied coordinatewise and does
  not go through the continuity.

  **The continuity is proved as well, 2026-09-19, and it has four named
  inputs.**

  - `IsCompact.exists_pos_forall_dist_image_lt` — the value space estimate: a
    continuous map is uniformly continuous near a compact set, with the first
    point confined to `K` and the second free, which is *not*
    `IsCompact.uniformContinuousOn_of_continuous`, that one confining both. Its
    proof is `lebesgue_number_lemma_of_metric` applied to the cover of `K` by
    the preimages of the `ε / 2`-balls of `E'`.
  - `SkorokhodSpace.distWith_postcomp_le` — the window estimate, at one radius
    and one time change, anchored at the first path because `distWith` is not
    symmetric.
  - `SkorokhodSpace.totallyBounded_image_exhaustion` — the window values of a
    single càdlàg path are totally bounded, the bridge from the closed ball to
    the interval `IsCadlag.totallyBounded_image_Icc` speaks of being
    `ordConnected_exhaustion`.
  - `SkorokhodSpace.intWith_postcomp_le` — the passage to the integral over the
    window radius, and **the only one of the four that is not a pointwise
    bound**. A small integral does not make the integrand small at every radius;
    it makes the radii at which `distWith` exceeds a threshold `δ₁` small in
    Lebesgue measure, by at most `exp M / min 1 δ₁` times the integral, and on
    them the truncated integrand is paid for by `1`. The tail beyond the radius
    `M` is `exp (-M)`. So the metric of Milestone 4 is spent twice in this one
    statement: the truncation at `1` bounds the exceptional radii and the weight
    `exp (-u)` both bounds their measure and supplies the tail.

  The compact set the first input is applied to is the closure of the window
  image of the centre, compact by the third input together with
  `[CompleteSpace E]` — and the completeness is not avoidable, a continuous map
  on a non complete space failing to be uniformly continuous near a merely
  totally bounded set. The assembly chooses `M` by `Real.log`, `δ₁` by the first
  input, and the radius of the ball as
  `min (ε / 4) (ε / 4 * min 1 δ₁ / exp M)`; `SkorokhodSpace.intDist_comm` keeps
  the centre in the first argument, where the modulus is known, and
  `exists_lt_of_ciInf_lt` produces the time change that the infimum only
  approaches.
  **The forward direction of the reduction is proved with it**, as
  `SkorokhodSpace.isTightMeasureSet_map_postcomp`: a tight family of laws on
  `D ι E` has tight images on `D ι E'`. It is `MeasureTheory.IsTightMeasureSet.map`
  with the continuity above, plus the same index bookkeeping
  `isTightMeasureSet_map_extendNNReal` of Milestone 9 does; the converse is not
  it read backwards and needs the criterion.

* `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` — stage (B). The
  reduction to
  real-valued paths. Let `S` be a set of Borel probability measures on `D ι E`
  satisfying compact containment — for every `ε > 0` and `m` a compact `K ⊆ E`
  with `μ {f | ∀ t ∈ B m, f t ∈ K} ≥ 1 - ε` for every `μ ∈ S` — and let
  `H ⊆ E →ᵇ ℝ` be dense in the topology of uniform convergence on compact sets.
  Then `S` is tight if and only if `(· .map (postcomp h)) '' S` is tight in
  `D ι ℝ` for every `h ∈ H`. The forward direction is the previous item; the
  converse reads `SkorokhodSpace.isTightMeasureSet_iff`, whose first clause is
  the compact containment hypothesis verbatim and whose second has to be
  recovered from the real-valued moduli.

  **That recovery is the work, it is not the criterion applied, and the obstacle
  is named rather than guessed.** On a compact `K` the metric of `E` is recovered
  from finitely many `h ∈ H` — a finite `ε`-net of `K` and the functions
  `y ↦ min (dist y x_j) 1` approximated out of `H` — so what is wanted is a
  subdivision on whose cells *all* of `h_1 ∘ f, …, h_N ∘ f` oscillate little. Each
  `h_i` supplies its **own** `δ`-sparse based subdivision, and
  `SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells` bounds the oscillation of a
  subdivision only by that of one it **refines** — the factor `2` being the price
  of moving the left endpoint, and sharp. So a common refinement is what is
  needed, and a common refinement must carry every interior node of every `t^i`.

  **A common refinement exists and is useless, and that is proved, 2026-09-19.**
  `SkorokhodSpace.exists_eq_castSucc_of_cells` is the mechanism — a refinement
  carries every interior node of the subdivision it refines — and
  `SkorokhodSpace.exists_isSubdivisionBased_pair_forall_not_cells` is the
  refutation: for **every** `δ' > 0` there are two based `1/2`-sparse subdivisions
  of `exhaustion 0 3` admitting no `δ'`-sparse common refinement, namely
  `![-4, 0, 1, 4]` and `![-4, 0, 1 + γ, 4]` with `γ = min (δ'/2) 1`. For *given*
  subdivisions a common refinement does exist — the union of the nodes is sparse
  below its smallest gap — so what is refuted is exactly what a criterion of the
  form `∃ δ, ∀ paths` needs: a sparseness chosen before the paths. The refuted
  class is the larger one, the common refinement not being required to be based.

  **Reading the family as one path into `ℝ^N` does not help either**: the
  hypothesis controls the image law of each `h_i` separately, that is the
  marginals, and a subdivision for the vector path is exactly what is missing.

  **The second route is refuted as well, 2026-09-19, and by the same witness.**
  What was left to look at was Ethier–Kurtz' subdivision-free modulus `w''`, the
  three point quantity `sup min (d (x t) (x t₁)) (d (x t₂) (x t))` over
  `t₁ ≤ t ≤ t₂` of span `δ`; it was the candidate because it is read at one time
  triple and needs no common refinement. It does not carry, and what stood here as
  a remark about vectors — under `d ≈ max over i`, `min (max a) (max b)` is not
  bounded by `max over i of min (a i) (b i)`, take `a = (1,0)`, `b = (0,1)` — is
  now a statement about paths.

  The witness is one path with **two jumps in different coordinates**,
  `SkorokhodSpace.twoJump γ` in `D(ℝ, ℝ × ℝ)`: the first coordinate steps from `0`
  to `1` at time `1`, the second at `1 + γ`. Two theorems read it, one per route:

  * `SkorokhodSpace.exists_isCompact_modulusBased_postcomp_eq_zero` — for every
    `0 < δ < 1` there are a path of `D(ℝ, ℝ × ℝ)` and a compact `K` containing
    every one of its values such that two **bounded continuous** functions
    (`SkorokhodSpace.clipFst`, `SkorokhodSpace.clipSnd`) recover the metric of
    `ℝ × ℝ` on `K` *with equality*, both image paths have `modulusBased` equal to
    `0` at scale `δ`, and the path itself has `modulusBased` at least `1`. The
    finite family is granted the best form of its own hypothesis and the inference
    still fails.
  * `SkorokhodSpace.exists_min_edist_postcomp_eq_zero` — at the triple
    `1 - γ < 1 < 1 + γ`, of span `2 γ`, the three point quantity of the path is at
    least `1` and that of **both** images is exactly `0`.

  The mechanism is one sentence: each image sees one of the two jumps and is blind
  to the other, so each image is a single step and each has modulus `0`, while the
  pair has two jumps at distance `γ` that no `δ`-sparse subdivision separates.
  That last is `SkorokhodSpace.one_le_modulus_twoJump`, and it needs no upper bound
  on `δ` — beyond the diameter of the window there is no subdivision at all and the
  modulus is `⊤`, which is the `ℝ≥0∞` valuation of `SkorokhodSpace.modulus` paying
  for itself a third time.

  **What is *not* refuted is the criterion**, and the difference is the whole
  content. It quantifies over a **dense** class `H`, and `H` contains functions
  that see both jumps at once: `p ↦ p.1 + 2 * p.2` separates `(0,0)`, `(1,0)`,
  `(1,1)`, so its image path has two jumps at distance `γ` and a modulus of its
  own. A proof must therefore choose its test function **after** the path.

  **And what is refuted is narrower than it was stated to be, 2026-09-19.** The
  two theorems above rule out a finite family that **recovers the metric** on the
  compact set, which is what `clipFst` and `clipSnd` do. They do **not** rule out
  the family this roadmap actually names — the clipped distances
  `y ↦ min (dist y x_j) 1` to the points of a net.
  `SkorokhodSpace.one_le_modulus_postcomp_clipDist_twoJump` is the check, at the
  very path that refutes the other family: the single function
  `SkorokhodSpace.clipDist (1, 0)`, the clipped distance to the value **between**
  the two jumps, has image path `1, 0, 1` and modulus at least `1`.

  The reason is that the three point quantity compares both displacements to the
  **common middle value**, and the distance to that one value turns both
  comparisons into differences of its own values at once.
  `SkorokhodSpace.min_edist_postcomp_clipDist` says so with **equality** up to the
  clip: the image quantity is the quantity of the path, capped at `1`. So the
  level is `min η 1` — a function of `η` alone, not of the path, not of a compact
  set, not of a net — which is the uniformity that had to be checked before
  anything was built.

  **The passage now has three links, and two of them are proved.**

  1. `modulusBased` large ⟹ three point quantity large. The **hard** half of
     Ethier–Kurtz' comparison of `w'` with `w''`, and the only link that is open.
     Its **first half is proved**, and it is a structure theorem:
     `SkorokhodSpace.exists_forall_edist_lt_of_forall_min_edist_lt` says that a
     window on which the three point quantity is below `η` carries exactly **one
     break** — a single time `τ` before which the path stays within `η` of its
     value at the window's left end, and from which on it stays within `η` of its
     value at `τ`. The break is the first time the displacement reaches `η`, an
     infimum that right continuity makes a minimum, and the hypothesis is then
     read at a **single** triple `(u, τ, t₂)`.
     `SkorokhodSpace.edist_le_of_forall_min_edist_lt` is the same statement as an
     oscillation bound: `edist (f τ) (f u) + η`, the displacement **at** the break
     plus `η`.

     **The greedy subdivision that this item named until 2026-09-19 does not
     close the link, and the structure theorem says why.** Greedy cells — each
     run from its left endpoint as far as the oscillation allows — have
     oscillation `≤ η`, but they are not longer than `δ`; what the hypothesis
     gives is that no *two consecutive* cells fit in a window of span `δ`. So the
     nodes have to be thinned to every other one, and the merged cell measures
     its oscillation from the far left endpoint, which costs the displacement at
     the break in between — and that displacement is precisely the quantity the
     three point hypothesis leaves free. A path may jump by any amount at one
     time without violating it; the condition forbids two large displacements in
     one window, not one.

     **What the link needs instead**, written out at the section in
     `SkorokhodSpace/Suggested.lean`: nodes at the jumps of size `> 2 * η`, which
     are more than `δ` apart under the hypothesis and finitely many in a compact
     window (`IsCadlag.finite_largeLeftJumpSet_inter`). That they are far apart is
     `SkorokhodSpace.jump_le_two_mul_of_forall_min_edist_lt`, **proved**: a jump
     larger than `η` at one time of the window bounds the jump at every earlier
     time of it by `2 * η`. The threshold is `2 * η` and not `η`, and the reason
     is worth keeping: the naive triple `(t₁, p, q)` at two jumps has
     `edist (f q) (f p)` for its second displacement, which the jump at `q` does
     not bound — the path may return to `f p` just before `q`. Both readings that
     do work run their outer time up to `q`, and the only property of `q` either
     uses is that `edist (f q) (f t)` exceeds `η` on a left neighbourhood, which
     is why the hypothesis there is **strict**. Between two consecutive such jumps
     the
     window is filled with a uniform grid of `⌈(q-p)/(2*δ)⌉` cells, whose lengths
     lie in `(δ, 2*δ]` and whose oscillation the structure theorem bounds by
     `4 * η`. Two numbers of the original
     statement change with it: the hypothesis is read at span `2 * δ`, not `δ` —
     a path drifting at the largest slope the hypothesis at span `δ` allows moves
     by nearly `2 * η` across a cell of length `δ` — and the constant the route
     gives is `4`, not `2`. Neither matters to the consumer, which asks only that
     the modulus vanish as `δ → 0`.

     Of that route the **cell estimate** is proved,
     `SkorokhodSpace.edist_le_four_mul_of_forall_min_edist_lt`: a window whose
     jumps are all at most `2 * η` — the hypothesis asked on `Set.Ioc u v` and not
     at `u`, a cell not seeing the jump at its own left endpoint — has oscillation
     at most `4 * η`.

     **And the base point, which that route called its one point to decide, is
     not a point to decide but a refutation, 2026-09-19.**
     `SkorokhodSpace.IsSubdivisionBased` demands the base point among the nodes
     **and** every gap longer than `δ`; a jump in `Set.Ioo t₀ (t₀ + δ)` can
     therefore be put at no cell boundary, and is charged in full to the cell
     beginning at `t₀`. The unit step `SkorokhodSpace.step` has three point
     quantity `0` at every triple and every span
     (`SkorokhodSpace.min_edist_step_eq_zero`) and based modulus at least `1` at
     every `δ ≥ 1` (`SkorokhodSpace.one_le_modulusBased_step`), so **no** finite
     constant and no reading of the span makes the link true:
     `SkorokhodSpace.not_forall_modulusBased_le_mul_of_forall_min_edist_lt`,
     proved with the global hypothesis and hence against the strongest reading.

     **The link carries a boundary term at the base point**, which is what the
     classical statement on `[0, ∞)` writes as `sup_{t < δ} d(x t, x 0)` and what
     this roadmap never had:

     > `modulusBased t₀ m f δ ≤ 4 * η + 2 * ⨆ r ∈ Set.Ico (t₀ - 2*δ) t₀, edist (f r) (leftLim f t₀) + ⨆ r ∈ Set.Ico t₀ (t₀ + 2*δ), edist (f r) (f t₀)`,

     one summand for the cell beginning at `t₀` and one for the cell ending
     there, both sides suffering the same defect. The left one is measured
     against `leftLim f t₀` and **not** against `f t₀`: a jump **at** the base
     point sits at the left endpoint of the cell beginning there and is not seen
     by it, and measured against `f t₀` the term would not vanish and the
     criterion would be false for every path jumping at `t₀`.

     The term is `SkorokhodSpace.basePointOsc`, and that it **vanishes** is
     `SkorokhodSpace.tendsto_basePointOsc`, proved: the correction does not reach
     the consumer, which asks only that the modulus vanish as `δ → 0`, the right
     summand doing so by right continuity and the left one by the existence of
     the left limit. That the left one must be read against `leftLim f t₀` is
     `SkorokhodSpace.iSup_edist_step_left_eq_one`, also proved: at the unit step
     and the base point `1` the same supremum against `f t₀` is `1` at every `δ`.
     For a **family** the vanishing has to be uniform, and this item read that
     for a while as a hypothesis the criterion would have to carry. It is **not**
     one, 2026-09-19: it follows from the hypothesis the criterion already has,
     by `SkorokhodSpace.basePointOsc_le_three_mul_modulusBased` on the image side
     and the two transport statements below. What remains true is that the
     uniformity is a real condition on the family and not a formality — it says
     the paths do not accumulate displacement at the one time the subdivisions
     are pinned at, and
     `SkorokhodSpace.not_isCompact_closure_of_jumps_at_basePoint` is the same
     phenomenon from the other side.

     **The corrected link splits in two, and the analytic half is proved**,
     2026-09-19: `SkorokhodSpace.subdivisionOsc_le_of_forall_min_edist_lt` says
     what a *given* subdivision costs. It asks two things of it — every gap at
     most `2 * δ`, and every cell either free of jumps larger than `2 * η` in its
     **interior** or adjoining the base point — and returns
     `4 * η + 2 * SkorokhodSpace.basePointOsc t₀ f (2 * δ)`. Neither strict
     monotonicity, nor coverage of the window, nor sparseness is used, so the
     theorem is independent of `SkorokhodSpace.IsSubdivisionBased`. The exemption
     it grants the two cells at `t₀` is exactly the one the refutation forces and
     no wider, and the factor `2` on the left cell is not slack: that cell
     compares two *different* times of `Set.Ico (t₀ - 2*δ) t₀`, and the only
     value available to route between them is `Function.leftLim f t₀`
     (`SkorokhodSpace.edist_le_two_mul_basePointOsc`).

     That the corrected inequality survives its own counterexample is
     `SkorokhodSpace.one_le_four_mul_add_two_mul_basePointOsc_step`: at the unit
     step and `δ = 1` the right hand side is at least `1` at every level `η`,
     which is the lower bound `SkorokhodSpace.one_le_modulusBased_step` puts on
     the left hand side.

     **What is left is the combinatorial half**: a `t : Fin (n + 1) → ℝ` with
     `SkorokhodSpace.IsSubdivisionBased t₀ M δ t`, every gap in `(δ, 2 * δ]`, and
     no jump larger than `2 * η` in the interior of any cell but the two at `t₀`.
     The node-placing rule that produces it is written out at its section in
     `SkorokhodSpace/Suggested.lean`: from a node `x`, the next node is the jump
     in `Set.Ioc (x + δ) (x + 2*δ)` if there is one; otherwise `(x + q) / 2` for
     the jump `q` in `Set.Ioc (x + 2*δ) (x + 3*δ)` if there is one; otherwise
     `x + 2 * δ`. Its gap lies in `(δ, 2 * δ]` in all three cases **with no
     hypothesis at all**, which is what skipping over `Set.Ioc x (x + δ)` instead
     of looking into it buys; the invariant `J ∩ Set.Ioc x (x + δ) = ∅` is needed
     only for the jump-freeness, and the rule re-establishes it at its own output
     in each case, out of `SkorokhodSpace.two_mul_le_sub_of_forall_min_edist_lt`
     — two large jumps are at least `2 * δ` apart — and nothing else. The
     invariant is unavailable at the base point itself, which is precisely the
     cell the analytic half exempts, so the rule starts at `t₀` unconditioned.
     The middle case is the one that is easy to miss: without it a node at
     `x + 2 * δ` may land within `δ` of a jump, and then no admissible node
     reaches that jump.

     **The rule is built**, 2026-09-19: `SkorokhodSpace.nextNode`, with
     `SkorokhodSpace.lt_nextNode` and `SkorokhodSpace.nextNode_le` for the gap —
     unconditionally in `(δ, 2 * δ]` — and `SkorokhodSpace.notMem_Ioo_nextNode`
     and `SkorokhodSpace.notMem_Ioc_nextNode` for the jumps. It is stated over an
     abstract `2 * δ`-separated set `J`, nothing of `D(ℝ, E)` entering it, and
     `SkorokhodSpace.separated_setOf_lt_edist_leftLim` is the one line that hands
     the large jumps of a path to it. The asymmetry of the two jump statements is
     what makes the rule run at the base point: the invariant is unavailable
     there and the second statement does not need it, so it is re-established
     from the first node on.

     **The combinatorial half is complete**, 2026-09-19. The rule is iterated by
     `SkorokhodSpace.node`, with `SkorokhodSpace.strictMono_node`,
     `SkorokhodSpace.node_succ_sub_le` for the span, and
     `SkorokhodSpace.add_mul_le_node` for the linear growth that covers a window
     after finitely many steps. The two statements about jumps —
     `SkorokhodSpace.notMem_Ioc_node_succ` and
     `SkorokhodSpace.notMem_Ioo_node_succ` — carry over **without an induction**,
     one application of the single-step statements at the previous node being
     enough, because the invariant is re-established unconditionally. The one
     induction of the section is about the gaps and not about the jumps.

     **The mirror rule *is* `nextNode` read at `-x`**, on the reflected set
     `SkorokhodSpace.negSet`, and the half openness that looked like an
     obstruction is the reason. A jump at a node is carried by the cell that node
     opens, the cells being `Set.Ico`, so going right the rule reaches into
     `Set.Ioc (x + δ) (x + 2 * δ)` and going left into
     `Set.Ico (x - 2 * δ) (x - δ)` — and `x ↦ -x` is exactly what exchanges those
     two. `SkorokhodSpace.prevNode` is therefore one line, and its four
     statements — `SkorokhodSpace.prevNode_lt`, `SkorokhodSpace.le_prevNode`,
     `SkorokhodSpace.notMem_Ico_prevNode`,
     `SkorokhodSpace.notMem_Ioo_prevNode` — are their forward counterparts with
     `neg` pushed through. The left iteration is `SkorokhodSpace.pnode`.

     The two half sequences are joined at the base point by
     `SkorokhodSpace.nodeSeq`, indexed by `ℕ`; the branches agree at the join
     (`SkorokhodSpace.nodeSeq_of_ge`), which leaves two cases and not three in
     every statement about it. `SkorokhodSpace.cell_nodeSeq` is the cell
     condition in the exact disjunctive shape the analytic half asks for, so the
     two halves meet without an intermediate statement.
     `SkorokhodSpace.exists_subdivision_of_separated` is the combinatorial half
     entire: for a `2 * δ`-separated `J` and any window radius, a strictly
     increasing `t : Fin (n + 1) → ℝ` containing the base point, covering the
     window, with every gap in `(δ, 2 * δ]` and every cell but the two at the
     base point missing `J` in its interior. `Fin` enters there and nowhere else.

     **The corrected link is closed**, 2026-09-19, in the same run:
     `SkorokhodSpace.modulusBased_le_of_forall_min_edist_lt` —
     `modulusBased 0 m f δ ≤ 4 * η + 2 * SkorokhodSpace.basePointOsc 0 f (2 * δ)`
     for a path whose three point quantity stays below `η` on every window of
     span `2 * δ`. Nothing is computed in it beyond the two halves meeting: the
     window is `exhaustionMin_real` and `exhaustionMax_real`, and the sparseness
     of `SkorokhodSpace.IsSubdivision` is the gap bound read through
     `Real.dist_eq`. It is stated at the base point `0`, which is where the chain
     reads it; over a general base point the two window endpoints would have to
     be computed afresh, and no consumer asks for it.

     **And the boundary term costs the criterion no hypothesis of its own**,
     2026-09-19, which is the question the closing of the link raised and which
     had to be answered before the converse half was built. It is closed from
     both sides.

     *From above it is the modulus.*
     `SkorokhodSpace.basePointOsc_le_three_mul_modulusBased` —
     `basePointOsc 0 f δ ≤ 3 * modulusBased 0 m f δ` for `m > 0`. A based
     subdivision has the base point among its nodes and every gap longer than
     `δ`, so the cell beginning at `t₀` contains `Set.Ico t₀ (t₀ + δ)` entire and
     the cell ending there contains `Set.Ico (t₀ - δ) t₀` entire. The factor is
     `3` and not `2`: the left cell measures from its own left endpoint while the
     term measures against `Function.leftLim f t₀`, and that costs one triangle
     inequality, the left limit being reached by `le_of_tendsto` along `𝓝[<] t₀`.
     The hypothesis `0 < m` is used and is what puts the base point strictly
     inside the window, so that it has both a predecessor and a successor among
     the nodes; a consumer reads the statement at `m + 1`.
     `SkorokhodSpace.basePointOsc_le_three_mul_subdivisionOsc` is the same at a
     single subdivision.

     *From below it travels under post-composition*, and with the **same** test
     functions link 2 uses. What it needs and the three point quantity does not
     is **two** centres: the left half is measured against
     `Function.leftLim f t₀` and the right half against `f t₀`, and no single
     centre serves both. Both values lie in the compact set compact containment
     supplies — the left limit because a compact set is closed — so the same
     finite net serves both. `SkorokhodSpace.leftLim_postcomp` is what makes the
     left half readable: the left limit passes through post-composition with a
     continuous map, so the image path's own boundary term is what is bounded.
     The two halves are
     `SkorokhodSpace.min_edist_le_edist_postcomp_add` and
     `SkorokhodSpace.min_edist_leftLim_le_edist_leftLim_postcomp_add` pointwise,
     `SkorokhodSpace.min_iSup_edist_le_iSup_edist_postcomp` and
     `SkorokhodSpace.min_iSup_edist_leftLim_le_iSup_edist_leftLim_postcomp` under
     the supremum.

     **The two halves are not added into one statement**, and that is not
     laziness: `min (L + R) 2 ≤ min L 1 + min R 1` is false — at `L = 5`, `R = 0`
     the left side is `2` and the right side `1` — so a capped statement about
     the sum says less than the two capped statements about the summands. A
     consumer that wants the sum small argues that one summand is large.

     The one displacement estimate both link 2 and the boundary term rest on is
     `SkorokhodSpace.sub_le_dist_of_dist_clipDist_le`, stated once and spent
     twice at one centre by `le_min_dist_of_dist_clipDist_le` and once at each of
     two by the boundary term. It asks **no** positivity of `ρ`.

     **And the hypothesis on the test function was too strong until 2026-09-19.**
     `le_min_dist_of_dist_clipDist_le` asked `∀ y, dist (h y) (clipDist x y) ≤ ρ`
     — a bound at *every* point of `E`. The class `H` of the criterion is dense
     for uniform convergence **on compact sets**, so that bound is not what a
     consumer has. The statements now ask it only where they read it: at the
     three points of the triple, at the two values the boundary term is measured
     against, and at the path's values over the window. All of those lie in the
     compact set compact containment supplies, which is exactly where the density
     delivers.
  2. Three point quantity of the path ⟹ the same for the image under
     `SkorokhodSpace.clipDist (f t)`, capped at `1`
     (`SkorokhodSpace.min_edist_postcomp_clipDist`), and in the form a dense `H`
     supplies it, `SkorokhodSpace.le_min_dist_of_dist_clipDist_le`: a test
     function uniformly within `ρ` of the clipped distance to a point within `ρ`
     of the middle value still sees both displacements, up to `4 * ρ`. Two of the
     four `ρ` pay for the net, two for the density.
  3. Three point quantity of the image large ⟹ its `modulusBased` large. The
     **easy** half, `SkorokhodSpace.min_edist_le_two_mul_modulusBased`: in a
     `δ`-sparse subdivision the cell holding `t` holds `t₁` as well, or else it
     holds `t₂`, the span being at most `δ` and the cell longer.

  Links 2 and 3 hold at a **fixed** `δ`, which is what makes the chain usable:
  the `δ` a consumer chooses for the path is the `δ` the hypothesis is read at for
  the image, and nothing is asked to be refined.

  **The chain is composed, 2026-09-19**, into the three statements the converse
  half actually reads — each bounding a quantity of the path that link 1 asks
  about, capped at `1` and up to `4 * ρ`, by the based modulus of **one** image
  path, which is the quantity the hypothesis controls:

  * `SkorokhodSpace.min_edist_le_two_mul_modulusBased_postcomp` — the three point
    quantity, links 2 and 3 composed, constant `2`;
  * `SkorokhodSpace.min_iSup_edist_le_three_mul_modulusBased_postcomp` and
    `SkorokhodSpace.min_iSup_edist_leftLim_le_three_mul_modulusBased_postcomp` —
    the two halves of the boundary term, the transport followed by
    `basePointOsc_le_three_mul_modulusBased`, constant `3`.

  What is left for the converse half is therefore **not** the chain but the
  bookkeeping: choose `ρ` from `η`, a finite `ρ`-net of the compact set compact
  containment supplies, one `h_j ∈ H` per net point, and let the exceptional sets
  of the `N` applications add up to `ε`. The order of the choices is `ε`, `m`,
  `η`, `ρ`, `K`, `N`, `δ`, and it does not commute.

  **Stage (B) is closed, 2026-09-19**, in both halves:
  `SkorokhodSpace.isTightMeasureSet_of_isTightMeasureSet_map_postcomp` is the
  converse and `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` the
  equivalence, the test class of the latter being all of `E →ᵇ ℝ`, where the
  clipped distances are their own approximants.

  The arithmetic, so that it is not rediscovered: with `c = min η 1 / 64` the
  three point quantity of the path is below `4 * c`, each half of the boundary
  term is at most `4 * c`, and link 1 turns that into
  `4 * (4 * c) + 2 * (8 * c) = 32 * c < 64 * c = min η 1`. The level is cut down
  to `min η 1` for one reason and it is not tidiness: links 2 and 3 carry a cap
  at `1`, and `4 * c ≤ 1` is what removes it. The window radii are `2 * m + 6`
  for the values and one more for the image moduli, the strict upper end of
  `SkorokhodSpace.min_edist_le_two_mul_modulusBased` needing the room.

  **The hypothesis on the test class is weaker than density and is what the
  proof reads**: for every compact `K`, every `x` and every `ρ > 0` some `h ∈ H`
  is within `ρ` of `SkorokhodSpace.clipDist x` **on `K`**. Density for uniform
  convergence on compact sets delivers it; nothing else is used.

  **And link 1 had to be weakened first.** It asked its three point hypothesis at
  every triple of `ℝ`, and the chain supplies it only on a window — the based
  modulus of an image path says nothing about times outside the window its
  subdivisions cover. The hypothesis is now read on `Set.Icc (-R) R` with
  `R ≥ 2 * max m 0 + 6 * δ`, which is what
  `SkorokhodSpace.exists_subdivision_of_separated` now bounds the nodes by
  (`SkorokhodSpace.node_le_add_two_mul`, `SkorokhodSpace.sub_two_mul_le_pnode`,
  and `a = ⌈u / δ⌉₊ + 1` in place of any natural number above `u / δ`), plus the
  `2 * δ` that the separation of the large jumps reads to the left of the later
  jump. The same window travels through
  `SkorokhodSpace.subdivisionOsc_le_of_forall_min_edist_lt`, which asks its nodes
  to lie in it, `SkorokhodSpace.two_mul_le_sub_of_forall_min_edist_lt` and
  `SkorokhodSpace.separated_setOf_lt_edist_leftLim`, whose separated set is now
  the large jumps **inside** the window.

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
* **The hypothesis bundle of stage (A) is inhabited.**
  `SkorokhodSpace.exists_countable_dense_continuity_real` is
  `exists_countable_dense_continuity` over `ι = ℝ` and `E = ℝ`, with every
  instance of the bundle discharged. It is the index of every other acceptance
  example of this milestone, so the statement above is about the index the
  milestone is for and not about an empty class.
* **The hypothesis of the convergence theorems is met at a law that jumps, and
  fails at the jump.** `SkorokhodSpace.dirac_step_setOf_leftLim_eq_of_ne` and
  `SkorokhodSpace.dirac_step_setOf_leftLim_eq_one`, **proved 2026-09-18**: for
  the Dirac law at `SkorokhodSpace.step`, the path with one jump at `1`, the set
  `{f | f⁻ t = f t}` has measure `1` at every `t ≠ 1` and measure `0` at `t = 1`.
  A continuous path would have met the hypothesis everywhere and left a reader
  unable to tell it from a tautology; this one locates the exceptional set
  exactly. `SkorokhodSpace.dirac_setOf_leftLim_eq_one_iff` is the reading behind
  it — for a law carried by one path the hypothesis is that *that* path does not
  jump — and `SkorokhodSpace.leftLim_step_of_ne` the computation. What is probed
  is the hypothesis and not the strength of the conclusion: over a Dirac law the
  conclusion is a convergence of constants.
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

### The functionals a martingale problem tests

The consumer of stage (A) is the third item of the chain of
**MartingaleProblems** Milestone 11: a weak limit of solutions of a martingale
problem is a solution. It reads its hypothesis through
`mpSolution_of_tendsto_of_pContinuous` there, in the shape
`P {ω | ContinuousAt ψ (X ω)} = 1` for the functional

```
ψ t x = f (x t) - ∫_0^t g (x u) du,
```

and this part of the milestone says at which paths `ψ t` is continuous. Proved
2026-09-21.

* `continuousAt_integral_comp` — **the compensator is continuous at every path,
  with no hypothesis on its jumps.** The times are read through a measurable
  `φ : α → ι` against a finite `μ`, and the one condition is that `μ` sees a
  countable set of times through `φ` as a null set. A path has countably many
  jumps (`countable_leftJumpSet`), so off a `μ`-null set of parameters the
  values converge, and dominated convergence with the constant majorant `‖g‖`
  closes it. `continuousAt_setIntegral_toNNReal` is the instance
  `α = ℝ`, `μ` Lebesgue on `Set.Ioc 0 T`, `φ = Real.toNNReal`, which is the shape
  in which a martingale problem over `lebesgueClock` writes its compensator.
* `mpTest` — the functional itself, `f (z t) - ∫_0^t g (z u) du` as a function
  of the path alone. It is written without a clock and without a filtration,
  because where it is continuous is a question about the path space and nothing
  else; **MartingaleProblems** Milestone 11 is where it acquires both.
* `integrableOn_mpTest_integrand` and `mpTest_sub` — the integrand of the
  compensator is integrable over the window, and the functional is **linear in
  the pair it tests**: `mpTest f g t z - mpTest f' g' t z = mpTest (f - f') (g - g') t z`.
  The integrability is what makes the second a statement about the *integrals*
  and not only about the integrands, the Bochner integral of a non integrable
  function being `0`; it is `IsCadlag.measurable` of Milestone 2 composed with
  `Real.toNNReal` and with `g`, together with the bound `‖g‖` on a window of
  finite Lebesgue measure. This is what **MartingaleProblems** Milestone 11
  reads when its approximants solve an *approximating* martingale problem:
  the error of testing with the wrong pair is the norm of the difference of the
  pairs, and **no boundedness of the approximating pair is spent.**
* `continuousAt_mpTest` — the whole functional, continuous at every path that
  does not jump **at the one time it evaluates**. The asymmetry between the two
  summands is the content: the compensator carries none of the condition, the
  evaluation all of it, and the evaluation cannot be freed of it —
  `exists_jump_continuousAt_eval`.
* `measure_setOf_forall_notMem_leftJumpSet_eq_one` — the passage from the
  *times* of stage (A) to the *paths*: a law with no fixed discontinuity along a
  countable set of times gives full mass to the paths jumping at none of them.
  **No Fubini argument occurs in it**, and none is needed —
  `exists_countable_dense_continuity` has already made the exceptional times
  countable, and countability is what a union of null sets asks for.
  `measure_setOf_forall_notMem_leftJumpSet_comp_eq_one` is the same read through
  a process rather than through its law, which is the form the consumer writes
  its hypotheses in; `Measurable X` is not removable there, a non-measurable set
  of full outer measure having a complement of full outer measure too.
* `continuousAt_of_mem_evalFuns` — a member of `evalFuns E T` is continuous at
  every path that jumps at no time of `T`. The condition is asked over the whole
  of `T` rather than over the `Finset` of the particular member, membership in
  `evalFuns` being an existential.
* `measure_setOf_continuousAt_mpTest_eq_one` and
  `measure_setOf_continuousAt_mpTest_mul_eq_one` — the two halves of the
  hypothesis, the second for the tested increment multiplied by a member of
  `evalFuns E T`. The consumer asks its continuity of the **product** and not of
  the factors, and that is what makes one application of the paths statement
  answer for all three at once.

### Milestone 8: the past of the path space, generated by finitely many coordinates

The section above says **where** the finite dimensional test functions are
continuous; this one says **what they generate**, and the two together are what
`MeasureTheory.isDetermining_evalFuns` of **MartingaleProblems** Milestone 10
consumes. A determining class has to generate the past *and* be continuous at
almost every path, and `evalFuns` is the only class in this file of which both
are known — indicators of cylinders generate the past as well and are continuous
nowhere, so the choice is forced.

* `evalFuns_mono` and `evalFuns_insert_Iic_subset` — the class grows with the set
  of times it reads, and the class of the past of `s` therefore sits inside the
  class along the whole of `T` as soon as `s ∈ T`. That is the bridge to the
  continuity statements above, which are proved for members of `evalFuns E T`;
  the hypothesis is free, a martingale problem testing at times drawn from `T`.
* `one_mem_evalFuns` — the constant `1` as the product over the empty `Finset` of
  times.
* `generateFromFuns_evalFuns_eq_iSup` — along **any** set of times the class
  generates exactly the σ-algebra of the coordinates at those times. No
  countability, no density, no `CompleteSpace E`: those belong to
  `borel_eq_iSup_comap_eval_of_countable_rightDense` and enter only when the right
  hand side is to be the whole Borel structure. Separating the two is what makes a
  statement about a **proper** subset of times available at all, and it is the
  half of `generateFromFuns_evalFuns` that carries the work.
* `comap_eval_le_iSup_of_neBot` — a coordinate approached from the right by `S`
  is measurable for the coordinates in `S`. This is right continuity of the paths
  read as a measurability statement: the metric on `ι` supplies a sequence of
  times of `S` falling to `r`, the values converge along it, and
  `measurable_of_tendsto_metrizable` closes it.
* `iSup_comap_eval_insert_Iic_eq` and `generateFromFuns_evalFuns_Iic` — the past
  at `s` is generated by the coordinates at the earlier times of a right dense
  set **together with the coordinate at `s` itself**, and therefore by the test
  functions along `insert s (T ∩ Set.Iic s)`.

**Why `s` is put into the class by hand.** Right density supplies times of `T`
*above* a given time, which recovers the coordinate at every `r < s`: the path is
right continuous, and such a sequence may be kept below `s` as soon as `r < s`. At
`r = s` there is nothing above to approach from inside `Set.Iic s`, and a path
that jumps at `s` is read by no earlier coordinate; the proof recovers `f s` from
no earlier time. That is not an artefact — it is the same asymmetry that makes
evaluation the one functional of a martingale problem carrying a no-jump
condition (`exists_jump_continuousAt_eval`). Adding the single time costs nothing:
the class stays countably indexed when `T` is countable, and it asks nothing of
`s`, where carrying `s ∈ T` as a hypothesis would have to be discharged at every
time a consumer tests.

## Milestone 9: the nonnegative index inside the real one

Milestones 7 and 8 are stated over the index `ℝ`. The reason is
`isCompact_closure_iff`, whose converse half is false over an index with gaps
(`not_isCompact_closure_of_rigid`), and every statement of the oscillation
chain reads it. The processes of the roadmap **MartingaleProblems** live over
`ℝ≥0`. This milestone is the passage between the two indices, and it is made
**once**, as a map of path spaces.

**The map.** `SkorokhodSpace.extendNNReal : D(ℝ≥0, E) → D(ℝ, E)` sends `f` to
`f ∘ Real.toNNReal`, that is, extends the path by the constant value `f 0` on
the negative half line. It is càdlàg by `IsCadlag.comp_monotone_continuous`,
`Real.toNNReal` being monotone and continuous, and it is the mirror of
`IsCadlag.comp_coe_nnreal` of Milestone 2, which goes the other way.

**The theorems.**

* `SkorokhodSpace.isometry_extendNNReal` — the map is an isometry.
* `SkorokhodSpace.isClosedEmbedding_extendNNReal` — and its image is closed.
  Completeness of `D(ℝ≥0, E)` is `SkorokhodSpace.instCompleteSpace` of
  Milestone 5, and it is what turns the isometry into a closed embedding.
* `SkorokhodSpace.intDist_extendNNReal` — the metric statement behind it, at
  the level of `intDist` and therefore usable without the instance.
* `SkorokhodSpace.distWith_extendNNReal` — the windowed supremum for one time
  change, which is where the two indices actually meet.
* `TimeChange.ofNNReal` — a time change of `ℝ≥0` extended to `ℝ` by the
  identity on the negative half line, with `TimeChange.norm_ofNNReal_le`,
  `TimeChange.inv_ofNNReal` and `TimeChange.toNNReal_ofNNReal`.
* `TimeChange.orderIso_zero_nnreal` — every time change of `ℝ≥0` fixes `0`, so
  `TimeChange.fixing 0` is the whole group there. `TimeChange.ofNNReal` needs no
  hypothesis, while `TimeChange.toNNReal` of Milestone 5 needs `h0`.
* `exhaustion_nnreal`, `exhaustionMin_nnreal`, `exhaustionMax_nnreal`,
  `toNNReal_clamp` — the window of `ℝ≥0` written out, and the one identity that
  carries the clamp across.

**Why the isometry is content and not bookkeeping.** The two groups of time
changes are not symmetric. One of `ℝ` fixing `0` restricts to `ℝ≥0` and can only
lose norm; one of `ℝ≥0` extends to `ℝ` and picks up a Lipschitz constant `1`
from the pairs `a < 0 ≤ b`, where the left point does not move while the right
one does. That gain is free, and `TimeChange.one_le_max_lipConst` is the reason:
the larger of the two constants of a time change is at least `1` anyway, so the
`1` disappears in the maximum the norm takes. The extra freedom a time change of
`ℝ` has on the negative half line buys nothing, because both extended paths are
constant there.

**What the embedding transports.** Three things travel along it: the image of a
compact set is compact, so tightness of a set of laws on `D(ℝ≥0, E)` gives
tightness of the image laws; the image is closed, so a bounded continuous
function on `D(ℝ≥0, E)` extends and weak convergence of the image laws pulls
back; and a coordinate at a nonnegative time is a coordinate of the extended
path.

**And the one that does not.** Convergence of the finite dimensional
distributions along a dense `T ⊆ ℝ≥0` is *not* convergence along a dense subset
of `ℝ`, because `T` is not dense in `ℝ`. It is a hypothesis and not a
conclusion, so the embedding does not carry it. The times to be added are the
negative ones, where the extended path takes the value `f 0`, so what has to be
known there is convergence at the single time `0`. The statement of the
`ℝ≥0`-form of Milestone 8 therefore reads `Dense T` together with
`(0 : ℝ≥0) ∈ T`, and under those two the negative times are handled by replacing
each of them by `0`, which is a time of `T`.

**The `ℝ≥0`-form of Milestone 8, built on the embedding.**

* `SkorokhodSpace.isTightMeasureSet_map_extendNNReal` — tightness carries
  forward along the embedding, because a continuous image of a compact set is
  compact. **The mathematics of this one is Mathlib's**:
  `MeasureTheory.IsTightMeasureSet.map`
  (`Mathlib/MeasureTheory/Measure/Tight.lean:129`) is the statement for an
  arbitrary continuous map, and what is added here is the index — a consumer
  holds a hypothesis about a *family* `μ : γ → Measure D(ℝ≥0, E)` and not about
  `Measure.map e '' S`, and the two sets have to be identified. The
  measurability of the embedding is its continuity; completeness of `E` is not
  spent here.
* `SkorokhodSpace.tendsto_of_tendsto_map_extendNNReal` — weak convergence pulls
  back along the embedding: a bounded continuous function on `D(ℝ≥0, E)` extends
  to one on `D(ℝ, E)`, by
  `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`
  (`Mathlib/Topology/TietzeExtension.lean:273`), whose conclusion carries the
  equality `g ∘ e = f` that the comparison of integrals needs and not merely an
  estimate of norms. Its hypothesis `[NormalSpace Y]` is an instance and not a
  step, `D(ℝ, E)` being metric. The topology of `ProbabilityMeasure` is read
  through `→ᵇ ℝ` by
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, the
  push forward through `MeasureTheory.ProbabilityMeasure.toMeasure_map`, which
  is `rfl`, and `integral_map` moves the integral to the smaller space.
* `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional_nnreal` —
  a tight sequence of laws on `D(ℝ≥0, E)` whose finite dimensional
  distributions converge along a dense `T ∋ 0` converges weakly. It rests on
  `isClosedEmbedding_extendNNReal`, on the `ℝ`-form of the theorem, and on the
  two transports above. The set of real times it feeds the `ℝ`-form is
  `Real.toNNReal ⁻¹' T`, whose density is where `(0 : ℝ≥0) ∈ T` is spent: a
  nonpositive real lies in it because `Real.toNNReal` sends it to `0`, and a
  positive one is approximated by a point of `T` read back through the
  coercion, `Real.toNNReal` being a retraction there.
* `SkorokhodSpace.tendstoInDistribution_of_isTight_of_tendsto_finiteDimensional_nnreal`
  — the same for path valued random variables, `Measure.map` carrying the one
  form to the other.
* `SkorokhodSpace.tendstoInDistribution_eval_of_isTight_of_tendsto_finiteDimensional_nnreal`
  — and the marginal read off it at a nonnegative time the limit law does not
  charge with a jump. This is the form the roadmap **MartingaleProblems** asks
  for in its Milestone 10. **`SkorokhodSpace.tendstoInDistribution_eval` itself
  needed no crossing**: it is stated over an arbitrary index and applies over
  `ℝ≥0` as it stands. What had to be crossed is the index of the *criterion*,
  which is `isCompact_closure_iff` of Milestone 7 and everything above it.

**Tightness crosses in both directions, and that is what fixes the index of a
criterion.**

* `SkorokhodSpace.isTightMeasureSet_of_isTightMeasureSet_map_extendNNReal` —
  tightness travels **backward** along the embedding. The image being closed, a
  compact `K ⊆ D(ℝ, E)` has a compact preimage
  (`Topology.IsClosedEmbedding.isCompact_preimage`,
  `Mathlib/Topology/Compactness/Compact.lean:1017`), and the mass outside the
  preimage is the mass the image law puts outside `K`, by
  `MeasureTheory.Measure.map_apply` at `Kᶜ`. The same `ε` serves.
* `SkorokhodSpace.isTightMeasureSet_map_extendNNReal_iff` — the two transports
  read as one equivalence.

**The rule this settles, and it applies to every statement of Milestones 7 and 8
that a consumer over `ℝ≥0` would otherwise ask to have duplicated.** A
*hypothesis* crosses only forward; a *conclusion* crosses backward. The
`ℝ≥0`-form of Milestone 8 had to be written out because it carries the
convergence of the finite dimensional distributions across as a hypothesis, and
that one does not travel at all — a dense `T ⊆ ℝ≥0` is not dense in `ℝ`. A
tightness *criterion* carries a conclusion: it is therefore stated once, over
`ℝ`, where `isCompact_closure_iff` is available, and a consumer whose processes
run over `ℝ≥0` crosses its family, applies the criterion, and comes back. Nothing
of it is to be restated over `ℝ≥0`.

**Compact containment crosses too, and it is the one hypothesis of Milestone 8
that a consumer over `ℝ≥0` holds in a different shape**, 2026-09-19.

`SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` carries compact
containment as a hypothesis, and by the rule above a hypothesis crosses only
forward. The crossing is made here, once.

* `SkorokhodSpace.IsCompactContained` — the predicate itself, on a **family**
  `μ : γ → Measure D(ι, E)`: for every level and every window one compact set of
  the value space that every member of the family charges outside of by at most
  that level. The uniformity in the index is its whole content, and that is why
  it is a predicate on a family and not on a measure; the level is `ℝ≥0∞` and the
  measure is that of the complement, so that neither a subtraction nor an
  `ENNReal.toReal` appears.
* `SkorokhodSpace.preimage_extendNNReal_setOf_forall_mem_exhaustion` — **the two
  windows are the same condition**, not merely comparable ones. Over `ℝ` the
  window is two sided and reaches times the processes do not have; under the
  embedding every one of those times reads the value at `0`, which lies in every
  window. So the crossing of the window is an equality of sets.
* `SkorokhodSpace.measurableSet_setOf_forall_mem_exhaustion` — **and the
  crossing needs the window set to be measurable**, which is where it differs
  from everything else in this milestone. A bound travels from a measure to its
  image along `MeasureTheory.Measure.le_map_apply` for an arbitrary set — that is
  what let the modulus conditions of Milestone 8 be stated over sets no one can
  measure — but *back* along `MeasureTheory.Measure.map_apply` only for a
  measurable one, and compact containment crosses back. The window set is an
  uncountable intersection of coordinate conditions, and that it is measurable is
  the statement that a càdlàg path on a window is determined there by the
  rationals of the window **together with its right endpoint**; the endpoint is
  not a formality, nothing approaching it from the right lying inside the window.
  The deterministic half is
  `SkorokhodSpace.forall_mem_Icc_of_forall_mem_dense`, which reads only right
  continuity and asks `K` to be closed and not compact.
* `SkorokhodSpace.isCompactContained_map_extendNNReal_iff` — the crossing, in
  both directions, with the **same** compact set of `E` on either side: the
  crossing changes the path space and not the value space.

**And the hypothesis is necessary**, so the criterion is not weakened by carrying
it: `SkorokhodSpace.isCompactContained_of_isTightMeasureSet` derives compact
containment from tightness, being the first conjunct of
`SkorokhodSpace.isTightMeasureSet_iff` crossed back. What compact containment
excludes is only families for which the criterion would be false — the constant
paths at height `n`, whose images under every bounded continuous map are tight
and which are not tight.

**At data it is free for a constant family**, and that is where the condition
lives. `SkorokhodSpace.isCompactContained_const`: a finite measure on a Polish
space is tight (`MeasureTheory.isTightMeasureSet_singleton`,
`Mathlib/MeasureTheory/Measure/Tight.lean:99`) and `D(ℝ≥0, E)` is Polish by
`SkorokhodSpace.instPolishSpace`, so one law repeated has compact containment for
nothing. A genuine family need not, and that is the emptiness test for the
predicate: it is inhabited, and it is not vacuous.

* `SkorokhodSpace.isCompactContained_of_forall_exists_bound` — **how a family
  that moves meets the condition**, and the reduction a consumer uses. **Proved
  2026-09-21.** For `E` a `ProperSpace` and any base point `x₀`, compact
  containment follows from a uniform bound on the **path maximum over a
  window**: to every `ε > 0` and every `m` there is `R : ℝ` with
  `μ i {γ | ∀ t ∈ exhaustion t₀ m, dist (γ.toFun t) x₀ ≤ R}ᶜ ≤ ε` for every `i`.

  **`ProperSpace` is exactly the gap and not a convenience.** The predicate asks
  for a **compact** `K ⊆ E` holding the path on the window; an estimate on the
  path maximum produces a **bounded** set. Closed balls being compact is the
  whole difference, and without it the implication fails for the reason it fails
  in an infinite dimensional Hilbert space, where the closed unit ball is
  bounded and not compact. It is also not an extra demand on this section:
  `ProperSpace E` implies `CompleteSpace E`
  (`Mathlib/Topology/MetricSpace/ProperSpace.lean:104`) and
  `SecondCountableTopology E` (`:66`), hence the Polishness assumed throughout,
  so the ambient hypothesis is subsumed rather than added to. `E = ℝ` is an
  instance of the statement and not the statement: the reduction has nothing to
  do with the line.

  **Why it was written.** Every statement of **MartingaleProblems**
  Milestone 11 carries compact containment as a hypothesis, and until this one
  the only witness was the constant family above — the criterion was inhabited
  and had never been met by a family that moves. The consumer it is written for
  is Donsker, where the bound is Doob's maximal inequality over the **discrete**
  index, Mathlib's `MeasureTheory.maximal_ineq`
  (`Mathlib/Probability/Martingale/OptionalStopping.lean:144`) for a
  `Submartingale` with `0 ≤ f`, and where the passage from the discrete maximum
  to the window maximum is an equality and not an estimate: a step path on a
  window takes exactly the values of its nodes. That instance is the next item
  and is not this one.

**The `ℝ≥0`-form of the criterion, and what it does and does not do to the rule
above.** `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal` states
stage (B) with **both** sides of the equivalence over `ℝ≥0`, which is the form
**MartingaleProblems** Milestone 11 consumes. It **restates nothing**: its proof
reads `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` once and crosses
three times — the hypothesis forward, the left side of the equivalence back over
`E`, and the right side back over `ℝ`, the two crossings on the right being
exchanged by `SkorokhodSpace.postcomp_extendNNReal`, which is `rfl`. So the rule
stands as stated for the mathematics; what it did not say, and now does, is that
a criterion carrying a hypothesis needs a wrapper that crosses it, and that the
wrapper is bookkeeping rather than a second proof.

**The test class may be thinned to a dense one**, 2026-09-21, and that is what
separates a criterion from a demand. Both forms above read their right hand side
at *every* `h : E →ᵇ ℝ`, while the sources of that hypothesis — a generator, an
algebra of test functions — supply it on a class that is merely dense, and
Ethier–Kurtz state their criterion with a dense class for that reason. Five
statements, in two groups: the supremum norm first, because it is the cheaper
argument, and then the density a generator actually has.

* `SkorokhodSpace.dist_postcomp_le` — two post-compositions of **one** path are
  at most as far apart as the two maps are, uniformly on the value space. It is
  the estimate `SkorokhodSpace.distWith_postcomp_le` is not: there the two
  arguments are two *paths* under one map, here they are two *maps* on one path,
  and the difference is that the time change may be taken to be the identity.
  That is the whole proof — the infimum defining `SkorokhodSpace.intDist` is
  bounded above by its value at `1`, whose logarithmic norm is `0`, the windowed
  supremum at `1` is a supremum of `dist (h y) (h' y)` over values of the path,
  and the integral over the radius costs nothing because `∫₀^∞ exp (−u) du = 1`.
  The bound is carried by a real `C` and not by a norm, so that it applies to
  `C(E, E')` for a metric `E'` with no algebraic structure; nonnegativity of `C`
  is not a hypothesis, the path exhibiting a value at which `C` dominates a
  distance.
* `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_dense` and
  `SkorokhodSpace.isTightMeasureSet_of_dense_forall_postcomp_nnreal` — tightness
  of the real images under a **dense** class gives it under every bounded
  continuous function, and hence, under compact containment, tightness of the
  family itself. The first reads no hypothesis of `μ` at all, not even
  finiteness. Both rest on
  `MeasureTheory.isTightMeasureSet_map_of_forall_exists_dist_le` of
  **WeakConvergence**, which turns a uniform approximation of a *map* into
  tightness of its image laws; completeness of `D(ℝ≥0, ℝ)` is what that
  statement spends, and it is `SkorokhodSpace.instCompleteSpace`.

**The density a generator has is weaker than that**, and the second group is what
covers it: a domain such as the compactly supported smooth functions is dense for
uniform convergence **on compact sets** only, a uniform limit of them vanishing
at infinity while the constant function does not. Three statements:

* `SkorokhodSpace.dist_postcomp_le_of_forall_mem_exhaustion` — the estimate above
  read on a window alone: if the two maps agree within `η` at the values the path
  takes on the window `M`, the two post-compositions are within `η + exp (−M)`.
  The integral over the window radius is split at `M`; below it the windowed
  supremum is at most `η` because a smaller window sits inside a larger one, and
  above it the truncation at `1` leaves `∫_M^∞ exp (−u) du = exp (−M)`. It is the
  bridge between a hypothesis quantified over all of `E`, which a generator
  domain cannot meet, and one quantified over the values of a path in a window,
  which compact containment holds in a compact set.
* `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_denseOnCompacts` and
  `SkorokhodSpace.isTightMeasureSet_of_denseOnCompacts_forall_postcomp_nnreal` —
  the same two conclusions from density on compact sets. Given `δ` and `ε`:
  choose the window `m` with `exp (−m) < δ/2`, let `Γ` be the compact set that
  holds the path on that window up to mass `ε`, and let `g` be within `δ/2` of
  `f` on `Γ`. The exceptional set of
  `MeasureTheory.isTightMeasureSet_map_of_forall_exists_measure_dist_gt_le` is
  then contained in the complement of that event, for **every** index at once,
  and that uniformity is exactly what compact containment says. So compact
  containment is read twice in the second of them — once as the hypothesis of the
  equivalence, once inside the approximation — and it is the same hypothesis both
  times.

  The density is a hypothesis and not an algebra: Stone–Weierstrass is what
  produces it for a point separating subalgebra and is not used here, which keeps
  these statements free of any algebraic structure on the test class.

**The window over `ℝ≥0`, and the half open form of the dense window lemma**,
2026-09-19, added for the consumer in **MartingaleProblems** Milestone 11 and
stated here because both are about the path space. Three statements, none of
which restates anything:

* `mem_exhaustion_zero_nnreal_iff` — at the base point `0` the window over `ℝ≥0`
  is `Set.Iic`, the ball having no negative half to reach. It is the shape in
  which a process over `ℝ≥0` meets its window.
* `SkorokhodSpace.measurableSet_setOf_forall_mem_exhaustion_nnreal` — the window
  set over `ℝ≥0` is measurable, which is the `ℝ`-statement carried along
  `SkorokhodSpace.preimage_extendNNReal_setOf_forall_mem_exhaustion`; that
  identity being an equality of sets, nothing is proved twice. It is what lets a
  bound travel **back** from an image law to the law of the variable, which
  `MeasureTheory.Measure.map_apply` asks measurability for and
  `MeasureTheory.Measure.le_map_apply` does not supply.
* `SkorokhodSpace.forall_mem_Ico_of_forall_mem_dense` — the dense window lemma in
  its **half open** form, which is the primitive one: on `Set.Ico a b` every
  point has points of the window strictly to its right, so no endpoint is read
  separately and the hypothesis `hb` of the closed form disappears. The closed
  form `SkorokhodSpace.forall_mem_Icc_of_forall_mem_dense` is now three lines on
  top of it, and both are stated over an arbitrary **densely ordered** index
  rather than `ℝ`, because the two consumers are over `ℝ` (the measurability
  above) and over `ℝ≥0`, and nothing in the proof knows which.

  **Neither side carries a metric, since 2026-09-20.** The index asks for a
  topology with the order topology and the values for a topology, and that is
  all the proof reads: `closure_Ioo`, `Dense.open_subset_closure_inter`,
  `IsRightContinuous` and `IsClosed.mem_of_tendsto`. The two statements are
  therefore written over variables of their own and not over this file's `ι`
  and `E`, whose metrics they inherited only from the section they stood in.
  The third consumer is what forced it: the window supremum of
  **MartingaleProblems** Milestone 9 applies them to `ℝ≥0∞`-valued paths, and
  `ℝ≥0∞` is no metric space, so under the old statement the lemma was
  unavailable to it and the argument would have been written twice.

A consumer who cannot pay `hb` — and the one in Milestone 11 cannot, the value at
the right endpoint of a window being exactly what a dense set does not reach —
enlarges the window instead and reads the half open form. That is free wherever
the hypothesis is quantified over all horizons.

* `SkorokhodSpace.mem_of_continuousWithinAt_of_forall_mem_dense` — the
  **pointwise** form, and it is the primitive one: to place *one* value `f t` in
  the closed set, what is read of `f` is `ContinuousWithinAt f (Set.Ioi t) t`,
  at that point and nowhere else, and of `t` that it lies in the half open
  window. The two quantified forms above are one line and three lines on top of
  it and their statements are unchanged.

  **The pointwise form is not a refinement for its own sake**, and the consumer
  that forced it names the difference. `MeasureTheory.biSup_enorm_Iic_le_biSup_enorm_inter_dense`
  in **MartingaleProblems** Milestone 11 reads a supremum over `Set.Iic T` and
  must therefore take the windows `Set.Ico t T'` with `T < T'`; its function is
  the error `Y - V` of an approximating pair, whose right continuity stops at
  the horizon because the compensator is an indefinite integral and past the
  horizon a Bochner junk value. The windows reach past the set on which the
  consumer has anything to say, so the quantified form is unusable there and
  the pointwise form is exactly right. Under the quantified form alone the
  hypothesis would have had to be strengthened to right continuity on the line
  — which no approximating pair supplies.

**Where compact containment is free, and what is left when it is**, 2026-09-20,
added for **MartingaleProblems** Milestone 11 and stated here because it is about
the path space.

`SkorokhodSpace.isTightMeasureSet_iff` has two conjuncts, and for the *image* of
a family under a bounded post-composition the first one costs nothing: a bounded
continuous `h : E →ᵇ ℝ` sends every value into the compact interval
`Set.Icc (-‖h‖) ‖h‖`, so the window set of an image law carries the whole mass.

* `SkorokhodSpace.modulusBased_le_subdivisionOsc` — and before any of it, the
  statement that says in which shape the *second* conjunct is ever produced:
  `modulusBased` is an infimum over based subdivisions, so naming **one** of them
  bounds it. It is `iInf_le` and three characters of proof, and it stood
  nowhere, although every upper bound on the modulus has that shape. The witness
  at the end of this block says why the converse reading is false: a subdivision
  fixed **before** the path is of no use.

* `SkorokhodSpace.isCompactContained_map_postcomp_of_measurableSet` — the
  statement, over an arbitrary index and with **no hypothesis at all on the
  family**: not finiteness, not tightness, and in particular not compact
  containment of the family itself, which is a genuine condition. Its one
  hypothesis is that the window set of `D(ι, ℝ)` be measurable, and that is the
  only index-specific input, because the bound travels to the image law along
  `MeasureTheory.Measure.map_apply` — `MeasureTheory.Measure.le_map_apply` bounds
  an image measure from below and is of no use here. The two indices are served
  by `SkorokhodSpace.isCompactContained_map_postcomp_nnreal` and
  `SkorokhodSpace.isCompactContained_map_postcomp_real`, one line each, and not
  by a proof each.
* `SkorokhodSpace.isTightMeasureSet_iff_modulusBased_nnreal` — with compact
  containment in hand tightness **is** the modulus condition, over the index the
  processes have. It restates nothing: it is `isTightMeasureSet_iff` with the
  first conjunct discharged and the family crossed by
  `SkorokhodSpace.isTightMeasureSet_map_extendNNReal_iff`. The modulus stays a
  quantity of the *extended* path, `isCompact_closure_iff` being false over an
  index with gaps.
* `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff` — the two composed, and
  hence an equivalence **with no hypothesis whatever**: the laws of the bounded
  real images are tight if and only if their moduli are small in probability,
  uniformly. This is the shape Milestone 11 of **MartingaleProblems** reads, and
  it fixes what its first item has to produce from a martingale approximation.

**And the remaining half is not nothing**, which is what the witness says.
`SkorokhodSpace.twoJumpImageLaw` is the family of Dirac laws at the two jumps of
Milestone 8 at distance `(n+1)⁻¹`, read through the clipped distance to the value
between them — the test function that sees both jumps at once, and the one on
which the coordinatewise route was refuted. It has compact containment by the
theorem above, in one line
(`SkorokhodSpace.isCompactContained_twoJumpImageLaw`), and it is **not tight**
(`SkorokhodSpace.not_isTightMeasureSet_twoJumpImageLaw`). So the equivalence is
not a triviality: the quantity that fails here is exactly the one a run at
Milestone 11 has to produce.

**A finding from that proof, corrected on 2026-09-20 after the author asked
whether the class is not simply true.** It is, and the correction is worth
keeping because the first reading blamed the wrong thing.
`MeasureTheory.Measure.map_dirac` asks `MeasurableSingletonClass` of **both**
spaces; elaborating it on `D(ℝ, ℝ × ℝ)` reaches the heartbeat limit, with the
error pointing at the theorem header rather than at the instance, and the first
report concluded that the instance search does not terminate on a path space.

That conclusion was wrong. `D(ι, E)` is a metric space, hence `T1`, and carries
the Borel structure of that metric, so `MeasurableSingletonClass` holds by
`isClosed_singleton.measurableSet` — and Mathlib's
`OpensMeasurableSpace.toMeasurableSingletonClass` finds it, in seconds and under
the default heartbeat limit, when it is asked directly. What reaches the limit
is the search *inside* that application, where it runs with metavariables. The
instance is therefore stated in `Suggested.lean` next to the `BorelSpace` one,
which makes `map_dirac` usable; `MeasureTheory.Measure.map_dirac'`
(`Mathlib/MeasureTheory/Measure/Dirac/Basic.lean:36`), which asks measurability
of the map instead, remains available and is the cheaper one where the map is
at hand anyway.
`MeasureTheory.Measure.le_dirac_apply`
(`Mathlib/MeasureTheory/Measure/Dirac/Def.lean:34`) is the other half,
and it is what lets the measure of a modulus set be bounded below **without** the
set being measurable — the modulus sets are among those this roadmap never
asserts measurable.

**Acceptance example.** `SkorokhodSpace.extendNNReal (jumpPathD …)` of the
roadmap **MartingaleProblems**, Milestone 6: the path law of the jump
construction, which lives on `D(ℝ≥0, E)`, read on `D(ℝ, E)`. It is the family
for which the index crossing was built, and the statement to be checked on it is
that its coordinate at a nonnegative time is unchanged by the crossing, which is
`extendNNReal_apply` together with `Real.toNNReal_coe`. It is proved
(2026-09-19) in **MartingaleProblems** as `extendNNReal_jumpPathD_toFun`, and
with it the whole chain: `map_eval_map_extendNNReal_map_jumpPathD` for the
coordinate of the crossed law, `map_eval_map_extendNNReal_map_jumpPathD_poisson`
for the independent control against `ProbabilityTheory.poissonMeasure`, and
`isTightMeasureSet_map_extendNNReal_map_jumpPathD` for the tightness transport,
whose hypothesis is there discharged on data.

## Milestone 10: Aldous' tightness criterion, and what it does not see

*Added 2026-09-19 at the author's request, out of a conversation rather than a
run, as the criterion practitioners reach for and as a record of what our
generality costs and what it does not.*

*And since 2026-09-20 it is not an aside: the tenth run of that day measured that
the whole remaining content of `isTight_map_postcomp_of_exists_martingale` in
**MartingaleProblems** Milestone 11 is the modulus condition. The route to
tightness itself is unchanged — Milestone 7 plus Milestone 8 — and what this
milestone supplies is the passage from an increment bound at stopping times,
which a Doob estimate gives, to the modulus.*

*Which statement of it that chain reads was **decided against the first answer**
on 2026-09-20, twenty-third run, and the correction is kept because it points at
a real trap. `SkorokhodSpace.modulusBased_le_of_forall_stoppingTime` below is
Aldous' criterion with the union bound avoided, by reading the hypothesis at a
**random** index; the run before had proposed it as the one theorem still
missing, on the ground that the composition in **MartingaleProblems** diverges.
The composition does diverge — but only under the condition `u ≤ N • δ` of
`MeasureTheory.measure_setOf_lt_modulusBased_le_gap`, which ties `N` to `δ`. One
stage above, the count is free, the horizon summand does not mention `δ`, and
the quantifiers stand in the classical order: `N` first, `δ` afterwards. What
that chain reads is therefore a **horizon** bound, built in
**MartingaleProblems** on the same day, and not this statement. Aldous at a
random time remains the sharper route and remains stated here; it is not the
route that chain needs.*

*And a warning for whoever builds it: `τ κ` for `κ` the first index with a gap
is **not a stopping time** — whether stage `k` has a gap is decided at
`τ (k+1)`, after `τ k`. That is why the classical proof detours through the
triangle inequality with a **fixed** increment, and it is the first thing to
settle.*

**The criterion.** For càdlàg processes `X n` adapted to filtrations `𝓕 n`, with
compact containment, and with

```
∀ ε T > 0,  lim_{δ→0} limsup_n  sup over stopping times τ ≤ T and θ ≤ δ
              P ( d (X n (τ + θ)) (X n τ) > ε )  =  0
```

the laws of `X n` are tight in `D ι E`.

**Proof, in outline, so that a run does not rediscover it.** Fix `ε`. Put
`τ 0 = ⊥` and `τ (k+1) = inf {t > τ k | d (X t) (X (τ k)) > ε}`. These are
stopping times, and they *are* the subdivision: between consecutive ones the path
moves by at most `ε`, so `modulusBased ≤ 2ε` as soon as no two of them lie within
`δ` and finitely many lie below `T` — the second following from the first, with
at most `T/δ` of them.

That they do not crowd is the whole of it, and it is the step Aldous solves by a
**second application of the hypothesis at a random time**: with
`σ = min (τ (k+1)) (τ k + δ)`, itself a bounded stopping time, the triangle
inequality

```
d (X σ) (X (τ k))  ≤  d (X σ) (X (τ k + δ))  +  d (X (τ k + δ)) (X (τ k))
```

reduces a displacement *inside* the window to two comparisons with a **fixed**
increment, one from `τ k` and one from `σ`, and the hypothesis bounds both —
which it can only do because it quantifies over *all* stopping times. That
quantifier is not decoration: at fixed times the condition follows from
convergence of the finite dimensional distributions and gives no tightness at
all, a jump at a random location having probability zero at every fixed time.
The interleaving of `lim_δ` and `limsup_n` in that step is the one place to check
against a source (Billingsley, 2nd ed., Theorem 16.10, or Jacod--Shiryaev
VI.4.5) before writing a signature.

**Index hypotheses, and they are not this roadmap's.** Milestone 1 asks `ι` for a
metric additive along the order (`AdditiveDist`), `ProperSpace` and
`OrderTopology` — a condition on the *geometry* of `ι`, which the modulus needs.
Aldous needs neither: no metric on `ι` occurs in the statement, the metric being
on `E`. What it needs instead is an **addition** `τ + θ` — that is \eqref{T4} of
the manuscript — and a **filtration with stopping times** over `ι`. So the two
criteria are incomparable, and this milestone is the only one here that mentions
a probability measure in its hypothesis rather than in its conclusion. It may
therefore belong in **MartingaleProblems**, where the stopping time machinery of
its Milestone 9 already stands.

**What the criterion does not see, and why that is Aldous' limit and not ours.**
It is sufficient, not necessary, and it fails exactly at **fixed times of
discontinuity**. The witness is one line: `X ≡ Set.indicator (Set.Ici 1) 1`,
deterministic and the same for every `n`, is trivially tight, while with
`τ = 1 - δ` and `θ = δ` the displacement `d (X 1) (X (1-δ)) = 1` for every `δ`.

Such processes are exactly what a clock with atoms produces, and this roadmap
admits them. The resolution is *not* to patch Aldous but to note that he is a
sufficient condition for something we already have: `modulusBased` is an
**infimum over subdivisions**, so the nodes may be laid where the jumps are, and
on the witness above the subdivision `{…, 1, …}` gives `modulusBased = 0`. The
implication chain is

```
Aldous ⟹ modulusBased → 0 in probability ⟹ tightness
```

and the second half is Milestone 7 together with Milestone 8. Only the first half
breaks at fixed discontinuities, and only the first half is dispensable. This is
the same role Billingsley's modified modulus `w''` plays, which takes the
*minimum* of the two one-sided oscillations and is therefore blind to one jump
per window; our infimum over subdivisions achieves it directly.

**The statement of this milestone that carries its probabilistic half, named**,
2026-09-20:

* `SkorokhodSpace.modulusBased_le_of_forall_stoppingTime` — the implication
  `Aldous ⟹ modulusBased small in probability`, which is the first half of the
  chain above and the only half that is not already proved elsewhere. For a
  process adapted to `𝓕`, if every stopping time `τ ≤ T` and every `θ ≤ δ`
  satisfy `P (d (X (τ+θ)) (X τ) > ε) ≤ γ`, then
  `P (modulusBased 0 m (X ·) δ' ≥ 2 ε) ≤ c (T, δ, ε) · γ` for a `δ'` depending on
  `δ`, `T` and `ε` alone. Its proof is the outline above; its step from a named
  subdivision to the modulus is `SkorokhodSpace.modulusBased_le_subdivisionOsc`
  of Milestone 9, and its stopping time machinery is Milestone 9 of
  **MartingaleProblems**. Its doc comment must say that the implication is one
  way only — the deterministic step below refutes the converse — and it must say
  that `isTight_map_postcomp_of_exists_martingale` of **MartingaleProblems**
  Milestone 11 does **not** read it: that item reaches the modulus by paying the
  union bound and settling the horizon separately, measured 2026-09-20. This
  statement is the sharper route and is not the one that item needs.

**Its deterministic half, built 2026-09-20 and free of probability.** The
statement above splits along the line every proof about this modulus does: a
deterministic half, which turns a family of times into a bound on
`SkorokhodSpace.modulusBased`, and a probabilistic half, which says that those
times do not crowd. The first is these five, stated so that the second plugs into
them without seeing the path space — the times arrive as a sequence `τ : ℕ → ι`
with a count `N`, which is the shape hitting times have.

* `SkorokhodSpace.subdivisionOsc_le_of_forall_cell` — a cellwise bound bounds the
  oscillation of a subdivision. It is the `iSup` unfolded in the direction
  opposite to `SkorokhodSpace.dist_le_of_subdivisionOsc_le`.
* `SkorokhodSpace.modulusBased_le_of_forall_cell` — the interface: name a based
  subdivision, bound its cells, and the modulus is bounded. It is the previous
  one composed with `SkorokhodSpace.modulusBased_le_subdivisionOsc`.
* `SkorokhodSpace.modulusBased_le_of_forall_gapped` — the deterministic half
  proper. An increasing, `δ`-sparse sequence `τ` of times up to a stage `N`, which
  starts at or before the window, ends at or after it, passes through the base
  point, and carries oscillation at most `c` on each cell, bounds the modulus by
  `c`. With `τ (k+1) = inf {t > τ k | dist (X t) (X (τ k)) > ε}` the cell bound
  holds with `c = ENNReal.ofReal ε` by the definition of the infimum, and the two
  remaining hypotheses are exactly the probabilistic content of the criterion.
* `mul_le_dist_of_gapped` and `card_le_of_gapped` — a `δ`-sparse chain of `N`
  steps spans at least `N * δ`, so at most `L / δ` of them fit into a span `L`.
  The index metric is additive along the order, so this is the sum of the gaps.
  Aldous needs it twice: it makes the count `N` above finite, and it turns a bound
  on the probability that **one** gap is short into a bound on the probability
  that **some** gap is short.

**Two things the outline above does not say, and both are about the base point.**

The first is that `SkorokhodSpace.IsSubdivisionBased` asks for `t₀` among the
nodes, so the recursion has to *start* there and not at the window's left edge.
Inserting `t₀` afterwards is not available: splitting a cell at an interior point
leaves the second piece measured from the new node, which costs a factor `2`
(`SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells`), and — decisively — it
destroys the `δ`-sparseness the construction exists to produce. The hypothesis
`hbase` is therefore where the base point enters the criterion.

The second is that on the index the processes have it costs nothing.
`SkorokhodSpace.modulusBased_extendNNReal_le_of_forall_gapped` asks for the times
on `ℝ≥0` alone, starting at `0`: `SkorokhodSpace.extendNNReal` is constant on the
negative half line, so the window `exhaustion 0 u` carries one free cell to the
left of `0`, of oscillation `0` and sparse as soon as `δ < u` — the regime the
criterion runs in anyway, `SkorokhodSpace.modulusBased_mono` carrying a bound at
one radius down to every smaller one.

**What the probabilistic half still has to supply, and where Mathlib stops.**
The hitting times `τ (k+1) = inf {t > τ k | ε < dist (X t) (X (τ k))}` are the
hitting times of an **open** set, so that they are stopping times is the début
theorem. Mathlib has only the discrete case, checked at the source on
`94ef6b89544e58e90f119da869f3fb48d1da0f4c`:
`MeasureTheory.Adapted.isStoppingTime_hittingBtwn` and
`MeasureTheory.Adapted.isStoppingTime_hittingAfter`
(`Probability/Process/HittingTime.lean:399` and `:412`) both carry
`[Countable ι]` and `[WellFoundedLT ι]`, and the words `debut` and `début` do not
occur in the library.

**The choice is made, and the début theorem is built**, 2026-09-20, in
**MartingaleProblems** under „The début of a right-open random set":
`MeasureTheory.isStoppingTime_debutTime` reads the début of a random set which
contains an interval `[t, v)` around each of its points as a stopping time for a
**right continuous** filtration, and `MeasureTheory.isRightOpen_oscSet`,
`MeasureTheory.measurableSet_mem_oscSet` and
`MeasureTheory.dist_le_of_lt_debutTime_oscSet` are its three inputs for the
oscillation set. The infimum along a countable dense set was rejected, and the
reason is the cell bound: between two such times the path could still move by
more than `ε` at an instant outside the dense set, so the very property these
times are formed for would be lost. What the right continuous filtration costs
the consumer is that its increment bound has to hold at `𝓕₊`-stopping times, and
that is said at the declaration.

**And the junk value is settled in the same breath.** `sInf ∅ = 0`, and the set
is empty as soon as the path never again moves by more than `ε` after `τ k`; then
`τ (k+1)` would be `0` and therefore *below* `τ k`, so the monotonicity that
`SkorokhodSpace.modulusBased_le_of_forall_gapped` asks for fails. This is the
same shape as `stepIndex` in **MartingaleProblems**, where the junk value
silently destroyed monotonicity in the time. `MeasureTheory.debutTime` is
therefore `WithTop ι` valued and `MeasureTheory.debutTime_of_eq_empty` says that
the empty case gives `⊤`.

**And the recursion is built on it**, 2026-09-20, in **MartingaleProblems** under
„The Aldous hitting recursion": `MeasureTheory.oscHitSeq` with
`MeasureTheory.isStoppingTime_oscHitSeq`. Of the three hypotheses
`SkorokhodSpace.modulusBased_le_of_forall_gapped` asks of its times, the
recursion supplies two without any probability:
`MeasureTheory.dist_stoppedValue_oscHitSeq_le` is the cell bound and
`MeasureTheory.lt_oscHitSeq_succ` the strict monotonicity, the latter from
`0 < ε` and right continuity, since the début of a right-open set need not be
attained. The `δ`-sparseness is the one that stays probabilistic.

**And `SkorokhodSpace.modulusBased_extendNNReal_le_of_forall_gapped` is
consumed**, 2026-09-20:
`MeasureTheory.modulusBased_extendNNReal_le_of_oscHitSeq` in
**MartingaleProblems** feeds it the recursion and keeps only the `δ`-sparseness
in the hypothesis, so the whole deterministic half of the criterion is one
implication. Two things about it are worth recording here, because they are
statements about the consumer of *this* milestone. The first: it does not use
`MeasureTheory.lt_oscHitSeq_succ`, because the strict monotonicity this
theorem asks for follows from its own `hgap` together with the unconditional
`MeasureTheory.oscHitSeq_le_succ`; the right continuity of the paths is spent
not here but in showing that `hgap` can hold at all. The second: the times are
handed over as an `ℝ≥0`-valued sequence under an explicit finiteness
hypothesis, produced from one statement by
`MeasureTheory.exists_coe_oscHitSeq_of_ne_top`, and not by reading
`WithTop.untopA`. At the **last** stage that finiteness is not wanted at all,
and the general form `MeasureTheory.modulusBased_extendNNReal_le_of_oscHitSeq_le`
drops it: `⊤` there means the path never again moves by more than `ε`, so any
point beyond the horizon closes the subdivision and `hmax` and `hosc` of this
theorem are met a fortiori. That general form asks its gap in the ordered shape
`τ k + δ < τ (k+1)` instead of through `dist`, because the last cell gets no
monotonicity from the recursion; under the monotonicity the two shapes agree.

**And the consumer reads it as a complement**, 2026-09-20:
`MeasureTheory.setOf_lt_modulusBased_subset_oscHitSeq` in **MartingaleProblems**
is the contrapositive, an inclusion of the set where
`SkorokhodSpace.modulusBased 0 u (SkorokhodSpace.extendNNReal (Φ ω)) δ` exceeds
`ENNReal.ofReal ε` in `N` gap events plus one horizon event — each gap event cut
down to the sample points at which the recursion has not yet passed `u`, which
is what makes it estimable at all. What that says about
*this* milestone is that no measurability of
`SkorokhodSpace.modulusBased` is needed on the way from the criterion to the
estimate: `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff` applies its measure
as an **outer** measure to an arbitrary set, and
`MeasureTheory.measure_mono` (`MeasureTheory/OuterMeasure/Basic.lean:51`) with
`MeasureTheory.measure_biUnion_finset_le` (`:80`) is the whole passage, carried
out in `MeasureTheory.measure_setOf_lt_modulusBased_le_oscHitSeq`. The question
whether the modulus is a measurable function of the path does not arise and is
not answered here. `card_le_of_gapped` of this milestone is what bounds the
number of summands the estimate then has.

**And the bound is `c`, not `2 c`.** `SkorokhodSpace.subdivisionOsc` measures each
cell from its **left endpoint**, where Billingsley's `w'` takes the diameter of
the cell, so the passage from an `ε`-controlled hitting recursion to the modulus
does not pay the classical factor `2`. The conclusion of
`SkorokhodSpace.modulusBased_le_of_forall_stoppingTime` above is therefore to read
`ε` where the outline wrote `2 ε`. This is the second time this factor has been
found not to be owed; the first was the composition of the two maximal estimates
on 2026-09-20.

**If an atom-tolerant Aldous is wanted**, the clause is small and needs no new
notion. The atom set `A` of a clock is deterministic and countable — from
`q (Set.Iic t) ≠ ∞` only countably many atoms lie in each window — so ask the
condition only on windows that miss it,

```
P ( d (X n (τ + θ)) (X n τ) > ε  ∧  Clock.interval q c τ (τ + θ) ∩ A = ∅ )
```

and put the atoms among the subdivision nodes. That is the same device as
`thm:absconvaug` of the manuscript: deterministic exceptional times are **named
and carried**, where random ones would force a new mode of convergence
(`rem:augvsws`). The hypothesis under which the verification from a martingale
problem goes through is already in **MartingaleProblems** Milestone 1 and is not
invented for this: optional sampling gives

```
𝔼[ f (X (τ+θ)) − f (X τ) | 𝓕 τ ]  ≤  C · q (Clock.interval q c τ (τ+θ))
```

for `|g| ≤ C`, and that tends to `0` precisely under `Clock.IsContinuousFor` —
the condition that replaced atomlessness in `isQuasiLeftContinuous_of_isMPSolutionFor`
on 2026-09-17.

**Acceptance examples.**

* The deterministic step above: tight, `modulusBased = 0`, Aldous' condition
  false. This is the instance on which a claim that the criterion is necessary
  would be checked.
* A jump process of **MartingaleProblems** Milestone 4 under `lebesgueClock`:
  the rate bound gives `C` and `lebesgueClock_isContinuousFor_optional` gives the
  limit, so the criterion applies and must return the tightness that
  `isTightMeasureSet_map_extendNNReal_map_jumpPathD` already has by another
  route. Two routes to the same conclusion is what makes this milestone
  checkable.
