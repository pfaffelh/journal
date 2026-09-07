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
* `AdditiveDist.orderIso_isometry_real`: a linear order with a metric inducing
  the order topology and additive along the order embeds into `ℝ` by an order
  isomorphism onto its image which is an isometry; the image is closed when
  closed balls are compact. State the embedding as a bundled
  `OrderIso`-and-`Isometry` onto its range.
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
* `exhaustion`: fixing a base point `t₀`, the sets `B m = closedBall t₀ m` are
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
* `ordConnected_exhaustion`: the window is an order interval. This is the step
  the clamp actually needs — being between the least and the greatest element
  of a set does not put a point in the set unless the set is order convex — and
  it is `AdditiveDist` again: above the base point `monotoneOn_dist_basepoint`
  gives it, below the base point the additivity is read from the other end.
  Proved (2026-09-07). It needs neither the order topology nor properness.
* Independence of the base point: two base points give exhaustions each of which
  refines the other after finitely many steps.

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

  None of these three items uses the countable dense set of (B) or its right
  approximation clause. They stood under (B) from 2026-08-29 to 2026-09-07, and
  the proofs do not bear that out. What (B) is genuinely for are two of the
  three items below, `IsCadlag.measurable` and `IsCadlag.eq_of_eqOn_dense`; the
  third, `IsCadlag.eq_of_forall_exists_dist_le`, is again (A′) and is listed
  there only because Milestone 4 consumes it next to them.

Under (B), with `E` a pseudometric space:

* `IsCadlag.measurable`: a càdlàg map into a Polish space is Borel measurable,
  via approximation by right continuous step functions along `D`. Linearity is
  what makes the step functions definable and the countable dense `D` is what
  indexes them; this is (B) exactly, with σ-compactness for the exhausting
  sequence of steps.
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
  distOn m f g = ⨅ λ, max (TimeChange.norm λ)
                          (⨆ t, r (restrictExhaustion m f (λ t)) (restrictExhaustion m g t))
  dist f g     = ∑' m, 2⁻¹ ^ m * min 1 (distOn m f g)
  ```
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
  every `f` with `f⁻ t = f t`, and discontinuous at every other `f`.

**Acceptance examples.**

* **The sliding step: the metric is not the uniform metric.** `ι = ℝ`, `E = ℝ`,
  `t₀ = 0`, `f = Set.indicator (Set.Ici 1) 1` and
  `g ε = Set.indicator (Set.Ici (1 + ε)) 1` for `ε > 0`. The uniform distance
  is `1` for every `ε`, while `distOn m f (g ε) ≤ Real.log (1 + ε)` for
  `ε ≤ 1 ≤ m`, witnessed by the piecewise linear time change fixing `0` that carries
  `1 + ε` to `1` and is affine on `[0, 1+ε]` and a translation beyond. So
  `dist f (g ε) → 0` as `ε → 0`. This is the defining property of the `J₁`
  topology, the one thing a wrong definition of `distOn` — the uniform metric,
  or an infimum over all order isomorphisms without the norm term — gets wrong,
  and the pair every later statement about `D ι E` is calibrated against.
* **Evaluation at the jump, which is the manuscript's `ex:atomicdiscontinuity`.**
  With `f` and `g (1/n)` as above, `g (1/n) → f` in `D ℝ ℝ` while
  `eval 1 (g (1/n)) = 0` and `eval 1 f = 1`. So `continuousAt_eval` must be
  false at `f`, and `f⁻ 1 = 0 ≠ 1 = f 1` is exactly its criterion; at any
  `t ≠ 1` the same map is continuous at `f`. The manuscript reads this as the
  failure of hypothesis `(C3a)` for a clock with an atom at `1`.
* **The two jumps that cannot merge.** `f n = Set.indicator (Set.Ici 1) 1 +
  Set.indicator (Set.Ici (1 + 1/n)) 1`. Pointwise `f n → 2 • Set.indicator
  (Set.Ici 1) 1`, and in `D ℝ ℝ` it does **not** converge: a time change of
  small norm moves `1` and `1 + 1/n` by little, so the image path still has two
  jumps of height `1` while the candidate limit has one of height `2`: for every
  càdlàg `h` and every `m ≥ 2`, `1/2 ≤ liminf n, distOn m (f n) h`, so no
  subsequence converges. This is the
  standard witness that `J₁` is not the topology of pointwise convergence, and
  it reappears in Milestone 7 as a family without compact closure.
* **The degenerate window.** `ι = Set.Icc (0:ℝ) 0` or `m = 0` on a discrete
  index: `B m` is a single point, every `distOn m f g` is
  `min over the trivial group of max 0 (r (f t₀) (g t₀))`, and `dist` is the sum
  of the tail. The metric axioms must all hold there, which is where the junk
  values of Milestone 3 are consumed.

## Milestone 5: completeness and separability

* `CompleteSpace (D ι E)`: for a Cauchy sequence extract a subsequence whose
  consecutive distances are summable, compose the time changes, and use
  completeness of `E` together with `TimeChange.norm_mul_le` to see that the
  composed time changes converge.
* `SeparableSpace (D ι E)`: the piecewise constant paths taking finitely many
  values from a countable dense subset of `E` on the intervals of a rational
  subdivision of `B m` are dense.
* `PolishSpace (D ι E)`, from the two above.
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
  `distOn`, at cost `|log (p / (1/Real.sqrt 2))|`.

## Milestone 6: the Borel structure

* `SkorokhodSpace.measurable_eval`: `f ↦ f t` is Borel measurable for every `t`.
* `SkorokhodSpace.measurableEmbedding_piDense`: for countable dense `D ⊆ ι`, the
  map `f ↦ (fun t : D ↦ f t)` into `D → E` is a measurable embedding.
* `SkorokhodSpace.borel_eq_iSup_comap_eval`:
  `borel (D ι E) = ⨆ t, MeasurableSpace.comap (eval t) (borel E)`, and the same
  with `t` ranging over a countable dense set only.
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
  hypothesis on `D`.
* **The law of a Poisson process is fixed by rational times.** `ι = Set.Ici (0:ℝ)`,
  `E = ℝ`, `D = ℚ ∩ ι`. Two laws on `D ι ℝ` whose finite dimensional
  distributions along `D` are those of a Poisson process of rate `1` are equal,
  by `borel_eq_iSup_comap_eval` along a countable dense set. The times at which
  the process jumps are almost surely irrational, so no coordinate in `D` sees a
  jump: the example shows the conclusion does not need the coordinates to
  determine the paths pointwise, only the σ-algebra.

## Milestone 7: the modulus and compactness

* `SkorokhodSpace.modulus m f δ`, the infimum of those `ε ≥ 0` for which there is
  a finite subdivision `min (B m) = t 0 < ... < t n = max (B m)` with
  `dist (t (i-1)) (t i) > δ` for every `i` and `r (f s) (f (t (i-1))) ≤ ε` for
  all `s ∈ Set.Ico (t (i-1)) (t i)`.
* `SkorokhodSpace.tendsto_modulus`: `modulus m f δ → 0` as `δ → 0`, for each
  fixed `f` and `m`. This is the càdlàg property in quantitative form.
* `modulus` is monotone in `δ` and in `m`.
* `SkorokhodSpace.isCompact_closure_iff`: `A ⊆ D ι E` has compact closure if and
  only if for every `m` the set `{f t | f ∈ A, t ∈ B m}` has compact closure in
  `E` and `lim_{δ→0} sup_{f ∈ A} modulus m f δ = 0`. Both directions.
* `SkorokhodSpace.isCompact_closure_of_compactContainment`: the sufficient form
  used in practice, where the first condition is replaced by the existence of a
  compact `K ⊆ E` with `f t ∈ K` for all `f ∈ A` and `t ∈ B m`.

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
* **A family that does have compact closure.**
  `A = {Set.indicator (Set.Ici a) 1 | a ∈ Set.Icc 1 2}`. The values lie in
  `{0,1}` and `modulus m f δ = 0` for `δ` smaller than the distance from `a` to
  the window ends, uniformly in `a` once the window is `B m` with `m ≥ 3`; so
  both conditions hold and the closure is compact. It is: the closure is the
  continuous image of `Set.Icc 1 2` under `a ↦ Set.indicator (Set.Ici a) 1`,
  which is where the sliding step example of Milestone 4 says the map is
  continuous.

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
  `SeparableSpace (D ι E)` of Milestone 5, which itself asks only for a countable
  dense subset of `E`. Its ingredients, in the
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
