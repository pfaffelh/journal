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

Prior art whose design is to be followed and whose code may be reused: the
repository `RemyDegenne/brownian-motion`, Apache License 2.0, file
`BrownianMotion/StochasticIntegral/Cadlag.lean`. It defines right continuity and
the càdlàg property for a preorder with a topology, together with jump sets and
closure properties. Milestone 2 below states what is wanted; where that file
already contains a declaration, it is to be taken over with its copyright header
and author attribution preserved, as the Apache licence requires.

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
  types `ℝ` and `ℤ` carry all five instances already.
* `dist_eq_sub_of_le` and `monotoneOn_dist_basepoint`: for `t₀ ≤ s ≤ t`,
  `dist s t = dist t₀ t - dist t₀ s`, and `t ↦ dist t₀ t` is monotone on
  `Set.Ici t₀`. This is the step from which the embedding above follows.
* `exhaustion`: fixing a base point `t₀`, the sets `B m = closedBall t₀ m` are
  compact, increasing, cover the index, and each is a linear order with a least
  and a greatest element. Define the clamp
  `clamp m t = min (max t (B m).min) (B m).max` and prove it is monotone,
  continuous, idempotent, and the identity on `B m`.
* Independence of the base point: two base points give exhaustions each of which
  refines the other after finitely many steps.

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
and each of the four statements below is trivially true. The other three running
instances `ℝ`, `Set.Ici (0:ℝ)` and `Set.Icc (0:ℝ) T` satisfy (B), with `D` the
rational points. So the jump theory is to be proved under (B) and instantiated
for those three; the discrete index gets its own one line instance and no
exhaustion argument. The metric on `ι` is first used in Milestone 3, and no
statement of this milestone uses it: `largeLeftJumpSet` measures with `dist` on
`E`.

Under (A), for `f : ι → E`:

* `Function.RightContinuous f`, defined as `∀ a, ContinuousWithinAt f (Set.Ioi a) a`.
* `IsCadlag f`, a structure with fields `right_continuous` and
  `left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)`.
* Basic closure properties: constants, compositions with continuous maps, sums
  and products in a topological ring, pointwise limits that are uniform on
  compacts, and the restriction of a càdlàg function to a subinterval.
* `IsCadlag.isBounded_image_of_isCompact`: the image of a compact set under a
  càdlàg map into a pseudometric space is bounded. The metric here is on `E`;
  the index contributes compactness of the domain and nothing else.
* `IsCadlag` for a continuous map.

Under (A′):

* `IsCadlag.tendsto_leftLim`, `Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x))`,
  which is `tendsto_leftLim_of_tendsto` applied to the `left_limit` field, and
  `IsCadlag.rightLim_eq`, `Function.rightLim f x = f x`, which is
  `ContinuousWithinAt.rightLim_eq` applied to the `right_continuous` field
  through `continuousWithinAt_Ioi_iff_Ici`; the second adds `[T2Space E]`. These
  connect the structure to `Function.leftLim` and `Function.rightLim` so that
  the existing API applies; every later statement about left limits uses those
  names, not a new one.
* The identity `Function.leftLim f x = f x` at continuity points, from
  `ContinuousWithinAt.leftLim_eq` applied to the restriction of continuity at
  `x` to `Iic x`, with `[T2Space E]`.

Under (B), with `E` a pseudometric space:

* Jump sets: `leftJumpSet f = {x | f⁻ x ≠ f x}` and, for `ε > 0`,
  `largeLeftJumpSet f ε = {x | ε ≤ dist (f⁻ x) (f x)}`. That
  `largeLeftJumpSet f ε` has no accumulation point, hence meets every compact
  set in a finite set, is (B) alone: an accumulation point yields a monotone
  sequence converging to it, which is where linearity and the order topology are
  used, and the one sided limit at that point contradicts the jump size. With
  them, the characterization of continuity of a càdlàg map as
  `leftJumpSet f = ∅`, from the identity of (A′) at continuity points in the one
  direction and, in the other, from `IsCadlag.tendsto_leftLim` rewritten along
  `f⁻ x = f x` to give continuity within `Iio x`, which together with the
  `right_continuous` field gives continuity at `x`.
* `leftJumpSet f` is countable. This adds **σ-compactness of `ι`** to (B), to
  turn local finiteness into countability along a countable exhaustion; every
  index of Milestone 1 has it, since closed balls are compact. The monotone case
  is `Monotone.countable_not_continuousAt`, which lives in
  `Mathlib/Topology/Order/Monotone.lean` and not in
  `Mathlib/Topology/Order/LeftRightLim.lean`, where only the module comment
  names it; the càdlàg case does not follow from it.
* `IsCadlag.measurable`: a càdlàg map into a Polish space is Borel measurable,
  via approximation by right continuous step functions along `D`. Linearity is
  what makes the step functions definable and the countable dense `D` is what
  indexes them; this is (B) exactly, with σ-compactness for the exhausting
  sequence of steps.
* A càdlàg map is determined by its restriction to a dense set: if `f` and `g`
  are càdlàg and agree on a dense `D ⊆ ι`, they are equal. This is right
  continuity together with the clause of (B) that every non-maximal point is
  approximable from the right, and it is the sharpest use of that clause
  anywhere in this roadmap. This is the statement Milestone 6 turns into a
  measurable embedding.

## Milestone 3: time changes

* `TimeChange ι`, the type of bi-Lipschitz order isomorphisms `λ : ι ≃o ι`.
  Give it a group structure.
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
  `lipConst (λ * μ) ≤ lipConst λ * lipConst μ` from `LipschitzWith.comp`.
* `TimeChange.norm_one`, `TimeChange.norm_inv` (`norm λ⁻¹ = norm λ`) and
  `TimeChange.norm_mul_le` (`norm (λ * μ) ≤ norm λ + norm μ`): the norm is a
  length function. Both facts are the corresponding statements for Lipschitz
  constants.
* `TimeChange.dist_le_of_norm_le`: on `B m`, `norm λ ≤ γ` implies
  `dist (λ t) t ≤ (exp γ - 1) * (2 * m)`, so a time change of small norm moves
  points of `B m` little. This is the estimate that makes the metric of
  Milestone 4 separate points.
* For the index `ℝ`, the identification of `norm` with Billingsley's
  `sup_{s < t} |log ((λ t - λ s) / (t - s))|`.

## Milestone 4: the space and its metric

* `SkorokhodSpace ι E`, notation `D ι E`, the type of càdlàg maps `ι → E`,
  as a structure bundling `toFun` with `isCadlag`.
* `SkorokhodSpace.restrictExhaustion m f = f ∘ clamp m`, a path constant outside
  `B m`.
* The localized distances
  ```
  distOn m f g = ⨅ λ, max (TimeChange.normOn m λ)
                          (⨆ t, r (restrictExhaustion m f (λ t)) (restrictExhaustion m g t))
  dist f g     = ∑' m, 2⁻¹ ^ m * min 1 (distOn m f g)
  ```
  Prove the supremum is attained on `B m` and is finite.
* `MetricSpace (D ι E)`: symmetry from `TimeChange.norm_inv`, the triangle
  inequality from `TimeChange.norm_mul_le`, and separation from
  `TimeChange.dist_le_of_norm_le` together with right continuity.
* `SkorokhodSpace.tendsto_iff`: `f n → f` if and only if for every `m` there are
  time changes `λ n` with `normOn m (λ n) → 0` and
  `sup_{t ∈ B m} r (f n (λ n t)) (f t) → 0`.
* `SkorokhodSpace.tendsto_of_tendsto_uniformly`: uniform convergence on compact
  sets implies convergence in `D ι E`; and the converse when the limit is
  continuous.
* Evaluation: `SkorokhodSpace.continuousAt_eval` — `f ↦ f t` is continuous at
  every `f` with `f⁻ t = f t`, and discontinuous at every other `f`.

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
