# The Skorokhod space

The space of càdlàg paths with the `J₁` topology. The string `cadlag` does not occur in
Mathlib, and neither does the space. What Mathlib does have, and what is **not**
to be rebuilt:

* `Mathlib/Topology/Order/LeftRightLim.lean`: `Function.leftLim` and
  `Function.rightLim` with `tendsto_leftLim`, `tendsto_rightLim`,
  `tendsto_leftLim_within`, `continuousWithinAt_Iio_iff_leftLim_eq`,
  `continuousWithinAt_Ioi_iff_rightLim_eq` and
  `continuousAt_iff_leftLim_eq_rightLim`. These are the whole one-sided-limit
  API and every statement about left limits below is to be phrased through
  them. It also has `Monotone.countable_not_continuousAt`, the monotone case of
  the countability of the jump set.
* `MeasureTheory.StieltjesFunction` in
  `Mathlib/MeasureTheory/Measure/Stieltjes.lean`: a bundled monotone right
  continuous function, with `right_continuous` and `rightLim_eq`. It is the
  precedent for how a right continuity condition is bundled in Mathlib, and
  `IsCadlag` below should read like it.
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
    discrete `AdditiveDist` subtype, or the `OrderTopology` instance directly.
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

Throughout the rest of this roadmap, `ι` denotes an index with these instances
and `E` a Polish space with metric `r`.

## Milestone 2: càdlàg functions

For `f : ι → E` with `[Preorder ι] [TopologicalSpace ι] [TopologicalSpace E]`:

* `Function.RightContinuous f`, defined as `∀ a, ContinuousWithinAt f (Set.Ioi a) a`.
* `IsCadlag f`, a structure with fields `right_continuous` and
  `left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)`.
* Basic closure properties: constants, compositions with continuous maps, sums
  and products in a topological ring, pointwise limits that are uniform on
  compacts, and the restriction of a càdlàg function to a subinterval.
* `IsCadlag.tendsto_leftLim` and `IsCadlag.rightLim_eq`, connecting the
  structure to `Function.leftLim` and `Function.rightLim` so that the existing
  API applies; every later statement about left limits uses those names, not a
  new one.
* `IsCadlag.isBounded_image_of_isCompact`: the image of a compact set under a
  càdlàg map into a pseudometric space is bounded.
* The identity `Function.leftLim f x = f x` at continuity points, from
  `continuousAt_iff_leftLim_eq_rightLim` together with right continuity.
* Jump sets: `leftJumpSet f = {x | f⁻ x ≠ f x}` and, for `ε > 0`,
  `largeLeftJumpSet f ε = {x | ε ≤ dist (f⁻ x) (f x)}`. Prove that
  `largeLeftJumpSet f ε` has no accumulation point, hence meets every compact set
  in a finite set, and that `leftJumpSet f` is countable. The monotone case of
  the last statement is `Monotone.countable_not_continuousAt`; the càdlàg case
  does not follow from it and is proved by the exhaustion.
* `IsCadlag.measurable`: a càdlàg map into a Polish space is Borel measurable,
  via approximation by the right continuous step functions of the exhaustion.
* A càdlàg map is determined by its restriction to a dense set: if `f` and `g`
  are càdlàg and agree on a dense `D ⊆ ι`, they are equal. This is the statement
  Milestone 6 turns into a measurable embedding.
* `IsCadlag` for a continuous map, and the characterization of continuity of a
  càdlàg map as `leftJumpSet f = ∅`.

## Milestone 3: time changes

* `TimeChange ι`, the type of bi-Lipschitz order isomorphisms `λ : ι ≃o ι`.
  Give it a group structure.
* `TimeChange.norm λ = log (max (LipschitzWith.const λ) (LipschitzWith.const λ⁻¹))`,
  with `TimeChange.normOn m λ` the same computed on `B m`.
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
index of Milestone 1 and `E` Polish; the roadmap **WeakConvergence** supplies
convergence determining classes and the continuous mapping theorem.

* `SkorokhodSpace.isTightMeasureSet_iff`: a set of laws is tight if and only if
  for every `ε > 0` and `m` there are a compact `K ⊆ E` and a function
  `δ ↦ η δ` tending to `0` with
  `μ {f | ∀ t ∈ B m, f t ∈ K} ≥ 1 - ε` and
  `μ {f | modulus m f δ ≥ η δ} ≤ ε`, uniformly over the set. Combine
  Milestone 7 with `MeasureTheory.isTightMeasureSet_of_isCompact_closure` and
  its converse.
* `SkorokhodSpace.tendsto_finiteDimensional_of_tendsto`: if `μ n → μ` weakly
  then, for every finite family `t 1, ..., t k` of points at which the limit has
  no fixed discontinuity — that is `μ {f | f⁻ (t i) = f (t i)} = 1` — the
  finite dimensional distributions converge. The set of `t` failing this is
  countable.
* `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional`: a tight
  family whose finite dimensional distributions along a dense set converge
  converges weakly. Prokhorov plus Milestone 6.
* `SkorokhodSpace.exists_countable_dense_continuity`: for a single `μ`, the set
  of `t` with `μ {f | f⁻ t = f t} = 1` has countable complement, hence contains
  a countable dense set.
