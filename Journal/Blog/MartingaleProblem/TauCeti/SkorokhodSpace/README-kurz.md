# The Skorokhod space

The space of càdlàg paths with the `J₁` topology. The space does not occur in
Mathlib; the *predicate* does, since #43352, as `Mathlib/Topology/Order/Cadlag.lean`,
and Milestone 2 is written against it.

The time index is a linear order carrying a metric that induces the order
topology, is additive along the order, and has compact closed balls. That
hypothesis is equivalent to being a closed subset of `ℝ` (Milestone 1), and
stating it as a class rather than fixing `[0,1]` or `[0,∞)` is what makes `ℝ`,
`[0,∞)`, `[0,T]`, `h • ℤ` and every closed subset of them instances of one
development.

This roadmap depends on **WeakConvergence** for separating and convergence
determining classes, for the continuous mapping theorem for almost everywhere
continuous maps, and for the Skorokhod representation theorem; the dependency is
an `import` and not only a citation, and only Milestone 8 uses it.

`Suggested.lean` prototypes the signatures. Most of them are discharged there,
against Mathlib `master`; that is evidence the milestones are reachable, not a
prescription of how. Where a proof route is named below it is because the
obvious route is **wrong**, not because it is the one taken.

## What Mathlib already has

Not to be rebuilt.

* `Topology/Order/Cadlag.lean`: `IsRightContinuous` and `IsLeftContinuous` in the
  root namespace; the structures `IsCadlag` and `IsCaglad`, with fields
  `isRightContinuous` and `tendsto_nhdsLT`; and the closure properties
  `Continuous.isCadlag`, `IsCadlag.const`, `.continuous_comp`, `.continuous_comp₂`,
  `.mul`, `.div'`, `.const_smul`. Under `[LinearOrder] [OrderTopology]` also
  `IsCadlag.tendsto_nhdsLT_leftLim`; under `[PseudoMetricSpace Y]`,
  `IsCadlag.isLocallyBounded` and `isBounded_image_of_isCadlag_of_isCompact`.

  `MeasureTheory.Filtration.IsRightContinuous` is a **different** predicate,
  about a filtration rather than a function; the two share a name and nothing
  else.
* `Topology/Order/LeftRightLim.lean`: `Function.leftLim`, `Function.rightLim`,
  and the part of the one-sided-limit API that holds for an arbitrary `f` —
  `tendsto_leftLim_of_tendsto`, `ContinuousWithinAt.leftLim_eq`,
  `leftLim_eq_of_tendsto` and their mirrors. The names in the `Monotone` and
  `Antitone` namespaces of that file carry a monotonicity hypothesis and ask for
  a conditionally complete codomain; a càdlàg path into a metric space satisfies
  none of that, and this roadmap uses none of them.
* `Monotone.countable_not_continuousAt` and its `MonotoneOn` companions;
  `MeasureTheory.StieltjesFunction`, the precedent for how right continuity is
  bundled (its field uses `Ici`, `IsRightContinuous` uses `Ioi`, and
  `continuousWithinAt_Ioi_iff_Ici` is the bridge).
* Prokhorov, tightness and the Lévy–Prokhorov metric, used in Milestone 8.
* `orderTopology_of_ordConnected`, `ProperSpace.of_isClosed`, and the instance
  that a discrete subgroup is closed (`AddSubgroup.isClosed_of_discreteTopology`
  under `[T1Space]`, with the older `_of_discrete` a deprecated alias).

**Prior art, cited and not presupposed.** `RemyDegenne/brownian-motion`
(Apache-2.0) contains a development of càdlàg paths whose predicate is what went
upstream as #43352. It is named as a source an implementer may consult and, the
licence permitting, draw on with its copyright header preserved — **not** as the
specification. Nothing here should be accepted merely because it matches that
file.

## Milestone 1: the index typeclass

```
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u
```

with `BasePoint α` carrying a distinguished point as **data**.

**Why `BasePoint` is data and not `[Nonempty ι]` with `Classical.arbitrary`.**
The metric of Milestone 4 is anchored at a point twice over, through the
exhaustion and through `TimeChange.fixing t₀`, while `D ι E` carries none, so a
parameterless instance must read one off the index. Under `Classical.arbitrary`
the identification `dist f g = totalDist 0 f g` on `D(ℝ, E)` is unavailable, and
with it not one acceptance example of Milestones 4 to 7 can even be stated. With
`BasePoint` the identification is `SkorokhodSpace.dist_eq`, and it is `rfl`.

* Instances for `ℝ`, `ℤ`, `ℕ`, `ℝ≥0`, and for a subtype of an `AdditiveDist`
  type. Two places where the subtype instance does not carry as far as it looks,
  both to be settled here rather than met later: it does **not** fire through a
  `SetLike` hull (`AdditiveDist (AddSubgroup.zmultiples h)` does not resolve
  while the same on the underlying `Set ℝ` does), and a discrete subset is not
  order-connected, so `orderTopology_of_ordConnected` does not reach `h • ℤ` —
  supply `PredOrder`/`SuccOrder` or `LocallyFiniteOrder`. `ℝ≥0` is likewise not
  a subtype of `ℝ` for instance search and needs its own instance.
* `lengthCoord t₀ t = if t₀ ≤ t then dist t₀ t else -dist t₀ t`, with
  `sub_lengthCoord_of_le`, `strictMono_lengthCoord`, `isometry_lengthCoord`. The
  coordinate is **written out** rather than read off the existence statement
  below, because a construction of a time change needs a *named* coordinate: an
  order isomorphism produced by an existential is opaque.
* `exists_orderIso_isometry_real` — an `AdditiveDist` index is order isomorphic
  and isometric to a closed subset of `ℝ`, namely the range of `lengthCoord`.
  **The order topology is not used**; `ProperSpace` enters only through
  completeness. The empty index takes `s = ∅`.
* `AdditiveDist.dist_eq_sub_of_le`, `monotoneOn_dist_basepoint`, and
  `dist_eq_abs_sub_of_sameSide` — the last for `s`, `t` on **one side** of `t₀`.
  The same-side hypothesis is necessary: on `ℝ` with `t₀ = 0`, `s = -1`, `t = 1`
  the two sides are `2` and `0`. It is the form the estimate of Milestone 3
  consumes, where only the common position relative to `t₀` is known.
* `exhaustion t₀ u = closedBall t₀ (max u 0)`, with `isCompact_exhaustion`,
  `exhaustionMin`, `exhaustionMax`, and the clamp
  `clamp m t = min (max t (B m).min) (B m).max` — monotone, continuous,
  idempotent, the identity on `B m`. **The radius is a real number**, because the
  metric of Milestone 4 integrates over it and a countable set of radii is not
  enough. The `max u 0` keeps the three definitions total, a negative radius
  emptying the window.
* `ordConnected_exhaustion` — the window is an order interval. This is what the
  clamp actually needs: being between the least and the greatest element of a set
  does not put a point in the set unless the set is order convex.
* `monotone_exhaustionMax`, `antitone_exhaustionMin`, and hence
  `measurable_clamp` in the radius. This is the only place the index carries a
  measurable structure, and it is a hypothesis of those statements and not of the
  milestone.
* `exhaustion_subset_exhaustion : exhaustion t₀ u ⊆ exhaustion t₁ (u + dist t₀ t₁)`
  for `0 ≤ u` — the whole of what relates two base points, from the triangle
  inequality alone.
* `rightIsolated ι = {t | IsOpen (Set.Iic t)}` and `countable_rightIsolated`.
  The proof is intrinsic and does not go through the embedding into `ℝ`.
* `exists_countable_ciSup_eq` — **one countable set computes the supremum of
  every right continuous real function on the index.** It is a countable dense
  set together with `rightIsolated ι`, and the second summand is not decoration:
  on `Set.Icc (0:ℝ) 1` the dense set `ℚ ∩ [0,1)` misses `1`, approached from the
  left only. The set does not depend on the function — a supremum-approximating
  sequence would, and a different countable set per window radius computes
  nothing. This discharges the measurability obligation of Milestone 4.

**Acceptance examples.**

* **The four running instances, computed.** On `ℝ` with `t₀ = 0`,
  `B m = Icc (-m) m` and `clamp m = fun t ↦ min (max t (-m)) m`. On
  `AddSubgroup.zmultiples 1`, `B m` is a **finite** set, so the exhaustion
  machinery must not silently assume an interval. On `Icc (0:ℝ) T`,
  `clamp m = id` as soon as `T ≤ m` — the degenerate case every later induction
  over `m` has to survive.
* **A metric that is not `AdditiveDist`**: `dist x y = min 1 |x - y|` on `ℝ`
  induces the order topology and is not additive. The embedding theorem fails on
  it, which is where the class is spent.
* **A window that is not an interval of `ℝ`**: `Icc (0:ℝ) 1 ∪ {2}` with
  `m = 3/2` gives `clamp (3/2) 2 = 1`. That the value lands in the window again
  is `ordConnected_exhaustion` and **not** the formula: on the three-point order
  `{0<1<2}` with `dist 0 1 = 2`, `dist 1 2 = 1`, `dist 0 2 = 1` — a metric — the
  ball `B 1` is `{0,2}`, not order convex, and the clamp leaves it. That metric
  is not `AdditiveDist`, which is the point: order convexity of the windows is a
  theorem about the class, not about `clamp`.

From Milestone 3 on, `ι` denotes an index with these instances and `E` a Polish
space. Milestones 2 and 8 state their own, weaker hypotheses item by item.

## Milestone 2: càdlàg functions

Four hypothesis bundles are distinguished and every item says which it is under:
**(A)** `[Preorder ι] [TopologicalSpace ι] [TopologicalSpace E]`, what
`Topology/Order/Cadlag.lean` uses; **(A′)** the same with `[LinearOrder ι]` and
`[OrderTopology ι]`, the weakest under which `leftLim` exists; **(B)** (A′) with
a countable dense `D ⊆ ι` of which every non-maximal point is a limit.

Upstream and not to be rebuilt: the predicates, the closure properties,
`IsCadlag.tendsto_nhdsLT_leftLim`, and `isBounded_image_of_isCadlag_of_isCompact`.
What the library does not carry:

* `IsCadlag.of_tendstoUniformly` — the uniform limit of càdlàg paths is càdlàg,
  under `[CompleteSpace E]`; and `IsCadlag.of_tendstoUniformlyOn_exhaustion`,
  uniform convergence on **every window** being enough. This is the step at which
  `CompleteSpace (D ι E)` of Milestone 5 is paid for.
* `IsCadlag.of_forall_eventuallyEq` — **being càdlàg is local**: a function
  agreeing near every point with *some* càdlàg function is càdlàg.
* `IsCadlag.comp_monotone_continuous` — `f ∘ g` for monotone continuous `g`, the
  two indices **different**, which is what the index crossing of Milestone 9
  needs.
* Jump sets: `leftJumpSet f = {x | f⁻ x ≠ f x}` and
  `largeLeftJumpSet f ε = {x | ε ≤ dist (f⁻ x) (f x)}`, with the local finiteness
  of the latter, `finite_largeLeftJumpSet_inter` on a compact window, the
  countability of `leftJumpSet f` — which adds **σ-compactness of `ι`** to (A′),
  to turn local finiteness into countability — and
  `IsCadlag.continuousAt_iff_notMem_leftJumpSet`.
* `IsCadlag.measurable`, and `IsCadlag.eq_of_eqOn_dense`: a càdlàg map is
  determined by its restriction to a set dense **from the right**.
* `IsCadlag.exists_subdivision` — **the structure theorem, and the rung
  Milestones 5 and 7 share**: for `f` càdlàg on a compact `Icc a b` and `ε > 0`
  there is a finite subdivision with oscillation at most `ε` on every cell. With
  `exists_subdivision_through` for a prescribed interior node.
* `stepRetract t` — the retraction of the index onto the range of a finite tuple,
  with `eventually_stepRetract_eq_nhdsGT`, `isCadlag_comp_stepRetract` (**the
  step path is càdlàg, and the path it is read off need not be**),
  `finite_range_comp_stepRetract` and `dist_comp_stepRetract_le`. `stepPath` is
  the resulting path.

**Acceptance examples.**

* **The single step** `1_{[1,∞)}` on `ℝ`: càdlàg, `leftLim` at `1` is `0`, the
  jump set is `{1}`. Its mirror `1_{(1,∞)}` is not càdlàg, being left continuous
  at `1` instead.
* **Jumps accumulating from the right**: `∑' n, 2⁻ⁿ 1_{[1/(n+1),∞)}` is càdlàg
  including at `0`, where infinitely many jumps accumulate — so local finiteness
  must be asked of `largeLeftJumpSet` and not of `leftJumpSet`.
* **The discrete index**, where every `f` is càdlàg and every jump set is empty:
  the statements must not become vacuous by asking for more than (A′).

## Milestone 3: time changes

* `TimeChange ι`, the bi-Lipschitz order isomorphisms, as a group.
* `TimeChange.exists_of_lengthCoord` — time changes are **built in the coordinate
  of Milestone 1**: a strictly monotone `φ : ℝ → ℝ` fixing `0` and mapping the
  range of `lengthCoord` onto itself induces one.
* `TimeChange.lipConst`, `TimeChange.norm λ = log (max (lipConst λ) (lipConst λ⁻¹))`,
  with `norm_one`, `norm_inv` and `norm_mul_le`: the norm is a **length
  function** on the group.
* `TimeChange.fixing t₀`, a `Subgroup`, the index of the infimum of Milestone 4.
* `TimeChange.dist_le_of_norm_le` — for a time change fixing the base point and
  `t ∈ B m`, `norm λ ≤ γ` gives `dist (λ t) t ≤ (exp γ - 1) * m`.

**The windowed norm is not a length function**, and `normOn_mul_le` is therefore
**not** part of this milestone: it is false, and `not_normOn_mul_le` is the
refutation. Two time changes each cheap on a window can compose to an expensive
one there, because the first moves the window.

**Acceptance examples.** The dilations of `ℝ` (`norm (c • ·) = |log c|`); the
translations, which have norm `0` and are why `fixing t₀` exists; and
`steep * double` on `B 1`, which is `not_normOn_mul_le` run as a computation.

## Milestone 4: the space and its metric

* `SkorokhodSpace ι E`, notation `D ι E`, a structure bundling `toFun` with
  `isCadlag`; `restrictExhaustion t₀ m f = f ∘ clamp t₀ m`.
* The windowed distance `distWith`, its infimum `distOn u f g` over the time
  changes fixing `t₀`, the integral `intDist` over the radius, and the metric
  `SkorokhodSpace.metricSpace t₀` — symmetry from `norm_inv`, the triangle
  inequality from `norm_mul_le`, separation from the exhaustion covering the
  index. `SkorokhodSpace.dist_eq` identifies the parameterless instance with the
  one at `basePoint`, and it is `rfl`.
* `SkorokhodSpace.tendsto_iff` — `f n → f` iff for every window there are time
  changes fixing the base point with `norm → 0` and uniform convergence on the
  window after the change; `tendsto_of_tendsto_uniformly`, with the converse when
  the limit is continuous.
* Evaluation: `continuousAt_eval` at every `f` with `f⁻ t = f t`, and
  discontinuous at every other. The second half is what forces the hypotheses of
  Milestone 8.

**Acceptance examples.**

* **The sliding step**: the metric is neither the uniform metric nor a sum over
  integer windows.
* **Evaluation at the jump**, the manuscript's `ex:atomicdiscontinuity`:
  `g (1/n) → f` in `D ℝ ℝ` while the evaluations at `1` do not converge.
* **The two jumps that cannot merge**: `1_{[1,∞)} + 1_{[1+1/n,∞)}` converges
  pointwise to `2 · 1_{[1,∞)}` and **not** in `D ℝ ℝ` — a time change cannot
  merge two jumps into one.
* **The degenerate window**: a one-point `B u`, where every `distOn u` vanishes.

## Milestone 5: completeness and separability

* `CompleteSpace (D ι E)` — extract a subsequence with summable distances,
  compose the time changes, and use `IsCadlag.of_tendstoUniformlyOn_exhaustion`.
* `not_separableSpace_of_rigid` — **and it is what fixes the shape of everything
  below it.** If `ι` is uncountable and its only time change is the identity, the
  space is not separable: the step paths at distinct jump times stay uniformly
  apart, there being no time change to move one onto another.
* `HasCountableCore ι` — the class the previous item forces: a countable `C ⊆ ι`
  such that every finite strictly monotone tuple is approximated by one out of
  `C`. Instances for `ℝ`, `ℝ≥0`, `h • ℤ` and `Icc (0:ℝ) 1`; the `ℝ≥0` one is
  **inherited** from `ℝ` rather than built again.
* `SeparableSpace (D ι E)` under `[HasCountableCore ι]`, the countable dense set
  being the step paths with jump times in `C` and values in a countable dense
  subset of `E`; and `PolishSpace (D ι E)` from the two, which costs nothing.
* `isClosed_range_continuous` — the continuous paths form a closed subspace, on
  which the metric induces uniform convergence on compact sets.

**Acceptance examples.** The shrinking bump, which shows why the norm is
logarithmic; a Cauchy sequence whose pointwise limit is **not** the answer; the
countable dense set exhibited on `Icc (0:ℝ) 1`; and separability **refuted** on
the middle-thirds Cantor set as index — the instance that fixes the shape of the
statement.

## Milestone 6: the Borel structure

* `measurable_eval` — `f ↦ f t` is Borel measurable for every `t`. Two cases: at
  a point with nothing immediately above it evaluation *is* continuous
  (`continuous_eval_of_nhdsGT_eq_bot`); elsewhere it is the infimum over
  shrinking windows of lower semicontinuous suprema
  (`lowerSemicontinuous_iSup_edist`, `iInf_iSup_edist_eq`).
* `measurableEmbedding_piDense` for a countable `D` dense **from the right**, and
  `exists_countable_rightDense`, so the hypothesis is not vacuous.
* `borel_eq_iSup_comap_eval_of_countable_rightDense` and
  `borel_eq_iSup_comap_eval` — the Borel structure **is** the coordinate
  structure.
* `measurable_of_measurable_eval` — a map into `D ι E` is measurable as soon as
  every coordinate is.
* `evalFuns T` — the finite dimensional test functions along a set of times:
  products `f ↦ ∏ t ∈ s, F t (f t)` over a `Finset` inside `T` with `F t : E →ᵇ ℝ`.
  With `isMulSystem_evalFuns`, `measurable_of_mem_evalFuns`,
  `bounded_of_mem_evalFuns`, and `generateFromFuns_evalFuns`: along a countable
  right dense set the class generates the Borel structure. Hence
  `eq_of_forall_rightDense_forall_integral_evalPi_eq` and, on a densely ordered
  index, `eq_of_forall_dense_forall_integral_evalPi_eq`.
* The past: `evalFuns_mono`, `one_mem_evalFuns`,
  `generateFromFuns_evalFuns_eq_iSup` (no countability, no density),
  `comap_eval_le_iSup_of_neBot` — right continuity read as measurability — and
  `generateFromFuns_evalFuns_Iic`, the past at `s` generated by the coordinates
  at earlier times of a right dense set **together with `s` itself**.

**Acceptance examples.**

* **Measurable but not continuous on one path**: `1_{[1,∞)}` — `measurable_eval 1`
  holds while `continuousAt_eval 1` fails there.
* **The maximal point must be in `D`**: on `Icc (0:ℝ) 1` with `D = ([0,1) ∩ ℚ)`
  the paths `0` and `1_{{1}}` agree on `D` and differ. This is why the density is
  asked *from the right* and why a maximal point must be a member.
* **The law of a Poisson process is fixed by rational times.**

## Milestone 7: the modulus and compactness

`IsSubdivision t₀ m δ t` — a strictly monotone tuple spanning the window with all
gaps at least `δ`; `subdivisionOsc f t`, the oscillation over the half open
cells; and Billingsley's `w'`,

```
modulus t₀ m f δ = ⨅ over δ-sparse subdivisions of B m, subdivisionOsc f t .
```

**The endpoints must not be pinned, and the subdivision must be based.** Two
corrections, each with a refutation:

* `modulusPinned`, which fixes `t 0 = (B m).min`, makes `isCompact_closure_iff`
  **false**: `not_tendsto_iSup_modulusPinned` exhibits step paths in `D(ℝ, ℝ)`
  with compact closure whose pinned modulus does not tend to `0`, the first gap
  being forced to exceed `δ`. `modulus_le_modulusPinned` says the correction only
  lowers the modulus, so every upper bound proved of the pinned form survives.
* Even unpinned, the converse fails over `ℝ` for a modulus whose subdivisions may
  avoid the base point (`not_isCompact_closure_of_jumps_at_basePoint`). The
  repair is Ethier–Kurtz's own: `IsSubdivisionBased` requires a node **at** the
  base point, and `modulusBased` is the corresponding infimum, with
  `modulus_le_modulusBased`.

And the criterion is **false for a general index**:
`not_isCompact_closure_of_rigid`. On a rigid index a bounded family of step paths
with distinct jump times has every modulus `0` and no compact closure. So

* `isCompact_closure_iff`, **over the index `ℝ`** and with `modulusBased`:
  `A ⊆ D ℝ E` has compact closure iff for every window the values are relatively
  compact and `sup_{f ∈ A} modulusBased m f δ → 0` as `δ → 0`.
  `isCompact_closure_iff_nnreal` is the same over `ℝ≥0`, and
  `isCompact_closure_of_compactContainment` the sufficient form used in practice.

The two halves:

* Forward — `tendsto_iSup_modulus_of_isCompact` and its based analogue, with
  `totallyBounded_values_of_isCompact` and, under `[CompleteSpace E]`,
  `isCompact_closure_values_of_isCompact`. Four radii appear and are nested for a
  reason: the modulus is asked on `B m`, the subdivision taken on `B (m+1)`, and
  the time change needs the room between.
* Converse — the finite net. `exists_finite_grid_timeChange` builds the grid and
  the change onto it; `stepPathFamilyLe` is the finite family; the counting rests
  on `dist_first_last_eq_sum` (the gaps telescope under `AdditiveDist`) and
  `sub_mul_le_two_mul_of_isSubdivision` (a `δ`-sparse subdivision has boundedly
  many nodes in a window). `abs_sum_tent_sub_le` — a sum of tents with separated
  centres is Lipschitz **whatever their number** — is what keeps the Lipschitz
  constant free of the node count. `badRadii` is a **definition** and not an
  anonymous set inside a proof, so that its measure can be estimated twice, crudely
  and sharply.

Beyond the criterion, and what Milestone 8 and **MartingaleProblems** read:

* `modulusBased_mono`, `modulusBased_mono_window`, `tendsto_modulusBased`,
  `modulusBased_le_of_edist_le`.
* `measurable_iInf_modulusBased` and `upperSemicontinuous_iInf_modulusBased` —
  the based modulus is measurable in the path, which is what a law can integrate.
* `setOf_le_modulusBased_subset` and `setOf_le_iInf_modulusBased_subset` — **the
  sandwich a consumer reads**.
* `measure_map_postcomp_setOf_le_modulusBased_le`,
  `measure_map_setOf_le_modulusBased_le`,
  `isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le` and the variant
  `…_off_finite`, exempting finitely many members.
* `basePointOsc` and `tendsto_basePointOsc`, with
  `basePointOsc_le_three_mul_modulusBased`.

**Acceptance examples.** One jump costs nothing; infinitely many jumps still give
`tendsto_modulus`; the two jumps that cannot merge, as a compactness test; **the
jump that marches to the window's edge**, which is why the endpoints are not
pinned; **the jump that marches to the base point**, which is why the subdivision
is based; a family that does have compact closure; and the same family on a rigid
index, where the criterion must not be stated at all.

## Milestone 8: tightness and convergence of finite dimensional distributions

Two stages, and they are stated separately because they are used separately.

**Stage (B) — the tightness criterion.**

* `isTightMeasureSet_iff` — a set of laws on `D(ℝ, E)` is tight iff for every
  error and every window the values are caught in one compact set of `E` and the
  based modulus is small with high probability, uniformly over the set.
* `isTightMeasureSet_iff_forall_postcomp` — **the reduction to real-valued
  paths**: tightness of the laws on `D ι E` is tightness of all their images
  under `postcomp h` for `h` in a suitable class of real functions, together with
  compact containment. `continuous_postcomp` and `dist_postcomp_le` carry it.

**Stage (A) — the convergence theorem.**

* `tendsto_finiteDimensional_of_tendsto` — weak convergence implies convergence
  of the finite dimensional distributions along the times the limit law does not
  charge; `tendsto_integral_evalPi_of_tendsto` is the same read as convergence of
  integrals, and `tendstoInDistribution_evalPi`, `tendstoInDistribution_eval` the
  same for random variables.
* `tendsto_of_isTight_of_tendsto_finiteDimensional` — **the converse, and the
  point of the milestone**: a tight sequence whose finite dimensional
  distributions converge along a countable set of times converges weakly. With
  `tendstoInDistribution_of_isTight_of_tendsto_finiteDimensional` for random
  variables, and `tendstoInDistribution_eval_of_isTight_of_tendsto_finiteDimensional`
  for the marginal at a time that need not lie in that set.
* `exists_countable_dense_continuity` — the hypothesis bundle is inhabited: for a
  single law the times it does not charge contain a countable dense set.

**The subsequence argument is not to be repeated here.** The passage from "every
subsequence has a further subsequence converging to `ν`" to "the sequence
converges to `ν`" is `tendsto_of_subseq_tendsto`, and the passage from tightness
to a convergent subsequence is Prokhorov; both are Mathlib's, and
`tendsto_of_isSeparating_of_isTightMeasureSet` of **WeakConvergence** packages
them. The chain between the two stages is long — a modulus bound becomes a bound
on one law's oscillation, then on finitely many laws at once, then on a sequence,
then a *good time* outside the exceptional set, then a displacement estimate for
the finite dimensional integrals — but no step of it repeats that argument.

**The functionals a martingale problem tests.** Stated here because they are
statements about the path space and nothing else, and consumed by
**MartingaleProblems**:

* `mpTest f g t z = f (z t) - ∫_0^t g (z u) du`, a function of the **path alone**
  — no clock, no filtration — with `mpTest_sub` (linear in the pair it tests) and
  `integrableOn_mpTest_integrand`.
* `continuousAt_integral_comp` — **the compensator is continuous at every path,
  with no hypothesis on its jumps**; the asymmetry between the two summands of
  `mpTest` is the whole content of `continuousAt_mpTest`, which is continuous at
  every path not jumping **at the one time it evaluates**.
* `measure_setOf_forall_notMem_leftJumpSet_eq_one` — the passage from the *times*
  of stage (A) to the *paths*; `continuousAt_of_mem_evalFuns`; and the two halves
  of the hypothesis, `measure_setOf_continuousAt_mpTest_eq_one` and
  `…_mul_eq_one`.

**Acceptance examples.**

* **The invariance principle**, the manuscript's `ex:invariance` and what the
  milestone is for.
* **The excluded times are not a technicality**: `μ n = δ(1_{[1+1/n,∞)})` and
  `μ = δ(1_{[1,∞)})` converge weakly while the marginals at `1` do not converge.
* **Compact containment alone is not tightness**: the two jumps that cannot
  merge take values in a compact set and are not tight.
* **The converse of the reduction needs compact containment**: the constant paths
  at height `n` have every real image tight and are not tight.

## Milestone 9: the nonnegative index inside the real one

`extendNNReal` — a path on `ℝ≥0` extended to `ℝ` by its value at `0`. It is an
**isometry with closed image** (`isometry_extendNNReal`,
`isClosedEmbedding_extendNNReal`), which is what lets every statement proved over
`ℝ` be read over `ℝ≥0`, the index the processes of **MartingaleProblems** carry.

* `intDist_extendNNReal` and `distWith_extendNNReal` — the metric statements
  behind it, usable without the instance. `TimeChange.ofNNReal` extends a time
  change by the identity on the negative half line; `orderIso_zero_nnreal` says
  every time change of `ℝ≥0` fixes `0`, so `fixing 0` is the whole group there.
* `isTightMeasureSet_map_extendNNReal`, its converse
  `isTightMeasureSet_of_isTightMeasureSet_map_extendNNReal` — the image being
  closed — and the equivalence `isTightMeasureSet_map_extendNNReal_iff`. Likewise
  `tendsto_of_tendsto_map_extendNNReal`, and hence
  `tendsto_of_isTight_of_tendsto_finiteDimensional_nnreal` with its two
  random-variable forms.
* `IsCompactContained` — the predicate on a **family** `μ : γ → Measure D(ι, E)`:
  for every level and every window, one compact set of `E` catching all but the
  level of the mass of every member.
  `preimage_extendNNReal_setOf_forall_mem_exhaustion` says **the two windows are
  the same condition** and not merely comparable ones;
  `measurableSet_setOf_forall_mem_exhaustion` is what the crossing additionally
  needs, and is where it differs from everything else here;
  `isCompactContained_map_extendNNReal_iff` is the crossing, with the **same**
  compact set on either side.
* `isCompactContained_of_forall_exists_bound` — how a family that moves meets the
  condition, and the reduction a consumer uses.
* `isTightMeasureSet_iff_modulusBased_nnreal` — with compact containment in hand,
  tightness **is** the modulus condition, over the index the processes have.
* `isCompactContained_map_postcomp_of_measurableSet` and
  `isTightMeasureSet_map_postcomp_iff` — the two composed, an equivalence with
  **no hypothesis whatever**.
* `forall_mem_Ico_of_forall_mem_dense` and
  `mem_of_continuousWithinAt_of_forall_mem_dense` — the dense window lemma, whose
  **pointwise** form is the primitive one: to place *one* value in a closed set it
  is enough that the path be right continuous there and take values in the set on
  a dense subset.

## Milestone 10: Aldous' tightness criterion, and what it does not see

Aldous' criterion in the deterministic half, and its limits.

* `modulusBased_le_of_forall_gapped` — the deterministic core: an increasing,
  `δ`-sparse chain of times starting at the base point and reaching past the
  window, along which the path moves little, bounds the based modulus. With
  `subdivisionOsc_le_of_forall_cell` and `modulusBased_le_of_forall_cell` as the
  interface — name a based subdivision, bound its cells, and the modulus is
  bounded — and `mul_le_dist_of_gapped`, `card_le_of_gapped` for the counting: a
  `δ`-sparse chain of `N` steps spans at least `N δ`, so at most `L/δ` of them fit
  a span `L`.
* `modulusBased_extendNNReal_le_of_forall_gapped` — the same read over `ℝ≥0`.

**What the criterion does not see, and it is stated as a limit and not as an
omission.** The deterministic single step is tight, has `modulusBased = 0`, and
**fails** Aldous' condition. So the criterion is sufficient and not necessary,
and no statement here may be an equivalence. A jump process of
**MartingaleProblems** Milestone 4 under the Lebesgue clock is the instance on
which it does apply.
