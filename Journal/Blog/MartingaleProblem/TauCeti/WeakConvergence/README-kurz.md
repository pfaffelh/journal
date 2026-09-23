# Weak convergence: separating classes, the continuous mapping theorem, and Skorokhod representation

Weak convergence of measures on a metric space is well developed in Mathlib.
Five things are wanted beyond it, each used pervasively downstream: the two
classes of functions that determine a measure or its convergence, as predicates
and with the instances Mathlib does not prove; the continuous mapping theorem
for maps continuous only almost everywhere; the separability and completeness of
the space of laws itself, of which Mathlib has only the metrizability; the
Skorokhod representation theorem; and the link between uniform integrability and
convergence in distribution.

Throughout, `E` is a metric space, `Ω` a measurable space, and measures are
Borel probability measures. Weak convergence is `Filter.Tendsto μ l (𝓝 μ₀)` in
`MeasureTheory.ProbabilityMeasure E`; for random variables it is Mathlib's
`MeasureTheory.TendstoInDistribution`, whose variables live on a **family** of
probability spaces, one per index, with the limit on a further space of its own.

`Suggested.lean` prototypes the signatures. Most of them are discharged there,
against Mathlib `master`; that is evidence the milestones are reachable, not a
prescription of how. Where a proof route is named below it is because the
obvious route is **wrong**, not because it is the one taken.

## What Mathlib already has

Not to be rebuilt.

* **Separating.** `ext_of_forall_integral_eq_of_IsFiniteMeasure` and its
  `lintegral` companion (`Measure/HasOuterApproxClosed.lean`), bundled as
  `FiniteMeasure.ext_of_forall_integral_eq`: the bounded continuous functions
  separate finite Borel measures. For a `StarSubalgebra` of `E →ᵇ 𝕜` separating
  points, `ext_of_forall_mem_subalgebra_integral_eq_of_polish` and
  `…_of_pseudoEMetric_complete_countable` (`Measure/FiniteMeasureExt.lean:36`
  and `:72`). For characteristic functions, `Measure.ext_of_charFun`
  (`Measure/CharacteristicFunction/Basic.lean:257`) and `Measure.ext_of_charFunDual`
  (`:462`) — both routed through the subalgebra theorem, so the route this
  roadmap packages is the one Mathlib itself takes.
* **Convergence determining.** `FiniteMeasure.tendsto_iff_forall_integral_tendsto`
  and the `ProbabilityMeasure` companions, in both directions; Lévy's theorem as
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun`
  (`Measure/LevyConvergence.lean`); and the Stone–Weierstrass step **under a
  tightness hypothesis**, `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
  (`ibid.:154`).
* **Continuous mapping**, for maps continuous everywhere:
  `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`, and
  `TendstoInDistribution.continuous_comp`
  (`Function/ConvergenceInDistribution.lean:136`).
* **The random variable side**, the whole of
  `Function/ConvergenceInDistribution.lean`, including Slutsky
  (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `:313`) and its
  companions. These are Mathlib's and are **not** part of any milestone below.
* Portmanteau, the Lévy–Prokhorov metric, `IsTightMeasureSet`, Prokhorov, and
  `Function/UniformIntegrable.lean`.

What follows is what that leaves.

## Milestone 1: the two classes as predicates, and the missing instances

Mathlib states the results above as `ext_of_…` and `tendsto_…` theorems and has
no predicate for a class of functions. Downstream a predicate is needed, because
"`Φ` is separating" occurs as a **hypothesis** of the càdlàg modification theorem
of **MartingaleProblems**.

**Conventions.** `IsSeparating` takes `Γ : Set (E → 𝕂)` over `[RCLike 𝕂]`, not
over `ℝ`: its consumer tests martingale problems against an operator
`A : Set ((E → 𝕂) × (E → 𝕂))`, so the classes it calls separating are
`𝕂`-valued, and over `ℝ` alone that roadmap would restate the same proposition
under the same name. `RCLike` is the weakest bundle the definition parses under.
And `IsSeparating` quantifies over **probability** measures, not finite ones:
over finite measures `IsConvergenceDetermining.isSeparating` is false, `∅` being
convergence determining on a one-point space while not separating `δ` from `2δ`.

* `MeasureTheory.IsSeparating Γ` — two Borel probability measures integrating
  every member of `Γ` alike are equal. Monotone in `Γ`.
* `MeasureTheory.IsConvergenceDetermining Γ` for `Γ : Set (E → ℝ)` — pointwise
  convergence of the integrals along `Γ` implies weak convergence. Monotone, and
  `IsConvergenceDetermining.isSeparating`.
* `isSeparating_setOf_boundedContinuous` and
  `isConvergenceDetermining_setOf_boundedContinuous`, one line each from
  Mathlib, so that no later proof reaches past the predicate.
* `IsSeparating.of_subalgebra`, from
  `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`.
  Mathlib states it for a `StarSubalgebra 𝕜 (E →ᵇ 𝕜)`; what is needed is a plain
  `Subalgebra ℝ (E →ᵇ ℝ)`, so attach the trivial star structure — same
  `carrier`, `star_mem'` pointwise. Two traps: `TrivialStar (E →ᵇ ℝ)` is **not**
  an instance (only `TrivialStar ℝ` is), so `star_trivial` does not apply; and
  `Subalgebra.SeparatesPoints.rclike_to_real` runs the other way.

**The reason this milestone exists.** On a complete separable metric space a
subalgebra of `E →ᵇ ℝ` that **strongly** separates points is convergence
determining, with **no hypothesis on the family of measures**. Mathlib has this
step only under a tightness hypothesis. The passage is one theorem:

> `MeasureTheory.isTightMeasureSet_of_stronglySeparatesPoints` — strong
> separation together with converging integrals **forces** tightness, along any
> `NeBot` filter with `Filter.cofinite ≤ 𝓕`.

With `StronglySeparatesPoints.separatesPoints` this feeds Mathlib's theorem and
yields `MeasureTheory.isConvergenceDetermining_of_stronglySeparatesPoints`.

`StronglySeparatesPoints` is introduced here — Mathlib has `Set.SeparatesPoints`
and no strong form: for every `x` and `δ > 0` there are a finite `s ⊆ Γ` and
`ε > 0` with `∀ y, δ ≤ dist y x → ∃ f ∈ s, ε ≤ |f y - f x|`.

Three hypotheses are load-bearing and each has a witness that refutes its
removal:

* **Strong** separation, not mere separation. With
  `A = {f : ℝ →ᵇ ℝ | Tendsto f atTop (𝓝 (f 0))}`, `μ n = δ n`, `μ₀ = δ 0`: `A`
  is a subalgebra separating points, the integrals converge, and `δ n` does not
  converge weakly.
* `Filter.cofinite ≤ 𝓕`. With `𝓕 = pure 0` the hypothesis is a single equation
  that constrains no `μ n` for `n ≥ 1`. For a sequence it is free
  (`Nat.cofinite_eq_atTop`), so the `IsConvergenceDetermining` consumer pays
  nothing.
* `[MetricSpace E] [CompleteSpace E]`, not `[PolishSpace E]`. The proof runs in
  the **given** metric — `Metric.thickening` does — and `PolishSpace` says only
  that *some* compatible metric is complete. The statement holds under
  `PolishSpace` alone, over a proof that upgrades the metric first. `E = (0,1)`
  is the witness: Polish, its own metric incomplete, `(0,1/2]` closed and totally
  bounded and not compact.

The proof runs in four steps (Ethier–Kurtz, Theorem 3.4.5(b)), each a statement
of this milestone in its own right:

1. `tendsto_integral_comp_of_forall_tendsto_integral` — for a finite `κ` and
   `f : κ → (E →ᵇ ℝ)` in `A`, the pushforwards on `κ → ℝ` converge weakly.
   Polynomials in the `f i` are handled by
   `exists_mem_subalgebra_comp_of_mem_coordAlgebra`; Stone–Weierstrass on a
   compact box extends this to every bounded continuous function.
   `le_liminf_measure_preimage_of_isOpen` is the portmanteau consequence step 3
   consumes.
2. `StronglySeparatesPoints.exists_finite_cover` — the geometric core, free of
   measures: a compact `K` is covered by finitely many sets
   `G l = {y | max_{h ∈ s l} |h y - h (x l)| < ε l}` lying inside
   `Metric.thickening δ K`. **This is the only step that uses strong
   separation.**
3. `le_liminf_measure_thickening_of_stronglySeparatesPoints` — where 1 and 2
   meet: the finitely many functions the cover mentions, read as an index type,
   exhibit `⋃ G l` as a preimage of an open set.
4. `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le` —
   the relaxed tightness criterion (Ethier–Kurtz, Theorem 3.2.2), **missing from
   Mathlib**: on a complete pseudometric space, compact `K` with
   `μ ((thickening δ K)ᶜ) ≤ ε` for all `μ ∈ S` and all `δ` gives tightness. The
   witnessing set is `⋂ m, cthickening (u m) (K m)` for a null sequence `u m`. A
   single `δ` does **not** suffice: on `ℓ²` the closed unit ball is
   `cthickening 1 {0}` and is not compact.

The remaining statements of the milestone:

* `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` — on a
  metric space the bounded uniformly continuous functions of bounded support are
  convergence determining. **Separability is not a hypothesis**, though
  Ethier–Kurtz assume it. The route is
  `tendsto_iff_forall_lipschitz_integral_tendsto` plus the cutoff
  `ballCutoff x₀ R = min 1 (max 0 (R + 1 - dist · x₀))`, itself a member of the
  class, which is what sees escaping mass.
* `tendsto_integral_of_tendsto_integral_mul` — the truncation step, separated
  from the class it is applied to: for `f` bounded continuous and cutoffs
  `ψ m → 1` in `ν`-mean, convergence of `∫ ψ m` and `∫ f ψ m` gives convergence
  of `∫ f`. Only `[TopologicalSpace E] [OpensMeasurableSpace E]`.
* `isConvergenceDetermining_setOf_hasCompactSupport` — on a locally compact
  separable `E`, the continuous functions of compact support. **Uniform
  approximation is not the route and cannot be**: on an infinite discrete space
  of diameter `1` the constant `1` is uniformly continuous of bounded support
  and at uniform distance `1` from every compactly supported function. Local
  compactness enters exactly once, in Urysohn's lemma.
* `isSeparating_pi` — products over an **arbitrary** index: for `Γ i` separating
  with bounded measurable members, the functions `x ↦ ∏ i ∈ J, f i (x i)` are
  separating on `Π i, S i`. This is what makes finite dimensional distributions
  determine a law; for a process the index is the time set, so a finite index
  proves nothing. The route is **not** the monotone class theorem — those
  products are a multiplicative system only if each `Γ i` is closed under
  multiplication, which a separating class need not be. What carries it is
  `integral_indicator_mul_eq_of_isSeparating`: separation is a *linear*
  condition, so `Γ i` may be replaced by an arbitrary indicator inside a
  weighted integral. Iterating over `J` gives equality on the **boxes**
  `Set.pi ↑J B`, and `isPiSystem_boxes` with `generateFrom_boxes` and
  `ext_of_generate_finite` give equality of the measures.
  `isConvergenceDetermining_pi` is the same for countable `ι`, Polish `S i` and
  **continuous** members; each of the three extra hypotheses has one job —
  countability for `IsTightMeasureSet.pi`, Polishness for Prokhorov, continuity
  because identifying a subsequential limit sees bounded continuous functions
  and nothing else.
* `IsTightMeasureSet.pi` — tightness of a countable product from tightness of
  the one-coordinate marginals. Mathlib has the two-factor case
  (`Measure/Tight.lean:143`). `[Countable ι]` is a hypothesis of the
  **statement**: over `ι = [0,1]` a product of standard Gaussians has tight
  marginals and is not tight.
* `isTightMeasureSet_map_of_forall_exists_measure_dist_gt_le` — tightness under
  an approximation of the *map*, with
  `isTightMeasureSet_map_of_forall_exists_dist_le` as the uniform case. Not a
  variant of `IsTightMeasureSet.map`: there one compact set is transported,
  here it must be **built**, as `⋂ k, cthickening (1/(k+1)) (K k)`, because the
  thickening of a compact set is compact for no reason at all.
* `exists_mem_subalgebra_forall_dist_le_of_isCompact` — Stone–Weierstrass on a
  compact set, carried back to the **bounded** functions. Mathlib's version
  concludes in `C(E, ℝ)`; a consumer of a test class needs a member of `A`
  itself. This is the density a generator's domain actually has: `Cc^∞(ℝ)` is
  not dense in `ℝ →ᵇ ℝ` in the supremum norm.
* `isTightMeasureSet_of_tendsto` — a convergent sequence of laws on a Polish
  space is tight. Not circular: here convergence is the hypothesis.
* `tendsto_of_isSeparating_of_isTightMeasureSet` — separating class plus
  tightness gives convergence. The plain-class counterpart of Mathlib's
  `tendsto_of_tight_of_separatesPoints`, which asks for a `StarSubalgebra`
  separating *points* rather than a class separating *measures*.
* `IsSeparating.ae_eq_of_forall_condExp_eq` — the conditional form: if
  `P[f ∘ U | m] =ᵐ f ∘ V` for every `f` in a separating `Γ`, with `V`
  `m`-measurable, then `U =ᵐ V`. The last step of the absolute continuity
  theorem of **MartingaleProblems**, and the one place a separating class is
  used against a σ-algebra rather than a second measure. Declare the two
  σ-algebras as `{m mΩ : MeasurableSpace Ω}`, ambient **last**, as `condExp`
  does: instance search takes the last, so the other order silently weakens the
  statement. The normalisation `(P G)⁻¹ • P.restrict G` divides by zero on a
  null `G`; that branch is separate.
* **Missing, and wanted.** Stability under uniformly bounded pointwise limits,
  for both notions. And: on a Polish space there is a countable convergence
  determining set of bounded uniformly continuous functions, and a countable
  separating set.

**Acceptance examples.**

* **The trigonometric algebra on `ℝ`** separates points, so
  `IsSeparating.of_subalgebra` must reproduce `Measure.ext_of_charFun`. It does
  **not** strongly separate points, while being convergence determining by
  Lévy's theorem — so strong separation is sufficient and not necessary, and no
  point of this milestone may be stated as an equivalence.
* **`δ n` against `δ 0`** with the `atTop`-limit subalgebra: every hypothesis of
  `isTightMeasureSet_of_stronglySeparatesPoints` except strong separation, and a
  false conclusion. This also shows the shortcut through
  `isTightMeasureSet_of_isCompact_closure` is circular — compact closure is
  available only once weak convergence is known.
* **`Γ = ∅` on `PUnit`** — both predicates hold, and restating `IsSeparating`
  over finite measures breaks exactly here.
* **Products over `ι = [0,∞)`** — two laws with the same finite dimensional
  distributions are equal. A formulation restricted to a finite index proves
  nothing here.
* **A countable Gaussian product** must produce a compact set whose coordinate
  windows **grow**: one compact set for all coordinates gives `Σ ε = ∞`.
* **Escaping mass**, `μ n = δ n` against the bounded-support class: the
  integrals converge to `0` and no probability measure has all those integrals
  `0`, so the hypothesis is never met. A version reading "the integrals
  converge, hence the sequence converges" — vague convergence — would be false.

### Provenance

Choices recorded so that a reviewer who wonders need not ask, and an implementer
who does not wonder need not read.

* **Why the `PseudoEMetricSpace` bundle for `IsSeparating.of_subalgebra` and not
  the `PolishSpace` form** (`FiniteMeasureExt.lean:72`): the latter is the former
  preceded by `upgradeIsCompletelyMetrizable`, and the separation of `E` never
  enters — only the separation of the algebra — so the metric may be a
  pseudometric.
* **Why `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`
  carries `[PseudoMetricSpace E] [CompleteSpace E]` and nothing else**: the proof
  measures no set it has not been handed, using only `measure_mono` and
  `measure_iUnion_le`, so neither `BorelSpace` nor separability occurs.
* **Why the members of `isSeparating_pi` are required bounded and measurable**:
  `IsSeparating` constrains only the map `μ ↦ (∫ f ∂μ)`, a non-integrable `f`
  contributing `0` on both sides; the proof needs each `f` as a *weight*.
* **Why no signed measures appear in `isSeparating_pi`**: the Jordan pair of
  `W • (μ - ν)` is written as two positive measures and `IsSeparating` applied to
  their normalisations, the constants agreeing by the previous induction step.

## Milestone 2: the continuous mapping theorem for almost everywhere continuous maps

Mathlib has the theorem for maps continuous everywhere, on measures and on
random variables. What is wanted is the single step to continuity off a null set
of the **limit**. Measurability of the continuity set is Mathlib's:
`measurableSet_of_continuousAt` (`Constructions/BorelSpace/Basic.lean:252`).

* `tendsto_of_measure_setOf_not_continuousAt_eq_zero`, and the form
  `tendsto_of_measure_setOf_continuousAt_eq_one` obtained from it by
  `prob_compl_eq_zero_iff` — for `h` Borel, `μ n → μ` weakly and the
  discontinuity set `μ`-null, the image measures converge. Mathlib's theorem is
  the case where that set is empty. The image measures enter as **data** with
  their defining equations, so the statement names no image *construction* and
  elaborates against versions whose `ProbabilityMeasure.map` differ in
  signature.

  Carry the hypothesis as `ν {x | ¬ ContinuousAt h x} = 0` rather than
  `= 1` on the continuity set: for a set not known to be measurable the two
  differ, and this is what keeps a metric off the **target**. The proof is
  portmanteau on both sides, through
  `closure (h ⁻¹' F) ⊆ h ⁻¹' F ∪ {x | ¬ ContinuousAt h x}`.
* `TendstoInDistribution.continuousAt_comp` — the same on Mathlib's structure.
  **State the continuity hypothesis on the sample space**,
  `μ' {ω | ContinuousAt h (Z ω)} = 1`, not on `E`: the two are the same
  statement, and the first is the form a user of the structure has.
  `Measurable h` becomes a hypothesis — it no longer follows from continuity —
  and that is the one thing the generalisation costs.

**The index is an arbitrary countably generated filter**, not `ℕ` with `atTop`:
that is the index of the portmanteau implication underneath, so restricting to a
sequence would be a hypothesis the proof does not read.

**Acceptance examples.**

* **The Heaviside function against an atom**: `h = 1_{[0,∞)}`, `μ n = δ(-1/n)`,
  `μ = δ 0`. The continuity set is `{0}ᶜ`, of `μ`-measure `0`; the conclusion
  fails. The smallest instance the hypothesis is there for.
* **Continuous `h`** must reproduce Mathlib's theorem with no further
  hypothesis — the collapse test.
* **Evaluation on Skorokhod space**, the downstream use: `π 1` is discontinuous
  at every path jumping at `1`. For a limit law with `P {ω | ω 1 = ω 1⁻} = 1`
  the theorem applies; for `P = δ ω` with such an `ω` it does not.
* **Differing sample spaces**: `Ω n = ({0,…,n}, uniform)`, `X n k = k/n`. The
  statement cannot be phrased on one fixed probability space.

## Milestone 3: the space of laws, and the Skorokhod representation theorem

Let `E` be a separable metric space. Mathlib metrizes the topology of
convergence in distribution and stops there: neither
`SeparableSpace (ProbabilityMeasure E)` nor complete metrizability of it occurs
anywhere. They come first, because the representation below and every relative
compactness argument downstream live in this space.

**Convention, fixed by Mathlib's design.** `LevyProkhorov` is a one-field
structure wrapping a measure, and the distance instances sit on it;
`ProbabilityMeasure E` carries the topology and no uniformity, so
`CompleteSpace (ProbabilityMeasure E)` is not a statement one can write down. So:
a **uniform** statement about the space of laws is made on
`LevyProkhorov (ProbabilityMeasure E)`, a **topological** one on
`ProbabilityMeasure E`, and `probabilityMeasureHomeomorph` carries the second
kind across. What crosses back is `IsCompletelyMetrizableSpace`, which is what
`PolishSpace` is defined from.

**Convention.** Statements wanting `E` Polish carry `[TopologicalSpace E]
[PolishSpace E] [BorelSpace E]` and **no metric**. That is necessity, not
economy: with a `[MetricSpace E]` in the signature the complete metric supplied
by `upgradeIsCompletelyMetrizable` is a second, competing instance, and the
`CompleteSpace E` read off the upgrade is stated for the upgraded uniformity
while the goal wants the given one.

### The space of laws

* `separableSpace_probabilityMeasure`, and its companion on the synonym. The
  countable dense family is the finitely supported measures with rational masses
  at points of a countable dense sequence. Completeness of `E` is nowhere used.
  Four statements carry it: `levyProkhorovEDist_sum_dirac_le` (geometric),
  `levyProkhorovEDist_sum_dirac_weights_le` (arithmetic),
  `exists_finite_partition_ball_of_denseRange` (the partition, and the one place
  `SeparableSpace E` is consumed) and `exists_nat_weights`.

  Two requirements on those two. The partition must return its representatives
  as **indices**, not as points — that is what makes the family countable, and
  why Mathlib's `SeparableSpace.exists_measurable_partition_diam_le` is not
  usable, being countably indexed with the representatives forgotten. And
  `exists_nat_weights` should **normalise** (`m i / ∑ j, m j`) rather than round
  down and let one index absorb the slack: that avoids truncated subtraction in
  `ℝ≥0∞` and a case distinction; the `+ 1` in `m i = ⌊c i · N⌋₊ + 1` keeps the
  denominator positive.

  The empty `E` is a separate line, not a hypothesis: `exists_dense_seq` wants
  `[Nonempty E]`, and on an empty `E` there is no probability measure at all.
* `secondCountableTopology_probabilityMeasure` — the same, read on the synonym
  where there is a uniformity to argue with, and carried back.
* `isTightMeasureSet_of_forall_exists_finite_iUnion_ball` — uniform total
  boundedness in measure gives tightness, four lines from Milestone 1's relaxed
  criterion. This is the skeleton inlined in Mathlib's
  `isTightMeasureSet_of_isCompact_closure` (`Measure/Prokhorov.lean:634`);
  factoring it out is what the completeness below needs, a Cauchy sequence having
  no compact closure to start from.
* `isTightMeasureSet_of_cauchySeq` (and its spelled-out form
  `isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt`) — a Cauchy sequence
  of laws is tight. This is where completeness of `E` is spent, twice: through
  Ulam's theorem for the finite head and through the previous item for the
  conclusion.
* `completeSpace_levyProkhorov_probabilityMeasure`,
  `isCompletelyMetrizableSpace_probabilityMeasure`, and
  `polishSpace_probabilityMeasure`: for `E` Polish, `ProbabilityMeasure E` is
  Polish. Three steps — Cauchy implies tight, Prokhorov gives a convergent
  subsequence, a Cauchy sequence with a convergent subsequence converges —
  transported along the homeomorphism.

### The Skorokhod representation theorem

`exists_ae_tendsto_of_tendsto`: if `μ n → μ` weakly on a separable `E`, there is
a probability space carrying random variables `X n`, `X` with laws `μ n`, `μ`
and `X n → X` almost surely. Separability is the only hypothesis.

**The space lives in the universe of `E`**, and asking for `Ω : Type` is a
different and false statement: the common space is `(E × ℝ) × (ℕ × ℕ → E)`, and
nothing brings it down to `Type 0`. The statement carries its own universe;
`Type _` is not a fix, auto-binding a second universally quantified universe.

**It is built, not glued, and that is a hypothesis question and not a taste
question.** Gluing the one-stage couplings along their common marginal is
available in Mathlib — `Measure.condKernel` for the disintegration,
`ProbabilityTheory.Kernel.traj` (Ionescu–Tulcea) for the countable product — but
`condKernel` requires `[StandardBorelSpace]` on the fibre, and separable metric
does **not** imply standard Borel (a non-Borel `A ⊆ ℝ` with the subspace
topology is the witness, by Lusin–Souslin). So the construction puts every stage
on one space at once: the first factor carries the limit variable together with
**one** uniform variable shared by every stage, the second an independent draw
from each conditional law. That is Ethier–Kurtz's Lemma 3.1.3 with `N = ∞`, and
it is why the theorem holds under separability alone.

The pieces, each wanted in its own right:

* `exists_measurable_partition_diam_le_null_frontier` — a countable measurable
  partition into sets of diameter `≤ ε` with `μ`-null frontiers. Mathlib's
  partition is built from balls of one fixed radius and says nothing about
  frontiers; the radii must be chosen **one per centre** from the open interval
  `(ε/4, ε/2)`, because `exists_null_frontier_thickening` avoids only countably
  many charged radii and so produces a radius in an interval, not a prescribed
  one. Supported by `frontier_biInter_range_subset` and
  `frontier_disjointed_subset` (Mathlib has only the two-set case, and states it
  sharply, so the induction must discard the intersections by hand).
  `exists_finite_partition_diam_le_null_frontier` is the finite, positive-mass
  form the stage consumes; the remainder is taken as the **complement** of the
  kept union, so its frontier is null for free.
* `tendsto_tsum_posPart_sub_of_tendsto_measure` and
  `tendsto_tsum_abs_sub_of_tendsto_measure` — the Scheffé step: piecewise
  convergence of the masses gives convergence of the sum over **all** pieces at
  once. The first is Tannery's theorem with `ν (A i)` dominating, which is why
  the *positive part* and not the absolute value is the quantity with an `n`-free
  bound; the second follows through `|d| = 2 max d 0 - d`. This does not follow
  from piecewise convergence by any finite argument.
* `exists_coupling_tsum_offDiag_le` — two probability vectors are the marginals
  of a `π` whose off-diagonal mass is at most `∑' i, (p i - q i)` in `ℝ≥0∞`. The
  coupling is `min (p i) (q i)` on the diagonal plus the two residues coupled
  independently. Writing the diagonal as a **summand** rather than an `if`-branch
  is what avoids subtraction surviving a `tsum`; the degenerate `D = 0` then
  needs no separate treatment, `0/0` never being evaluated.
* `exists_coupling_of_partition` and `exists_coupling_of_tendsto` — the one-stage
  coupling, on `E × E` itself: the joint law *is* a measure on `E × E`, the
  variables are `Prod.fst` and `Prod.snd`. The pieces must be **bounded**, not
  merely of small diameter: `Metric.diam` of an unbounded set is `0` by
  convention, so `A 0 = univ` would pass a diameter test and fail everything else.
* `exists_measurable_map_restrict_volume_eq_sum_smul_dirac` — a probability
  vector and a sequence of points are realised by a measurable map out of
  `(0,1]`. The predicate is `y ≤ s (i+1) ∨ 1 ≤ y`, and the second disjunct is not
  a convenience: without it `Nat.find` cannot be formed at `y = 1` whenever the
  partial sums never reach `1`.
* `condLaw` — the conditional law made **total**, falling back to `μ` where
  `μ A = 0`. Mathlib's `ProbabilityTheory.cond` is the *zero* measure there,
  which is right for conditioning and wrong for a coupling: a zero factor in the
  product destroys the marginals. The fallback is never observed, because
  `measure_mul_condLaw_apply` holds on a null piece too.
* `map_eval_prod_infinitePi` — **the randomisation step**: on a product of a
  space carrying a measurable index with `Measure.infinitePi m`, the map "look up
  the coordinate the index names" has the mixture law `∑ᵢ P{ι = i} · m i`. This
  is what keeps the milestone at `SeparableSpace E`: realising the position
  inside a piece as a **function** of one uniform variable is the Borel
  isomorphism theorem and needs `E` Polish; realising it as a **coordinate**
  needs no topology at all.
* `exists_measurable_partitionIndex` and
  `exists_measurable_index_of_stochastic_matrix`, with the variant
  `…_diag` that puts the diagonal branch on a **named** interval. The index map's
  fibres must be **exactly** the pieces, not merely contained in them, or the
  mass bookkeeping `P{j = i} = μ (A i)` breaks. The diagonal variant is what
  converts a *number* into an *inclusion*: with the diagonal at a known place,
  "the two indices disagree" is an event of the uniform variable alone — and
  events of one variable are what nest.
* `exists_measurable_pair_of_partition` and, for every stage at once,
  `stagesMeasure` with `exists_measurable_pair_of_partition_subset`. The point of
  the second is that all stages read their limit variable off the **same**
  coordinate: a glued family of laws on `E × E` cannot give that, the almost sure
  statement being about one limit variable and not one per stage. The per-stage
  hypothesis is a **row defect** — `μ n` gives each piece at least `1 - t n`
  times what `ν` gives it — and the conclusion is an **inclusion**, not an
  estimate.
* `ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` — the final step, from a
  nested bad event.

  **Borel–Cantelli over the stages is not available**, and that is a statement
  about the theorem and not about the proof: the one-stage bound may tend to `0`
  arbitrarily slowly. With `ν = δ 0` and
  `μ n = (1 - 1/log n) δ 0 + (1/log n) δ 1` the bound is at least `1/log n` at
  every level and `∑ 1/log n = ∞`, while the theorem still holds — with `U`
  uniform and `X n = 1` exactly on `{U ≤ 1/log n}` the bad events are **nested**.
  Almost sure convergence comes from the dependence between the stages, not from
  the per-stage bounds. This is why the tail halves are bounded by two different
  means: the partition remainders are summable (`ν (A^{(m)} 0) ≤ 2⁻ᵐ`), while the
  uniform-variable halves are **not summed** but nest into `{ξ > 1 - 1/K}` of
  measure `1/K`. Summing them would give `∑ 1/m = ∞` and prove nothing.

The converse is Mathlib's and is not to be rebuilt:
`tendstoInDistribution_of_ae_tendsto`, already along a countably generated
filter.

**Acceptance examples.**

* **`E = ℚ`** — separable, so `ProbabilityMeasure ℚ` is separable; not complete,
  and `δ (q n)` for `q n → √2` alternating is Cauchy without a limit, since
  `{x : ℚ | x < √2}` is clopen. The split of this milestone into a separable part
  and a complete part is not cosmetic.
* **An uncountable discrete `E`** — complete, not separable, and
  `{δ x}` is uncountable and pairwise at distance `1`. The instance on which
  `separableSpace_probabilityMeasure` without its hypothesis is false.
* **Skorokhod does not upgrade a given sequence.** Independent fair coins have
  `μ n = μ` for every `n` and converge almost surely nowhere; the theorem must
  build **new** variables. This refutes the standard misreading, "if `μ n → μ`
  then any realisation converges a.s.".
* **The frontier of a ball can be charged**: `μ = δ 0`, `ε = 1`, and the ball of
  radius `1` about `1` has `0` on its frontier. The fixed-radius shortcut fails
  here, which is what forces the per-centre choice of radius.
* **A piece that is not bounded**: `A 0 = univ`, `μ = δ 0`, `ν = δ 100`. The mass
  vectors agree, `Metric.diam (A 0) = 0 ≤ ε` by convention, and every coupling
  puts all its mass on `dist > 1`. So boundedness of the pieces is a hypothesis.
* **Separable and not standard Borel** — a non-Borel `A ⊆ ℝ` with the subspace
  topology. Every ingredient of the product construction is available over it;
  `Measure.condKernel` is not. This is the instance on which the two candidate
  constructions differ.
* **A `μ`-null piece**, where `condLaw` falls back and is never observed:
  `E = {0,1}`, `μ = δ 0`, `ν = (δ 0 + δ 1)/2`. The bound `1/2` is attained
  exactly. A proof arguing "the indices agree, hence the distance is at most the
  diameter" without first discarding the `μ`-null pieces would be wrong here.

## Milestone 4: uniform integrability against convergence in distribution

Mathlib's uniform integrability theory is about a **single** measure; convergence
in distribution is about laws whose variables live on a family of spaces. The
link is absent, and the convergence theorem of **MartingaleProblems** consumes it
three times. Every statement here takes `TendstoInDistribution X l Z μ μ'` as its
hypothesis, so the differing spaces are Mathlib's and not this roadmap's.

* `tendsto_integral_of_tendstoInDistribution_of_uniformIntegrable` — with `X`
  uniformly integrable, `Z` is integrable and the means converge; and the form
  for laws, `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`.

  The route is **truncation, not the Skorokhod representation**: the approximant
  is the identity clamped to `[-N, N]` as a bounded continuous function, so one
  and the same expression is what the hypothesis drives to zero and what bounds
  the displacement of the mean. Three ε/3. The step the hypothesis does not give
  is the middle one — the limit law is no member of the family, and nothing in
  weak convergence transports the integral of an unbounded function; what does is
  the portmanteau inequality for a nonnegative continuous function.
* `IsUniformlyIntegrableLaws`, the truncation criterion for a family on varying
  spaces: `lim_N sup_n 𝔼[|X n| - |X n| ⊓ N] = 0`.

  **The truncated expectation is a lower integral and not a Bochner integral**,
  and that is the whole point. As a Bochner integral the criterion is *satisfied
  by exactly the families it exists to exclude*: a family with infinite first
  moment makes the integrand non-integrable at every `N`, `integral_undef`
  returns the junk value `0`, and the supremum is `0`. The Cauchy law is the
  witness: it satisfies the Bochner form of the criterion and has no first
  moment, so the convergence theorem above fails for it. In `ℝ≥0∞` there is no
  junk value, and the criterion then *implies* integrability
  rather than presupposing it (`integrable_id_of_lintegral_truncTail_lt_top`).

  The lesson generalises past this milestone: **a criterion phrased as a Bochner
  integral of a nonnegative integrand is silently vacuous wherever that integrand
  fails to be integrable — which is precisely where such criteria are applied.**
* The de la Vallée-Poussin form, and the stability lemmas: domination, uniform
  boundedness, product with a uniformly bounded family, finite union.

**Acceptance examples.**

* **The escaping spike**, `X n = (n+1) 1_{[0,1/(n+1)]}` on `([0,1], Lebesgue)`:
  converges in measure to `0`, every mean is `1`. The theorem must not apply, and
  the truncation criterion must say why — its supremum is `1` for every `N`.
* **The same spike, tamed**: height `√(n+1)` instead. The criterion is computable
  in closed form and gives `⨆ n ≤ 1/(4N) → 0`, so the means converge. The two
  spikes differ only in the height, which makes the pair a test of the criterion
  rather than of the example.
* **A family on varying spaces**: `Ω n = ({0,…,n}, uniform)`, `X n k = k/n`.
  Mathlib's `UniformIntegrable` does not typecheck on it, its functions living on
  different spaces. This is what forces the milestone's own predicate.
* **Finite union, not countable**: `{X n} ∪ {five spikes}` is uniformly
  integrable while the full spike family is not.

## Milestone 5: the functional monotone class theorem

Mathlib has Dynkin's π–λ theorem for **sets** (`MeasurableSpace.induction_on_inter`,
`MeasureTheory/PiSystem.lean`; the namespace is `MeasurableSpace`, not
`MeasureTheory`). The functional form is absent; `docs/1000.yaml` carries the
monotone class theorem as `Q242045` with no declaration. It is the tool the
products of Milestone 1 rest on, and the determining sets of **MartingaleProblems**
are built with it. `Ω` is a bare measurable space; no topology.

* `IsMulSystem K` — `∀ f ∈ K, ∀ g ∈ K, f * g ∈ K`, the multiplicative counterpart
  of `IsPiSystem`; `indicatorFuns 𝒞`; and `isMulSystem_indicator_of_isPiSystem`.
  The `insert ∅` is **necessary** — two disjoint sets have product indicator `0`,
  the indicator of `∅` and of no other set, and a π-system need not contain `∅`
  — and free, by `generateFrom_insert_empty`.
* `generateFromFuns K = ⨆ f ∈ K, MeasurableSpace.comap f (borel ℝ)`, with
  `generateFromFuns_le_iff`, monotonicity, and `generateFromFuns_indicatorFuns`:
  `generateFromFuns (indicatorFuns (insert ∅ 𝒞)) = generateFrom 𝒞`, which is
  where the functional form meets the set form. And `generateFromFuns_comp`:
  substitution commutes with generation, an **equality**, needing nothing of `X`
  — not even measurability, both sides being σ-algebras on the source. That is
  the step by which a determining class on a path space is transported to the
  sample space carrying the process.
* `ioiCells K`, the finite intersections of `f ⁻¹' Ioi c`, indexed by a **list**
  of pairs — a `Finset` of functions with one level each would not do, two
  members being allowed to name the same `f`. With `isPiSystem_ioiCells` and
  `generateFromFuns_eq_generateFrom_ioiCells`. The single preimages do not form a
  π-system, which is why the finite intersections are built into the family.
* `induction_on_mulSystem` — **the theorem**: a property holding on a
  multiplicative system of bounded functions and on the constants, preserved by
  addition, scalar multiplication and bounded monotone limits, holds of every
  bounded `generateFromFuns K`-measurable function. State it `@[elab_as_elim]`,
  as `induction_on_inter` is. Four steps, each a declaration of its own:
  `of_tendstoUniformly_of_mono_lim`; `of_continuous_comp_of_isMulSystem` (via
  Stone–Weierstrass on a compact box); `of_indicator_mem_ioiCells` and
  `of_indicator_of_measurable`; `of_simpleFunc` and `of_nonneg_of_measurable`.

  Two design points that are not free. The **span** `Submodule.span ℝ (insert 1 K)`
  is the right object and the property `P` is not: `P` is linear and closed under
  monotone limits and is **not** closed under multiplication, so multiplicativity
  has to be kept inside `K` and released only through the span. And the ramps of
  step three must be taken **jointly**, as one continuous function of the `n`
  values, for the same reason — one factor at a time would need `P` multiplicative.
  The approximation in step four detours through `ℝ≥0∞` (`SimpleFunc.eapprox`)
  because that is what makes it *increasing*, which `SimpleFunc.approxOn` does not.
* `ext_of_forall_integral_eq_of_isMulSystem` — two finite measures agreeing on
  `∫ f` for `f ∈ K` **and on the total mass** agree on `generateFromFuns K`. The
  total mass is an independent hypothesis: a multiplicative system need not
  contain the constants, and `K = {0}` with `δ x` against `2 δ x` is the witness.
* `integral_mul_eq_zero_of_isMulSystem` and the conditional form
  `condExp_eq_of_forall_integral_mul_eq` — the shape in which the martingale
  property is verified: `𝔼[X · Z] = 𝔼[Y · Z]` for `Z` in the system gives
  equality of the conditional expectations.
* `integral_mul_ofReal_eq_zero_of_isMulSystem` — the same for a `𝕂`-valued `g`
  against a **real** system `K`, by taking real and imaginary parts. This is a
  different and smaller statement than the `RCLike` variants, where `K` itself is
  `𝕂`-valued and multiplicativity must survive the passage to the real
  subalgebra; and it is the shape the consumer needs, the test functions of
  `MartingaleProblems` being real while the integrand is `𝕂`-valued.
* `generateFromFuns_setOf_continuous_bounded` — on a pseudometrizable space the
  bounded continuous functions generate the Borel σ-algebra. This is what turns a
  criterion tested against bounded **continuous** functions into one tested
  against every bounded Borel function, and it is the only place the topology of
  the state space enters this milestone. Metrizability is used and all that is
  used.
* **`induction_on_mulSystem` has no `RCLike` variant.** Its monotone limit clause
  needs the order on `ℝ`.

**Acceptance examples.**

* **Dynkin is the special case**: `K = indicatorFuns (insert ∅ 𝒞)` must return
  `induction_on_inter`. A version that failed to would be indexing the wrong
  σ-algebra.
* **`𝒞 = {{0},{1}}` on `ℕ`**: the `insert ∅` is not decoration.
* **`K = {0}`**: the total mass hypothesis is not decoration.
* **Laplace transforms on `[0,∞)`**: two finite measures with the same Laplace
  transform are equal — the form `prop:hawkesduality` of the manuscript uses, and
  where the total mass comes free at `t = 0`.
* **The martingale property against a determining class**: products of bounded
  continuous functions of coordinates at times `≤ s` form a multiplicative system
  generating the filtration, so the martingale property is verified against
  countably many test products rather than against the whole σ-algebra.

## Milestone 6: the space of measurable paths modulo null sets, and its Polish structure

Let `α` be a measurable space, `μ` finite on it, `E` a metric space. Mathlib has
the quotient (`AEEqFun`, `α →ₘ[μ] E`) and the convergence (`TendstoInMeasure`)
and does not connect them: the quotient carries no metric, the convergence no
topology. The metric that joins the two is

```
distInMeasure f g = ∫ a, min 1 (dist (f a) (g a)) ∂μ ,
```

which for finite `μ` metrizes `TendstoInMeasure μ`, is complete when `E` is, and
separable when `E` and `μ` are. That is Kurtz (1991), *Random time changes and
convergence in distribution under the Meyer–Zheng conditions*, Ann. Probab. **19**,
1010–1034, Section 4, with `α = [0,∞)` and `μ(dt) = e^{-t} dt`; his `M_E[0,∞)`
is the Polish space Step 1 of the manuscript's `thm:MZconv` runs in — which is
why the Skorokhod representation of Milestone 3 is needed for **Polish** spaces
only.

**Convention.** The metric goes directly on `α →ₘ[μ] E` and not on a type
synonym: Mathlib's competing metrics of a.e.-classes live on `Lp`, a different
type, so nothing is shadowed. The truncation `min 1 (dist · ·)` is what makes the
integral finite without an integrability hypothesis — the same device as
`ENNReal.ofReal` in the Lévy–Prokhorov distance.

* `AEEqFun.distInMeasure` with the `Dist` instance, well defined on classes
  because the integrand changes on a null set only. The integrand is measurable
  because the coercion of an a.e.-class is **strongly** measurable and not merely
  a.e. so, which is what makes the sets `{a | ε ≤ dist (f a) (g a)}` honestly
  measurable. `SecondCountableTopology E` is **not** a hypothesis of any of this.
* `distInMeasure_triangle` and the `PseudoMetricSpace` instance — pointwise,
  `min 1` being subadditive on nonnegative reals, so nothing of `μ` beyond
  finiteness is used.
* `distInMeasure_eq_zero_iff` and `AEEqFun.metricSpace` for `[MetricSpace E]`.
  This is the one place where `E` must be a metric and not a pseudometric space,
  and it is why the quotient is taken.
* `AEEqFun.tendsto_iff_tendstoInMeasure`, and with the instance installed
  `tendsto_nhds_iff_tendstoInMeasure`, which states the point of contact with the
  manuscript's `fact:pseudopath`(i) in its proper form — convergence in the
  *topology*, not of a sequence of numbers. Markov's inequality must be applied
  at the level `min 1 ε`: the truncation has to be carried into the level too, or
  the inclusion of sets is the wrong way round. `distInMeasure_le_add` is the
  reusable half.
* `exists_tendsto_distInMeasure_of_cauchy` and the `CompleteSpace` instance, for
  `[CompleteSpace E]`. Kurtz (4.2)–(4.4): a subsequence with summable distances,
  `lintegral_tsum` to move the sum inside, and the truncation is undone by
  **summability itself**, the terms being eventually below `1`. Off the good set
  the limit is put equal to `x 0` and **not** to a fixed `x₀ : E`: `E` need not be
  nonempty. Mathlib has no completeness of convergence in measure to appeal to.
* `exists_countable_dense_distInMeasure` and `AEEqFun.separableSpace`, for
  `[IsSeparable μ]` and `[SeparableSpace E]`. Mathlib's `Lp.SecondCountableTopology`
  is the same statement for the `Lᵖ` metrics and fixes the right hypotheses, but
  does not transfer: its proof runs through `Lp.induction`, whose additivity step
  has no counterpart here — `distInMeasure` is not a norm and `E` is not a normed
  group.

  The approximating family cannot be a family of **sums** of indicators, the
  obvious candidate: `E` is a bare metric space and carries no addition, so
  those terms do not typecheck. It is `AEEqFun.stepFun`, the step function
  attached to a **list** of index pairs, earlier entries having priority. A list is what makes the index type countable
  with no bookkeeping (`Countable (List (ℕ × ℕ))` is instance search) and what
  replaces the sum by a case distinction. `exists_mem_stepFun` — whichever branch
  fires, the value is named by *some* entry whose set contains the argument — is
  what lets the covering sets **overlap**, so no disjointification is needed.
  `stepClass` is named as a **definition** and not described inside a proof, which
  is what makes its countability one line.

  The empty `E` is a separate line: on it `α →ₘ[μ] E` is a subsingleton.
* `AEEqFun.secondCountableTopology` and `AEEqFun.polishSpace`. One line each
  behind the separability: unlike `ProbabilityMeasure E` above, the metric lives
  on the type itself, so no `IsCompletelyMetrizableSpace` statement of its own is
  needed.
* `measurableSet_of_measurable_injective` — for `γ` measurable and injective with
  `γ '' S` measurable, `S` is measurable. It carries **no topology**, and it is
  the whole of the argument that puts the càdlàg paths inside this space as a
  Borel set: no Lusin–Souslin, no completeness, no separability.
  `measurableSet_of_continuous_injective` is the topological corollary.
