# Abstract martingale problems

A martingale problem specifies a process by requiring a family of functionals of
it to be martingales. The classical form fixes an operator `A` on functions on a
state space `E` and asks that `f (X t) - ∫ s in Ioc 0 t, (A f) (X s)` be a
martingale for every `f` in the domain of `A`. The theory of uniqueness, of the
Markov property, of path regularity and of convergence does not use the operator
and does not use the state space; it uses only the family of martingales. This
roadmap develops the abstract form first and obtains the classical statements as
instances.

The worked instance — jump processes, Hawkes processes and the analysis they
need — is the separate **JumpProcesses** roadmap, which depends on this one.

This roadmap depends on **WeakConvergence**, **SkorokhodSpace** and, in one
milestone, **KolmogorovExtension**.

`Suggested.lean` prototypes the signatures. Most of them are discharged there,
against Mathlib `master`; that is evidence the milestones are reachable, not a
prescription of how. Where a proof route is named below it is because the
obvious route is **wrong**, not because it is the one taken.

## What Mathlib already has

Not to be rebuilt.

* `MeasureTheory.Filtration`, `Adapted`, `StronglyAdapted`, `IsStronglyProgressive`
  and `IsStoppingTime` in `Probability/Process/`. `ProgMeasurable` is a
  deprecated alias of `IsStronglyProgressive`.
* `Martingale`, `Supermartingale`, `Submartingale`, stated for `[Preorder ι]`, so
  a continuous time index needs no new definition, and for values in a real
  Banach space, so complex-valued martingales need no separate development.
* **But the theorems about them are for a discrete index.** Optional stopping,
  optional sampling, the upcrossing theory and the convergence theorems all fix
  `Filtration ℕ`. Milestone 8 states what that leaves. What is *not* tied to `ℕ`
  is `tendsto_of_no_upcrossings`.
* **Localization is already there**: `Probability/Process/LocalProperty.lean`
  with `IsPreLocalizingSequence` and `Locally`.
* `Probability/Process/FiniteDimensionalLaws.lean` and
  `Probability/Process/Kolmogorov.lean` (namespace `ProbabilityTheory`),
  conditional expectation, `UniformIntegrable`, Polish spaces, weak convergence
  and Prokhorov.

## Conventions fixed once

* The index `ι` is a **preorder**, matching `MeasureTheory.Filtration`.
  Individual milestones add a linear order, a lattice or a countable dense subset
  and say so.
* The scalar field of the test processes is `𝕂` with `[RCLike 𝕂]`. Test
  processes are `𝕂`-valued; the sets that test them are real-valued, because
  testing against a complex weight says no more.
* **An operator is a relation**, `A : Set ((E → 𝕂) × (E → 𝕂))`, not a
  function. This is needed for domains on which the operator is multivalued and
  costs nothing elsewhere.
* Compensation carries a convention parameter `c : Clock.Conv` selecting the
  **optional** or the **predictable** interval. It is a parameter of the
  definition, not a global choice.
* **The compensating interval is a difference of down-sets, not `Set.Ico`.**
  Mathlib's `Set.Ico` is defined for `[Preorder α]` but is the wrong set on a
  preorder that is not linear: what the additivity of the compensator needs is
  only that `t ↦ Set.Iio t` be monotone.

## Milestone 1: the clock

```
structure Clock (ι : Type*) [Preorder ι] where
  measurableSpace : MeasurableSpace ι
  q : Measure ι
  measurableSet_Iic : ∀ t, MeasurableSet (Set.Iic t)
  measurableSet_Iio : ∀ t, MeasurableSet (Set.Iio t)
  measure_Iic_ne_top : ∀ t, q (Set.Iic t) ≠ ⊤
```

with `Clock.Ioc q s t = Set.Iic t \ Set.Iic s`, `Clock.Ico q s t = Set.Iio t \ Set.Iio s`
and `Clock.Conv` selecting between them.

**`measure_Iic_ne_top` is not σ-finiteness**, and the two are incomparable:
Lebesgue measure on `ℝ` is σ-finite and fails it, counting measure on an
uncountable antichain satisfies it and is not σ-finite.

* `Clock.interval_union` — for `s ≤ t ≤ u` the intervals are disjoint and add.
  **This additivity is the only property of the interval the compensator uses**,
  and it is why the interval is a difference of down-sets: it needs `t ↦ Set.Iio t`
  monotone and nothing else.
* `Clock.Ico_eq_setIco` and `Clock.Ioc_eq_setIoc` under `[LinearOrder ι]`, marked
  `@[simp]` and rewriting the clock form **into** Mathlib's.
* `Clock.IsAtomless q` and `Clock.interval_eq_of_isAtomless` — where the two
  conventions coincide.
* `Clock.IsContinuousFor q c` — the compensating window between two times shrinks
  as they approach.
* `Clock.IsShiftInvariant` for `[AddMonoid ι]`, and `Clock.interval_add` under a
  linear order. The linear order is not decoration there: the statement is false
  on a preorder that is not linear.
* Instances: counting measure on `ℕ`, Lebesgue on `[0,∞)`, `∑ n, δ n` on
  `[0,∞)`, and every locally finite Borel measure on a closed subset of `ℝ`.

**Acceptance examples.**

* **The four clocks of the manuscript**, each an instance, each computing.
* **The diamond, where `Set.Ico` is the wrong interval.** On `{0 < a, b < t}`
  with `a`, `b` incomparable, `Set.Ico a t = {a}` while the clock interval is the
  larger set the additivity needs.
* **Atomless and atomic at once**: `volume + δ 1`, where the two conventions
  genuinely differ.
* **Shift invariance is not automatic**: `∑ n, δ n` on `[0,∞)` fails it.

## Milestone 2: the abstract martingale problem

* `IsMPSolution 𝓧 𝓕 P`, defined as `∀ Y ∈ 𝓧, Martingale Y 𝓕 P`, and the local
  variant `IsLocalMPSolution` through Mathlib's `Locally`. `MPSolutions 𝓧 𝓕`,
  with `MPSolutions (𝓧 ∪ 𝓨) = MPSolutions 𝓧 ∩ MPSolutions 𝓨`.
* `mpProcess q c X f g = fun t ω ↦ f (X t ω) - ∫ s in Clock.interval q c ⊥ t, g (X s ω) ∂q`
  and `mpFamily A q c X`, with `IsMPSolutionFor A q c X 𝓖 P`.
* `IsMPSolutionFor.map` — the property depends on `P` only through the law of
  `X`, so it transfers along a modification.
* `MPSolutions.span` — a solution for `A` solves for `Submodule.span 𝕂 A`,
  `mpProcess` being linear in the pair.
* `IsMPSolutionFor.insert_of_tendsto` and its bounded pointwise corollary
  `…_of_forall_norm_le` — closure of the solution property along limits of test
  pairs.

  **No closure operator for bounded pointwise convergence is built.** Such a
  closure is a transfinite iteration, and every consumer here needs only the one
  step, which the two items give.
* `IsMPSolutionFor.submartingale_mpProcess_of_tendsto` — the one-sided companion,
  for real-valued test pairs.

**Acceptance examples.** The Poisson process, computed by hand; **a clock with an
atom, where the two conventions give different solutions**; the bump sequence
against `insert_of_tendsto`; and a pair on which the one-sided companion is
genuinely weaker.

## Milestone 3: canonical families, determining sets, and the finite dimensional criterion

* `IsCanonical 𝓧 X` and `IsDetermining 𝓩° 𝓧` — the latter saying that the
  martingale identity may be tested against `𝓩° s` alone.
* `isDetermining_products` — for the natural filtration and any dense `D`, the
  products of bounded functions of finitely many earlier coordinates are
  determining.
* `Clock.IsProgressive Q X 𝓕` and `Clock.IsProgressiveComp` — joint measurability
  in time and sample point, the second for the **real functionals** of the
  process, which is the form the compensator needs.
* `isMPSolutionFor_iff_forall_fdd` — **the criterion**: `X` solves the problem iff
  for all `s ≤ t`, all finite chains of earlier times and all bounded measurable
  test functions the corresponding integral identity holds. Hence the solution
  property depends only on the finite dimensional distributions of `X`.
* The supporting chain: `pathCylinders` with `isPiSystem_pathCylinders` and
  `generateFrom_pathCylinders`; `mpFamily_sub_of_isProgressive`;
  `integral_sub_mul_eq_zero_of_martingale`; `setIntegral_eq_of_forall_cylinder`.

**Acceptance examples.** The manuscript's `ex:determining`; **the filtration is a
hypothesis, not a convention** (an independent coin enlarging the filtration
changes nothing, an arbitrary enlargement does); a process measurable at every
time and progressive at none; and the metrizable case, where bounded continuous
test functions suffice.

## Milestone 4: mixtures, shifts and the restart lemma

* `MPSolutions.isConvex` and `MPSolutions.integral_mem` — a measurable mixture of
  solutions is a solution.
* `Shift` and `ShiftSystem 𝓧°`, with `isShiftSystem_mpFamily`: `mpFamily` carries
  a shift system when the clock is shift invariant.
* `restart` — **the restart lemma.** Under adaptedness, `r ≤ r + u`, and
  integrability, a solution reweighted by a bounded density and shifted is a
  solution of the shifted problem. `restart_canonical` is the case `Ω = F`.

  The hypotheses are exactly those: **no `𝔼[Z] = 1` and no determining set**.
* The three measure theoretic inputs for a reweighted image measure, none of them
  in Mathlib in this shape.

**Acceptance examples.** The shifted problem of `ex:shiftXA`; **a clock that is
not shift invariant breaks the shift system** (`δ 1` on `[0,∞)` with `r = 1/2`);
and mixtures at the smallest scale.

## Milestone 5: uniqueness and the Markov property, without an operator

The milestone's own notion:

* `PropagatesAgreement 𝓕° π N` — for `P, Q ∈ N`, `s ≤ t` and every bounded
  non-negative `𝓕° s`-measurable weight, agreement of the weighted law at `s`
  propagates to `t`. With `weightedLaw`, `weightedLaw_univ`,
  `propagatesAgreement_of_transfer`.
* `measure_cylinder_inter_eq_of_propagatesAgreement` and
  `measure_cylinder_eq_of_propagatesAgreement` — the induction over a chain, the
  top coordinate's set kept as a separate argument.
* `measure_biInter_eq_of_propagatesAgreement` — the same over an **unordered**
  finite set of times. **This is the one place the linear order on the index is
  consumed.**
* `eq_of_propagatesAgreement` and `subsingleton_of_propagatesAgreement`.

The consequences:

* `propagatesAgreement_of_unique_onedim` — under a shift system, uniqueness of
  the **one dimensional** distributions of every shifted problem suffices.
* `isMarkov_of_unique_onedim` — every solution is Markov, in general time
  inhomogeneously.
* `subsingleton_mpSolutions_of_unique_onedim` — for a linearly ordered index, at
  most one solution with a given initial law. This is the manuscript's
  `thm:absuniq`, **and it takes a single `r`**.
* `isStrongMarkov` — with càdlàg paths and a measurable shift system, the Markov
  property at every almost surely finite stopping time.
* The classical statement as an instance, for `E` metrizable and
  `A ⊆ Cb(E) × Bdd(E)`.

The canonical path space this milestone needs: `IsRightLocallyConstant`,
`RightContinuousPath E` with `coordinate` and `generateFrom_coordinate`,
`pathShift`, and the adaptedness and integrability of `mpFamily` there.

**Acceptance examples.** **Uniqueness of the one dimensional laws is genuinely
weaker than uniqueness**, and the milestone assumes only the former. The two
state chain, all the way through, with its transition operator computed. And the
converse direction, where it is **not**: Brownian motion is the unique solution
for `(f, f''/2)` on `Cc^∞(ℝ)`, and that is an instance of the theorem and not of
its converse.

## Milestone 6: localization

The localizing systems here are a **refinement** of Mathlib's
`IsLocalizingSequence`, not a replacement. A **strict** stopping time is one for
`𝓕` and not for the right continuous filtration `⨅ s > t, 𝓕 s`, and the
distinction is the content of the milestone.

* `LocalizingSystem 𝓧° Σ` with its three clauses (L1)–(L3).
* `localizingSystem_of_boundedJumps` — for càdlàg test processes starting at `0`
  with bounded jumps, the hitting times of the **running supremum** form a
  localizing system.
* `localRestart` and `subsingleton_localMPSolutions`.

**Acceptance examples.** The exploding jump process, where the local problem has a
solution and the global one has none. **The running supremum is not a
convenience**: for a càdlàg `Y`, the hitting time of the *norm* is a stopping
time for the right continuous filtration only, and the whole point of the
milestone is to stay with `𝓕`.

## Milestone 7: duality

A dual process determines the one dimensional distributions, hence, with
Milestone 5, gives uniqueness. The milestone is built from one algebraic identity
and then the analysis needed to run it on clocks of each kind.

* `chain_identity` — the staircase identity, on a preorder with a least element:
  for `Φ, γ₁, γ₂` with the increment relation, the sum along a staircase from
  `(⊥, t)` to `(t, ⊥)` telescopes. **The telescoping reads neither endpoint**, so
  the statement is the one for an arbitrary interval.
* `duality` — the identity at two independent processes, and `duality_weighted`
  with a weight on the **first** factor. `not_secondIncrement_of_weight_on_dual`
  shows the weight must sit there.
* `propagatesAgreement_of_duality` and `isMarkov_of_duality` — the bridge to
  Milestone 5; `uniqueness_of_duality` the standard application.

The clocks, in increasing difficulty, each a statement of its own:

* `duality_of_atomless` — by the time change `Q t = q (Set.Iio t)`.
* `duality_discrete` — `ι = ℕ` with counting measure, which follows from
  `chain_identity` **alone** and needs none of the analysis. This is the collapse
  test.
* `Clock.stretches` and `duality_of_mixed` — finitely many atoms in an otherwise
  atomless clock.
* The purely atomic cases, in order of generality:
  `duality_of_atomic` (finitely many atoms below `t`),
  `duality_of_atomic_antichain_of_integrable`,
  `duality_of_atomic_weakOrder_of_integrable` (via `Clock.atomLayers` and the
  averaged kernel `Clock.atomLayerKernel`),
  `duality_of_atomic_chain_of_integrable`,
  `duality_of_atomic_finiteHeight_of_integrable` (via
  `Clock.IsAtomCertificate` and `exists_isAtomCertificate_of_finiteHeight`),
  `duality_of_atomic_intervalFinite`, `duality_of_atomic_twoChains_of_bounded`,
  `duality_of_atomic_blockStack_of_bounded`,
  `duality_of_atomic_idealExhaustion` and `…_finiteCoreReduction`.

  The linear algebra behind the certificates is stated separately and is of
  independent interest: `Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`,
  `Matrix.exists_isSymm_mulVec_one_eq_single`, `Matrix.krylovCertificate_unique`;
  and the complex analysis behind the infinite chains:
  `tailProduct`, `norm_le_of_bddOn_imAxis_of_subexponential`,
  `chainTailProduct_pairing_eq_zero`.

**Where it stops, and it is stated as a limit and not as an omission.**
`exists_atomic_antichain_duality_ne` and
`not_exists_isAtomCertificate_of_isDirected_of_noMinOrder` are witnesses that no
certificate exists in general; `exists_atomic_antichain_duality_ne` is a clock
whose atoms below `t` are pairwise incomparable and for which the duality fails.

**Acceptance examples.** **The diamond, which fixes the convention** — with
`m c² = m a · m b` the predictable and optional conventions disagree. **The
antichain of `ex:antichain`, which fixes the integrability.** **The three order
types an interval-finite chain must survive** (`ω` accumulating at `t`, `ω*`
accumulating at `0`, and the two-sided one). And `duality_discrete` as the
collapse test.

## Milestone 8: continuous time martingales and the càdlàg modification

What Mathlib's discrete-index theory leaves.

**Optional sampling and stopping in continuous time.**
`Submartingale.stoppedValue_min_le_condExp` for a bounded stopping time and its
form `…_of_ae_finite` for an almost surely finite one under an integrability
hypothesis; `Martingale.stoppedProcess_of_rightContinuous`; Doob's inequalities,
the supremum being measurable because right continuity makes it a supremum over a
countable set.

**Regularization.** The deterministic content carries no probability at all:
`HasUpcrossings`, the oscillation of a real function along a one sided filter.
Then submartingale regularization, which Mathlib does not have although the
ingredient does.

* The modification as a **construction** and not an existential: `rightLimAlong D g t`,
  `cadlagModif Y`, `isCadlag_rightLimAlong`.
* `Submartingale.cadlagModif_ae_eq_iff_continuousWithinAt_integral` — it is a
  modification **exactly** where `t ↦ 𝔼[Y t]` is right continuous, and
  `Martingale.cadlagModif_ae_eq` says the condition is automatic for a martingale.

**The càdlàg modification theorem.** `IsRegularizingClass Φ X 𝓧`,
`CompactContainment X D`, and
`exists_cadlag_modification_of_isRegularizingClass`. The one step no amount of
real valued work replaces is `exists_tendsto_of_forall_tendsto_comp`: an
`E`-valued limit out of real ones, which is where compact containment is spent.
`isRegularizingClass_mpFamily` and `isCompensatorFor_mpFamily` discharge the
hypotheses for `mpFamily`, the latter needing `Clock.IsContinuousFor`.

**Quasi-left-continuity.** `IsQuasiLeftContinuous X 𝓕 P`, with
`IsQuasiLeftContinuous.ae_eq_leftLim`;
`isQuasiLeftContinuous_of_forall_ae_tendsto_comp` — from countably many scalar
convergences to the vector statement; and
`isQuasiLeftContinuous_of_isRegularizingClass`, the abstract form of
Ethier–Kurtz 4.3.12 with no operator and no compensator of any special shape,
resting on `IsOptionalSamplingFor` and `IsStronglyMeasurableAlongStoppingTimes`.
`tendsto_ae_condExp_rclike` is Lévy's upward theorem for an `RCLike` integrand,
which Mathlib has only over `ℝ`.

**Two things that must be assumed and are not consequences**, each with a
witness: `LiftWitness` shows the right continuity of `Y` does **not** follow from
that of `f ∘ X` and of the compensator; and
`not_isQuasiLeftContinuous_of_isRegularizingClass_of_free_solutionSet` shows a
martingale hypothesis on `Y` is indispensable. `not_isQuasiLeftContinuous_of_atom`
shows atomlessness of the clock is a hypothesis of the **statement**.

**Acceptance examples.** A submartingale with no càdlàg modification, and the
exact obstruction; optional sampling needing its boundedness (Brownian motion and
the hitting time of `1`); Doob's two inequalities computed; **the coin at an
atom, which separates the two theorems of this milestone**; and cutting down to
an open subset.

## Milestone 9: the abstract convergence theorem

**`P`-continuity at `X` is written `P {ω | ContinuousAt ψ (X ω)} = 1`** and
carries no definition of its own.

* `mpSolution_of_tendsto` — **the theorem.** Under (a) convergence of the tested
  integrals, (b) a uniform `L¹` bound, and (c) the vanishing martingale gap, a
  limit in distribution of solutions solves the limiting problem.
  `mpSolution_of_tendsto_of_pContinuous` is the corollary in which (a) is
  replaced by convergence in distribution together with `P`-continuity, and
  `mpSolution_of_tendsto_augmented` the augmented form.
* The analytic core, `integral_eq_zero_of_tendstoInDistribution`, with
  `radialTrunc`, `integrable_of_tendstoInDistribution`,
  `tendsto_integral_tail` and `unifIntegrable_tail_of_tendstoInDistribution`.
* `isMPSolution_of_forall_condExp_eq_of_dense` — the passage from the martingale
  identity along a dense `D` to the whole index, and the last step of the
  theorem, with `tendsto_eLpNorm_sub_of_forall_condExp_eq`.
* The apparatus for verifying (c) on a chain: `chainCompensated` with
  `martingale_chainCompensated`, `gridPath`, `coordFiltration`,
  `naturalFiltration_eq_comap_block`, and
  `integral_sub_mul_eq_zero_of_martingale_stoppedValue` with its dominated and
  bounded forms.
* `IsDetermining` witnesses: `isDetermining_of_generateFromFuns` — **a generating
  multiplicative class is already a determining set** — with
  `isDetermining_indicatorFuns`, `isDetermining_pathCylinders` and
  `isDetermining_evalFuns`.

**Acceptance examples.**

* **The rescaled Markov chain of `ex:invariance`**, with hypothesis (c) verified
  over the chain's **own** natural filtration.
* **The i.i.d. chain as an emptiness probe**, and the same probe with a nonzero
  (K3), so that the probe is not about a degenerate object.
* **The probe reads the jump number and not the time, and the two are not the
  same** — the renewal count against `⌊n t⌋`. `tendsto_stepIndex_div_atTop` is the
  renewal law of large numbers, and **it is deterministic**.
* **Speeding up the rate is a time change**, and **one waiting time out of step
  already breaks the identification** of a jump process with a grid path.
* **`P`-continuity is not continuity**, the manuscript's `ex:atomicdiscontinuity`:
  evaluation on `D ℝ ℝ` is discontinuous at every path that jumps at the time
  read, and the hypothesis is about the *law* and not about the functional.

## Milestone 10: the Skorokhod instances

The instances of the abstract theory on `D(ℝ≥0, E)`, and the acceptance test is
**Donsker**.

**Compact containment and tightness.**

* `UniformCompactContainment` — kept **verbatim from `CompactContainment` except
  for the quantifier order**, so that the two compose. It is stated about path
  space valued variables and not about processes, for a measured reason.
* `isCompactContained_map_of_uniformCompactContainment` and the converse
  `uniformCompactContainment_iff_isCompactContained_map`, the latter **without any
  hypothesis on the family**. **The window is bought at a horizon one unit
  longer**, and that is the shape of the argument rather than a convenience.
* `isTight_map_postcomp_of_exists_martingale` — the criterion the rest consumes.

**Approximability, and what it excludes.**

* `MeasureTheory.IsApproximable 𝓕 P q T K V ε₀ u` — to every error two
  approximating pairs, each a martingale plus an **absolutely continuous**
  compensator with an `L^q` bound on its density.
* `IsApproximable.integral_eq_of_eqOn_Ico` — **what approximability excludes is
  the deterministic jump.** If `V` is constant on `Set.Ico a b` as a function of
  time *and* sample point, its mean cannot move across `b`. The unit step
  `1_{[b,∞)}` is therefore approximable by nothing, over no filtration and under
  no measure — and it carries no randomness at all. A process with **random**
  jump times is not affected.
* `IsEventuallyApproximable` — the error quantified **outside** the index, which
  is how Ethier–Kurtz (9.26) reads, with finitely many members exempted
  (`…_off_finite`, and `…_off_finite_window` where the exempted set may move with
  the window). **The exchange of quantifiers is not idle**: the deterministic unit
  steps of height `(i+1)⁻¹` are the witness.
* `isTightMeasureSet_map_postcomp_of_isEventuallyApproximable`.

  **Its filtration is indexed**, `𝓕 : γ → Filtration ℝ≥0 mΩ`, and that is not
  bookkeeping: the rescaled walks of Donsker have **no common filtration**.
  Adaptedness of every member would put the whole tail σ-algebra into every
  `𝓕 t`, and the martingale property would then force the increments to vanish.
  No consumer ties two members through the filtration; what is shared is the
  scalars.

**The convergence seams.**

* `mpSolution_of_tendsto_cadlag` — the limit of càdlàg solutions solves the
  limiting problem, with `cadlagFiltration`, `measurable_mpTest` and `abs_mpTest_le`
  supporting it; the wrappers `…_of_approx`, `…_of_pathwise`, `…_asymptotic`.
* `isRelativelyCompact_of_approx` and `tendsto_of_isRelativelyCompact_of_unique`.
* `tendstoInDistribution_id_of_tendsto`, and the seams
  `mpSolution_of_tendsto_cadlag_of_subseq`, `…_of_subseq_of_zero` (at the
  **vanishing martingale gap** rather than at exact martingality of a moving test
  pair) and `…_pathOfProcess`.

**Acceptance test: Donsker.** `E = ℝ`, `X n t = n^{-1/2} ∑_{k ≤ ⌊n t⌋} ξ k` for
i.i.d. centred `ξ` of variance `1`, and `A = {(f, f''/2)}` on `Cc^∞(ℝ)`. The four
chain points are to be met once each and in order.

**Acceptance examples.**

* **The times `D` must avoid the fixed discontinuities.**
* **The pathwise form is weaker where it matters**: a `g n` differing from `g` on
  a set the processes visit with probability tending to `0`.
* **Separating is not convergence determining**, and the milestone must not
  confuse them: in `isRelativelyCompact_of_approx` the algebra is used for the
  first and not the second.

## Infrastructure carried here and used elsewhere

`Suggested.lean` also carries general machinery that no milestone above is
*about* and that the **JumpProcesses** roadmap reads. It is listed so that a
reviewer meeting it in the prototype knows why it is there:

* step paths — `IsStepPath`, `measurable_stepIndex_comp`, `measurable_stepPath_comp`,
  `eventuallyEq_nhdsGE_stepPath`, `stepPathFiltrationE`;
* joint measurability of a right continuous process —
  `measurable_uncurry_min_of_rightContinuous`,
  `isStronglyProgressive_of_measurable_uncurry_min`;
* continuous time stopping — `martingale_stoppedProcess`, `dyadStop`,
  `stoppedValue_ae_eq_condExp` (these belong to Milestone 8 and are stated there);
* the augmentation of a filtration by the null sets — `Filtration.augment`,
  `condExp_augment`, `Martingale.of_augment`, `naturalFiltration_augment_eq_of_ae_eq`
  — with the almost sure comparison `aeCompletion`, `naturalFiltration_inter_le`,
  `martingale_of_ae_eq_of_le_aeCompletion`;
* two analytic items — `expMeasure_Ioi` with `expMeasure_Ioi_add`, and
  `eq_exp_add_integral_of_hasDerivWithinAt`, the scalar linear equation solved by
  the integrating factor.

## Milestone 11: existence from a dual process

> **This milestone is a roadmap-for-a-roadmap and is not to be attempted as
> stated.** Its last step rests on the **KolmogorovExtension** roadmap, which does
> not yet exist in Mathlib, and the fibred state space of its last point is a
> design change no other milestone needs. It is recorded so that the shape of the
> argument is not lost.

Data: a Markov semigroup on `E₂`, a measurable `F : E₁ × E₂ → ℝ`, and a family of
operators subject to a balance condition in integrated form — no strong
continuity, no generator, no domain theory. Then `dualSemigroup`,
`exists_projectiveFamily_of_dual`, and `exists_mpSolution_of_dual` through the
Kolmogorov extension theorem.

## Milestone 12: the full generator, and which operators are generators

> **This milestone is a roadmap-for-a-roadmap and is not to be attempted as
> stated.** It names one proposition and its converse because a remark of the
> manuscript rests on them; it does not develop the theory they belong to. What a
> full treatment would need is the subject of the `OneParameterSemigroups`
> roadmap.

`IsDissipative`, `MeasurableContractionSemigroup`, `fullGenerator T` as the pairs
`(f,g)` with `T t f - f = ∫ s in Ioc 0 t, T s g`; then
`fullGenerator_isDissipative`, `mpSolution_resolvent_repr`,
`isDissipative_of_forall_exists_mpSolution` and `isMPSolutionFor_fullGenerator`.
