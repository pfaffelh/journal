# Martingale problems

A martingale problem specifies a process by requiring a family of functionals of
it to be martingales. The classical form fixes an operator `A` on functions on a
state space `E` and asks that `f (X t) - ∫ s in Ioc 0 t, (A f) (X s)` be a
martingale for every `f` in the domain of `A`. The theory of uniqueness, of the
Markov property, of path regularity and of convergence does not use the operator
and does not use the state space; it uses only the family of martingales. This
roadmap develops the abstract form first and obtains the classical statements as
instances.

Mathlib supplies the probabilistic base, which is **not** to be rebuilt:

* `MeasureTheory.Filtration`, `MeasureTheory.Adapted`,
  `MeasureTheory.StronglyAdapted`, `MeasureTheory.IsStronglyProgressive` and
  `MeasureTheory.IsStoppingTime` in `Mathlib/Probability/Process/`. Note that
  `ProgMeasurable` is a deprecated alias of `IsStronglyProgressive`; use the
  new name.
* `MeasureTheory.Martingale`, `MeasureTheory.Supermartingale` and
  `MeasureTheory.Submartingale` in `Mathlib/Probability/Martingale/Basic.lean`.
  The definitions are stated for `[Preorder ι]`, so a continuous time index
  needs no new definition, and `MeasureTheory.Martingale` is stated for values
  in a real Banach space, so complex-valued martingales need no separate
  development.
* The theorems about them are for a **discrete index**, and Milestone 9 states
  what that leaves. `Mathlib/Probability/Martingale/OptionalStopping.lean` fixes
  `{𝒢 : Filtration ℕ m0}` and proves `Submartingale.expected_stoppedValue_mono`,
  `submartingale_iff_expected_stoppedValue_mono` and Doob's maximal inequality
  `MeasureTheory.maximal_ineq`. `Mathlib/Probability/Martingale/OptionalSampling.lean`
  proves the optional sampling theorem `Martingale.stoppedValue_min_ae_eq_condExp`
  under `[LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]`, an index
  order-isomorphic to a subset of `ℕ`, and for a martingale only. The upcrossing
  theory of `Mathlib/Probability/Martingale/Upcrossing.lean` —
  `upcrossingsBefore`, `upcrossings`, `upcrossings_lt_top_iff` and the Doob
  estimates `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
  and `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part` — and the
  convergence theorems of `Mathlib/Probability/Martingale/Convergence.lean` fix
  `Filtration ℕ` as well. What is **not** tied to `ℕ` is the step from "no
  oscillation" to convergence: `tendsto_of_no_upcrossings`
  (`Mathlib/Topology/Order/LiminfLimsup.lean:317`) holds along an arbitrary
  filter, over a densely ordered target and a dense set of levels. Only the
  *counting* of upcrossings is discrete, which is what Milestone 9 splits along.
  Doob's `Lᵖ` inequality is absent for every index.
* **Localization is already there.**
  `Mathlib/Probability/Process/LocalProperty.lean` has
  `ProbabilityTheory.IsPreLocalizingSequence`,
  `ProbabilityTheory.IsLocalizingSequence`
  — stopping times valued in `WithTop ι`, almost surely increasing to `⊤` — and
  the combinator `ProbabilityTheory.Locally p 𝓕 X P` saying that `X` has
  property `p` locally, with `Locally.localSeq`, `Locally.stoppedProcess_localSeq`,
  `Locally.of_prop`, `Locally.mono`, `IsStable.locally_and_iff` and the
  idempotence `IsStable.locally_locally_iff`, the last under
  `[IsRightContinuous 𝓕]`. The namespace is `ProbabilityTheory`, not
  `MeasureTheory`, unlike the rest of `Mathlib/Probability/Process/`.
  Every local notion below is an instance of `Locally`; none of it is to be
  redefined. What is there is the abstract combinator only: the file names
  martingales in its module comment and nowhere else, and
  `ProbabilityTheory.IsStable` is proved for no property of interest here —
  `IsStable.and` is the only closure lemma, and the identifier occurs in no
  other probability file. The martingale instance is Milestone 9.
* `Mathlib/Probability/Process/FiniteDimensionalLaws.lean`, namespace
  `ProbabilityTheory`: `isProjectiveMeasureFamily_map_restrict`,
  `isProjectiveLimit_map`, `map_eq_iff_forall_finset_map_restrict_eq`,
  `identDistrib_iff_forall_finset_identDistrib` and `map_eq_of_forall_ae_eq`.
  These say that a law is determined by its finite dimensional distributions and
  that modifications share them, and Milestone 3 is to be phrased through them.
* `Mathlib/Probability/Process/Kolmogorov.lean`, namespace `ProbabilityTheory`:
  the Kolmogorov condition
  `IsKolmogorovProcess` and `IsAEKolmogorovProcess`, stated for an index in a
  `PseudoEMetricSpace` with no order, together with `mk`, `ae_eq_mk`,
  `mk_of_secondCountableTopology` and the measurability lemmas. It is the
  precedent for how the hypothesis of a modification theorem is bundled, and the
  `IsRegularizingClass` of Milestone 9 should read like it. The
  Kolmogorov–Chentsov theorem itself is **not** in Mathlib: the string
  `Chentsov` occurs in the library in exactly two places, the module comment of
  this file and `Mathlib/Topology/EMetricSpace/PairReduction.lean`, and neither
  is the modification statement. The proof exists in
  `RemyDegenne/brownian-motion`, `BrownianMotion/Continuity/`, under a bounded
  covering number hypothesis; it is a moment criterion and not a martingale
  argument, so it belongs neither to this roadmap nor to **SkorokhodSpace**.
* Conditional expectation, `MeasureTheory.UniformIntegrable`, Polish spaces,
  weak convergence and Prokhorov's theorem.

This roadmap depends on **WeakConvergence** for separating classes, the
functional monotone class theorem, the continuous mapping theorem and the
Skorokhod representation theorem; on
**SkorokhodSpace** for the space of càdlàg paths, used in Milestone 11; and on
**KolmogorovExtension** for the projective limit, used in Milestone 12.

## Conventions fixed once

* The index `ι` is a preorder, matching `MeasureTheory.Filtration`. Individual
  milestones add a linear order, a lattice, a countable dense subset, or an
  ordered monoid structure, and each says which.
* The scalar field of the test processes is `𝕂` with `[RCLike 𝕂]`. Test
  processes are `𝕂`-valued; the sets that test them are real-valued, because
  testing an increment against real functions already separates real and
  imaginary part.
* An operator is a **relation**, `A : Set ((E → 𝕂) × (E → 𝕂))`, not a function.
  This is needed for domains on which the operator is multivalued and costs
  nothing elsewhere.
* Compensation carries a convention parameter `c : Clock.Conv` selecting the
  optional or the predictable interval. It is a parameter of the definition, not
  a global choice; the same Markov chain needs one convention on `ℕ` and the
  other after its grid is embedded in `[0,∞)`.
* **The compensating interval is a difference of down-sets, not `Set.Ico`.**
  Mathlib's `Set.Ico`, `Set.Ioc`, `Set.Iio` and `Set.Iic` are defined for
  `[Preorder α]` (`Mathlib/Order/Interval/Set/Defs.lean`), so the weaker order is
  no obstacle to using them — but `Set.Ico s t` and `Set.Iio t \ Set.Iio s` are
  **different sets** on a preorder, and it is the second that the clock needs.
  See Milestone 1.

## Milestone 1: the clock

The compensator integrates against a measure on the index, not necessarily
Lebesgue measure. Fix `[Preorder ι]`.

* `Clock ι`, a structure bundling a `MeasurableSpace ι`, a `Measure` `q` on it,
  the hypothesis that `Set.Iic t` and `Set.Iio t` are measurable for every `t`,
  and `q (Set.Iic t) ≠ ∞`.

  **`measure_Iic_ne_top` is not σ-finiteness, and the two are incomparable.**
  The condition says every *single* down-set has finite mass, which is what makes
  the compensator `∫_{⟨⊥,t⟩} g (X s) q(ds)` a real number and the increment
  `Y t - Y s` an honest difference rather than `∞ - ∞`. σ-finiteness does not give
  that — it permits `q (Set.Iic t) = ∞`, and then `Y t` does not exist; `ℝ` with
  Lebesgue measure is σ-finite and not a clock. Conversely the clock condition
  does not give σ-finiteness: on an uncountable antichain (`t ≤ u ↔ t = u`) with
  counting measure every `Set.Iic t = {t}` has mass `1`, and counting measure on
  an uncountable set is not σ-finite. The union `⋃ t, Set.Iic t = univ` is
  uncountable in general, which is exactly what σ-finiteness would need to be
  countable.

  Nothing in this development integrates over all of `ι` — only over windows —
  so σ-finiteness is never required, and `SigmaFinite` occurs nowhere in
  `Suggested.lean`. The `SFinite` instances there are all for measures on `Ω`,
  on products or on kernels; the single clock-side occurrence is
  `SFinite (lebesgueClock.q.restrict S)`, which `inferInstance` finds because
  that is a concrete image of Lebesgue measure. For an abstract `Q : Clock ι`
  there is nothing to infer: `q` is a structure field with no instance.

  **Available on demand, and not worth stating before then.** If a proof ever
  needs Fubini over `ι × Ω` for an *abstract* clock, σ-finiteness is what it
  will want, and it follows in about ten lines from one extra hypothesis that is
  nowhere assumed today: a countable cofinal family `(t n)`. Take
  `A n = ⋃ k ≤ n, Set.Iic (t k)` — measurable by `measurableSet_Iic`, monotone,
  of finite mass as a finite union by `measure_Iic_ne_top`, and covering `univ`
  by cofinality; that is Mathlib's `spanningSets`. It holds for every instance
  the manuscript carries (`ℝ≥0` via `ℕ`, `ℕ₀`, `[0,T]`, `h·ℤ`, and `ℝ₊^d` via
  `(n,…,n)`). Until there is a consumer it would be a lemma nobody applies, so
  it is recorded here rather than proved.
* The two intervals `Clock.Ioc q s t = Set.Iic t \ Set.Iic s` and
  `Clock.Ico q s t = Set.Iio t \ Set.Iio s`, with `Clock.Conv` the two element
  type selecting between them and `Clock.interval q c s t` the selected one.
* `Clock.interval_union`: for `s ≤ t ≤ u` the intervals are disjoint and
  `interval q c s u = interval q c s t ∪ interval q c t u`. This additivity is
  the only property used downstream and holds for both conventions because
  `t ↦ Set.Iic t` and `t ↦ Set.Iio t` are monotone.
* `Clock.measure_interval_ne_top`, and measurability of `interval q c s t`.
* `Clock.Set_Ico_subset` and `Clock.Ico_eq_setIco`: `Set.Ico s t ⊆ Clock.Ico q s t`
  for `[Preorder ι]`, with equality under `[LinearOrder ι]`. The inclusion is
  always strict where an element below `t` is incomparable to `s`, since
  `Set.Ico s t = {x | s ≤ x ∧ x < t}` demands comparability while
  `Set.Iio t \ Set.Iio s = {x | x < t ∧ ¬(x < s)}` does not. On the diamond
  `{0 < a, b < t}` with `a`, `b` incomparable, `Set.Ico a t = {a}` whereas
  `Clock.Ico q a t = {a, b}`. State both lemmas so that no later proof silently
  substitutes one for the other, and note in the docstring of `Clock.Ico` that
  the name follows `Set.Ico` only up to this inclusion.
* Mark the two equalities `Clock.Ico_eq_setIco` and `Clock.Ioc_eq_setIoc`
  `@[simp]`, rewriting the clock form **into** Mathlib's. Under
  `[LinearOrder ι]` the conventions become `Set.Ico s t` and `Set.Ioc s t` by
  `not_lt` and `not_le`, so every concrete index — `ℝ≥0∞`, `Set.Ici (0:ℝ)`,
  `Set.Icc (0:ℝ) T`, `ℕ`, `AddSubgroup.zmultiples h` — lands in Mathlib's
  interval API automatically, with `Set.Ico_union_Ico_eq_Ico` and the rest
  available. The difference of down-sets is the primitive of the abstract layer
  only; it is not a parallel interval library.
* The reason the clock takes the difference of down-sets and not `Set.Ico`:
  `Clock.interval_union` above needs `t ↦ Set.Iio t` monotone and nothing else,
  whereas the corresponding statement for `Set.Ico` needs comparability. The
  additivity is what every compensator argument downstream rests on, so it is
  the property the definition is chosen to have.
* `Clock.IsAtomless q`, defined as `q {u | t ≤ u ∧ u ≤ t} = 0` for every `t`,
  together with `Clock.interval_eq_of_isAtomless`: the two conventions give the
  same measure of every interval exactly when the clock is atomless.
* `Clock.IsContinuousFor q c`, defined as
  `Tendsto (fun s ↦ q.real (interval c (min s t) (max s t))) (𝓝 t) (𝓝 0)` for
  every `t`: the compensating window between `s` and `t` loses its mass as `s`
  runs into `t`. It is the hypothesis under which the compensator of `mpFamily`
  is continuous in time, and so the input of Milestone 9 that the martingale
  problem itself does not supply. Only a linear order and a topology on the
  index enter, no order topology and no completeness.

  **It does not imply `Clock.IsAtomless`.** Over a discrete index it is
  vacuous — `𝓝 t` is `pure t` and the window at `s = t` is empty under both
  conventions — so counting measure on `ℕ` has it and is atomic. Over a first
  countable index an atomless clock should have it, by continuity from above of
  a measure finite on down-sets; that implication is not part of this milestone,
  because the clock the roadmap uses gets the property by computing the mass of
  the window exactly (`lebesgueClock_isContinuousFor_optional`).
* For `[AddMonoid ι]` with a compatible order, `Clock.IsShiftInvariant q`,
  defined as `q ((r + ·) '' B) = q B` for measurable `B` — the **image** of `B`
  under the shift, not its preimage. The preimage form `q ((r + ·) ⁻¹' B) = q B`
  is a different and false condition: for Lebesgue measure on `[0,∞)`, `r = 2`
  and `B = [0,1]` the preimage is empty while `q B = 1`, and for counting
  measure on `ℕ`, `r = 2` and `B = {0}` likewise. The image form is what the
  manuscript's `def:clock` states and what the instances below satisfy.
* `Clock.interval_add`, expressing
  `interval q c (r + s) (r + t) = (r + ·) '' interval q c s t` up to a null set,
  **under (T2a)**. The linear order is not decoration: over
  `ι = [0,∞)^2` with the product order the identity is false on a set of
  positive measure, because a `v` with `v ≤ r + t` and `¬ (v ≤ r)` need not
  satisfy `r ≤ v` and so need not be of the form `r + u`. With `r = (1,0)`,
  `s = 0`, `t = (2,2)` the point `(0,1)` lies in the left hand side and not in
  the right. What the proof needs is exactly that `¬ (v ≤ r)` implies `r ≤ v`,
  which over a linear order is totality and over a product order is false.

  The form the shift system consumes is neither of the two above but the
  identity of measures
  `(q.restrict (interval q c s t)).map (r + ·) = q.restrict (interval q c (r+s) (r+t))`,
  which is what makes the substitution `v = r + u` a single application of
  `MeasureTheory.integral_map`; that is `Clock.setIntegral_shift`. State it that
  way, and the order condition sits in the clock and nowhere else.
* `lebesgueClock_isShiftInvariant` and the counting measure on `ℕ`: the
  two instances of `Clock.IsShiftInvariant`, and the two that keep the shift
  system of Milestone 5 from resting on an uninhabited condition. The first is
  proved (`Suggested.lean`, `section LebesgueShift`, 2026-09-14) and holds for
  **both** conventions at once. Its two inputs are `lebesgueClock_apply`, which
  reads the mass of a measurable set of `ℝ≥0` as a Lebesgue measure on `ℝ`, and
  `lebesgueClock_preimage_const_add`, which says that translating a set lying
  above `r` back by `r` preserves its mass.

  The route is the **preimage** and not the image: `(r + ·) ⁻¹' interval q c
  (r + s) (r + t) = interval q c s t` is `add_le_add_iff_left` and needs no
  interval lemma, after which the mass is `measure_preimage_add`
  (`Mathlib/MeasureTheory/Group/Measure.lean:230`) applied to Lebesgue measure
  on `ℝ`. The hypothesis `B ⊆ Set.Ici r` of `lebesgueClock_preimage_const_add`
  is necessary: `u ↦ r + u` is injective and not surjective on `ℝ≥0`, so for
  `B = Set.Iic r` the two sides are the mass of `{0}` and `r`. A compensating
  window starting at `r + s` meets the hypothesis, which is why the restriction
  in `Clock.IsShiftInvariant.map_interval` is part of the statement and not a
  convenience.
* The instances: counting measure on `ℕ`, Lebesgue measure on `[0,∞)`,
  `∑ n, δ (n : ℝ)` on `[0,∞)`, and every locally finite Borel measure on a
  closed subset of `ℝ`.

**Acceptance examples.**

* **The manuscript's four clocks**, `ex:clocks`, each of which must be an
  instance and must compute: `ι = Set.Ici (0:ℝ)` with Lebesgue measure, where
  `interval q c 0 t` is `Set.Ioc 0 t` or `Set.Ico 0 t` and the compensator is
  `∫ u in Set.Ioc 0 t, g (X u)`; `ι = ℕ` with counting measure, where it is
  `∑ k ∈ Finset.Ioc 0 n, g (X k)`; `ι = Set.Ici (0:ℝ)` with `∑ n, δ n`, the
  clock with atoms; and `ι = (Set.Ici (0:ℝ)) ^ 2` with Lebesgue measure, where
  `Set.Iic t` is a box and the index is **not** linearly ordered. The fourth is
  the one that decides the design: on it `Clock.Ico q s t` and `Set.Ico s t`
  differ, and every downstream proof has to survive that.
* **The diamond, where `Set.Ico` is the wrong interval.** `ι = {0 < a, b < t}`
  with `a` and `b` incomparable. Then `Set.Ico a t = {a}` while
  `Clock.Ico q a t = Set.Iio t \ Set.Iio a = {a, b}`. A definition of the
  compensating interval by `Set.Ico` loses the mass at `b`, and
  `Clock.interval_union` fails for it, since `Set.Ico 0 t` is `{0, a, b}` while
  `Set.Ico 0 a ∪ Set.Ico a t = {0} ∪ {a}`. This is the instance that the
  `@[simp]` lemmas `Clock.Ico_eq_setIco` must **not** fire on, `ι` not being
  linearly ordered.
* **Atomless and atomic, at the same point.** `ι = Set.Ici (0:ℝ)` with
  `q = volume + Measure.dirac 1`. Then `Clock.IsAtomless q` is false, and
  `Clock.interval_eq_of_isAtomless` must fail: `q (Clock.Ioc q 0 1) = 1 + 1` and
  `q (Clock.Ico q 0 1) = 1`, the two conventions differing by exactly the atom.
  With `q = volume` alone they agree at every pair, which is the other half of
  the equivalence. This is the pair the convention parameter `Clock.Conv` exists
  for, and the manuscript's `ex:atomicdiscontinuity` runs on its atomic part
  `q = Measure.dirac 1` alone.
* **Shift invariance is not automatic.** Lebesgue measure on `Set.Ici (0:ℝ)` and
  counting measure on `ℕ` satisfy `Clock.IsShiftInvariant`; `∑ n, δ (n : ℝ)`
  satisfies it for integer shifts only, and `volume + Measure.dirac 1` for none.
  So `Clock.interval_add` must carry the hypothesis, and the three instances
  must be checked separately rather than by a common lemma.

## Milestone 2: the abstract martingale problem

Two named stages of hypotheses. The first two items below carry the marks
**(A)** and **(L)**; every other item of this milestone is (A), because
`Locally` occurs in exactly one of them.
**(A)** `[Preorder ι]`, a measurable space `Ω`, a filtration `𝓕`, and
`[RCLike 𝕂]`; this carries the global problem, and it is all of it.
**(L)** additionally `[LinearOrder ι]`, `[OrderBot ι]`, `[TopologicalSpace ι]`
and `[OrderTopology ι]`; this carries the local problem, because it is what
Mathlib's `ProbabilityTheory.Locally` is stated under.
Stage (L) is read off the source and not chosen: `Locally` sits in
`Mathlib/Probability/Process/LocalProperty.lean` inside `section LinearOrder`,
under `variable [LinearOrder ι]` (`:77`) and `variable [OrderBot ι]` (`:88`),
with its own binders `[TopologicalSpace ι] [OrderTopology ι] [Zero E]` (`:93`).
The bottom element is not decoration: the definition stops the process by
`fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)`, so it names `⊥`, and `[Zero E]` is
what that indicator needs — `𝕂` supplies it. The stage that carries the whole
localization apparatus is therefore strictly stronger than (A), and Milestone 7
inherits it.

* (A) `IsMPSolution (𝓧 : Set (ι → Ω → 𝕂)) (𝓕 : Filtration ι m) (P : Measure Ω)`,
  defined as `∀ Y ∈ 𝓧, Martingale Y 𝓕 P`.
* (L) the local variant `IsLocalMPSolution`, defined as
  `∀ Y ∈ 𝓧, Locally (fun Z ↦ Martingale Z 𝓕 P) 𝓕 Y P` with Mathlib's
  `ProbabilityTheory.Locally`, whose argument order is `Locally p 𝓕 X P`. Do not
  introduce a localizing sequence by hand:
  `IsLocalizingSequence` and the `Locally` API already exist, and
  `IsStable.locally_locally_iff` is the idempotence that the local theory of
  Milestone 7 would otherwise have to prove.
* `MPSolutions 𝓧 𝓕`, the set of solutions, with the basic API: it is closed
  under restriction of `𝓧`, and `MPSolutions (𝓧 ∪ 𝓨) = MPSolutions 𝓧 ∩ MPSolutions 𝓨`.
* Given a state space `E` with `[MeasurableSpace E]`, a clock `q`, a convention
  `c`, a relation `A : Set ((E → 𝕂) × (E → 𝕂))` and a jointly measurable
  `X : ι → Ω → E`, the family
  ```
  mpFamily A q c X = {fun t ω ↦ f (X t ω) - ∫ s in Clock.interval q c 0 t, g (X s ω) ∂q | (f,g) ∈ A}
  ```
  and `IsMPSolutionFor A q c X 𝓖 P`, defined as `IsMPSolution (mpFamily A q c X) 𝓖 P`
  for a filtration `𝓖` containing the natural one. Define the version with
  respect to an arbitrary `𝓖` as the primitive and the natural filtration as the
  special case; the reverse order duplicates every subsequent statement.
* The natural filtration used is the one generated by `X` **and** by the
  compensator integrands, `⨆ s ≤ t, comap (X s) ⊓ ...`; give it a name and prove
  that the compensated process is adapted to it.
* `IsMPSolutionFor.map`: the property depends on `P` only through the law of
  `X`, so it transfers along a modification and along equality of laws on the
  canonical space. Use `ProbabilityTheory.map_eq_of_forall_ae_eq` (`:99`) and
  `ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib` (`:77`) of
  `Mathlib/Probability/Process/FiniteDimensionalLaws.lean`, whose namespace is
  `ProbabilityTheory` and not `MeasureTheory`, rather than reproving that
  modifications share finite dimensional laws.
* `IsMPSolutionFor` with an initial law: `IsMPSolutionFor A q c X 𝓖 P ∧ P.map (X 0) = μ`.
* `mpProcess q c X f g`, the compensated process
  `fun t ω ↦ f (X t ω) - ∫ s in Clock.interval q c 0 t, g (X s ω) ∂q` of a
  single pair, with `mpFamily A q c X = (fun p ↦ mpProcess q c X p.1 p.2) '' A`.
  The family is what the abstract layer of Milestone 2 consumes; the single
  process is what the two closure statements below speak about.
* `MPSolutions.span`: a solution for `A` is a solution for `Submodule.span 𝕂 A`
  in `(E → 𝕂) × (E → 𝕂)`, because `mpProcess q c X` is linear in `(f,g)`.
* `IsMPSolutionFor.insert_of_tendsto`, closure along a solution. Let `X` solve
  the martingale problem for `A` with respect to `𝓖`, let `f g : E → 𝕂` with
  `mpProcess q c X f g t` integrable for every `t`, and let `(f n, g n)` be a
  sequence in `Submodule.span 𝕂 A` with, for all `s ≤ t`,
  `fun ω ↦ f n (X t ω)` tending to `fun ω ↦ f (X t ω)` in `L¹ P` and
  `fun ω ↦ ∫ u in Clock.interval q c s t, g n (X u ω) ∂q` tending to its
  counterpart for `g` in `L¹ P`. Then `IsMPSolutionFor (insert (f,g) A) q c X 𝓖 P`.
  The proof is adaptedness of the new process together with the `L¹` contraction
  `MeasureTheory.eLpNorm_condExp_le_eLpNorm` of
  `Mathlib/MeasureTheory/Function/ConditionalExpectation/Real.lean` applied to
  the martingale identity of each `(f n, g n)`. State it for the filtration `𝓖`
  at hand rather than deriving it from `isMPSolutionFor_iff_forall_fdd` of
  Milestone 3, which would give the conclusion for the natural filtration only.
  The hypothesis is on `f` and `g` as they are composed with `X`, so it applies
  to unbounded `f` and `g` and does not narrow the operator to bounded
  functions.
* `IsMPSolutionFor.insert_of_tendsto_of_forall_norm_le`, the bounded pointwise
  corollary. Let `(f n, g n)` be a sequence in `Submodule.span 𝕂 A`, let `C : ℝ`
  satisfy `‖f n x‖ ≤ C` and `‖g n x‖ ≤ C` for all `n` and `x`, and let
  `f n x → f x` and `g n x → g x` for every `x`. Then
  `IsMPSolutionFor (insert (f, g) A) q c X 𝓖 P`. The two `L¹` limits of the
  previous item come out of dominated convergence, the second against `q ⊗ P`
  on `Clock.interval q c s t ×ˢ Set.univ`, where `Clock.measure_interval_ne_top`
  of Milestone 1 makes the constant bound integrable. The bound depends on the
  sequence alone, not on `X`, on `P` or on the clock, so this is the hypothesis
  one checks against an operator; the previous item is the one that speaks about
  a given solution and it is the one the rest of the roadmap uses. Carry the
  uniform bound as a hypothesis of the statement rather than as a predicate:
  bounded pointwise convergence is not the convergence of a topology on `E → 𝕂`,
  so `seqClosure` and `IsSeqClosed` of
  `Mathlib/Topology/Defs/Sequences.lean` do not apply to it, and a predicate of
  its own would have this one use.
* No closure operator for bounded pointwise convergence is built. Such a closure
  — the smallest set closed under bounded pointwise limits of sequences, a
  transfinite recursion over the countable ordinals, with Ethier–Kurtz,
  Appendix 3, Proposition 3.1 for its being a submodule and Proposition 4.3.1
  for two operators with equal closures having equal solutions — is used at one
  place in Ethier–Kurtz, in Theorem 4.3.8, and there only to substitute one pair
  `(Set.indicator E 1, 0)` into an identity that holds on the operator. A single
  sequence converging to that pair does the same work, by the previous item and
  by the next one; that is Ethier–Kurtz, Proposition 4.3.9, and Milestone 9
  carries the application.
* `IsMPSolutionFor.submartingale_mpProcess_of_tendsto`, the one sided companion,
  for real valued test pairs. Let `X` solve the martingale problem for `A` with
  respect to `𝓖`, let `(f n, g n)` be a sequence in `Submodule.span ℝ A`, let
  `C : ℝ` satisfy `‖f n x‖ ≤ C` and `-C ≤ g n x` for all `n` and `x` — a bound
  on `g n` from below only — let `f n x → f x` and `g n x → g x` for every `x`,
  and let `mpProcess q c X f g t` be integrable for every `t`. Then
  `Submartingale (mpProcess q c X f g) 𝓖 P`. For `s ≤ t` and
  `MeasurableSet[𝓖 s] B` the martingale identity of `(f n, g n)` reads
  `∫ ω in B, (f n (X t ω) - f n (X s ω)) ∂P = ∫ ω in B, (∫ u in Clock.interval q c s t, g n (X u ω) ∂q) ∂P`;
  the left side converges by dominated convergence and the right side has
  liminf at least its counterpart for `g` by Fatou's lemma applied to
  `g n + C ≥ 0` against `q ⊗ P` on `Clock.interval q c s t ×ˢ Set.univ`, finite
  by `Clock.measure_interval_ne_top`. This gives
  `∫ ω in B, mpProcess q c X f g s ω ∂P ≤ ∫ ω in B, mpProcess q c X f g t ω ∂P`,
  and `MeasureTheory.submartingale_of_setIntegral_le`
  (`Mathlib/Probability/Martingale/Basic.lean:281`, stated for `[Preorder ι]`
  from the variable block at `:48`, and asking besides
  `[SigmaFiniteFiltration μ ℱ]`, `StronglyAdapted ℱ f` and integrability of
  every `f i`) concludes. Two sided bounds give a martingale, which is the previous item; a
  lower bound gives a submartingale, and that inequality is all the applications
  need. Mathlib's Fatou lemma is `MeasureTheory.lintegral_liminf_le`
  (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:233`) for `ℝ≥0∞`-valued
  functions; the Bochner form for real functions bounded below is derived from
  it by adding the constant, and is stated as a lemma of its own next to the
  dominated convergence theorem.

**Acceptance examples.**

* **The Poisson process, computed by hand.** `ι = Set.Ici (0:ℝ)`, `E = ℕ`,
  `q = volume`, `c` optional, `A = {(f, fun x ↦ f (x+1) - f x) | f bounded}`,
  and `X` a Poisson process of rate `1`. Then `mpProcess q c X f (A f) t` is
  `f (X t) - ∫ u in Set.Ioc 0 t, (f (X u + 1) - f (X u))`, and
  `IsMPSolutionFor A q c X 𝓖 P` holds for the natural filtration. Taking
  `f = id` truncated gives the compensated process `X t - t`, so the milestone's
  definition must return the textbook compensator on this instance. Taking
  `c` predictable changes nothing, the clock being atomless — which is
  `Clock.interval_eq_of_isAtomless` of Milestone 1 doing visible work.
* **A clock with an atom, where the two conventions give different solutions.**
  `q = Measure.dirac 1` on `Set.Ici (0:ℝ)`, `E = ℝ`, `A = {(id, id)}` and `X`
  the deterministic path `Set.indicator (Set.Ici 1) 1`. In the optional
  convention the compensator is `X 1 * 1_{t ≥ 1}` and in the predictable one
  `X 1 * 1_{t > 1}`, so `mpProcess` differs at `t = 1` and exactly one of the
  two is adapted to the natural filtration. This is the manuscript's
  `ex:atomicdiscontinuity`, and it is why `c` is a parameter of the definition
  and not a global choice.
* **`insert_of_tendsto` against the indicator.** `E = ℝ`, `U = Set.Ioo (-1) 1`,
  `f n x = min 1 (n * Metric.infDist x Uᶜ)`, which is `0` off `U` and increases
  pointwise to `Set.indicator U 1` on `U`, and `g n = 0`. Then `‖f n‖ ≤ 1` and `g n → 0`
  pointwise, so `insert_of_tendsto_of_forall_norm_le` adjoins
  `(Set.indicator U 1, 0)` to `A` without any closure construction. This is the
  single use Ethier–Kurtz make of the bounded pointwise closure, and the
  acceptance test is that the sequence suffices; Milestone 9 consumes exactly
  this pair.
* **The one sided companion is genuinely weaker.** With `g n = -C` constant and
  `f n = 0` the conclusion of `submartingale_mpProcess_of_tendsto` is that
  `fun t ω ↦ C * q (Clock.interval q c 0 t)` is a submartingale, which it is,
  being increasing and deterministic; upgrading the conclusion to `Martingale`
  is false for it as soon as `q ≠ 0`. So the two items must be separate
  statements, and the lower bound on `g n` cannot be strengthened to a
  conclusion.

## Milestone 3: canonical families, determining sets, and the finite dimensional criterion

Fix a measurable path space `F` with measurable coordinates `π t : F → E`
generating its σ-algebra, and `X : Ω → F`.

* `IsCanonical 𝓧 X`, saying that every `Y ∈ 𝓧` is of the form `Y t = Y° t ∘ X`
  for measurable `Y° t : F → 𝕂` drawn from a given family `𝓧°`.
* `IsDetermining 𝓩° 𝓧`, saying that for every probability `P`, every `Y ∈ 𝓧`
  and all `s ≤ t` with `Y s, Y t` integrable,
  `(∀ Z ∈ 𝓩° s, 𝔼[Y t * Z (X ·)] = 𝔼[Y s * Z (X ·)]) → P[Y t | 𝓕 s] =ᵐ Y s`.
  The members of `𝓩° s` are bounded, real valued and `π`-measurable up to `s`.
* `isDetermining_products`: for the natural filtration of `X` and any dense
  `D ⊆ ι`, the set of products `∏ i, h i (π (t i))` with `t i ∈ D`, `t i ≤ s`
  and `h i` bounded continuous is determining. This uses that the σ-algebra of
  `F` is generated by the coordinates, together with the functional monotone
  class theorem `induction_on_mulSystem` of the roadmap **WeakConvergence**,
  Milestone 5, applied to the multiplicative system of those products.
* `Clock.IsProgressive Q X 𝓕`: for every `t` there is `Z : ι → Ω → E` agreeing
  with `X` on `Set.Iic t` whose uncurried form is
  `Q.measurableSpace ⊗ 𝓕 t`-measurable. This is progressive measurability in the
  shape a `Clock` forces — the clock carries its `MeasurableSpace ι` as a field
  and not as an instance, so the subtype of `Set.Iic t` cannot be written without
  `@` — and it is a hypothesis of `isMPSolutionFor_iff_forall_fdd` in both its
  forms. It is a hypothesis on `X` and the clock alone, never on `P`.

  **It shares a name with `MeasureTheory.IsProgressive` and not the statement,
  and the two must not be conflated.** The library's predicate
  (`Probability/Process/Adapted.lean:192`) reads
  `∀ i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω ↦ u p.1 p.2`:
  it measures the restriction to the **subtype** `Set.Iic i`, whose
  `MeasurableSpace` is `Subtype.instMeasurableSpace` and therefore comes from an
  *instance* `[MeasurableSpace ι]`. A `Clock` has no such instance — its
  σ-algebra is the field `Q.measurableSpace` — so the subtype comparison cannot
  even be stated without `@`, and instance search, being syntactic, will not
  find it. Ours quantifies instead over an **extension** `Z` that agrees with `X`
  below `t` and is measurable on all of `ι × Ω`; the two formulations coincide
  when the clock's σ-algebra happens to be the instance, and neither implies the
  other as written. The same holds for the strongly measurable variant
  `MeasureTheory.IsStronglyProgressive` (`:262`), which is what the stopping
  results of Milestone 9 consume and which this roadmap cites under its own name
  wherever an instance is available.
* `Clock.IsProgressiveComp Q X 𝓕`: the same statement for the **real
  functionals** of the process, `∀ h : E → ℝ` measurable, `(u, ω) ↦ h (Z u ω)`
  is `Q.measurableSpace ⊗ 𝓕 t`-measurable, together with
  `isMPSolutionFor_iff_forall_fdd` restated on it. The `E` valued form above is
  **not available over a bare `[MeasurableSpace E]`**: its only proof
  approximates `X s` by `X r` with `r` slightly above `s` and passes to the
  limit, and a limit of `E` valued measurable maps is measurable only when the
  diagonal of `E` is, which for an arbitrary σ-algebra it is not. The real form
  is, by the same argument run in `ℝ`, and it is what the criterion actually
  consumes — `mpFamily_sub_of_measurable_path` already takes
  `Measurable[Q.measurableSpace] fun u ↦ g (X u ω)` and not the measurability of
  `X` itself, and `stronglyMeasurable_integral_comp` is stated for a composite
  `g ∘ W`. Milestone 4 supplies the instance for the jump process
  (`measurable_uncurry_jumpProcess`), and it is the only construction in this
  roadmap whose state space carries no topology.
* `Clock.interval_subset_Iic`, `Clock.measurableSet_interval` and
  `Clock.measure_interval_ne_top`: every compensating interval lies below its
  right end, is measurable, and has finite mass. The last is what makes the
  compensator a bounded function of `ω` for a bounded `g`.
* `stronglyMeasurable_integral_comp`: `StronglyMeasurable.integral_prod_left`
  with both σ-algebras passed by hand, so that `Q.measurableSpace` and `𝓕 t` can
  be handed to it. Together with `MeasureTheory.Measure.integrableOn_of_bounded`
  (`MeasureTheory/Integral/IntegrableOn.lean:713`) — a bounded measurable
  function is integrable on a set of finite measure — this is what turns
  `Clock.IsProgressive` into strong adaptedness of the compensator.
* `mpFamily_sub_of_measurable_path`: for a measurable path,
  `Y t ω - Y s ω = f (X t ω) - f (X s ω) - ∫ u in Clock.interval q c s t, g (X u ω) ∂q`.
  This is `Clock.interval_union` plus `setIntegral_union`, and it is the identity
  that makes the right hand side of the finite dimensional criterion the
  increment of `Y`.
* `isMPSolutionFor_iff_forall_fdd`: `X` solves the martingale problem for `A` if
  and only if for all `s ≤ t`, all finite families `t 1 ≤ ... ≤ t n ≤ s` and all
  bounded measurable `h 1, ..., h n`,
  ```
  𝔼[(f (X t) - f (X s) - ∫ u in Clock.interval q c s t, g (X u) ∂q) * ∏ k, h k (X (t k))] = 0
  ```
  for every `(f,g) ∈ A`; and the same with `h k` bounded continuous when `E` is
  metrizable. The continuous form rests on the measurable one through exactly two
  statements of the roadmap **WeakConvergence**, and on nothing else:
  `integral_mul_ofReal_eq_zero_of_isMulSystem`, which carries the vanishing of
  `∫ g · f` from a multiplicative system of **real** functions to the whole
  σ-algebra it generates while the other factor stays `𝕂` valued, and
  `generateFromFuns_setOf_continuous_bounded`, which says that on a
  pseudo-metrizable space the bounded continuous real functions generate the
  Borel σ-algebra. The multiplicative system is the set of products
  `ω ↦ ∏ k, h k (X (r k) ω)` with `r k ≤ s` and `h k` bounded continuous; it is
  multiplicative because `Fin.append` concatenates two families, and
  `Fin.prod_univ_add` splits the product back. What is needed of the σ-algebra
  it generates is **one inequality and not an equality with `𝓕 s`**:
  `MeasurableSpace.comap (X r) _ ≤ generateFromFuns K` for every `r ≤ s`, by
  `MeasurableSpace.comap_iSup` and `MeasurableSpace.comap_comp` applied to that
  second statement. The hypothesis of the first on the constant function,
  `∫ g = 0`, is the right hand side at `n = 0`, where the empty product is `1`.
  Metrizability is consumed in the second and nowhere else. This is the statement that turns every later theorem into a
  statement about finite dimensional distributions, and it is the reason the
  index needs no order structure beyond a preorder. The filtration is the
  natural one of `X`, `𝓕 s = ⨆ r ∈ Set.Iic s, MeasurableSpace.comap (X r) _`,
  and that is a hypothesis of the equivalence and not a convention: the right
  hand side tests against the coordinates alone, so for a larger filtration the
  direction from right to left fails. The second hypothesis that cannot be
  dropped is `Clock.IsProgressive Q X 𝓕`: the right hand side is a family of
  vanishing integrals and constrains no measurability, while the left hand side
  unfolds to `StronglyAdapted 𝓕 Y ∧ …`; and for a fixed `ω` the integrand
  `fun u ↦ g (X u ω)` need not be `Q.measurableSpace`-measurable under
  `∀ t, Measurable (X t)` alone, so that both compensators are the junk value `0`
  and the increment identity fails.
* `pathCylinders`, `isPiSystem_pathCylinders` and `generateFrom_pathCylinders`:
  the finite intersections `⋂ i ∈ u, π i ⁻¹' B i` over a `Finset` of times form a
  π-system, and they generate `⨆ i, MeasurableSpace.comap (π i) _`. They are
  attached to a family of coordinates `π : ι → F → E` and to nothing else — no
  order on the index, no measure, no process — and they are the π-system of the
  finite dimensional criterion as well as of `prop:uniqfromprop` in Milestone 6.
* `mpFamily_sub_of_isProgressive`, `stronglyAdapted_mpFamily_of_isProgressive`
  and `integrable_mpFamily_of_bounded`: the increment identity, the adaptedness
  and the integrability of the test processes, each read off
  `Clock.IsProgressive` and the bounds on `(f,g)`, with no hypothesis on `P`
  beyond `IsFiniteMeasure`. The first of them is `mpFamily_sub_of_measurable_path`
  with the path measurability supplied instead of assumed, and it is where the
  agreement of the progressive version `Z` with `X` below `t` is consumed: both
  compensating windows lie in `Set.Iic t`, so `setIntegral_congr_fun` exchanges
  the two.
* `integral_sub_mul_eq_zero_of_martingale`: a martingale increment integrates to
  zero against every bounded real `𝓕 s`-measurable test function. This is the
  whole of the direction from left to right of the criterion, and it is a
  statement about martingales alone. Its proof is the pull-out property
  `condExp_smul_of_aestronglyMeasurable_left` together with `integral_condExp`:
  `∫ Z • (Y t - Y s) = ∫ P[Z • (Y t - Y s) | 𝓕 s] = ∫ Z • P[Y t - Y s | 𝓕 s]`,
  and the last conditional expectation is `0`.
* `setIntegral_eq_of_forall_cylinder`: two integrable functions whose set
  integrals agree on the cylinders of the past agree on the whole past. This is
  the direction from right to left, and it is `MeasurableSpace.induction_on_inter`
  over `pathCylinders` read on the times below `s`: the complement step is
  `integral_add_compl` against the empty cylinder — which is why the criterion
  has to be tested at `n = 0` as well, the total integrals being the base of the
  complement — and the countable step is `integral_iUnion`.
* The consequence that the solution property depends only on the finite
  dimensional distributions of `X`.

**Acceptance examples.**

* **The manuscript's `ex:determining`, verbatim.** `𝓕 t = σ(X s : s ≤ t)`,
  `F = D ι E` or `C ι E`, `D ⊆ ι` dense, and
  `𝓩° t = {fun ω ↦ ∏ i ∈ Finset.range n, h i (ω (t i)) | t i ∈ D ∩ Set.Iic t,
  h i ∈ Cb(E)}`. `isDetermining_products` must return exactly this set as
  determining, and the multiplicative system it feeds to `induction_on_mulSystem`
  of **WeakConvergence** Milestone 5 is the same `K` that milestone's own
  acceptance example uses for the martingale property. The two roadmaps meet on
  one instance, and that they name it the same way is part of the test.
* **The filtration is a hypothesis, not a convention.** Take `Ω = F × {0,1}` with
  the second factor independent of `X` and fair, `𝓖 t` the σ-algebra generated
  by `X` up to `t` **and** the coin, and `Y t = mpProcess q c X f g t + coin`.
  The right hand side of `isMPSolutionFor_iff_forall_fdd` tests only against
  products in the coordinates of `X`, so it cannot see the coin, while
  `IsMPSolutionFor A q c X 𝓖 P` for the enlarged `𝓖` is a strictly stronger
  statement. This is the instance on which the direction from right to left
  fails for a larger filtration, and it is why the equivalence names the natural
  filtration.
* **A process that is measurable at every time and progressive at none.** Take
  `ι = ℝ` with `q` the Lebesgue measure on `[0,1]`, `E = ℝ`, `g = id`, and any
  `X` whose sections `X t` are measurable while `(u, ω) ↦ X u ω` is not jointly
  measurable. Every hypothesis of the criterion except `Clock.IsProgressive`
  holds, `fun u ↦ g (X u ω)` is not `q`-measurable for some `ω`, and the Bochner
  integral returns its junk value `0` there; `mpFamily_sub_of_measurable_path`
  then fails at that `ω`, and with it the direction from right to left. This is
  the instance that shows `Clock.IsProgressive` is a hypothesis and not a
  convenience.
* **Bounded continuous suffices exactly when `E` is metrizable.** For `E = ℝ`
  both forms of `isMPSolutionFor_iff_forall_fdd` hold, and the bounded
  continuous form is the one Milestone 10 consumes. For `E` a measurable space
  with no topology only the bounded measurable form is even statable, which is
  why the milestone carries both and marks which hypothesis each needs.

## Milestone 5: mixtures, shifts and the restart lemma

* `MPSolutions.isConvex` and, more generally,
  `MPSolutions.integral_mem`: if `ϑ ↦ P ϑ` is a measurable family of solutions
  and `∫ 𝔼^{P ϑ}|Y t| ∂ν < ∞` for every `Y` and `t`, then `∫ P ϑ ∂ν` is a
  solution. Both directions of the corresponding disintegration statement when
  `E` is standard Borel.
* Fix `[AddCommMonoid ι]` with a compatible order. A `Shift` on `F` is a family
  `θ r : F → F` of measurable maps with `π t ∘ θ r = π (r + t)`.
* `ShiftSystem 𝓧°`: a family `𝓧° r` of families of `StronglyAdapted` processes
  (`Mathlib/Probability/Process/Adapted.lean:105`; `Adapted` is a different
  notion since 2026-01-13, see Milestone 9) with
  `𝓧° 0 = 𝓧°` such that every `Ŷ ∈ 𝓧° r` satisfies
  `Ŷ t ∘ θ r = Y (r + t) - Y r + κ` for some `Y ∈ 𝓧°` and some `𝓕° r`-measurable
  and bounded `κ`, and such that `θ r` is measurable from the past at `r + s` to
  the past at `s`.
* `isShiftSystem_mpFamily`: `mpFamily A q c π` carries a shift system, with the
  shifted problem equal to the original one and `κ = f ∘ π r`. It rests on
  `Clock.IsShiftInvariant` of Milestone 1 through the single change of variables
  `Clock.setIntegral_shift`, on `⊥ = 0`, on the pointwise path measurability
  `Measurable[q] (fun u ↦ g (π u f))` that keeps both compensators away from the
  junk value `0`, and on the adaptedness of the test processes, which is a
  statement about the filtration and the clock and belongs with
  `Clock.IsProgressive` rather than here. It needs **no** order beyond a
  preorder: the totality that `ex:shiftXA` uses sits inside
  `Clock.IsShiftInvariant` and nowhere else, which is the point of stating the
  clock condition as the identity of windows rather than as `q (r + B) = q B`.

  The two extra clauses are the ones a first draft of this milestone left out.
  The measurability clause is `\JS`, III.2.39(i); the manuscript's proof of
  `lem:restart` uses it in the sentence "`(Z°_s ∘ θ r)(X)` is
  `σ(X(u) : u ≤ r+s)`-measurable". The bound on `κ` is the measure free
  surrogate for the manuscript's `κ̃ ∈ L¹(P)`, which a structure that knows no
  measure cannot state; in `ex:shiftXA` it is `κ = f ∘ π r` with `f` bounded.
* `shiftMeasurable_of_natural`: the natural filtration of the coordinates
  satisfies the measurability clause, and the whole content is
  `Shift.eval_comp`. This is why the clause costs nothing in the canonical case.
* `restart`: let `X` be adapted and solve the martingale problem for `𝓧°` with
  respect to `𝓖`, with `Y u ∘ X` integrable for every `Y ∈ 𝓧°`; let `r : ι` with
  `r ≤ r + u` for every `u`, and let `Z ≥ 0` be bounded and `𝓖 r`-measurable.
  Then the law of `X (r + ·)` under `Z • P` solves the martingale problem for
  `𝓧° r`. Everything in Milestone 6 rests on it.

  Three hypotheses beyond the shift system, each used once. `X` adapted and
  `r ≤ r + u` are the two halves of the manuscript's step "so is `Z`, because
  `𝓖 r ⊂ 𝓖 (r+s)`". Integrability of the base family is the last line of the
  manuscript's proof, and it has to be a hypothesis because Mathlib's
  `Martingale` is `StronglyAdapted` plus the conditional expectation identity
  and carries no integrability.

  The normalisation `𝔼[Z] = 1` is **not** among the hypotheses: it plays no part
  in the martingale property. It is `isProbabilityMeasure_map_withDensity_ofReal`,
  which says that the restarted measure is a probability measure exactly when the
  density has expectation one.

  The determining set `𝓩°` of the manuscript's proof is not needed: the
  conditional expectation is identified against *all* sets of `𝓕° s` through
  `ae_eq_condExp_of_forall_setIntegral_eq`
  (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:253`). What the
  determining set buys on paper — testing against a small class — is bought here
  by the σ-algebra itself, and `def:canonical` does not have to exist first.
* `restart_canonical`, the special case `Ω = F`, `X = id`, where the conclusion
  reads `(Z • P).map (θ r) ∈ MPSolutions (𝓧° r)`. The two hypotheses of `restart`
  that speak of `X` become `Measurable id`.
* The three measure theoretic inputs, each stated for a general reweighted image
  measure `(Z · P) ∘ ψ⁻¹` and none of them in Mathlib in this shape:
  `integral_map_withDensity_ofReal` and `integrable_map_withDensity_ofReal`,
  which transport an integral and integrability through the density and the map
  at once, and `integral_smul_martingale_eq`, that a martingale tested against a
  **bounded weight** measurable for the earlier past has equal integrals at the
  two times. Mathlib has the **indicator** case, as
  `MeasureTheory.Martingale.setIntegral_eq`
  (`Probability/Martingale/Basic.lean:100`, in v4.33.1 and on `master`, checked
  2026-09-17): `∫ ω in s, f i ω = ∫ ω in s, f j ω` for `s ∈ ℱ i` and `i ≤ j`,
  with the one sided versions `Supermartingale.setIntegral_le` (`:163`) and
  `Submartingale.setIntegral_le` (`:242`). For a **bounded weight** in place of
  the indicator it has nothing. The step is
  the pull-out property `condExp_smul_of_aestronglyMeasurable_left`
  (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean:223`) followed by
  `integral_condExp` (`…/ConditionalExpectation/Basic.lean:236`), and the weight
  of the restart lemma — a density times an indicator — is exactly why the
  indicator form would not have sufficed.

**Acceptance examples.**

* **The shifted problem of the manuscript's `ex:shiftXA`.** For the family
  `mpFamily A q c X` with a shift invariant clock **over a linearly ordered
  index**, the shifted family `𝓧° r` is again `mpFamily A q c X` up to the
  `𝓕° r`-measurable constant `κ` = the compensator up to `r`.

  The linear order belongs in that sentence, and the multiparameter clock is the
  instance that shows it. Over `ι = [0,∞)^2` with Lebesgue measure, `f = 0` and
  `g = 1`, the test process is `Y t ω = - t₁ t₂`, and the shift identity
  `Y' t (θ r ω) = Y (r + t) ω - Y r ω + κ ω` reads
  `t₁ t₂ = (r₁ + t₁)(r₂ + t₂) - r₁ r₂ - κ ω`, that is
  `κ ω = r₁ t₂ + t₁ r₂`. The right hand side depends on `t` and `κ` does not, so
  no `κ` exists unless `r = 0`. The step that fails is the substitution
  `v = r + u` of `ex:shiftXA`, which identifies `r + ⟨0,t⟩` with `⟨r, r+t⟩`; see
  `Clock.interval_add` in Milestone 1 for what that identification costs.
  Instantiated at the Poisson process of Milestone 4 and
  `r = 1`: `θ 1` is the time shift, and `restart` says that under `Z • P` the
  process `N (1 + ·) - N 1` is again a Poisson process. That the constant `κ`
  cannot be dropped is visible there — `N (1 + t)` is not a martingale after
  compensation by `t` alone, only `N (1+t) - N 1` is.
* **A clock that is not shift invariant breaks the shift system.**
  `q = Measure.dirac 1` on `Set.Ici (0:ℝ)` and `r = 1/2`. The compensator of the
  shifted process integrates over `Clock.interval q c 0 t` translated by `1/2`,
  which carries no atom, so `mpFamily A q c X ∘ θ r` is not of the required
  form. `Clock.IsShiftInvariant` is therefore a hypothesis of the shift system
  and not of the clock, and this is the instance that shows it.
* **Mixtures, at the smallest scale.** Two solutions `P 0` and `P 1` of the same
  martingale problem with different initial laws `δ 0` and `δ 1`: the mixture
  `(P 0 + P 1)/2` is a solution with initial law `(δ 0 + δ 1)/2`, by
  `MPSolutions.isConvex`. It is **not** the solution started from the mean, and
  no item of the milestone claims it is; the disintegration statement is what
  recovers `P 0` and `P 1` from it, and requires `E` standard Borel.

## Milestone 6: uniqueness and the Markov property, without an operator

**The converse direction is deliberately absent, and it is not ours to supply.**
What is below runs from uniqueness to the Markov property: if the one
dimensional distributions are determined, every solution is Markov and the
solution is unique. Ethier--Kurtz, Theorem 4.4.1 runs the other way --- a Markov
process is the unique solution of the martingale problem for its generator ---
and it is not here, because it is a *semigroup* criterion: it asks for `A`
linear and dissipative and for a subrelation `A'` with
`range (lam - A') = domain A' = L` separating, for some `lam > 0`, which is a
Hille--Yosida condition. The manuscript behind this roadmap takes uniqueness
from the theorem below together with duality instead, and leaves Theorem 4.4.1
and Corollary 4.4.4 out by design.

That makes the missing direction a natural piece of joint work rather than a
gap: the `OneParameterSemigroups` roadmap supplies Hille--Yosida, Theorem 4.4.1
sits directly on it, and this milestone supplies the converse. Neither roadmap
has the full uniqueness theory alone. Whoever takes it up should state it there
and cite this milestone, not the other way round.

**The Markov free half, and it is the bottom of the milestone.** Uniqueness of
the finite dimensional distributions is not a Markovian fact, and the milestone
is built so that this is visible: the condition the uniqueness argument consumes
is `PropagatesAgreement`, and every statement in this group is free of shifts,
of determining sets and of `restart`.

* `PropagatesAgreement 𝓕° π N`: for `P, Q ∈ N`, `s ≤ t` and every bounded
  non-negative `𝓕° s`-measurable weight `Z`, agreement of the `Z`-weighted law
  of `π s` forces agreement of the `Z`-weighted law of `π t`. The weight is a
  parameter and not a σ-algebra: the unconditional form
  `P = Q on 𝓕° s ⟹ P = Q on 𝓕° s ⊔ σ (π t)` is a different and unusable
  condition, because the induction below delivers agreement on finitely many
  coordinates and that form demands agreement on the whole of `𝓕° s`.
* `weightedLaw π P Z t`, the law of `π t` under `Z • P`, together with
  `weightedLaw_one` and `weightedLaw_indicator_apply`. It is written as
  `restart` writes the reweighting, so that the initial law of a restarted
  solution is `weightedLaw π P Z r` on the nose.
* `weightedLaw_univ`, that the total mass of a weighted law is the mass of the
  density and so does not depend on the time at which the coordinate is read;
  and `weightedLaw_const_mul`, that the weighted law is positively homogeneous
  in the weight. These two are what the normalisation of `lem:propagation`
  consists of: the first is "take `h ≡ 1`", the second is "divide by `E[Z]`".
* `isFiniteMeasure_weightedLaw` and `propagatesAgreement_of_transfer`: a
  weighted law is finite when the weight is bounded and the measure is, and a
  set propagates agreement as soon as the integral of each member of a
  separating family against the weighted law at `t` is the integral of some
  function against the weighted law at `s`, by a map that does not depend on
  the member of `N`. Nothing is asked of that map — no measurability, no
  boundedness, no integrability — because equal measures integrate every
  function alike. It is the interface through which duality reaches
  `prop:uniqfromprop`; see `duality_weighted` in Milestone 8, whose transfer
  operator is `Λ s t y x = 𝔼[f (x, Y^y T)]`.
* `measure_cylinder_inter_eq_of_propagatesAgreement`: the induction over a
  chain, with the top coordinate's set a separate argument. That separation is
  the content of the step -- the induction hypothesis is used with the top set
  shrunk -- and it runs over a **preorder**.
* `measure_cylinder_eq_of_propagatesAgreement`: the finite dimensional
  distributions agree along every monotone chain.
* `pathCylinders`, `isPiSystem_pathCylinders`, `generateFrom_pathCylinders`: the
  measurable cylinders of a path space, indexed by a `Finset` of times, and the
  two facts the extension theorem asks for.
* `measure_biInter_eq_of_propagatesAgreement`: the same over an unordered finite
  set of times. This is the **one** place where the linear order on the index is
  consumed, through `Finset.orderIsoOfFin`.
* `eq_of_propagatesAgreement` and `subsingleton_of_propagatesAgreement`: two
  members of `N` with the same law at `⊥` are equal. The σ-field of the path
  space is a hypothesis, `mF = ⨆ i, comap (π i)`, and the filtration enters only
  through `∀ u ≤ v, Measurable[𝓕° v] (π u)` -- not as the canonical filtration,
  so the statements hold for every filtration the coordinate process is adapted
  to.

Hypotheses of the Markov half: a shift system, a determining set for every
`𝓧° r`, and uniqueness of the one dimensional distributions of the shifted
problems.

* `propagatesAgreement_of_unique_onedim`: under a shift system and uniqueness of
  the one dimensional distributions of every shifted problem, a set of
  probability solutions of `𝓧° 0` propagates agreement. This is
  `lem:propagation`, it is the first statement of the milestone that is
  Markovian, and it is what turns the group above into `thm:absuniq`(b) by one
  application of `eq_of_propagatesAgreement`. It rests on `restart_canonical`,
  on `Shift.eval_comp` for `π 0 ∘ θ s = π s`, and on the normalisation
  `Z / E[Z]`, which needs the degenerate case `E[Z] = 0` treated separately.

  Three hypotheses on the index replace (T4): `⊥ = 0`, which is what makes
  `π ⊥ ∘ θ s = π s`; `r ≤ r + u`, which is `restart`'s own; and `s ≤ t` yields
  `u` with `t = s + u`, which is (T4) itself and is used exactly once, to name
  the time at which the shifted problem is read. The integrability proviso of
  `lem:restart` is carried as a hypothesis on the members of the set, as the
  manuscript carries it.

  A determining set is **not** among its inputs. It was, as long as `restart`
  was stated after the manuscript, whose proof identifies the conditional
  expectation through `def:canonical`(ii); the proof of `restart` in Milestone 5
  tests against every set of `𝓕° s` instead, so `𝓩°` never enters.
* `isMarkov_of_unique_onedim`: every solution is Markov, in general time
  inhomogeneously — for `f` bounded measurable and `r, t : ι`,
  `𝔼[f (X (r + t)) | 𝓖 r] =ᵐ 𝔼[f (X (r + t)) | X r]`. This is `thm:absuniq`(a).
  It rests on `restart` in the two level form, applied **twice at the same
  shift `r`** to the two weights of the manuscript proof, and on the pull-out
  property of the conditional expectation in both directions
  (`condExp_smul_of_aestronglyMeasurable_left` and `..._right`), which is the
  self adjointness `E[U · E[V|𝓜]] = E[E[U|𝓜] · V]` that the last step asks for.

  The one dimensional hypothesis is consumed **at the single shift `r`** and not
  at every shift. That is the difference to `lem:propagation`, whose induction
  walks through the shifted problems, and it is why this statement needs neither
  (T2a) nor (T4): the index carries a preorder, a bottom element and the
  additive structure, and `hsub` does not occur. `rem:chainonly` says as much of
  the manuscript proof; here it is the shape of the hypothesis.

  `X` is an arbitrary measurable process and not the coordinate process, which
  is `rem:restarttwolevel`: the first weight `1_{F₀}` is `𝓖 r`-measurable and
  need not be a functional of the path.

  Two auxiliary statements carry it.
  * `map_withDensity_ofReal_eq_of_setIntegral_eq`: two bounded non-negative
    densities that integrate alike over every set of a sub-σ-algebra give the
    same law to every map measurable for that sub-σ-algebra. It is the step that
    identifies the initial laws of the two restarted measures, and it is stated
    for a general sub-σ-algebra because that is all its proof uses.
  * `stateSigma`, with `stateSigma_eq_comap`: the σ-algebra
    `σ(X r) = MeasurableSpace.comap (X r)` the Markov property conditions on,
    as a definition rather than a local abbreviation. A σ-algebra introduced
    inside a proof by `set` or `let` enters the local instance cache and
    displaces the ambient `MeasurableSpace Ω`, so that `Measurable f` silently
    becomes a statement about the sub-σ-algebra; the named definition is a term
    and not a local hypothesis, and the ambiguity does not arise.

  The weight `Z₂ = E[1_{F₀} | σ(X r)]` is carried in the truncated form
  `max 0 (min 1 ·)`. `restart` asks for the bounds on the weight pointwise and a
  conditional expectation has them almost everywhere; the truncation is
  `StronglyMeasurable[σ(X r)]` and bounded on the nose and almost everywhere
  equal, and every use of the weight is an integral. The degenerate case
  `P(F₀) = 0`, which the manuscript excludes by hypothesis, is split off instead,
  so the conclusion holds for every set of `𝓖 r`.
* `subsingleton_mpSolutions_of_unique_onedim`: when `ι` is linearly ordered, the
  set of solutions with a given initial law has at most one element. This is
  `thm:absuniq`(b), and it is `propagatesAgreement_of_unique_onedim` composed
  with `subsingleton_of_propagatesAgreement`; the linear order is (T2a) and is
  spent only in the sorting step `measure_biInter_eq_of_propagatesAgreement`.
* `isShiftSystem_mpFamily_lebesgueClock` and
  `subsingleton_mpSolutions_mpFamily_lebesgueClock`: the same two statements at
  `ι = ℝ≥0` and the clock of Milestone 4, with every hypothesis about the index
  or the clock discharged. `⊥ = 0` is `NNReal.bot_eq_zero`, `r ≤ r + u` is
  `le_self_add`, (T4) is `exists_add_of_le`, (T2a) is the order `ℝ≥0` carries,
  and the shift system is `lebesgueClock_isShiftInvariant` of Milestone 1. What
  survives speaks of the operator, the shift and the filtration alone.

  This is the measure of the milestone against emptiness, and it is a different
  question from provability: the abstract statements above hold over a preorder
  and a clock hypothesis that the zero measure satisfies, so without a witness
  for that hypothesis one cannot tell a theorem from a vacuity.
* `eq_of_forall_onedim`: two solutions with the same initial law have the same
  finite dimensional distributions.
* The classical statement, as an instance: for `E` metrizable and
  `A ⊆ Cb(E) × Bdd(E)`, if any two solutions of the martingale problem for
  `(A, μ)` have the same one dimensional distributions for every `μ`, then every
  solution is Markov and the solution is unique.
* `isStrongMarkov`: with càdlàg paths, `A ⊆ Cb(E) × Bdd(E)` and the shift system
  measurable, the Markov property holds at every almost surely finite stopping
  time taking countably many values, and, when a measurable family `x ↦ P x` of
  solutions from each starting point exists, at every almost surely finite
  stopping time. State the transition operator `T t f x = ∫ f (ω t) ∂(P x)` and
  prove `𝔼[f (X (τ + t)) | 𝓖 τ] =ᵐ T t f (X τ)`.

**The seam with Milestone 4: what `eq:absonedim` costs on the data.** The
hypothesis `honedim` is a statement about the *path space*, and Milestone 4
proves uniqueness of the one dimensional laws for an *arbitrary* process. Three
statements join them, and they are of three different kinds — an accounting
step, a step that is free, and a path regularity that neither milestone states.

* `measure_map_eq_of_forall_integral_eq`: two finite measures whose push
  forwards integrate every measurable real function bounded by `1` alike are
  equal. Milestone 4 determines the one dimensional distributions through
  integrals of bounded functions and Milestone 6 asks for them as measures;
  indicators are the test functions and finiteness is what undoes
  `ENNReal.toReal`. It is the only genuinely new accounting between the two.
* `onedim_mpFamily_jumpOperator`: `honedim` discharged on the data of
  Milestone 4 for a rate bounded by `L`. The quantifier over the shift `r` costs
  nothing and `r` does not occur in the proof, because `isShiftSystem_mpFamily`
  makes the shifted problem the original one: `𝓧₀ = fun _ ↦ mpFamily A Q c π` as
  a set. So the shift is not a step, and `eq:absonedim` at every `r` is one
  statement about `mpFamily` and not a family of them.
* `IsRightLocallyConstant` and `measurable_uncurry_of_isRightLocallyConstant`:
  the coordinate process of a right continuous path space is measurable in time
  and sample point **jointly**. This is the input `onedim_mpFamily_jumpOperator`
  carries and the path space of this milestone does not supply:
  `hgen : mF = ⨆ i, comap (π i)` gives measurability of each coordinate and
  nothing about the pair. On the full function space `ℝ≥0 → E` even the weaker
  `hpath` of `isShiftSystem_mpFamily` fails, since a path need not be measurable
  in time; on the subspace of time measurable paths the evaluation map is still
  not jointly measurable. Path regularity is therefore a hypothesis of the seam
  and not a convenience. The proof is the dyadic approximation `dyadAbove` from
  **above** — right continuity controls the path to the right of a time and
  nothing to the left — with `le_dyadAbove` and `dyadAbove_lt`; each stage
  factors through the countable grid and is jointly measurable by
  `measurable_from_prod_countable_right` with no regularity at all, and the
  regularity enters only in the limit.

  `Nat.ceil` and not `Nat.floor`, and the reason is the library:
  `Nat.measurable_floor` carries `[IsStrictOrderedRing R]` and `ℝ≥0` is a
  semiring, while `Nat.measurable_ceil` has no such hypothesis.

**The canonical path space.** The milestone's path space is a hypothesis — `F`,
`π`, `Shift F π`, `𝓕₀` — and `Shift` has no witness. These four statements build
one, and they are what the instances of the milestone stand on.

* `RightContinuousPath E`, the paths `ℝ≥0 → E` on which
  `IsRightLocallyConstantPath` holds, with `coordinate`, the evaluation map, and
  `measurable_coordinate`. The σ-field is the **trace of the product σ-field**,
  `MeasurableSpace.comap toFun`; taking it as the σ-field generated by the
  coordinates proves the same theorems with more work.
* `generateFrom_coordinate`: the σ-field of `RightContinuousPath E` is the one
  the coordinates generate, which is `hgen`. `MeasurableSpace.comap_process_pi`
  is the whole proof, because `fun f u ↦ coordinate u f` is `toFun`.
* `measurable_uncurry_coordinate`: the coordinate process is measurable in time
  and path jointly, which is `hjoint`, and `measurable_comp_coordinate` is
  `hpath` as its corollary at a fixed path.
* `pathShift`, the `Shift` structure on it: `θ r f = fun u ↦ f (r + u)`, whose
  `eval_comp` is `rfl` and whose measurability is `measurable_pi_lambda`. Right
  local constancy is preserved by translation, so the space is closed under it.
  `pathFiltration`, the natural filtration of the coordinates, carries `hadapt`
  (`measurable_pathFiltration`) and `hsm` (`shiftMeasurable_pathFiltration`),
  the second by `shiftMeasurable_of_natural` because `pathFiltration_eq` is
  `rfl`.
* `stronglyAdapted_mpFamily_coordinate`: the test processes of `mpFamily` are
  adapted to the natural filtration of the coordinates, which is `hY`. The state
  term is adapted by `measurable_pathFiltration`; the compensator asks for the
  joint measurability of `measurable_uncurry_of_isRightLocallyConstant`
  **relative to the sub-σ-algebra** `𝓕₀ t`, which is
  `measurable_uncurry_min_of_isRightLocallyConstant`: the truncation `min · t`
  keeps the approximation `min (dyadAbove n s) t` countably valued and inside
  the window, where the coordinates are measurable for `𝓕₀ t`.
* `integrable_mpFamily_coordinate`: the test processes are integrable under
  every **finite** measure, which is `hint`. Both terms are bounded, the state
  term by the bound on `p.1` and the compensator by the bound on `p.2` times the
  mass of the window (`Clock.measure_interval_ne_top`). Finiteness is the
  weakest hypothesis under which the statement holds: a bounded non-zero
  function is not integrable against an infinite measure. `hint` of
  `subsingleton_mpSolutions_of_unique_onedim` therefore quantifies over
  probability measures, which is all its proof applies it to.
* `jumpPath` and `isRightLocallyConstantPath_jumpProcessE`: the jump process of
  Milestone 4 read as a map from its construction space `(ℕ → E) × (ℕ → ℝ)` into
  `RightContinuousPath E`, with the right local constancy of its paths — true
  there because nothing happens between two jump times — and its measurability,
  which is `measurable_of_measurable_toFun` on
  `measurable_jumpProcessE_apply`. The right local constancy holds at **every**
  sample point and under no hypothesis, which is what a map into a subtype
  needs: an almost sure statement would define the map off a null set only.
  `coordinate_jumpPath`, the statement that the coordinate of the image is the
  process, is `rfl`.
* `jumpPathD` and `measurable_jumpPathD`: the same map into the Skorokhod space
  `D(ℝ≥0, E)` of the roadmap **SkorokhodSpace**, for `E` Polish and complete.
  Proved (2026-09-18). This is the target the convergence theorems of Milestone 8
  there consume — `tendstoInDistribution_eval` is hypothesis (a) of
  `mpSolution_of_tendsto` (Milestone 10) and is stated over `D(ι, E)` and over
  nothing else — so a family of jump processes is a family those theorems apply
  to only once it is written in this space. Measurability is
  `SkorokhodSpace.measurable_of_measurable_eval` coordinatewise, on
  `measurable_jumpProcessE_apply`.

  **Two things separate it from `jumpPath`, and both are settled here.**
  The index bundle at `ℝ≥0` is the first, and it is supplied: `D(ℝ≥0, E)` became
  an object of the development on 2026-09-18 with `NNReal.instAdditiveDist`,
  `NNReal.instBasePoint` and `NNReal.instHasCountableCore`, and the crossing of
  the two indices is `IsCadlag.comp_coe_nnreal`. The second is that **the
  defining property of this space does not hold at every sample point**, where
  the defining property of `RightContinuousPath E` does: right local constancy
  survives the explosion set (`eventuallyEq_nhdsGE_stepPath`, no hypothesis at
  all), while the left limits do not, and `isStepPath_jumpProcessE` carries the
  non explosion of the jump times for exactly that reason. `jumpPathD` is
  therefore defined by cases on a measurable set, with the **constant path at the
  starting state** `ω.1 0` off it, and the statement that it agrees with the
  process is an almost sure one. That is the standing rule of 2026-09-18 read on
  a definition rather than on a theorem: the non explosion is in the hypothesis,
  and the junk value is named instead of being called harmless.

  **The set is `CadlagSetE`, and it is not `NonExplosiveE`.** Non explosion alone
  does not make the path a step path: `isStepPath_jumpProcessE` asks two things,
  and the second is that **every holding time is strictly positive**, without
  which two jump times coincide and the local constancy that carries the left
  limits is not available. `CadlagSetE lam = {ω | ∀ n, 0 < ω.2 n} ∩ NonExplosiveE lam`
  is exactly the hypothesis of that theorem read as a set, and
  `measurableSet_cadlagSetE` is its measurability, from
  `measurableSet_nonExplosiveE` and a countable intersection. Both halves are
  almost sure under `jumpMeasure`, and in different ways: the positivity is free
  (`ae_pos_snd_jumpMeasure`, no hypothesis at all, the waiting law being
  exponential), the non explosion is a hypothesis of the caller
  (`ae_mem_nonExplosiveE_jumpMeasure` and the criteria above it). That asymmetry
  is why the two are carried separately and only joined in
  `ae_mem_cadlagSetE_jumpMeasure`.
* `isCadlag_nnreal_jumpProcessE_of_mem`, `jumpPathD_toFun_of_mem` and
  `jumpPathD_toFun_of_not_mem`: the path is càdlàg over `ℝ≥0` on `CadlagSetE`,
  the coordinate of the image is the process there, and off it the image is the
  constant path. Proved (2026-09-18). The third is stated so that the junk value
  is a theorem and not a reading of the definition.
* `ae_mem_cadlagSetE_jumpMeasure` and `ae_jumpPathD_toFun_eq`: almost every
  sample point lies in `CadlagSetE`, and there the Skorokhod path map agrees with
  the process **at every time at once**. Proved (2026-09-18). The second is an
  almost sure identity of *paths* and not of a fixed coordinate, which is what
  every distributional conclusion of Milestones 7 to 11 needs: a coordinatewise
  statement would give a null set per time and no null set for the path.
* `map_eval_map_jumpPathD` and `isProbabilityMeasure_map_jumpPathD`: the law
  `(jumpMeasure mu nu).map (jumpPathD lam)` on `D(ℝ≥0, E)` is a probability
  measure whose coordinate at `t` is the law of `jumpProcessE lam t`. Proved
  (2026-09-18). This is the form in which the path law is compared with anything
  known: every identification already proved for the process —
  `jumpMeasure_map_jumpProcessE_zero` at the start, `poissonMeasure` at the
  Poisson rate — becomes one for the path law without a second computation.
* `eq_map_jumpPathD_of_forall_dense`: a probability measure on `D(ℝ≥0, E)` whose
  finite dimensional distributions agree with those of
  `(jumpMeasure mu nu).map (jumpPathD lam)` along **some dense set of times** is
  that law. Proved (2026-09-19). This is
  `SkorokhodSpace.eq_of_forall_dense_forall_integral_evalPi_eq` (**SkorokhodSpace**
  Milestone 6) read at the index `ℝ≥0`, which is densely ordered and has no
  greatest element, so the two conditions that statement puts on the times
  collapse into density; the countable core is `NNReal.instHasCountableCore`.

  **It says what the item above does not.** The coordinate identification pins
  down the one dimensional distributions and nothing more — a law on a path space
  is not determined by its marginals. Here the law itself is determined, and what
  is spent is the finite dimensional family together with the density of the
  times: no modulus of the paths, no compact containment, and no non explosion
  beyond what `jumpPathD` has already consumed. No time is asked to be a
  continuity time either, and that is the difference from Milestone 8 of
  **SkorokhodSpace**: there two sequences are compared and the fixed
  discontinuities of the limit have to be avoided, while an identification at
  fixed times has no limit to avoid.
* `eq_map_jumpPathD_poisson_of_forall_dense`: the same on the Poisson data, so
  the hypotheses on `E` and on the rate are jointly discharged. Proved
  (2026-09-19). Read together with `map_eval_map_jumpPathD_poisson` it says that
  the Poisson path law on `D(ℝ≥0, ℕ)` has Poisson marginals and is the only law on
  that space with its finite dimensional distributions along ℚ.

**Acceptance example.** `map_eval_map_jumpPathD_poisson`, proved (2026-09-18):
the Poisson data run through `jumpPathD` land in `D(ℝ≥0, ℕ)`, and the coordinate
of the resulting law at `t` is `ProbabilityTheory.poissonMeasure t`. It probes
two things at once and is worth stating for both. As an emptiness probe it shows
that `ℕ` carries the whole bundle the map asks of its state space —
`MetricSpace`, `BorelSpace`, `PolishSpace`, `CompleteSpace` — and that the non
explosion hypothesis is dischargeable on data (`ae_mem_nonExplosiveE_poisson`).
Beyond that it is an **independent control on a law of the Skorokhod space**:
`poissonMeasure` is defined with nothing of this development in it. The bridge
it needs is `jumpMeasure_map_jumpProcessE_poisson`, also proved (2026-09-18) —
`jumpMeasure_map_jumpProcess_poisson` is about `jumpProcess`, and the local
construction is a *different function*, agreeing with the old one only where the
holding times are strictly positive. That is almost everywhere and nowhere
guaranteed, so the identification is carried across and not reused.

**The path law has no fixed discontinuity, at any time whatever.** The
convergence statements of the roadmap **SkorokhodSpace**, Milestone 8 —
`SkorokhodSpace.tendsto_finiteDimensional_of_tendsto` and
`SkorokhodSpace.tendstoInDistribution_eval` — carry a hypothesis on the limit
law: at each time read off, the paths that jump there must carry no mass.
`SkorokhodSpace.exists_countable_dense_continuity` supplies such times for an
arbitrary law, and only a countable dense set of them. For the jump construction
the answer is the strongest one available, and it is proved (2026-09-18):

* `instNullSingletonClassExpMeasure`: the exponential law charges no point. It is
  `expMeasure_eq_withDensity` read as an absolute continuity against Lebesgue
  measure. Mathlib has the distribution function of `expMeasure`
  (`cdf_expMeasure_eq`) and not this.
* `jumpTimeE_succ_shift` and `measurable_jumpTimeE_snd`: the jump times split off
  their **first** increment, and are measurable in the waiting times alone. The
  recursion of `jumpTimeE` peels off the *last* increment, which is the right
  form for the step index and the wrong one here: the coordinate that
  `waitingMeasure_map_split` isolates is `ξ 0`.
* `expMeasure_one_setOf_div_add_eq`: for a divisor `c ≠ ⊤` and a shift `b`, the
  waiting times `u` with `ENNReal.ofReal u / c + b = a` are, off `Set.Iic 0`, at
  most one, so the exponential law gives them no mass. The three degenerate cases
  are settled by the finiteness of `a` alone: at `b = ⊤` and at `c = 0` the left
  hand side is `⊤`. The hypothesis `c ≠ ⊤` is **necessary** — there the quotient
  is `0` for every finite numerator and the set is everything when `b = a` — and
  free in the application, where `c` is an `ENNReal.ofReal`.
* `waitingMeasure_setOf_jumpTimeE_eq`, `jumpMeasure_setOf_jumpTimeE_eq` and
  `ae_forall_jumpTimeE_ne`: no jump time of index `≥ 1` has an atom at a finite
  value, first with the chain held fixed, then under `jumpMeasure`, then for all
  indices at once. The index is `n + 1` and not `n` because
  `jumpTimeE _ _ _ 0 = 0` is the convention that the path starts at time `0`, and
  that one *is* an atom.
* `continuousAt_jumpProcessE_of_forall_ne` and
  `continuousAt_nnreal_jumpProcessE_of_forall_ne`: off the jump times the path is
  locally constant, hence continuous, over `ℝ` and then over `ℝ≥0`. The window is
  the one the step index reads, and its two ends are produced differently: on the
  right the next jump time may be `⊤` — an absorbing state — and any real bound
  serves, while on the left it is finite because it is `≤ ENNReal.ofReal x`. Non
  explosion enters as the hypothesis of `NonExplosiveE` and is what makes the
  window exist; without it `stepIndex` returns its junk value and the path is
  locally constant at no time past the explosion.
* `leftLim_jumpPathD_eq_of_forall_ne`, `ae_leftLim_jumpPathD_eq` and
  `map_jumpPathD_setOf_leftLim_eq`: the Skorokhod path does not jump at a time
  that is no jump time; a fixed time is almost surely not a jump time; and the
  law `(jumpMeasure mu nu).map (jumpPathD lam)` gives, **for every** `t : ℝ≥0`,
  the set of paths continuous at `t` full measure. The only hypothesis is the non
  explosion, in the form `ae_mem_nonExplosiveE_jumpMeasure` states it.
* `map_jumpPathD_setOf_leftLim_eq_poisson`: the emptiness probe, on the Poisson
  data, where every hypothesis is discharged.
* `jumpMeasure_setOf_leftLim_jumpPathD_eq`: the same statement on the **sample
  space**, `(jumpMeasure mu nu) {ω | (jumpPathD lam ω)⁻ t = jumpPathD lam ω t} = 1`.
  That is the form the two convergence theorems for random variables take their
  hypothesis in, because it is the form a user of the structure has; here the two
  sets are the same by `rfl`, the event being a preimage under `jumpPathD`.
* `tendstoInDistribution_evalPi_jumpPathD` and
  `tendstoInDistribution_eval_jumpPathD`: a family of path valued variables
  converging in distribution to the path of the construction has its finite
  dimensional marginals converging, **at every countable family of times** and at
  every single time. These are
  `SkorokhodSpace.tendstoInDistribution_evalPi` and
  `SkorokhodSpace.tendstoInDistribution_eval` (roadmap **SkorokhodSpace**,
  Milestone 8) with their hypothesis `ht` discharged on the data of this
  milestone. The quantifier over the family costs nothing, because the previous
  item gives the hypothesis at *every* time rather than on a set the law
  concedes, so the caller chooses the times. Nothing is asked of the
  approximating variables beyond the convergence itself; they need not be jump
  constructions.

  **What these two still ask for, and where it comes from.** Their hypothesis is
  weak convergence *on the path space*, and an approximating family delivers
  convergence of the finite dimensional distributions along one dense set of
  times. The two are bridged by
  `SkorokhodSpace.tendstoInDistribution_eval_of_isTight_of_tendsto_finiteDimensional`
  (**SkorokhodSpace** Milestone 8, 2026-09-19), which adds tightness to the
  convergence along a dense `T` and returns the marginal at every time the limit
  law does not charge with a jump — in particular at times outside `T`, which is
  the whole point, since a time of the index set need stand in no relation to `T`
  at all. That bridge is stated over the index `ℝ`, inherited from
  `SkorokhodSpace.isCompact_closure_iff` of Milestone 7 there, while `jumpPathD`
  lands in `D(ℝ≥0, E)`; `SkorokhodSpace.isClosedEmbedding_extendNNReal`
  (**SkorokhodSpace** Milestone 9, proved 2026-09-19) is the item that joins the
  two, and it joins them once for all the declarations of that file which stand
  over `ℝ`, rather than repeating them.

  **What the crossing leaves to be said.** Three of the four pieces travel along
  the embedding on their own: tightness forward, because a continuous image of a
  compact set is compact; weak convergence backward, because the image is
  closed; and the coordinate at a nonnegative time, because the extended path
  has the same value there. The fourth is the hypothesis on the finite
  dimensional distributions, and it does not travel: a dense `T ⊆ ℝ≥0` is not
  dense in `ℝ`. The times to be added are the negative ones, where the extended
  path takes the value at `0`, so the `ℝ≥0`-form of the bridge,
  `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional_nnreal`, reads
  `Dense T` together with `(0 : ℝ≥0) ∈ T`, and each negative time is answered by
  the time `0` of `T`.

  **The bridge in the form this milestone consumes it** is
  `SkorokhodSpace.tendstoInDistribution_eval_of_isTight_of_tendsto_finiteDimensional_nnreal`
  (**SkorokhodSpace** Milestone 9, proved 2026-09-19): path valued variables on
  `D(ℝ≥0, E)`, tight laws, finite dimensional distributions converging along a
  dense `T ∋ 0`, and out comes convergence in distribution of the value at every
  nonnegative time the limit law does not charge with a jump. The evaluation
  step of that chain, `SkorokhodSpace.tendstoInDistribution_eval`, is stated over
  an arbitrary index and needed no crossing at all; the crossing is spent on the
  compactness criterion beneath it.

**The path law sent through the crossing.** The five statements of
**SkorokhodSpace** Milestone 9 are about a family of measures on `D(ℝ≥0, E)`, and
this development produces exactly one such family. Sending it through is the
acceptance example that milestone names, and it is proved (2026-09-19):

* `extendNNReal_jumpPathD_toFun` and `extendNNReal_jumpPathD_toFun_of_mem`: the
  crossing does not move a coordinate at a nonnegative time, so on the good set
  the crossed path is the process there. This is
  `SkorokhodSpace.extendNNReal_apply` together with `Real.toNNReal_coe`, and it
  is the statement the acceptance example of that milestone asks for.
* `measurable_extendNNReal_jumpPathD` and
  `isProbabilityMeasure_map_extendNNReal_map_jumpPathD`: the crossed path map is
  measurable, the crossing being an isometry, and its law is a probability
  measure. Every consumer over the index `ℝ` asks for both as instances.
* `map_eval_map_extendNNReal_map_jumpPathD`: the coordinate of the crossed law at
  a nonnegative time is the law of `jumpProcessE` there. **Nothing of the law is
  lost in the crossing**, which is what makes the passage usable: a statement
  proved about the process is a statement about the law on `D(ℝ, E)` as well, at
  every time the model has.
* `map_eval_map_extendNNReal_map_jumpPathD_poisson`: the independent control, on
  `D(ℝ, ℕ)`. Its marginal at every nonnegative time is
  `ProbabilityTheory.poissonMeasure t`, into whose definition nothing of this
  development enters.
* `isTightMeasureSet_map_jumpPathD` and
  `isTightMeasureSet_map_extendNNReal_map_jumpPathD`: the path law is tight on
  `D(ℝ≥0, E)` — a single finite measure on a complete second countable metric
  space is, by `MeasureTheory.isTightMeasureSet_singleton` — and its image under
  the crossing is tight on `D(ℝ, E)`. The second is not a new estimate, the
  conclusion being available on the target space directly; what it is, is the
  first passage of a law of this development through
  `SkorokhodSpace.isTightMeasureSet_map_extendNNReal`, whose hypothesis is here
  discharged on data and whose family form `{μ i | i}` is matched against a
  measure actually produced here.
* `isTightMeasureSet_map_postcomp_map_jumpPathD`: the same service for the other
  transport of Milestone 8 there, `SkorokhodSpace.isTightMeasureSet_map_postcomp`
  — the path law pushed forward under `f ↦ h ∘ f` for a continuous `h : E → E'`
  into any Polish `E'`. With `E' = ℝ` this is the tightness of the law of the
  **real valued** process `h ∘ X`, which is the shape the tightness criterion of
  Milestone 8 reduces to.

* `jumpFiltrationE_eq_comap_jumpPath` and `measurable_pathFiltration_jumpPath`:
  the natural filtration of the construction **is** the pull back of
  `pathFiltration` along `jumpPath`, by `naturalFiltration_comp`, so the path map
  is measurable from one past to the other. An identity of σ-algebras, not an
  inclusion, because both sides are natural filtrations of processes that agree
  along the map.
* `martingale_map_of_martingale_comp`: a martingale **pushes forward** along a
  measurable map. If `Y ∘ θ` is a martingale for `𝓖` under `P` and `θ` is
  measurable from `𝓖 i` to `𝓕 i` at every `i`, then `Y` is a martingale for `𝓕`
  under `P.map θ`. This is not `martingale_comp_of_map_eq` read backwards: the
  pull back needs the filtration downstairs to be exactly the comap, the push
  forward needs only that the map is measurable from one past to the other — and
  it needs the adaptedness upstairs as an input, because a push forward cannot
  produce it. Integrability is no hypothesis; `integrable_map_measure` reads it
  off the martingale downstairs, and that is the only use of the finiteness of
  `P`. No topology on the index.
* `jumpPath_isMPSolution`: the image of the jump measure under the path map
  solves the martingale problem of the jump operator for the coordinate process
  and `pathFiltration`. This is the **seam**: the first martingale problem
  solution of this file that lives on a path space, and what makes the Markov
  and uniqueness statements of this milestone non vacuous on data. The
  hypotheses are those of `jumpProcessE_isMPSolution_of_nonneg` and nothing more
  — bounded nonnegative rate, Dirac kernel at an absorbing state — so a
  vanishing rate is admitted. `mem_mpFamily_comp_jumpPath` is the transport of
  the test processes, and it is an identity of the defining data and not an
  almost sure identity, because `coordinate_jumpPath` is `rfl`.
* `map_coordinate_bot_jumpPath` and `isProbabilityMeasure_map_jumpPath`: the
  image measure has initial law `nu` — which is `hinit` of
  `onedim_mpFamily_jumpOperator` — and is a probability measure, which every
  statement of this milestone asks for.

**The solution set of the jump problem is a singleton.** The seam above puts a
solution on the canonical path space; these put the *only* one there, and the
statement is an identity of sets and not two implications.

* `onedim_mpFamily_jumpOperator_coordinate`: `eq:absonedim` at the coordinate
  process of the canonical path space, which is `onedim_mpFamily_jumpOperator`
  with its two hypotheses about `(F, π)` discharged — measurability of each
  coordinate (`measurable_coordinate`) and **joint** measurability in time and
  path (`measurable_uncurry_coordinate`). The second is the one the abstract
  path space does not supply, and it is why the space is a subtype carrying a
  regularity and not a function space.
* `subsingleton_mpSolutions_jumpOperator_coordinate`: `thm:absuniq`(b) on the
  data of Milestone 4. At most one probability measure on the canonical path
  space solves the martingale problem of a bounded jump operator with a
  prescribed initial law. Every hypothesis of
  `subsingleton_mpSolutions_mpFamily_lebesgueClock` is met by a theorem of the
  two blocks above: the shift is `pathShift`, the clock is `lebesgueClock`, the
  σ-field is `generateFrom_coordinate`, the integrability proviso is
  `integrable_mpFamily_jumpOperator_coordinate`. The absorbing convention
  `habs` is **not** among them — uniqueness does not need it, only existence
  does.
* `mpSolutions_jumpOperator_coordinate_eq_singleton`: the solution set **is**
  `{(jumpMeasure mu nu).map (jumpPath lam)}`. Existence and uniqueness in one
  statement, and the first martingale problem in this development shown to have
  exactly one solution. What is not assumed: no topology on `E`, no
  completeness, no separability, no standard Borel structure, no positivity of
  the rate and no countability of the state space — a measurable structure with
  measurable diagonal and nothing else.
* `map_coordinate_map_jumpPath`: the law of the unique solution at `t` is the
  law of `jumpProcessE lam t` under `jumpMeasure mu nu`, by `Measure.map_map`,
  because the coordinate of the image is the process by `rfl`. This is what
  makes a closed form computed on the construction a closed form for the
  solution.
* `isMarkov_jumpOperator_coordinate`: the Markov half of the same instance.
  `isMarkov_of_unique_onedim` at the data of Milestone 4, with
  `onedim_mpFamily_jumpOperator_coordinate` as its `eq:absonedim` — literally
  the input the uniqueness half consumes, so the two halves of this milestone
  are discharged on one set of data by one lemma. Markov is the **conclusion**:
  the input is uniqueness of the one dimensional laws, which comes from
  Milestone 4 through `integral_eq_of_isMPSolution_of_map_eq`, and not from a
  semigroup and not from Hille–Yosida. That is `rem:noch1` checkable in Lean,
  and Ethier–Kurtz 4.4.1 runs the other way and is a different theorem.

**Acceptance examples.**

* **The two state chain of Milestone 4, all the way through** —
  `mpSolutions_flip_coordinate_eq_singleton` and
  `real_map_coordinate_flip_eq`. `E = Bool`, `lam ≡ 1`,
  `mu = Kernel.deterministic (!·)`, so the generator is
  `A f x = f (!x) - f x`. The martingale problem on the canonical path space
  started at `false` has exactly one solution, and at time `t` that solution
  puts mass `(1 - exp (-2t))/2` on `{true}`. The hypothesis of the second
  statement is that `P` is *a* solution; the conclusion is a number, and the
  number comes from `jumpMeasure_map_jumpProcess_flip` — the exponential series
  of the generator — and not from the path construction. Two independent routes
  to one value is what an acceptance example is for. The probe at `t = 0` is
  written out: the solution sits at `false`.
* **The transition operator of that example, computed.**
  `isMarkov_jumpOperator_coordinate` gives the Markov property on these data;
  its transition operator is `T t = exp (t • A)`, which is the
  `T t f x = ∫ f (ω t) ∂(P x)` of `isStrongMarkov`, and `expJumpApply_flip` is
  that exponential in closed form on the two state chain. The acceptance test is
  that the two readings of `T t f false` at `f = 1_{true}` agree, which is the
  number above.
* **Uniqueness of the one dimensional laws is genuinely weaker than uniqueness.**
  The hypothesis of this milestone is that the one dimensional distributions of
  the shifted problems are determined, for **every** shift; dropping the shift
  and asking it at `r = 0` only is not enough, since the finite dimensional
  distributions are built from the shifted problems by `restart`. So the
  hypothesis must quantify over `r`, and an implementer who states it at one
  time proves a different theorem.
* **The converse direction, and where it is not.** Brownian motion is the unique
  solution of the martingale problem for `(f, f''/2)` on `Cc^∞(ℝ)` — that is
  Ethier–Kurtz Theorem 4.4.1, a Hille–Yosida statement, and it is **not** an
  item of this milestone. Running the milestone the other way on the same
  instance: given that the one dimensional laws of every solution are Gaussian,
  the milestone concludes the Markov property and uniqueness. The two together
  are the full picture, and the acceptance test is that this instance is
  covered by exactly one half of it.

## Milestone 7: localization

Stage (L) of Milestone 2 — `[LinearOrder ι]`, `[OrderBot ι]`,
`[TopologicalSpace ι]`, `[OrderTopology ι]` — with a countable dense subset and
`[AddCommMonoid ι]`. The stage is inherited and not chosen: every statement of
this milestone speaks about `Locally`, which is declared under it.

* The localizing systems here are a **refinement** of Mathlib's
  `IsLocalizingSequence`, not a replacement: a system is a set of times, closed
  under the shift, from which localizing sequences are drawn. State
  `LocalizingSystem.isLocalizingSequence` connecting the two, so that
  `Locally` and its API apply to everything below.
* A **strict** stopping time is one for `𝓕`, not for the right continuous
  filtration `⨅ s > t, 𝓕 s`. The distinction is the content of this milestone:
  the debut of an open set is a stopping time only for the right continuous
  filtration, and the times used below have to be strict for the shift
  construction to produce stopping times on every ambient space.
* `LocalizingSystem 𝓧° Σ`, a set `Σ` of strict stopping times on `F` with:
  (L1) `Σ` contains an increasing sequence tending to infinity for which
  stopping every `Y ∈ 𝓧°` gives a martingale exactly when `P` solves the local
  problem; (L2) `σ ∈ Σ` and `r : ι` imply `r + σ ∘ θ r ∈ Σ`; (L3) for every
  local solution, every `Y ∈ 𝓧°`, every `r` and every `σ ∈ Σ` with `r ≤ σ`, the
  process `t ↦ Y ((r + t) ⊓ σ) - Y r` is a martingale for `(𝓕 (r + t))`.
* `localizingSystem_of_boundedJumps`: if every `Y ∈ 𝓧°` is càdlàg with `Y 0 = 0`
  and jumps bounded by a constant, then the hitting times of the **running
  supremum**, `τ n = inf {t | n ≤ sup_{s ≤ t} ‖Y s‖}`, are strict stopping times
  and satisfy (L1). The running supremum is what makes the times strict; the
  hitting times of `‖Y‖` itself are not.
* `localRestart`: the restart lemma of Milestone 5 for local solutions, with `Z`
  bounded, on a two level filtered space.
* `subsingleton_localMPSolutions`: uniqueness for the local problem, from
  (L1)–(L3) and Milestone 6.
* The jump processes of Milestone 4 with unbounded rate as the example, and the
  path dependent variant as the example where the local problem is the primary
  one and the global problem needs an extra integrability hypothesis.

**Acceptance examples.**

* **The exploding jump process.** `E = ℕ`, `lam n = 2 ^ n`,
  `mu n = Measure.dirac (n + 1)`. This is the instance for which
  `IsLocalMPSolution` holds and `IsMPSolution` does not, so the two predicates of
  Milestone 2 are genuinely different here, and
  `localizingSystem_of_boundedJumps` applies with jump size `1`.

  The localizing times are `rateTime lam k` of Milestone 4 — the hitting times of
  the running supremum of the rate along the path — and **not** the jump times.
  The jump times are not stopping times for the natural filtration of the
  process, on this instance or on any other: `not_isStoppingTime_min_jumpTimeE`
  is the witness, the constant chain, at which the waiting times leave no trace
  in the path. On these data the chain increases at every jump *almost surely*,
  so the two sequences agree almost everywhere; `IsStoppingTime` is not an almost
  sure notion, and that is exactly the distinction this milestone exists to make.
  This is a second reason for the running supremum, independent of the strictness
  named in the point above and sharper than it — a debut that the filtration
  cannot see is not repaired by passing to `⨅ s > t, 𝓕 s`.
* **The running supremum is not a convenience.** For a càdlàg `Y` with
  `Y 0 = 0`, the hitting time `inf {t | n ≤ ‖Y t‖}` of the norm is not a
  stopping time for `𝓕` itself — it is the debut of the open set
  `{x | n < ‖x‖}` only after passing to `⨅ s > t, 𝓕 s` — while
  `inf {t | n ≤ ⨆ s ∈ Set.Iic t, ‖Y s‖}` is, the running supremum being
  adapted and non-decreasing so that `{τ ≤ t}` is `{n ≤ ⨆ s ∈ Set.Iic t, ‖Y s‖}`.
  Concretely, on `Y t = Set.indicator (Set.Ici 1) 1` the two agree; on a path
  that approaches level `n` from below without reaching it before time `1` and
  crosses at `1` they do not. This is the distinction the milestone exists to
  make, and a formalization that used the norm hitting times would be stating
  the theorem for the right continuous filtration.
* **The path dependent variant, where the local problem is primary.** The Hawkes
  process of `ex:hawkes` with a rate that is a functional of the past: the
  stopped processes are martingales for every localizing time by (L3), while the
  global martingale property needs `𝔼[N t] < ∞`, which the manuscript supplies
  through the renewal equation `m = μ₀ + φ * m`. So the milestone's two levels
  are both instantiated on one process, and the extra hypothesis for the global
  level is visible as a separate fact about `φ`.

## Milestone 8: duality

* `chain_identity`: let `ι` be a preorder with a least element, `q` a measure for
  which the sets `Ico s t` are measurable, and
  `Φ, γ₁, γ₂ : ι → ι → ℝ` with
  `Φ s' t - Φ s t = ∫ r in Ico s s', γ₁ r t ∂q` for `s ≤ s'` and
  `Φ s t' - Φ s t = ∫ r in Ico t t', γ₂ s r ∂q` for `t ≤ t'`. Then for every
  staircase `0 = s 0 ≤ ... ≤ s m = t` and `t = t 0 ≥ ... ≥ t m = 0`,
  ```
  Φ t 0 - Φ 0 t = ∑ k, (∫ r in Ico (s k) (s (k+1)), γ₁ r (t (k+1)) ∂q
                        - ∫ r in Ico (t (k+1)) (t k), γ₂ (s k) r ∂q)
  ```
  An exact telescoping identity; no analysis, no hypothesis on the staircase
  beyond monotonicity.
* `chain_identity_of_absolutelyContinuous`: for `ι = [0,∞)`, `q` Lebesgue and
  `Φ` absolutely continuous in each variable with `∇Φ = (γ₁, γ₂)` satisfying
  `∫∫ |γ i| < ∞` on squares, one has
  `Φ t 0 - Φ 0 t = ∫ s in Ioc 0 t, (γ₁ s (t - s) - γ₂ s (t - s))` for almost
  every `t`. Obtain it from `chain_identity` by refining the staircase.
* `duality`: let `X`, `Y` be independent measurable processes with values in
  `E₁`, `E₂`, let `f, g, h` be measurable on `E₁ × E₂` and `α`, `β` measurable
  on `E₁`, `E₂`, subject to the domination hypotheses that for every `T` there
  are an integrable `Γ T` and a constant `C T` with
  `sup_{r,s,t ≤ T} (|α (X r)| + 1) * |f (X s, Y t)| ≤ Γ T` and the three
  analogous bounds, and `∫_0^T |α (X u)| + ∫_0^T |β (Y u)| ≤ C T`. If
  `f (X t, y) - ∫_0^t g (X s, y)` is a martingale for every `y` and
  `f (x, Y t) - ∫_0^t h (x, Y s)` is a martingale for every `x`, then for almost
  every `t`
  ```
  𝔼[f (X t, Y 0) * exp (∫_0^t α (X u))] - 𝔼[f (X 0, Y t) * exp (∫_0^t β (Y u))]
    = 𝔼[∫_0^t (g (X s, Y (t-s)) - h (X s, Y (t-s))
             + (α (X s) - β (Y (t-s))) * f (X s, Y (t-s)))
        * exp (∫_0^s α (X u) + ∫_0^{t-s} β (Y u)) ds]
  ```
  Fubini, absolute continuity and dominated convergence; no path regularity and
  no Skorokhod space.
* `duality_of_atomless`: for an atomless clock and the predictable convention,
  `Φ t 0 = Φ 0 t` for every `t`, by the time change `Q t = q (Set.Iio t)` and its
  right inverse. State the time change as a lemma in its own right. The
  conclusion holds at every `t` and not merely `q`-almost every `t`, by
  `eq_comp_add_of_chain_identity` in place of
  `chain_identity_of_absolutelyContinuous`.
* `eq_comp_add_of_chain_identity`: for intervals `I J : Set ℝ` and
  `Ψ : ℝ → ℝ → ℝ` absolutely continuous in each variable on `I ×ˢ J` with
  `∇Ψ = (ψ, ψ)` for one and the same `ψ`, integrable on compact subrectangles,
  there is a locally absolutely continuous `f : ℝ → ℝ` with `Ψ x y = f (x + y)`
  for every `x ∈ I`, `y ∈ J`. Apply `chain_identity_of_absolutelyContinuous` to
  `(u, v) ↦ Ψ (x + u) (y' + v)` on the square of side `x' - x`, where the right
  hand side vanishes, and turn its `∀ᵐ r` into `∀ r` by continuity of
  `r ↦ Ψ (x + r) y' - Ψ x (y' + r)`. The proof of
  `chain_identity_of_absolutelyContinuous` reads its argument on `[0,T]²` only,
  so it holds on a square.
* `Clock.stretches`: for `q = μ + ∑ i, m i • Measure.dirac (a i)` on
  `Set.Icc 0 t* ⊆ ℝ` with `μ` atomless, finitely many atoms
  `0 ≤ a 1 < ... < a N < t*` and `0 < m i` — an atom at `t*` itself lies in no
  `Set.Ico s s' ⊆ Set.Iio t*` and is discarded — the images of the diffuse
  stretches
  under `Q s = q (Set.Iio s)`: `S j = Set.Icc (α j) (β j)` with `α 0 = 0`,
  `β j = α j + c j` and `α j = β (j-1) + m j`, where `c j` is the `μ`-mass of the
  `j`-th stretch, together with `Set.range Q = ⋃ j, S j`, `Q (a j) = β (j-1)` and
  `Q t* = β N`. The gaps `Set.Ioo (β (j-1)) (α j)` are the atoms, one each, of
  length `m j`.
* `duality_of_mixed`: with `Φ, γ` as in `chain_identity` and `γ₁ = γ₂ = γ`, a
  clock as in `Clock.stretches` and the transported pair satisfying the
  integrability of `chain_identity_of_absolutelyContinuous`, one has
  `Φ s t = Φ t s` for all `s, t ≤ t*` in the predictable convention, and in
  particular `Φ t* 0 = Φ 0 t*` at every such `t*`. No lower bound on any `c j`.
  Three steps. `eq_comp_add_of_chain_identity` on `S i ×ˢ S j` gives
  `Ψ x y = f i j (x + y)` on a domain `D i j = Set.Icc (α i + α j) (β i + β j)`
  that is symmetric in `i, j`. Crossing the gap at `a i` gives
  `f i j (u + m i) = f (i-1) j u + m i * deriv (f (i-1) j) u` for
  `u ∈ β (i-1) +ᵥ S j`, because the jump of `Ψ` across the gap is
  `m i * γ (a i) ·` while the same row is the density of `y ↦ Ψ (β (i-1)) y`;
  that row is a density exactly when `0 < c j`. Where `c j = 0` the stretch
  `S j` is a point, the relation degenerates to
  `f i j (α i + α j) - f (i-1) j (β (i-1) + α j) = m i * γ (a i) (a (j+1))`, and
  the value on the right is a corner value, because `γ (a i) ·` is constant on
  `Q ⁻¹' {α j}` and `a (j+1)` lies in that set. The same corner value is reached
  along the other coordinate:
  `f (i-1) (j+1) (β (i-1) + α (j+1)) - f (i-1) j (β (i-1) + β j)
   = m (j+1) * γ (a i) (a (j+1))`, for every `i` and `j < N`. Then induction on
  `i - j` makes `w i j = f i j - f j i` vanish: on
  `Set.Icc (α i + α j) (α i + β j)` by the crossing relation applied to `w` if
  `0 < c j`, and if `c j = 0` at the single point of that interval by the two
  degenerate relations applied to `w`, which give
  `w i j (α i + α j) = w (i-1) j (β (i-1) + α j) + m i * δ i (j+1)` for the
  antisymmetric corner defect `δ k l = γ (a k) (a l) - γ (a l) (a k)`, together
  with `m (j+1) * δ i (j+1) = w (i-1) (j+1) _ - w (i-1) j _`; both vanish by the
  hypothesis at `i - j - 1` and `i - j - 2`, and `δ k k = 0` settles
  `i - j = 1`. On `Set.Icc (α i + β j) (β i + β j)` — non-empty only if
  `0 < c i` — because there `w i j + m (j+1) * deriv (w i j) = 0` with initial
  value `0` at the junction, whose only absolutely continuous solution is `0`.
  Like `atomGrid`, the induction uses its hypothesis at two levels at once.
* `duality_defect_eq_integral`: for a clock `q` on `ι` with a least element `0`
  and `Φ, γ` as in `chain_identity` with `γ₁ = γ₂ = γ`,
  `Φ s t = Φ 0 t + ∫ r in Iio s, γ r t ∂q` and `Φ s t = Φ s 0 + ∫ r in Iio t, γ s r ∂q`,
  hence
  ```
  Φ t 0 - Φ 0 t = ∫ r in Iio t, (γ r 0 - γ 0 r) ∂q .
  ```
  Both are the increment representations at `s = 0`, where `Iio 0 = ∅`; no
  chain, no atom, no comparability. It is worth its own name because it turns
  every duality statement into a statement about the antisymmetric part
  `κ r s = γ r s - γ s r` of `γ` alone: the two representations are compatible
  exactly when
  `∫_{Iio s} (γ r t - γ r 0) ∂q = ∫_{Iio t} (γ s r - γ 0 r) ∂q` for all `s, t`,
  and that condition splits along `γ = (λ + κ) / 2` into one condition on the
  symmetric `λ` and one on `κ`, of which only the latter meets the defect. On a
  chain the `κ` condition forces `κ = 0`, which is `atomGrid_symm`; on a finite
  partial order with nonnegative masses it forces the defect to vanish, which is
  `dualityDefect_eq_zero_of_nonneg`.
**Duality under a weight.** The identity of `chain_identity` carries a
multiplicative weight, and the four points below are what that buys: the route
from duality to uniqueness that does not pass through a shift system. The
weight sits on the first factor, the staircase starts where the weight is
measurable, and the dual time is the one that matches the clock mass.

* `chain_identity` is stated above with the staircase running from `(⊥, t)` to
  `(t, ⊥)`; the telescoping reads neither endpoint, so the statement is the one
  for an arbitrary monotone `s` and antitone `t` with the same length,
  ```
  Φ (s m) (t m) - Φ (s 0) (t 0)
    = ∑ k, (∫ r in Ico (s k) (s (k+1)), γ₁ r (t (k+1)) ∂q
            - ∫ r in Ico (t (k+1)) (t k), γ₂ (s k) r ∂q)
  ```
  and the form above is its instance. A least element of `ι` is needed for
  `duality_defect_eq_integral`, which reads `Iio ⊥ = ∅`, and for nothing else in
  this group.
* `duality_weighted`: with the data of `duality_of_atomless`, a time `s₀`, a
  bounded non-negative `𝓕^X s₀`-measurable `Z`, a time `s' ≥ s₀` and the dual
  time `T` determined by `q (Ico s₀ s') = q (Ico ⊥ T)`,
  ```
  𝔼[Z * f (X s', Y ⊥)] = 𝔼[Z * f (X s₀, Y T)] .
  ```
  The martingale property in the `X` direction is read on `[s₀, ∞)` only, which
  is what `lem:restartmemory` supplies for the reweighted measure: `Z • P` is a
  solution from `s₀` onwards, by the tower property and nothing else. Three
  ingredients. The `X` increments are `integral_smul_martingale_eq` of
  Milestone 5, which is already proved and already free of the shift. The `Y`
  increments are unchanged, because a weight on the first factor leaves the
  second factor independent and its law untouched:
  `MeasureTheory.prod_withDensity_left`
  (`MeasureTheory/Measure/WithDensity.lean:701`) is that step in measure form.
  The conclusion is `duality_of_atomless` on the rectangle
  `Icc s₀ s' ×ˢ Icc ⊥ T`.

  The condition on `T` is not a hypothesis on the clock but the definition of
  the dual time: it is `rem:haarrole`'s clock time anti-diagonal
  `Q (s k) + Q (t k) = Q (s') `, which `eq:cancel` wants and which translation
  invariance of `q` is one way to obtain. At `s₀ = ⊥` it holds with `T = s'`
  for every clock, and that is why `duality` does not name it. Under Lebesgue
  measure it is `T = s' - s₀`.
* `not_secondIncrement_of_weight_on_dual`: the weight has to sit on the first
  factor. Take `E₁ = Unit`, `E₂ = ℝ`, `f x y = y`, `h = 0`, and for `Y` the
  martingale with `Y ⊥ = 0` and `Y t` a fair sign for `t ≥ 1`; then `γ₂ = 0`
  while `Z = 1 + Y 1` gives `Φ^Z ⊥ ⊥ = 0` and `Φ^Z ⊥ 1 = 1`. So the second
  increment relation fails for a weight that reads the dual process, and it
  fails at the first step and not in a limit. This is the witness for the
  measurability hypothesis of `duality_weighted`, and it is why that hypothesis
  is `𝓕^X s₀` and not the filtration of the product.
* `propagatesAgreement_of_duality`: the weighted laws of `X` under the members
  of a solution set are related by the transfer operator
  `Λ s t y x = 𝔼[f (x, Y^y T)]`, so `propagatesAgreement_of_transfer` of
  Milestone 6 applies and the set propagates agreement. With
  `eq_of_propagatesAgreement` this is `cor:uniqviadual` — uniqueness for every
  initial law — through `prop:uniqfromprop`, with no shift system, no
  determining set and no appeal to `thm:absuniq`. The separating hypothesis
  `cor:uniqviadual`(i) is the only hypothesis of that corollary which survives.
* `isMarkov_of_duality`: the same identity with `Z` an indicator of a set in
  `𝓕^X s` reads `𝔼[f (X t, y) | 𝓕^X s] = Λ s t y (X s)`, so a solution which
  has a dual is Markov, over a countable separating family and with one null
  set for all of it. The Markov property is therefore a *consequence* of
  possessing a state-based dual and not a hypothesis anywhere in this route —
  which also says how far the route reaches: a dual whose `X` side is a
  function of the state carries the Markov property with it.
* `duality_weighted_of_condExp`: the balance condition the weighted identity
  actually consumes is `γ₁ = γ₂` *after* weighting, that is
  `𝔼[Z * (g r (X, Y t) - h (X r, Y t))] = 0` for the weight at hand, and over
  all bounded `𝓕^X s₀`-measurable weights this is
  `𝔼[g r (X, ·) - h (X r, ·) | 𝓕^X s₀] = 0`. It admits a path dependent `g`,
  and it is the exact room the identity leaves outside the Markov world. The
  conclusion is that of `duality_weighted`, and the proof is the same chain,
  which reads the balance nowhere else.

* `atomGrid_symm`: let `M : ℕ`, let `m : ℕ → ℝ` with `m i ≠ 0` for
  `1 ≤ i` and `i ≤ M - 1`, and let `Φ : ℕ → ℕ → ℝ` satisfy
  `m j * (Φ (i+1) j - Φ i j) = m i * (Φ i (j+1) - Φ i j)` for
  `1 ≤ i, j ≤ M - 1`. Then `Φ i j = Φ j i` for `1 ≤ i, j ≤ M`. Apply the
  hypothesis to the antisymmetric part `w i j = Φ i j - Φ j i`, which satisfies
  it because the relation is linear in `Φ` and carried into itself by
  transposition, and induct on the distance `d = |i - j|` from the diagonal with
  the levels `d` and `d - 1` carried along together: at `d = 1` antisymmetry and
  `m j ≠ 0` give `w (j+1) j = - w (j+1) j`, and the step from `d` to `d + 1`
  reads the relation at `(j + d, j)`, where both terms on the right sit at
  distances `d` and `d - 1`. Purely arithmetic — no measure, no clock, and `ℕ`
  as the only index — so it belongs in `Mathlib/Algebra/Order/` rather than in
  the probability tree. It is what gives the chain the stronger conclusion
  `Φ s t = Φ t s`, which the partial order does not have. Its two-level
  induction is also the shape of the one in `duality_of_mixed`, and the
  cross-multiplication it runs on is what carries that proof across a stretch
  of zero diffuse mass.
* `atomGrid_symm_int`: let `m : ℤ → ℝ` with `m i ≠ 0` for all `i`, and let
  `Φ : ℤ → ℤ → ℝ` satisfy
  `m j * (Φ (i+1) j - Φ i j) = m i * (Φ i (j+1) - Φ i j)` for all `i j`. Then
  `Φ i j = Φ j i` for all `i j`. The proof is that of `atomGrid_symm` word for
  word — the base case reads the relation on the diagonal, the step at
  `(j + d, j)`, and neither names a least or greatest index; the bounds
  `1 ≤ i, j ≤ M - 1` of the finite lemma mark where its relations stop, not
  where the induction starts. The induction on the distance `d` is well
  founded because every pair of integers is at finite distance, and that is
  the single point where the index being `ℤ` enters. Same home as
  `atomGrid_symm`, next to it.

The next four items carry the partial order case. They are matrix algebra over
`ℝ` and know neither clock nor measure nor order, and belong in
`Mathlib/LinearAlgebra/Matrix/`; the fifth assembles them on a finite partial
order.

* `Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`: for
  `A B : Matrix n n ℝ` with `A.IsSymm` and `Bᵀ = -B`, `(A * B).trace = 0`.
  Mathlib supplies `Matrix.IsSymm` (`LinearAlgebra/Matrix/Symmetric.lean:35`),
  `Matrix.trace_transpose` (`LinearAlgebra/Matrix/Trace.lean:73`) and
  `Matrix.trace_mul_comm` (`Trace.lean:158`); it has no predicate for `Bᵀ = -B`
  by itself — `Matrix.IsSkewAdjoint`
  (`LinearAlgebra/Matrix/SesquilinearForm.lean:560`) is relative to a form `J` —
  so the hypothesis is written out. This is the smallest self contained target
  of this roadmap.
* `Matrix.trace_mul_eq_dotProduct_diag_of_isSymm`: let `V K : Matrix n n ℝ` with
  `Kᵀ = -K`, put `δ i = (V * K) i i`, and assume
  `(V * K) i j + (V * K) j i = δ i + δ j` for all `i j`. Then for every `T` with
  `T.IsSymm`, `(T * (V * K)).trace = δ ⬝ᵥ (T *ᵥ 1)`. Transpose under the trace
  and shift cyclically to get `(T * (V * K)).trace = (T * (V * K)ᵀ).trace`, then
  substitute the hypothesis. Together with the previous item: if `(T * V).IsSymm`
  as well, then `δ ⬝ᵥ (T *ᵥ 1) = 0`. That is the whole use made of the
  compatibility condition.
* `Matrix.mulVec_one_eq_zero_iff_of_nonneg`: for `A : Matrix n n ℝ` with
  `0 ≤ A i j` for all `i j`, `A *ᵥ 1 = 0 ↔ A = 0` — the row sums of a
  nonnegative matrix vanish exactly when the matrix does. Applied to the powers
  of a nonnegative `V` it gives `V ^ k *ᵥ 1 = 0 ↔ V ^ k = 0`, hence
  `V ^ (r-1) *ᵥ 1 ≠ 0` for the nilpotency index `r`, which is the hypothesis of
  the next item. This is the only place in the partial order case where
  nonnegativity of the masses is used.
* `Matrix.exists_isSymm_mulVec_one_eq_single`: let `V : Matrix n n ℝ` with
  `V ^ r = 0` and `V ^ (r - 1) *ᵥ 1 ≠ 0`. Then for every `t` there is a `T` with
  `T.IsSymm`, `(T * V).IsSymm` and `T *ᵥ 1 = Pi.single t 1`. Explicitly: pick
  `i` with `(V ^ (r-1) *ᵥ 1) i ≠ 0`, set `p k = (V ^ (r-1-k))ᵀ *ᵥ (c • Pi.single i 1)`
  with `c = ((V ^ (r-1) *ᵥ 1) i)⁻¹`, so that `Vᵀ *ᵥ p k = p (k-1)` and
  `p 0 ⬝ᵥ 1 = 1`; normalise to `p̂ k = ∑ j ≤ k, w (k-j) • p j`, where `w` inverts
  `∑ k, (p k ⬝ᵥ 1) • X ^ k` in `ℝ[X] ⧸ X ^ r`, so that `p̂ k ⬝ᵥ 1 = if k = 0 then 1 else 0`;
  and with `ψ k = (Vᵀ) ^ k *ᵥ Pi.single t 1` and `c j = (V ^ j *ᵥ 1) t` put, with
  `Matrix.vecMulVec` (`Data/Matrix/Mul.lean:626`) for the outer product,
  ```
  T = ∑ k, (vecMulVec (p̂ k) (ψ k) + vecMulVec (ψ k) (p̂ k))
        - ∑ k, ∑ l, c (k + l) • vecMulVec (p̂ k) (p̂ l) .
  ```
  Symmetry is by construction, `T *ᵥ 1 = Pi.single t 1` because the two `c k`
  sums cancel, and `T * V = Vᵀ * T` because `ψ kᵀ * V = ψ (k+1)ᵀ` and
  `p̂ lᵀ * V = p̂ (l-1)ᵀ` carry the first two sums into one another while the
  third depends on `k + l` only. In the third sum `V` meets the second factor on
  one side and the first on the other, and the free index runs over the full
  range on both; the boundary terms cancel because `c j = 0` for `j ≥ r`.
* `Matrix.krylovCertificate_unique`: let `V : Matrix n n ℝ` with `V ^ r = 0`,
  `ψ k = (Vᵀ) ^ k *ᵥ Pi.single t 1` for `k < r` with `ψ (r-1) ≠ 0`, and
  `c k = ψ k ⬝ᵥ 1`. If `T = ∑ k, ∑ l, B k l • vecMulVec (ψ k) (ψ l)` is symmetric
  with `T * V = Vᵀ * T` and `T *ᵥ 1 = Pi.single t 1`, then `B k l = b (k + l)`
  for a `b : ℕ → ℝ` with `b j = 0` for `j < r - 1` and
  `∑ l, b (k + l) * c l = if k = 0 then 1 else 0` for `k < r`; this triangular
  system with diagonal `c (r-1) = ψ (r-1) ⬝ᵥ 1` has exactly one solution, and
  conversely every such `b` gives a `T` with the three properties. Two facts
  carry it: the `ψ k` are linearly independent (apply `(Vᵀ) ^ (r-1-k₀)` to a
  vanishing combination with least index `k₀`), so the `vecMulVec (ψ k) (ψ l)`
  are too and coefficients may be compared in `T * V = Vᵀ * T`, which reads
  `B (k-1) l = B k (l-1)` and `B 0 (l-1) = 0`; and `c (r-1) ≠ 0` when `t` is
  the greatest element of the poset and `V s a = if a < s then m a else 0`,
  because every longest chain ends at `t`. Consequences: the `T` of
  `Matrix.exists_isSymm_mulVec_one_eq_single` lies in this class (there
  `i = t`, so `p k = c • ψ (r-1-k)`), hence does not depend on any choice and
  has vanishing row `0`; and `b j = (-1) ^ j * q j` where
  `1 / P(c) = ∑ j, q j * c ^ (-j)` is the expansion at `∞` of the reciprocal of
  the chain polynomial `P(c) = ∑ k, (-c) ^ k * c k = (1 + c • Vᵀ)⁻¹ *ᵥ Pi.single t 1 ⬝ᵥ 1`,
  which makes `T` the residue at `∞` of
  `vecMulVec (z c) (z c) / (c * P c)` with `z c = (1 + c • Vᵀ)⁻¹ *ᵥ Pi.single t 1`,
  and, when `P` has simple zeros `c k`, the real matrix
  `vecMulVec (Pi.single t 1) (Pi.single t 1) - ∑ k, (-c k / P' (c k)) • vecMulVec (x k) (x k)`
  with `x k = -(c k)⁻¹ • z (c k)` (Task 23, run 29, Theorems 27 and 28; on a
  chain `P c = ∏ l, (1 - c * m l)` and this is `Clock.omegaChainPotential`'s
  certificate). The chain polynomial is the weighted independence polynomial
  of the incomparability graph evaluated at `-c`; it need not be real-rooted
  (the ladder `a i < b j ↔ i < j` with `m (a i) = (2/3) ^ i`, `m (b j) = 2 ^ (-j)`
  has complex zeros already at eight atoms per chain), and `T` is real all the
  same.
* `Matrix.certificate_mulVec_single_top`: let `V : Matrix n n ℝ`, `t : n`,
  `d : ℕ` and `Ω : ℝ` with `Ω ≠ 0` and `V ^ d *ᵥ 1 = Ω • Pi.single t 1`. If `T`
  is symmetric with `T * V = Vᵀ * T` and `T *ᵥ 1 = Pi.single t 1`, then
  `T *ᵥ Pi.single t 1 = Ω⁻¹ • ((Vᵀ) ^ d *ᵥ Pi.single t 1)`. Proof:
  `T *ᵥ (V ^ d *ᵥ 1) = (Vᵀ) ^ d *ᵥ (T *ᵥ 1)` by induction on `d` from
  `T * V = Vᵀ * T` (`Matrix.mulVec_mulVec`), then evaluate both sides. Nothing
  else is used — no nonnegativity, no nilpotency. So the row `t` of *every*
  certificate is the same, and two certificates differ by a matrix with
  vanishing row `t`. For the partial order with greatest element `t`,
  `V s a = if a < s then m a else 0`, `d` the height and `Ω` the mass-weight of
  the longest chains (the chain count already used for `c (r-1) ≠ 0` above),
  the row is `T t a = m a * (weight of the longest chains starting at a) / Ω`
  — the mass-weighted distribution of the starting points of longest chains
  (Task 23, run 30, Proposition 29). On the ladder `a i < b j ↔ i < j` with `n`
  levels this is `T t (b 1) = 1 / ∑ i ≤ n, ∏ l ≤ i, m (a l) / m (b l)`, a partial
  theta sum, and it explains the measured `0.51704641` of run 29; the same run-30
  computation shows that the boundary entries `T (a 2) (b n)` and `T (b 2) (b n)`
  of every certificate of the truncation are forced as well (Theorem 31), which
  gives the lower bound `‖T‖_m ≥ |κ_n| / m (a 2)` that the LP minimum attains
  exactly (verified in rationals for `n ≤ 14` at `(α, β) = (1/2, 1/3)`).
* `Matrix.certificate_mulVec_pow_one`: let `V : Matrix n n ℝ` and `t : n`. If
  `T` is symmetric with `T * V = Vᵀ * T` and `T *ᵥ 1 = Pi.single t 1`, then for
  every `k`
  ```
  T *ᵥ (V ^ k *ᵥ 1) = (Vᵀ) ^ k *ᵥ Pi.single t 1,
  (V ^ k *ᵥ 1) ⬝ᵥ (T *ᵥ (V ^ l *ᵥ 1)) = (V ^ (k + l) *ᵥ 1) t .
  ```
  Proof: induction on `k` with `Matrix.mulVec_mulVec`; nothing else. So every
  certificate is determined on `Submodule.span ℝ (Set.range fun k => V ^ k *ᵥ 1)`,
  the Krylov space of `1`, and `Matrix.certificate_mulVec_single_top` is the
  instance `k = d` and should be derived from it. Its interest is the infinite
  case (Task 23, run 31, Theorems 36 and 37), which is not formalised here but
  fixes what the finite statement is for: on a countable partial order with
  greatest element `t`, summable masses and `e k = (V ^ k *ᵥ 1) t` the weight of
  the `k`-chains, one has `∑ a, m a * (V ^ k *ᵥ 1) a = e (k+1)` and
  `(k+1) * e (k+1) ≤ (∑ a, m a) * e k`, hence `V ^ k *ᵥ 1 / e k → Pi.single t 1`
  in the mass-weighted `ℓ¹` norm, and every certificate bounded by
  `|T s u| ≤ C * w s * w u` has column `t` equal to `lim_k ((Vᵀ) ^ k *ᵥ Pi.single t 1) / e k`,
  i.e. `T t a = m a * lim_k e_{k-1}(atoms above a) / e k`. The limit must
  therefore exist; on the disjoint union of two `ω`-chains with
  `m (a i) = B ^ (-i)`, `m (b j) = B ^ (-j) * 2 ^ ((-1) ^ (j+1))`, `B ≥ 16`, it
  does not (the even and odd subsequences of `e_k(b)/e_k(a)` are separated by
  `1/(4/B;4/B)_∞ < 2 (1/B;1/B)_∞`), so that well-founded partial order carries
  no bounded certificate and no uniformly bounded family of truncation
  certificates; well-foundedness is not the right hypothesis for the existence
  of certificates, convergence of the normalised chain count is a necessary one.
* `dualityDefect_eq_zero_of_nonneg`: let `α` be a finite partial order,
  `m : α → ℝ` with `0 ≤ m`, and `κ : α → α → ℝ` with `κ a b = - κ b a`. Put
  `Ψ s t = ∑ a ∈ Finset.Iio s, m a * κ a t`. If
  `Ψ s t + Ψ t s = Ψ s s + Ψ t t` for all `s, t`, then `Ψ t t = 0` for every `t`.
  Read `Ψ` as the matrix product `V * K` with `V s a = if a < s then m a else 0`;
  `V` is nilpotent because `V s a ≠ 0` forces `a < s`, its entries are
  nonnegative, and the four items above close the argument. No least element, no
  greatest element, no chain and no antichain condition; the masses may vanish.
  Nonnegativity is not removable — with `m = (0, 1, -1, 0)` on
  `0 < a, 0 < b, a < z, b < z` the defect at `z` is free.
* `Clock.atomChain`: for a clock `q` and a point `t` below which the atoms of `q`
  are finitely many and pairwise comparable, the monotone enumeration
  `u : Fin (N+2) → ι` with `u 0 = 0`, `u (N+1) = t` and `u i` the `i`-th atom,
  together with `q (Ico (u i) (u (i+1))) = m i` and the statement that
  `Ico (u i) (u (i+1))` carries the single atom `u i` for `1 ≤ i` and no atom for
  `i = 0`. The optional convention gets `Ioc (u (i-1)) (u i)` carrying the single
  atom `u i`, on the chain that stops at the largest atom.
* `Clock.atomPoset`: for a clock `q` on `ι` with a least element `0` and a point
  `t` below which the atoms of `q` are finitely many, the finite partial order
  `{0} ∪ {a | a < t ∧ q {a} ≠ 0}` induced from `ι`, with masses
  `m a = (q {a}).toReal`, together with `0 ≤ m` and
  `q (Iio s) = ∑ a ∈ Finset.Iio s, m a` for `s ≤ t` when `q` is purely atomic.
  This is the object `dualityDefect_eq_zero_of_nonneg` runs on, and it asks
  nothing of how the atoms lie relative to one another.
* `duality_of_atomic`: with `Φ, γ` as in `chain_identity` and `γ₁ = γ₂ = γ`, a
  purely atomic clock, and a `t` below which the atoms are finitely many, one has
  `Φ t 0 = Φ 0 t` in the predictable convention, with no hypothesis beyond the
  existence of the integrals. Read the compatibility of the two increment
  representations of `duality_defect_eq_integral` on `Clock.atomPoset`, drop the
  symmetric part of `γ`, and apply `dualityDefect_eq_zero_of_nonneg`;
  `duality_defect_eq_integral` at `s = 0` turns `Ψ t t = 0` into
  `Φ t 0 = Φ 0 t`. The predictable convention is a hypothesis of the statement,
  not a limitation of the proof: with `Ioc 0 s` in place of `Iio s` the matrix is
  `V s a = if a ≤ s ∧ a ≠ 0 then m a else 0`, whose diagonal does not vanish, so
  `V` is not nilpotent, `Matrix.exists_isSymm_mulVec_one_eq_single` does not
  apply, and the conclusion is false. The counterexample is the diamond
  `0 < a, b < c` with `m a = 1`, `m b = 4`, `m c = 2`, where `𝟙` is orthogonal to
  the left eigenvector of `V` for the eigenvalue `m c`; the condition is
  `m c ^ 2 = m a * m b`. The optional convention on a chain is the predictable
  one for the reflected chain, and `atomGrid_symm` covers it; a general partial
  order offers no reflection and no substitute. Along a chain the
  conclusion sharpens, by `atomGrid_symm`, to `Φ (u i) (u j) = Φ (u j) (u i)` at
  every pair and hence to `γ` symmetric there — with masses of either sign, where
  `dualityDefect_eq_zero_of_nonneg` needs `0 ≤ m`. That sharpening is a chain
  phenomenon: at incomparable pairs `Φ s t = Φ t s` fails, while the defect
  `Φ t 0 - Φ 0 t` still vanishes. With `duality_of_atomless`,
  `duality_of_mixed`, `duality_of_atomic_intervalFinite`,
  `duality_of_atomic_twoChains_of_bounded`,
  `duality_of_atomic_blockStack_of_bounded`,
  `duality_of_atomic_weakOrder_of_integrable` and
  `duality_of_atomic_finiteHeight_of_integrable` this covers every clock that is
  atomless, or has finitely many atoms below the point in question, or is mixed
  with finitely many atoms there, or whose atoms below the point form an
  interval-finite chain, or a discrete chain with interval-finite block
  quotient and `Φ` bounded, or a totally preordered set of atoms — a chain, an
  antichain, or any stack of antichains — with `γ` integrable for `m ⊗ m` on
  atom pairs, or an arbitrary poset of bounded chain length with the same
  integrability. The last two of the eight ask nothing of the order type and
  everything of the density; the ones before them ask nothing of the density
  and something of the order type or of the value `Φ`. What none of the eight
  reaches is a set of atoms of unbounded chain length whose incomparability is
  not transitive, or a chain carrying a `γ` that is neither `m ⊗ m`-integrable
  nor attached to a bounded `Φ`. Where incomparability is transitive the
  finiteness is not a convenience of the matrix proof but a hypothesis of the
  statement:
  `exists_atomic_antichain_duality_ne` produces infinitely many incomparable
  atoms of positive summable mass on which the conclusion fails, and
  `duality_of_atomic_weakOrder_of_integrable` is what survives there.
* `duality_of_atomic_antichain_of_integrable`: with `Φ, γ` as in
  `chain_identity` and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` below which
  the atoms are pairwise **incomparable**, and `γ` integrable for `m ⊗ m` on
  pairs of atoms below `t`, one has `Φ t 0 = Φ 0 t`. Read the compatibility of
  the two increment representations on the antisymmetric part `κ = γ - γ.swap`:
  the relation at a pair `(a, t)` with `a` an atom gives
  `∑' b, m b * κ b a = Φ t 0 - Φ 0 t` for every atom `a`, and summing that
  against `m a` turns the left side into `∑' (a, b), m a * m b * κ b a`, which
  vanishes by antisymmetry and `Summable.tsum_comm`, and the right side into
  `(Φ t 0 - Φ 0 t) * q (Iio t)`. Integrability is exactly what licenses the
  interchange, and it is the same hypothesis as in
  `duality_of_atomic_chain_of_integrable`, so the two together are the
  integrable case of an antichain and of a chain. Both are the special cases
  of `duality_of_atomic_weakOrder_of_integrable` in which the layer chain has
  one layer, respectively one point per layer.
* `Clock.atomLayers`: for a preordered `T`, a purely atomic clock `q` and a `t`
  such that the atoms below `t` are **totally preordered** — `a ≤ b ∨ b ≤ a`
  for any two of them, equivalently their incomparability is transitive — the
  layer chain `Antisymmetrization` of those atoms, a linear order, together
  with the layer masses `λ p = ∑' a ∈ p, m a`, the conditional laws
  `π p a = m a / λ p` on each layer of positive mass, and the two facts that
  carry everything else: `Iio s = ⋃ p < ⟦s⟧, p` for every atom `s`, so
  `q (Iio s)` and more generally `∑' a < s, m a * f a` depend on `s` only
  through `⟦s⟧`, and `q (Iio t) = ∑' p, λ p`. The order side is Mathlib:
  `Antisymmetrization α r` is the quotient by `AntisymmRel`
  (`Order/Antisymmetrization.lean:125`), `toAntisymmetrization` is the
  projection (`:131`), `instPartialOrderAntisymmetrization` (`:263`) makes it
  a partial order for any `Preorder`, and it is a `LinearOrder` under
  `[@Std.Total α (· ≤ ·)]` together with `[DecidableLE α] [DecidableLT α]`
  (`:308`), which classical choice supplies. The two transport lemmas are
  there as well: `toAntisymmetrization_le_toAntisymmetrization_iff` (`:317`)
  and `toAntisymmetrization_lt_toAntisymmetrization_iff` (`:322`), the second
  being what turns `Iio s` into a union of layers. What is new is the
  transport of the clock.
* `Clock.atomLayerKernel`: for `κ : T → T → ℝ` antisymmetric with
  `∑' (a, b), m a * m b * |κ a b| < ∞` on atoms below `t`, the averaged kernel
  `κ̃ p l = ∑' (a, b), π p a * π l b * κ a b` on `Clock.atomLayers`. It is
  antisymmetric, every defining sum converges absolutely, and
  `∑' (p, l), λ p * λ l * |κ̃ p l| ≤ ∑' (a, b), m a * m b * |κ a b|`, so the
  integrability hypothesis descends to the layer chain.
* `atomLayerKernel_increment_eq`: the averaged system is the system of the
  averaged data. With `Ψ s t = ∑' a < s, m a * κ a t` and
  `Ψ̃ p l = ∑' o < p, λ o * κ̃ o l` one has `Ψ̃ p l = ∑' b ∈ l, π l b * Ψ a b`
  for any `a ∈ p`, and in particular `Ψ̃ p p = ∑' a ∈ p, π p a * Ψ a a`: the
  diagonal of the averaged system is the layer average of the diagonal. Both
  are `Summable.tsum_comm` on `Clock.atomLayers`, using that `Ψ a b` depends
  on `a` only through `⟦a⟧`.
* `atomLayerKernel_rel`: if `Ψ s t + Ψ t s = Ψ s s + Ψ t t` at every
  **comparable** pair of atoms below `t`, then `Ψ̃ p l + Ψ̃ l p = Ψ̃ p p + Ψ̃ l l`
  at every pair of layers. For `p ≠ l` every pair from `p × l` is comparable,
  and the claim is the average of the relation against `π p ⊗ π l` together
  with `atomLayerKernel_increment_eq`; for `p = l` it is trivial.
* `duality_of_atomic_weakOrder_of_integrable`: with `Φ, γ` as in
  `chain_identity` and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` below which
  the atoms are totally preordered and the point `t` itself alone in its layer,
  and `γ` integrable for `m ⊗ m` on pairs of atoms below `t`, one has
  `Φ t 0 = Φ 0 t`. Read the compatibility of the two increment representations
  on `κ = γ - γ.swap`, push the whole system to `Clock.atomLayers` by
  `Clock.atomLayerKernel`, and apply `duality_of_atomic_chain_of_integrable`
  there: `atomLayerKernel_rel` supplies its hypothesis,
  `Clock.atomLayerKernel` its integrability, and
  `atomLayerKernel_increment_eq` returns the conclusion at the top layer,
  which is `Φ t 0 - Φ 0 t` because `t` is alone there. Transitivity of
  incomparability is what the proof uses and all it uses: it is exactly the
  statement that `Iio s` depends on `s` only through its layer. The smallest
  order in which it fails is `0 < a, b` with `a < c`, `b` incomparable to `c`
  and to `a`, where `Iio b ≠ Iio c` although `b` and `c` are incomparable.
* `exists_atomic_antichain_duality_ne`: there are a preordered `T` with a least
  element, a purely atomic clock `q` of finite total mass whose atoms below `t`
  are pairwise incomparable and carry strictly positive masses, and
  `Φ, γ : T → T → ℝ` satisfying both increment representations of
  `chain_identity` with `γ₁ = γ₂ = γ` at every comparable pair, all integrals
  existing, such that `Φ t 0 ≠ Φ 0 t`. Take `T = {0} ∪ A ∪ {t}` with
  `A = {a i | i : ℕ}` an antichain, `q {0} = 0`, `m i > 0` summable with total
  mass `M` and tails `σ i`, and
  `κ (a i) (a j) = (if j < i then 1 else if i < j then -1 else 0) * (σ (i ⊓ j) * σ (i ⊓ j + 1))⁻¹`,
  `κ (a j) 0 = κ (a j) t = M⁻¹ ^ 2`, `γ = κ / 2`. The identity
  `m j * (σ j * σ (j+1))⁻¹ = (σ (j+1))⁻¹ - (σ j)⁻¹` telescopes the row sums to
  `∑' j, m j * κ (a j) (a i) = M⁻¹` for every `i`, which is the relation at
  `(a i, t)`; the relations at `(0, a i)` and at pairs from `A` are trivial
  because `q (Iio (a i)) = 0`. Every row converges absolutely, with
  `∑' j, m j * |κ (a j) (a i)| = 2 * (σ i)⁻¹ - M⁻¹`, so the integrals of the
  increment representation exist, while `∑' (i, j), m i * m j * |κ (a i) (a j)|`
  diverges. `Φ` takes three values, so boundedness of `Φ` is not a substitute
  for the integrability of `γ` outside chains. This is the sharpness statement
  for the finiteness hypothesis of `duality_of_atomic` and for the
  integrability hypothesis of `duality_of_atomic_antichain_of_integrable`.
* `duality_of_atomic_intervalFinite`: with `Φ, γ` as in `chain_identity` and
  `γ₁ = γ₂ = γ`, a purely atomic clock, and a `t` below which the atoms are
  pairwise comparable and **interval-finite** — any two of them enclose only
  finitely many others — one has `Φ t 0 = Φ 0 t`, in either convention, with
  no hypothesis beyond the existence of the integrals. Interval-finiteness
  makes the atoms below `t` order isomorphic to an interval of `ℤ`; each
  interval between consecutive atoms carries a single atom, so the increment
  representation collapses to one-step relations, and `atomGrid_symm_int`
  applied to the antisymmetric part gives `Φ (u i) (u j) = Φ (u j) (u i)` at
  every pair of atoms. The two boundaries are reached by tails: for a purely
  atomic clock the existence of the integrals in the increment representation
  is the absolute convergence of the atom sums, so the `q`-integrals over
  `Iio (u k)` and over `Ico (u k) t` vanish along the enumeration, in both
  coordinates, and no bound on `γ` or on its antisymmetric part enters. The
  conclusion sharpens as on finite chains to symmetry of `Φ` at every pair
  below `t`. This subsumes the chain case of `duality_of_atomic` and covers
  atoms accumulating at `0`, at interior points, and at `t` itself, of order
  types `ω`, `ω*` and `ζ`. Interval-finiteness is the exact reach of the
  induction, and strictly stronger than every atom having a neighbouring atom
  on both sides: two chains of type `ζ` stacked one above the other have
  neighbours at every atom while pairs from different chains enclose
  infinitely many atoms, the one-step relations alone leave the cross pairs
  free, and any argument there must use the increment representation across
  the accumulation point between the chains, which is what
  `duality_of_atomic_twoChains_of_bounded` does.
* `tailProduct`: for `μ : ℤ → ℝ` with `0 < μ i` and `Summable μ`, the function
  `tailProduct μ i c = ∏' i' : {i' // i < i'}, (1 + c * μ i')` from `ℂ` to `ℂ`,
  together with `Differentiable ℂ (tailProduct μ i)`, the recursion
  `tailProduct μ (i-1) c = (1 + c * μ i) * tailProduct μ i c`, the bound
  `‖tailProduct μ i c‖ ≤ Real.exp (∑' i, Real.log (1 + ‖c‖ * μ i))`, the lower
  bound `1 ≤ ‖tailProduct μ i c‖` for `0 ≤ c.re` from `1 ≤ ‖1 + c * μ‖` there,
  `Tendsto (fun i ↦ tailProduct μ i c) atTop (𝓝 1)`, and boundedness of
  `fun i ↦ tailProduct μ i c` on `Iic i₀`. The exponent is of type zero:
  `Tendsto (fun r : ℝ ↦ (∑' i, Real.log (1 + r * μ i)) / r) atTop (𝓝 0)`, from
  `Real.log_le_sub_one_of_pos`
  (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:307`) giving the summable
  dominant `μ i` for each quotient and `tendsto_tsum_of_dominated_convergence`
  (Tannery, `Mathlib/Analysis/Normed/Group/Tannery.lean:45`). The product
  converges by `multipliable_one_add_of_summable`
  (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:171`). Summability of
  `μ` is what makes the product converge and the exponent sublinear, and it is
  the finite mass of the clock.
* `norm_le_of_bddOn_imAxis_of_subexponential`: for `f : ℂ → ℂ` with
  `Differentiable ℂ f`, `∀ ε > 0, ∃ A, ∀ z, ‖f z‖ ≤ A * Real.exp (ε * ‖z‖)` and
  `∀ y : ℝ, ‖f (y * I)‖ ≤ C`, one has `‖f z‖ ≤ C` for every `z`, hence `f` is
  constant by `Differentiable.exists_eq_const_of_bounded`
  (`Mathlib/Analysis/Complex/Liouville.lean:128`). Apply
  `PhragmenLindelof.right_half_plane_of_bounded_on_real`
  (`Mathlib/Analysis/Complex/PhragmenLindelof.lean:717`) to
  `fun z ↦ f z * Complex.exp (-ε * z)` and to `fun z ↦ f (-z) * Complex.exp (-ε * z)`:
  the growth hypothesis holds with `c = 1`, the imaginary axis bound is `C`
  because the exponential has modulus one there, and the bound along the
  positive real ray is `A * exp ((ε' - ε) * x) → 0` for `ε' < ε`, which is where
  the sublinear exponent is used; let `ε` tend to `0`. Mathlib's version asks
  for a bound on the real ray in addition to the one on the axis, and the
  auxiliary exponential is what supplies it.
* `tailProduct_pairing_eq_zero`: for `μ` as in `tailProduct` and
  `a : ℤ → ℝ` with `Summable fun i ↦ |a i|`, if
  `∑' i, a i * tailProduct μ i c = 0` for every `c` with `0 ≤ c.re`, then
  `a = 0`. Split the sum at a foot point `i₀` using the recursion: below `i₀`
  the quotient `tailProduct μ i c / tailProduct μ i₀ c` is the polynomial
  `∏ i' ∈ Ioc i i₀, (1 + c * μ i')`, above it the reciprocal of such a product,
  whose modulus is at most one on `0 ≤ c.re`. The polynomial part is entire and
  subexponential, the reciprocal part is bounded by `∑' i, |a i|`, so
  `norm_le_of_bddOn_imAxis_of_subexponential` makes the polynomial part
  constant; along real `c → ∞` the reciprocal part tends to `0`, so the
  constant is `0`, and evaluating at `c = 0` gives `∑ i ≤ i₀, a i = 0` for every
  `i₀`. Differences of consecutive `i₀` give `a = 0`. No hypothesis beyond
  `ℓ¹`.
* `crossGrid_eq_zero_of_bddFlux`: let `μ ν : ℤ → ℝ` be positive and summable and
  let `x : ℤ → ℤ → ℝ` have `Summable fun i ↦ μ i * |x i j|` for every `j` and
  `Summable fun j ↦ ν j * |x i j|` for every `i`, and satisfy
  `∑' i' < i, μ i' * x i' j = - ∑' j' ≥ j, ν j' * x i j'` for all `i, j`. Write
  `F i j` for the common value and `R j = ∑' i, μ i * x i j`. If
  `∃ j₀, BddAbove (Set.range fun p : ℤ × {j // j₀ ≤ j} ↦ |F p.1 p.2|)`, then
  `x = 0`. Put `G j c = ∑' i, μ i * F i j * tailProduct μ i c`; Abel summation
  with the recursion of `tailProduct` gives
  `∑' i, μ i * x i j * tailProduct μ i c = R j + c * G j c`, termwise
  differencing in `j` gives `G (j+1) = (1 + c * ν j) * G j + ν j * R j`, the
  bound on `F` and summability of `μ` give a `j`-uniform summable dominant, so
  `G j c → 0` as `j → ∞` by dominated convergence, and iterating the recursion
  bounds `‖G j c‖` by `∑' j ≥ j₀, ν j * |R j|`, finite because `‖R j‖` is
  bounded and `ν` is summable. Then
  `norm_le_of_bddOn_imAxis_of_subexponential` makes each `G j` constant, and
  comparing the coefficient of `c` in the recursion gives `G j = 0` and
  `R j = 0`; `tailProduct_pairing_eq_zero` applied to `fun i ↦ μ i * x i j`
  gives `x · j = 0` for `j ≥ j₀`. Rows below `j₀` follow one at a time: if all
  rows above `j` vanish then `F i j = - ν j * x i j`, so
  `F (i+1) j = (1 - μ i / ν j) * F i j`, the products converge absolutely by
  summability of `μ`, and `F i j → 0` as `i → -∞` forces `F · j = 0`.
* `duality_of_atomic_twoChains_of_bounded`: with `Φ, γ` as in `chain_identity`
  and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` below which the atoms are
  pairwise comparable and form two interval-finite chains stacked one above the
  other — every atom of the lower chain below every atom of the upper one — and
  `Φ` bounded on `Iic t ×ˢ Iic t`, one has `Φ t 0 = Φ 0 t`, in either
  convention. Inside each chain `duality_of_atomic_intervalFinite` gives
  symmetry, so the antisymmetric part `w s t = Φ s t - Φ t s` vanishes there and
  `γ` survives only on cross pairs `x i j = γ (b i) (a j)`; continuity of `Φ` at
  the accumulation point in both coordinates, which is the vanishing of the
  atom-sum tails, turns the increment representation into the hypothesis of
  `crossGrid_eq_zero_of_bddFlux` with `F i j = w (b i) (a j)`, and boundedness
  of `Φ` is boundedness of `F`. This is the first item that crosses an
  accumulation point of atoms, and it does so by the north limit of `G`, not by
  an induction. Boundedness of `Φ` is a bound on the value and not on `γ`; the
  probabilistic source of such a `Φ` supplies it, since the domination
  hypotheses of `duality` bound `𝔼[f (X s, Y t) * exp (∫_0^s α + ∫_0^t β)]` by
  `exp (C T) * 𝔼[Γ T]` for `s, t ≤ T`.
* `Clock.atomBlocks`: for a clock `q` and a `t` below which the atoms form a
  chain in which every atom has an immediate predecessor and an immediate
  successor among the atoms, the quotient of the atoms by "only finitely many
  atoms lie in between", together with the statements that each class is convex
  and order isomorphic to `ℤ`, that consecutive atoms of the whole chain are
  consecutive in their class, and that the quotient carries a linear order. The
  classes are the objects `duality_of_atomic_intervalFinite` settles, and the
  quotient is what the next item runs its induction on.
* `duality_of_atomic_blockStack_of_bounded`: with `Φ, γ` as in `chain_identity`
  and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` below which the atoms form a
  chain as in `Clock.atomBlocks` whose quotient is interval-finite, and `Φ`
  bounded on `Iic t ×ˢ Iic t`, one has `Φ t 0 = Φ 0 t`, in either convention.
  Induct on the distance `d P Q` of two blocks in the quotient, which is finite
  by interval-finiteness. At `d = 0` this is `duality_of_atomic_intervalFinite`.
  At `d ≥ 1`, with `P` below `Q`, the discreteness of the atom chain makes
  `Ico (b i) (b (i+1))` and `Ico (a j) (a (j+1))` carry a single atom each, so
  `F i j = Φ (b i) (a j) - Φ (a j) (b i)` satisfies the two increment relations
  of `crossGrid_eq_zero_of_bddFlux` with `x i j = γ (b i) (a j) - γ (a j) (b i)`;
  the limits at the two facing edges are the values at the largest block of
  `Ico P Q` and the smallest block of `Ioc P Q`, reached as tails of the
  absolutely convergent atom sums, and vanish by the inductive hypothesis at
  distance `d - 1`. Boundedness of `Φ` bounds `F`, so
  `crossGrid_eq_zero_of_bddFlux` gives `F = 0`. Blocks of order type `ℤ` and a
  quotient of order type `ℤ` are both allowed, so this covers atom sets with
  countably many accumulation points; `duality_of_atomic_twoChains_of_bounded`
  is the case of two blocks. Its reach is the one-step relations, hence chains
  in which every atom has neighbours; chains without neighbours are the subject
  of `duality_of_atomic_chain_of_integrable`, which replaces the one-step
  relations by a Stieltjes product rule and asks integrability of `γ` instead.
* `HasAtomIncrements`: for a linear order `T`, a countable `A : Set T` and
  `j : A → ℂ` with `Summable fun a ↦ ‖j a‖`, the predicate
  `∀ s t, s ≤ t → f t - f s = ∑' a : {a : A // (a : T) ∈ Set.Ico s t}, j a` on
  `f : T → ℂ`, together with: the difference of two functions with the same
  increments is constant, `f` is bounded when `A` is bounded in mass and `f` is
  bounded at one point, the jump `j a = f a⁺ - f a` is recovered as
  `Tendsto (fun n ↦ f (t n) - f a) atTop (𝓝 (j a))` along any sequence
  `t n ∈ A` decreasing with `⋂ n, Set.Ioo a (t n) ∩ A = ∅`, and the existence
  of such a sequence for every non-maximal `a` from countability of `A`. This
  is the increment representation of the manuscript read as a predicate, and it
  is all that survives of an atomic clock when the atoms have no neighbours.
* `HasAtomIncrements.mul`: if `f` has increments `j` and `g` has increments
  `k`, both bounded, then `f * g` has increments
  `fun a ↦ f a * k a + g a * j a + j a * k a`. Expand the jumps of `f * g` over
  `Ico s t`, write `f a = f s + ∑ a' < a, j a'` and likewise for `g`, and split
  the resulting double sum into the parts `a' < a`, `a' > a` and `a' = a`; all
  rearrangements are absolutely convergent. This is Abel summation with no
  successor function, and it is what carries the transformation method from
  `ℤ`-indexed chains to arbitrary countable ones.
* `chainTailProduct`: for a countable `A` in a linear order and `m : A → ℝ`
  with `0 < m a` and `Summable m`, the function
  `chainTailProduct m a c = ∏' a' : {a' // a < a'}, (1 + c * m a')` from `ℂ` to
  `ℂ`, and `chainProduct m s c = ∏' a' : {a' // s ≤ a'}, (1 + c * m a')`,
  together with `Differentiable ℂ (chainTailProduct m a)`, the identity
  `chainProduct m s c = (1 + c * m a) * chainTailProduct m a c` when `a` is the
  least element of `A ∩ Ici s`, the bound
  `‖chainTailProduct m a c‖ ≤ Real.exp (∑' a, Real.log (1 + ‖c‖ * m a))` with
  the type-zero statement for that exponent, the bounds
  `1 ≤ ‖chainTailProduct m a c‖` and
  `‖chainTailProduct m a c‖ ≤ ‖chainProduct m ⊥ c‖` for `0 ≤ c.re`, the lower
  bound `∏' a, (1 + m a ^ 2 * ‖c‖ ^ 2) ^ (1/2 : ℝ) ≤ ‖chainProduct m ⊥ c‖` for
  `0 ≤ c.re` from `1 + m ^ 2 * ‖c‖ ^ 2 ≤ ‖1 + c * m‖ ^ 2`, and
  `HasAtomIncrements (fun s ↦ chainProduct m s c) (fun a ↦ - c * m a * chainTailProduct m a c)`
  from the telescoping identity
  `∏ a ∈ S, (1 + z a) - 1 = ∑ a ∈ S, z a * ∏ a' ∈ S, a < a', (1 + z a')`. The
  convergence and the sublinear exponent are the same facts as in
  `tailProduct`, of which this is the version for an arbitrary index chain.
* `chainTailProduct_pairing_eq_zero`: for `m` as in `chainTailProduct` and
  `α : A → ℝ` with `Summable fun a ↦ |α a|`, if
  `∑' a, α a * chainTailProduct m a c = 0` for every `c` with `0 ≤ c.re`, then
  `α = 0`. Split the sum at a foot point `s₀ : T`: below `s₀` the quotient by
  `chainProduct m s₀ c` is the entire subexponential product over
  `A ∩ Ioo a s₀`, above it the reciprocal of the product over `A ∩ Icc s₀ a`,
  of modulus at most one on `0 ≤ c.re`. The first part is constant by
  `norm_le_of_bddOn_imAxis_of_subexponential`, and along real `c → ∞` the
  second tends to `0`, so the constant is `0`; evaluating at `c = 0` gives
  `∑' a < s₀, α a = 0` for every `s₀`, and the jump statement of
  `HasAtomIncrements` gives `α = 0`. This is `tailProduct_pairing_eq_zero`
  with the foot-point decomposition read on a chain rather than on `ℤ`.
* `atomDiag_eq_zero_of_integrable`: let `A` be countable in a linear order with
  a least element `0` and a greatest element `t`, let `m : A → ℝ` be positive
  and summable, and let `h : A → T → ℝ` satisfy `h a 0 = 0`,
  `h a b + h b a = h a a + h b b` for `a b : A`, and `H s u + H u s = 0` for all
  `s u : T`, where `H s u = ∑' a < s, m a * h a u` and every such series
  converges absolutely, together with `Summable fun p : A × A ↦ m p.1 * m p.2 * |h p.1 p.2|`.
  Then `h a a = 0` for every `a : A`. Put `Δ u = ∑' a < u, m a * h a a`,
  `κ a u = h a u - h a a`, `w s u = H s u + Δ u - Δ s`, so that `w` has
  increments `fun a ↦ m a * κ a u` in its first argument, `κ` is antisymmetric
  on `A × A` and `w` is antisymmetric. `HasAtomIncrements.mul` applied to
  `w · u` and `chainProduct m · c` gives
  `∑' a, m a * κ a u * chainTailProduct m a c - c * ∑' a, m a * w a u * chainTailProduct m a c = w t u - Δ u * chainProduct m ⊥ c`.
  Summing that identity at `u = b : A` against `m b * chainTailProduct m b c`
  kills both double sums by antisymmetry and gives `P = chainProduct m ⊥ · * Q`
  for `P c = ∑' a, m a * w t a * chainTailProduct m a c` and
  `Q c = ∑' a, m a * Δ a * chainTailProduct m a c`; the identity at `u = 0`
  gives `R = Δ t + c * Q` for `R c = ∑' a, m a * h a a * chainTailProduct m a c`,
  and at `u = t` it gives `S = R * (1 - chainProduct m ⊥ ·)` for
  `S c = ∑' a, m a * h a t * chainTailProduct m a c`. The lower bound on
  `‖chainProduct m ⊥ c‖` makes `R` bounded on `0 ≤ c.re`, so
  `norm_le_of_bddOn_imAxis_of_subexponential` makes `R` constant, whence
  `Q = 0`, whence `Δ a = 0` for every atom by
  `chainTailProduct_pairing_eq_zero`, whence `h a a = 0` at every non-maximal
  atom by the jump statement of `HasAtomIncrements`; at a maximal atom,
  `P = 0` and antisymmetry give `H a t = - Δ t` for every atom, and the tail of
  the absolutely convergent series at the bottom of `A` gives `Δ t = 0`.
* `duality_of_atomic_chain_of_integrable`: with `Φ, γ` as in `chain_identity`
  and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` below which the atoms are
  pairwise comparable, and `γ` integrable for `m ⊗ m` on pairs of atoms below
  `t`, one has `Φ t 0 = Φ 0 t`, in either convention. The two increment
  representations of `duality_defect_eq_integral`, read on the antisymmetric
  part, are the hypotheses of `atomDiag_eq_zero_of_integrable` with
  `h a u = κ a u - κ a 0` and `κ = γ - γ.swap`, and the duality defect is
  `- Δ t`. No hypothesis on the order type of the atom set enters: it may be
  dense in itself, and its Cantor–Bendixson rank is unrestricted. Bounded `γ`
  on atom pairs is the readable sufficient condition for the integrability,
  and it is a hypothesis on the density and not on the value, so this item and
  `duality_of_atomic_twoChains_of_bounded` are incomparable.
* `Clock.IsAtomCertificate`: for a purely atomic clock `q` with atom masses
  `m : T → ℝ≥0` of finite total mass `M`, a finite `Z : Finset T`, weights
  `w s = m s + (if s ∈ Z then 1 else 0)` and a point `t`, the predicate on
  `T : T → T → ℝ` given by: `T` is symmetric, `∃ C, ∀ s u, |T s u| ≤ C * w s * w u`,
  `m u * ∑' a, (if u < a then T s a else 0) = m s * ∑' a, (if s < a then T a u else 0)`
  for all `s, u`, and `∑' a, T s a = if s = t then 1 else 0`. It is the
  transcription of "`T` symmetric, `T * V` symmetric, `T *ᵥ 1 = single t 1`"
  from `atomPoset_certificate` to a countable atom set, with the one bound that
  licenses the rearrangements.
* `atomDiag_eq_zero_of_isAtomCertificate`: let `κ : T → T → ℝ` be antisymmetric
  with `∑' (a, b), m a * m b * |κ a b| < ∞` and `∑' b, m b * |κ b z| < ∞` for
  every `z ∈ Z`, put `Ψ s u = ∑' a < s, m a * κ a u`, and assume
  `Ψ s u + Ψ u s = Ψ s s + Ψ u u` at every pair. If `Clock.IsAtomCertificate`
  holds at `t`, then `Ψ t t = 0`. The proof is `atomPoset_certificate`'s two
  lines with `Summable.tsum_comm` in front of each: the triple sum
  `∑' (s, a, b), |T s a| * (if b < a then m b else 0) * |κ b s|` is bounded by
  `C * (M + Z.card) * (∑' s, m s * ρ s + ∑' z ∈ Z, ρ z)` with
  `ρ s = ∑' b, m b * |κ b s|`, so `trace (T * (V * K)) = trace ((T * V) * K)`;
  the first equals `Ψ t t` by the relation and `∑' u, T s u = if s = t then 1 else 0`,
  the second vanishes because `T * V` is symmetric and `K` antisymmetric.
  Integrability enters only as the licence for two relabellings, and
  `exists_atomic_antichain_duality_ne` is the witness that it cannot be
  dropped: there the certificate exists and is bounded, and the two orders of
  summation of `trace ((T * V) * K)` differ by twice the duality defect.
* `exists_isAtomCertificate_of_finiteHeight`: if there is an `r` such that no
  chain `c 0 < c 1 < ⋯ < c r` of atoms has `m (c i) ≠ 0` for `i < r` — the
  entries of the `r`-th power of `V s a = if a < s then m a else 0` are the
  sums of `m (c 0) * ⋯ * m (c (r-1))` over chains, all nonnegative, with row
  sums at most `M ^ r` — then for every `t` there are a `Z` of at most two
  points and a `T` with `Clock.IsAtomCertificate`. Take
  `u = V ^ (r-1) *ᵥ 1`, nonzero because a nonnegative matrix with vanishing
  row sums is zero (`mulVec_one_eq_zero_iff_of_nonneg`, unchanged for a
  countable index because the row sums converge), pick `i✶` with `u i✶ ≠ 0`
  and build `T` by the formula of `exists_isSymm_mulVec_one_eq_single`. The
  bound is the only new step and is one line: `(Vᵀ *ᵥ x) c = m c * ∑' s > c, x s`
  gives `‖Vᵀ *ᵥ x‖₁ ≤ M * ‖x‖₁` and `|(Vᵀ *ᵥ x) c| ≤ m c * ‖x‖₁`, so every
  vector entering the formula is `ℓ¹` and dominated by `w` except for the two
  seeds `single t 1` and `single i✶ (u i✶)⁻¹`, which is what `Z = {t, i✶}` is
  for.
* `duality_of_atomic_finiteHeight_of_integrable`: with `Φ, γ` as in
  `chain_identity` and `γ₁ = γ₂ = γ`, a purely atomic clock, a `t` such that
  the atoms below `t` have **bounded chain length**, and `γ` integrable for
  `m ⊗ m` on pairs of atoms below `t`, one has `Φ t 0 = Φ 0 t`. Compose the
  previous two items on `κ = γ - γ.swap`. Nothing is asked of the
  incomparability: it need not be transitive, so this is the first item that
  reaches posets which are not weak orders, and the layers may be infinite.
  It contains `duality_of_atomic_antichain_of_integrable` as the case `r = 2`
  and `duality_of_atomic` as the case of a finite atom set, where the
  integrability is vacuous. It is incomparable with
  `duality_of_atomic_chain_of_integrable` and with
  `duality_of_atomic_weakOrder_of_integrable`, both of which live on atom sets
  of unbounded chain length.
* `not_exists_isAtomCertificate_of_isDirected_of_noMinOrder`: let `t` be the
  greatest element of the poset with `m t = 0`, and let the atom set
  `A = {a | m a ≠ 0}` be nonempty, directed downwards and without a minimal
  element. Then there is no `T` with `Clock.IsAtomCertificate` at `t`, for any
  `Z`. Three steps. The relation at `(s, u)` with `m s = 0` and `u ∈ A` gives
  `θ (Ioi u) = 0` for `θ = T s ·`, absolutely summable by the bound. Directed
  downwards, countable and without a minimal element gives a strictly
  decreasing `u : ℕ → A` with `u n < v n` for a fixed enumeration `v` of `A`,
  so `Ioi (u n) ↑ ⋃ a ∈ A, Ioi a`, and `tendsto_tsum_compl_atTop_zero`
  (`Topology/Algebra/InfiniteSum/Group.lean`, the `to_additive` twin of
  `tendsto_tprod_compl_atTop_one`) makes every row with `m s = 0` supported on
  `L = {x | ∀ a ∈ A, ¬ a < x}`. Every point of `L` carries zero mass and `t`
  does not lie in `L`, so `1 = ∑' x, T t x = ∑' x ∈ L, T t x = ∑' x ∈ L, T x t
  = 0`. The hypotheses are exactly the negation of well-foundedness of `A` in
  the presence of downward directedness, so this and
  `exists_isAtomCertificate_of_finiteHeight` bound the certificate method from
  both sides; it stops where `duality_of_atomic_chain_of_integrable` takes
  over, and the two are genuinely different tools: neither hypothesis implies
  the other. It contains the case of a chain `A` with neither a least nor a
  greatest element.
* `duality_of_atomic_idealExhaustion`: with `Φ, γ` as in `chain_identity` and
  `γ₁ = γ₂ = γ`, a purely atomic clock on a countable partial order with least
  element `0`, `m ≥ 0`, and a `t` such that (i) `Φ a 0 = Φ 0 a` for every
  `a < t` — supplied by `duality_of_atomic` on the ideal `Iic a` whenever that
  ideal is finite — and (ii) the set `W = Iio t` is **directed upwards and has
  no maximum**, one has `Φ t 0 = Φ 0 t`. No `m ⊗ m`-integrability, no bound on
  `Φ`, no certificate. Proof: put `g c = m c * (γ c 0 - γ 0 c)`; the increment
  representation at `(t, 0)` reads `Φ t 0 - Φ 0 t = ∑' c ∈ Iio t, g c`
  (absolutely convergent — it is the existence of the integrals), and (i) says
  `∑ c ∈ Iio a, g c = 0` for every `a ∈ W`. A countable directed set without
  maximum has a strictly increasing cofinal sequence `a n` (Mathlib:
  `IsDirected`, `exists_seq_strictMono_tendsto` in spirit; here build it by
  hand from an enumeration), `Iio (a n) ↑ W`, and `tendsto_tsum_compl_atTop_zero`
  (or `Summable.tendsto_sum_tsum_nat` along the increasing sets) gives
  `∑' c ∈ W, g c = lim n, ∑ c ∈ Iio (a n), g c = 0`. The same two lines cover
  two further shapes of `W`, which should be separate lemmas sharing the proof:
  `W \ {0}` a disjoint union of pairwise incomparable directed pieces without
  maxima (the finite sums over `⋃ k ≤ n, Iio (a k n)` are sums over the pieces
  because the ideals meet only in `{0}`, where `g 0 = 0`), and every
  `c ∈ W \ {0}` **chain-covered**, i.e. with an `a ∈ W` such that
  `Iio a = Iic c` (then `g c = 0` for each `c` singly, and the tail of the
  absolutely convergent series does the rest). The general form behind all
  three — `δ t = 0` whenever `𝟙_W` lies in the bounded pointwise sequential
  closure of the span of the ideal indicators `𝟙_{Iio a}`, `a ∈ W`, and its
  extension by a set `X` of minimal atoms with `𝟙_{W \ X}` in that closure
  (Task 23, run 32, Theorem 38) — is not what should be formalised first; the
  three concrete shapes are. What they settle, all for arbitrary summable
  masses: the **ladder** `a i < b j ↔ i < j` (directed: `a i, b j < b (max i j + 1)`;
  every `Iic` finite), on which no item above applies for `m ⊗ m`-non-integrable
  `γ` and on which the certificate question of runs 25–31 stays open; the
  **disjoint union of two `ω`-chains**, in particular with the masses
  `m (a i) = B ^ (-i)`, `m (b j) = B ^ (-j) * 2 ^ ((-1) ^ (j+1))`, `B ≥ 16`,
  where `Matrix.certificate_mulVec_pow_one` shows that **no** bounded
  certificate exists — so the certificate method is sufficient and not
  necessary, and this pair is the acceptance test for that; trees without
  leaves, and weak orders of level type `ω` with finite levels, where
  `duality_of_atomic_weakOrder_of_integrable` needed the integrability. It does
  **not** reach two stacked `ζ`-chains (there (i) is the question itself for
  the upper chain), and it does not reach an index in which `W` has maximal
  elements that are not minimal atoms (infinite crown, infinite `N`), which
  remain with `duality_of_atomic_finiteHeight_of_integrable`. The item is two
  lines on top of `duality_of_atomic` and a dominated-convergence step, and it
  is the first in this milestone that reaches an infinite index of infinite
  height with non-transitive incomparability without any hypothesis beyond the
  existence of the integrals.
* `duality_of_atomic_finiteCoreReduction`: the setting of
  `duality_of_atomic_idealExhaustion` — countable partial order with least
  element `0`, `m ≥ 0`, `t` with `W = Iio t`, (i) `Φ a 0 = Φ 0 a` for every
  `a ∈ W` — and, in place of the shape hypothesis on `W`, a **finite down-set
  `K ⊆ W` with `0 ∈ K`** such that `𝟙_{W \ K}` lies in the bounded pointwise
  sequential closure of the span of the ideal indicators `𝟙_{Iio d}`, `d ∈ W`
  (as functions on `W \ {0}`). Then `Φ t 0 = Φ 0 t`. The concrete instance to
  formalise first, as its own lemma: **a finite core `K` with an `ω`-chain
  hanging above each maximal element of `K`**, every `m ≥ 0`, no
  integrability — there every chain point `c` is chain-covered
  (`Iio c' = Iic c`), so `𝟙_{W \ K}` is the pointwise limit of finite sums of
  `𝟙_{Iio c'} - 𝟙_{Iio c}`. Proof (Task 23, run 33, Theorem 39): write
  `P = K \ {0}`, `Z : (P → ℝ) →ₗ (K → ℝ)`, `Z f s = ∑ a ∈ Iio s, f a`, and
  `κ` for the antisymmetric part of `γ`. For `d ∈ W` the relation at `(d, s)`,
  `s ∈ K`, together with (i) says that `s ↦ ∑ a ∈ Iio d, m a * κ a s` restricted
  to `K` equals `-(Z ψ_d)` with `ψ_d b = m b * κ b d` — so it lies in
  `LinearMap.range Z`, which is a closed subspace of the finite-dimensional
  `K → ℝ`; dominated convergence (`tendsto_tsum_of_dominated_convergence`) at
  each of the finitely many `s ∈ K` carries this to the closure, hence to
  `χ s = ∑' c ∈ W \ K, m c * κ c s`. Pick `ψ''` with `Z ψ'' = χ` and, adding a
  multiple of `Pi.single k 1` for a maximal `k ∈ K` (which `Z` kills), with
  `∑ a ∈ P, ψ'' a = ∑' c ∈ W \ K, m c * κ c t`. Then `κ'` on `K ∪ {t}`, equal to
  `κ` on `K × K` and to `κ a t + ψ'' a / m a` in the column `t`, satisfies the
  relations at **all** pairs of the finite poset `K ∪ {t}` with the same
  defect at `t`, and `duality_of_atomic` on that finite poset closes. So the
  item is `duality_of_atomic` plus one dominated-convergence step, exactly like
  its sibling, and it contains `duality_of_atomic_idealExhaustion` as the case
  `K = {0}`. What it settles that nothing above reaches: the doubly hanging
  double bow-tie of run 32 (`p₀ < p`, `q₀ < q`, `r₀ < r`, `s₀ < s`;
  `p, q, r < a`; `p, q, s < a'`; chains above `a` and `a'`), on which every
  exhaustion hypothesis fails and the duality holds through the relation at
  the incomparable pair `(r, s)` — the reduction is what explains that; and all
  980 random cores of `Task23/random_hanging.py`, including the 39 where the
  plain exhaustion failed. The finite conjecture C(K) of run 32
  (`Task23/core_conjecture.py`) is **not** needed for this and should not be
  formalised. Mechanics verified exactly in `Task23/core_reduction.py`
  (rc = 0): the chain values lie in `range Z` on every truncation, and the
  corrected `κ'` satisfies the finite relations on random posets with
  arbitrary down-sets `K`, with mixed signs included (the reduction itself uses
  `m ≥ 0` nowhere; only `duality_of_atomic` does).
* `Lagrange.sum_inv_prod_sub_eq_zero`: for a `Finset s` with `2 ≤ #s` and an
  `x : ι → F` injective on `s`, `∑ k ∈ s, (∏ l ∈ s.erase k, (x k - x l))⁻¹ = 0`,
  while the sum is `(1 : F)` for `#s = 1`. It is `Lagrange.coeff_eq_sum`
  (`LinearAlgebra/Lagrange.lean:490`) at `P = 1`, whose left hand side is
  `(1 : F[X]).coeff (#s - 1)`. It belongs in
  `Mathlib/LinearAlgebra/Lagrange.lean` and not here.
* `Clock.atomTailProduct`: for `m : ℕ → ℝ` with `0 < m k` for all `k`,
  `Summable m` and `Function.Injective m`, the product
  `atomTailProduct m k i = ∏' l : {l // i < l}, (1 - m l / m k)`, together with
  its multipliability and `atomTailProduct m k i ≠ 0`. Multipliability is
  `Real.multipliable_one_add_of_summable`
  (`Analysis/SpecialFunctions/Log/Summable.lean:96`) applied to
  `fun l ↦ - m l / m k`; the value is nonzero because only finitely many `l`
  have `m k ≤ m l`, so the product splits into a finite product of nonzero
  factors and a positive tail, which is `Real.rexp_tsum_eq_tprod`
  (`Analysis/SpecialFunctions/Log/Summable.lean:83`).
* `Clock.atomTailProduct_sub_eq`: with `w m k i = if k ≤ i then
  atomTailProduct m k i else 0`, one has `w m k i - w m k (i-1) =
  m i / m k * w m k i` for all `i, k ≥ 1`. Three cases: `k < i` is the
  definition of the product, `k = i` holds because `w m k (k-1) = 0` and
  `m i / m k = 1`, and `i < k` has both sides zero. The step `k = i` is the
  only one that is not formal.
* `Clock.omegaChainPotential`: for `m` as above,
  `omegaChainPotential m i j = ∑ k ∈ Finset.Icc 1 (min i j),
  (m k * ∏' l : {l // l ≠ k}, (1 - m l / m k))⁻¹ *
  atomTailProduct m k i * atomTailProduct m k j`, a finite sum, together with
  its symmetry, `omegaChainPotential m i 0 = 0`, the recursion
  `m i * (Φ i j - Φ i (j-1)) = m j * (Φ i j - Φ (i-1) j)` for `1 ≤ i, j` and
  `Tendsto (omegaChainPotential m i) atTop (𝓝 (if i = 1 then (m 1)⁻¹ else 0))`.
  The recursion holds for each rank one summand by `atomTailProduct_sub_eq`,
  both sides being `m i * m j / m k * w m k i * w m k j`. The limit is
  `Lagrange.sum_inv_prod_sub_eq_zero` at the nodes `(m k)⁻¹`, `k ≤ i`: the
  tail products cancel against the infinite product in the coefficient, and
  what is left is `∑ k ≤ i, (m k * ∏ l ≤ i, l ≠ k, (1 - m l / m k))⁻¹`.
* `exists_isAtomCertificate_of_omegaChain`: let the poset be
  `T = {0} ∪ Set.range a ∪ {t✶}` with `a : ℕ → T` strictly monotone,
  `0 < a i < t✶`, `m 0 = m t✶ = 0` and atom masses `m i > 0` with `Summable m`
  and `m (i+1) ≤ θ * m i` for some `θ < 1`. Then `Clock.IsAtomCertificate`
  holds at `t✶` with `Z = {0, t✶}` for
  `T (a i) (a j) = - m i * m j * (Φ i j - Φ i (j-1)) / m j`,
  `T t✶ (a 1) = T (a 1) t✶ = 1` and all other entries zero, with
  `Φ = omegaChainPotential m`. The bound of `Clock.IsAtomCertificate` is the
  boundedness of `G i j = (Φ i j - Φ i (j-1)) / m j`, and it is a divided
  difference: `G i j` is `(-1) ^ (j+1) / (∏ l ∈ Finset.Icc 1 j, m l)` times the
  divided difference of `fun c ↦ c * ∏' l : {l // i < l}, (1 - c * m l)`
  at the nodes `(m 1)⁻¹, …, (m j)⁻¹`, so the mean value form and Cauchy's
  estimate on the circle of radius `(m j)⁻¹` give
  `|G i j| ≤ 2 / m j ^ 2 * exp (2 * (∑' l : {l // i < l}, m l) / m j) *
  ∏ l ∈ Finset.Icc 1 j, m j / m l`, which under `m (i+1) ≤ θ * m i` is at most
  `2 / m 1 ^ 2 * exp (2 * θ / (1 - θ)) * θ ^ ((j-1) * (j-4) / 2)`. This is the
  first atom set of infinite height for which the certificate is produced:
  `exists_isAtomCertificate_of_finiteHeight` does not apply because `V` is not
  nilpotent, and `not_exists_isAtomCertificate_of_isDirected_of_noMinOrder`
  does not apply because the atom set has a least element.
* `duality_discrete`: the case `ι = ℕ` with counting measure, which follows from
  `chain_identity` alone and needs none of the analysis, and is the case
  `m ≡ 1` of `duality_of_atomic`.
* `uniqueness_of_duality`: a dual process determines the one dimensional
  distributions, hence, with Milestone 6, gives uniqueness. This is the standard
  application and is the reason the milestone exists.

**Acceptance examples.**

* **The diamond, which fixes the convention.** `ι = {0 < a, b < c}` with
  `m a = 1`, `m b = 4`, `m c = 2`, so that `m c ^ 2 = m a * m b`. In the
  **predictable** convention `V s a = if a < s then m a else 0` is nilpotent and
  `duality_of_atomic` gives `Φ c 0 = Φ 0 c`. In the **optional** convention
  `V s a = if a ≤ s ∧ a ≠ 0 then m a else 0` has `m c` on the diagonal, `𝟙` is
  orthogonal to the left eigenvector of `V` for that eigenvalue, and the
  conclusion is **false**. So the convention is a hypothesis of
  `duality_of_atomic` and not a limitation of the proof, and this is the
  instance that shows a formalization cannot quietly state it for both.
* **The antichain of `ex:antichain`, which fixes the integrability.**
  `ι = {0} ∪ {a i | i : ℕ} ∪ {t✶}` with the `a i` pairwise incomparable,
  `m i > 0` summable of total mass `M`, tails `σ i`, and
  `κ (a i) (a j) = sgn (i - j) / (σ (i ⊓ j) * σ (i ⊓ j + 1))`,
  `κ (a j) 0 = κ (a j) t✶ = M⁻¹ ^ 2`, `γ = κ / 2`. Every row converges
  absolutely — `∑' j, m j * |κ (a j) (a i)| = 2 / σ i - 1 / M` — so all the
  integrals of the increment representation exist, while
  `∑' (i,j), m i * m j * |κ (a i) (a j)|` diverges, and
  `Φ t✶ 0 - Φ 0 t✶ = 1 / M ≠ 0`. This is `exists_atomic_antichain_duality_ne`,
  and it refutes at once: the extension of `duality_of_atomic` from finite to
  countable atom sets, the dropping of the `m ⊗ m`-integrability from
  `duality_of_atomic_antichain_of_integrable`, and — since `Φ` takes three
  values — any attempt to replace that integrability by boundedness of `Φ`.
* **The three order types an interval-finite chain must survive.** Atoms of type
  `ω` accumulating at `t` (`a i = 1 - 2 ^ (-i)`), of type `ω*` accumulating at
  `0` (`a i = 2 ^ (-i)`), and of type `ζ` accumulating at both. Each is
  interval-finite, so `duality_of_atomic_intervalFinite` applies and sharpens to
  `Φ (u i) (u j) = Φ (u j) (u i)` at every pair. Two `ζ`-chains stacked one
  above the other are **not** interval-finite although every atom has both
  neighbours, so the same item does not apply and
  `duality_of_atomic_twoChains_of_bounded` is what covers it. The pair is the
  acceptance test for the reach of the one step induction.
* **The clock with no atoms, and the clock with both.** For `q = volume` on
  `Set.Icc 0 t✶`, `duality_of_atomless` gives `Φ t 0 = Φ 0 t` at **every** `t`
  by the time change `Q t = q (Set.Iio t)`, not merely almost every `t`; for
  `q = volume + ∑ i ≤ N, m i • Measure.dirac (a i)`, `Clock.stretches` computes
  `Set.range Q` as the union of the intervals `S j` with gaps of length exactly
  `m j` at the atoms, and `duality_of_mixed` closes it with no lower bound on
  the diffuse masses `c j` — so `c j = 0` for some `j`, a stretch degenerate to
  a point, is part of the acceptance test and not an excluded case.
* **`duality_discrete` as the collapse test.** `ι = ℕ` with counting measure is
  the case `m ≡ 1` of `duality_of_atomic`, and it follows from `chain_identity`
  alone. Any development of the milestone must reproduce it without invoking the
  matrix algebra, the certificates or the complex analysis; if it cannot, the
  layering of the milestone is wrong.

## Milestone 9: continuous time martingales and the càdlàg modification

Fix `[LinearOrder ι]` with the order topology and a countable dense `D ⊆ ι`, and
`E` metrizable. The stability item below and everything from
`IsMPSolutionFor.integral_comp_stoppedLim_eq` on add `[OrderBot ι]`, and each
says so. The bottom element enters through Mathlib's stopping time API and not
through a choice made here: a stopping time is `WithTop ι`-valued, and the
stopped process that `ProbabilityTheory.IsStable` quantifies over is
`stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ`
(`Mathlib/Probability/Process/LocalProperty.lean:142`, under `variable
[OrderBot ι]` at `:88`). The first three items are the continuous
time replacements for the discrete index theorems listed above; Milestones 6, 7
and 11 use them.

* Optional sampling in continuous time. For a right continuous submartingale `Y`
  and stopping times `σ`, `τ` for `𝓕`, with `τ` bounded,
  `Submartingale.stoppedValue_min_le_condExp`:
  `stoppedValue Y (fun ω ↦ min (σ ω) (τ ω)) ≤ᵐ[P] P[stoppedValue Y τ | hσ.measurableSpace]`,
  and `Martingale.stoppedValue_min_ae_eq_condExp_of_rightContinuous` with `=ᵐ`
  in place of `≤ᵐ`. Mathlib's `Martingale.stoppedValue_min_ae_eq_condExp` is the
  discrete case and is the input: approximate `σ` and `τ` from above by stopping
  times with values in a finite subset of `D`, apply it there, and pass to the
  limit by right continuity. This is where the countable dense `D` is used, and
  it is the only hypothesis on `ι` the passage needs.
* `Submartingale.stoppedValue_min_le_condExp_of_ae_finite`: the same conclusion
  for an almost surely finite `τ` that is not bounded, under
  `Integrable (stoppedValue Y τ)` and
  `Tendsto (fun T ↦ ∫ ω in {ω | T < τ ω}, ‖Y T ω‖ ∂P) atTop (𝓝 0)`; and the
  corollary for a right continuous martingale whose increments are bounded,
  where both hypotheses are automatic.
* Stability of the martingale property under stopping, in continuous time, with
  `[OrderBot ι]`.
  `Martingale.stoppedProcess_of_rightContinuous`: for a right continuous
  martingale `Y` and a stopping time `τ` for `𝓕`, the stopped process
  `stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (Y t)) τ` is a martingale;
  and `isStable_martingale_rightContinuous`, the packaged
  `ProbabilityTheory.IsStable 𝓕 (fun Z ↦ Martingale Z 𝓕 P ∧ IsStronglyProgressive 𝓕 Z ∧ ∀ᵐ ω ∂P, ∀ t, Tendsto (fun r ↦ Z r ω) (𝓝[≥] t) (𝓝 (Z t ω)))`.
  The conjunction is what is stable, and it has **three** members and not two:
  the martingale half holds under the other two together, and each of the two
  survives stopping on its own — progressivity by Mathlib's
  `IsStronglyProgressive.stoppedProcess` and the indicator step
  `isStronglyProgressive_indicator`, right continuity by
  `tendsto_nhdsGE_stoppedProcess`. Then `ProbabilityTheory.IsStable.locally` of
  `Mathlib/Probability/Process/LocalProperty.lean` gives at once that a stopped
  local martingale is a local martingale, and `ProbabilityTheory.Locally.mono`
  forgets the two conjuncts the consumer does not read
  (`locally_martingale_stoppedProcess`); so `IsLocalMPSolution` of Milestone 2 is
  preserved by stopping without any further work, and no localizing sequence is
  constructed by hand.

  **The conjunction is not split again.** `ProbabilityTheory.IsStable.locally_and_iff`
  asks that each side be stable on its own, and the martingale property alone is
  not: it is precisely the conjunct whose proof consumes the other two. The
  direction the consumer needs is the one `Locally.mono` supplies, and it is the
  only one available here. Mathlib has the localization scaffolding but nothing about the
  martingale property in it: `Submartingale.stoppedProcess` of
  `Mathlib/Probability/Martingale/OptionalStopping.lean` is stated for
  `Filtration ℕ` and real valued processes, and `Locally` is never instantiated
  at a martingale. The proof is the first item applied at the bounded stopping
  times `σ ⊓ τ`, and the same argument gives the submartingale form.

  Over the index `ℝ≥0` this is **proved, 2026-09-20**, as
  `martingale_stoppedProcess`: for a progressive right continuous martingale and
  any stopping time the stopped process is a martingale. Three things about it
  are worth saying here because none of them is visible from the statement.

  **It carries no bound on the paths.** Until the fourth run of that day it did,
  one constant per time window, because the expectation identity at a bounded
  stopping time was reached by dominated convergence against that constant. The
  bound is gone and nothing replaces it. The dyadic approximations of the stopped
  value are, each of them, the conditional expectation of the **one** function
  `Y j` for the σ-algebra of the approximating time
  (`uniformIntegrable_stoppedValue_dyadStop`, from Mathlib's
  `MeasureTheory.Integrable.uniformIntegrable_condExp`), so the family is
  uniformly integrable for every martingale and Vitali convergence
  (`MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`) does what dominated
  convergence did. That is the classical hypothesis of the theorem, and here it
  costs nothing because it is not assumed but derived.

  **Integrability of the stopped value is then a theorem and not a by-product**,
  `integrable_stoppedValue_of_rightContinuous`; the constant majorant used to
  give it for free.

  **Right continuity is what remains**, and it is used at one place only, the
  pointwise convergence of the approximations. Progressivity is used for the
  adaptedness of the stopped process and for the measurability of the stopped
  value for the σ-algebra of the stopping time, and nowhere else.

  **And right continuity is asked almost everywhere, 2026-09-20.** Until the
  fifth run of that day it was asked at every sample point, and that is more
  than the proof spends: the convergence of the approximations is consumed by
  Vitali, which quantifies almost everywhere. `tendsto_stoppedValue_dyadStop` is
  therefore stated at **one** sample point and `ae_tendsto_stoppedValue_dyadStop`
  gathers it; the whole chain from there
  (`integrable_stoppedValue_of_rightContinuous`,
  `integral_stoppedValue_eq_of_rightContinuous`, `stoppedValue_ae_eq_condExp`,
  `isOptionalSamplingFor_of_martingale`, `martingale_stoppedProcess`) carries
  `∀ᵐ ω ∂P`. The difference is not cosmetic: right continuity of the test
  process of the path dependent construction holds exactly on the non explosion
  set, because `tendsto_nhdsGE_mpFamilyF_hawkes` produces it out of the local
  integrability of the rate along the path and that integrability **is** the non
  explosion at the sample point
  (`not_intervalIntegrable_hawkesSelfRate_of_not_summable`). The everywhere form
  was therefore a hypothesis the Hawkes data cannot supply, and the almost
  everywhere form is one the almost sure non explosion discharges.

  What the `ℝ≥0` proof does use and a general `ι` does not have is the dyadic
  approximation of the stopping time from above. The replacement over an
  arbitrary `ι` is an increasing sequence of finite subsets of `D` exhausting `D`
  and the first element of the `n`-th of them above the time; this is a stopping
  time of finite range, it decreases to the original when `D` is order dense, and
  Mathlib's countable range optional sampling
  (`Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range`) is
  stated over an arbitrary `[LinearOrder ι] [OrderTopology ι]
  [FirstCountableTopology ι]`, so it applies there unchanged. Order density of
  `D` is an assumption the `ℝ≥0` form does not need to state and the general form
  does.

  **The packaging is proved over `ℝ≥0` as well, 2026-09-20**, as
  `isStable_martingale_rightContinuous`, with `stableMartingaleProp_zero` for the
  inhabitedness of the property and `locally_martingale_stoppedProcess` for the
  consequence. Two things about it were not visible from the item above.

  **The indicator costs a lemma on the progressive side.** The process `IsStable`
  quantifies over carries `{ω | ⊥ < τ ω}.indicator` in front of the stopping, so
  besides `martingale_indicator_bot` on the martingale side there has to be
  `isStronglyProgressive_indicator` on the other. It does not touch the product
  σ-algebra of the definition of `IsStronglyProgressive`: the indicator is the
  product with the time independent process `fun _ ω ↦ S.indicator 1 ω`, which is
  progressive by `StronglyAdapted.isStronglyProgressive_of_continuous` because it
  is adapted and constant in time, and `IsStronglyProgressive.mul` finishes. The
  set lies in `𝓕 ⊥` because it is the complement of `{ω | τ ω ≤ ⊥}`.

  **Right continuity survives stopping, and the two cases are not symmetric.**
  `tendsto_nhdsGE_stoppedProcess` holds at every sample point and asks nothing of
  the stopping time. Where the time has occurred the stopped path is constant on
  the right and the limit is trivial; where it has not, the stopped path agrees
  with the path on a right neighbourhood, and the neighbourhood exists because
  `ENNReal` is densely ordered — some `c` lies strictly between the time and the
  stopping time, it is finite because it lies below the latter, and `Set.Ico s c`
  is the neighbourhood (`Ico_mem_nhdsGE`,
  `Mathlib/Topology/Order/OrderClosed.lean:357`, the `to_dual` of
  `Ioc_mem_nhdsLE`). This is the only place the order structure of the index
  enters.
* Doob's inequalities in continuous time. The supremum
  `fun ω ↦ ⨆ t ∈ Set.Iic T, ‖Y t ω‖` is measurable because right continuity
  makes it the supremum over `Set.Iic T ∩ D`; that reduction is a lemma of its
  own and it is **proved, 2026-09-20**, as
  `biSup_enorm_Iic_eq_of_isRightContinuous`, together with
  `measurable_biSup_enorm_of_countable`. Three things are fixed by it and none
  of them was visible from the phrase above.

  **The supremum is taken in `ℝ≥0∞` and not in `ℝ`.** Over `ℝ` the supremum of
  a family that is not bounded above is `0` (`Real.iSup_of_not_bddAbove`), so
  `⨆ t ∈ S, |Y t ω|` vanishes on exactly the set where the path escapes, and a
  condition `∫ ω, (⨆ t ∈ S, |Y t ω|) ∂P < ε` is satisfied by the families it is
  written to exclude. `biSup_eq_zero_of_not_bddAbove` states the junk value and
  `biSup_natCast_eq_zero` witnesses that its hypothesis is inhabited. This is
  the fifth instance of the pattern the standing rule on non-explosion names,
  and it decides the shape of the approximability condition of Milestone 11.

  **The right endpoint of the window is not reached by a dense set.** Nothing
  inside `Set.Iic T` approaches `T` from the right, so the reduction is to
  `insert T (Set.Iic T ∩ D)` and not to `Set.Iic T ∩ D`. It is the asymmetry
  `SkorokhodSpace.forall_mem_Ico_of_forall_mem_dense` is stated to avoid, paid
  for here by the `insert` rather than by enlarging the window.

  **Countability is what makes the quantity measurable at all.** In the binder
  form `⨆ t ∈ W` the supremum runs over the whole index, so Mathlib's
  `Measurable.iSup` — which asks `[Countable ι]` — does not apply over an
  uncountable window; `iSup_subtype'` and the countable `D` are the step, and
  the reduction above is what supplies `D`.

  **Doob's maximal inequality in continuous time**, `2026-09-20`. It is the
  composition of the reduction above with the countable time bound, and no
  analysis is left in it: `Submartingale.mul_measReal_lt_biSup_enorm_le` reads
  the window supremum along `insert T (Set.Iic T ∩ D)` and hands that countable
  set to `Submartingale.mul_measReal_exists_ge_abs_le_countable`.

  **The strict level is the primitive and the non-strict level is the
  corollary**, which is the reverse of the usual order and is forced by the
  supremum: from `ENNReal.ofReal ε < ⨆ s ∈ S, ‖Y s ω‖ₑ` a time at which the
  level is exceeded can be produced, and from `ENNReal.ofReal ε ≤ ⨆ s ∈ S,
  ‖Y s ω‖ₑ` it cannot, the supremum not being attained.
  `Submartingale.mul_measReal_le_biSup_enorm_le` recovers the classical form by
  reading the strict one at every `x < ε` and letting `x` increase along
  `𝓝[<] ε`. Neither form uses measurability of the level set: both sides read
  `Measure.real`, and the passage between the level sets is `measureReal_mono`.

  **Doob's `Lᵖ` inequality**, `2026-09-20`, in three statements, of which the
  middle one carries no probability. `lintegral_rpow_le_of_weak_type` says that
  a non-negative measurable `M` whose level sets obey
  `ENNReal.ofReal t * μ {a | t ≤ M a} ≤ ∫⁻ a in {a | t ≤ M a}, ENNReal.ofReal (g a)`
  at every `t > 0` obeys `∫⁻ M ^ p ≤ (p/(p-1))^p * ∫⁻ g ^ p` for `1 < p`,
  provided `∫⁻ M ^ p ≠ ⊤`. It is the whole of Doob's `Lᵖ` inequality except for
  the input, and it is stated over a bare measure space so that the discrete and
  the continuous time forms share one proof; it is split into
  `lintegral_rpow_le_mul_lintegral_mul_rpow`, which produces the intermediate
  bound by `M ^ (p-1)`, and `lintegral_rpow_le_of_le_mul_lintegral_mul_rpow`,
  which is Hölder against `q = p/(p-1)` and the cancellation of `A ^ (1/q)`.

  **The level sets are read non-strictly here and strictly in the maximal
  inequality above**, and that is deliberate: Mathlib's `maximal_ineq` is stated
  at `{ε ≤ f*}` and the layer cake formula exists in both forms
  (`lintegral_rpow_eq_lintegral_meas_le_mul`, `…_lt_mul`), so the non-strict
  reading consumes the martingale input as it stands.

  **Fubini does not appear, and that is what makes the proof short.** The usual
  argument exchanges `∫ dt` with `∫ dμ` after inserting the weak type bound.
  Here the exchange is Mathlib's own layer cake formula read a second time under
  the weighted measure `ν = μ.withDensity (ENNReal.ofReal ∘ g)`: `ν {t ≤ M}`
  *is* `∫⁻_{t ≤ M} g` by `withDensity_apply`, so
  `lintegral_comp_eq_lintegral_meas_le_mul ν` with weight `t ^ (p-2)` performs
  the exchange in one step and `lintegral_withDensity_eq_lintegral_mul` reads the
  result back under `μ`. Neither `lintegral_lintegral_swap` nor a Lebesgue
  integral of `t ^ (p-2)` over an interval is used; the inner integral is the
  Bochner `integral_rpow`.

  **The finiteness hypothesis is where the cancellation happens** and is carried,
  not derived: the proof ends at `A ≤ C · B^(1/p) · A^(1/q)` and divides by
  `A^(1/q)`.

  `Submartingale.lintegral_rpow_range_sup'_le` is the instance over `ℕ`: for a
  non-negative submartingale, `∫⁻ (f*)^p ≤ (p/(p-1))^p * ∫⁻ (f n)^p` with
  `f* = (Finset.range (n+1)).sup' _ fun k ↦ f k ω`, the shape `maximal_ineq`
  produces, and `Submartingale.eLpNorm_range_sup'_le` is the same statement as
  `‖f*‖ₚ ≤ p/(p-1) · ‖f n‖ₚ`. The passage between the two shapes is
  `eLpNorm_le_of_lintegral_rpow_le`, which is where the two conventions meet:
  `eLpNorm` reads `‖·‖ₑ` and the core reads `ENNReal.ofReal`, and for a
  non-negative function these agree by `Real.enorm_eq_ofReal`.

  **The continuous time instance is stated in `ℝ≥0∞` and reached by monotone
  convergence, not by a continuous time weak type bound** (`2026-09-20`).
  `Submartingale.lintegral_biSup_enorm_rpow_le`,
  `∫⁻ ω, (⨆ t ∈ Set.Iic T, ‖Y t ω‖ₑ)^r ≤ (r/(r-1))^r · ∫⁻ ω, ‖Y T ω‖ₑ^r` for a
  non-negative right continuous submartingale, `1 < r`, and each `Y t` in `Lʳ`.

  Three things fix that shape. **Every real valued encoding of the window
  supremum carries a junk value** — `(⨆ t, ‖Y t ω‖ₑ).toReal` is `0` where the
  path escapes, and so is `⨆ t, Y t ω` read in `ℝ` by
  `biSup_eq_zero_of_not_bddAbove` — so the conclusion is taken in `ℝ≥0∞`, where
  the escaping paths contribute `⊤`. **The finiteness of the supremum is then
  not a hypothesis but a consequence**, monotone convergence giving the bound
  also where both sides are `⊤`. And **no localised weak type bound in
  continuous time is needed**: the level set `{ENNReal.ofReal t ≤ ⨆ s ∈ S, ‖Y s‖ₑ}`
  is the decreasing intersection of the sets `{∃ s ∈ S, t' ≤ Y s}` over
  `t' ↑ t`, so that route runs through `tendsto_measure_iInter_atTop`
  (`MeasureTheory/Measure/Continuity.lean:220`) and
  `tendsto_setIntegral_of_antitone` (`MeasureTheory/Integral/Bochner/Set.lean:299`),
  and the route through the finite pieces avoids both.

  The step the proof turns on: enumerate `S = insert T (Set.Iic T ∩ D)` so that
  the **first** time is `T`, which is possible because `T ∈ S`; then `T` lies in
  every finite piece, every time of `S` lies below `T`, and the largest time of
  every piece is `T`. The instance over `ℕ` therefore bounds each piece by
  `Y T` directly, with no need for the monotonicity of `r ↦ ‖Y r‖ₚ` and hence
  no conditional Jensen inequality. Its finiteness hypothesis over a finite
  piece follows from `Lʳ` of the members, the maximum being one of them. The
  passage to the limit is `lintegral_iSup`
  (`MeasureTheory/Integral/Lebesgue/Add.lean:36`) together with
  `ENNReal.orderIsoRpow` (`Analysis/SpecialFunctions/Pow/NNReal.lean:788`),
  which is an order isomorphism and therefore commutes with suprema, and the
  supremum over the pieces is the window supremum by
  `biSup_enorm_Iic_eq_of_isRightContinuous`.

  **What the `Lᵖ` inequality consumes is a localised bound, and that is a
  distinction the maximal inequalities above do not make.** The right hand side
  of `lintegral_rpow_le_of_weak_type` is `∫⁻ a in {t ≤ M a}, g a` and not a
  constant, and a constant would be useless there: inserted into the layer cake
  it gives `∫⁻ M^p ≤ C · ∫⁻ t^(p-2) dt`, which diverges. Mathlib's
  `maximal_ineq` is localised in exactly this sense, and since `2026-09-20` so
  are `Submartingale.mul_measReal_exists_ge_le_setIntegral` over `ℕ` and
  `Submartingale.mul_measReal_exists_ge_le_setIntegral_countable` over an
  arbitrary linear order,
  `ε * P {ω | ∃ s ∈ S, ε ≤ Y s ω} ≤ ∫ ω in {ω | ∃ s ∈ S, ε ≤ Y s ω}, (Y T ω)⁺`
  for countable `S` bounded above by `T`. Two steps separate the localised bound
  from the global one and only two: over a finite piece the level set lies in
  the filtration at the largest time of that piece, so the submartingale
  property carries the integral from there to `T`; and the integrals over the
  increasing pieces are dominated by the integral over their union, the
  integrand being non-negative. `Submartingale.mul_measReal_exists_ge_le_integral_posPart`
  is now the one line weakening of the first.

  **The localised form has no lower bound on `S` and is one sided**, where the
  global one has a lower bound and is two sided. Both differences have the same
  cause: the minimal inequality, which is what spends the lower bound, would
  localise to the level set of `-Y`, a *different* set, and the two bounds could
  not be added.

  The form the manuscript uses is the corollary for a right continuous
  martingale `X`, applied to the non-negative submartingale `‖X ·‖`:
  `Martingale.lintegral_biSup_enorm_rpow_le` and `Martingale.measure_iSup_norm_le`
  (`2026-09-20`), and each is that application and nothing more.

  **The maximal corollary carries the constant `1`, and that decides which
  window bound it is an application of.** `Martingale.measure_iSup_norm_le` is
  `ε * P {ω | ENNReal.ofReal ε ≤ ⨆ t ∈ Set.Iic T, ‖X t ω‖ₑ} ≤ 𝔼‖X T‖`. Read
  through the two sided `Submartingale.mul_measReal_le_biSup_enorm_le` it would
  be `2 𝔼‖X T‖ - 𝔼‖X ⊥‖` instead, which is at least `𝔼‖X T‖` because `‖X ·‖` is
  a submartingale, so the classical constant would be lost. The one sided
  window bounds `Submartingale.mul_measReal_lt_biSup_enorm_le_of_nonneg` and
  `Submartingale.mul_measReal_le_biSup_enorm_le_of_nonneg` (`2026-09-20`) are
  what it is an application of: for a non-negative submartingale no absolute
  value is needed, so the localised one sided estimate applies directly and the
  bound is `𝔼[Y T]`. They are not the two sided theorems specialised — the
  discrete inputs differ — and, like the localised estimate they rest on, they
  have no lower bound on the window and no term at `⊥`.

  **No `eLpNorm` form of the window inequality is stated, and that is a
  decision and not an omission.** `eLpNorm` is taken of a real valued function,
  and the real valued encodings of the window supremum all read `0` where the
  path escapes, so such a form would have to carry the almost sure finiteness
  of the supremum as a hypothesis. That finiteness is a theorem here,
  `Martingale.ae_biSup_enorm_lt_top` (`2026-09-20`): the escape set lies in
  every level set `{ENNReal.ofReal n ≤ ⨆ t ∈ Set.Iic T, ‖X t ω‖ₑ}`, whose
  measure the maximal inequality bounds by `𝔼‖X T‖ / n`. So the `ℝ≥0∞` form
  loses nothing — a consumer may take `.toReal` and know it is not reading a
  junk value — while an `eLpNorm` form would say no more than the form it is
  derived from. Milestone 11, the consumer, reads in `ℝ≥0∞` anyway.

  **That `‖X ·‖` is a submartingale is itself a gap in Mathlib**, closed here as
  `Martingale.submartingale_norm` (`2026-09-20`): the strings
  `submartingale_abs`, `Martingale.abs`, `Martingale.norm` and `convex` do not
  occur in `Mathlib/Probability/Martingale/` (checked 2026-09-20 against
  `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`). Its input does exist there and
  is what makes the proof three lines: `MeasureTheory.norm_condExp_le`
  (`MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:246`), the
  conditional Jensen inequality for the norm, stated with no integrability
  hypothesis. The statement is for a Banach space valued martingale rather than
  a real one because that costs nothing — `norm_condExp_le` is already there.

  Two norms meet in the corollary and the meeting is the only computation in
  it: the submartingale theorem reads `‖Y t ω‖ₑ` of the *real* process
  `Y t ω = ‖X t ω‖`, and that is `‖X t ω‖ₑ` because the norm is non-negative.
  Right continuity is asked of the paths of `X` and carried to `‖X ·‖` by
  `IsRightContinuous.continuous_comp`, which is weaker than asking it of the
  norm and is what a càdlàg martingale supplies.
* Oscillation of a real function along a one sided filter, which is the
  deterministic content of regularization and carries no probability at all.
  `HasUpcrossings a b g S n` says that `g` runs through an increasing tuple
  `u 0 < ⋯ < u (2 n - 1)` inside `S` alternating between below `a` and above
  `b`. It is stated with the tuple and not with a count, because the count
  exists only after a monotone enumeration of `S` has been chosen while the
  tuple exists as soon as the times do, and because it is monotone in `S` by
  inspection.

  `exists_chain_alternating` builds the tuple greedily: along a filter `L` whose
  points eventually lie in `S`, and on which every point of `S` is eventually
  overtaken in the sense of a relation `R`, two frequently true properties
  interleave into an alternating `R`-chain. The relation is abstract because the
  two one sided filters need opposite ones, and neither order nor topology
  enters. `hasUpcrossings_of_frequently_nhdsWithin_Iio` and
  `hasUpcrossings_of_frequently_nhdsWithin_Ioi` instantiate it at
  `𝓝[S ∩ Set.Iio t] t` and `𝓝[S ∩ Set.Ioi t] t`; the second builds the chain
  descending and reads it backwards, which exchanges the two parities.

  `exists_tendsto_nhdsWithin_Iio_of_hasUpcrossings_bound` and
  `exists_tendsto_nhdsWithin_Ioi_of_hasUpcrossings_bound` are the conclusion: a
  function bounded on `S` whose upcrossings of every rational interval inside
  `S` are bounded in number has one sided limits along `S` at **every** point.
  Both hypotheses are read over `S` and not over `S ∩ Set.Iio t`, so one
  hypothesis serves every `t`; that is what makes the almost sure version a
  statement about one null set instead of one for each `t`. Mathlib supplies the
  passage from "no oscillation across a dense set of levels" to convergence,
  `tendsto_of_no_upcrossings` (`Topology/Order/LiminfLimsup.lean:317`), over an
  arbitrary filter, and `Rat.denseRange_cast` supplies the levels.
* Submartingale regularization, which Mathlib does not have, although the
  ingredient does. For a submartingale `Y` indexed by `ι` and a countable
  `S ⊆ ι` bounded above by `T`, almost surely the number of upcrossings of every
  rational interval inside `S` is bounded
  (`Submartingale.ae_exists_not_hasUpcrossings`); if `S` is in addition bounded
  below by `R`, the path is almost surely bounded on `S`
  (`Submartingale.ae_bddOn`). With the two deterministic theorems above this is
  `Submartingale.ae_exists_tendsto_nhdsWithin`, the real valued input of
  `exists_cadlag_modification_of_isRegularizingClass`.

  The input is the Doob upcrossing estimate, in Mathlib as
  `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
  and `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part`, together
  with `upcrossings_lt_top_iff`; all of these are indexed by `ℕ`, and three steps
  carry them to an arbitrary `ι`, each named separately.

  `le_upcrossingsBefore_of_alternating'` is the first: an alternating pattern of
  length `2 n` read off at strictly increasing indices `j 0 < ⋯ < j (2 n - 1)`,
  all below `M`, forces `upcrossingsBefore a b f M` to be at least `n`. This is
  the induction inside `ProbabilityTheory.not_frequently_of_upcrossings_lt_top`
  (`Probability/Martingale/Convergence.lean:112`) read as a positive statement,
  and the free indices are what it needs: the tuple of a path lies at indices
  that depend on the sample point, while the reindexing it is measured against
  must not. `le_upcrossingsBefore_of_alternating` is its case `j = id`.

  The second is `Filtration.comp`, the reindexing of a filtration along a
  monotone map, with `Submartingale.comp_monotone`: a submartingale read along a
  monotone `e : ℕ → ι` is a submartingale for `Filtration.comp 𝓕 e`. Mathlib has
  neither; `Probability/Process/Filtration.lean` carries no `comp`.

  The third is `Finset.monoEnum`, the monotone enumeration of a nonempty finite
  set of times, **constant from its last element on**, with
  `Finset.monotone_monoEnum`, `Finset.monoEnum_mem` and
  `Finset.exists_lt_card_monoEnum_eq`. That it saturates rather than stopping at
  `Fin (card)` is not cosmetic: it makes the enumeration a monotone map on all of
  `ℕ`, which is what `Filtration.comp` asks for, and it bounds the indices of a
  tuple inside the set by the cardinality, which is the time at which Doob's
  estimate is read. `le_upcrossingsBefore_monoEnum` joins the three: an
  alternating tuple inside a finite `s` satisfies
  `n ≤ upcrossingsBefore a b (Y ∘ Finset.monoEnum hs) s.card`.

  `Submartingale.ae_exists_not_hasUpcrossings_of_lt` is then the estimate for one
  pair of levels and `Submartingale.ae_exists_not_hasUpcrossings` for all
  rational pairs at once. The passage from the finite sets to `S` uses **no**
  monotonicity of the counts in the exhausting index — different finite sets
  carry different enumerations, and comparing their counts would be work.
  Instead the bad event is written as the increasing union
  `⋃ N, ⋂ M ≥ N, {n ≤ V M}`, whose measure is a supremum of measures each bounded
  by Markov's inequality; continuity from below (`Monotone.measure_iUnion`,
  `MeasureTheory/Measure/Continuity.lean:71`) replaces Fatou's lemma and needs no
  measurability. The uniform bound on the count is Doob's estimate at the last
  time of the finite set, which `Submartingale.setIntegral_le` applied to the
  submartingale `(Y - a)⁺` bounds by the estimate at `T`.

  `Submartingale.ae_bddOn` is the other half, and it is a **maximal**
  inequality and not an upcrossing one. Both sides are taken in the same shape,
  real valued, over the event `{ω | ∃ k ≤ n, ε ≤ f k ω}` rather than over a
  `Finset.sup'`, and with **no** sign assumption on `ε` or on the process:
  `Submartingale.mul_measReal_exists_ge_le_integral_posPart`,
  `ε · P.real {∃ k ≤ n, ε ≤ Y k} ≤ 𝔼[(Y n)⁺]`, and
  `Submartingale.mul_measReal_exists_le_neg_le_integral_posPart_sub`,
  `ε · P.real {∃ k ≤ n, Y k ≤ -ε} ≤ 𝔼[(Y n)⁺] - 𝔼[Y 0]`. Each is
  `Submartingale.expected_stoppedValue_mono`
  (`Probability/Martingale/OptionalStopping.lean:43`) read at the hitting time of
  a half line, with the stopped value split over the event that the level is
  reached; the extra `𝔼[Y 0]` in the second is what the asymmetry costs, a
  submartingale being pushed up.

  Mathlib has the upper side, as `MeasureTheory.maximal_ineq` (`ibid.:144` on
  master, `:155` in v4.33.1), but in `ℝ≥0∞` and for a **non-negative**
  submartingale over `Finset.sup'`; bridging that to the two sided bound through
  `Y⁺` costs more than the six line proof does. The lower side Mathlib does not
  have in any form: the string `inf'` does not occur in
  `Mathlib/Probability/Martingale/`.

  The collection over the finite sets is here a plain increasing union, and not
  the `⋃ N, ⋂ M ≥ N` of the upcrossing bound: the event that some time of `F N`
  carries `|Y| ≥ k` is monotone in `N` by inspection, being a condition over a
  set rather than a count read along an enumeration.

  **The lower bound `hRS : ∀ s ∈ S, R ≤ s` belongs to the statement**, and
  `Submartingale.ae_bddOn` is false without it. Witness: `ι = ℤ` with the trivial
  filtration, `Y k ω = k`, which is a submartingale, and `S = Set.Iic 0`,
  countable and bounded above by `0`; then `s ↦ |Y s ω|` is unbounded on `S` at
  every sample point. What fails is the bound `𝔼[Y R] ≤ 𝔼[Y (min F)]`, the only
  place where the first time of a finite piece is controlled, and it has to be
  uniform in the piece while `min F` runs downwards. Under `[OrderBot ι]`, the
  index of this milestone's last block, `R = ⊥` serves.
* The modification as a **construction**, not an existential: `cadlagModif Y`,
  defined from the right limits along a countable dense set, together with
  `isCadlag_cadlagModif`, `measurable_cadlagModif`, `adapted_cadlagModif` for a
  right continuous complete filtration, and `cadlagModif_ae_eq` giving the
  modification property. A named construction with its properties is what later
  milestones need; an existential statement loses the object.
* `Submartingale.cadlagModif_ae_eq_iff_continuousWithinAt_integral`: the
  construction is a modification of a submartingale exactly at the points where
  `t ↦ 𝔼[Y t]` is right continuous, hence everywhere when that map is right
  continuous.
* `Martingale.cadlagModif_ae_eq`: for a martingale the condition is automatic.
  The three points above state what is wanted in full and are to be reviewed on
  their own terms. As prior art, cited and not presupposed: the repository
  `RemyDegenne/brownian-motion` (Apache-2.0, copyright Rémy Degenne) carries a
  development of this for real valued quasimartingales, on its branch `master`
  (`314f04a`, 2026-08-01) and not on `paper` (`55dde5d`, 2026-07-31) nor on
  `origin/master` (`eaa4391`, 2026-06-09), which have no
  `BrownianMotion/StochasticIntegral/Quasimartingale/` at all. On `master` that
  directory holds three files, each with an Apache-2.0 header:
  `Quasimartingale/Basic.lean`, 54 lines and no `sorry`, defining
  `IsRealQuasimartingale` as adaptedness together with integrability and
  bounded variation over `ElementaryPredictableSet`;
  `Quasimartingale/MaximalInequality.lean`, 895 lines and no `sorry`, which is
  Doob's maximal inequality in continuous time, the third item of this milestone
  above; and `Quasimartingale/CadlagModification.lean`, 1162 lines with four
  `sorry` at lines 41, 1002, 1138 and 1152. That last file carries the whole
  chain — `regularitySet`, `ae_right_limit`, `ae_left_limit`,
  `measurable_rightLimWithin`, `adapted_rightLimWithin`, `rightContModif`, and
  then `cadlagModif` with `isCadlag_cadlagModif`, `measurable_cadlagModif`,
  `adapted_cadlagModif` and `stronglyAdapted_cadlagModif` — under the names this
  milestone uses. The statement that the modification is one exactly where
  `t ↦ 𝔼[X t]` is right continuous is there as
  `cadlagModif_ae_eq_of_continuousWithinAt_integral` (line 1133) and is one of
  the four `sorry` (line 1138); `Martingale.isRealQuasimartingale` (line 1148)
  is a second (line 1152), so the four line corollary
  `Martingale.cadlagModif_ae_eq` rests on both. The monotone passage from the
  upcrossing estimate on finite subsets of `D` to all of `D` — the analytic core
  of this milestone — is carried out there and can be read.
  What is **not** there is everything `E` valued: that development is
  `X : ι → Ω → ℝ` throughout, while
  `exists_cadlag_modification_of_isRegularizingClass` below regularizes the real
  process `f ∘ X` for each `f` in a countable separating subclass of `Φ` and
  assembles an `E` valued path from the results, with `CompactContainment`
  keeping the limits inside `E`. That assembly appears nowhere in that
  repository. An implementer may consult it and, the licence permitting, draw on
  it with its copyright header preserved; nothing here should be accepted merely
  because it matches that file, and no statement of this roadmap refers to it.
* `IsRegularizingClass Φ X 𝓧`: a set `Φ` of bounded continuous functions on `E`
  such that for every `f ∈ Φ` there are `Y ∈ 𝓧` and a `StronglyAdapted`
  `𝕂`-valued `C`
  with `f (X t) = Y t + C t` almost surely for every `t`, with `C` almost surely
  having one sided limits along `D`, and with `C` right continuous in `L¹`.
  **Right continuity in `L¹` is stated in `ℝ≥0∞`**, as
  `∫⁻ ω, ‖C s ω − C t ω‖ₑ ∂P → 0` along `𝓝[>] t`, and not through the Bochner
  integral. The Bochner form has a junk value: `∫ ω, ‖C s ω − C t ω‖ ∂P` is `0`
  whenever the integrand fails to be integrable, so it is satisfied by
  compensators that are nowhere near right continuous. The witness is
  `C s = g` for `s ≠ t` with `g` measurable and not integrable, `C t = 0`, and
  `Y := f ∘ X − C`: the paths are constant in `s` off `t`, so the one sided
  limits exist, every field holds, and the right limit of `C` at `t` is `g` and
  not `C t`. The lower integral has no junk value and the witness dies at once.
  It is also what Fatou is stated in, so the formulation and the proof of
  `IsCompensatorFor.ae_eq_of_tendsto_nhdsWithin_Ioi` want the same object.
  `StronglyAdapted` (`Mathlib/Probability/Process/Adapted.lean:105`) and not
  `Adapted`: since 2026-01-13 the latter (`ibid.:60`) is measurability with
  respect to `𝓕 i` and asks for `[MeasurableSpace 𝕂]`, which `RCLike` does not
  supply, while `StronglyAdapted` is the notion `Martingale` itself is built
  from (`Mathlib/Probability/Martingale/Basic.lean:53`).
  The pair `(Y, C)` belonging to `f` is one object, `IsCompensatorFor f Y C`,
  and not two conditions on `Φ`: the theorem below on quasi-left-continuity asks
  more of `C`, and it must be the same `C` that the decomposition uses, so the
  two existential quantifiers have to bind together.
  Note that the first condition is not a hypothesis — `C := f ∘ X - Y` satisfies
  it — so the content is the choice of `Y` in `𝓧` together with the last two
  conditions. The standard verification of the last two is that `C` has finite
  variation.
* `CompactContainment X D` and `CompactContainment.family`, the two variants:
  for every `ε` and `T` a compact `K` with
  `P {∀ t ∈ Iic T ∩ D, X t ∈ K} > 1 - ε`, and the version over `[0,T]` for a
  family of processes. A lemma relating them for right continuous processes.
* `CompactContainment.ae_exists_isCompact`: run along `ε = (n+1)⁻¹`, compact
  containment says that almost every path meets **some** compact set on
  `Iic T ∩ D`, the set depending on the path. It carries `D.Countable`, the
  measurability of each `X t`, `[T2Space E]` and `[OpensMeasurableSpace E]`, and
  none of the four is a convenience: `CompactContainment` bounds the outer
  measure of a set that is not asserted to be measurable, and a lower bound on
  the outer measure of a union bounds nothing on its complement. What makes the
  set measurable is that `{ω | ∀ t ∈ Iic T ∩ D, X t ω ∈ K}` is a **countable**
  intersection of preimages of a compact, hence closed, hence measurable set.
  Proved on 2026-09-15.
* `exists_tendsto_of_forall_tendsto_comp`, the step that makes an `E` valued
  limit out of real ones and the one part of the càdlàg theorem that no amount
  of real valued regularization supplies. Along a filter on which the path
  eventually sits inside a compact `K`, convergence of `f ∘ g` for every `f` of a
  family that separates the points of `K` by continuous functions forces
  convergence of `g`. A compact set catches a cluster point, a continuous `f`
  carries a cluster point of `g` to one of `f ∘ g`, and a convergent filter in a
  Hausdorff space has exactly one; so any two cluster points of `g` in `K` agree
  under every `f`, hence agree, and
  `IsCompact.tendsto_nhds_of_unique_mapClusterPt`
  (`Mathlib/Topology/Compactness/Compact.lean:181`) turns that uniqueness into
  convergence. No countability of the family, no metric on `E` and no separation
  axiom on `E`: the Hausdorff property the argument uses is the one of `𝕂`, and
  the separation hypothesis is read only between two points of `K`.
  Proved on 2026-09-15.
* `ae_exists_tendsto_of_forall_ae_exists_tendsto`, the assembly, and the
  statement the càdlàg theorem consumes twice — once for the right limits and
  once for the left. Along a filter that eventually stays inside `Iic T ∩ D`,
  almost sure convergence of `f ∘ X` for every `f` of a **countable** class
  separating the points of `E` gives almost sure convergence of `X`. Countability
  enters here and nowhere else: it is what lets the exceptional sets of the
  individual `f` be collected into one, and it is one of the two reasons
  `exists_cadlag_modification_of_isRegularizingClass` asks for a countable
  separating subclass — the other being the squares, which
  `isQuasiLeftContinuous_of_isRegularizingClass` asks for as well. Proved on
  2026-09-15.
* `ae_exists_tendsto_comp_of_isRegularizingClass`, the real valued half of
  Doob's regularization read through a regularizing class: for one `f` of the
  class, `f ∘ X` has almost surely, at **every** point of the index at once,
  both one sided limits along `D`. This is where `IsMPSolution 𝓧 𝓕 P` is spent.
  It turns the member `Y` of `𝓧` into a martingale,
  `Martingale.submartingale_re` and `Martingale.submartingale_im` into two real
  submartingales, `Submartingale.ae_exists_tendsto_nhdsWithin` gives them their
  one sided limits along `D`, and `IsCompensatorFor.exists_limits` carries
  those of the compensator; `f ∘ X = Y + C` holds at every point of the
  countable `D` at once and therefore inherits both.

  The index carries `[(atTop : Filter ι).IsCountablyGenerated]`, and that
  hypothesis cannot be dropped: the upcrossing bound reads its time set between
  two bounds, while the conclusion is quantified over **every** `t : ι`, and one
  null set for each `t` is not a null set. A countable cofinal `u : ℕ → ι` makes
  it a countable union. The instance holds for `ℝ≥0` and for `ℝ` through
  `atTop_isCountablyGenerated_of_archimedean`
  (`Order/Filter/AtTopBot/Archimedean.lean:147`). A greatest element of `ι`
  costs nothing: where no `u n` exceeds `t`, cofinality makes `t` greatest,
  `Set.Ioi t` is empty, the filter is `⊥` and the right limit is vacuous — so no
  `NoMaxOrder` appears.

  Three of its inputs are the process half of a Mathlib statement that exists
  only in the conditional expectation half:
  `Martingale.comp_continuousLinearMap`, a martingale composed with a
  continuous `ℝ` linear map is a martingale, and `Martingale.submartingale_re`
  and `Martingale.submartingale_im` reading it at `RCLike.reCLM` and
  `RCLike.imCLM`. Mathlib has `ContinuousLinearMap.comp_condExp_comm`
  (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:359` in v4.33.1)
  and no process version. Proved on 2026-09-17.
* `IsCompensatorFor.ae_eq_of_tendsto_nhdsWithin_Ioi`, the right limit of the
  compensator along `D` is the compensator: if `C s ω` converges to `W ω` along
  `𝓝[D ∩ Set.Ioi t] t` for almost every `ω`, then `W = C t` almost surely. In
  the notation of the càdlàg theorem this is `C_{t+} = C t`, and it is the only
  place where `l1_rightContinuous` of `IsCompensatorFor` is used.

  The proof is Fatou and nothing else. Along a sequence `u` running into
  `𝓝[D ∩ Set.Ioi t] t` the paths `C (u n) ω` go to `W ω` almost surely, so
  `‖C (u n) ω − C t ω‖ₑ` goes to `‖W ω − C t ω‖ₑ` and in particular the `liminf`
  is that; the lower integrals go to `0` by right continuity; `lintegral_liminf_le`
  (`MeasureTheory/Integral/Lebesgue/Add.lean:231`) puts
  `∫⁻ ‖W − C t‖ₑ ≤ 0`, and a vanishing lower integral has a vanishing integrand
  almost everywhere. **No integrability of `C` enters, and `W` is not assumed
  measurable** — that is the gain of the `ℝ≥0∞` formulation of the field.

  `[(𝓝[D ∩ Set.Ioi t] t).NeBot]` is not a technicality: at a point isolated from
  the right the hypothesis is vacuous and `W` is arbitrary. It holds where the
  càdlàg theorem uses it, `D` being dense and `t` not greatest.
  `[FirstCountableTopology ι]` is what makes the filter countably generated and
  so produces `u`. Proved on 2026-09-17.
* `MeasureTheory.UnifIntegrable.of_norm_le_ae`, uniform integrability passes to a
  family dominated in norm: if `g i` is a.e. strongly measurable and
  `‖g i x‖ ≤ ‖f i x‖` almost everywhere for every `i`, and `f` is uniformly
  integrable, then so is `g`. The two families may take their values in
  different normed groups, which is what the use below needs.

  Mathlib has a domination lemma, `UnifIntegrable.ae_mono`
  (`MeasureTheory/Function/UniformIntegrable.lean:142`) — so this is not a gap to
  be reported upstream, and the entry says so rather than claiming an absence
  that has since been filled. **One** difference remains and is the reason the
  lemma stands here rather than being waited for: `ae_mono` quantifies both
  families over the **same** normed group (`{f g : ι → α → β}` in its section),
  while the use below has a real dominating family and a `𝕂` valued dominated
  one.

  **The measurability of the dominated family is not a convenience.** Until
  2026-09-18 this entry said “nothing is assumed of `g` — neither measurability
  nor integrability”, and against `v4.33.1` that was true. It is **false** on
  `master`, where `eLpNorm` is `∞` for a function that is not a.e. strongly
  measurable: without the hypothesis the conclusion does not hold, and so the
  statement — not merely its proof — had to change. It is the one place in this
  roadmap where the two Mathlib versions differ in what is true.

  The proof is `eLpNorm_mono_ae` applied to the indicators, which are dominated
  on the set by hypothesis and off it because both vanish. Proved on 2026-09-17.
* `Martingale.condExp_ae_eq_of_tendsto_nhdsWithin_Ioi`, the right limit of a
  martingale along `D` has the martingale value for its conditional expectation:
  if `Y` is a martingale, `t < T`, `𝓝[D ∩ Set.Ioi t] t` is not `⊥`, and `Y s ω`
  converges to `V ω` along that filter for almost every `ω`, then
  `P[V | 𝓕 t] =ᵐ[P] Y t`. In the notation of the càdlàg theorem this is
  `P[Y_{t+} | 𝓕 t] = Y t`, and together with
  `IsCompensatorFor.ae_eq_of_tendsto_nhdsWithin_Ioi` it is the whole modification
  half of `f ∘ X = Y + C`. The statement mentions neither `X` nor the
  regularizing class, so it stands before any modification is constructed.

  **`t < T` is what carries the uniform integrability**, and is why a bound
  appears in a statement about a limit at `t`: the family of a martingale is
  uniformly integrable on an order ideal, `Y s =ᵐ[P] P[Y T | 𝓕 s]` holding for
  `s ≤ T`. The order topology turns `t < T` into
  `Set.Iio T ∈ 𝓝[D ∩ Set.Ioi t] t`, so a sequence running into the filter is
  eventually below `T`, and shifting the sequence by that index is cheaper than
  carrying an `Eventually` through Vitali.

  **The real and imaginary parts are not split**, although
  `Integrable.uniformIntegrable_condExp_filtration`
  (`Probability/Process/Filtration.lean:214`) is real valued and the martingale
  is `𝕂` valued. What carries uniform integrability across is domination:
  `norm_condExp_le`
  (`MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:246`) gives
  `‖P[Y T | 𝓕 s]‖ ≤ᵐ[P] P[‖Y T‖ | 𝓕 s]`, whose right hand side is the
  conditional expectation family of one fixed integrable real function, and
  `UnifIntegrable.of_norm_le_ae` above does the rest. A real–imaginary split
  would need a recombination lemma that Mathlib does not have either, so
  domination is strictly the cheaper route.

  The remaining three steps are Mathlib's: `Lp.eLpNorm_le_of_ae_tendsto`
  (`MeasureTheory/Function/LpSpace/Complete.lean:92`) puts the limit in `L¹`,
  `tendsto_Lp_finite_of_tendsto_ae`
  (`MeasureTheory/Function/UniformIntegrable.lean:540`) is Vitali, and
  `eLpNorm_condExp_le_eLpNorm`
  (`MeasureTheory/Function/ConditionalExpectation/Real.lean:288`) is the `L¹`
  contraction that carries the convergence through the conditional expectation.
  `[(𝓝[D ∩ Set.Ioi t] t).NeBot]` cannot be dropped, for the reason it cannot be
  dropped in the compensator half. Proved on 2026-09-17.
* `ae_eq_of_condExp_eq_of_condExp_mul_conj`, squaring out: a function is
  determined almost surely by its conditional expectation together with that of
  its squared modulus. If `f` is `m'` measurable, `f` and `g` are square
  integrable, `P[g | m'] =ᵐ[P] f` and `P[g * conj g | m'] =ᵐ[P] f * conj f`, then
  `g =ᵐ[P] f`. This is the step for which `hΦsq` sits in the hypotheses of the
  càdlàg theorem: read at `f` and at `f * conj f`, the two conditional
  expectations of the modification half give the two hypotheses, and the
  conclusion is agreement with **one** null set and not one per member of the
  class.

  The proof is an expansion and carries no process notion. With `d := g − f`,
  `∫ d conj d` is `∫ g conj g − ∫ g conj f − ∫ f conj g + ∫ f conj f`; the first
  is `∫ f conj f` by the second hypothesis and `integral_condExp`, the second is
  `∫ f conj f` by pulling the `m'` measurable factor `conj f` out
  (`condExp_bilin_of_aestronglyMeasurable_right`,
  `MeasureTheory/Function/ConditionalExpectation/PullOut.lean:215`) and the first
  hypothesis, the third is the conjugate of the second and `∫ f conj f` is real.
  So `∫ ‖g − f‖ ^ 2 = 0`, and a vanishing integral of a nonnegative integrand has
  a vanishing integrand.

  **`MemLp _ 2 P` is the right hypothesis and `Integrable` is not.** All four
  products must be integrable, and the cross terms are integrable exactly because
  both factors are square integrable (`MemLp.integrable_mul`,
  `MeasureTheory/Function/L1Space/Integrable.lean:1085`); the hypothesis on
  `g * conj g` constrains a conditional expectation, not the integrability of a
  product. Proved on 2026-09-17.
* `rightLimAlong D g t`, the right limit of `g` along `D` at `t`, and `g t` where
  there is none. This is the candidate modification, written as a function of one
  path and of nothing else.

  **The filter is guarded and not only the existence of a limit.** At a point
  isolated from the right along `D` the filter `𝓝[D ∩ Set.Ioi t] t` is `⊥` and
  *every* point of `E` is a limit along it, so an unguarded choice would name one
  — a value where there is no answer, the failure mode recorded for `sInf ∅`,
  `x / 0` and the Bochner integral of a non-integrable function. Under the guard
  `rightLimAlong D g t = g t` there (`rightLimAlong_of_not_neBot`), so the
  modification property holds at such a point by definition. `tendsto_rightLimAlong`
  says that where the filter is not `⊥` and a limit exists, this is one of them;
  no separation on `E` is asked, so one and not the. Written on 2026-09-17.
* `nhdsWithin_inter_Ioi_neBot`: for `D` dense and `r` not a greatest element,
  `(𝓝[D ∩ Set.Ioi r] r).NeBot`. `Dense D` is spent here and, in the path
  argument, nowhere else.

  **`[DenselyOrdered ι]` cannot be dropped and is not a convenience.** At a point
  `r` with an immediate successor the filter is `⊥` however dense `D` is, the
  right limit at `r` is unconstrained, and the path through `r` is uncontrolled.
  `ℝ≥0` and `ℝ` are densely ordered. Proved on 2026-09-17.
* `isCadlag_rightLimAlong`, **the deterministic half of Doob's
  regularization**: if `g` has both one sided limits along a dense `D` at every
  point, then `rightLimAlong D g` is càdlàg. No measure, no filtration, no
  process — a statement about one path, and the whole of the path side of
  `exists_cadlag_modification_of_isRegularizingClass`. It splits into
  `tendsto_rightLimAlong_nhdsWithin_Ioi` and
  `exists_tendsto_rightLimAlong_nhdsWithin_Iio`.

  **`[RegularSpace E]` is what the right continuity costs**, and it is read at
  one step. The values of `rightLimAlong D g` off `D` are limits, and a limit is
  not pinned down by "eventually in a neighbourhood" unless the neighbourhood is
  closed: the proof takes a closed neighbourhood `V` of `rightLimAlong D g t`
  (`closed_nhds_basis`, `Topology/Separation/Regular.lean:174`) and an open
  `U ∋ t` with `g '' (U ∩ D ∩ Set.Ioi t) ⊆ V`, observes that for
  `r ∈ U ∩ Set.Ioi t` the filter `𝓝[D ∩ Set.Ioi r] r` still runs inside
  `U ∩ D ∩ Set.Ioi t`, and closes with `IsClosed.mem_of_tendsto`. Without
  regularity the same argument gives only membership in the closure of `V`, which
  is no information. **No separation on `E` is used here**: `rightLimAlong D g t`
  is *a* limit and the nearby values approach that one; `[T2Space E]` enters the
  probabilistic statements at a different step. The left limits are the same
  argument with `U ∩ Set.Iio t` in place of `U`, and there no element has to be
  interpolated because `r < t` already makes `r` non-greatest. Proved on
  2026-09-17.
* `ae_forall_exists_tendsto_of_isRegularizingClass`, the `E`-valued
  regularization **at every point of the index at once**:
  `∀ᵐ ω, ∀ t`, the path `s ↦ X s ω` has both one sided limits along `D` at `t`.
  `ae_exists_tendsto_comp_of_isRegularizingClass` gives this for one scalar test
  function and `exists_tendsto_of_forall_tendsto_comp` makes an `E`-valued limit
  out of a family of scalar ones; what this adds is that the two are joined under
  **one** null set.

  Countability is spent twice, in two places that are not interchangeable: the
  countability of `Φ₀` collects the exceptional sets of its members, while
  `[(atTop : Filter ι).IsCountablyGenerated]` supplies the cofinal sequence `u`
  along which compact containment is read, and the countability of `D` is what
  makes the compact containment event measurable. One compact set per `n` and per
  `ω`, not one per `t`.

  **The filter is allowed to be `⊥` and the statement stays true**, which removes
  every hypothesis about maxima and about isolated points. Where the filter is
  `⊥` the convergence holds for any value, and `X t ω` is named as the witness so
  that no `[Nonempty E]` is needed. Where it is not, the filter itself produces a
  point `b ∈ D` above `t` and `u` an `n` with `b ≤ u n`; the filter is eventually
  below `b`, hence inside `Set.Iic (u n) ∩ D`, which is where the compact set
  lives. Proved on 2026-09-17.
* `ae_isCadlag_rightLimAlong_of_isRegularizingClass`, **the càdlàg half of
  the modification theorem**: under the hypotheses of the theorem below, almost
  every `rightLimAlong D (fun s ↦ X s ω)` is a càdlàg path. The candidate
  modification is thereby named and its path property proved; what the theorem
  below still owes is the modification property `X' t = X t` almost surely for
  each `t`, which is a conditional expectation argument and not a path argument.
  Each hypothesis is read at one step: `[RegularSpace E]` at the right
  continuity, `[T2Space E]` at `exists_tendsto_of_forall_tendsto_comp`,
  `[DenselyOrdered ι]` and the density of `D` at `nhdsWithin_inter_Ioi_neBot`,
  the countability of `D` and the measurability of `X` at
  `CompactContainment.ae_exists_isCompact`, and
  `[(atTop : Filter ι).IsCountablyGenerated]` at the cofinal sequence. Proved on
  2026-09-17.
* `exists_cadlag_modification_of_isRegularizingClass`: if `P` is a probability
  measure solving the martingale problem for `𝓧`, `Φ` is a regularizing class
  for `X` along `𝓧` containing a countable subset `Φ₀` of bounded continuous
  functions that separates the points of `E` and whose squares `f * conj f` lie
  in `Φ`, and `X` satisfies compact containment, then `X` has a modification
  with paths in the càdlàg space. The modification is
  `fun t ω ↦ rightLimAlong D (fun s ↦ X s ω) t`, the right limit of the path
  along `D`, which is the object the two halves of the proof are about.

  **`IsMPSolution 𝓧 𝓕 P` belongs to the statement**, and the theorem is false
  without it; it was missing until 2026-09-16. `IsRegularizingClass` constrains
  `𝓧` only through the membership `Y ∈ 𝓧` and says nothing about what a member
  of `𝓧` is, so `𝓧 = Set.univ`, `Y = f ∘ X` and `C = 0` satisfy it for **every**
  process and every class — all four fields of `IsCompensatorFor` are trivial at
  `C = 0`. The witness that the conclusion then fails: `ι = E = ℝ`, `P` any
  probability measure, `X t ω = 1` for rational `t` and `0` otherwise,
  deterministic and valued in `Set.Icc 0 1`, so compact containment holds;
  `Φ` the bounded continuous functions, `Φ₀ = {Real.arctan}`. A càdlàg
  modification would be `1` almost surely at every rational at once and `0`
  almost surely at an irrational `t₀`, and right continuity along rationals
  decreasing to `t₀` forces `0 = 1` on a set of positive measure.

  What the hypothesis supplies is the regularization of `Y`: a member of `𝓧` is
  a `𝕂`-valued martingale, its real and imaginary parts are real submartingales,
  and `Submartingale.ae_exists_tendsto_nhdsWithin` gives them one sided limits
  along `D`. The compensator carries its own by a field of `IsCompensatorFor`,
  and `f ∘ X = Y + C` inherits them.

  **Four hypotheses carry the modification half**, and each is read at exactly
  one step of it. They were written out on 2026-09-17, fifth run of that day,
  when the half was proved.

  * **`hcont`, the continuity of the members of `Φ₀`.** Point separation alone
    does not reach an `E`-valued limit: the one route from the real limits to it
    is `exists_tendsto_of_forall_tendsto_comp`, and it reads
    `∀ f ∈ Φ₀, Continuous f` — a compact set catches a cluster point and a
    **continuous** `f` carries it. Neither `IsSeparating Φ` nor
    `IsRegularizingClass` gives continuity of a single member.
  * **`hsq`, closure under `f ↦ f * conj f`**, carries the modification
    property, and point separation by itself does not. The chain is: for `f ∈ Φ`
    continuous and bounded and `X'` the right limit along `D`,
    `f (X' t) = Y_{t+} + C_{t+}`; then `C_{t+} = C t` almost surely, which is
    `IsCompensatorFor.ae_eq_of_tendsto_nhdsWithin_Ioi` above; then
    `P[Y_{t+} | 𝓕 t] = Y t`, which is
    `Martingale.condExp_ae_eq_of_tendsto_nhdsWithin_Ioi`; and
    `P[C_{t+} | 𝓕 t] = C t` because `C t` is `𝓕 t`-strongly measurable.
    Together `P[fun ω ↦ f (X' t ω) | 𝓕 t] =ᵐ[P] fun ω ↦ f (X t ω)`. Reading that
    at `f` and at `f * conj f` and expanding the square is
    `ae_eq_of_condExp_eq_of_condExp_mul_conj`, so `f (X' t) = f (X t)` almost
    surely for each of the countably many `f ∈ Φ₀`, and point separation
    finishes. Without `hsq` the null set of that identity depends on `f`, and a
    countable family that separates points does not determine a conditional law.
    The hypothesis is asked of the members of `Φ₀` only, and the square lands in
    `Φ` and not in `Φ₀`: the square is fed to the compensated decomposition and
    never to the point separation.

    The alternative repair is a filtration right continuous up to null sets:
    then `Y_{t+}`, measurable for `𝓕_{t+}`, is measurable for `𝓕 t`, and
    `Y_{t+} = P[Y_{t+} | 𝓕 t] = Y t`. Those are the usual conditions, and
    Mathlib has neither them nor the augmentation (checked 2026-09-12); that is
    a milestone of its own. `hsq` is the cheaper of the two, asks nothing of
    the filtration, and is the one this roadmap carries.
  * **`hbdd`, a bound on each member of `Φ₀`.**
    `ae_eq_of_condExp_eq_of_condExp_mul_conj` asks `MemLp _ 2 P` of both sides,
    and `IsRegularizingClass` does not give it: `Y t` is integrable by
    definition, but `C t` is only `StronglyAdapted`, so `f ∘ X t = Y t + C t` is
    not even known to be integrable. A bound supplies everything at once —
    `f ∘ X t` and `f ∘ X' t` become bounded, hence in every `Lᵖ` under a
    probability measure, and `C t` becomes integrable as a difference. A class
    of bounded continuous functions satisfies it anyway, and the square inherits
    it, `‖f x * conj (f x)‖ = ‖f x‖ ^ 2 ≤ M ^ 2`.
  * **`[FirstCountableTopology ι]`**, because `C_{t+} = C t` passes through a
    sequence running into `𝓝[D ∩ Set.Ioi t] t`, hence through a countably
    generated filter. It is a different hypothesis from
    `[(atTop : Filter ι).IsCountablyGenerated]`, which
    `ae_exists_tendsto_comp_of_isRegularizingClass` carries: cofinality is not
    first countability. `ℝ≥0` and `ℝ` have both.

  **`IsSeparating Φ` is not among them and is not a hypothesis of this
  statement.** It stood here from the beginning and was dropped on 2026-09-17,
  fifth run of that day, when the proof was written and no step read it. What
  the proof separates with is the **pointwise** separation of `Φ₀`, at the last
  line: two points of `E` on which every member of `Φ₀` agrees are equal.
  Separation of **measures**, which is what `IsSeparating` says, neither implies
  nor is implied by pointwise separation; it is what the uniqueness statements
  of the roadmap **WeakConvergence** need, and it belongs there. Carrying it
  here would have made the theorem inapplicable to a class that determines paths
  but not laws.

  That the theorem is **false** without `hcont`, `hsq` or `hbdd` is not claimed;
  no witness is known for any of the three.
* `norm_compensator_sub_le_of_isProgressive`: for `g` measurable with
  `‖g x‖ ≤ b` and `X` progressive for the clock, and `s ≤ t`,
  ```
  ‖∫ u in interval c ⊥ t, g (X u ω) ∂q - ∫ u in interval c ⊥ s, g (X u ω) ∂q‖
    ≤ b * q.real (interval c s t) .
  ```
  It is `mpFamily_sub_of_isProgressive` of Milestone 2 read at `f = 0`, so the
  state term drops out and no measurability of `f` is asked. The whole block
  below is this estimate read three times.
* `isCompensatorFor_mpFamily`: under the same hypotheses on `g` together with
  `Clock.IsContinuousFor q c` and `∀ t, Measurable[𝓕 t] (X t)`, the pair
  ```
  Y t ω = f (X t ω) - ∫ u in interval c ⊥ t, g (X u ω) ∂q ,
  C t ω = ∫ u in interval c ⊥ t, g (X u ω) ∂q
  ```
  satisfies `IsCompensatorFor X 𝓕 P D f Y C` for every `D` and every finite `P`.
  The decomposition field is `sub_add_cancel` and holds at every sample point;
  the compensator is **continuous** in `t` at every sample point, and
  `exists_limits` is that continuity restricted along `nhdsWithin_le_nhds`, so
  the countability of `D` plays no part; `l1_rightContinuous` is the same
  estimate under the lower integral, where the bound is uniform in `ω` and the
  measure is finite.

  Three hypotheses the abstract statement carries and this one does not: the
  measurability of `f`, since `IsCompensatorFor` constrains `C` and `C` does not
  see `f`; `[OrderTopology ι]`, the estimate reading the index only through
  `𝓝 t`; and any countability or density of `D`, which is quantified over.
* `isRegularizingClass_mpFamily`: if every `p ∈ A` has `p.2` measurable and
  bounded — the bound may depend on `p` — and `X` is progressive and adapted for
  a clock with `Clock.IsContinuousFor`, then
  `IsRegularizingClass (Prod.fst '' A) X (mpFamily A Q c X) 𝓕 P D`. The member of
  `𝓧` exhibited is the test process of `mpFamily` itself, so that the càdlàg
  theorem and the solution speak about the same processes, and the first
  component of a pair is unconstrained.

  This is the hypothesis `hΦ` of
  `exists_cadlag_modification_of_isRegularizingClass`, produced rather than
  assumed, and with `h𝓧` it is the pair that ties the càdlàg theorem to the
  martingale problem. What remains to be supplied at an instance is about the
  state space and not about the process: a countable, bounded, continuous,
  point separating `Φ₀ ⊆ Prod.fst '' A` closed under `f ↦ f * conj f` into
  `Prod.fst '' A`, and compact containment.
* `lebesgueClock_isContinuousFor_optional`: the Lebesgue clock on `ℝ≥0` has
  `Clock.IsContinuousFor` under the optional convention, the window `(s ⊓ t, s ⊔ t]`
  having mass `|s - t|` exactly by `lebesgueClock_apply_Ioc`. The clock every
  jump process of Milestone 4 runs on is therefore an admissible one here.
* `measurable_of_measurable_indicator_comp`: over a **countable** `E` with
  measurable points, a map `F : α → E` is measurable as soon as every real
  functional `1_{x} ∘ F` is, the σ-algebra on `α` being carried explicitly
  because the one this is applied to — a product with a value of a filtration —
  is not an instance.

  It is the step that separates the `E` valued path from its real functionals.
  The dyadic argument of `measurable_uncurry_min_of_rightContinuous` reaches
  every real functional of a right continuous process and not the process
  itself, because a limit of `E` valued measurable maps is measurable only when
  the diagonal of `E` is; a countable `E` with measurable points has one, and
  here it is not used through a limit at all, the limit having been taken in
  `ℝ`.
* `lebesgueClock_isProgressive_jumpProcessE`: for `E` countable with measurable
  points and `lam` measurable,
  ```
  lebesgueClock.IsProgressive (fun t ω ↦ jumpProcessE lam t ω) (jumpFiltrationE lam hlam) .
  ```
  The extension the definition asks for is the path stopped at `t`, which is the
  shape `measurable_uncurry_jumpProcessE` produces; below `t` the truncation does
  nothing. No topology on `E` is needed.

  With it the jump construction of Milestone 4 satisfies all three hypotheses of
  `isRegularizingClass_mpFamily`, and the emptiness probe of this milestone has
  a state process. What a probe still has to supply is about the state space
  alone: a countable, bounded, continuous, point separating `Φ₀` closed under
  `f ↦ f * conj f`, and compact containment — on a **finite** state space with
  the discrete topology the indicators of the points are such a `Φ₀`, being
  idempotent, and compact containment is trivial.
* `measurable_jumpFiltrationE_self`, `mem_image_fst_jumpOperator_bool`,
  `boolIndicators` and `exists_cadlag_modification_flip`: **the emptiness probe
  of this milestone, discharged on data.** **Proved** on 2026-09-17, ninth run.
  For every initial law `nu` on `Bool`, the local jump construction at the flip
  rate has a càdlàg modification:
  ```
  ∃ X', (∀ t, X' t =ᵐ[jumpMeasure flipKernel nu] jumpProcessE flipRate t)
        ∧ ∀ᵐ ω, IsCadlag (fun t ↦ X' t ω) .
  ```
  Every one of the twelve hypotheses of
  `exists_cadlag_modification_of_isRegularizingClass` is met by data and none is
  assumed: the solution is `jumpProcessE_isMPSolution`, the regularizing class is
  `isRegularizingClass_mpFamily` fed by
  `lebesgueClock_isProgressive_jumpProcessE`, the countable dense time set is any
  one, `ℝ≥0` being separable, and the state space is `Bool`.

  `measurable_jumpFiltrationE_self` is the adaptedness
  `isRegularizingClass_mpFamily` asks for, and it is `jumpFiltrationE` unfolded —
  that filtration *is* the natural one, so the statement is
  `measurable_naturalFiltration` at `j = i`. `mem_image_fst_jumpOperator_bool`
  says that over `Bool` the domain of the generator is the **full** function
  space, since measurability is free on a countable space with measurable points
  and boundedness is free on a finite one; with it `Φ₀ ⊆ Φ` and the closure of
  `Φ` under `f ↦ f * conj f` are the same one line. `boolIndicators` is `Φ₀`.

  **What the probe does not show.** On a finite state space every path has
  relatively compact range, so `CompactContainment` is `K = Set.univ` and the
  hypothesis the theorem exists to exploit is vacuous; likewise `T2Space`,
  `RegularSpace`, `OpensMeasurableSpace` and the continuity of `Φ₀` come from the
  discrete topology and say nothing about a general `E`. The probe establishes
  joint satisfiability of the hypotheses on data that also solves a martingale
  problem, which is what it is for, and it is the first statement in this
  development that produces a càdlàg process out of a martingale problem.
* The classical statement as a one line instance: for `A ⊆ Cb(E) × Bdd(E)` whose
  domain is separating and contains a countable subset separating points, every
  solution of the martingale problem for `A` satisfying compact containment has
  a càdlàg modification. Formalize the abstract theorem and derive this; the
  operator, its domain and the compensator play no part in the proof.

The modification has its paths in the càdlàg space over the whole state space.
The last three items cut it down to an open subset `U ⊆ E`, which is how the
one point compactification and a product of state spaces are handled
(Ethier–Kurtz, Remark 4.3.11). Fix `[OrderBot ι]` and `E` a metric space.

* `IsMPSolutionFor.integral_comp_stoppedLim_eq`, the identity along an
  increasing sequence of stopping times (Ethier–Kurtz, Theorem 4.3.8, (3.31)
  and (3.32)). Let `X` solve the martingale problem for `A` with càdlàg paths,
  let `(f, g) ∈ A` with `f` bounded continuous and `g` bounded, let `τ m` be an
  increasing sequence of stopping times for `𝓕`, `τ = ⨆ m, τ m`, and
  `Y t ω = limUnder atTop (fun m ↦ X (min (τ m ω) t) ω)`. Then
  ```
  ∫ ω, f (Y t ω) ∂P
    = ∫ ω, f (X ⊥ ω) ∂P
      + ∫ ω, (∫ u in Clock.interval q c ⊥ (min (τ ω) t), g (X u ω) ∂q) ∂P .
  ```
  Optional sampling at the bounded stopping time `min (τ m) t`, which is the
  first item of this milestone, gives the identity at each `m`, and `m → ∞` is
  bounded convergence together with the continuity of `f`. The identity holds
  for the pairs of `A` itself; it is not extended to a closure of `A`, and
  Milestone 2 says why.
* `IsMPSolutionFor.ae_forall_mem_of_tendsto` (Ethier–Kurtz, Proposition 4.3.9).
  Let `U ⊆ E` be open, let `X` solve the martingale problem for `A` with càdlàg
  paths and `P (X ⊥ ⁻¹' U) = 1`, and let `(f n, g n)` be a sequence in `A` with
  `f n` bounded continuous, `g n` bounded, `C : ℝ` satisfying `‖f n x‖ ≤ C` and
  `-C ≤ g n x` for all `n` and `x`, `f n x → Set.indicator U 1 x` for every `x`,
  and `g n x → 0` for every `x`. Then `∀ᵐ ω ∂P, ∀ t, X t ω ∈ U`, and almost
  every path has no limit point in `E \ U` on any interval `Set.Iic t`, so it is
  càdlàg as a `U`-valued map. The stopping times are
  `τ m = sInf {t | infEdist (X t ω) (E \ U) < 1/m}`, the previous item supplies
  the identity at `(f n, g n)`, and `n → ∞` is dominated convergence on the left
  and Fatou's lemma on the right, which is where the lower bound on `g n` is
  used. The Fatou step is `IsMPSolutionFor.submartingale_mpProcess_of_tendsto`
  of Milestone 2 read at the stopped process.
* `IsMPSolutionFor.ae_forall_mem_iInter_of_tendsto` (Ethier–Kurtz,
  Proposition 4.3.10): the same conclusion for `U = ⋂ k, U k` with each `U k`
  open, from a sequence as above for each `k` separately. The previous item
  gives `∀ᵐ ω ∂P, ∀ t, X t ω ∈ U k` for every `k`, and a countable intersection
  of almost sure events is almost sure. No hypothesis about `U` itself is
  needed, which is the reason to state this case separately: a sequence
  converging to `Set.indicator (⋂ k, U k) 1` need not exist in `A` even when one
  exists for every `U k`.

A càdlàg path has left limits; it need not reach them. The last block of this
milestone says when a solution does, which is a second path property proved in
the language of the martingale problem and not of the state space. Keep
`[LinearOrder ι]` with the order topology and the countable dense `D`, add
`[OrderBot ι]` and the conditionally complete lattice structure for the suprema
of stopping times, and let `E` be a separable metric space. Throughout this
block a stopping time is `WithTop ι`-valued, the supremum of a sequence of them
is taken in `WithTop ι`, and a process is read at one through
`MeasureTheory.stoppedValue`; the first item spells this out and the later ones
write `X (min (τ n ω) t) ω` for `stoppedValue X (fun ω ↦ min (τ n ω) t) ω`.

* `IsQuasiLeftContinuous X 𝓕 P`: for every `τ : ℕ → Ω → WithTop ι` with each
  `τ n` a stopping time for `𝓕` and `Monotone τ`, and every `t`,
  ```
  ∀ᵐ ω ∂P, ⨆ n, τ n ω ≤ (t : WithTop ι) →
    Tendsto (fun n ↦ stoppedValue X (τ n) ω) atTop
      (𝓝 (stoppedValue X (⨆ n, τ n) ω)) .
  ```
  The times are `WithTop ι`-valued because that is what a stopping time is in
  Mathlib: `IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → WithTop ι)`
  (`Mathlib/Probability/Process/Stopping.lean:76`). Reading the process at such a
  time is `MeasureTheory.stoppedValue` (`:797`), which is
  `fun ω ↦ u (τ ω).untopA ω`, with `WithTop.untopA` the order dual of
  `WithBot.unbotA` — a `noncomputable abbrev` under `[Nonempty α]`,
  `Mathlib/Order/WithBot.lean:270` — so `[OrderBot ι]` already supplies what it
  asks and no hypothesis is added for it. The supremum `⨆ n, τ n ω` is taken in
  `WithTop ι` through the instance `SupSet (WithTop α)` for `[SupSet α]`
  (`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:52`), so the
  conditionally complete lattice structure on `ι` fixed above is all it needs.
  The clause `⨆ n, τ n ω ≤ t` is what makes `τ n` and `⨆ n, τ n` bounded
  stopping times, and it is why the statement is quantified over `t` rather than
  over an event `{τ < ∞}`; on `ι = [0, ∞)` a countable cofinal family of `t`
  recovers `P {lim X (τ n) = X τ, τ < ∞} = P {τ < ∞}`, which is the form of
  Ethier–Kurtz, Theorem 4.3.12. Mathlib has no notion of this kind: the strings
  `quasi-left` and `QuasiLeftContinuous` occur nowhere in the library.
* `IsQuasiLeftContinuous.ae_eq_leftLim`: reading the definition at the constant
  stopping times `τ n = s n` for a monotone `s` with `s n < t` and
  `s n → t` gives `∀ᵐ ω ∂P, Function.leftLim (X · ω) t = X t ω`, for a process
  whose paths have left limits almost surely and a Hausdorff `E`. This is the
  sharpening of Ethier–Kurtz, Lemma 3.7.7, which says only that the set of `t`
  failing it is countable; that lemma is
  `SkorokhodSpace.exists_countable_dense_continuity` in **SkorokhodSpace**
  Milestone 8. Proved on 2026-09-06.

  Both hypotheses beyond the sequence are indispensable, and the version with
  `¬ IsMin t` in their place is false. On `ι = ℕ` and `t = 1` every monotone
  sequence of stopping times bounded by `1` is eventually constant, so
  quasi-left-continuity holds vacuously, while `𝓝[<] (1 : ℕ) = pure 0` makes
  `Function.leftLim (X · ω) 1 = X 0 ω`. What `¬ IsMin t` must be replaced by is
  approachability from the left by a sequence — the hypothesis that
  `not_isQuasiLeftContinuous_of_atom` below already carries. And since the
  almost-sure quantifier of `IsQuasiLeftContinuous` sits inside the
  quantifier over sequences, the exceptional set depends on the sequence and
  uncountably many sequences cannot be combined: the passage from one sequence
  to the filter `𝓝[<] t` is exactly what the existence of the left limit —
  the second half of `IsCadlag`, assumed by Ethier–Kurtz here anyway —
  supplies.
* `IsCadlag.exists_tendsto_comp_monotone`: a càdlàg path converges along
  every nondecreasing sequence of indices that has a supremum. The proof splits
  on whether the sequence **reaches** its supremum: where it does, monotonicity
  makes the values eventually constant and no path property is read; where it
  does not, the sequence runs into `𝓝[<] T` and the limit is the left limit, the
  second field of `IsCadlag`. Right continuity is not used, and the statement
  produces *a* limit without claiming uniqueness, so no separation axiom on `E`
  enters. **In Lean** on 2026-09-17, tenth run.
* `isQuasiLeftContinuous_of_forall_ae_tendsto_comp`: **from countably many
  scalar convergences to quasi-left-continuity**. For a countable class `Φ₀` of
  continuous functions separating the points of `E`, almost sure càdlàg paths,
  and the scalar convergence `f (X_{τ n}) → f (X_{τ'})` for each `f ∈ Φ₀` along
  every nondecreasing sequence of stopping times bounded by `t`, the process is
  quasi-left-continuous. This is the last line of the abstract theorem below
  isolated: the path property produces a limit `l` and the separation identifies
  it with `X_{τ'}`. Countability is what allows the null set of the scalar
  statement to be chosen once for all `f` rather than once per `f`; no
  compactness, no separation axiom on `E`, and no measurability of `X` are read,
  the uniqueness of limits being taken in `𝕂` alone. **In Lean** on 2026-09-17,
  tenth run.
* `tendsto_ae_condExp_rclike`: **Lévy's upward theorem for an `RCLike` valued
  integrand**. For a filtration `ℱ : Filtration ℕ m` on a finite measure space
  and any `g : Ω → 𝕂`, `μ[g | ℱ n]` converges almost everywhere to
  `μ[g | ⨆ n, ℱ n]`. Mathlib's `MeasureTheory.tendsto_ae_condExp` sits in a
  section whose variable block fixes `{g : Ω → ℝ}`
  (`Probability/Martingale/Convergence.lean:243`), so the `𝕂` valued case is the
  two components, recombined by `RCLike.re_add_im`; the passage of `condExp`
  through `RCLike.reCLM` and `RCLike.imCLM` is
  `ContinuousLinearMap.comp_condExp_comm`
  (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:359`). No
  integrability is assumed, exactly as in the real valued statement: where `g` is
  not integrable both sides are `0`. **In Lean** on 2026-09-17, eleventh run.
* `tendsto_integral_norm_condExp_of_tendsto`: a sequence that vanishes in `L¹`
  has conditional expectations that vanish in `L¹`. This is conditional Jensen in
  the form `integral_norm_condExp_le`
  (`MeasureTheory/Function/ConditionalExpectation/Real.lean:206`) and nothing
  else. The σ-algebras are an **arbitrary sequence** — no filtration, no
  monotonicity — so the statement applies to `n ↦ (hτ n).measurableSpace` without
  knowing that the stopping times are nondecreasing. **In Lean** on 2026-09-17,
  eleventh run.
* `tendstoInMeasure_zero_of_tendsto_integral_norm`: a sequence of integrable
  functions whose `L¹` norms tend to `0` tends to `0` in measure. Only
  `ofReal_integral_norm_eq_lintegral_enorm`
  (`MeasureTheory/Integral/Bochner/Basic.lean:543`) stands between the Bochner
  form in which `IsL1LeftContinuousAlongStoppingTimes` is stated and the
  `eLpNorm` form in which Mathlib states the implication
  (`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`). **In Lean** on
  2026-09-17, eleventh run.
* `ae_eq_condExp_iSup_of_tendsto`: **the identification of a pathwise limit with
  a conditional expectation**, and the shape in which the three items above are
  consumed. If a sequence `a` splits, for each `n`, as
  `a n =ᵐ[μ] μ[W | ℱ n] + μ[Z n | ℱ n]` with one fixed `W` and a perturbation `Z`
  vanishing in `L¹`, and if `a n → A` almost surely, then
  `A =ᵐ[μ] μ[W | ⨆ n, ℱ n]`. The `L¹` hypothesis yields an almost sure statement
  about the perturbation only along a subsequence
  (`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`), and that suffices
  precisely because the *left* side converges along the whole sequence: the
  subsequence evaluates a limit already known to exist rather than producing one.
  In the application `a n` is `f (X (min (τ n) t))` and the left convergence is
  the càdlàg property of the paths, which is why the statement carries no
  hypothesis on `a` beyond the convergence itself. **In Lean** on 2026-09-17,
  eleventh run.
* `ae_forall_eq_of_right_dense`: **from an identity that holds at each time
  almost surely to one that holds almost surely at all times**. Let `D` be
  countable, let every `t` either lie in `D` or be approached from the right
  along `D` — `(𝓝[D ∩ Set.Ioi t] t).NeBot` — let `f (X t) = Y t + C t` hold
  almost surely for each `t ∈ D`, and let the paths of `f ∘ X`, of `Y` and of `C`
  be almost surely right continuous along `D ∩ Set.Ioi t` at every `t`. Then
  `∀ᵐ ω, ∀ t, f (X t ω) = Y t ω + C t ω`. Neither hypothesis nor conclusion reads
  a measurability: this is a statement about paths. **In Lean** on 2026-09-17,
  twelfth run.
* `IsCompensatorFor.ae_forall_decomposition`: the previous item read at the
  `decomposition` field of `IsCompensatorFor`, and
  `IsCompensatorFor.decomposition_stoppedValue`, its value at a random time
  `σ : Ω → WithTop ι`:
  `f (stoppedValue X σ) =ᵐ[P] stoppedValue Y σ + stoppedValue C σ`. **`σ` is
  neither a stopping time nor measurable**; both are irrelevant, because the
  identity holds at all times at once and is merely evaluated at `(σ ω).untopA`.
  **In Lean** on 2026-09-17, twelfth run.
* `LiftWitness`: the witness that the **right continuity of `Y` does not follow**
  from that of `f ∘ X` and of `C` and must be assumed. On `ι = ℝ≥0` and `Ω = ℝ`
  with Lebesgue measure on `Set.Icc 0 1`, with `X` constant, `f = 0`, `C = 0` and
  `Y t ω = 1` exactly on the diagonal `(t : ℝ) = ω`, every field of
  `IsCompensatorFor` holds for **every** `D` (`isCompensatorFor_diagY`), a
  countable right dense `D` exists (`exists_countable_right_dense`, from
  `TopologicalSpace.exists_countable_dense` and `Dense.open_subset_closure_inter`),
  and the conclusion fails (`not_ae_forall_diagY_eq_zero`). `IsCompensatorFor`
  constrains `Y` only through the decomposition, which pins it down at each time
  only off a null set; the right continuity of `Y` is what forbids the null sets
  to fill the space. **In Lean** on 2026-09-17, twelfth run.
* `not_isQuasiLeftContinuous_of_isRegularizingClass_of_free_solutionSet`: a
  martingale hypothesis on `Y` **is indispensable** in the theorem below, and
  until 2026-09-17 there was none. Constrain `Y` by nothing and `Y := f ∘ X`,
  `C := 0` satisfy every remaining hypothesis — all of them are statements about
  the zero process — for **any** `X` and even for `D = ∅`. The coin of
  `AtomWitness` over `ι = ENNReal` is a càdlàg `X` with a separating `Φ` that is
  not quasi-left-continuous, so the statement without it is false. What it lacks
  is optional sampling, which with `C = 0` the decomposition says nothing about.
  **In Lean** on 2026-09-17, twelfth run.
* `isStoppingTime_iSup`: the supremum of a sequence of stopping times is a
  stopping time, `{⨆ n, τ n ≤ i} = ⋂ n, {τ n ≤ i}`. Mathlib carries the infimum
  (`MeasureTheory.IsStoppingTime.iInf`,
  `Mathlib/Probability/Process/Stopping.lean:381`) and not the supremum, and the
  asymmetry is real: the infimum needs `Filtration.IsRightContinuous`,
  `DenselyOrdered` and `NoMaxOrder`, the supremum needs nothing beyond the
  conditionally complete order of the index, since `OrderTop.bddAbove` makes
  `ciSup_le_iff` available over `WithTop ι`. **In Lean** on 2026-09-17,
  fourteenth run.
* `IsOptionalSamplingFor Y 𝓕 P`: for every `t`, every stopping time `σ ≤ t`,
  `stoppedValue Y σ =ᵐ[P] P[Y t | hσ.measurableSpace]`. This is the property of
  the process that quasi-left-continuity consumes, and it is a hypothesis rather
  than a consequence of `Martingale Y 𝓕 P`: optional sampling in continuous time
  needs right continuous paths and a bound, and `stoppedValue_ae_eq_condExp` of
  this milestone supplies it over `ℝ≥0` and over no other index. Naming the
  consequence rather than the cause is what removes the solution set `𝓧` from
  the theorem below. **In Lean** on 2026-09-17, fourteenth run.
* `isOptionalSamplingFor_of_martingale`, the property over `ι = ℝ≥0`: for `Y` a
  martingale with right continuous paths, strongly progressively measurable and
  bounded, `IsOptionalSamplingFor Y 𝓕 P`. It is `stoppedValue_ae_eq_condExp` of
  this milestone quantified over the stopping times bounded by a `t`, and it is
  the one input every instance of the two theorems below needs. The statement
  belongs where both of its ends are visible: `stoppedValue_ae_eq_condExp` is
  proved after the block in which `IsOptionalSamplingFor` is defined, so either
  that block moves or the instances are stated after it.
* `IsStronglyMeasurableAlongStoppingTimes C 𝓕`: for every stopping time `σ`,
  `stoppedValue C σ` is `hσ.measurableSpace`-strongly measurable.
  `IsCompensatorFor` gives `StronglyAdapted 𝓕 C`, and adaptedness at a *time* is
  not adaptedness at a *stopping time*. Over a Borel codomain this is
  `MeasureTheory.measurable_stoppedValue`
  (`Mathlib/Probability/Process/Stopping.lean:1044`) applied to
  `IsStronglyProgressive 𝓕 C`; for a `𝕂`-valued compensator it is assumed,
  because `RCLike` gives `𝕂` a topology and no `MeasurableSpace`, so the Borel
  hypothesis of that theorem cannot be written. **In Lean** on 2026-09-17,
  fourteenth run.
* `ae_eq_limUnder_condExp_stoppedValue`: one continuous bounded test function `g`
  and one nondecreasing family `σ ≤ σ' ≤ t` of stopping times. Then
  `g (stoppedValue X σ')` is almost everywhere strongly measurable and
  ```
  (fun ω ↦ limUnder atTop fun n ↦ g (stoppedValue X (σ n) ω))
    =ᵐ[P] P[g ∘ stoppedValue X σ' | ⨆ n, stoppingFiltration hσ hσmono n] .
  ```
  This is `ae_eq_condExp_iSup_stoppedValue` with its seven hypotheses discharged
  from `IsCompensatorFor`, `IsOptionalSamplingFor`,
  `IsStronglyMeasurableAlongStoppingTimes` and
  `IsL1LeftContinuousAlongStoppingTimes`. Two of the discharges are worth
  naming. Optional sampling at `σ n` against `stoppedValue Y σ'` is **not** a
  second hypothesis: `IsOptionalSamplingFor` gives both sides against `Y t` and
  `MeasureTheory.condExp_condExp_of_le` joins them, because `σ n ≤ σ'` makes
  `𝓕_{σ n}` a sub-σ-algebra of `𝓕_{σ'}`. And the integrability of the
  compensator is not assumed at all: `C_ρ = g (X_ρ) - Y_ρ` is bounded by
  `M + ‖Y_ρ‖`, and `Y_ρ` is integrable because it is almost everywhere a
  conditional expectation. The limit is taken in `𝕂` and not in `E`, so no
  hypothesis on `E` beyond its topology occurs. **In Lean** on 2026-09-17,
  fourteenth run.
* `stoppingFiltration`: a nondecreasing sequence `σ : ℕ → Ω → WithTop ι` of
  stopping times for `𝓕` gives a `Filtration ℕ m`, `n ↦ (hσ n).measurableSpace`.
  Monotonicity is `MeasureTheory.IsStoppingTime.measurableSpace_mono` and the
  bound `MeasureTheory.IsStoppingTime.measurableSpace_le`, both of
  `Mathlib/Probability/Process/Stopping.lean`; neither asks anything of the index
  beyond `Preorder`. This is the only place at which the stopping times of
  quasi-left-continuity are read as a filtration. **In Lean** on 2026-09-17,
  thirteenth run.
* `ae_eq_condExp_iSup_stoppedValue`: **the middle step**, that is, all of
  `isQuasiLeftContinuous_of_isRegularizingClass` except the final appeal to the
  separating class. Let `f ∘ X = Y + C` hold almost surely at all times at once,
  let `ℱ : Filtration ℕ m` be arbitrary, and let
  `stoppedValue Y (σ n) =ᵐ[P] P[stoppedValue Y σ' | ℱ n]` — optional sampling —
  and `stoppedValue C (σ n)` be `ℱ n`-strongly measurable. If the stopped
  increments of `C` vanish in `L¹` and `f (stoppedValue X (σ n))` converges
  almost surely to `A`, then
  `A =ᵐ[P] P[f (stoppedValue X σ') | ⨆ n, ℱ n]`.

  **No stopping time occurs in the statement**, and none has to: `σ` and `σ'`
  enter only through `stoppedValue`, which is evaluation at `(σ ω).untopA`, and
  the stopping times are read in the two hypotheses alone. `OrderBot ι` is the
  only instance on the index that the proof reads, and it is read by `untopA`.

  The three hypotheses that `IsCompensatorFor` does **not** supply are named by
  the statement rather than hidden in it: the decomposition is
  `IsCompensatorFor.ae_forall_decomposition` and not the field `decomposition`,
  by `LiftWitness`; optional sampling needs right continuity and a bound on `Y`,
  which are properties of the solution class, and `stoppedValue_ae_eq_condExp`
  supplies it over `ℝ≥0`; and strong measurability of `stoppedValue C (σ n)` for
  `ℱ n` is progressive measurability of `C`, since `StronglyAdapted` is
  adaptedness at a *time* and not at a stopping time. **In Lean** on 2026-09-17,
  thirteenth run.
* `isQuasiLeftContinuous_of_isRegularizingClass`, the abstract form of
  Ethier–Kurtz, Theorem 4.3.12, with no operator and no compensator of any
  special shape. Let `Φ₀ ⊆ Φ` be countable, continuous, bounded and separating
  the points of `E`, let `Φ` contain the square `f * conj f` of every `f ∈ Φ₀`,
  let `X` be càdlàg, and let every `f ∈ Φ` have a decomposition `f ∘ X = Y + C`
  with `IsCompensatorFor X 𝓕 P D f Y C`, with `Y` and `C` right continuous,
  `IsOptionalSamplingFor Y 𝓕 P`, `IsStronglyMeasurableAlongStoppingTimes C 𝓕`,
  and `C` **left continuous in `L¹` along stopping times**: for every
  nondecreasing sequence `τ` of stopping times, with `τ' = ⨆ n, τ n`, and every
  `t`,
  ```
  Tendsto (fun n ↦ ∫ ω, ‖C (min (τ' ω) t) ω - C (min (τ n ω) t) ω‖ ∂P)
    atTop (𝓝 0) .
  ```
  Then `IsQuasiLeftContinuous X 𝓕 P`. The proof runs at
  `σ n = min (τ n) t` and `σ' = min τ' t`, which are stopping times by
  `MeasureTheory.IsStoppingTime.min_const` and `isStoppingTime_iSup` above, and
  it has three moves.

  First, the **paths**: `stoppedValue X (σ n) ω = X ((σ n ω).untopA) ω` runs
  along a nondecreasing sequence of indices bounded by `t`, so
  `IsCadlag.exists_tendsto_comp_monotone` gives a limit at almost every
  sample point, and `g` continuous carries it to `g`. No supremum of the `σ n`
  is computed and no interchange of `min` with `⨆` is needed: the limit is
  produced, not identified.

  Second, the **conditional expectation**:
  `ae_eq_limUnder_condExp_stoppedValue` above, read once at `f` and once at
  `f * conj f`, gives
  ```
  A =ᵐ[P] P[f ∘ stoppedValue X σ' | ⨆ n, 𝓕_{σ n}] ,
  A₂ =ᵐ[P] P[(f * conj f) ∘ stoppedValue X σ' | ⨆ n, 𝓕_{σ n}] ,
  ```
  with `A` and `A₂` the two `limUnder`s. The squares are the reason `Φ` is asked
  for them, and `A₂ = A * conj A` almost surely, because a limit of products is
  the product of the limits.

  Third, the **identification**: `ae_eq_of_condExp_eq_of_condExp_mul_conj` of
  Milestone 9 turns the two identities into
  `f (stoppedValue X σ') =ᵐ[P] A`, and on the event `τ' ≤ t`, where
  `σ n = τ n` and `σ' = τ'`, that is the convergence that
  `isQuasiLeftContinuous_of_forall_ae_tendsto_comp` asks for, one `f ∈ Φ₀` at a
  time. The measurability of `A` costs nothing: `A` is almost everywhere a
  conditional expectation by the second move, hence strongly measurable for
  `⨆ n, 𝓕_{σ n}`, and `MemLp A 2 P` follows from the bound.

  **The identification is where `E` would enter and does not.** The other road
  at this corner is `IsSeparating.ae_eq_of_forall_condExp_eq` of
  **WeakConvergence** Milestone 1, which separates measures rather than points
  and needs no squares; it costs `[OpensMeasurableSpace E]`,
  `[MeasurableSpace.CountablySeparated E]`, a real valued class, and each member
  of the class as a bounded continuous function.
  `ae_eq_of_condExp_eq_of_condExp_mul_conj` mentions `E` nowhere — it speaks of
  `f g : Ω → 𝕂` and of nothing else — and the bound it asks for is needed for the
  integrabilities of the second move in any case. That is why
  `exists_cadlag_modification_of_isRegularizingClass` and this statement are
  twins and not cousins: both read `Φ` through a countable, bounded, continuous,
  point separating and square closed `Φ₀`, and neither reads `IsSeparating`.

  **No measurability of `X` is read anywhere**, and in particular
  `MeasureTheory.measurable_stoppedValue` is not used: the limit is taken in `𝕂`
  and not in `E`, and what has to be measurable is a scalar function, which the
  conditional expectation supplies for free.
* `tendsto_compensator_mpFamily`, the compensator of `mpFamily` as a **continuous**
  function of time at every sample point: for `g` measurable with `‖g x‖ ≤ b`, a
  progressively measurable `X` and a clock with `Clock.IsContinuousFor c`,
  ```
  Tendsto (fun s ↦ ∫ u in Clock.interval q c ⊥ s, g (X u ω) ∂q) (𝓝 t)
    (𝓝 (∫ u in Clock.interval q c ⊥ t, g (X u ω) ∂q)) .
  ```
  It is `norm_compensator_sub_le_of_isProgressive` squeezed against the shrinking
  windows, and it is continuity and not right continuity: the window between `s`
  and `t` is small on both sides. **In Lean** on 2026-09-17, fifteenth run.
* `tendsto_measureReal_interval_of_isLUB`, the mass of the window between a
  nondecreasing sequence and its least upper bound: for `s` monotone with
  `∀ n, s n ≤ T` and `IsLUB (Set.range s) T`, and a clock with
  `Clock.IsContinuousFor c`,
  `Tendsto (fun n ↦ q.real (Clock.interval q c (s n) T)) atTop (𝓝 0)`. The
  sequence converges to `T` (`tendsto_atTop_isLUB`) and the clock hypothesis is a
  statement about `𝓝 T`; `s n ≤ T` turns its `min` and `max` into the endpoints.
* `tendsto_measureReal_interval_of_forall_exists_lt`, the same conclusion from
  `Clock.IsAtomless` instead, by continuity from above: the windows decrease, and
  their intersection sits inside `{u | T ≤ u ∧ u ≤ T}`, which atomlessness
  declares null. Neither hypothesis implies the other — over a discrete index
  `Clock.IsContinuousFor` is vacuous and atomlessness may fail — and **under
  `Clock.Conv.predictable` neither is needed**, the intersection being empty.
* `isL1LeftContinuousAlongStoppingTimes_mpFamily`, the hypothesis of
  `isQuasiLeftContinuous_of_isRegularizingClass` that the clock and not the
  process discharges: for a bounded measurable `g`, a progressively measurable
  `X` and `Clock.IsContinuousFor c`, the compensator
  `C t = ∫ u in Clock.interval q c ⊥ t, g (X u) ∂q` is left continuous in `L¹`
  along stopping times. Dominated convergence over the pointwise estimate
  `‖C (min τ' t) - C (min (τ n) t)‖ ≤ b * q.real (Clock.interval q c (min (τ n) t) (min τ' t))`,
  with `q.real (Set.Iic t)` as the majorant, finite by `Clock.measure_Iic_ne_top`.
  The least upper bound is read off the stopping times and **no interchange of
  `min` with `⨆` is performed**, which is what would need the index to be a
  complete lattice. Strong measurability along stopping times is an input, since
  `𝕂` carries no `MeasurableSpace`.
* `isQuasiLeftContinuous_of_isMPSolutionFor`, the classical instance
  (Ethier–Kurtz, Theorem 4.3.12). For `A` with every `p ∈ A` carrying a
  continuous bounded `p.1` and a measurable bounded `p.2`, a countable
  `Φ₀ ⊆ Prod.fst '' A` that separates the points of `E` and whose squares lie in
  `Prod.fst '' A`, a progressively measurable and adapted `X` with càdlàg paths,
  a clock with `Clock.IsContinuousFor c`, optional sampling for the members of
  `mpFamily A Q c X` and strong measurability of the compensators along stopping
  times: `IsQuasiLeftContinuous X 𝓕 P`. Every hypothesis of the abstract theorem
  is read off the data by `isCompensatorFor_mpFamily`,
  `tendsto_compensator_mpFamily` and
  `isL1LeftContinuousAlongStoppingTimes_mpFamily`.

  **The clock is not asked to be atomless**, although Ethier–Kurtz state the
  theorem for a clock without atoms. What the `L¹` left continuity needs is that
  the windows shrink, and `Clock.IsContinuousFor` — which the compensator needs
  anyway, for its one sided limits — says exactly that along the filter a
  nondecreasing sequence converges along. The sharpness is unaffected: the clock
  of `not_isQuasiLeftContinuous_of_atom` fails `Clock.IsContinuousFor` and not
  merely `Clock.IsAtomless`, which is `AtomWitness.not_isContinuousFor_atomClock`.

  **The separating class must be countable**, as for
  `exists_cadlag_modification_of_isRegularizingClass` and for the same reason: a
  separating class gives one null set per test function and countably many of
  them may be combined, uncountably many may not. `IsSeparating` alone, which
  this statement carried until 2026-09-17, does not suffice.

  **`IsMPSolution` is replaced by `IsOptionalSamplingFor`**, and `Measurable p.2`
  is added: the first because over a general index the martingale property does
  not give optional sampling, the second because the compensator is a Bochner
  integral of `p.2 ∘ X`. **In Lean** on 2026-09-17, fifteenth run.
* `isOptionalSamplingFor_of_martingale`, the discharge of the first of those two
  hypotheses over the index `ℝ≥0`: for a martingale `Y` that is progressively
  measurable, has right continuous paths and is bounded on every bounded stretch
  of time, `IsOptionalSamplingFor Y 𝓕 P`. It is `stoppedValue_ae_eq_condExp` with
  the level chosen by the bound, since the definition quantifies over a time and
  a stopping time below it. The bound is the **local** one, one constant per
  level and not one for all time, which is what the compensator of a test process
  permits: it grows with the window. `isOptionalSamplingFor_zero` is the
  emptiness check. **In Lean** on 2026-09-17, sixteenth run.
* `isStronglyMeasurableAlongStoppingTimes_of_isStronglyProgressive`, the
  discharge of the second over `ℝ≥0` and a real codomain: a progressively
  measurable real process is strongly measurable at every stopping time for the
  σ-algebra of that stopping time. It is Mathlib's `measurable_stoppedValue`
  (`Probability/Process/Stopping.lean:1044`) followed by
  `Measurable.stronglyMeasurable`, and it is available here and not in the
  abstract theorem for the reason the docstring of
  `IsStronglyMeasurableAlongStoppingTimes` records: `RCLike 𝕂` carries a topology
  and no `MeasurableSpace`, so the `[BorelSpace β]` hypothesis of that theorem
  cannot be written down over a general `𝕂`, while over `ℝ` it can. **In Lean**
  on 2026-09-17, sixteenth run.
* `IsCadlag.comp_coe_nnreal`, the restriction of a càdlàg path on `ℝ` to a
  càdlàg path on `ℝ≥0`. The jump construction is written over `ℝ` and every
  statement of Milestones 3, 6 and 9 is indexed by `ℝ≥0`, which is the index the
  clock and the filtration carry; the crossing is not formal, since `IsCadlag` is
  a statement about the one sided neighbourhood filters. Only the restriction is
  available and only it is wanted: nothing on `[0, ∞)` recovers the negative
  times. **In Lean** on 2026-09-17, sixteenth run — and **in the roadmap
  SkorokhodSpace** since 2026-09-18, where it is the two index form of
  `IsCadlag.comp_monotone_continuous` applied to the coercion. It was proved
  twice; the copy in this file, with
  `tendsto_coe_nnreal_nhdsWithin_Ioi` and `tendsto_coe_nnreal_nhdsWithin_Iio`
  as its two halves, is gone, and the statement is imported.
* `ae_isCadlag_nnreal_jumpProcessE`, `isOptionalSamplingFor_mpFamily_jumpProcessE`
  and `isStronglyMeasurableAlongStoppingTimes_compensatorE`, the three
  hypotheses of `isQuasiLeftContinuous_of_isMPSolutionFor` read off the data of
  Milestone 4. The first is `ae_isCadlag_jumpProcessE` through
  `IsCadlag.comp_coe_nnreal`. The second spends the same four statements that
  `martingale_stoppedProcess_mpFamily_jumpProcessE` spends —
  `jumpProcessE_isMPSolution`, `isStronglyProgressive_mpFamily_jumpProcessE`,
  `tendsto_nhdsGE_mpFamily_jumpProcessE` and the local bound
  `exists_bound_mpFamily_jumpProcessE` — so it costs no hypothesis beyond the
  ones the jump construction already carries. The third rests on
  `isStronglyProgressive_compensatorE`, which says of the compensator alone what
  `isStronglyProgressive_mpFamily_jumpProcessE` says of the difference
  `f ∘ X - C`; the two proofs are the same one with the first summand deleted,
  and the deletion costs the bound on the rate, the bound on the integrand
  becoming a hypothesis instead of a consequence of `abs_jumpApply_le`. **In
  Lean** on 2026-09-17, sixteenth run.
* `isQuasiLeftContinuous_jumpProcessE`, Ethier–Kurtz 4.3.12 for the Markovian
  jump processes: over a countable state space with the discrete topology and
  measurable points, and for a measurable rate with `0 < lam ≤ L`, the local jump
  process is quasi-left-continuous. Every hypothesis of
  `isQuasiLeftContinuous_of_isMPSolutionFor` is read off the data of Milestone 4.
  The separating class is the point indicators
  (`mem_image_fst_jumpOperator_indicator`): countable because `E` is, idempotent
  so that `hsq` is about them and not about a larger class, separating because a
  point is determined by its own indicator, and bounded by `1` — which is what
  makes them usable where a general test function over an infinite `E` is not.
  They are written as `Set.indicator` and not as an `if`, a general state space
  carrying no `DecidableEq`. The discrete topology is what makes `Continuous p.1`
  free. `Nonempty E` is not a hypothesis: the initial distribution is a
  probability measure, so the empty state space is excluded by `measure_univ`,
  and `0 < L` is read off any state. **In Lean** on 2026-09-17, sixteenth run.
* `isQuasiLeftContinuous_poissonProcess`, the Poisson process is
  quasi-left-continuous. It is `isQuasiLeftContinuous_jumpProcessE` on the
  Poisson data, the rate being the constant `1`, and it is the first instance of
  that theorem over an **infinite** state space: over two states the countability
  of the separating class and the boundedness of its members are free for any
  test function whatever, so an instance there cannot show that the countability
  hypothesis carries weight. Over `ℕ` the point indicators are a countable class
  inside an uncountable one, and it is they that are used. The two instances `ℕ`
  supplies are `TopologicalSpace ℕ := ⊥` and `DiscreteTopology ℕ`, so
  `Continuous p.1` stays free. **In Lean** on 2026-09-17, seventeenth run.
* `isQuasiLeftContinuous_mm1`, the M/M/1 queue is quasi-left-continuous, with
  positivity `0 < β` and bound `β + δ` from `birthDeathRate_mm1_mem` and the
  Markov property of the kernel carried as an instance hypothesis exactly as in
  `mm1_isMPSolution`. It is the instance with a **state dependent** rate, taking
  the two values `β` at the empty queue and `β + δ` elsewhere; on a constant rate
  the positivity and the bound are the same statement at every state, and an
  instance where they are not is what shows the two hypotheses of
  `isQuasiLeftContinuous_jumpProcessE` are spent separately. **In Lean** on
  2026-09-17, seventeenth run.
* `exists_bound_mpFamily_jumpProcessE`, the local bound of a test process of the
  local jump problem, `C + 2LC·j` on `[0, j]` with `C` a bound for the test
  function and `L` one for the rate. It is the third hypothesis of
  `martingale_stoppedProcess` and the fourth of
  `isOptionalSamplingFor_of_martingale`, and both spend it. Nothing is assumed
  about the state space: the two positivity facts the estimate needs, `0 ≤ L` and
  `0 ≤ C`, are read off the sample point, whose first coordinate is a chain of
  states, so the empty state space is not a case to be excluded and no measure is
  needed to produce a point. **In Lean** on 2026-09-17, sixteenth run.
* `not_isQuasiLeftContinuous_of_not_ae_tendsto`, the contrapositive of
  `IsQuasiLeftContinuous.ae_eq_leftLim` and the half of the counterexample that
  is independent of the martingale problem: for a nondecreasing `s : ℕ → ι` with
  `∀ n, s n ≤ t` and `⨆ n, s n = t`,
  `¬ (∀ᵐ ω ∂P, Tendsto (fun n ↦ X (s n) ω) atTop (𝓝 (X t ω)))` implies
  `¬ IsQuasiLeftContinuous X 𝓕 P`. The constant stopping times `τ n = s n` are
  what the definition is tested on, so no left limit has to exist and neither
  `T2Space E` nor a topology on the index beyond the order one enters. It leaves
  `not_isQuasiLeftContinuous_of_atom` with the construction of the solution and
  nothing else.
* `not_isQuasiLeftContinuous_of_atom`, the sharpness, as a named example and not
  as a remark. Atomlessness is not a convenience of the proof, and it is not a
  hypothesis of `exists_cadlag_modification_of_isRegularizingClass`, which holds
  for every clock: an atom of `q` at a `u` that is approachable from the left is
  a fixed time of discontinuity. Approachable from the left is a hypothesis of
  the statement, `∃ s : ℕ → ι, StrictMono s ∧ (∀ n, s n < u) ∧ Tendsto s atTop
  (𝓝 u)`; at `u = ⊥` the example does not exist, because there is no sequence
  `s n ↑ u` and quasi-left-continuity asks nothing there. The conclusion carries
  `¬ Q.IsContinuousFor c` beside `Q.q {u} ≠ 0`, and that is the conjunct that
  makes the delimitation exact, since atomlessness is not a hypothesis of
  `isQuasiLeftContinuous_of_isMPSolutionFor` and shrinking windows are. It also
  carries `IsProbabilityMeasure P`, the bounds and the continuity of `hA`,
  `IsSeparating (Prod.fst '' A)` and the almost sure càdlàg paths — because
  without them the example is empty: for `A = ∅` the family `mpFamily A Q c X`
  is empty, `IsMPSolution` holds of every measure, and any process that fails
  quasi-left-continuity settles the statement while saying nothing about atoms.
  `IsSeparating (Prod.fst '' A)` is what forces `A ≠ ∅`, since on `Bool` the
  empty class does not separate `Measure.dirac true` from `Measure.dirac false`.
  The predicate is `MeasureTheory.IsSeparating` of **WeakConvergence**,
  Milestone 1, read at `𝕂 = ℝ`; this roadmap defines no separating class of its
  own, and `isSeparating_coinClass` below is an instance of that one.
  The witness is built in the namespace `AtomWitness`: `coinMeasure`, the fair
  coin `2⁻¹ • (Measure.dirac true + Measure.dirac false)` on `Bool` with
  `coinMeasure {true} = 2⁻¹`; `atomClock u`, the clock whose index σ-algebra is
  `⊤` and whose measure is `Measure.dirac u`, with
  `atomClock_apply_singleton : (atomClock u).q {u} = 1`, so that the atom is
  there and every down-set is measurable for free, together with
  `not_isAtomless_atomClock : ¬ (atomClock u).IsAtomless`, which says that the
  example is an example *of an atom*, as its name claims — `measure_mono` from
  the singleton into the degenerate interval `{v | u ≤ v ∧ v ≤ u}` — and
  `not_isContinuousFor_atomClock : ¬ (atomClock u).IsContinuousFor
  Clock.Conv.optional`, which is what binds the sharpness to the hypothesis it is
  sharp against: without it the example might satisfy every hypothesis of
  `isQuasiLeftContinuous_of_isMPSolutionFor` and contradict that theorem instead
  of delimiting it. Below `u` the window `Set.Iic u \ Set.Iic s` still contains
  the atom, so the function the clock hypothesis asks to vanish is constantly `1`
  along a sequence increasing to `u`;
  `coinProcess u t ω = if u ≤ t then ω else false`,
  the path over `Ω = E = Bool`, where the coin is both the sample point and the
  state; `isCadlag_coinProcess`, which holds for every `u` and every `ω`
  because the path is locally constant on either side of `u`; and
  `not_isQuasiLeftContinuous_coinProcess`, which holds for **every** filtration,
  the constant stopping times of `not_isQuasiLeftContinuous_of_not_ae_tendsto`
  being stopping times for all of them. The operator is `coinClass`, the
  singleton of `coinPair = (fun b ↦ if b then 1 else 0, fun _ ↦ 2⁻¹)`, and
  `isSeparating_coinClass` is `IsSeparating (Prod.fst '' coinClass)`: a single
  indicator separates the probability measures on `Bool`, since it pins the mass
  of `{true}` and the total mass pins the rest. `coinFiltration u` is `⊥` below
  `u` and the whole σ-algebra from `u` on, and `isMPSolution_coinProcess` is the
  martingale property of
  `mpFamily coinClass (atomClock u) Clock.Conv.optional (coinProcess u)` under
  `coinMeasure`, for every `u` with `¬ u ≤ ⊥`. It rests on two computations and
  no theory: `integral_coinPair_snd`, that the compensator
  `∫ s in Clock.interval q .optional ⊥ t, coinPair.2 (X s) ∂q` is `2⁻¹` for
  `u ≤ t` and `0` otherwise — `setIntegral_const` against `Measure.dirac u`,
  whose mass on the compensating interval is `atomClock_real_of_mem` or
  `atomClock_real_of_notMem` according as `u ≤ t` — and `integral_coinMeasure`,
  that the mean against the coin is the average of the two values. So the
  process is `0` strictly before `u` and `(if ω then 1 else 0) - 2⁻¹` from `u`
  on, which is centred: the constant `2⁻¹` in `coinPair.2` is not a choice, it
  is the balance `p.1 true - p.1 false = p.2 true + p.2 false` that the
  martingale property across `u` demands. `integrable_bool` is the side
  condition throughout, every real function on `Bool` being bounded and
  measurable. The convention is not a choice either: in
  `Clock.Conv.predictable` the interval is `Set.Iio t`, the atom is charged only
  strictly after `u`, and the martingale property at `t = u` reads
  `2⁻¹ * (p.1 true + p.1 false) = p.1 false`, that is `p.1 true = p.1 false`, so
  every predictable version of the witness has a constant `p.1` and no
  separating one exists. Under `Clock.IsAtomless` the two conventions agree, so
  one of them suffices for the sharpness. On `E = Bool` with
  `q = Measure.dirac u` there is therefore a solution that flips a fair coin at
  `u` and is constant on either side of it, and for `s n ↑ u` its paths have
  `X (s n) → X (u-) ≠ X u` on an event of probability one half. The
  existence of a càdlàg modification and quasi-left-continuity therefore
  separate exactly at the atoms of the clock, and the example is what makes the
  separation checkable.

**Acceptance examples.**

* **A submartingale with no càdlàg modification, and the exact obstruction.**
  `ι = Set.Ici (0:ℝ)`, `Y t = Set.indicator (Set.Ioi 1) 1` deterministic. It is
  a submartingale, its paths are already càdlàg, and `t ↦ 𝔼[Y t]` is **not**
  right continuous at `1`. Replacing it by `Y' t = Set.indicator (Set.Ici 1) 1`
  gives the same left limits and a right continuous mean. So
  `Submartingale.cadlagModif_ae_eq_iff_continuousWithinAt_integral` must
  distinguish the two: `cadlagModif Y` is `Y'`, which is not a modification of
  `Y` at `t = 1`, while it is one of `Y'`. This is the pair that shows the
  criterion is an equivalence and not a technical hypothesis, and it is why the
  martingale case (`Martingale.cadlagModif_ae_eq`) is automatic — the mean is
  constant there.
* **Optional sampling needs the boundedness, or the two hypotheses.**
  `ι = Set.Ici (0:ℝ)`, `Y` a standard Brownian motion,
  `τ = inf {t | Y t = 1}`, which is almost surely finite and not bounded.
  Then `𝔼[stoppedValue Y τ] = 1 ≠ 0 = 𝔼[Y 0]`, so
  `Submartingale.stoppedValue_min_le_condExp` for a bounded `τ` does not extend
  by itself; the uniform integrability hypothesis
  `Tendsto (fun T ↦ ∫ ω in {ω | T < τ ω}, ‖Y T ω‖ ∂P) atTop (𝓝 0)` of the second
  item fails on it, and must therefore be carried. `τ ⊓ T` for fixed `T` is the
  bounded instance on which the first item does apply.
* **Doob's `Lᵖ` inequality, computed.** For `Y` a standard Brownian motion and
  `r = 2`, `Martingale.lintegral_biSup_enorm_rpow_le` must give
  `∫⁻ ω, (⨆ t ∈ Set.Iic T, ‖Y t ω‖ₑ) ^ 2 ≤ 4 * ∫⁻ ω, ‖Y T ω‖ₑ ^ 2 = 4 * T`, the
  constant being `(r/(r-1))^r = 4`. The measurability of the supremum here is
  exactly the reduction to `Set.Iic T ∩ ℚ` that the milestone states as a lemma
  of its own; without right continuity the supremum over an uncountable set need
  not be measurable, which is why that reduction is an item and not a step. The
  quantities are lower integrals and not `eLpNorm`s, for the reason given in the
  milestone: a real valued encoding of the window supremum reads `0` where the
  path escapes. That the escape set is null here is
  `Martingale.ae_biSup_enorm_lt_top` and not an assumption.
* **Doob's maximal inequality, computed, and the constant is the point.** For
  the same `Y`, `Martingale.measure_iSup_norm_le` must give
  `ε * P {ω | ε ≤ ⨆ t ∈ Set.Iic T, ‖Y t ω‖ₑ} ≤ 𝔼|Y T|`, with `1` and not `2` in
  front of the right hand side. The two sided window bound
  `Submartingale.mul_measReal_le_biSup_enorm_le` gives `2 𝔼|Y T| - 𝔼[Y 0]` on
  these data, which is `2 𝔼|Y T|`; the example is what distinguishes the two
  routes, and it fails for the two sided one.
* **The coin at an atom, which separates the two theorems of this milestone.**
  `E = Bool`, `q = Measure.dirac 1`, and the solution that flips a fair coin at
  time `1` and is constant on either side. It **has** a càdlàg modification —
  `exists_cadlag_modification_of_isRegularizingClass` asks nothing of the clock
  — and it is **not** quasi-left-continuous, since `X (s n) → X 1⁻ ≠ X 1` with
  probability `1/2` for any `s n ↑ 1`. This is
  `not_isQuasiLeftContinuous_of_atom`, and the same process with `q = volume` is
  quasi-left-continuous by `isQuasiLeftContinuous_of_isMPSolutionFor`. The pair
  fixes where the regularity of the clock is a hypothesis and where it is not,
  and it is `Clock.IsContinuousFor` and not `Clock.IsAtomless` that the positive
  theorem asks for — `lebesgueClock_isContinuousFor_optional` gives it for
  `q = volume`, `not_isContinuousFor_atomClock` denies it for the dirac.

  The positive half is `isQuasiLeftContinuous_flip`: the two state jump process
  of Milestone 4 over `lebesgueClock` is quasi-left-continuous, every hypothesis
  discharged on data. The paths it is applied to are **the paths of the process
  itself** and not of a modification — a step path is càdlàg to begin with, so
  `exists_cadlag_modification_flip` is not an input here. It is an instance of
  `isQuasiLeftContinuous_jumpProcessE`, which says the same over **any** countable
  state space and is therefore a statement about the Markovian jump processes and
  not about one example: the Poisson process and M/M/1 of Milestone 4 are covered
  by it, both having bounded rate. It is kept as a named statement because it is
  one half of a *pair* — the general theorem says nothing about the clock beyond
  `Clock.IsContinuousFor`, and it is on precisely these data that the other clock
  makes the conclusion fail. **In Lean** on 2026-09-17, sixteenth run.
* **Cutting down to an open subset.** `E = ℝ`, `U = Set.Ioo (-1) 1`, and the
  bump sequence `f n x = min 1 (n * Metric.infDist x Uᶜ)` of Milestone 2 with
  `g n = 0`. For a solution started inside `U` whose paths do not leave it,
  `IsMPSolutionFor.ae_forall_mem_of_tendsto` must conclude
  `∀ᵐ ω ∂P, ∀ t, X t ω ∈ U` and càdlàg-ness as a `U`-valued map. For a Brownian
  motion, which does leave `U`, the hypothesis `f n x → Set.indicator U 1 x`
  still holds while the conclusion fails — because `(f n, 0)` is not in `A`
  there, the compensator of a bump function under `f''/2` not being `0`. The
  contrast is what shows the hypothesis is about `A` and not about the path.

## Milestone 10: the abstract convergence theorem

Fix `[Preorder ι]`, a measurable path space `F`, and processes `X n` on spaces
`(Ω n, 𝓕 n, P n)` with paths in `F`.

* **`P`-continuity at `X` is written `P {ω | ContinuousAt ψ (X ω)} = 1`** and
  carries no definition of its own. The manuscript's `def:Pcont` asks for a Borel
  `C` with `P {X ∈ C} = 1` such that `ψ (α m) → ψ α` whenever `α m → α` in `F`
  with `α ∈ C`: the approximating points range over the whole of `F` and only the
  limit is confined to `C`, so the condition is sequential continuity at each
  point of `C`. Over a first countable `F` that is `ContinuousAt ψ` at each point
  of `C`, and the certifying set adds nothing, because the continuity set
  `{x | ContinuousAt ψ x}` is itself Borel — `measurableSet_of_continuousAt`,
  `MeasureTheory/Constructions/BorelSpace/Basic.lean` — and is therefore the
  largest `C` that any certificate can name.
  **Confining the approximating points to `C` as well is a different condition,
  and a false one.** `F = ℝ`, `C = {0}`, `ψ = Set.indicator {0} 1`, `X ≡ 0` and
  `X n ≡ 1/n`: the only sequences inside `C` are eventually constant, so `ψ`
  would be certified; `X n → X` in distribution; and `ψ (X n) = 0` does not
  converge to `ψ (X) = 1`. The condition has to be read off the continuity set of
  `ψ`, not off a set the approximating paths are asked to stay in.
  `ContinuousAt` rather than the sequential form is what the statements below
  carry, since no first countability of `F` is assumed and the portmanteau
  argument underneath reads the topological continuity set.
* `mpSolution_of_tendsto`: assume `X` and every `X n` measurable, every member of
  every `𝓩° r` bounded and measurable, `𝓧` canonical for `X` with determining set
  `𝓩°`, and that for every `Y ∈ 𝓧` with canonical version `Y°` and every `t ∈ D`:
  every `Y° r (X n)` with `r ∈ D ∩ Iic t` is integrable; (a) the real random
  variables `Y° r (X n)` for `r ∈ D ∩ Iic t` converge in distribution to their
  counterparts under `X`, and so does `(Y° t - Y° s) * Z (X n)` for every
  `s ∈ D ∩ Iic t` and `Z ∈ 𝓩° s`; (b) `{Y° r (X n) | r ∈ D ∩ Iic t, n}` is
  uniformly integrable; (c) `𝔼^{P n}[(Y° t (X n) - Y° s (X n)) * Z (X n)] → 0`.
  Then `P[Y t | 𝓕 s] =ᵐ Y s` for all `s ≤ t` in `D`; and when `ι` carries the
  order topology and is first countable, every index is either in `D` or
  approached from the right inside `D`, and every `Y ∈ 𝓧` is right continuous,
  `P` is a solution. That last step is
  `isMPSolution_of_forall_condExp_eq_of_dense`, and the condition on `D` is its
  hypothesis `hDr` and not density — see there for why density is not enough.
  State hypothesis (a) in this form. It carries no topology on `F`: it is a
  statement about finitely many real random variables, and the versions where
  `F` is metrizable and the coordinates are continuous are corollaries.
  **In Lean** on 2026-09-17, nineteenth run.
  **Items (a) and (b) are quantified outside `∀ Z ∈ 𝓩° s`, and that is forced.**
  They mention `Y°` and not `Z`, and they are what produces `Integrable (Y r) P`,
  which `IsDetermining` asks for whether or not `𝓩° s` has a member; an empty
  `𝓩° s` makes the orthogonality hypothesis of `IsDetermining` vacuous but leaves
  its integrability hypothesis standing, so an integrability hypothesis hidden
  under `∀ Z` would have no source there.
  **Uniform integrability is written by the tails**
  `∫ max (‖Y° r (X n)‖ - c) 0 ≤ ε` and not by the truncated integrals
  `∫_{c ≤ ‖Y° r (X n)‖} ‖Y° r (X n)‖ ≤ ε`. The tail form is implied by the other,
  since `max (‖x‖ - c) 0 ≤ {y | c ≤ ‖y‖}.indicator ‖·‖ x` pointwise, so it is the
  weaker hypothesis; and it asks no measurability of the sublevel sets. It is
  also what the proof reads.
* `radialTrunc`, the bounded continuous approximation to the identity that the
  previous item runs on: `radialTrunc c x = (c / max c ‖x‖) • x`, the retraction
  of a normed space onto the closed ball of radius `c`, with
  `‖x - radialTrunc c x‖ ≤ max (‖x‖ - c) 0`. Convergence in distribution carries
  the integrals of **bounded** continuous functions, and the integrals that have
  to converge are those of the variables themselves; the truncation is the
  bridge, and the tail is the error it commits. Written without a case
  distinction so that continuity is `Continuous.div` and the denominator, bounded
  below by `c`, is never zero. **In Lean** on 2026-09-17, nineteenth run, with
  `integrable_tail`, `integral_tail_antitone` and
  `abs_integral_sub_integral_radialTrunc_le`.
* `integral_eq_zero_of_tendstoInDistribution`, the analytic core: for variables
  on different probability spaces converging in distribution, uniformly
  integrable by the tails, integrable on each space and with vanishing
  integrals, the limit has vanishing integral. The `𝕂`-valued statement is
  obtained by testing against `RCLike.reCLM` and `RCLike.imCLM`, since the test
  functions carried by convergence in distribution are **real**; the truncation
  level is chosen for the sequence by the uniform integrability and for the
  limit by `tendsto_integral_tail`, and the larger of the two serves both sides.
  Mathlib's `MeasureTheory.UnifIntegrable` is a predicate about one fixed
  measure and does not apply across a sequence of spaces. **In Lean** on
  2026-09-17, nineteenth run; restated on convergence in distribution in the
  twentieth.
* `integrable_of_tendstoInDistribution`: a family with a uniform `L¹` bound has
  an integrable limit. This is the half of (b) that is spent before any
  martingale identity, and nothing else in the statement makes `Y s` and `Y t`
  integrable. The bound travels by the bounded continuous truncations
  `min ‖x‖ M`, and the passage `M → ∞` is monotone convergence. Measurability of
  the limit is not a hypothesis: it is the field `aemeasurable_limit` of
  `MeasureTheory.TendstoInDistribution`, which over `𝕂` upgrades to
  `AEStronglyMeasurable` by `AEMeasurable.aestronglyMeasurable`. **In Lean** on
  2026-09-17, nineteenth run; restated on convergence in distribution in the
  twentieth.
* `MeasureTheory.TendstoInDistribution.tendsto_integral_comp`: convergence in
  distribution carries the integrals of bounded continuous test functions, for
  variables living on a family of spaces. This is the whole interface through
  which the theorem above reads its convergence hypothesis, and it is
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
  (`MeasureTheory/Measure/ProbabilityMeasure.lean`) composed with `integral_map`,
  whose measurability side condition is the field `forall_aemeasurable` of the
  structure. It belongs in Mathlib beside the structure. **In Lean** on
  2026-09-17, twentieth run.
  **Convergence in distribution is Mathlib's, not this roadmap's.** The file
  carried its own predicate until the twentieth run of 2026-09-17, on the ground
  that `MeasureTheory.TendstoInDistribution` was the same notion for one fixed
  space. That ground was false: the structure is declared over a family
  `{Ω : ι → Type*}` with `{μ : (i : ι) → Measure (Ω i)}` and
  `[∀ i, IsProbabilityMeasure (μ i)]`
  (`MeasureTheory/Function/ConvergenceInDistribution.lean`, the variable block
  above the structure), so the family case is the stated case there. Using it
  costs a `MeasurableSpace` with `OpensMeasurableSpace` on the value space and
  probability measures on the approximating spaces; over `𝕂` both hold by
  instance (`RCLike.measurableSpace`, `RCLike.borelSpace`,
  `MeasureTheory/Constructions/BorelSpace/Complex.lean`), and the approximating
  measures were already asked to be probability measures.
* `tendsto_integral_tail`: the tails of a single integrable function vanish. It
  is what lets the limit carry the same truncation level as the sequence, and it
  is dominated convergence. **In Lean** on 2026-09-17, nineteenth run.
* `mpSolution_of_tendsto_of_pContinuous`: the corollary in which (a) is replaced
  by `X n → X` in distribution on `F` together with
  `P {ω | ContinuousAt (Y° r) (X ω)} = 1` for `r ∈ D ∩ Iic t` and
  `P {ω | ContinuousAt ((Y° t - Y° s) * Z) (X ω)} = 1` for `s ∈ D ∩ Iic t` and
  `Z ∈ 𝓩° s`. It is `MeasureTheory.TendstoInDistribution.continuousAt_comp` of
  the roadmap **WeakConvergence** applied twice and nothing else.
  **In Lean** on 2026-09-17, twenty-first run.
  **`F` is neither separable nor metric.** What the continuous mapping theorem
  reads on the path space is `HasOuterApproxClosed F` on top of the
  `OpensMeasurableSpace F` that `MeasureTheory.TendstoInDistribution` asks for
  anyway. Every pseudo-metrizable space has it (`instHasOuterApproxClosed`,
  `MeasureTheory/Measure/HasOuterApproxClosed.lean`), so the separable metric
  path space of the manuscript is an instance of this statement and not a
  hypothesis of it.
  **The continuity is asked of the products and not of the factors**, which is
  the weaker hypothesis: continuity at a point is stable under differences and
  products, so continuity of `Y° t`, `Y° s` and `Z` at `X ω` gives continuity of
  `(Y° t - Y° s) * Z` there, and the converse fails. It is also the product that
  the proof composes.
* `IsDetermining.comp_fst`: a determining set read on an augmented path space
  `F × G`, through `Z ∘ Prod.fst`. The two statements have the same content,
  since `(Z ∘ Prod.fst) (X ω, γ (X ω)) = Z (X ω)`, and the proof is the image
  being unfolded. **In Lean** on 2026-09-17, twenty-first run.
* `mpSolution_of_tendsto_augmented`: the manuscript's `thm:absconvaug`. For a
  measurable `γ : F → G`, the augmentation `x ↦ (x, γ x)` carries the readings
  `γ` along as a second coordinate, and the statement is the previous one on
  `F × G`: `X n → X` in distribution **jointly with** `γ (X n) → γ (X)`, and the
  `P`-continuity asked of functionals on `F × G`. A functional discontinuous only
  because it reads the path at prescribed places becomes continuous there. In the
  instance that motivates it (`prop:atomaug`), `G = E^A` for the countable set
  `A` of atoms of the clock and `γ ω = (ω a)_{a ∈ A}`. **In Lean** on 2026-09-17,
  twenty-first run.
  **There is no `Y°` on `F` among the hypotheses.** The manuscript asks for Borel
  `Ŷ°` on the augmented space with `Ŷ° ∘ γ̂ = Y°`; the formalisation takes the
  canonical version on `F × G` from the start, `Y t ω = Y° t (X ω, γ (X ω))`,
  which is the same requirement with the detour through `F` removed.
  **The augmented convergence hypothesis is strictly stronger than the plain
  one, and that is the trade.** It gives back `X n → X` in distribution by
  `MeasureTheory.TendstoInDistribution.continuous_comp continuous_fst`
  (`MeasureTheory/Function/ConvergenceInDistribution.lean`), at the cost of
  `BorelSpace F`; the converse fails, and `ex:atomicdiscontinuity` is the
  witness — `ω n = indicator (Set.Ici (1 + 1/n)) 1` converges to
  `indicator (Set.Ici 1) 1` in `J₁` while the values at `1` converge to the wrong
  limit.
  **`OpensMeasurableSpace` and `HasOuterApproxClosed` are asked of the product**
  and not of the factors, which is again the weaker hypothesis. The routes from
  the factors carry side conditions the statement does not read:
  `Prod.opensMeasurableSpace` (`MeasureTheory/Constructions/BorelSpace/Basic.lean`)
  needs `SecondCountableTopologyEither`, and the only instance of
  `HasOuterApproxClosed` is `instHasOuterApproxClosed` for pseudo-metrizable
  spaces, so obtaining it on `F × G` means metrizing both factors.
* `integral_tail_le_of_tendstoInDistribution`: a uniform tail bound survives the
  passage to the limit in distribution. The tail `max (‖x‖ - c) 0` is continuous
  but **unbounded**, so convergence in distribution does not carry its integral;
  the bounded truncations `min (max (‖x‖ - c) 0) M` do, each is dominated by the
  tail on every space, and `M → ∞` on the limit side is dominated convergence
  against the tail of the limit. The same device as in
  `integrable_of_tendstoInDistribution`, one level up. **In Lean** on 2026-09-17,
  twenty-first run.
* `unifIntegrable_tail_of_tendstoInDistribution`: uniform integrability of the
  limit family under `P`, in the tail form the milestone carries, with the
  integrability of the limits as part of the conclusion. It is what makes the
  passage from `D` to the whole index work: the family that has to be uniformly
  integrable there is the **limit** family under `P` and not the approximating
  one. **In Lean** on 2026-09-17, twenty-first run.
  **The truncation level is the same on both sides.** It is chosen by the
  hypothesis for the approximating family and serves the limit unchanged, which
  is why the statement is an implication between two clauses of one shape rather
  than a statement about enlarging a level.
  **Integrability of the limits is not a hypothesis.** The uniform bound at
  `ε = 1` gives `∫ ‖ξ r n‖ ≤ c₁ + 1` uniformly in `n` and `r`, and
  `integrable_of_tendstoInDistribution` turns that into integrability of each
  limit — the computation `mpSolution_of_tendsto` performs inline.

**Acceptance examples.**

* **The rescaled Markov chain of the manuscript's `ex:invariance`.**
  `E = ℝ^d`, `q n = (1/n) * ∑ k ≥ 1, δ (k/n)` with the optional convention,
  `X n t = Ξ n ⌊n * t⌋` for a chain with one step kernel `P n`, and
  `Y n t = f (Ξ n ⌊n t⌋) - ∑ j < ⌊n t⌋, (P n f - f) (Ξ n j)` — the Doob
  decomposition read along the embedded grid; (a) and (b) are the convergence and
  uniform integrability of finitely many real variables. The conclusion is that
  the limit solves the martingale problem for the limiting operator. This is the
  invariance principle, and it instantiates every hypothesis of the milestone at
  once.
  **Hypothesis (c) is not the exact martingale property alone, and the
  difference is where the example does its work.** The canonical version `Y°`
  that (c) speaks of is one function on one path space, the same for every `n`;
  the exact martingale `Y n` is a different function for every `n`, because
  `P n` and the grid are. So (c) splits in two, and only the first summand is
  free: `𝔼[(Y n t - Y n s) * Z (X n)] = 0` by the martingale identity, and
  `𝔼[‖(Y° t - Y° s) (X n) - (Y n t - Y n s)‖] → 0`, which is the manuscript's
  `(K3)`, the convergence `n (P n f - f) → A f` of the rescaled generators.
  `tendsto_integral_mul_of_martingale` is the statement in which the two meet
  and `tendsto_integral_mul_rescaledChain` is it on the chain. **In Lean** on
  2026-09-17, twenty-third run.
* `integral_mul_eq_of_condExp_eq` and `integral_sub_mul_eq_zero_of_condExp_eq`:
  a bounded variable of the past may be pulled through a conditional expectation
  under the integral, and hence a martingale increment is orthogonal to every
  bounded variable of its past. This is the engine of (c). It is stated on the
  conditional expectation identity `μ[f | m'] =ᵐ g` and not on `Martingale`,
  because that is what is used — the index set, the order and the adaptedness of
  the family play no part, only the single identity at the pair of times in
  question. The pull-out is
  `MeasureTheory.condExp_smul_of_aestronglyMeasurable_left`
  (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean`); the weight is
  real and the variable `𝕂`-valued, so it is the `smul` form and not the `mul`
  form that reads. **In Lean** on 2026-09-17, twenty-third run.
* `chainCompensated` and `martingale_chainCompensated`, the Doob decomposition
  `f (Ξ n) - ∑ j < n, (P f - f) (Ξ j)` along a chain and the proof that it is a
  martingale. It is `MeasureTheory.martingale_nat` on the one step identity.
  **In Lean** on 2026-09-17, twenty-third run.
  **It is a formula and not `MeasureTheory.martingalePart`**, which is the same
  object built out of `μ[· | 𝓖 j]` and therefore determined only almost
  everywhere. `StronglyAdapted` is not an almost sure notion and the martingale
  that (c) reads has to be one function and not a class, so the compensator is
  the kernel's increment `P f - f`.
  **The Markov property is asked for in the form in which it is used** — the
  conditional expectation identity `μ[f (Ξ (n+1)) | 𝓖 n] =ᵐ (P f) (Ξ n)` — and
  not through a `ProbabilityTheory.Kernel`. That is the weaker hypothesis: a
  chain given by a kernel supplies it, and so does a chain that is Markov only
  along the test function `f`, which is all the proof reads. The state space
  carries no structure at all, not a measurable space and not a topology.
  **Integrability of a martingale is a hypothesis and not a consequence.**
  Mathlib's `MeasureTheory.Martingale` is `StronglyAdapted` together with the
  conditional expectation identity and carries no integrability — unlike
  `Submartingale` and `Supermartingale`, which do
  (`Probability/Martingale/Basic.lean`). A theorem that integrates a martingale
  has to ask for it.
* `gridPath`, `measurable_gridPath`, `coordFiltration`, `comap_gridPath_le` and
  `measurable_comp_gridPath`: the chain read along the grid of mesh `1/r` as a
  path in the raw space `ℝ≥0 → E`, its measurability, and the statement that a
  functional of the path before `s` becomes, on the grid path, a variable of the
  chain before `⌊r s⌋`. The last is `MeasurableSpace.comap_iSup` twice and
  `MeasurableSpace.comap_comp` once, and the one thing it needs beyond
  bookkeeping is `0 ≤ r`, without which `Nat.floor_mono` does not carry `u ≤ s`
  across the multiplication. **In Lean** on 2026-09-17, twenty-third run.
* `tendsto_integral_mul_rescaledChain_natural`, the acceptance example
  assembled: hypothesis (c) for the rescaled chain over its **own** natural
  filtration, with the weight a functional of the path before `s` read on the
  grid path. Every hypothesis about measurability is discharged; what is carried
  is what the manuscript carries — the Markov property, the integrability of the
  test function along the chain, the bound on the weight, and `(K3)`.
  **In Lean** on 2026-09-17, twenty-third run.
  **The path space is `ℝ≥0 → E` with the product σ-algebra and nothing else** —
  no topology, no metric, no separability, and `E` a bare measurable space. That
  is this milestone's own acceptance test for hypothesis (a), "`F` a bare
  measurable space", carried out on (c).
* `coordChain`, `measurable_coordChain`, `indep_comap_coordChain` and
  `condExp_coordChain`, the **i.i.d. chain** — the coordinates `Ξ i ω = ω i` of
  an infinite product measure — and its Markov property in the form
  `martingale_chainCompensated` reads. The one step kernel sends every state to
  `ν`, so the compensator is the *constant* `∫ f dν`; the conditional
  expectation identity is `MeasureTheory.condExp_indep_eq` on the independence
  of a coordinate from its past, which is `ProbabilityTheory.indep_iSup_of_disjoint`
  on the disjoint index sets `{i + 1}` and `Set.Iic i` fed by
  `ProbabilityTheory.iIndepFun_infinitePi` at the identity. **In Lean** on
  2026-09-17, twenty-fourth run.
  **The passage from `iIndepFun` to `iIndep` of the comap σ-algebras is
  definitional** — Mathlib defines the first as the second
  (`Probability/Independence/Kernel/IndepFun.lean`) — so no bridge lemma is
  needed and none exists.
* `tendsto_integral_mul_coordChain`, the **emptiness probe** of the acceptance
  example: the nine hypotheses of `tendsto_integral_mul_rescaledChain_natural`
  discharged together on the i.i.d. chain, with a bounded measurable test
  function, a bounded measurable weight read at the coordinate at time `0` — a
  functional of the path before `s` for every `s`, since `0 ≤ s` in `ℝ≥0` — and
  `(K3)` discharged by taking the canonical increment to *be* the martingale
  increment. **In Lean** on 2026-09-17, twenty-fourth run.
  **What it establishes is joint satisfiability and not a hard limit.** With
  `(K3)` exact the conclusion is a limit of zeros; that is the honest reading,
  and it is the reading a probe is for. A statement over hypotheses that cannot
  hold at once is true and empty, and this branch has met that twice — `Shift`
  was assumed ten times before it had an inhabitant, and `hint` of the path
  dependent case turned out to be unsatisfiable.
* `tendsto_integral_mul_coordChain_perturbed`, the same probe with a **nonzero**
  `(K3)`: the canonical increment differs from the martingale increment by the
  constant `(n + 1)⁻¹`, so the `L¹` distance is `(n + 1)⁻¹` and not `0`, and the
  conclusion is a limit and not a sequence of zeros. **In Lean** on 2026-09-17,
  twenty-fourth run.
  **This is what makes the theorem do work rather than merely hold.** With
  `(K3)` exact the estimate `‖∫ (G n - H n) · W n‖ ≤ b · ∫ ‖G n - H n‖` inside
  `tendsto_integral_mul_of_integral_eq_zero` is `0 ≤ 0` and the bound `b` on the
  weight is never read; here it is. A probe that only shows the hypotheses
  consistent is weaker than one that also shows the estimate carrying something.
* `measure_chainCompensated_ne_pos` and
  `measure_chainCompensated_ne_pos_of_two_atoms`, the statements that keep the
  probe from being about a degenerate object: the compensated chain is **not**
  almost surely constant. Its increment from `0` to `1` is `f (ω 1) - ∫ f dν`,
  so it is nonzero on the cylinder over any set on which `f` avoids its own
  mean, and two atoms carrying different values of `f` suffice because the mean
  cannot equal both. **In Lean** on 2026-09-17, twenty-fourth run.
  **This is what a deterministic witness would not give.** A constant or
  deterministic chain satisfies the nine hypotheses as well, and proves nothing:
  its Doob decomposition is constant, the martingale identity of (c) is `0 = 0`,
  and the orthogonality the example is about is never used. The probe has to be
  random to be a probe.
  **The target set is not required to be measurable**: a measure in Mathlib is
  monotone on arbitrary sets, so `measure_mono` from the cylinder suffices.
* `integral_coinPair_coinMeasure`, `norm_coinPair_le`,
  `tendsto_integral_mul_coordChain_coin` and
  `measure_chainCompensated_ne_pos_coin`, the probe **on data**: the fair coin
  of `AtomWitness`, the indicator of `true`, and the mean `2⁻¹`, so that the
  approximating martingale is the centred simple random walk read along the
  grid. Neither statement carries a hypothesis of any kind. **In Lean** on
  2026-09-17, twenty-fourth run.
  **The coin is reused and not rebuilt.** `AtomWitness.coinMeasure` and
  `AtomWitness.integral_coinMeasure` were built for the counterexample of
  Milestone 9 and serve here unchanged; the two witnesses of this file — the one
  that fails quasi-left-continuity and the one that inhabits the convergence
  theorem — sit on the same coin.
* `naturalFiltration_eq_comap_block`: the natural filtration of a chain is the
  comap of the block of its first `n + 1` coordinates. Both sides are
  `⨆ j ≤ n, comap (Ξ j)`; the right-hand one because the product σ-algebra of the
  block is the supremum of the comaps of its evaluations, and
  `MeasurableSpace.comap_iSup` carries the comap through. No measure, no kernel
  and no topology. **In Lean** on 2026-09-18, first run.
  It is the bridge between a conditional expectation proved over the block
  σ-algebra a disintegration produces and one read over the filtration
  hypothesis (c) is written over.
* `jumpChain`, `measurable_jumpChain`, `condExp_jumpChain`: the **embedded jump
  chain** of Milestone 4, read as a process on the sample space of the jump
  construction, and its Markov property in the shape
  `martingale_chainCompensated` reads it. The compensator is
  `Pf x = ∫ f d(mu x)` — a function of the state. **In Lean** on 2026-09-18,
  first run.
* `tendsto_integral_mul_jumpChain`: the nine hypotheses of
  `tendsto_integral_mul_rescaledChain_natural` discharged together on the
  embedded jump chain of an **arbitrary** Markov kernel, under `jumpMeasure mu
  nu`. `E` carries nothing but its σ-algebra; the test function and the weight
  are bounded and measurable. **In Lean** on 2026-09-18, first run.
  **This is the hypothesis `hPf` met in a shape `measurable_const` cannot
  meet.** The i.i.d. probe discharges it with a constant compensator, and a
  hypothesis that is only ever met in its trivial shape has not been met. It is
  also the join between this milestone and Milestone 4: the convergence theory
  and the only construction by hand this roadmap has.
* `measure_chainCompensated_chain_eq` and
  `measure_chainCompensated_jumpChain_eq`: **how often the compensated chain
  moves at its first step, exactly** — it is the mass the one step kernel puts
  away from its own mean, averaged over the initial law,
  `∫⁻ x, mu x {y | f y ≠ ∫ f d(mu x)} ∂nu`. The chain of the proof is
  `comp_chainKernel_map_split`, then `Measure.compProd_apply`, then
  `comp_chainKernel_map_zero` at the started measure `mu x`. **In Lean** on
  2026-09-18, first run.
  **Non-degeneracy is measured and not asserted.** The i.i.d. probe exhibits a
  set of positive measure on which the compensated chain moves; this computes
  the measure of that set for every kernel and every bounded test function, so
  the degenerate case is visible as the vanishing of a named quantity rather
  than as the failure of an argument.
* `measure_ne_integral_pos_of_two_atoms` and
  `measure_chainCompensated_jumpChain_pos`: two atoms carrying different values
  of the test function put mass away from the mean, and an initial law charging
  a set on which the kernel keeps a fixed amount of mass away from its own mean
  makes the compensated chain move with positive probability. **In Lean** on
  2026-09-18, first run.
  **The integrand never has to be shown measurable.** The lower bound is an
  indicator, so `x ↦ mu x {y | f y ≠ ∫ f d(mu x)}` — a kernel evaluated at a
  *state dependent* set — is only ever bounded below pointwise and integrated
  through `lintegral_mono`.
* `mm1ChainKernel`, `mm1AtTwo`, `mm1ChainKernel_apply_one`,
  `mm1ChainKernel_apply_zero`, `integral_mm1ChainKernel_zero`,
  `integral_mm1ChainKernel_one`, `integral_mm1ChainKernel_ne`,
  `tendsto_integral_mul_jumpChain_mm1` and
  `measure_chainCompensated_jumpChain_pos_mm1`: the probe **on data**, over the
  embedded chain of the M/M/1 queue at `β = δ = 1` started from a queue of
  length one, with the indicator of the queue length `2` as test function.
  Neither conclusion carries a hypothesis. **In Lean** on 2026-09-18, first run.
  **The compensator takes two values, and the empty queue is where they part.**
  From `0` the queue can only grow, so `mm1ChainKernel 0` is a Dirac measure and
  `Pf 0 = 0`; from `1` it goes up or down with equal probability and
  `Pf 1 = 2⁻¹`. That is `integral_mm1ChainKernel_ne`, and it is what the i.i.d.
  probe cannot supply.
  **The data is the milestone's own and not a new object.** `birthDeathKernel`
  and the M/M/1 rates are Milestone 4's acceptance example; the probe reuses
  them, as the coin probe reuses `AtomWitness.coinMeasure`.
* `tendsto_integral_mul_jumpChain_perturbed`, the jump chain probe with a
  **nonzero** `(K3)`: the canonical increment is the martingale increment
  displaced by the constant `(n + 1)⁻¹`, so the conclusion is a limit and not a
  sequence of zeros and the bound on the weight is read. Together with
  `tendsto_integral_mul_jumpChain` it leaves no hypothesis of
  `tendsto_integral_mul_rescaledChain_natural` met only in a shape that proves
  nothing: `hPf` by a compensator that reads the state, `happrox` by an
  approximation that is not an equality. **In Lean** on 2026-09-18, second run.
* **The probe reads the jump number and not the time, and the two are not the
  same.** `gridPath (jumpChain E) n` is the embedded chain at the index
  `⌊n · t⌋`, while the jump process is that same chain at the index
  `stepIndex (jumpTime lam ω.1 ω.2) t` — `jumpProcess_eq_jumpChain_stepIndex`,
  which is `rfl`. The first index is deterministic, the second random. The
  distance between them is exact and not a matter of taste, and four statements
  measure it. **In Lean** on 2026-09-18, second run.
* `jumpTime_const_mul` and `jumpProcess_const_mul_rate`: **speeding up the rate
  is a time change.** Multiplying the rate by `c` divides every jump time by
  `c`, so `jumpProcess (c · lam) t ω = jumpProcess lam (c t) ω` at every sample
  point, with no hypothesis beyond `0 < c`. The rescaling of `ex:invariance`
  applied to the jump construction is therefore **one** process read along a
  sequence of times, and the embedded chain is untouched.
  **The first of the two is unconditional and the second is not**, and the
  reason is the junk value: at `c = 0` the holding time `ξ n / 0` is `0` and so
  is `T n / 0`, so `jumpTime_const_mul` is true at `c = 0` as well, whereas
  `stepIndex_div_const` inverts an inequality and needs `0 < c`.
* `stepIndex_natCast`, `jumpTime_unit`,
  `jumpProcess_const_mul_rate_eq_gridPath` and
  `jumpProcess_eq_gridPath_unitWaiting`: **the grid path is the jump process of
  a deterministic clock.** For unit waiting times the jump times at rate `c` are
  `n / c`, the renewal count of `c t` is `⌊c t⌋` — `stepIndex` of `n ↦ n` is
  `Nat.floor` — and the sped up jump process *is* `gridPath (jumpChain E) c`, at
  every chain and every time. So the two objects of this milestone and of
  Milestone 4 are the same object under a clock that does not fluctuate.
* `jumpProcess_ne_gridPath_unitDelay`: **and one waiting time out of step
  already breaks it.** With the chain the identity on `ℕ`, rate `1`, and the
  zeroth waiting time `2` instead of `1`, the process still sits at the state
  `0` at time `1` while the grid path has moved to `1`. The witness is
  deterministic, so the gap is not a null set and no modification repairs it.
* `stepIndex_le_iff` and `stepIndex_le_iff_of_exists`: `{stepIndex T t ≤ n}` is
  the event `t < T (n + 1)` **or** the explosion set, and the second disjunct
  reads every jump time at once. So the renewal count is a stopping time for the
  filtration of the first `n + 1` jump times only under non explosion. This is
  one more place where `sInf ∅ = 0` makes a statement quietly true, and it is
  why the passage below has to be stated over a non explosive clock rather than
  over the construction as it stands.
* `lt_stepIndex_iff`, `tendsto_stepIndex_atTop` and
  `tendsto_stepIndex_div_atTop`: **the renewal law of large numbers, and it is
  deterministic.** For jump times `T` monotone with `T n → ∞` and `T n / n → m`
  for some `0 < m`, the renewal count satisfies `stepIndex T s / s → m⁻¹` as
  `s → ∞`. The proof is the sandwich
  `T (stepIndex T s) ≤ s < T (stepIndex T s + 1)` — `T_stepIndex_le` and
  `lt_stepIndex_succ` — divided by `stepIndex T s`, together with
  `stepIndex T s → ∞`, which is `stepIndex_le_iff_of_exists` read
  contrapositively. **In Lean** on 2026-09-18, second run.
  **Nothing about the waiting times enters, and that is the finding.** The
  passage between the jump number and the time looked probabilistic and is not:
  the limit theorem holds for every clock whose jump times grow linearly, and
  the divergence of the jump times is precisely the hypothesis that keeps the
  junk value `sInf ∅ = 0` out of the statement.
* `tendsto_stepIndex_mul_div_atTop`, the same on the grid: divided by `n`, the
  renewal count of `n t` converges to `t / m`, while `⌊n t⌋ / n` converges to
  `t`. **In Lean** on 2026-09-18, second run.
  **So the two indices of the probe agree in the limit exactly when the mean
  spacing of the jump times is `1`**, and differ by the factor `m` otherwise —
  which is what the rescaling by `n` is for.
* `integral_id_gammaMeasure`, `integrable_id_gammaMeasure`,
  `integral_sq_gammaMeasure`, `integrable_sq_gammaMeasure` and
  `variance_id_gammaMeasure`: **the gamma law is square integrable, has mean
  `a / r` and variance `a / r ^ 2`**, with `integral_id_expMeasure` and
  `integrable_id_expMeasure` the case `a = r = 1`. **In Lean** on 2026-09-18,
  third and fourth run.
  **One identification carries all of them**: `gammaPDF_toReal_smul_pow` says
  that the density against `x ^ n` is the Euler integrand `n` steps up, and the
  mean and the second moment are its cases `n = 1` and `n = 2`, differing only in
  how often `Real.Gamma_add_one` is applied afterwards. The variance is then
  `MeasureTheory.variance_eq_sub` and arithmetic, over the `MemLp _ 2` that
  `memLp_two_iff_integrable_sq` (`MeasureTheory/Function/L2Space.lean:52`) reads
  off `integrable_sq_gammaMeasure`.
  The whole content of the mean is that the density against the
  identity is the Euler integrand one step up —
  `x ^ (a - 1) · x = x ^ ((a + 1) - 1)`, as `gammaPDF_toReal_smul` — so that
  `Real.integral_rpow_mul_exp_neg_mul_Ioi` at `a + 1`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:465`) applies and
  `Real.Gamma_add_one` cancels the normalising constant. The exponential case is
  its corollary at `a = r = 1`; the integrability is the same identification
  read the other way, over `integrableOn_rpow_mul_exp_neg_mul_Ioi`. The indicator sits on
  `Set.Ioi 0` and not on `Set.Ici 0` because at `0` the identity vanishes, so the
  identification holds at **every** real point and no null set is spent.
  **Mathlib has the mean of no distribution of `Probability/Distributions/`**,
  in `v4.33.1` nor on `upstream/master` `a218e50f981` (2026-09-17): the only
  integrals of `Exponential.lean` and `Gamma.lean` are the normalisation
  (`lintegral_exponentialPDF_eq_one`, `lintegral_gammaPDF_eq_one`) and the
  distribution function, and no declaration of that directory carries `mean_` or
  `variance_` in its name.
  **But the scaled convergence of the Euler integral is Mathlib's, two
  directories from the value.** Inside `Analysis/SpecialFunctions/Gamma/` the
  *value* of `∫ t in Ioi 0, t ^ (a - 1) · exp (-(r · t))` is there for every
  rate `r` and the *convergence* only at `r = 1`; the scaled convergence sits in
  `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:74` as
  `integrableOn_rpow_mul_exp_neg_mul_rpow`, stated for `x ^ s · exp (-b · x ^ p)`
  and used there only at `p = 2`. `integrableOn_rpow_mul_exp_neg_mul_Ioi` is its
  case `p = 1` and nothing more; the translation is `Real.rpow_one`.
  **Checked on 2026-09-18 in `v4.33.1` and on `upstream/master` `a218e50f981`**,
  after the third run had recorded the opposite as a gap.
* `waitingMeasure_map_eval`, `integrable_waiting_eval`,
  `identDistrib_waiting_eval` and `tendsto_sum_waiting_div_atTop`: **the strong
  law of large numbers for the waiting times**, `∑_{k<n} ξ k / n → 1` almost
  surely. **In Lean** on 2026-09-18, third run. Etemadi's version in Mathlib
  (`ProbabilityTheory.strong_law_ae`, `Mathlib/Probability/StrongLaw.lean:786`)
  asks for pairwise independence, integrability of one coordinate and identical
  distribution; the first is `iIndepFun_waiting` through
  `ProbabilityTheory.iIndepFun.indepFun`, the other two are
  `Measure.infinitePi_map_eval`, and what the statement adds to it is the
  **value** of the limit, which is `integral_id_expMeasure`.
* `jumpTime_const` and `tendsto_jumpTime_div_atTop`: **the mean spacing of the
  jump times at a constant rate is the reciprocal of the rate.** **In Lean** on
  2026-09-18, third run. This is the almost sure hypothesis `T n / n → m` of
  `tendsto_stepIndex_div_atTop`, discharged over the jump construction, and with
  it the passage between jump number and time is complete: at rate `c` the
  renewal count of `s` grows like `c · s`.
  **The rate is not assumed positive**, and the statement is true without it: at
  `c = 0` every holding time is the junk value `x / 0 = 0`, the jump times are
  constantly `0`, and `c⁻¹ = 0` is the limit of the constant sequence. The junk
  value tells the truth on both sides here, as it does in `jumpTime_const_mul`
  and unlike `stepIndex_div_const`. Positivity is what the *other* hypothesis of
  `tendsto_stepIndex_div_atTop` needs, `0 < m`, which at `m = c⁻¹` is `0 < c`.
* **Reading the probe at the renewal count instead of at `⌊n t⌋`**, which is
  what the three statements above make a computation rather than a claim. The
  probe `tendsto_integral_mul_rescaledChain_natural` is stated over
  `gridPath (jumpChain E) n`, that is over the chain read at `⌊n t⌋`;
  `jumpProcess_const_mul_rate_eq_gridPath` says the two agree exactly when the
  indices do, and `tendsto_stepIndex_mul_div_atTop` together with
  `tendsto_jumpTime_div_atTop` says that at rate `c` they agree in the limit
  precisely for `c = 1`. Restating the probe over
  `fun t ↦ jumpProcess (fun _ ↦ (n : ℝ)) t` and carrying the limit through is
  what this milestone still owes.
  **What it owes is not a restatement, and the fourth run of 2026-09-18 says
  so with a witness**: see the two statements below.
* `jumpProcess_constWaiting`: **at a constant rate with constant waiting times
  the jump process is a grid path — of mesh `w / c` and not `1 / c`.** The chain
  is read at `⌊t · (c / w)⌋`, so the mesh is set by the clock as much as by the
  rate, and `jumpProcess_eq_gridPath_unitWaiting` is the case `w = 1`, where the
  two coincide and the clock becomes invisible. **In Lean** on 2026-09-18,
  fourth run. The proof is `jumpTime_const`, `stepIndex_div_const` and
  `stepIndex_natCast` and nothing else.
  **The factor `c / w` is `c / m` with `m` the mean waiting time**, which is the
  limit `tendsto_stepIndex_mul_div_atTop` gives for the random clock: the
  deterministic computation and the law of large numbers agree on which index is
  read, and both say `⌊c t⌋` is right only at `m = 1`.
* `naturalFiltration_jumpChain_le_comap_fst` and
  `not_measurable_jumpProcess_naturalFiltration_jumpChain`: **the jump process
  is measurable for no σ-algebra of the chain filtration, at any index.** **In
  Lean** on 2026-09-18, fourth run. The witness is a pair of sample points with
  the *same chain* — the identity on `ℕ` — and different constant clocks, `1/2`
  and `1`: at time `1` and rate `1` the first sits at the state `2` and the
  second at the state `1`.
  **This refutes the restatement above rather than postponing it.** Hypothesis
  `hW` of `tendsto_integral_mul_rescaledChain` asks the weight to be
  `naturalFiltration (Ξ n) ⌊n s⌋`-measurable; `measurable_comp_gridPath` supplies
  that for the grid path, and nothing can supply it for the jump path. The
  failure is not one of **index** — no `k` helps, and the statement is quantified
  over all of them — but of **factor**: the chain filtration is generated by the
  chain alone and holds no information about the clock, while the renewal count
  is a function of the clock. Measurability is not an almost sure notion, so one
  pair of sample points settles it.
  **What the probe therefore needs is a filtration that contains the clock**,
  and over such a filtration the index read is a **stopping time** and not a
  constant. That is the missing input, and it is named here rather than assumed
  away.
* `supRectangles`, `isPiSystem_supRectangles`, `generateFrom_supRectangles`,
  `setIntegral_eq_of_forall_supRectangle`,
  `setIntegral_eq_measureReal_smul_integral_of_indep` and `condExp_sup_of_indep`:
  **the irrelevant enlargement.** Is `m₂` independent of `m₁ ⊔ m₀` and is `f`
  measurable for `m₀`, then `μ[f | m₁ ⊔ m₂] = μ[f | m₁]` almost surely: adding an
  independent σ-algebra to the conditioning changes nothing. **In Lean** on
  2026-09-18, fifth run, over an arbitrary Banach space and with no topology on
  the sample space.
  **Mathlib has only the case `m₁ = ⊥`**, `MeasureTheory.condExp_indep_eq`
  (`Mathlib/Probability/ConditionalExpectation.lean:42`), the only theorem in
  that file; `condExp_sup` and `condexp_sup` occur nowhere in `Mathlib/`, checked
  against `upstream/master` `a218e50f981` (2026-09-17) and against v4.33.1. It is
  the twenty-fifth gap of `TODO.md` point 8.
  **The proof is the one `condExp_indep_eq` itself runs**: the π-system of
  rectangles `t₁ ∩ t₂`, the extension over it, and the degenerate case as the
  engine — on a rectangle the integral of an `m₁ ⊔ m₀`-measurable integrand cut
  down to `t₁` factors into `μ.real t₂` times an integral over `t₁`, and there
  the defining property of `μ[f | m₁]` closes.
  **`m₀` is an argument and not `σ(f)`**, because the range of `f` carries no
  measurable space to comap from; where it does, `σ(f)` is the smallest
  admissible `m₀`. **The independence is asked of `m₁ ⊔ m₀` and not of `m₀`
  alone**: `m₂` must be independent of the past and of the integrand jointly,
  and pairwise independence does not give that.
* `indep_comap_fst_comap_snd`, `condExp_sup_comap_snd` and
  `condExp_jumpChain_clock`: **the first of the two inputs the probe needs is
  supplied.** **In Lean** on 2026-09-18, fifth run. The two factors of a product
  measure are independent σ-algebras — `ProbabilityTheory.indepFun_prod`
  (`Mathlib/Probability/Independence/Basic.lean:727`) at the two identities — so
  a σ-algebra lying under the first factor may be enlarged by the **whole**
  second factor for free, and `jumpMeasure` is a product by definition.
  `condExp_jumpChain_clock` is therefore `condExp_jumpChain` word for word over
  `naturalFiltration (jumpChain E) n ⊔ comap Prod.snd ⊤`: the Markov property of
  the embedded chain survives an enlargement by the whole clock.
  **That the conditional expectation survives the enlargement was not automatic**
  and is the reason this statement comes before any construction over the
  enlarged filtration.
* `integral_sub_mul_eq_zero_of_martingale_stoppedValue` and
  `integral_sub_mul_eq_zero_of_martingale_stoppedValue_min`: **the orthogonality
  of hypothesis (c) at a random pair of indices.** A martingale increment between
  two stopping times of the chain filtration is orthogonal to every bounded
  variable of the earlier one. **In Lean** on 2026-09-18, fifth run. It is
  `integral_sub_mul_eq_zero_of_condExp_eq` at `m' = hσ.measurableSpace`, fed by
  `Martingale.stoppedValue_ae_eq_condExp_of_le` and by
  `Martingale.stoppedValue_min_ae_eq_condExp`
  (`Mathlib/Probability/Martingale/OptionalSampling.lean:141` and `:195`).
  **It relocates the second missing input of the probe.** Over the enlarged
  filtration the whole clock sits in the σ-algebra at index `0`, so every
  clock measurable index is a stopping time *trivially*, by being measurable at
  the bottom; being a stopping time is free. What is not free is **boundedness**,
  which optional sampling asks of the later index and which the renewal count at
  a fixed time does not have. The minimum form is what answers that: the later
  index may be truncated at a constant while the earlier one is left alone, so
  the weight keeps the σ-algebra it is measurable for — truncating the earlier
  index too would shrink that σ-algebra and lose the weight. What then remains is
  the passage `K → ∞`, a convergence of integrals and no longer a question about
  filtrations.
* `integral_sub_mul_eq_zero_of_martingale_stoppedValue_of_dominated` and
  `integral_sub_mul_eq_zero_of_martingale_stoppedValue_of_bdd`: **the passage
  `K → ∞` is done, and the hypothesis it costs is a dominating function.** The
  later stopping time is arbitrary, subject only to being finite. **In Lean** on
  2026-09-18, sixth run.
  **The convergence is not analytic.** At each sample point the truncated
  sequence is *stationary*: `τ ω` is a natural number, so `min (τ ω) K = τ ω`
  as soon as `K ≥ τ ω`. What the interchange of limit and integral needs is
  therefore a dominating function and nothing else, and `hdom` asks for it in the
  weakest place it can be asked — the martingale is dominated by `g` along the
  path up to `τ`, at indices `n ≤ τ ω` and nowhere else. Uniform integrability
  would also do; it is not taken, because it is strictly more than this proof
  uses and strictly harder to check at the application.
  **The index is `WithTop ℕ` and not `ℕ∞`.** `ENat` is a `def` over `WithTop ℕ`
  with its own order instances, so a `min` written at `ℕ∞` and a `min` produced
  by `IsStoppingTime.min` are definitionally equal and do not match as `rw`
  patterns; the associativity step fails against a term it is equal to. This is
  the trap already recorded at `jumpProcess_isLocalMPSolution` for `ENNReal`
  against `WithTop ℝ≥0`.
* `norm_chainCompensated_le` and `integral_sub_mul_eq_zero_of_chainCompensated`:
  **which of the two forms the probe may use, and what it pays.** **In Lean** on
  2026-09-18, sixth run. A compensated chain built from a bounded test function
  carries `‖M n ω‖ ≤ C + 2 n C` and no better bound — the compensator is a sum of
  `n` increments of size at most `2 C` and nothing cancels — so there is **no**
  uniform bound and the bounded form does not apply. The dominated form does, with
  `g = C + 2 τ C`, and its hypothesis is therefore that the random index has a
  **finite mean**.
  **That hypothesis is not an artefact of the formalisation.** It is the
  manuscript's own `𝔼[N t] < ∞` of `thm:pathjumpMP`(b), arrived at from the other
  side: the local statement needs no such thing, and the moment the orthogonality
  is read at a random index rather than a constant one, the first moment of that
  index is exactly what has to be paid.
* `lintegral_natCast_eq_tsum_measure` und
  `integrable_natCast_of_tsum_measure_ne_top`: **die Schichtkuchenformel für eine
  `ℕ`-wertige Größe** — ihr Integral ist die Summe der Maße ihrer Schwänze, und
  eine summierbare Schwanzfolge ist die Integrierbarkeit. **In Lean** am
  2026-09-18, siebter Lauf. Mathlib hat die *stetige* Schichtkuchenformel
  (`lintegral_eq_lintegral_meas_lt`,
  `MeasureTheory/Integral/Layercake.lean:496`, `upstream/master` `a218e50f981`)
  und die zählende nicht; dort gesucht unter `lintegral_natCast`,
  `integrable_natCast` und `tsum_measure_lt`, kein Treffer. Der Beweis ist die
  punktweise Identität `k = ∑' n, 1_{n < k}` und `lintegral_tsum`; weder eine
  Ordnung des Index noch σ-Endlichkeit kommen vor, anders als in der stetigen
  Fassung.
* `measure_lt_stepIndex_le` und `integrable_stepIndex_jumpMeasure`: **der
  Erneuerungszähler der Sprungkonstruktion hat einen endlichen Erwartungswert**,
  unter `0 < lam ≤ L`. **In Lean** am 2026-09-18, siebter Lauf. Damit ist
  `integral_sub_mul_eq_zero_of_chainCompensated` auf die Sprungkonstruktion
  anwendbar.
  **Die Abschätzung ist grob, und das ist der Punkt.** Der natürliche Weg über
  den Gammaschwanz braucht das Gesetz der `n`-ten Partialsumme, und Mathlib hat
  es nicht. Er wird nicht gebraucht: mehr als `n` Sprünge vor `t` erzwingen
  `∑_{k ≤ n} ξ k ≤ L t`, also — bei f.s. positiven Wartezeiten — daß **jede**
  der ersten `n+1` Wartezeiten in `Iic (L t)` liegt. Das ist eine
  **Zylindermenge**, `Measure.infinitePi_pi` rechnet ihr Maß als `q^(n+1)` aus
  mit `q = expMeasure 1 (Iic (L t)) < 1`, und eine geometrische Schranke reicht.
  Kein Gammagesetz, keine erzeugende Funktion, keine Unabhängigkeitsaussage über
  die hinaus, die schon für Borel--Cantelli dasteht.
* `clockFiltration`, `measurable_clockFiltration_jumpTime` und
  `isStoppingTime_stepIndex_augment`: **der Erneuerungszähler ist eine Stoppzeit
  — der augmentierten Uhrenfiltration.** **In Lean** am 2026-09-18, siebter Lauf.
  Zwei Berichtigungen stecken darin, und beide zählen.
  **Er ist nicht umsonst.** Über `naturalFiltration (jumpChain E) i ⊔ comap
  Prod.snd ⊤` liegt die ganze Uhr schon bei `i = 0` in der σ-Algebra, also wäre
  ein uhrmeßbarer Index trivial eine Stoppzeit. Der Erneuerungszähler ist **nicht
  uhrmeßbar**: `jumpTime` teilt die `k`-te Wartezeit durch `lam` an der `k`-ten
  Marke der Kette und liest damit beide Faktoren. Was den Beweis trägt, ist, daß
  er sie *bis zum selben Index* liest, und die scharfe Schranke ist `k ≤ i + 1`
  und nicht `k ≤ i` — die Rekursion `T (k+1) = T k + ξ k / lam (y k)` liest den
  Zustand **vor** dem Sprung.
  **Und über der schlichten Filtration ist die Aussage falsch.**
  `stepIndex_le_iff` sagt warum: `{stepIndex T t ≤ i}` ist das Ereignis
  `t < T (i+1)` **oder** die Explosionsmenge, auf der `sInf ∅ = 0` den Müllwert
  zurückgibt, und der zweite Zweig liest alle Sprungzeiten auf einmal und liegt
  in keinem `𝓖 i`. Die Explosionsmenge ist eine Nullmenge, also ist die ehrliche
  Aussage die über der **augmentierten** Filtration. Das ist die erste Stelle
  dieser Entwicklung, an der die Augmentierung keine Bequemlichkeit ist, sondern
  der Inhalt: ein lügender Müllwert wird durch eine Nullmenge berichtigt, und
  Nullmengen sind genau das, was `Filtration.augment` hinzufügt.
  `Martingale.augment` trägt das kompensierte Kettenmartingal hinüber und
  `Filtration.le_augment` das Gewicht; nichts oberhalb ist neu zu beweisen.
* `stepIndex_mono_time` und `not_stepIndex_mono_time`: **der Erneuerungszähler
  wächst mit der Zeit — außerhalb der Explosionsmenge, und nur dort.** **In
  Lean** am 2026-09-18, achter Lauf. Die Voraussetzung ist die Nichtexplosion
  **zur späteren Zeit** und sonst nichts; weder Monotonie von `T` noch eine
  Ordnung der Fenster kommt vor, und der Beweis ist `stepIndex_le` an der Stelle
  `stepIndex T t`.
  **Der Zeuge ist der Inhalt.** `T = (0, 0, 5, 5, …)` ist monoton und beschränkt,
  also explosiv; bei `s = 1` und `t = 6` ist `stepIndex T 6 = 0`, weil kein
  Fenster `6` enthält und `sInf ∅ = 0` zurückkommt, während `stepIndex T 1 = 1`
  ist. Der Zähler **fällt**. Das ist der dritte Müllwert dieser Entwicklung, der
  eine Aussage kippt, nach `x / 0 = 0` am absorbierenden Zustand und
  `sInf ∅ = 0` in `{stepIndex ≤ i}`, und es ist derselbe.
* `integral_sub_mul_eq_zero_of_martingale_stoppedValue_of_dominated`,
  `_of_bdd` und `_of_chainCompensated` verlangen die Ordnung ihrer beiden
  Stoppzeiten **fast überall** statt überall. **In Lean** am 2026-09-18, achter
  Lauf. Das ist die Voraussetzung, die der Beweis liest — `hστ` kommt dreimal vor
  und jedesmal innerhalb einer f.s.-Aussage —, und es ist die, die die Anwendung
  liefern kann: nach `not_stepIndex_mono_time` ist die überall-Fassung über der
  Sprungkonstruktion **falsch**, und die Menge, auf der sie scheitert, ist die
  Explosionsmenge.
* `martingale_chainCompensated_jumpChain` und
  `integral_sub_mul_eq_zero_jumpChain_stepIndex`: **Voraussetzung (c) über der
  Sprungkonstruktion, als *eine* Aussage.** **In Lean** am 2026-09-18, achter
  Lauf. Für beschränktes meßbares `f`, `0 < lam ≤ L` und `0 ≤ s ≤ t` verschwindet
  das Integral von `(M_{N t} − M_{N s}) · W` über `jumpMeasure mu nu`, wobei `M`
  das kompensierte Kettenmartingal, `N` der Erneuerungszähler und `W` beschränkt
  und meßbar für die σ-Algebra des früheren Zählers ist.
  **Die Schranke `lam ≤ L` ist keine Bequemlichkeit.** Sie trägt zweierlei:
  die Integrierbarkeit des Zählers (`integrable_stepIndex_jumpMeasure`) und die
  Ausschöpfung der Halbachse durch die Sprungzeiten (`ae_exists_lt_jumpTime`),
  und beides wird benutzt. Sie ist die formale Entsprechung dazu, daß das
  Manuskript `𝔼[N t] < ∞` in `thm:pathjumpMP`(b) führt und nicht in (a).
  Über `E` steht nichts als seine σ-Algebra, und keine Topologie kommt vor.
  **Das Gewicht lebt über der augmentierten Filtration**, und das ist nicht
  abzuschütteln: der Zähler ist nach `not_stepIndex_mono_time` nur außerhalb der
  Explosionsmenge monoton und nach `stepIndex_le_iff` nur dort eine Stoppzeit.
  Beide Defekte sind Nullmengen, und Nullmengen sind, was `Filtration.augment`
  aufnimmt.
* **Hypothesis (a) is about real random variables and carries no topology.** In
  the example above the path space `F` is `D ι E` and the functionals
  `Y° t` are evaluations, but the statement of (a) never mentions `F`'s
  topology: it asks for convergence in distribution of `Y° r (X n)` and of
  `(Y° t - Y° s) * Z (X n)`, finitely many real variables at a time. The
  acceptance test is that `mpSolution_of_tendsto` can be applied with `F` a bare
  measurable space, and that `mpSolution_of_tendsto_of_pContinuous` — which does
  need a separable metric `F` — is derived from it and not the other way round.
* **`P`-continuity is not continuity**, and the manuscript's
  `ex:atomicdiscontinuity` is why. The evaluation `ψ = π 1` on `D ℝ ℝ` is
  discontinuous at every path jumping at `1`; it is nevertheless `P`-continuous
  at `X` for every `P` with `P {ω | ω 1⁻ = ω 1} = 1`, that event being exactly
  where `ψ` is continuous. For a limit law charging paths that jump at `1` — the generic case when
  the clock has an atom there — no `C` works, and
  `mpSolution_of_tendsto_augmented` is what remains: adjoining the coordinate at
  `1` to the path space makes the functional continuous. This pair fixes the
  division of labour between the two corollaries.
* `isMPSolution_of_forall_condExp_eq_of_dense`, the passage from the martingale
  identity along `D` to the whole index, and the last step of
  `mpSolution_of_tendsto`. Over an index with the order topology and a first
  countable one, for `𝓧` strongly adapted, integrable at each index and with
  right continuous paths, and for a `D` such that every index is either in `D` or
  has `𝓝[D ∩ Set.Ioi t] t` nontrivial, the identity along `D` gives
  `IsMPSolution 𝓧 𝓕 P`. Two hypotheses that look natural are absent and one that
  looks technical is not.
  **Density of `D` is not enough**, and the hypothesis is the one
  `LiftWitness.exists_countable_right_dense` already delivers: at an index
  `t ∉ D` isolated from the right — an index with an immediate successor, which
  an order like `Set.Iic 0 ∪ Set.Ici 1` inside `ℝ` has — the filter
  `𝓝[D ∩ Set.Ioi t] t` is `⊥`, right continuity at `t` is vacuous and `Y t` is
  unconstrained. Asking `D` to contain the greatest element of `ι` covers only
  one of the two ways an index can be unapproachable from the right.
  **Countability of `D` is not used.** It is what makes such a `D` cheap to
  exhibit; what the proof needs is that `𝓝[D ∩ Set.Ioi t] t` be countably
  generated, and that is `[FirstCountableTopology ι]`.
  **Uniform integrability is not a hypothesis, it is a consequence.** A sequence
  of times in `D` bounded above by a single `t₁ ∈ D` makes `Y (w n)` the
  conditional expectation of the one integrable function `Y t₁`, by the identity
  along `D` alone, and the conditional expectations of a fixed integrable
  function are a uniformly integrable family. So the identity along `D` produces
  what carrying it across needs. **In Lean** on 2026-09-17, seventeenth run.
* `tendsto_eLpNorm_sub_of_forall_condExp_eq`, the step in which that uniform
  integrability is spent: for a sequence in `D` bounded above by a member of `D`,
  almost everywhere convergence of `Y (w n)` becomes `L¹` convergence. It is
  Vitali on top of `Integrable.uniformIntegrable_condExp_filtration`, with
  `norm_condExp_le` and `UnifIntegrable.of_norm_le_ae` carrying the property from
  the real dominating family to the `𝕂`-valued one, so the real--imaginary split
  is avoided exactly as in
  `Martingale.condExp_ae_eq_of_tendsto_nhdsWithin_Ioi`. **In Lean** on
  2026-09-17, seventeenth run.
* `exists_seq_mem_of_nhdsWithin_Ioi_neBot`, the sequence the two steps run along:
  inside `D`, falling to `t` from the right, bounded above by a member of `D`,
  and confined to a prescribed neighbourhood of `t`. The upper bound is what buys
  the uniform integrability and it costs nothing — the filter already produces a
  point `t₁` of `D ∩ Set.Ioi t`, and `Set.Iio t₁` is a neighbourhood of `t`, so
  cutting the filter down to it changes nothing. This is cheaper than extracting
  a decreasing subsequence, which is the other way to a common upper bound and
  needs a recursion. The neighbourhood argument is what lets the second step keep
  its sequence below a time `t` that is not in `D`. **In Lean** on 2026-09-17,
  seventeenth run.
* `integral_sub_mul_eq_zero_jumpProcessE_time`, `_apply`,
  `integral_sub_mul_eq_zero_map_jumpPath_time` und
  `integral_sub_mul_eq_zero_jumpPath_time`: **die Orthogonalität an der *Zeit*,
  über der Sprungkonstruktion.** **In Lean** am 2026-09-18, neunter Lauf. Für ein
  Testprozeß des Sprungoperators und `s ≤ t` verschwindet
  `∫ (Y t − Y s) · W` gegen jedes beschränkte, für die Vergangenheit bei `s`
  meßbare Gewicht — über dem Stichprobenraum der Konstruktion, in expliziter
  Gestalt an einer beschränkten meßbaren Testfunktion
  (`∫ ((f (X t) − ∫_0^t 𝒜f (X r) dr) − (f (X s) − ∫_0^s 𝒜f (X r) dr)) · W = 0`),
  über dem kanonischen Pfadraum von Meilenstein 6 unter dem Bildmaß, und in der
  Gestalt, die Voraussetzung (c) liest: Zuwachs und Gewicht beide mit `jumpPath`
  verkettet.
  **Damit ist die Lücke geschlossen, die der Abschnittskopf vor `StepIndexJunk`
  benennt** — dort steht, die Probe beweise eine Orthogonalität an der
  *Sprungnummer* und `ex:invariance` spreche von einer an der *Zeit*, und nichts
  schließe das.
  **Die Zeitfassung braucht weder die Augmentierung noch eine Stoppzeit**, weil
  `s` und `t` nicht zufällig sind. Alles, was die Sprungnummernfassung teuer
  machte, tritt durch `stepIndex` als *Index* ein: der Zähler ist nur außerhalb
  der Explosionsmenge eine Stoppzeit (`stepIndex_le_iff`) und nur dort monoton in
  der Zeit (`not_stepIndex_mono_time`). Hier liest keine Aussage `{stepIndex ≤ n}`
  als Ereignis, also ist keine Nullmenge aufzunehmen, und die Filtration ist das
  schlichte `jumpFiltrationE`.
  **Bezahlt wird statt dessen mit der Martingaleigenschaft in stetiger Zeit.**
  Die Sprungnummernfassung ruht auf `martingale_chainCompensated`, einer
  Einschrittidentität über `ℕ`; diese hier ruht auf
  `jumpProcessE_isMPSolution_of_nonneg`, also auf dem ganzen Meilenstein 4. Die
  beiden Orthogonalitäten sind nicht zwei Lesarten eines Satzes, sondern ruhen auf
  verschiedenen Martingalen.
  **Die Schranke `lam ≤ L` bleibt, `0 < lam` fällt weg.** Die Rate darf
  verschwinden, sofern der Kern dort absorbiert; die lineare Geburt-Tod-Kette an
  ihrem absorbierenden Zustand ist also nicht ausgeschlossen. `[MeasurableEq E]`
  ist von derselben Stelle geerbt, und keine Topologie auf `E` kommt vor.
* `tendsto_integral_mul_jumpPath_time`: **Voraussetzung (c) an einer
  approximierenden Familie von Sprungkonstruktionen.** **In Lean** am 2026-09-18,
  neunter Lauf. Jedes Glied hat eigene Rate, eigenen Kern, eigenes Anfangsgesetz
  und eigene Schranke; hinzuzugeben ist allein die `L¹`-Approximation des
  kanonischen Zuwachses durch den Zuwachs des Testprozesses — das ist `(K3)` des
  Manuskripts an der **Zeit** statt an der Sprungnummer. Der Grenzwert ist Null,
  weil **jedes** Glied exakt Null ist; die Arbeitsteilung ist dieselbe wie in
  `tendsto_integral_mul_of_martingale`, eine Stufe darüber. Die Integrierbarkeit
  des Zuwachses ist keine Voraussetzung, sondern fällt aus dem Martingal.
* `isDetermining_of_comap`, `isDetermining_pathFiltration` und
  `isDetermining_jumpPath`: **die ersten Zeugen für `IsDetermining`.** **In Lean**
  am 2026-09-18, neunter Lauf. `IsDetermining` trägt den ganzen Meilenstein — alle
  drei Fassungen des Konvergenzsatzes verlangen es —, und bis dahin war es in der
  Datei **unbewohnt**: die einzige Aussage darüber war `IsDetermining.comp_fst`,
  die einen Zeugen fortträgt und also einen braucht. Dasselbe Integritätsproblem,
  das `Shift` vor dem Bau des kanonischen Pfadraums hatte, und dieselbe Antwort.
  **Der Zeuge ist keine neue Idee, sondern die Definition der bedingten
  Erwartung.** Ist die Filtration unten der Rückzug einer σ-Algebra oben, so
  ziehen die Indikatoren der Mengen oben genau auf die Mengen der Vergangenheit
  zurück, und die Orthogonalität gegen sie alle ist, was
  `ae_eq_condExp_of_forall_setIntegral_eq` verbraucht. Die trennende Menge darf
  also stets **alle** beschränkten meßbaren Funktionen der Vergangenheit sein; der
  Inhalt einer schärferen — der trennenden Klassen des Manuskripts, `fact:sepcond`
  — ist, daß eine kleinere genügt.
  **Die starke Adaptiertheit der Familie ist Voraussetzung und nicht wegzulassen.**
  `IsDetermining` folgert `P[Y t | 𝓕 s] =ᵐ Y s`, und dafür muß die rechte Seite
  `𝓕 s`-meßbar sein; die Orthogonalität allein sagt darüber nichts. Die Definition
  verlangt es zu Recht nicht — es ist eine Eigenschaft von `𝓧` und nicht von `𝓩` —,
  also muß jeder Zeuge es liefern.
  Über dem kanonischen Pfadraum ist die Rückzugsvoraussetzung
  `MeasurableSpace.comap_id`, über der Sprungkonstruktion
  `jumpFiltrationE_eq_comap_jumpPath`. Keine Topologie auf dem Pfadraum, keine
  Separabilität, und über `ι` nichts als was `IsDetermining` selbst trägt.
  **Damit sind über der Sprungkonstruktion nur noch die Voraussetzungen (a) und
  (b) ohne Zeugen**; sie sind das Straffheitsargument, das das Manuskript
  ausdrücklich nicht liefert. *(Berichtigt am 2026-09-18, zehnter Lauf: an der
  **konstanten** Folge haben auch (a) und (b) einen Zeugen, siehe
  `mpSolution_of_tendsto_jumpPath`. Ohne Zeugen ist (a) und (b) an einer
  **nichttrivialen** approximierenden Folge, und das ist die Straffheit.)*
* `isDetermining_of_generateFromFuns` und `isDetermining_indicatorFuns`: **eine
  erzeugende multiplikative Klasse ist schon eine trennende Menge**, und das ist
  die Stelle, an der `IsDetermining` die trennenden Klassen des Manuskripts
  (`fact:sepcond`) trifft. **In Lean** am 2026-09-18, zehnter Lauf.
  `isDetermining_of_comap` nimmt *alle* beschränkten meßbaren Funktionen der
  Vergangenheit und ist damit der triviale Zeuge; hier darf die Klasse so klein
  sein, wie sie will, sofern sie unter Produkten abgeschlossen ist, die Konstante
  `1` trägt und die Vergangenheit erzeugt. Der funktionale Monotone-Klassen-Satz
  der Roadmap `WeakConvergence` — `integral_mul_eq_zero_of_isMulSystem` — trägt
  die Orthogonalität von der Klasse auf alles, was sie erzeugt.
  **Der Transport auf den Stichprobenraum ist `generateFromFuns_comp`**, ebenfalls
  vom selben Lauf und in `WeakConvergence` eingetragen: die Klasse lebt auf dem
  Pfadraum, die Integrale auf dem Raum, der den Prozeß trägt, und die von den
  verketteten Funktionen erzeugte σ-Algebra ist der **Rückzug** der von der Klasse
  erzeugten. Eine Gleichheit, also geht auf dem Weg nichts verloren.
  **Real- und Imaginärteil werden getrennt behandelt**, weil der
  Monotone-Klassen-Satz über reellen Funktionen spricht und `IsDetermining` über
  `RCLike 𝕂`; zusammengesetzt wird mit `RCLike.ext`, und sonst sieht kein Schritt
  des Beweises `𝕂`.
  **Die Konstante `1` ist keine Zierde**: `integral_mul_eq_zero_of_isMulSystem`
  trägt das Verschwinden von `∫ g` als eigene Voraussetzung und sagt, warum sie
  nicht wegfällt; hier ist sie genau die Orthogonalität an der konstanten
  Funktion.
  `isDetermining_indicatorFuns` ist der Zeuge, der die Aussage von einer
  Umformulierung unterscheidet: die **Indikatoren eines erzeugenden π-Systems**
  sind eine trennende Menge. `isMulSystem_indicator_of_isPiSystem` macht aus dem
  π-System die multiplikative Klasse — mit `∅` dazu, was nach
  `generateFromFuns_indicatorFuns` nichts kostet —, und über das π-System hinaus
  ist nur `Set.univ ∈ 𝒞 s` verlangt, weil es die Konstante `1` liefert. Damit darf
  die trennende Menge so klein sein wie das Zylinder-π-System, das die Filtration
  erzeugt, und das ist, wozu eine trennende Klasse da ist.
* `measurableSet_pathCylinders_of_le`, `isDetermining_pathCylinders`,
  `isDetermining_pathCylinders_coordinate` und
  `isDetermining_pathCylinders_jumpPath`: **die Zylinder der Vergangenheit sind
  eine trennende Menge**, über jeder Filtration, die der Rückzug der natürlichen
  Filtration einer Koordinatenfamilie ist, und insbesondere über dem kanonischen
  Pfadraum und über dem Stichprobenraum der Sprungkonstruktion. **In Lean** am
  2026-09-18, zehnter Lauf. Die trennenden Funktionale sind hier die Indikatoren
  endlich vieler Koordinatenbedingungen zu Zeiten unter `s`, also eine **echt
  kleinere** Klasse als alle beschränkten meßbaren Funktionen der Vergangenheit.
  Der Erzeugungsschritt ist `generateFrom_pathCylinders` zusammen mit
  `iSup_subtype'` — genau die Umschreibung, die
  `setIntegral_eq_of_forall_cylinder` in Meilenstein 3 schon führt —, und
  `Set.univ` ist der Zylinder über der leeren Zeitmenge, der die Konstante `1`
  liefert. Die Zeiten sind durch den Untertyp `Set.Iic s` indiziert und nicht
  durch eine Kette; eine lineare Ordnung wird nirgends verbraucht.
* `isDetermining_evalFuns`: **die endlichdimensionalen Testfunktionen der
  Vergangenheit sind eine trennende Menge auf dem Pfadraum.** **In Lean** am
  2026-09-21, fünfzehnter Lauf. Die Klasse ist
  `SkorokhodSpace.evalFuns E (insert s (T ∩ Set.Iic s))` über einer von rechts
  dichten Zeitmenge `T`, und die Filtration ist der Rückzug der
  Koordinatenvergangenheit längs der Pfadabbildung. Die fünf Eingaben von
  `isDetermining_of_generateFromFuns` stehen sämtlich in **SkorokhodSpace**
  Meilenstein 8; die fünfte, die Erzeugung, ist
  `SkorokhodSpace.generateFromFuns_evalFuns_Iic`.
  **Das ist keine Bequemlichkeit, sondern eine Zwangslage.** Der dritte Punkt der
  Kette von Meilenstein 11 verlangt von *einer* Klasse zugleich `IsDetermining`
  und die `P`-Stetigkeit ihrer Glieder; die früheren Zeugen —
  `isDetermining_of_comap` (alle beschränkten meßbaren Funktionen der
  Vergangenheit) und `isDetermining_pathCylinders` (Indikatoren) — erfüllen das
  erste und können das zweite nicht erfüllen, denn ein Indikator ist an keiner
  Randstelle stetig. `evalFuns` ist die einzige Klasse, von der beides bewiesen
  ist.
  **Die Zeit `s` steht ausdrücklich in der Klasse.** Die Rechtsdichtheit liefert
  Zeiten *oberhalb* einer gegebenen und gewinnt damit jede Koordinate zu `r < s`
  zurück; bei `r = s` gibt es innerhalb von `Set.Iic s` nichts mehr oberhalb, und
  ein Pfad, der bei `s` springt, wird von keiner früheren Koordinate gelesen.
  `s ∈ T` als Voraussetzung mitzuführen leistete dasselbe und wäre an jeder
  getesteten Zeit einzulösen; `insert s` kostet nichts und verlangt nichts.
* `mpSolution_of_tendsto_jumpPath_of_isDetermining` und
  `mpSolution_of_tendsto_jumpPath_cylinders`: **die Probe ein zweites Mal, über
  den Zylindern allein.** **In Lean** am 2026-09-18, zehnter Lauf. Der Kern der
  Probe trägt die trennende Menge als Parameter; `mpSolution_of_tendsto_jumpPath`
  (alle beschränkten meßbaren Funktionen der Vergangenheit) und
  `mpSolution_of_tendsto_jumpPath_cylinders` (die Zylinder) sind zwei Folgerungen
  daraus.
  **Das ist die Messung, für die eine trennende Klasse da ist:** derselbe Satz,
  dieselbe Konklusion, dieselben drei übrigen Voraussetzungen — es ändert sich
  **allein** die Voraussetzung `IsDetermining`. Was eine trennende Klasse kauft,
  ist an dieser Stelle genau eine kleinere Menge von Testfunktionalen und sonst
  nichts; bezahlt wird sie einmal, im funktionalen Monotone-Klassen-Satz hinter
  `isDetermining_of_generateFromFuns`.
* `lebesgueClock_real_interval_optional` und `abs_mpFamily_coordinate_le`: **ein
  Testprozeß von `mpFamily` ist auf einem beschränkten Zeitfenster gleichmäßig
  beschränkt**, in der Zeit und im Pfad. **In Lean** am 2026-09-18, zehnter Lauf.
  Die Schranke ist `‖p.1‖ + ‖p.2‖ * t`, und sie ist gleichmäßig in `r ≤ t`, weil
  das Fenster `Set.Ioc ⊥ r` mit `r` wächst; die Uhr ist das Lebesguemaß, also ist
  die Masse des Fensters `r` selbst und die Konstante explizit. Das ist der
  Begleiter von `integrable_mpFamily_coordinate`, das dieselben zwei Schranken
  liest und nur Integrierbarkeit meldet: Voraussetzung (b) von
  `mpSolution_of_tendsto` verlangt mehr als Integrierbarkeit, nämlich **eine**
  Abschneidestufe für **alle** `r ∈ D ∩ Set.Iic t` zugleich, und das gibt eine
  gleichmäßige Schranke und Integrierbarkeit allein nicht.
* `mpSolution_of_tendsto_jumpPath`: **die Leerheitsprobe des Konvergenzsatzes, an
  der konstanten Folge.** **In Lean** am 2026-09-18, zehnter Lauf. Alle vier
  Voraussetzungen von `mpSolution_of_tendsto` sind auf den Daten von Meilenstein 4
  eingelöst, für ein **beliebiges** `D` und ein beliebiges Glied der Testfamilie:
  `IsDetermining` durch `isDetermining_jumpPath` — oder, in der Zylinderfassung
  `mpSolution_of_tendsto_jumpPath_cylinders`, durch
  `isDetermining_pathCylinders_jumpPath` —, die Verteilungskonvergenz durch
  `MeasureTheory.tendstoInDistribution_const`, die gleichgradige Integrierbarkeit
  durch `abs_mpFamily_coordinate_le`, und das Verschwinden der geprüften Zuwächse
  durch `integral_sub_mul_eq_zero_jumpPath_time`.
  **Was der Satz zurückgibt, ist die Martingalidentität, die
  `jumpPath_isMPSolution` schon hat**, also nichts Neues über den Sprungprozeß.
  Was er belegt, ist etwas über den **Satz**: seine vier Voraussetzungen sind an
  einer wirklichen Lösung eines Martingalproblems gemeinsam bewohnt. Das ist es,
  was eine Roadmap-Aussage braucht, die auf ihnen ruht, und was Meilenstein 10
  nicht hatte.
  **Die Stelle, an der die Probe klemmen sollte, klemmt nicht.** Voraussetzung (b)
  verlangt **eine** Abschneidestufe, gleichmäßig über `r ∈ D ∩ Set.Iic t`;
  `tendsto_integral_tail` gibt sie je Funktion, und ein Maximum über ein
  unendliches `D ∩ Set.Iic t` gibt es nicht. Die Sprungkonstruktion entkommt dem,
  **ohne `D` einzuschränken**: ihre Testprozesse sind auf einem beschränkten
  Zeitfenster gleichmäßig beschränkt, also sind die Schwänze von (b) nicht klein,
  sondern **Null**. Ebenso ist der Grenzwert in (c) nicht klein, sondern jedes
  Glied ist exakt Null. Die Probe ist deshalb nirgends eine Abschätzung.
  Die Voraussetzungen sind die von `jumpProcessE_isMPSolution_of_nonneg` und keine
  weiteren; keine Topologie auf `E` kommt vor.
* `tail_integral_mpFamily_coordinate_le` und
  `integrable_mpFamily_coordinate_comp`: **über dem kanonischen Pfadraum und einem
  Operator mit beschränkten Komponenten sind die Integrierbarkeit und
  Voraussetzung (b) von `mpSolution_of_tendsto` für eine *beliebige*
  approximierende Familie automatisch.** **In Lean** am 2026-09-18, elfter Lauf.
  Die Abschneidestufe kommt aus `abs_mpFamily_coordinate_le`, und weil die
  Schranke an `Y r` als Funktion auf dem Pfadraum sitzt und gleichmäßig im Pfad
  ist, übersteht sie die Verkettung mit **jeder** Abbildung in den Pfadraum und
  die Integration gegen **jedes** Wahrscheinlichkeitsmaß: die Schwänze von (b)
  sind Null.
  **Über die approximierende Familie geht dabei nichts ein** — nicht ihre Räume,
  nicht ihre Maße, nicht ihre Abbildungen, und insbesondere keine gleichmäßige
  Schranke an die Raten der Approximanten. Voraussetzung (b) trägt an dieser
  Stelle also keine Information, und was von der Lücke bleibt, ist Voraussetzung
  (a), die Verteilungskonvergenz.
  Die Grenze des Befundes ist die Beschränktheit der zweiten Komponenten: ein
  Erzeuger ohne sie — der lokale Zweig, eine unbeschränkte Rate — hat kein solches
  `c`, und dort ist (b) durch gleichgradige Integrierbarkeit zu erarbeiten.
* `mpSolution_of_tendsto_mpFamily_coordinate`: **der Konvergenzsatz über dem
  kanonischen Pfadraum für einen beschränkten Operator**, mit genau den beiden
  Voraussetzungen, die dort nicht automatisch sind. **In Lean** am 2026-09-18,
  elfter Lauf. Übrig bleiben (a), die Verteilungskonvergenz der geprüften Größen,
  und (c), das Verschwinden der geprüften Zuwächse; Integrierbarkeit und (b) sind
  durch die beiden vorigen Punkte eingelöst. Das ist die Gestalt, die
  Meilenstein 11 verbraucht: dort sind die approximierenden Prozesse càdlàg, (a)
  fällt aus der Konvergenz in der Skorokhodtopologie an den Zeiten ohne feste
  Unstetigkeit, und (c) liefern die approximierenden Martingalprobleme.
  **Die Aufteilung sagt, wo die Arbeit eines Konvergenzarguments sitzt**, und sie
  sagt, daß sie nicht in einer Abschätzung der gleichgradigen Integrierbarkeit
  sitzt: solange der **Grenz**operator beschränkt ist, dürfen die Approximanten
  beliebig sein, andere Räume, andere Maße, andere und auch unbeschränkte Raten.
* `mpSolution_of_tendsto_map_jumpPath_of_isDetermining`,
  `mpSolution_of_tendsto_map_jumpPath` und
  `mpSolution_of_tendsto_map_jumpPath_cylinders`: **die Probe unter dem Bildmaß,
  auf dem kanonischen Pfadraum selbst.** **In Lean** am 2026-09-18, elfter Lauf.
  Die Pfadabbildung ist die **Identität**, die Prozesse sind die Testprozesse von
  `mpFamily` über `RightContinuousPath E`, die Filtration ist `pathFiltration`,
  und das Maß ist das Bild `(jumpMeasure mu nu).map (jumpPath lam)`, das
  `jumpPath_isMPSolution` löst. Beide trennenden Mengen des zehnten Laufs passen:
  `isDetermining_pathFiltration` und `isDetermining_pathCylinders_coordinate`.
  **Warum der Raumwechsel nicht kosmetisch ist:** Meilenstein 6 und
  Meilenstein 11 sprechen über Maße auf einem Pfadraum und nicht über
  Stichprobenräume, die Pfade tragen — `mpSolutions_jumpOperator_coordinate_eq_singleton`
  ist eine Identität von Mengen von Maßen auf `RightContinuousPath E`, und jede
  Aussage von `SkorokhodSpace`, die eine Lösung verbrauchen könnte, lebt dort
  ebenfalls. Bis hierher hatte der Konvergenzsatz Zeugen allein über dem
  Stichprobenraum, war also an Daten bewohnt, die keine Aussage weiter oben
  verbrauchen kann.
  Der Beweis läuft über `mpSolution_of_tendsto_mpFamily_coordinate` und löst
  deshalb weder die Integrierbarkeit noch (b) ein; zu liefern bleiben die
  Verteilungskonvergenz — an einer konstanten Folge `tendstoInDistribution_const`
  — und `integral_sub_mul_eq_zero_map_jumpPath_time` für (c). Was die Fassung über
  dem Stichprobenraum dafür einbringt, ist eine Konklusion über die Filtration der
  Konstruktion selbst, `jumpFiltrationE`, die das Bildmaß vergißt.

## Milestone 11: the Skorokhod instances

Now `ι = [0,∞)`, `E` Polish, and paths in the càdlàg space `D ι E` of the
roadmap **SkorokhodSpace**.

**The index of this milestone is `ℝ`, not `ℝ≥0`, and it is decided rather than
chosen.** Every statement of this milestone that *produces* tightness rests on
`SkorokhodSpace.isCompact_closure_iff` of Milestone 7 there, which is false over
an index with gaps (`SkorokhodSpace.not_isCompact_closure_of_rigid`) and is
therefore available over `ℝ` alone. That the processes run over `ℝ≥0` costs
nothing, because tightness crosses the index **in both directions**:
`SkorokhodSpace.isTightMeasureSet_map_extendNNReal_iff` (**SkorokhodSpace**
Milestone 9, proved 2026-09-19). The rule behind it is worth stating once, since
it settles the same question for every later item: a *hypothesis* crosses only
forward, from `ℝ≥0` to `ℝ`, and a *conclusion* crosses backward. That is why the
`ℝ≥0`-form of Milestone 8 there had to be written out — it carries the
convergence of the finite dimensional distributions across as a hypothesis, and
that one does not cross at all, a dense `T ⊆ ℝ≥0` not being dense in `ℝ` — while
nothing of this milestone is to be restated over `ℝ≥0`.

**What has to exist in SkorokhodSpace before this milestone can begin, checked at
the source 2026-09-19.** The finding of the twelfth run of that day was that in
`SkorokhodSpace/Suggested.lean` the predicate `IsTightMeasureSet` occurred only
ever as a **hypothesis** or in the transports of Milestone 9, which carry
tightness along the index crossing and therefore ask for it as well: **no
declaration there produced tightness from anything but tightness.** It is
`SkorokhodSpace.isTightMeasureSet_iff` that removes that, and it is item 2 below.
Three named items of **SkorokhodSpace** Milestone 8 that this milestone consumes
had no declaration at all, and they are needed in this order:

1. `SkorokhodSpace.postcomp` with `SkorokhodSpace.continuous_postcomp` and
   `Measurable (postcomp h)` — the map `f ↦ h ∘ f` for continuous `h : E → E'`.
   **The map, its coordinates and its measurability are proved since
   2026-09-19**, in `SkorokhodSpace/Suggested.lean`: `SkorokhodSpace.postcomp`,
   `SkorokhodSpace.postcomp_toFun`, `SkorokhodSpace.measurable_postcomp`. Well
   definedness is **Mathlib's** and was not ours to prove:
   `IsCadlag.continuous_comp`, `Mathlib/Topology/Order/Cadlag.lean:119`.
   Measurability is `SkorokhodSpace.measurable_of_measurable_eval`
   coordinatewise and was cheap. **The continuity is proved too**, as
   `SkorokhodSpace.continuous_postcomp`, with four named inputs:
   `IsCompact.exists_pos_forall_dist_image_lt`, that a continuous map is
   uniformly continuous near a compact set in the one sided form with the second
   point free; `SkorokhodSpace.distWith_postcomp_le`, the windowed estimate at
   one radius and one time change; `SkorokhodSpace.totallyBounded_image_exhaustion`,
   which with `[CompleteSpace E]` makes the closure of the window values of the
   centre compact; and `SkorokhodSpace.intWith_postcomp_le`, the estimate of the
   integral over the window radius. The last is a Markov inequality and not a
   pointwise bound: a small `SkorokhodSpace.intWith` leaves
   `SkorokhodSpace.distWith` large on a set of radii of small Lebesgue measure,
   and that set is paid for by the trivial bound `1` on the truncated integrand.
   **This item is therefore closed**; what remains of the three are items 2 and
   3. And the forward half of item 3 came with it, as
   `SkorokhodSpace.isTightMeasureSet_map_postcomp`.
2. `SkorokhodSpace.isTightMeasureSet_iff` — the tightness criterion at the level
   of measures, compact containment together with the modulus condition. This is
   the statement `isCompact_closure_iff` of Milestone 7 is *for*, and it is the
   one every item below reads. **Proved 2026-09-19**, together with
   `SkorokhodSpace.modulusBased_mono`, which is the step at which the countable
   family of conditions becomes the limit Milestone 7 asks for. Its two
   measure theoretic inputs, `isTightMeasureSet_of_forall_exists_isCompact_closure`
   and `measure_compl_iInter_le`, hold for arbitrary — in particular non
   measurable — sets, and that is what let the criterion be stated over the
   modulus sets at all. **This item is therefore closed**, and with it the finding
   that held this milestone up: `SkorokhodSpace` now has a declaration that
   produces tightness from something other than tightness.
3. `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` — the reduction to real
   valued paths, whose forward direction is item 1 and whose converse reads item
   2. **The only one of the three still open**, and its converse is not item 2
   applied: each test function `h` supplies its own `δ`-sparse subdivision, and
   one subdivision has to serve them all. `SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells`
   bounds the oscillation of a subdivision only by that of one it **refines**, so
   a common refinement is what is needed — and that a common refinement cannot be
   had with a sparseness chosen before the paths is **proved**, 2026-09-19, as
   `SkorokhodSpace.exists_isSubdivisionBased_pair_forall_not_cells`.

   **Both routes the roadmap had named are now refuted**, the second on 2026-09-19
   as well. The fallback was Ethier–Kurtz' subdivision-free three point modulus
   `w''`, and it fails on the same witness: a path of `D(ℝ, ℝ × ℝ)` with **two
   jumps in different coordinates**, by
   `SkorokhodSpace.exists_isCompact_modulusBased_postcomp_eq_zero` and
   `SkorokhodSpace.exists_min_edist_postcomp_eq_zero`. What is refuted is a family
   that recovers the metric of the value space on the compact set — granted even
   with equality there. The criterion itself stands, because it quantifies over a
   **dense** class, which contains functions seeing both jumps at once; a proof has
   therefore to choose its test function **after** the path.

   **And that proof has a shape now, 2026-09-19.** The refutation is narrower than
   it read: it does not touch the family this roadmap names, the clipped distances
   `y ↦ min (dist y x_j) 1` to the points of a net. At the very witness that
   defeats the coordinates, the clipped distance to the value **between** the two
   jumps has image path `1, 0, 1` and modulus at least `1`
   (`SkorokhodSpace.one_le_modulus_postcomp_clipDist_twoJump`), because the three
   point quantity compares both displacements to the **common middle value** and
   the distance to that value reads both at once —
   `SkorokhodSpace.min_edist_postcomp_clipDist`, with **equality** up to the clip,
   so at the level `min η 1`, which depends on `η` alone. The passage has three
   links, of which **two are proved**: the reduction to the middle value
   (`SkorokhodSpace.min_edist_postcomp_clipDist`,
   `SkorokhodSpace.le_min_dist_of_dist_clipDist_le`) and the easy half of the
   comparison with the modulus
   (`SkorokhodSpace.min_edist_le_two_mul_modulusBased`). The open one is the
   **hard** half of Ethier–Kurtz' comparison of `w'` with `w''`, and that is what
   a run at this item builds. It is written out at the item in
   `SkorokhodSpace/README.md`, Milestone 8; it is not an application of item 2.

   Its **first half stands** since 2026-09-19:
   `SkorokhodSpace.exists_forall_edist_lt_of_forall_min_edist_lt`, that a window
   on which the three point quantity is below `η` carries exactly **one break**.
   The greedy subdivision that the item named for the second half does **not**
   close it — merging two greedy cells crosses that break, and the displacement
   at a break is the one quantity the hypothesis leaves free. The replacement
   puts the nodes at the large jumps instead — that they are far enough apart is
   `SkorokhodSpace.jump_le_two_mul_of_forall_min_edist_lt`, proved the same day —
   and its cell estimate is
   `SkorokhodSpace.edist_le_four_mul_of_forall_min_edist_lt`: a window whose
   jumps are all at most `2 * η` has oscillation at most `4 * η`.

   **And the item as stated is false, 2026-09-19.** A based subdivision carries
   the base point among its nodes and has every gap longer than `δ`, so a jump in
   `Set.Ioo t₀ (t₀ + δ)` sits at no cell boundary and is charged in full to the
   cell beginning at `t₀`. The unit step, whose three point quantity is `0` at
   every triple and every span, has based modulus at least `1`
   (`SkorokhodSpace.not_forall_modulusBased_le_mul_of_forall_min_edist_lt`), so no
   finite constant repairs it. The link carries a **boundary term at the base
   point** — the term the classical statement on `[0, ∞)` writes as
   `sup_{t < δ} d(x t, x 0)` — with the left half measured against
   `leftLim f t₀`. It is `SkorokhodSpace.basePointOsc`, it vanishes as `δ → 0`
   (`SkorokhodSpace.tendsto_basePointOsc`), so the consumer is unaffected, and
   against `f t₀` it would not vanish
   (`SkorokhodSpace.iSup_edist_step_left_eq_one`); for a family the vanishing is
   a hypothesis and not a formality. It is written out at the item in
   `SkorokhodSpace/README.md`, Milestone 8.

   **In the corrected shape the link splits, and its analytic half stands**,
   2026-09-19: `SkorokhodSpace.subdivisionOsc_le_of_forall_min_edist_lt` says what
   a *given* subdivision costs — every gap at most `2 * δ`, every cell either free
   of jumps larger than `2 * η` in its interior or adjoining the base point, and
   the oscillation is at most `4 * η + 2 * SkorokhodSpace.basePointOsc t₀ f (2*δ)`
   — using neither monotonicity nor coverage nor sparseness. That the corrected
   inequality survives its own counterexample is
   `SkorokhodSpace.one_le_four_mul_add_two_mul_basePointOsc_step`. What is left is
   the *existence* of such a subdivision. The node-placing rule that produces it
   is built the same day — `SkorokhodSpace.nextNode` with `lt_nextNode`,
   `nextNode_le`, `notMem_Ioo_nextNode` and `notMem_Ioc_nextNode`, over an
   abstract `2 * δ`-separated set, and
   `SkorokhodSpace.separated_setOf_lt_edist_leftLim` handing it the large jumps
   of a path.

   **The combinatorial half is complete the same day**:
   `SkorokhodSpace.exists_subdivision_of_separated` produces, for a
   `2 * δ`-separated set and any window radius, a strictly increasing
   `t : Fin (n + 1) → ℝ` that contains the base point, covers the window, has
   every gap in `(δ, 2 * δ]`, and misses the set in the interior of every cell but
   the two at the base point — which is the conjunction of what
   `SkorokhodSpace.IsSubdivisionBased` and
   `SkorokhodSpace.subdivisionOsc_le_of_forall_min_edist_lt` ask for.

   **And the two halves are joined the same day**:
   `SkorokhodSpace.modulusBased_le_of_forall_min_edist_lt` gives
   `modulusBased 0 m f δ ≤ 4 * η + 2 * SkorokhodSpace.basePointOsc 0 f (2 * δ)`
   for a path whose three point quantity stays below `η` on every window of span
   `2 * δ`, at the base point `0`, which is where the chain reads it. The link is
   closed. It is written out at the item in `SkorokhodSpace/README.md`,
   Milestone 8.

   **And the boundary term costs the criterion no hypothesis of its own**, the
   same day, which is what the closing of the link left to decide. It is closed
   from above by `SkorokhodSpace.basePointOsc_le_three_mul_modulusBased` —
   `basePointOsc 0 f δ ≤ 3 * modulusBased 0 m f δ` for `m > 0`, a based
   subdivision having the base point among its nodes and every gap longer than
   `δ` — so a family whose image moduli are controlled has its image boundary
   terms controlled with them. And from below it travels under post-composition
   with the **same** test functions link 2 uses, except that it needs **two**
   centres and not one: its left half is measured against `leftLim f t₀` and its
   right half against `f t₀`, and both values lie in the compact set compact
   containment supplies, the left limit because a compact set is closed
   (`SkorokhodSpace.leftLim_postcomp`,
   `SkorokhodSpace.min_iSup_edist_le_iSup_edist_postcomp`,
   `SkorokhodSpace.min_iSup_edist_leftLim_le_iSup_edist_leftLim_postcomp`). So
   the earlier reading of this item — that for a family the vanishing of the
   boundary term is a hypothesis and not a formality — is **corrected**: it is a
   consequence of the hypothesis the criterion already carries.

   **And the chain is composed the same day**, into the three statements the
   converse half reads: `SkorokhodSpace.min_edist_le_two_mul_modulusBased_postcomp`
   for the three point quantity and
   `SkorokhodSpace.min_iSup_edist_le_three_mul_modulusBased_postcomp` with
   `SkorokhodSpace.min_iSup_edist_leftLim_le_three_mul_modulusBased_postcomp` for
   the two halves of the boundary term. Each bounds a quantity of the path that
   link 1 asks about, capped at `1` and up to `4 * ρ`, by the based modulus of
   **one** image path — which is the quantity the hypothesis of this item
   controls. What is left is the bookkeeping of the net and of the exceptional
   sets, not the chain.

   **And link 2 asked more of its test function than a consumer has**, until the
   same day: `SkorokhodSpace.le_min_dist_of_dist_clipDist_le` demanded the bound
   `dist (h y) (clipDist x y) ≤ ρ` at *every* `y ∈ E`, while the class `H` is
   dense only for uniform convergence **on compact sets**. The statements now ask
   it at the points they read — the three of the triple, the two the boundary
   term measures against, the path's values over the window — all of which lie in
   the compact set compact containment supplies. The positivity of `ρ` went with
   it, having never been used.

   **This item is closed, 2026-09-19.**
   `SkorokhodSpace.isTightMeasureSet_of_isTightMeasureSet_map_postcomp` is the
   converse and `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` the
   equivalence this item names, the latter with the test class `E →ᵇ ℝ`, where
   the clipped distances are their own approximants. Compact containment is a
   hypothesis of both and is not removable.

   **What held it up at the end was not the bookkeeping but link 1**, which asked
   its three point hypothesis at every triple of `ℝ` — a level at which no
   consumer has it, the based modulus of an image path saying nothing about times
   outside the window its subdivisions cover. It is now read on
   `Set.Icc (-R) R` with `R ≥ 2 * max m 0 + 6 * δ`, the nodes being confined to
   `2 * u + 4 * δ` around the base point by
   `SkorokhodSpace.exists_subdivision_of_separated`, and the same window travels
   through `SkorokhodSpace.subdivisionOsc_le_of_forall_min_edist_lt`,
   `SkorokhodSpace.two_mul_le_sub_of_forall_min_edist_lt` and
   `SkorokhodSpace.separated_setOf_lt_edist_leftLim`.

   The arithmetic, with `c = min η 1 / 64`:
   `4 * (4 * c) + 2 * (8 * c) = 32 * c < 64 * c = min η 1`. The level is cut down
   to `min η 1` because links 2 and 3 are capped at `1` and `4 * c ≤ 1` is what
   removes the cap. **No exceptional set is measurable**, and none has to be: the
   image bound reaches the path by `MeasureTheory.Measure.le_map_apply`, which
   holds for an arbitrary set.

Item 3 is **closed**, 2026-09-19, so
`isTight_map_postcomp_of_exists_martingale` has a conclusion it can reach and
`isRelativelyCompact_of_approx` an input. The form in which those two read it is
`SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal` of **SkorokhodSpace**
Milestone 9, 2026-09-19, which carries both sides of the equivalence over `ℝ≥0`
and asks its hypothesis as `SkorokhodSpace.IsCompactContained`.

**What a run at either has to do first, and it is measured and not guessed:
the two compact containments are not the same statement.** `CompactContainment`
of this file is about a **process** under **one** measure, over a **one sided**
window along a set `D`, and with a real `ε`:

> `∀ ε > 0, ∀ T, ∃ K, IsCompact K ∧ 1 - ε < (P {ω | ∀ t ∈ Set.Iic T ∩ D, X t ω ∈ K}).toReal`

The hypothesis `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` carries is
about a **set of laws on the path space**, over the **two sided** window
`exhaustion 0 m` and every time in it, with `ε : ℝ≥0∞` and the complement:

> `∀ ε > 0, ∀ m : ℕ, ∃ K, IsCompact K ∧ ∀ μ ∈ S, μ {f | ∀ t ∈ exhaustion 0 m, f t ∈ K}ᶜ ≤ ε`

Four differences, and three of them are translation: the measure of the
complement against `1 -` the measure, `ℝ≥0∞` against `ℝ`, and one law against a
family — the family version has to be **uniform in `n`**, which
`CompactContainment` as stated does not express at all, being a predicate on one
process. The fourth is not translation: the window. Over the index `ℝ≥0` the two
sided window reaches times the one sided one does not, and the passage is
Milestone 9 of **SkorokhodSpace** — under
`SkorokhodSpace.isClosedEmbedding_extendNNReal` a path is continued to the
negative axis by its value at `0`, so the negative half of the window is
answered by the time `0` and by nothing else. A run at Milestone 11 states the
uniform, path space form first and derives it; it does not read
`CompactContainment` into the criterion directly.

**This is done, 2026-09-19, and it is done in SkorokhodSpace and not here**,
because three of the four differences are about the path space and the fourth is
about the index. What a run at Milestone 11 now holds:

* `SkorokhodSpace.IsCompactContained` — the uniform, path space form, a predicate
  on a **family** of laws. It is what the item above asked to be stated first,
  and its being about a family rather than about one process is what
  `CompactContainment` could not express.
* `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal` — stage (B) of
  **SkorokhodSpace** Milestone 8 with both sides over `ℝ≥0`, so that
  `isRelativelyCompact_of_approx` reads it without crossing the index itself. The
  windows are crossed by
  `SkorokhodSpace.preimage_extendNNReal_setOf_forall_mem_exhaustion`, which is an
  equality of sets and not an inclusion.
* `SkorokhodSpace.isCompactContained_of_isTightMeasureSet` — compact containment
  is **necessary** for tightness, so carrying it costs the criterion nothing; and
  `SkorokhodSpace.isCompactContained_const` shows it is free for one law repeated,
  which locates the condition where it belongs, in the uniformity in `n`.

**The translation of `CompactContainment` itself is the fourth difference, and it
is done, 2026-09-19.** A family `X n` of processes over `ℝ≥0`, each satisfying
`CompactContainment` with its own compact sets, does **not** give
`SkorokhodSpace.IsCompactContained` of the family of path laws — the compact set
has to be chosen once for all `n`. What stands:

* `UniformCompactContainment` — the hypothesis, kept **verbatim from
  `CompactContainment`** except for the quantifier order, so that
  `UniformCompactContainment.compactContainment` is the instance at a single `n`
  and not a second translation. It is `∃ K, ∀ n` where `CompactContainment` at
  each `n` is `∀ n, ∃ K`, and that is its whole content.
* It is stated about **path space valued variables**
  `X : (n : γ) → Ω n → D(ℝ≥0, E)` and not about processes `ι → Ω n → E`, and the
  reason is measured rather than aesthetic: this file has no general path map of
  a process into `D(ℝ≥0, E)` and cannot have a **total** one — a process with
  only almost surely càdlàg paths needs a value on the exceptional set, which is
  why `jumpPathD` puts `SkorokhodSpace.const` there. The two statements of
  Milestone 6 that this milestone consumes,
  `tendstoInDistribution_evalPi_jumpPathD` and
  `tendstoInDistribution_eval_jumpPathD`, already quantify over path space valued
  variables for the same reason; the hypothesis is stated where the chain reads
  it.
* `isCompactContained_map_of_uniformCompactContainment` — the passage to
  `SkorokhodSpace.IsCompactContained` of the image laws. It spends exactly two
  things and both are named: `Dense D`, which buys the times of the window
  outside `D`, and the measurability of `X n`, which carries the bound to the
  image law by `MeasureTheory.Measure.map_apply` at the window set — measurable
  by `SkorokhodSpace.measurableSet_setOf_forall_mem_exhaustion_nnreal`. The set
  `{ω | ∀ t ∈ Set.Iic T ∩ D, X n ω t ∈ K}` is **not** asserted measurable and is
  not used as if it were: it is only bounded above by the measurable preimage of
  the window.
* **The window is bought at a horizon one unit longer**, and that is the shape of
  the argument rather than a convenience. The value at the right endpoint of a
  closed window is what a dense set does not reach, so the closed form of the
  dense window lemma cannot be used; the uniform hypothesis is applied at `m + 1`
  and `SkorokhodSpace.forall_mem_Ico_of_forall_mem_dense` reads `[0, m]` inside
  the half open `[0, m+1)`. The enlargement is free because the hypothesis is
  quantified over all horizons.
* `uniformCompactContainment_of_isCompactContained_map` and
  `uniformCompactContainment_iff_isCompactContained_map` — the converse, for any
  `D` whatever and **without density**, and hence the equivalence. This is what
  says the uniform hypothesis is the right one and not merely a sufficient one:
  it is the hypothesis the criterion carries, in the shape a consumer of this
  file can discharge. The level is halved and capped below `1` because
  `CompactContainment` asks a strict inequality where the path space form gives a
  weak one.
* `uniformCompactContainment_of_forall_map_eq` — the emptiness test, and it
  locates the condition: a family all of whose members have the **same** law has
  the hypothesis for nothing, by `SkorokhodSpace.isCompactContained_const`. A
  single process never fails it; what the hypothesis excludes is the escape of
  mass **along the index**.

* `SkorokhodSpace.mpTest` — the functional a martingale problem tests, read on
  the path space: `f (z t) - ∫_0^t g (z u) du` as a function of the path alone.
  It is defined in **SkorokhodSpace** Milestone 8, before any filtration exists,
  because the statements about *where it is continuous* are statements about the
  path space and nothing else.
* `rightDense_of_dense` — over a densely ordered index without a greatest
  element, plain density **is** right density. The right density that
  `isDetermining_evalFuns` and
  `SkorokhodSpace.borel_eq_iSup_comap_eval_of_countable_rightDense` ask of a set
  of times is strictly stronger in general — an index with a right isolated
  point separates the two — and over `ℝ` and `ℝ≥0` it is not. This is what makes
  the time set of the third item free:
  `SkorokhodSpace.exists_countable_dense_continuity` delivers `Dense` and not
  right dense, and the gap is one line.
* `cadlagFiltration` — the coordinate filtration of `D(ℝ≥0, E)`, `naturalFiltration`
  at `SkorokhodSpace.measurable_eval`, with `cadlagFiltration_eq` and
  `measurable_cadlagFiltration`.
* `naturalFiltration_comp_eq_comap` — the natural filtration of the path of a
  process **is** the coordinate past pulled back along the path map. This is what
  says the filtration hypothesis of the two items below is inhabited at the
  canonical choice; the proof is that `MeasurableSpace.comap` commutes with a
  supremum and with a composition.
* `tendsto_toNNReal_nhdsGE`, `tendsto_comp_toNNReal_nhdsGE` and
  `measurable_compensator_cadlagFiltration` — the compensator is measurable for
  the coordinate past at the time the window ends. This is the expensive half of
  the adaptedness, and it is `measurable_uncurry_min_of_rightContinuous` of
  Milestone 4 read at a càdlàg path instead of a step path: the truncation
  `min u t` keeps every coordinate the integrand reads below `t`, and off the
  window it changes nothing. **Only right continuity is spent**; no left limit
  is read, which is why the item below asks its no jump condition at the single
  time the *evaluation* reads.
* `measurable_mpTest` and `abs_mpTest_le` — the tested functional is measurable
  for the past at the time it is read, and bounded by `‖f‖ + ‖g‖ * t` uniformly
  in the time below `t` and **in the path**. The bound is the counterpart of
  `abs_mpFamily_coordinate_le` over the càdlàg path space, and it is what makes
  the integrability and the uniform integrability of
  `mpSolution_of_tendsto` carry no information here: the tails above it are not
  small but zero.
* `mpSolution_of_tendsto_cadlag`: let `X n` have càdlàg paths, let their laws
  converge weakly to the law of `X` on `D(ℝ≥0, E)`, let `T` be countable, right
  dense and free of fixed discontinuities of the limit law, and let the tested
  increments
  `∫ (mpTest f g t (X n) - mpTest f g s (X n)) * Z (X n) d(P n)`
  tend to `0` for every `Z` of `SkorokhodSpace.evalFuns E (insert s (T ∩ Set.Iic s))`.
  Then `X` satisfies the martingale identity of the martingale problem to
  `(f, g)` along `T`. **Proved 2026-09-21.**

  **The filtration is a hypothesis and is the coordinate past pulled back along
  the path map.** That is the weakest form: it is what
  `isDetermining_evalFuns` reads, it is what makes the tested process adapted,
  and it leaves the consumer free in how the filtration is built;
  `naturalFiltration_comp_eq_comap` inhabits it. **Adaptedness is not a
  hypothesis** and is derived from it.

  **What the consumer supplies is the vanishing of the tested increments and
  nothing else that is analytic.** The other three hypotheses of
  `mpSolution_of_tendsto_of_pContinuous` are discharged from the path space
  alone — integrability and uniform integrability from `abs_mpTest_le`,
  `P`-continuity from **SkorokhodSpace** Milestone 8, and the determining
  property from `isDetermining_evalFuns`.
* `SkorokhodSpace.integrableOn_mpTest_integrand`,
  `SkorokhodSpace.mpTest_sub` and `abs_mpTest_sub_mpTest_le` — the tested
  functional is **linear in the pair it tests**, and the error of testing with
  the wrong pair is `‖f - f'‖ + ‖g - g'‖ * t`, uniformly in the time below `t`
  and **in the path**. The first two are statements about the path space alone
  and stand in **SkorokhodSpace** Milestone 8; the third is the second read
  through `abs_mpTest_le`. The integrability is what makes the linearity a
  statement about the *integrals* and not only about the integrands, the
  Bochner integral of a non integrable function being `0`; it is
  `IsCadlag.measurable` of **SkorokhodSpace** Milestone 2 together with the
  bound `‖g‖` on a window of finite measure. **Boundedness of `f'` and `g'` is
  not read**, only of the differences, which is what makes the error vanish
  along an approximating sequence.
* `measurable_cadlagFiltration_of_mem_evalFuns` — a finite dimensional test
  function of times below `s` is measurable for the coordinate past at `s`.
  This is `measurable_cadlagFiltration` at each factor and
  `Finset.measurable_prod`; the hypothesis is on the set of times, so
  `insert s (T ∩ Set.Iic s)` qualifies.
* `tendsto_integral_mpTest_sub_mul_of_approx` — the tested increments of an
  approximating family vanish, which is the hypothesis `hzero` of the previous
  item. **Proved 2026-09-21.**

  The approximants are martingale solutions to the pairs `(f' n, g' n)` and are
  tested with the limiting pair `(f, g)`. **The step is an estimate and not a
  limit theorem**, and that is what makes it cheap: the exact increment, tested
  with `(f' n, g' n)` against a test function of the past, integrates to
  **zero** and not to something small, by
  `integral_sub_mul_eq_zero_of_martingale`; what is left is bounded pointwise
  by `2 * (‖f - f' n‖ + ‖g - g' n‖ * t) * ‖Z‖`, uniformly in `n` and in the
  sample point, and the limit is `squeeze_zero_norm`.

  **The filtration of the approximants is read at exactly one place**, the
  measurability of `Z ∘ X' n` for the past at `s`, and the hypothesis `h𝓕'` is
  the same as `h𝓕` of the previous item, one for each `n`;
  `naturalFiltration_comp_eq_comap` inhabits it. **The times carry no
  hypothesis here at all**: only `S ⊆ Set.Iic s` is read, so countability,
  right density and the absence of fixed discontinuities belong to the previous
  item alone.
* `mpSolution_of_tendsto_cadlag_of_approx`: the wrapper in which the
  approximants solve an approximating problem rather than the limiting one. If
  the `X' n` are martingale solutions to the pairs `(f' n, g' n)` with
  `‖f - f' n‖ → 0` and `‖g - g' n‖ → 0`, and their path laws converge weakly on
  `D(ℝ≥0, E)`, then the limit satisfies the martingale identity of the
  martingale problem to `(f, g)` along `T`. It is the previous two items
  composed, and it adds nothing analytic. **Proved 2026-09-21.**

  **Its two filtration hypotheses point in opposite directions, and that is
  what makes the chain join, 2026-09-21.** The one on the limit is an
  *equality* — the coordinate past pulled back along the path map — because the
  determining class has to generate that filtration. The one on the
  approximants is an *inclusion*: all that is read of it is that a finite
  dimensional test function of the past be measurable, so the filtration of the
  approximants has only to **contain** the coordinate past. The weaker form is
  not a nicety. The filtration the second item hands over is **right
  continuous**, and the natural filtration of a càdlàg path is not; with an
  equality the two items could be joined only by carrying a martingale from the
  given filtration down to the natural one, which is true by the tower property
  but is a theorem, and Mathlib has none (checked 2026-09-21 at
  `Mathlib/Probability/Martingale/Basic.lean`, where the filtration is fixed
  throughout the file). `comap_pathOfProcess_le_of_stronglyAdapted` is the
  inclusion at the data of the second item, and it is three rewrites.

  **The `P`-continuity this derivation needs is proved, 2026-09-21**, in
  **SkorokhodSpace** Milestone 8, and it decides which of the two versions of
  Milestone 10 the item reads: `mpSolution_of_tendsto_of_pContinuous`, not
  `mpSolution_of_tendsto`, because the hypothesis that is available on the path
  space is weak convergence of the *paths* and the functionals are continuous
  only off the jumps. The five statements:
  `SkorokhodSpace.continuousAt_setIntegral_toNNReal`,
  `SkorokhodSpace.continuousAt_mpTest`,
  `SkorokhodSpace.measure_setOf_forall_notMem_leftJumpSet_comp_eq_one`,
  `SkorokhodSpace.measure_setOf_continuousAt_mpTest_eq_one` and
  `SkorokhodSpace.measure_setOf_continuousAt_mpTest_mul_eq_one`.

  **The compensator carries no jump condition at all**, and that is the finding
  that shapes the item: `SkorokhodSpace.continuousAt_integral_comp` is continuous
  at *every* path, the jumps of the limit path being a countable — hence
  Lebesgue null — set of times. So the set `D` is asked for by the **evaluation**
  alone, and it is asked at the single time the test function reads.

  **The determining class is proved, 2026-09-21**: `MeasureTheory.isDetermining_evalFuns`
  of Milestone 10 below gives `MeasureTheory.IsDetermining` for
  `SkorokhodSpace.evalFuns E (insert s (T ∩ Set.Iic s))` whenever `T` is right
  dense and the filtration is the pull back of the coordinate past. With it, both
  hypotheses of `mpSolution_of_tendsto_of_pContinuous` are met by **one and the
  same** class, which was the obstruction: the earlier witnesses for
  `IsDetermining` take all bounded measurable functions of the past, or
  indicators, and neither is continuous anywhere it has to be. The remaining
  bookkeeping of `mpSolution_of_tendsto_of_pContinuous` — the integrability and
  the uniform integrability of the tested functionals along the approximating
  sequence — is `abs_mpTest_le`, whose tails are zero rather than small; the
  convergence of the integrals is what `mpSolution_of_tendsto_cadlag` carries as
  its hypothesis and `mpSolution_of_tendsto_cadlag_of_approx` discharges.
* `mpSolution_of_tendsto_cadlag_of_pathwise`: the same with the uniform
  convergence of `f n` and `g n` replaced by
  `𝔼^{P n}‖(f n - f) (X n t)‖ → 0` and
  `𝔼^{P n} ∫_0^t ‖(g n - g) (X n u)‖ du → 0`. No further hypothesis is needed:
  uniform integrability is bought by boundedness of `f` and `g`, not of `f n`
  and `g n`. State also the sufficient condition: uniform boundedness of the
  `f n`, `g n`, locally uniform convergence, and compact containment of the
  family `{X n}`.
* `mpSolution_of_tendsto_cadlag_asymptotic`: the version in which the
  approximating martingales are arbitrary progressively measurable pairs
  `(ξ n, φ n)` with `ξ n - ∫_0^· φ n` a martingale, subject to
  `sup_n sup_{s ≤ T} 𝔼[|ξ n s| + |φ n s|] < ∞` and the two asymptotic conditions
  testing `ξ n - f (X n)` and `∫ (φ n - g (X n))` against products
  `∏ h i (X n (t i))`.
* `isTight_map_postcomp_of_exists_martingale`, the criterion the previous items
  and the next one consume. Let `X n` have càdlàg paths and be adapted to
  `𝓕 n`, let `𝓛 n` be the real `(𝓕 n)`-progressive processes with
  `‖Y‖ = ⨆ t, 𝔼[|Y t|] < ∞`, and let
  `𝓐 n = {(Y, Z) ∈ 𝓛 n × 𝓛 n | Martingale (fun t ↦ Y t - ∫ s in Clock.interval q c 0 t, Z s) (𝓕 n) (P n)}`.
  Call `f : E →ᵇ ℝ` *approximable* when for all `ε, T > 0` there are
  `(Y n, Z n) ∈ 𝓐 n` with
  `⨆ n, ∫⁻ ω, ⨆ t ∈ Set.Iic T ∩ D, ‖Y n t ω - f (X n t ω)‖ₑ ∂(P n) < ε` and
  `⨆ n, 𝔼[eLpNorm (Set.Iic T).indicator (Z n) p] < ∞` for some `1 < p ≤ ∞`.
  Let the approximable functions be closed under products — the reason is below,
  under „The one remaining quantity", and it is a witness and not a
  convenience. Then for every `f` in the sup-norm closure of the approximable
  functions the
  laws of `postcomp f ∘ X n` are tight in `D ι ℝ`, and the laws of
  `(f 1, …, f k) ∘ X n` are tight in `D ι (Fin k → ℝ)`. The `𝕂`-valued case is
  the real one applied to `Re f` and `Im f` together with the `Fin k` form.
  This is where the continuous time Doob inequalities of Milestone 9 are used.

  **The name under which it stands, 2026-09-21.** The general form, taking the
  two pairs and the two errors as hypotheses, is
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_exists_bounded_pair`;
  the form whose hypothesis is a **martingale** and whose error is zero is
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_martingale`. Both carry
  `IsTightMeasureSet` in the name because that is the conclusion and because the
  file names its statements after it throughout. What is still open of the item
  as stated here is the passage to the **sup-norm closure** of the approximable
  functions and the `Fin k` valued form; the single real `f` is done.

  **The first condition is a lower integral in `ℝ≥0∞`, and that is not
  cosmetic.** Written over `ℝ` as `𝔼[⨆ t ∈ Set.Iic T ∩ D, |Y n t - f (X n t)|]`
  it is satisfied by a family whose approximation error is *unbounded* on the
  window, because `Real.iSup_of_not_bddAbove` makes the supremum `0` there and
  the integral with it. The witness is `biSup_natCast_eq_zero` of Milestone 9,
  and the honest form is the one above: in `ℝ≥0∞` an unbounded supremum is `⊤`
  and the condition excludes exactly what it is meant to. The same reading
  applies to the second condition, which is already an `eLpNorm` and therefore
  already in `ℝ≥0∞`.

  **What the criterion may assume about the supremum, and what it has to prove.**
  The quantity is measurable because `D` is countable
  (`measurable_biSup_enorm_of_countable`), and it is the supremum over the whole
  window because the paths are right continuous
  (`biSup_enorm_Iic_eq_of_isRightContinuous`, which reads the right endpoint
  separately). What the criterion has to produce from it is the maximal
  estimate, and its discrete half is available over an arbitrary linear order
  since 2026-09-20: `Submartingale.mul_measReal_exists_ge_abs_le_countable`,
  `ε * P {ω | ∃ s ∈ S, ε ≤ |Y s ω|} ≤ 2 𝔼[(Y T)⁺] - 𝔼[Y R]` for countable `S`
  between `R` and `T`. It answers the question this milestone opened — whether
  Mathlib's `maximal_ineq`, which is indexed by `ℕ` and reads a `Finset.sup'`,
  can be dragged along `D`: it can, through `Filtration.comp`,
  `Finset.monoEnum` and continuity from below, and the passage needs no
  measurability of the level set. Its continuous time form is
  `Submartingale.mul_measReal_lt_biSup_enorm_le` and
  `Submartingale.mul_measReal_le_biSup_enorm_le` of Milestone 9, which read the
  window supremum directly.

  The `Lᵖ` half is `lintegral_rpow_le_of_weak_type` of Milestone 9, which turns
  either maximal estimate into `∫⁻ M^p ≤ (p/(p-1))^p ∫⁻ g^p` and carries no
  probability, together with its instance over `ℕ`,
  `Submartingale.lintegral_rpow_range_sup'_le`, its `eLpNorm` form
  `Submartingale.eLpNorm_range_sup'_le`, and the window bound itself,
  `Submartingale.lintegral_biSup_enorm_rpow_le`. Mathlib has none of these for
  any index (checked 2026-09-20 against
  `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`: the docstring of `maximal_ineq`
  says the `Lᵖ` inequality "will be proved in an upcoming PR", and `eLpNorm`
  occurs in `Mathlib/Probability/Martingale/` only in `BorelCantelli.lean` and
  `Convergence.lean`).

  **The window bound is read in `ℝ≥0∞`, and this criterion is to read it there
  too.** Its approximability condition is already a lower integral in `ℝ≥0∞`
  for the same reason — a real valued supremum vanishes where the path escapes
  — so the two fit without a `toReal` anywhere between them.

  **What the conclusion costs, measured 2026-09-20: one of its two conjuncts is
  free, and the item is therefore exactly the other one.** The tightness this
  item asserts is read through `SkorokhodSpace.isTightMeasureSet_iff`, whose
  first conjunct is compact containment and whose second is the modulus
  condition. On the **image** side the first is free: `f : E →ᵇ ℝ` sends every
  value into `Set.Icc (-‖f‖) ‖f‖`, so the window set of the image law carries the
  whole mass. That is
  `SkorokhodSpace.isCompactContained_map_postcomp_of_measurableSet` of
  **SkorokhodSpace** Milestone 9, with **no hypothesis on the family at all**,
  and its two instances
  `SkorokhodSpace.isCompactContained_map_postcomp_nnreal` and
  `SkorokhodSpace.isCompactContained_map_postcomp_real`.

  What this item therefore has to produce, and the **only** thing it has to
  produce, is the right hand side of
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff`:

  > for every `ε, η > 0` and every window radius `m` there is `δ > 0` with
  > `P n {modulusBased 0 m (extendNNReal (postcomp f (X n ·))) δ ≥ η} ≤ ε`
  > for **every** `n`.

  That equivalence carries no hypothesis whatever, so nothing of the consumer's
  compact containment is spent here; `UniformCompactContainment` is spent on the
  **original** family, in
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal`, and the two must
  not be confused.

  **And the route from the Doob estimate to that quantity is named, its
  deterministic half built 2026-09-20.** What a maximal estimate gives is a bound
  on increments at stopping times; what the display above asks for is a bound on
  the modulus. The passage between them is Aldous' criterion, whose statement for
  this chain is `SkorokhodSpace.modulusBased_le_of_forall_stoppingTime` of
  **SkorokhodSpace** Milestone 10. Its deterministic half — everything in it that
  does not mention a measure — is
  `SkorokhodSpace.modulusBased_le_of_forall_gapped` with its two feeders
  `SkorokhodSpace.subdivisionOsc_le_of_forall_cell` and
  `SkorokhodSpace.modulusBased_le_of_forall_cell`, the counting bounds
  `mul_le_dist_of_gapped` and `card_le_of_gapped`, and the specialisation to the
  index this item has,
  `SkorokhodSpace.modulusBased_extendNNReal_le_of_forall_gapped`. They take the
  hitting times as a sequence `τ : ℕ → ℝ≥0` with a count `N`, which is the shape
  those times have, and ask of them only what a second application of the
  increment bound at a random time delivers: that consecutive ones do not lie
  within `δ`. What is left for this item is therefore that one probabilistic
  estimate, and the count of terms in the union it is summed over is
  `card_le_of_gapped`.

  **And the times are stopping times**, 2026-09-20, which is what had to hold
  before that estimate could be evaluated at them at all. They are the hitting
  times of an **open** set, so this is the début theorem, and Mathlib has only
  the discrete case — both `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`
  and `MeasureTheory.Adapted.isStoppingTime_hittingAfter` carry `[Countable ι]`
  and `[WellFoundedLT ι]`, and the words `debut` and `début` do not occur in
  the library. What Mathlib *does* have is the reduction the theorem is proved
  by, `MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous`
  together with `MeasureTheory.Filtration.rightCont`; the missing passage is
  from a right-open random set to `{τ < i} ∈ 𝓕 i`, and it is
  `MeasureTheory.setOf_debutTime_lt_eq` — pure order topology, one density
  argument. The four declarations that carry this are
  `MeasureTheory.debutTime` with `MeasureTheory.isStoppingTime_debutTime`, and
  for the oscillation set `MeasureTheory.isRightOpen_oscSet`,
  `MeasureTheory.measurableSet_mem_oscSet` and the cell bound
  `MeasureTheory.dist_le_of_lt_debutTime_oscSet`; they stand under „The début of
  a right-open random set" and „The Aldous hitting times as an instance of the
  début".

  **The price is named and not hidden**: the times are stopping times for the
  right continuous filtration, so a consumer without `[𝓕.IsRightContinuous]`
  passes to `𝓕₊` and must have its increment bound at `𝓕₊`-stopping times.

  **Prior art for the general theorem, cited and not presupposed.** The début
  theorem *without* right-openness — for an arbitrary progressively measurable
  random set — is developed in the repository `RemyDegenne/brownian-motion`
  (Apache-2.0, Copyright Rémy Degenne; locally at `~/Code/lean/brownian-motion`,
  branch `master`, `314f04a`, 2026-08-01) in
  `BrownianMotion/Choquet/Debut.lean` (581 lines, **no `sorry`**) with
  `BrownianMotion/Choquet/MeasurableSection.lean` beside it (498 lines, no
  `sorry`). Its `isStoppingTime_debut` goes the measure-theoretically heavy way,
  through Choquet capacities and measurable sections
  (`IsPavingAnalytic.nullMeasurableSet_debut_lt`), carries a `ProgMeasurableSet`
  layer with its own lemmas for the traces on `Iic`, `Iio`, `Ico`, `Icc`, and
  pays for the generality with completion — hence the `nullMeasurable` prefixes.
  It also carries `leastGE`, `leastGT` and `hittingAfter'`.

  **This roadmap deliberately does not need that.** The oscillation sets Aldous
  hits are right open by construction (`isRightOpen_oscSet`) and the filtration
  is right continuous by the choice recorded above, so
  `isStoppingTime_of_measurableSet_lt_of_isRightContinuous` applies directly and
  the Choquet layer never enters — which is why the point the roadmaps had
  flagged as this milestone's most expensive cost one order-topology lemma. The
  general theorem would also cost the completion of the filtration, which
  nothing here has so far needed.

  The reference is worth keeping for the case this roadmap does **not** cover: a
  début of a random set that is not right open, or hitting times of general
  sets. An implementer may consult it and, the licence permitting, draw on it
  with its copyright header preserved; **nothing here should be accepted merely
  because it matches that file.**

  **And the recursion itself stands**, 2026-09-20, in the section „The Aldous
  hitting recursion": `MeasureTheory.oscHitSeq` with `oscHitSeq_zero`,
  `oscHitSeq_succ`, and its four properties
  `MeasureTheory.oscHitSeq_le_succ`, `MeasureTheory.monotone_oscHitSeq`,
  `MeasureTheory.dist_stoppedValue_oscHitSeq_le` and
  `MeasureTheory.isStoppingTime_oscHitSeq`, on the two general lemmas
  `MeasureTheory.le_debutTime_oscSet` and `MeasureTheory.lt_debutTime_oscSet`.
  The anchor of step `k+1` is Mathlib's own `MeasureTheory.stoppedValue`, whose
  `WithTop.untopA` is never read here — `oscSet X σ c ε ω ⊆ {t | σ ω < t}` is
  empty when `σ ω = ⊤`, so the recursion stays at `⊤` once it has run off the
  end, with no case distinction and no finiteness hypothesis.

  **The one open hypothesis of `MeasureTheory.measurableSet_mem_oscSet` is
  discharged inside the induction, and it is the only analytic input.** The
  anchor `stoppedValue X (τ k)` agrees on `{τ k < q}` with
  `stoppedValue X (min (τ k) q)`, which is `𝓕 q`-measurable by
  `MeasureTheory.stronglyMeasurable_stoppedValue_of_le`
  (`Probability/Process/Stopping.lean:1016`), the minimum being a stopping time
  bounded by `q` through `MeasureTheory.IsStoppingTime.min_const` (`:365`); that
  is where `IsStronglyProgressive X` enters and the single step needed only
  `Adapted X`. The anchor itself is `MeasureTheory.stoppedValue` (`:797`), whose
  definition `u (τ ω).untopA ω` is why the `⊤` case needs no clause here.

  **What the recursion delivers and what it does not.** Of the three hypotheses
  `SkorokhodSpace.modulusBased_le_of_forall_gapped` asks for, two are now free:
  the cell bound is `dist_stoppedValue_oscHitSeq_le` — stated on the half-open
  interval, its left endpoint included at the cost of `0 ≤ ε` — and strict
  monotonicity is `MeasureTheory.lt_oscHitSeq_succ`. The third, `δ`-sparseness,
  is the probabilistic estimate and is what remains of this item.

  **And the deterministic half is now one implication**, 2026-09-20:
  `MeasureTheory.modulusBased_extendNNReal_le_of_oscHitSeq`. If the Aldous times
  of `X` at level `ε` are finite up to stage `N` at a sample point, `δ`-sparse
  below `N`, and have overtaken the horizon `u` at `N`, then
  `SkorokhodSpace.modulusBased 0 u (SkorokhodSpace.extendNNReal f) δ ≤
  ENNReal.ofReal ε` for any càdlàg `f` with `f.toFun = fun t ↦ X t ω`.
  Everything in the criterion that does not mention a measure now stands in one
  chain from
  `MeasureTheory.isStoppingTime_oscHitSeq` to the modulus, and the single
  hypothesis of that implication which a measure has to discharge is `hgap`.

  **It spends neither `0 < ε` nor any regularity of the paths, and that relocates
  where the right continuity is paid.** Strict monotonicity of the times is a
  *consequence* of `hgap` there: the times are weakly monotone for free
  (`MeasureTheory.oscHitSeq_le_succ`) and a positive gap makes consecutive ones
  distinct. `MeasureTheory.lt_oscHitSeq_succ` is therefore not an input of the
  deterministic half but the reason `hgap` is not vacuous — the probabilistic
  estimate has to bound the probability that a gap is *short*, and without strict
  monotonicity the gap could be `0` with probability one.

  **Finiteness is carried in the hypothesis and not in a `WithTop.untopA`.** The
  standing rule of this development applies to `debutTime` as to every other
  function totalised by `sInf`, and the two lemmas that make it cheap are
  `MeasureTheory.oscHitSeq_ne_top_of_le` — finiteness at a stage is finiteness at
  every earlier one, `monotone_oscHitSeq` read contrapositively — and
  `MeasureTheory.exists_coe_oscHitSeq_of_ne_top`, which turns the single
  statement `oscHitSeq X ε N ω ≠ ⊤` into the `ℝ≥0`-valued times up to `N`.

  **At the last stage, however, `⊤` is the *good* case**, and the general form
  `MeasureTheory.modulusBased_extendNNReal_le_of_oscHitSeq_le` says so: it asks
  finiteness only *below* `N` and asks of the last time only that it lie at or
  before the `N`-th hitting time. Where the recursion is `⊤` at `N` the path
  never again moves by more than `ε` after the previous time, so any point beyond
  the horizon closes the subdivision and the modulus is bounded a fortiori; a
  statement that asks the times to be `ℝ≥0`-valued up to and including `N`
  excludes exactly that case. Its gap hypothesis is the ordered
  `τ k + δ < τ (k+1)` rather than the `dist` form — not a strengthening, since
  under the monotonicity of the recursion the two agree, but what makes the last
  cell go through, where `hlast` is an inequality in the wrong direction to
  supply monotonicity. The convenient form
  `MeasureTheory.modulusBased_extendNNReal_le_of_oscHitSeq` is its corollary.

  **And the implication is read as a set inclusion**, 2026-09-20:
  `MeasureTheory.setOf_lt_modulusBased_subset_oscHitSeq`. For a family of paths
  `Φ : Ω → D(ℝ≥0, E)` with `(Φ ω).toFun = fun t ↦ X t ω`, `0 ≤ ε` and
  `0 ≤ δ < u`,

  ```
  {ω | ENNReal.ofReal ε < SkorokhodSpace.modulusBased 0 u
        (SkorokhodSpace.extendNNReal (Φ ω)) δ}
    ⊆ (⋃ k ∈ Finset.range N,
        ({ω | oscHitSeq X ε (k+1) ω ≤ oscHitSeq X ε k ω + ↑δ.toNNReal}
          ∩ {ω | oscHitSeq X ε k ω < ↑u.toNNReal}))
      ∪ {ω | oscHitSeq X ε N ω < ↑u.toNNReal}.
  ```

  It is the contrapositive of the general form and **of that form only**: with
  the form that asks finiteness up to and including `N`, a third and alien term
  `{ω | oscHitSeq X ε N ω = ⊤}` would stand on the right and its probability
  would have to be estimated separately; here `⊤` at stage `N` belongs to the
  good side. The last time is the `k₀`-th hitting time **cut off** at a point
  beyond the horizon, which is finite whether or not the recursion has run off
  the end, and `MeasureTheory.exists_coe_oscHitSeq_of_ne_top` is not used in the
  proof.

  **The horizon condition inside each gap event is not decoration.** Without
  `{ω | oscHitSeq X ε k ω < ↑u.toNNReal}` the gap event contains every sample
  point at which `oscHitSeq X ε k ω = ⊤`, since `⊤ ≤ ⊤ + δ` holds in
  `WithTop ℝ≥0`. Those are the *good* points — the path never again moves by more
  than `ε` — and an estimate of the unrestricted event would have to bound their
  probability, which is neither small nor what a maximal inequality produces. It
  is also what carries the proof: the subdivision stops not at `N` but at the
  **first** stage `k₀ ≤ N` at which the horizon has been overtaken, below which
  every time is `< u` and therefore finite.

  **And the estimate itself**, 2026-09-20:
  `MeasureTheory.measure_setOf_lt_modulusBased_le_oscHitSeq`, three lines from
  the inclusion and **with no measurability hypothesis at all**,

  ```
  μ {ω | ENNReal.ofReal ε < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ ∑ k ∈ Finset.range N,
        μ ({ω | oscHitSeq X ε (k+1) ω ≤ oscHitSeq X ε k ω + ↑δ.toNNReal}
            ∩ {ω | oscHitSeq X ε k ω < ↑u.toNNReal})
      + μ {ω | oscHitSeq X ε N ω < ↑u.toNNReal}.
  ```

  Neither the modulus nor the gap events are asked to be measurable, because
  `MeasureTheory.measure_mono` (`MeasureTheory/OuterMeasure/Basic.lean:51`) and
  `MeasureTheory.measure_biUnion_finset_le` (`:80`) are stated for
  `OuterMeasureClass` and hold of arbitrary sets; the right hand side of
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff` applies its measure in
  exactly that way. A consumer reads the criterion's set
  `{f | η ≤ modulusBased 0 u f δ}` through this at any `ε` with
  `ENNReal.ofReal ε < η`.

  Two estimates are therefore left for a measure, one per kind of summand: the
  **gap** probabilities, `N` of them, which is where Doob from Milestone 9 is
  consumed, and the single **horizon** probability. How many terms of the first
  kind there can be is the deterministic `card_le_of_gapped` of
  **SkorokhodSpace**.

  **And the gap events are made estimable**, 2026-09-20:
  `MeasureTheory.le_dist_stoppedValue_oscHitSeq`, with the general
  `MeasureTheory.le_dist_debutTime_oscSet` underneath it. If the paths are right
  continuous and `oscHitSeq X ε (k+1) ω = (t : WithTop ι)` is a time, then

  ```
  ε ≤ dist (X t ω) (stoppedValue X (oscHitSeq X ε k) ω).
  ```

  This is the counterpart of `MeasureTheory.dist_stoppedValue_oscHitSeq_le` —
  below `τ (k+1)` the path stays within `ε` of the anchor, **at** `τ (k+1)` it is
  at least `ε` away — and neither is the negation of the other, since `oscSet` is
  defined by a *strict* inequality. It is what turns the gap event
  `{τ (k+1) ≤ τ k + δ}` into the quantity Aldous' criterion hypothesises about,
  and `MeasureTheory.setOf_oscHitSeq_gap_subset_dist` below is that passage
  written out — together with the horizon hypothesis it needs.

  **And this is where the right continuity of the paths is really paid.** The
  deterministic half does not use it; `MeasureTheory.lt_oscHitSeq_succ` uses it
  only to say that the gap hypothesis is not vacuous. Here it carries the
  argument: `oscSet` is right-open, so `ε < dist` is witnessed only strictly to
  the right of the début, an infimum of a right-open set need not be attained,
  and the value at the début is reached by a passage to the limit along
  `𝓝[oscSet X σ c ε ω] t`. That filter is `NeBot` because a greatest lower bound
  lies in the closure of its set (`IsGLB.mem_closure`,
  `Topology/Order/IsLUB.lean:55`), so no sequence and no first countability are
  needed; what does not survive the limit is the strictness. `0 < ε` is not used
  either.

  **The Mathlib lemma the stopping time `σ` above needs is supplied here**,
  2026-09-20: `MeasureTheory.IsStoppingTime.add_const_of_orderedSub`.
  `σ = min (τ (k+1)) (τ k + δ)` is a stopping time by
  `MeasureTheory.IsStoppingTime.min` once `fun ω ↦ τ k ω + δ` is one, and over
  `ℝ≥0` Mathlib has no such statement. There are exactly two lemmas of that
  shape, and both are unusable here:
  `MeasureTheory.IsStoppingTime.add_const`
  (`Probability/Process/Stopping.lean:389`), which asks `[AddGroup ι]`, and
  `MeasureTheory.IsStoppingTime.add_const'` (`:403`), which asks
  `[Countable ι]`. `ℝ≥0` is neither. The statement here is the one over a
  canonically ordered additive monoid with truncated subtraction,

  ```
  [AddCommMonoid ι] [LinearOrder ι] [CanonicallyOrderedAdd ι]
  [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι] :
    IsStoppingTime f τ → ∀ i : ι, IsStoppingTime f fun ω ↦ τ ω + i,
  ```

  and its proof is a case distinction the group proof does not need: for `i ≤ j`
  the set `{τ + i ≤ j}` is `{τ ≤ j - i}` by `le_tsub_iff_right`, carried by the
  filtration because `tsub_le_self`, and for `j < i` it is **empty** because
  `i ≤ τ ω + i` in a canonically ordered monoid. The equivalence
  `a + i ≤ j ↔ a ≤ j - i` is false over `ℝ≥0` without `i ≤ j` — the right hand
  side becomes `a ≤ 0` — which is why the group proof does not transfer verbatim.
  `AddLeftReflectLE` is what `le_tsub_iff_right` asks for and is an instance over
  `ℝ≥0`.

  **And the gap event is turned into the distance between two stopping times**,
  2026-09-20: `MeasureTheory.setOf_oscHitSeq_gap_subset_dist`. With
  `α = min (τ k) u` and `β = min (τ (k+1)) (α + δ)` — both stopping times, with
  `α ≤ β ≤ α + δ` and both bounded by `u + δ` —

  ```
  {ω | τ (k+1) ω ≤ τ k ω + δ} ∩ {ω | τ k ω < u}
    ⊆ {ω | ε ≤ dist (stoppedValue X β ω) (stoppedValue X α ω)}.
  ```

  On the intersection both minima are attained on the left, so `β ω = τ (k+1) ω`
  and `α ω = τ k ω`, and the statement is
  `MeasureTheory.le_dist_stoppedValue_oscHitSeq`. The finiteness of `τ (k+1) ω`
  is not a further hypothesis but follows from `τ (k+1) ω ≤ τ k ω + δ` with
  `τ k ω` finite. `0 < ε` is not used; right continuity of the paths is.

  **The horizon hypothesis cannot be dropped**, and the reason is the standing
  rule of this development: without it the gap event contains the sample points
  at which `τ k ω = ⊤`, where `⊤ ≤ ⊤ + δ` holds and the conclusion is plainly
  false. This is why
  `MeasureTheory.setOf_lt_modulusBased_subset_oscHitSeq` carries the horizon into
  each of its gap events.

  **And the two times are what the criterion asks for**, 2026-09-20:
  `MeasureTheory.isStoppingTime_oscHitSeqCap` and
  `MeasureTheory.isStoppingTime_oscHitSeqGap` say that `α` and `β` are stopping
  times — the first by `MeasureTheory.IsStoppingTime.min_const`, the second by
  `MeasureTheory.IsStoppingTime.min` over
  `MeasureTheory.IsStoppingTime.add_const_of_orderedSub`, which is where that
  lemma is spent. Their order relations are deterministic and carry no
  hypothesis on `X` at all:
  `MeasureTheory.oscHitSeqCap_le_oscHitSeqGap` (`α ≤ β`, from
  `oscHitSeq_le_succ` and `le_self_add`),
  `MeasureTheory.oscHitSeqGap_le_add` (`β ≤ α + δ`, `min_le_right`) and
  `MeasureTheory.oscHitSeqGap_le_coe` (`β ≤ u + δ`). The last is why the cap at
  `u` earns its place twice over: it excludes the explosion set from the gap
  event, and it is what makes the times **bounded**, which is what Doob's
  inequalities and optional sampling ask of a stopping time.

  **And Markov's inequality is applied on the gap event**, 2026-09-20:
  `MeasureTheory.measure_setOf_oscHitSeq_gap_le`, in the shape Mathlib states
  it — the level as a **factor on the left** and not a reciprocal on the right,

  ```
  ENNReal.ofReal ε * μ ({ω | τ (k+1) ω ≤ τ k ω + δ} ∩ {ω | τ k ω < u})
    ≤ ∫⁻ ω, ENNReal.ofReal (dist (stoppedValue X β ω) (stoppedValue X α ω)) ∂μ.
  ```

  It is `MeasureTheory.mul_meas_ge_le_lintegral`
  (`MeasureTheory/Integral/Lebesgue/Markov.lean:59`; the `₀` form with
  `AEMeasurable` at `:52`) applied to the **level set** of the distance, with
  `MeasureTheory.measure_mono` along
  `MeasureTheory.setOf_oscHitSeq_gap_subset_dist` carrying the gap event into
  it. The gap event is therefore **not asked to be measurable** — only the
  distance of the two stopped values is, which is
  `MeasureTheory.stronglyMeasurable_dist_stoppedValue_oscHitSeqGap`, and its
  input is `MeasureTheory.stronglyMeasurable_stoppedValue_of_le`
  (`Probability/Process/Stopping.lean:1016`) at the bounds `u` and `u + δ`.
  That is the third time the cap at the horizon pays for itself: it excludes
  the explosion set, it makes the times bounded, and it is what makes them
  measurable at a fixed index of the filtration. `0 < ε` is not used; at
  `ε ≤ 0` the statement is true and empty.

  **And the gap summands are discharged in the estimate itself**, 2026-09-20:
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist`,

  ```
  ENNReal.ofReal ε * μ {ω | ENNReal.ofReal ε < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ ∑ k ∈ Finset.range N, ∫⁻ ω, ENNReal.ofReal (dist (X β_k ω) (X α_k ω)) ∂μ
      + ENNReal.ofReal ε * μ {ω | oscHitSeq X ε N ω < ↑u.toNNReal},
  ```

  which is `measure_setOf_lt_modulusBased_le_oscHitSeq` with the inequality
  above summed over the `N` gap terms. **The level multiplies rather than
  divides**: `ENNReal` division is total and therefore lies where the level is
  `0` or `⊤`, so in the product form the statement carries no positivity
  hypothesis at all and a consumer divides at a level it has already assumed
  positive.

  **And the horizon summand is removed rather than estimated**, 2026-09-20:
  `MeasureTheory.setOf_oscHitSeq_lt_subset_iUnion_gap`. If the horizon lies
  within the reach of `N` steps of size `δ`, that is `u ≤ N • δ`, then

  ```
  {ω | τ N ω < u}
    ⊆ ⋃ k ∈ Finset.range N, ({ω | τ (k+1) ω ≤ τ k ω + δ} ∩ {ω | τ k ω < u}),
  ```

  because a recursion all of whose steps exceed `δ` is past `N • δ ≥ u` at
  stage `N`, and every earlier time is below `u` by `monotone_oscHitSeq`, which
  supplies the horizon condition of the gap event for free. **Nothing in it is
  probabilistic and nothing analytic**: no measure, no topology on the index,
  no hypothesis on `X`, not even `0 ≤ ε`. Its base case is `oscHitSeq_zero`
  with `⊥ = 0`, which `CanonicallyOrderedAdd` forces.

  `MeasureTheory.measure_setOf_lt_modulusBased_le_gap` is the estimate that
  follows, with the two occurrences of the same union as a factor `2`, and
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le` is
  the whole probabilistic content of this item in one inequality,

  ```
  ENNReal.ofReal ε * μ {ω | ENNReal.ofReal ε < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ 2 * ∑ k ∈ Finset.range N, ∫⁻ ω, ENNReal.ofReal (dist (X β_k ω) (X α_k ω)) ∂μ.
  ```

  **And this reduction to one quantity is a detour, measured 2026-09-20 and
  recorded here because it was written the other way round.** The condition
  `u ≤ N • δ` ties the count to the radius, `N ≈ u / δ`, and under that tie the
  composition of this estimate with
  `lintegral_ofReal_dist_le_sqrt_of_biSup_le` **diverges**: each summand is at
  most `ENNReal.ofReal √(S.toReal)` with `S = O(ofReal δ ^ (1 - 1/q) * K)`, so
  the sum is `O(δ^((1-1/q)/2 - 1))` and the exponent is negative for every
  `q ∈ (1, ∞]`. The route that converges is the statement one stage **above**,
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist`, whose
  `N` is free:

  ```
  ENNReal.ofReal ε * μ {ω | ENNReal.ofReal ε < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ ∑ k ∈ Finset.range N, ∫⁻ ω, ENNReal.ofReal (dist (X β_k ω) (X α_k ω)) ∂μ
      + ENNReal.ofReal ε * μ {ω | oscHitSeq X ε N ω < u.toNNReal}.
  ```

  There the quantifiers stand in the classical order — **`N` first, then
  `δ`** — because the horizon summand does not mention `δ` at all. The two
  quantities are therefore the right shape and the single one is not, and the
  item is finished by bounding the horizon separately, which is the block
  "The horizon probability" below. `MeasureTheory.measure_setOf_lt_modulusBased_le_gap`
  and its consumer remain true and remain here; what falls is their role as the
  route.

  What is left of this item is therefore two quantities: how the martingale
  hypothesis makes those `N` lower integrals small, uniformly in the family, and
  how it makes the horizon probability small uniformly for large `N`. That is
  where Doob from Milestone 9 is spent, and the count `N` is the deterministic
  `SkorokhodSpace.card_le_of_gapped` where the `δ`-tied route is taken.

  **And the horizon probability is bounded, 2026-09-20**, in the block "The
  horizon probability", which is the second of the two quantities and the one
  that makes `N` a free parameter:

  ```
  N * (ENNReal.ofReal ε ^ 2 * μ {ω | oscHitSeq X ε N ω < u})
    ≤ ∑ k ∈ Finset.range N, ∫⁻ ω, ENNReal.ofReal (dist (X β_k ω) (X α_k ω)) ^ 2 ∂μ
  ```

  — `MeasureTheory.mul_measure_setOf_oscHitSeq_lt_le_sum_lintegral`, with
  `α_k = min (τ k) u` and `β_k = min (τ (k+1)) u`, both stopping times bounded by
  `u`. **`δ` does not occur in it**, which is the whole reason for it: a
  consumer fixes `N` from this estimate first and lets `δ` tend to zero
  afterwards, in the gap sum, where `N` is by then a constant.

  It is three steps and each is cheap.
  `MeasureTheory.setOf_oscHitSeq_lt_subset_dist` is the inclusion
  `{τ (k+1) < u} ⊆ {ε ≤ dist (X β_k) (X α_k)}`, which is
  `le_dist_stoppedValue_oscHitSeq` with both minima attained on the left;
  `MeasureTheory.sq_mul_measure_setOf_oscHitSeq_lt_le` is Markov **at the
  square** on it, measurable by
  `MeasureTheory.stronglyMeasurable_dist_stoppedValue_oscHitSeqCap`; and
  `MeasureTheory.nsmul_measure_setOf_oscHitSeq_lt_le_sum` is the counting step
  `N * μ {τ N < u} ≤ ∑_{k<N} μ {τ (k+1) < u}`, which is `monotone_oscHitSeq` and
  nothing else.

  **Three things about it are worth recording.** The first: the cells here are
  **consecutive** and not `δ`-capped — `β_k` is literally `α_{k+1}` — so the
  compensator increments sum over them to the increment over `[⊥, u]`, that is
  to `u ^ (1 - 1/q) * K`, **independently of `N`**; against the `N` on the left
  that is a horizon bound `O(1/N)`, with constants depending only on `‖f‖`, `u`,
  `q` and `K` and hence uniform in the family. That summation is
  `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le`, proved
  2026-09-20 and described under the class `𝓐 n` below; it is **not**
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le` summed, because
  that statement has Hölder applied per cell and per-cell Hölder grows like
  `N^{1/q}`. The second: the estimate is at the **square** because
  over the first power each summand would carry a square root by
  `lintegral_ofReal_dist_le_sqrt_of_biSup_le` and a sum of `N` square roots is
  `O(√N)` even when the sum under them is `O(1)`. The third: the uncapped cell
  asks for **neither** an addition on the index nor
  `MeasureTheory.IsStoppingTime.add_const_of_orderedSub`, so this block carries
  none of the algebraic hypotheses on `ι` that the gap block carries — two
  applications of `MeasureTheory.isStoppingTime_oscHitSeqCap` and `min_le_right`
  twice are the whole stopping time content.

  **And the bridge between the two index conventions, 2026-09-20.** The times of
  this block live in `WithTop ι`, because a hitting time need not be attained;
  the times of `IsApproximatingPair` live in the index itself, because a
  compensator is indexed by the filtration.
  `MeasureTheory.untopA_oscHitSeqCap_le` and
  `MeasureTheory.untopA_oscHitSeqCap_le_succ` carry the capped times across —
  `(min (oscHitSeq X ε k ω) u).untopA ≤ u` and the same increasing in `k` — and
  they are exactly the two hypotheses
  `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le` asks of its
  chain; the identification of the `stoppedValue` time with the transported one
  is `rfl`. They are `WithTop.untopA_le` (`Mathlib/Order/WithBot.lean:659`) and
  `WithTop.untopA_mono` (`:483`), the duals of `le_unbotA` and `unbotA_mono`.

  **The junk value of `untopA` is not read, and the reason is named**: it is not
  a non-explosion hypothesis but the cap, `min (·) u ≤ u < ⊤` at every sample
  point. Without the cap the second statement would be **false** in the
  direction that matters — past the end of the recursion `oscHitSeq` is `⊤`,
  whose `untopA` is junk, and the sequence would fall rather than rise. That is
  the trap `MeasureTheory.not_stepIndex_mono_time` records for `stepIndex`, here
  closed by the cap rather than by a hypothesis.

  **And the two halves joined, 2026-09-21 — the horizon term with `N` in the
  denominator.** The block "The horizon term, assembled" carries the first
  statement of this item in which the deterministic half over `oscHitSeq` and
  the analytic half over `IsApproximatingPair` occur together:

  ```
  N * (ENNReal.ofReal ε₀ ^ 2 * P {ω | oscHitSeq V ε₀ N ω < u})
    ≤ ofReal u ^ (1 - 1/q) * K * (1 + 2 * ofReal c) + N * (2 ε' + 4 ofReal c ε)
  ```

  — `MeasureTheory.measure_setOf_oscHitSeq_lt_le_of_isApproximatingPair`, for a
  real process `V` bounded by `c`, progressively measurable and with right
  continuous paths, and two pairs of the class with common `q`, `T`, `K`
  approximating `V` and `V²` on the window `Set.Iic u` up to `ε` and `ε'`.
  Divided by `N` the first summand is `O(1/N)` with constants of the class and
  not of its member; the second is the approximation error, which the division
  leaves as it is. **That is the order of the quantifiers**: `N` from the first
  summand, then `ε` against `N`, then `δ` in the gap sum, where `N` is a
  constant. `δ` does not occur in the statement at all.

  The cell of the chain is
  `MeasureTheory.lintegral_ofReal_dist_sq_le_of_isApproximatingPair`, which is
  `ofReal_integral_sq_sub_le` read at two stopping times with the two
  increments of the approximants left as **lower integrals of compensator
  increments** rather than as Hölder bounds — that being what
  `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le` can sum over a
  chain and what `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le`
  cannot. Of the recursion the assembly reads three facts and no more:
  `MeasureTheory.isStoppingTime_oscHitSeqCap`,
  `MeasureTheory.untopA_oscHitSeqCap_le` and
  `MeasureTheory.untopA_oscHitSeqCap_le_succ`. A different recursion with those
  three is served by the same two statements.

  **The constant is `1 + 2 c`, not `1 + 4 c`.** The increment of the square is
  read at the weight `1` and contributes one compensator increment of the
  second pair; the cross term is read at the weight `V` and carries the factor
  `2` of `(v_b - v_a)² = (v_b² - v_a²) - 2 v_a (v_b - v_a)`, hence `2 c` times
  the compensator increment of the first pair. The `4` in front of `c ε` is
  that `2` times the `2` of the two ends of the window at which the
  approximation error is read.

  **One statement had to be factored out for this, and the factoring is a
  finding.** `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le_lintegral`
  is `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le` with the
  Hölder step left undone, `‖∫ W (Y β - Y α)‖ₑ ≤ ofReal c * ∫⁻ ‖C β - C α‖ₑ`,
  and it carries **neither the horizon `T` nor a window length `δ`**: both are
  read by the Hölder step alone. So optional sampling and the invisibility of
  the martingale part to a weight from the past hold over *any* bounded
  stopping times whatever, and the uniform version is the composition of this
  one with `IsApproximatingPair.lintegral_enorm_compensator_sub_le`. The
  relation is that of `IsApproximatingPair.enorm_compensator_sub_le_lintegral`
  to `IsApproximatingPair.enorm_compensator_sub_le`, one level up.

  **And the same bound in the shape its consumer reads**,
  `MeasureTheory.measure_setOf_oscHitSeq_lt_le_div_of_isApproximatingPair`:

  ```
  ofReal ε₀ * P {ω | oscHitSeq V ε₀ N ω < u}
    ≤ (ofReal u ^ (1 - 1/q) * K * (1 + 2 ofReal c) / N + (2 ε' + 4 ofReal c ε)) / ofReal ε₀
  ```

  for `0 < ε₀` and `N ≠ 0`. The shape is read off
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist`, whose
  second summand is `ofReal ε * μ {oscHitSeq X ε N < u}` — the level in the
  **first** power and with no factor `N` — while the statement above it carries
  `N * ofReal ε₀ ^ 2`, because Markov is applied at the square and the counting
  step makes the `N`. The two divisions are `ENNReal.mul_le_mul_iff_left` with
  `ENNReal.div_mul_cancel` (`Mathlib/Basic/ENNReal/Inv.lean:176`) and
  `ENNReal.le_div_iff_mul_le` (`:369`); neither is ever carried out on the right
  hand side, which is why no finiteness beyond `N ≠ 0` and `0 < ε₀` is asked.

  **And a passage that is not cosmetic.** The horizon block produces
  `∫⁻ ω, ofReal (dist …) ^ 2 ∂P` and the square identity produces
  `ofReal (∫ ω, (…)² ∂P)`; the two are the same only through
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`
  (`MeasureTheory/Integral/Bochner/Basic.lean:734`), which asks the square to be
  integrable. That is where the bound on `V` is spent a fourth time, after the
  weight of the cross term, the integrability of the stopped values and their
  products.

  **The gap term, 2026-09-21, and the limit it has is not `0`.** The block "The
  gap term" carries the other of the two quantities
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist` leaves —
  the **first summand** of its right hand side: the `N` increments over the
  **`δ`-capped** cells `α_k = min (τ k) u`, `β_k = min (τ (k+1)) (α_k + δ)`.

  ```
  ∑ k ∈ range N, ∫⁻ ω, ofReal (dist (V β_k ω) (V α_k ω)) ∂P
    ≤ N * ofReal √(((1 + 2 c) * (ofReal δ ^ (1 - 1/q) * K) + (2 ε' + 4 c ε)).toReal)
  ```

  — `MeasureTheory.sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair`,
  for `u + δ ≤ T` and the errors read on the window `Set.Iic (u + δ)`. The cell
  is `MeasureTheory.lintegral_ofReal_dist_le_sqrt_of_isApproximatingPair`.

  **Here Hölder is applied per cell, and that is right, whereas at the horizon
  it was wrong.** The horizon cells are consecutive and `N` of them span one
  window of length `u`, so estimating each separately would pay `N^{1/q}` and
  `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le` sums them first.
  The gap cells are **separated by the gaps**, are not a chain, and `N` is a
  constant here — so
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le` is the right
  estimate and its `δ^{1-1/q}` is what vanishes. The two blocks therefore use
  the two forms of the same passage, and that is why both forms exist.

  *This paragraph names the passage and not a statement the proof calls*, and
  the difference was measured on 2026-09-22, ninth run: the proof of the gap
  cell reads the two **factors** of that composite separately —
  `lintegral_ofReal_dist_sq_le_of_isApproximatingPair` leaves the compensator
  increments standing and `IsApproximatingPair.lintegral_enorm_compensator_sub_le`
  discharges them, one per cell — so the composite itself is never invoked. That
  is why weakening the block needed
  `IsApproximatingPair.lintegral_mul_enorm_compensator_sub_le` and no weighted
  form of the composite.

  **What does not vanish, and it is a correction of the previous run's
  proposal.** As `δ ↓ 0` at fixed `N` the bound tends to
  `N √(2 ε' + 4 c ε)` and **not** to `0` —
  `MeasureTheory.tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero`. The cells are
  increments of `V`, and `V` is known only through the approximants `Y` and
  `Y'`; shrinking the window removes the compensator part and nothing else. The
  order of the quantifiers is therefore `N`, then `δ`, then `ε`: `N` from the
  horizon term, whose first summand is `O(1/N)`; `δ` from here at that fixed
  `N`; and `ε`, `ε'` last, from the approximability condition of \EK, Theorem
  9.4, which asks them to be small for *given* `N` and `δ`. \EK{} say the same
  at (9.28) — "`ε` is then chosen depending on `δ`".

  **The window is `Set.Iic (u + δ)` and not `Set.Iic u`**, because the right
  endpoint of a gap cell overshoots the horizon by at most `δ`
  (`MeasureTheory.oscHitSeqGap_le_coe`), and the approximation errors are read
  wherever the times take their values. That is the one place the two blocks
  differ in their window, and it is why the hypothesis is `u + δ ≤ T`.

  **The two blocks meet, 2026-09-21**, in
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair`:

  ```
  ofReal ε₀ * P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ N * ofReal √(((1 + 2 c) * (ofReal δ ^ (1 - 1/q) * K) + A).toReal)
      + (ofReal u ^ (1 - 1/q) * K * (1 + 2 ofReal c) / N + A) / ofReal ε₀
  ```

  with `A = 2 ε' + 4 ofReal c * ε`, for `δ < u`, `u + δ ≤ T`, `0 < ε₀` and
  `N ≠ 0`. It is `le_trans` of
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist` followed by
  `add_le_add` of the two block results, and it makes no estimate of its own.
  Every quantity on the right is a constant of the class — `u`, `q`, `K`, the
  bound `c`, the count `N`, the window `δ` — or one of the two approximation
  errors.

  **The version with a free `N` is the one that composes, and this is where the
  other one is ruled out for good.**
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le`
  removes the horizon summand at the price `u ≤ N • δ`, and the bound it yields
  is `u √C · δ^{(1-1/q)/2 - 1}`, whose exponent is negative for *every* `q`
  because `(1 - 1/q)/2 ≤ 1/2 < 1`. Keeping the horizon summand is what lets `N`
  be fixed before `δ`; that is the computation of the run of 2026-09-20,
  twenty-third of the day, now standing at the statement it decides.

  **Two windows, one hypothesis.** The statement carries the approximation
  errors only on `Set.Iic (u + δ)`, the larger of the two windows; the horizon
  block's `Set.Iic u` version follows by `biSup_mono` under `lintegral_mono`,
  and its `u ≤ T` by `le_self_add` against `u + δ ≤ T`. The four integrability
  hypotheses are the gap block's, and the horizon block reads the two at the
  capped times.

  **And the same at an image path**,
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_postcomp_le_of_isApproximatingPair`,
  which is the shape this milestone's criterion consumes: for a bounded
  continuous `g : E →ᵇ ℝ` and an `E`-valued `X` with path map `Φ`, the same
  inequality for the image path
  `SkorokhodSpace.postcomp g (SkorokhodSpace.extendNNReal (Φ ω))` with
  `c = ‖g‖`. That is the form
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal` of Milestone 8
  hands it and the form the three transports
  `SkorokhodSpace.min_edist_le_two_mul_modulusBased_postcomp`,
  `SkorokhodSpace.min_iSup_edist_le_three_mul_modulusBased_postcomp` and
  `SkorokhodSpace.min_iSup_edist_leftLim_le_three_mul_modulusBased_postcomp`
  read. The index crossing and the post-composition commute definitionally
  (`SkorokhodSpace.postcomp_extendNNReal`), so it may be read either way round,
  and **nothing measurable is asked of `E`**: the modulus is that of a real
  valued path throughout.

  **The bound on the process is a consequence there and not a hypothesis.**
  `MeasureTheory.IsApproximatingPair` has no bound of its own, and the assembly
  asks for one because the square identity spends it four times; an `E →ᵇ ℝ`
  carries it, so a consumer of the criterion never has to produce it.

  **One composition lemma is missing from Mathlib for that passage**, and the
  shape of the gap is worth naming because the same pair of files has the
  abstraction on one side and not on the other.
  `MeasureTheory.IsStronglyProgressive.continuous_comp` — progressive
  measurability survives post-composition with a continuous map, one line from
  `Continuous.comp_stronglyMeasurable` — belongs in
  `Mathlib/Probability/Process/Adapted.lean` next to
  `MeasureTheory.IsStronglyProgressive.mul`
  (`Mathlib/Probability/Process/Adapted.lean:293`),
  `MeasureTheory.IsStronglyProgressive.inv`
  (`Mathlib/Probability/Process/Adapted.lean:323`) and
  `MeasureTheory.IsStronglyProgressive.div'`
  (`Mathlib/Probability/Process/Adapted.lean:327`), which are three instances of
  it and are each proved separately; `Mathlib/Topology/Order/Cadlag.lean`
  derives its own `mul`, `div`, `inv` and `const_smul` from `IsCadlag.continuous_comp`
  (`Mathlib/Topology/Order/Cadlag.lean:119`). The name avoids
  `MeasureTheory.IsStronglyProgressive.comp`
  (`Mathlib/Probability/Process/Adapted.lean:280`), which is the composition in
  the **time** argument. It asks neither an order topology nor a measurable
  structure on the values, only `Preorder ι` and a `MeasurableSpace ι`.

  **A trap of the `open` that cost a compile.** The notation `E →ᵇ ℝ` is
  `scoped[BoundedContinuousFunction]`, and `open scoped BoundedContinuousFunction`
  **inside** `namespace MeasureTheory` opens `MeasureTheory.BoundedContinuousFunction`,
  which exists and carries no notation, while the root namespace is silently not
  opened. The error it produces names neither cause:
  `elaboration function for Mathlib.Tactic.superscriptTerm has not been implemented`,
  because `→ᵇ` is no longer a token and `ᵇ` is parsed as a superscript. The
  remedy is `open scoped _root_.BoundedContinuousFunction`, and the
  `ambiguousOpen` linter says so in a warning that is easy to miss beside the
  error it causes.

  **What the assembly is not.** It stands over a real valued `V`, or over one
  test function `g` at a time, and it is one inequality at one `(N, δ, ε₀)`. The
  criterion needs it uniformly over the family — and it needs the passage from
  the countable separating family back to the metric of `E`, which the three
  transports above supply. The three limits in the order `N`, `δ`, `ε` are the
  item "The approximability condition" at the end of this milestone; uniformity
  over the family is the one after that.

  **Two statements were factored out for this.**
  `MeasureTheory.lintegral_ofReal_dist_le_sqrt_of_lintegral_sq_le` is
  Cauchy--Schwarz read from a bound on `∫⁻ ofReal (dist ·) ²`, the side the
  horizon block produces, rather than on `ofReal (∫ (·)²)`, the side
  `lintegral_ofReal_dist_le_sqrt_toReal_of_le` reads; performing the equality
  once there is what lets the gap block use the horizon block's cell statement
  unchanged. And `MeasureTheory.untopA_oscHitSeqGap_le_add` is the shortness of
  the gap cell read **in the index**,
  `(min (τ (k+1)) (min (τ k) u + δ)).untopA ≤ (min (τ k) u).untopA + δ`, which
  is what the Hölder step asks and what the consecutive cells cannot give. Its
  junk value is unread for the same reason as its two siblings: the cap, not a
  hypothesis.

  **A naming trap that cost a compile and is recorded so it costs no other.**
  The countable dense set of the début theorem is called `D` throughout this
  development, and `D(ι, E)` is the notation for the path space; a section or
  argument named `D` shadows the notation, and a statement mentioning both
  fails with a synthesis error about `LE (MeasurableSpace ?m → Type)` that
  names neither. In
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist` the dense
  set is therefore `S`.

  **And the order lemmas of Mathlib do not have the shape a memory supplies.**
  `mul_le_mul_left'` and `add_le_add_left'` do **not** exist — neither on
  `master` nor on v4.33.1. What exists is
  `mul_le_mul_right (bc : b ≤ c) (a : α) : a * b ≤ a * c` and
  `mul_le_mul_left (bc : b ≤ c) (a : α) : b * a ≤ c * a`
  (`Algebra/Order/Monoid/Unbundled/Basic.lean:61` and `:69`), with their
  `to_additive` images. The suffix names the side on which the **varying**
  argument stands, so `add_le_add_left (h : b ≤ c) (a) : b + a ≤ c + a` adds
  the constant on the *right* — the reverse of what the word suggests, and the
  reverse of the older convention a memory is likely to supply.

  **The times are written in the `WithTop ℝ≥0` shape** — `↑δ.toNNReal` rather
  than `ENNReal.ofReal δ` — because that is where `oscHitSeq` takes its values.
  The two types are the same, but the `binop%` elaborator does not place a
  `WithTop ℝ≥0` and an `ℝ≥0∞` under one `+`, and a statement mixing them fails to
  elaborate.

  **Strict monotonicity is not free and its price is named.** The début of a
  right-open set need not be attained, so `le_debutTime_oscSet` alone leaves
  `τ k = τ (k+1)` possible. `lt_debutTime_oscSet` excludes it from `0 < ε`
  together with right continuity at `τ k`, and it is false for `ε = 0`. It
  needs no `OrderBot` on the index.

  **The bound is `ε` and not `2 ε`**, because `SkorokhodSpace.subdivisionOsc`
  measures each cell from its left endpoint where Billingsley's `w'` takes the
  diameter.

  **And the remaining half is not a formality.**
  `SkorokhodSpace.not_isTightMeasureSet_twoJumpImageLaw` exhibits a family of
  image laws under a bounded post-composition — two jumps approaching each other,
  read through the clipped distance to the value between them — which has compact
  containment in one line and is not tight. The quantity that fails there is
  exactly the one the martingale hypothesis of this item is for.

  **The one remaining quantity is not bounded by what the martingale hypothesis
  says about `f` alone**, 2026-09-20, and this fixes the shape the criterion has
  to take. After
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le` what
  is left is `∫ |Y β - Y α|` for the real process `Y = f ∘ X` and the two
  stopping times. Write `Y = M + C` with `M` a martingale and `C` the
  compensator. The compensator part is Hölder: `|C β - C α| ≤ ∫_α^{α+δ} |Z|` and
  hence `O(δ^{1-1/p})` from the `eLpNorm` bound the criterion carries. **The
  martingale part is not small at all.** A martingale with a jump of size `1` at
  a deterministic time has `∫ |M β - M α| = 1` for `α` just below the jump and
  `β` at it, for **every** `δ > 0`, while `sup_t ∫ |M t| ≤ 1` and its
  compensator is `0`; both hypotheses of `𝓐 n` hold and the quantity does not go
  to zero. What the martingale property gives is not the increment but its
  integral against a weight from the past, and that is
  `integral_mul_stoppedValue_sub_eq_zero` below.

  **The passage to the increment is the square, and it costs `f²`.** With `D`
  the compensator of `Y²` — that is, with `(f², g₂) ∈ A` supplying a second pair
  `(Y², D) ∈ 𝓐 n` — the increment of the square and the cross term are both
  compensator increments,

  ```
  ∫ (Y β - Y α)² = ∫ (D β - D α) - 2 ∫ Y α * (C β - C α),
  ```

  because `(Y β - Y α)² = (Y β² - Y α²) - 2 Y α (Y β - Y α)` and the martingale
  parts of both terms integrate away — the first against the weight `1`, the
  second against the weight `Y α`, which is bounded and `𝓕_α`-measurable.
  Hölder makes both right hand terms `O(δ^{1-1/p})`, and Cauchy–Schwarz turns
  the left hand side into `∫ |Y β - Y α|`. **Doob is not spent at this point**;
  what is spent is optional sampling between two stopping times, the pull out
  property of the conditional expectation, and Hölder.

  **This is Ethier--Kurtz's own proof, and it was rediscovered rather than read.
  Recorded 2026-09-20 so that no run derives it a third time.** \EK, Theorem
  9.4 is the item stated here, and its proof (p. 147) is the estimate above,
  with displays worth citing by number:

  * (9.26) defines the dominating variable, and it reads the approximants of
    **both** `f` and `f²`:
    `γ_α(δ) = 2 sup |f²(X_α) - Y'_α| + 4‖f‖ sup |f(X_α) - Y_α|
              + δ^{1/q'} ‖Z'_α‖_{p',T+1} + 2‖f‖ δ^{1/q} ‖Z_α‖_{p,T+1}`,
    the suprema over `[0, T+1] ∩ ℚ` and `1/p + 1/q = 1`, `1/p' + 1/q' = 1`.
  * (9.27) is the conclusion,
    `𝔼[(f(X_α(t+u)) - f(X_α(t)))² | 𝓕_t] ≤ 𝔼[γ_α(δ) | 𝓕_t]`
    for `0 ≤ t ≤ T`, `0 ≤ u ≤ δ`, and it holds for all real `t, u` and not
    merely rational ones **by right continuity of `X_α`**.
  * (9.28) bounds `sup_α 𝔼[γ_α(δ)]`, and `ε` is then chosen depending on `δ`.
  * Remark 9.5(a): **`p = 1` is not sufficient**, with a two-state Markov chain
    of rate `n` as the witness — whose finite dimensional distributions converge
    to those of the zero process while the family does not converge in
    distribution. That is what makes `p ∈ (1,∞]` a hypothesis and not a
    convenience.
  * Remark 9.5(b): for *sequences* the `sup_α` in both conditions may be
    replaced by `limsup_α`.

  **Where \EK{} go next, and where this roadmap does not.** They feed (9.27)
  into \EK, Theorem 8.6, their conditional-moment criterion for relative
  compactness, whose condition (b) asks

  ```
  𝔼[q^β (X_α(t+u)) (X_α(t)) * q^β (X_α(t)) (X_α(t-v)) | 𝓕^α_t] ≤ 𝔼[γ_α(δ) | 𝓕^α_t]
  ```

  — the **product of a forward and a backward increment**, which is Billingsley's
  `w''` in conditional form; Remark 8.7(a) is what lets the one-sided (9.27)
  serve, and Theorem 8.8 gives sufficient conditions for the `γ_α`.

  This roadmap reaches the modulus through **Aldous** instead
  (**SkorokhodSpace** Milestone 10), and the choice is recorded rather than
  implied. It was not made against 8.6 on the merits: by the time (9.27) was in
  hand, the début theorem, `oscHitSeq` and the deterministic half
  `modulusBased_le_of_forall_gapped` already stood, so two of the three
  hypotheses of the Aldous route were discharged and none of 8.6 existed.
  Both routes consume (9.27) and neither is more general; 8.6 would additionally
  need the backward increment and the passage of Remark 8.7(a). **If a run finds
  the remaining `δ`-sparseness estimate expensive, 8.6 is the alternative to
  weigh, and this paragraph is the place to start.**

  **Hence the approximable functions are to be closed under products.** The
  criterion may not be stated for an arbitrary set of approximable `f` and its
  sup-norm closure: the estimate above reads the hypothesis at `f²` as well, so
  what the criterion quantifies over is a **subalgebra**, which is what
  `isRelativelyCompact_of_approx` below asks for anyway and what makes the two
  items fit. The witness above shows this is not a convenience — with `f`
  alone the conclusion of the intermediate estimate is false.

  **And optional sampling between two stopping times is supplied**, 2026-09-20,
  because Mathlib has it for no index this development uses.
  `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le`
  (`Probability/Martingale/OptionalSampling.lean:141`) carries `[Countable ι]`,
  the countable range form (`ibid.:121`) asks both times to have countable
  range, and the section titled *Optional Sampling* (`ibid.:158`) runs under
  `[LocallyFiniteOrder ι]` and `[DiscreteTopology ι]`. The four declarations
  that close the gap are

  * `stoppedValue_ae_eq_condExp_stoppedValue` —
    `stoppedValue Y α =ᵐ[P] P[stoppedValue Y β | 𝓕_α]` for a right continuous
    martingale over `ℝ≥0` and `α ≤ β ≤ j`. It is the tower property over the one
    time form `stoppedValue_ae_eq_condExp` of Milestone 9, with
    `MeasureTheory.condExp_condExp_of_le`
    (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:345`) along
    `MeasureTheory.IsStoppingTime.measurableSpace_mono`
    (`Probability/Process/Stopping.lean:464`); **no analysis is added** to what
    the one time form already paid for.
  * `integral_mul_stoppedValue_eq` —
    `∫ W * stoppedValue Y β = ∫ W * stoppedValue Y α` for `W` bounded and
    `𝓕_α`-measurable, by `MeasureTheory.integral_condExp` (`ibid.:237`) and the
    pull out property `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound`
    (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean:260`). `W` is
    bounded rather than integrable because that is the pull out form which needs
    no integrability of the product, and the consumer has the bound.
  * `integral_mul_stoppedValue_sub_eq_zero` — the same with the increment on one
    side, `∫ W * (stoppedValue Y β - stoppedValue Y α) = 0`.
  * `integral_mul_stoppedValue_sub_eq_compensator` — the quasimartingale form,
    `∫ W * (Y β - Y α) = ∫ W * (C β - C α)` whenever `Y - C` is a right
    continuous martingale. It asks two integrabilities and they are about `Y`,
    not about `C`: the stopped values of the martingale are integrable for free
    by `integrable_stoppedValue_of_rightContinuous`, and those of `C` are the
    difference.

  **The square identity itself is proved**, 2026-09-20, and with it the return
  from the square to the increment:

  * `integral_sq_stoppedValue_sub_eq` — the display above, for `Y - C` and
    `Y² - D` right continuous martingales and `α ≤ β ≤ j`. Its two summands are
    `integral_mul_stoppedValue_sub_eq_compensator` at the weights `1` and
    `stoppedValue Y α`, the latter `hα.measurableSpace`-measurable by
    `MeasureTheory.measurable_stoppedValue`
    (`Probability/Process/Stopping.lean:1044`), and the algebra
    `(b - a)² = (b² - a²) - 2 a (b - a)` is `ring`. **Boundedness of `Y` is not
    among its hypotheses**: what the proof reads is a bound on the *weight*
    `stoppedValue Y α` alone — the pull out property is used in its bounded form
    — together with integrability of the four stopped values. Nothing here
    manufactures a compensator for `Y²` out of one for `Y`; that is the pair the
    hypothesis supplies, and it is why the approximable functions have to be
    closed under products.
  * `integral_sq_stoppedValue_sub_eq_of_bounded` — the same with a global bound
    `|Y t ω| ≤ c` in place of the five, which is what the consumer has, `Y`
    being `f ∘ X` for a bounded `f`.
  * `lintegral_ofReal_dist_le_sqrt_integral_sq` — Cauchy–Schwarz in the two
    shapes the neighbours have,
    `∫⁻ ofReal (dist (f ω) (g ω)) ≤ ofReal √(∫ (f ω - g ω)²)`, over a
    probability measure and for arbitrary real `f, g`. It is the nonnegativity
    of the variance of `|f - g|` (`ProbabilityTheory.variance_nonneg` through
    `ProbabilityTheory.variance_eq_sub`), then `Real.le_sqrt` and
    `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`; no inner product space
    and no `eLpNorm`. A merely finite measure would carry the factor `√(P univ)`
    into every application, and the consumer is a law.

  **And the Hölder estimate on the compensator increment is proved**, the same
  day, in the two shapes the two applications have:

  * `lintegral_enorm_le_rpow_mul_eLpNorm` —
    `∫⁻ s in Set.Ioc a b, ‖Z s‖ₑ ≤ ofReal (b - a) ^ (1 - 1/q.toReal) *
    eLpNorm Z q (ℙ|_S)` for `1 ≤ q` and any `S ⊇ Set.Ioc a b`. It is
    `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`
    (`MeasureTheory/Function/LpSeminorm/CompareExp.lean:65`) at `p = 1`, the
    window length entering as `μ Set.univ` of the restricted measure. The
    ambient set is a parameter and not the window, because the hypothesis of
    `𝓐 n` bounds the density on a horizon once while the window moves.
  * `enorm_setIntegral_le_rpow_mul_eLpNorm` — the same read at the Bochner
    integral, `‖∫ s in Set.Ioc a b, Z s‖ₑ ≤ …`, by
    `MeasureTheory.enorm_integral_le_lintegral_enorm`. It asks **no**
    integrability, which is why it is stated in `ℝ≥0∞`.

  Neither mentions a probability measure, a filtration or a stopping time: they
  are estimates on one real function over one window, read at a fixed sample
  point before anything is integrated over `Ω`.

  **And the class `𝓐 n` is written down**, 2026-09-20, as the predicate
  `IsApproximatingPair 𝓕 P q T K Y C Z`: `Y - C` a right continuous martingale
  over `ℝ≥0`, `C t ω = ∫_{(0,t]} Z s ω`, and
  `∫⁻ ω, eLpNorm (Z · ω) q (ℙ|_(0,T]) ≤ K`. It is membership of the pair
  `(Y, Z)` in \EK's class together with the bound display (9.26) reads on it.

  * **`K` is a parameter of the predicate, and that is how uniformity in the
    family is expressed.** The criterion asks `⨆ n, 𝔼[eLpNorm (Z n) q] < ∞`; a
    family satisfying the predicate with one and the same `K` has that
    supremum bounded, and no statement below has to quantify over the family.
  * **The compensator is carried as a density, and the alternative is
    recorded rather than dismissed.** Mathlib has the fundamental theorem of
    calculus for absolutely continuous functions,
    `MeasureTheory.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
    (`MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:225`),
    so an absolutely continuous compensator *is* an indefinite integral, of
    `deriv (C · ω)`. What that passage does not hand back is joint
    measurability of `(s, ω) ↦ deriv (C · ω) s`, so the density form is not
    the weaker one in substance; it is also the one
    `enorm_setIntegral_le_rpow_mul_eLpNorm` reads with no step in between.
  * **The almost sure `MemLp` of the density is a field beside the bound on
    its mean, and it is not redundant.** A finite mean makes a function almost
    everywhere finite only if it is measurable, and the measurability at issue
    is that of `ω ↦ eLpNorm (fun s ↦ Z s ω) q ν`. **Mathlib has that for no
    exponent and in no shape** — checked 2026-09-20 against
    `94ef6b89544e58e90f119da869f3fb48d1da0f4c`: neither
    `MeasureTheory/Integral/Prod.lean` nor the directory `LpSeminorm/` carries
    the measurability of an `eLpNorm` in a parameter. It is a Mathlib gap of
    its own and belongs in `TODO.md` point 8.

  Seven consequences are proved with it, and each is a link the assembly reads:
  `IsApproximatingPair.ae_integrableOn`, the only place the horizon's finite
  length is spent; `IsApproximatingPair.compensator_sub_eq`, the increment of
  the compensator as the integral of the density over the window, through
  `setIntegral_Ioc_sub_setIntegral_Ioc`;
  `IsApproximatingPair.enorm_compensator_sub_le`, the Hölder bound at one
  sample point; and
  `IsApproximatingPair.lintegral_enorm_compensator_sub_le`, the same
  integrated, `∫⁻ ω, ‖C (b ω) ω - C (a ω) ω‖ₑ ≤ ofReal δ ^ (1 - 1/q) * K` for
  **arbitrary** `a b : Ω → ℝ≥0` with `a ≤ b ≤ T` and `b - a ≤ δ` — no stopping
  time and no measurability of `a`, `b`, the lower integral being monotone
  without either.

  **And the chain of consecutive windows, 2026-09-20**, which is what the
  horizon term reads and what the `δ`-capped cell cannot give:

  ```
  ∑ k ∈ Finset.range N, ∫⁻ ω, ‖C (σ (k+1) ω) ω - C (σ k ω) ω‖ₑ ∂P
    ≤ ENNReal.ofReal u ^ (1 - 1/q) * K
  ```

  — `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le`, for
  **arbitrary** `σ : ℕ → Ω → ℝ≥0` with `σ k ω ≤ σ (k+1) ω` and `σ N ω ≤ u ≤ T`.
  **`N` does not occur on the right**, and that is the statement: over `N` cells
  of length `δ` the previous item gives `N ofReal δ ^ (1-1/q) K`, which under the
  tie `N ≈ u/δ` is `u δ^{-1/q} K` and diverges as `δ ↓ 0`; consecutive cells
  have no `δ` to diverge in.

  **Where the order of the steps decides the exponent.**
  `IsApproximatingPair.enorm_compensator_sub_le` has Hölder applied already, and
  summing *that* over `N` cells of lengths `δ_k` gives `∑_k δ_k^{1-1/q}`, hence
  `N^{1/q} u^{1-1/q}` for equal cells — it still grows. The chain therefore
  starts one step lower, at
  `IsApproximatingPair.enorm_compensator_sub_le_lintegral`, which is
  `IsApproximatingPair.compensator_sub_eq` followed by
  `MeasureTheory.enorm_integral_le_lintegral_enorm` and takes **no** exponent;
  `sum_lintegral_Ioc_succ` telescopes the `N` lower integrals into the one over
  `(σ 0, σ N]` — `MeasureTheory.lintegral_union`
  (`MeasureTheory/Integral/Lebesgue/Basic.lean:615`) along
  `Set.Ioc_union_Ioc_eq_Ioc`
  (`Mathlib/Order/Interval/Set/LinearOrder.lean:382`), with no measurability of
  the integrand — and Hölder is applied **once**, over `(0, u]`.
  `IsApproximatingPair.sum_enorm_compensator_sub_le` is that chain at one sample
  point.

  **Two economies worth recording.** `σ 0 = 0` is *not* a hypothesis and no
  lower bound on `σ 0` is: the chain telescopes to `(σ 0, σ N]`, and `σ 0 ≥ 0`
  holds in `ℝ≥0` by fiat. And the monotonicity is asked in the successor form
  `σ k ≤ σ (k+1)`, which is the form a recursion has —
  `MeasureTheory.oscHitSeq_le_succ` at the consumer — `monotone_nat_of_le_succ`
  doing the rest.

  **A Mathlib gap sits in the passage and is elementary**: moving the finite sum
  out of the lower integral is the **superadditive** direction, free of
  measurability, and Mathlib has it for two summands only —
  `MeasureTheory.le_lintegral_add`
  (`MeasureTheory/Integral/Lebesgue/Add.lean:273`) is the sole declaration of
  the shape `le_lintegral…` in the library, checked 2026-09-20 against
  `94ef6b89544e58e90f119da869f3fb48d1da0f4c`, while
  `MeasureTheory.lintegral_finsetSum` (`:356`) is the equality under
  `Measurable`. The `Finset` version is proved here as `le_lintegral_finsetSum`,
  by induction, and it belongs in `TODO.md` point 8. The hypothesis is not
  removable in the other direction: `not_forall_lintegral_add_le` is the witness.

  **The two halves are joined by
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le`**: for stopping
  times `α ≤ β ≤ j ≤ T` with windows at most `δ` long and a weight `W` bounded
  by `c` and `𝓕_α`-measurable,
  `‖∫ W (Y β - Y α)‖ₑ ≤ ofReal c * (ofReal δ ^ (1 - 1/q) * K)`. Between
  `integral_mul_stoppedValue_sub_eq_compensator` on the left and the previous
  item on the right there is only
  `MeasureTheory.enorm_integral_le_lintegral_enorm`.

  **Where `1 < q` is spent, and it is one statement.**
  `one_sub_one_div_toReal_pos` — the exponent `1 - 1/q.toReal` is positive,
  true at `q = ⊤` as well, false at `q = 1` — and
  `tendsto_ofReal_rpow_mul_nhdsGT_zero`, that `ofReal δ ^ (1 - 1/q) * K → 0` as
  `δ ↓ 0` for `K ≠ ⊤`. That is what lets the sum over `N ≈ u/δ` windows vanish,
  and it is exactly \EK, Remark 9.5(a).

  **A correction to this item, 2026-09-20: the second pair is `(Y', D)` and not
  `(Y², D)`.** The paragraph above on the square reads the hypothesis "with
  `(f², g₂) ∈ A` supplying a second pair `(Y², D) ∈ 𝓐 n`", and that is stronger
  than what the class delivers: membership at `f²` supplies some `Y'` near
  `f² ∘ X`, and nothing makes it the square of the approximant `Y` of `f`.
  \EK's (9.26) reads `Y'_α` and `Z'_α` with an exponent `p'` of their own —
  four summands, two approximation errors and two `L^q` norms. Hence
  `integral_sq_stoppedValue_sub_eq`, which asks literally for `Y² - D` to be a
  martingale, is a special case the criterion **cannot invoke**; the assembly
  reads `integral_mul_stoppedValue_sub_eq_compensator` twice instead, at the
  weight `1` for the pair near `f²` and at the weight `f ∘ X α` — bounded by
  `‖f‖` and `𝓕_α`-measurable, `X` being adapted — for the pair near `f`. Both
  are instances of
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le`, which is why
  that statement carries an arbitrary bounded weight from the past. What
  survives of the earlier reading is the conclusion that made it: the
  approximable functions still have to be closed under products, because the
  estimate reads the hypothesis at `f²` as well.

  **And the approximation error of (9.26) is read**, 2026-09-20 — the
  hypothesis `∫⁻ ω, ⨆ t ∈ W, ‖Y t ω - f (X t ω)‖ₑ ∂P ≤ ε`, which until then no
  statement of this milestone touched. Three statements carry it from the
  approximant to the process:

  * `enorm_sub_le_add_two_mul_biSup`, the triangle inequality at the two ends
    of a window, `‖V b ω - V a ω‖ₑ ≤ ‖Y b ω - Y a ω‖ₑ + 2 ⨆ t ∈ W, ‖Y t - V t‖ₑ`
    for `a, b ∈ W`; the factor `2` counts the ends and is owed.
  * `lintegral_enorm_sub_le_of_biSup_le`, the same integrated, for
    **arbitrary** `a b : Ω → ι` with values in `W` — no stopping time, no
    measurability of the times, exactly the economy of
    `IsApproximatingPair.lintegral_enorm_compensator_sub_le`.
  * `lintegral_enorm_sub_le_of_biSup_le_of_countable` and
    `lintegral_enorm_sub_le_of_biSup_Iic_le`, the two readings of the window.

  **Where the countability of the window is really spent, and it is not where
  this roadmap said.** The compensator estimate needed no measurability at all,
  the lower integral being monotone without one; here it is needed, and the
  step that needs it is the **addition**. The lower integral is not subadditive
  for arbitrary functions, and `not_forall_lintegral_add_le` is the witness:
  on `Bool` with the σ-algebra `⊥` and the Dirac measure at `true`, the
  indicators of `{true}` and of `{false}` each have lower integral `0` while
  their sum is the constant `1`. So the measurability hypothesis of
  `MeasureTheory.lintegral_add_right'`
  (`MeasureTheory/Integral/Lebesgue/Add.lean:331`) is not a convenience of
  Mathlib's proof, and the window has to be countable — or be reduced to a
  countable one.

  **The consumer's form is the second**, because the times it substitutes are
  hitting times and take their values wherever the path takes them: a
  hypothesis quantified over a countable set would not be applicable to them.
  `lintegral_enorm_sub_le_of_biSup_Iic_le` reads the whole window `Set.Iic T`
  and pays with **almost sure** right continuity of the paths of `Y - f ∘ X`,
  through `biSup_enorm_Iic_eq_of_isRightContinuous` of Milestone 9. \EK{} spend
  right continuity in exactly this place, their (9.27) holding for all real
  times and not merely rational ones. That the reduction is only almost
  everywhere is why the measurability asked of the supremum is `AEMeasurable`
  and not `Measurable` — and it is the right side of the trade here, since in
  this development the right continuity of paths is what Vitali convergence
  delivers, quantified almost everywhere.

  **The error is read twice, and the weighted reading is the cheaper one.**
  (9.26) reads the approximation error at both pairs: at the pair near `f² ∘ X`
  against the weight `1`, which is `lintegral_enorm_sub_le_of_biSup_Iic_le`
  above, and at the pair near `f ∘ X` against the weight `f ∘ X α`, which is
  `enorm_integral_mul_sub_le_of_biSup_le` through the regrouped triangle
  inequality `enorm_sub_sub_le_two_mul_biSup`. **The weighted one needs no
  measurability at all**, and that is not symmetry: it splits a *Bochner*
  integral, where `MeasureTheory.integral_add` asks integrability of the
  summands — which a consumer holds from a bounded `f` — and the remaining tail
  is bounded by monotonicity of the lower integral alone. It therefore stands
  over an arbitrary window, with no countability, no topology on the index and
  no right continuity.

  **And the passage to the metric of `E` does not occur in this item at all,
  checked 2026-09-20.** The conclusion here is the tightness of the laws of
  `postcomp f ∘ X n` in `D ι ℝ`, so the modulus of
  `mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le` is read at the
  **image** path and its `dist` is the distance of two reals.  No net of a
  compact set and no recovery of the metric of `E` from the test functions
  enters; that recovery is the business of
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp`, the third item of
  **SkorokhodSpace** Milestone 8. The whole junction is
  `ofReal_dist_eq_enorm_sub`, and
  `lintegral_ofReal_dist_le_of_biSup_Iic_le` is the estimate already written in
  the shape that statement integrates.

  **The square identity at the process, 2026-09-20**, and with it the last
  analytic step of this item:

  * `ofReal_integral_sq_sub_le` — display (9.26) itself,
    `ofReal (∫ (V b - V a)²) ≤ (‖∫ (Y' b - Y' a)‖ₑ + 2 ε')
    + 2 (‖∫ V a · (Y b - Y a)‖ₑ + ofReal c · (2 ε))` for `Y` near `V` and `Y'`
    near `V²`, with `V` bounded by `c`. The real identity
    `(v_b - v_a)² = (v_b² - v_a²) - 2 v_a (v_b - v_a)` is `ring`; both right
    hand terms are `enorm_integral_mul_sub_le_of_biSup_le`, at the weight `1`
    and at the weight `V (a ·) ·`, so the window needs no countability, no
    topology and no right continuity. The four summands are exactly \EK's.
  * `lintegral_ofReal_dist_le_sqrt_toReal_of_le` — the bridge that was missing
    between the two: `lintegral_ofReal_dist_le_sqrt_integral_sq` has a Bochner
    integral under its root while every estimate here produces a bound in
    `ℝ≥0∞`. It is `ENNReal.ofReal_le_iff_le_toReal`
    (`Basic/ENNReal/Real.lean:262`), and `S ≠ ⊤` is owed because
    `toReal ⊤ = 0`.
  * `lintegral_ofReal_dist_le_sqrt_of_biSup_le` — the two composed, in the
    shape `mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le`
    integrates. The bound `S` is a parameter and not the sum itself, because
    it is `S` that the assembly drives to zero.

  **The square is taken at the process, and that is what makes it available at
  all.** `integral_sq_stoppedValue_sub_eq` asks for `Y² - D` to be a
  martingale, which the class does not supply; here the square is a square by
  definition and the two approximants stay unrelated, each with an error of its
  own. The correction recorded above is thereby not merely noted but paid for.

  **The integrability of the square is not a hypothesis**, and the bound on `V`
  pays for itself a second time: `‖V‖ ≤ c` makes the increment `≤ 2c`, and
  `MeasureTheory.Integrable.mono'`
  (`MeasureTheory/Function/L1Space/Integrable.lean:105`) against the constant
  turns the measurability Cauchy–Schwarz asks for anyway into integrability.

  **No quantity of this item is left to estimate at one pair of times.** Every
  analytic ingredient exists, the predicate that binds them does too, and every
  hypothesis of the criterion is read by some statement.

  **What is left is not bookkeeping, and this roadmap said otherwise until
  2026-09-20.** The remaining step was described as `N ≈ u/δ`, the sum of the
  `N` window bounds, and `tendsto_ofReal_rpow_mul_nhdsGT_zero` in
  `mul_measure_setOf_lt_modulusBased_le_lintegral_dist_of_le`. Counting the
  powers of `δ` shows that this does not close. That consumer bounds
  `ofReal ε · μ {modulusBased > ε}` by `2 ∑_{k<N} ∫⁻ ofReal (dist …)` with
  `N ≈ u/δ`; each summand is at most `ofReal √(S.toReal)` with
  `S = O(δ^(1−1/q))`, so the right hand side is `O(δ^((1−1/q)/2 − 1))`, and the
  exponent is negative. Summing the squares first and applying Cauchy–Schwarz
  over `k` does better — the windows are disjoint, so `∑_k ∫ Δ_k² = O(1)` and
  Hölder over `k` cancels the `δ` exactly — but it still leaves `O(√N)`.

  **Both computations pay the factor `N` for a union bound over the `N`
  windows, and Aldous does not take one.** The outline of **SkorokhodSpace**
  Milestone 10 names the step: a *second application of the hypothesis at a
  random time*, read at one stopping time rather than at each `k`. So the
  statement between the present state and this item is
  `SkorokhodSpace.modulusBased_le_of_forall_stoppingTime`, which exists in that
  roadmap and in none of the three `Suggested.lean`. Everything built for this
  item is its input: the estimate at **one** pair of times, which that route
  reads once and not `N` times.

  **And that statement belongs here rather than in SkorokhodSpace.** Its only
  consumer is this item, its inputs are the stopping time machinery of
  Milestone 9, and a filtration occurs in its hypothesis — the three reasons
  that milestone itself gives for the move.

  **A correction to the two paragraphs above, 2026-09-21.** They name
  `SkorokhodSpace.modulusBased_le_of_forall_stoppingTime` as *the* statement
  between the present state and this item, and that is no longer what the
  computation shows. The divergence they record is real, but it is a finding
  about **one** of the two routes, not about the item: it belongs to
  `MeasureTheory.measure_setOf_lt_modulusBased_le_gap`, which ties `N` to `δ` by
  `u ≤ N • δ` and thereby forbids choosing `N` first. The route with a **free**
  `N` — `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_lintegral_dist`,
  which leaves the horizon probability standing as a second summand instead of
  absorbing it — has no such tie, and its horizon summand is bounded by
  `MeasureTheory.measure_setOf_oscHitSeq_lt_le_of_isApproximatingPair` with
  `N` in the denominator. The Aldous route stays in the roadmap as the second
  way and is not withdrawn; what is withdrawn is the claim that it is the
  **only** one.

  **Why the square is the only route, as a theorem and no longer as a
  paragraph**, 2026-09-20. That the martingale part of the increment is not
  small in `L¹` — so that neither Doob nor Hölder carries this item, and the
  square identity is not a convenience — is witnessed in Lean, on the coin of
  `AtomWitness` and with no new construction:
  `coinMartingale u` is a martingale over `coinFiltration u`
  (`martingale_coinMartingale`) with `sup_t 𝔼|M t| ≤ 1`
  (`integral_abs_coinMartingale_le`) and compensator `0`, so the pair `(M, 0)`
  lies in `𝓐 n` for every exponent and with `K = 0`; yet
  `𝔼|M t - M s| = 1` across `u` (`integral_abs_coinMartingale_sub_eq_one`), and
  `exists_integral_abs_coinMartingale_sub_eq_one` finds such a pair **inside a
  window of length `δ`, for every `δ > 0`, with `u = 1` held fixed**. The
  martingale does not move with `δ`; only the window does. Hence the closure of
  the approximable functions under products is a consequence of the estimate
  and not an assumption of convenience.
* **The approximability condition, and the order of the three limits.**
  `MeasureTheory.IsApproximable 𝓕 P q T K V ε₀ u`: to every positive error
  there are two pairs of the class `MeasureTheory.IsApproximatingPair` with one
  and the same `q`, `T`, `K`, approximating `V` and `V²` to within that error on
  the horizon `Set.Iic T`, together with the four integrabilities of their
  stopped values. This is \EK, Theorem 9.4, written as a predicate on the
  process it approximates, so that a consumer never has to speak of
  `⨆ n, 𝔼[eLpNorm (Z n) q] < ∞`.

  **The errors are read on one fixed window and this is the decision the
  predicate makes.** The assembly reads them on `Set.Iic (u + δ)`, which moves
  with `δ`, and a hypothesis that moves with the variable of a limit is not one
  a limit can be taken under. `Set.Iic T` is the natural fixed window because
  `u + δ ≤ T` is asked anyway, and the passage back is one line,
  `MeasureTheory.lintegral_biSup_Iic_mono`, the `biSup_mono` under
  `lintegral_mono` the assembly already wrote once. That lemma is stated over an
  abstract `F : ℝ≥0 → Ω → ENNReal` and not inline, because inline the same four
  lines run into a `whnf` timeout of 200000 heartbeats: the elaboration carries
  the integrand along.

  **`ε₀` and `u` are parameters of the predicate, and that is the weakest form
  it has.** The four integrabilities stand at the stopped values along
  `MeasureTheory.oscHitSeq V ε₀` capped at `u`, so they see `ε₀` and `u`, and no
  reformulation on a window hides that. Quantifying instead over all times
  bounded by `T` would ask for an integrable supremum over the horizon, which is
  strictly more. The window `δ` *is* quantified inside, because it is the
  variable of the second limit and a consumer may not be asked for a hypothesis
  per value of it.

  **The third limit, once and for all:**
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximable` is the
  assembly with `A = 2 ε' + 4 ofReal c * ε` replaced by `0`,

  ```
  ofReal ε₀ * P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ N * ofReal √(((1 + 2 c) * (ofReal δ ^ (1 - 1/q) * K)).toReal)
      + ofReal u ^ (1 - 1/q) * K * (1 + 2 ofReal c) / N / ofReal ε₀
  ```

  the statement in which the approximants no longer occur. The limit runs along
  the sequence of errors `(n : ℝ≥0∞)⁻¹` under `ge_of_tendsto` over `atTop`, whose
  `NeBot` is free, and nothing is lost by it: the left hand side does not depend
  on the approximants, so a bound holding at each `n` passes to the limit. What
  is proved is the continuity of the right hand side at `A = 0`, which is
  `ENNReal.tendsto_toReal` at the finite
  `(1 + 2 c) * (ofReal δ ^ (1 - 1/q) * K)` and `ENNReal.Tendsto.div_const`.

  **And then the first two:**
  `MeasureTheory.tendsto_measure_setOf_lt_modulusBased_of_isApproximable`,

  ```
  Tendsto (fun δ : ℝ≥0 ↦ P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ ω)) δ})
    (𝓝[>] 0) (𝓝 0)
  ```

  for `0 < u`, `u < T`, `0 < ε₀`. This is the probabilistic content of \EK,
  Theorem 9.4. **The order of the limits is the proof and is visible in it**:
  given a target `η`, the count `N` is chosen first from the horizon term
  `B / N / ofReal ε₀`, which is `O(1/N)` and does not see `δ`; the window `δ`
  second, at that fixed `N`, from
  `MeasureTheory.tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero` at `A = 0`; and the
  error is already gone. `ENNReal.add_halves` adds the two halves.

  **Both horizon hypotheses are strict and each is spent once.** `0 < u` is what
  makes `δ < u` hold near `0`; `u < T` is what makes `u + δ ≤ T` hold there. A
  non-strict `u ≤ T` would leave no room for `δ`, and the statement would be
  about an empty set of admissible windows.

  **A limit Mathlib has for every division semiring and not for `ℝ≥0∞`.**
  `tendsto_const_div_atTop_nhds_zero_nat`
  (`Mathlib/Analysis/SpecificLimits/Basic.lean:52`) asks `DivisionSemiring 𝕜`,
  which `ℝ≥0∞` is not — `⊤` has no inverse — so the horizon term is brought to
  `ENNReal.tendsto_inv_nat_nhds_zero`
  (`Mathlib/Topology/Instances/ENNReal/Lemmas.lean:484`) by `div_eq_mul_inv` and
  one `ring`. That is a typeclass boundary and not a gap in the library.

  **And the same at an image path**,
  `MeasureTheory.tendsto_measure_setOf_lt_modulusBased_postcomp_of_isApproximable`,
  for a bounded continuous `g : E →ᵇ ℝ` and an `E`-valued `X` with `g ∘ X`
  approximable: the same limit for
  `SkorokhodSpace.postcomp g (SkorokhodSpace.extendNNReal (Φ ω))`. It is the
  statement above at `V = g ∘ X` and the four steps of the passage are those of
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_postcomp_le_of_isApproximatingPair`.
  This is the shape `isTight_map_postcomp_of_exists_martingale` consumes, one
  test function at a time; what still separates the two is the uniformity over
  the family, and the constants `u`, `q`, `K`, `‖g‖` of the bound behind it are
  there precisely because none of them belongs to a member.
* **What approximability excludes, and it is the deterministic jump.**
  `MeasureTheory.IsApproximable.integral_eq_of_eqOn_Ico`: if `V` is constant on
  `Set.Ico a b` — the same value at every time of the cell *and* at every sample
  point — and `b ≤ T`, then an approximable `V` has `∫ V b = ∫ V a`. With it
  `MeasureTheory.not_isApproximable_of_eqOn_Ico_of_integral_ne` and the smallest
  witness, `MeasureTheory.not_isApproximable_indicator_Ici`: the unit step
  `1_{[b,∞)}`, a process with no randomness whatever, is approximable by no pair.

  **The proof reads the mean of the martingale and nothing else**, so the
  filtration does not enter: the mean of a martingale is constant over any
  filtration. Between a time `r` inside the cell and `b` the mean of `Y` moves by
  the mean of the compensator alone, and that is bounded by
  `MeasureTheory.IsApproximatingPair.lintegral_enorm_compensator_sub_le` at the
  window `(r, b]`, whose bound `ofReal (b - r) ^ (1 - 1/q) * K` goes to zero as
  `r` climbs to `b`. That is where the absolute continuity of the compensator is
  spent, and it is the only place. Enlarging `𝓕` — revealing the increment of a
  discretely indexed process gradually across the cell — is therefore no escape;
  the obstruction is not adaptedness but that an indefinite integral has no
  atoms, while the compensator of a jump at a *deterministic* time is a Dirac
  mass.

  **The two auxiliaries it needs are stated for their own sake**, both being
  what any statement about the mean of an approximating pair wants and neither
  being a field of the class:
  `MeasureTheory.IsApproximatingPair.stronglyMeasurable_compensator` — `C` is
  `Y - (Y - C)`, so the two progressivity fields give it —,
  `MeasureTheory.IsApproximatingPair.integrable_compensator`, which is the
  compensator bound at the window `(0, t]` with
  `MeasureTheory.IsApproximatingPair.compensator_zero` removing the lower end,
  and the general passage
  `MeasureTheory.abs_integral_sub_le_of_lintegral_enorm_sub_le` between the
  `ENNReal` shape of the approximation errors and the real shape of a mean.

  **It fixes the quantifier order the criteria of this milestone are read
  under.** A family whose members jump at deterministic times has `IsApproximable`
  at **no** member, so the hypothesis `happ` of
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_isApproximable` and of
  the four statements above it is unsatisfiable on such data. The rescaled random
  walks of the acceptance test are such a family: read as step paths they jump at
  the deterministic times `k / c`, and their compensator along the grid is purely
  atomic. \EK quantify (9.26) along the index, and so are these items to be read:
  the approximation error goes to zero **with the family**, the finitely many
  members it does not yet cover being tight one by one. The items themselves are
  true as they stand and are not withdrawn; what changes is which data they are
  applied to.
* **Finitely many members may be exempted.**
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_isApproximable_off_finite`:
  the hypothesis of the item above asked of all `i ∉ G` for a finite `G : Set γ`
  gives the same conclusion. The members outside `G` go through that item,
  instantiated at the subtype `↥Gᶜ` — its constants `q`, `T`, `K` are already
  uniform in the member, so the hypothesis restricts verbatim — and the members
  of `G` are finitely many probability measures.

  Two general statements carry it, and they are about tightness alone:
  `MeasureTheory.isTightMeasureSet_of_finite`, a finite set of finite measures is
  tight, and `MeasureTheory.isTightMeasureSet_range_of_finite_compl`, a family is
  tight as soon as it is tight off a finite set of indices.
  **Mathlib has the two ends and not the middle**, read at the source on
  2026-09-21 against `94ef6b89544`: `MeasureTheory.isTightMeasureSet_singleton`
  (`Mathlib/MeasureTheory/Measure/Tight.lean:99`) and
  `MeasureTheory.IsTightMeasureSet.union` (`:119`, a `protected lemma union`
  inside `namespace IsTightMeasureSet`, so the qualified name occurs nowhere in
  the source), beside `.subset` (`:114`), `.inter` (`:125`) and `of_compactSpace`
  (`:109`). In that file the word `Finite` occurs only in the docstrings of the
  singleton statements: the iterate of `union` is not there.

  **The exceptional set is data of the statement and not a filter.** The
  hypothesis reads `∀ ε₀, ∀ u, ∃ q T K, ∀ i`, so a filter phrasing `∀ᶠ i in F`
  could only sit innermost, and along *this* route the exceptional set may not
  move: the proof splits the family once and for all, and a split varying with
  the horizon `m : ℕ` — which the consumer quantifies unboundedly — would union
  to an infinite exceptional set. `Filter.cofinite` therefore buys nothing here,
  and a moving exemption needs the other route, which is the next item.

  (The three filter phrasings are not interchangeable, and the comparison is
  recorded once so that it is not made again: `∀ᶠ i in F` under `cofinite ≤ F` —
  that is, `F.sets ⊆ cofinite.sets` — says exactly that the complement is finite,
  and `∀ᶠ i in cofinite` is the weakest of them, hence the strongest statement.
  For `γ = ℕ` it is reached from `atTop` by `Nat.cofinite_eq_atTop`.)

  **What it does not reach, stated so that no run mistakes it.** The
  approximation error `ε` is quantified **inside** `MeasureTheory.IsApproximable`,
  so a member is approximable either to every error or to none, and by the item
  above a rescaled random walk is approximable to none. A family whose `n`-th
  member is approximable only to within some `ε n` with `ε n → 0` is therefore
  exempted by no finite `G`. That is the weakening \EK (9.26) actually make, it
  moves the `∀ ε` of the structure out past the index, and it is a different
  statement rather than an instance of this one.
* **The exempted set may move with the window.**
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_isApproximable_off_finite_window`:
  the finite `G` is produced **inside** the hypothesis, after `ε₀` and `u`, so a
  family whose members become approximable only as the accuracy asked is relaxed
  satisfies it, and the item above is its instance at a `G` depending on neither.

  **Why the move is admissible here and not there.** The item above splits the
  family once and for all and needs the split to be the same at every horizon;
  this one never splits it. It goes through
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le_off_finite`
  of **SkorokhodSpace**, Milestone 7, which supplies the exempted members with
  their own window out of the tightness of their single image law — the
  criterion there is an equivalence, so it gives as well as takes — and there the
  exemption is consumed one horizon at a time.

  **What it still does not reach, and the three items below do.** The error `ε`
  remains quantified inside `MeasureTheory.IsApproximable`, so a member is
  approximable to every error or to none. The lever for moving it out is
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair`,
  which carries the error of the approximants as an explicit summand `A` on its
  right hand side, while
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximable` discards
  it in a limit along `ε = (n : ℝ≥0∞)⁻¹`.
* **The error quantified outside the index.**
  `MeasureTheory.IsEventuallyApproximable 𝓕 P q T K V ε₀ u` for a family
  `V : γ → ℝ≥0 → Ω → ℝ`: to every positive error a **finite** `G : Set γ`, off
  which every member has two pairs of `MeasureTheory.IsApproximatingPair`, with
  one and the same `q`, `T`, `K` for the whole family and every error,
  approximating it and its square to within that error, together with the four
  integrabilities the assembly reads. The exceptional set moves with the error;
  the constants do not, and that is what the uniformity over the family rests
  on.

  **The filtration is indexed by the family**, `𝓕 : γ → Filtration ℝ≥0 mΩ`, and
  so are the progressivity hypothesis and the right continuity instance of the
  two consumers below. That is not generality on suspicion but what this
  milestone's own acceptance test needs: the rescaled walks of Donsker's theorem
  are martingales over `MeasureTheory.floorFiltration` of their own mesh, and
  **no single filtration serves them all**. Adaptedness of the member at mesh
  `m` at a positive time `t` puts `σ (ξ_0, …, ξ_{⌊t (m+1)⌋ - 1})` into `𝓕 t`,
  and `⌊t (m+1)⌋ → ∞` along the family, so a shared `𝓕 t` would carry the whole
  tail `σ (ξ_k : k)` at *every* positive time; over such a filtration the
  increments of any member are already known and the martingale field forces
  them to vanish. A shared filtration therefore reaches no nondegenerate family
  of walks at all.

  **Nothing joins two members through the filtration**, which is what makes the
  indexing free: the estimate under the criterion reads `𝓕` only at the member
  it is estimating, the quantities shared across the family being the scalars
  `q`, `T`, `K`, `ε₀`, `u` and the exceptional set. A consumer with one
  filtration passes the constant family.

  `MeasureTheory.isEventuallyApproximable_of_forall_isApproximable` reads the
  relation to the condition above: approximability off a finite set is this
  condition at a `G` that does not move, so this is a weakening of that and not
  a different condition.

  **The form a consumer arrives with is the other one**, and it is the same
  statement: `MeasureTheory.isEventuallyApproximable_of_tendsto_zero_cofinite`
  asks that **every** member have pairs, their error `e i` going to zero along
  `Filter.cofinite`. The exchange is the equivalence `Filter.eventually_cofinite`
  (`Mathlib/Order/Filter/Cofinite.lean:49`) and nothing else — `{i | ¬ e i ≤ ε}`
  finite *is* the exceptional set at the error `ε`. `Filter.cofinite` and not
  `Filter.atTop`: the structure asks for a finite set, and `atTop` says that only
  for an ordered index, the two agreeing on `ℕ` by `Nat.cofinite_eq_atTop`.
* **Tightness of the image laws from eventual approximability.**
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_isEventuallyApproximable`:
  the conclusion of the two items above under
  `MeasureTheory.IsEventuallyApproximable` at every horizon. Under it is the
  uniform estimate
  `MeasureTheory.exists_finite_forall_measure_setOf_lt_modulusBased_postcomp_le_of_isEventuallyApproximable`,
  which produces one exceptional set and one window serving every member outside
  it.

  **The order of the three choices is `N`, `ε`, `δ`, and not `N`, `δ`, `ε`.**
  The chain above sends the error to zero in a limit and after that limit the
  approximants no longer occur; here the error survives into the estimate, so
  the count is chosen first at no window, the **error** second — which is where
  the exceptional set is born, hence before the window — and the window last at
  that error, from
  `MeasureTheory.tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero` at `A = a₀` rather
  than at `A = 0`. That limit is `N · √a₀` and not `0`, so the error is chosen
  to leave it strictly below its share of the budget. The statement with a free
  `A` was proved before this item and is what it reads.

  The budget `θ = ofReal ε₀ * η` is split as `θ/2` for the gap term and twice
  `θ/4` for the horizon term and the error term; `η = ⊤` is disposed of first,
  so the halves are strict. The exponent `1 < q` is read off a member through
  the exceptional set at the error `1`, and an exceptional set exhausting the
  index makes the conclusion vacuous.
* **The witness that the exchange of quantifiers is not idle.** The family of
  deterministic unit steps at a fixed time `b` of height `(i+1)⁻¹`,
  `i : ℕ`. `MeasureTheory.not_isApproximable_scaledStep` says **no** member of
  it is approximable — the obstruction of
  `MeasureTheory.not_isApproximable_indicator_Ici`, an atom of the compensator
  at a deterministic time, which no error absorbs at a fixed member — while
  `MeasureTheory.isEventuallyApproximable_scaledStep` says the family is
  eventually approximable, the approximants being the zero pair
  (`MeasureTheory.isApproximatingPair_zero`) and the exceptional set the initial
  segment of indices whose height exceeds the error.

  It is therefore tight by the item above and reached by neither of the two
  items before it, which is the strictness of the weakening. The same shape is
  what a family of rescaled random walks has, with the height of a single jump
  in place of `(i+1)⁻¹`; what the witness establishes is the quantifier
  structure and not that particular family.
* **The same estimate uniformly over the family.**
  `MeasureTheory.exists_forall_measure_setOf_lt_modulusBased_postcomp_le_of_forall_isApproximable`:
  for a family `X : γ → ℝ≥0 → Ω → E` over **one** probability space, all
  approximable with the **same** `q`, `T`, `K`, and one `g : E →ᵇ ℝ`,

  ```
  ∀ η > 0, ∃ δ > 0, ∀ i,
    P {ω | ofReal ε₀ < modulusBased 0 u (postcomp g (extendNNReal (Φ i ω))) δ} ≤ η.
  ```

  **It is not the limit above stated for each member.** A `Tendsto` per member
  gives a `δ` per member, and the criterion needs one `δ` for all of them. The
  uniform statement is therefore proved at the *inequality*,
  `MeasureTheory.mul_measure_setOf_lt_modulusBased_postcomp_le_of_isApproximable`
  — the assembly at an image path, which stands for this reason and for no other
  — with `N` and `δ` quantified before the member. That this is possible is a
  reading of that inequality and not a further argument: on its right hand side
  stand `u`, `q`, `K`, `‖g‖`, `N`, `δ` and `ε₀`, and **no member occurs**. The
  common `q`, `T`, `K` of `MeasureTheory.IsApproximable` are the whole content of
  the uniformity.

  **One `ε₀` and one `u` suffice, and that is read off the consumer.**
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_iff` quantifies its bound `ε`,
  its horizon `m` and its threshold `η` **outside** the `∃ δ`, so a consumer
  arrives with all three fixed and instantiates once per triple. Asking instead
  for `∀ ε₀ > 0, ∀ i, IsApproximable … ε₀ u` would be strictly stronger and buy
  nothing.

  **The empty family carries no exponent, and no hypothesis is added for it.**
  `1 < q` is read off a member
  (`MeasureTheory.IsApproximable.one_lt_exponent`), so an empty `γ` has none to
  read it from; there the conclusion is vacuous and `δ = 1` serves. Carrying
  `1 < q` as a hypothesis would burden the nonempty case with what it already
  has.

  **The window is produced in `ℝ`**, the shape the consumer reads, and it exists
  because `𝓝[>] (0 : ℝ≥0)` is `NeBot` — `nhdsGT_neBot`,
  `Mathlib/Topology/Order/DenselyOrdered.lean:222`, `ℝ≥0` having no maximum — so
  positivity, the two window conditions and the smallness of the gap term are met
  at one point.

  **What still separates this from the criterion**, and it is two things and not
  one. The criterion measures a set of *paths* under the image law
  `((μ i).map (postcomp g)).map extendNNReal`; this measures a set of *sample
  points* under `P`. And its threshold enters as `η ≤ modulusBased …` where this
  one has `ofReal ε₀ < modulusBased …`. The strictness is bridged by taking `ε₀`
  below the threshold; the change of measure is the next item, and it is not
  formal. Checked at the source, 2026-09-21:

  - `MeasureTheory.Measure.map_apply` (`MeasureTheory/Measure/Map.lean:170`) asks
    the set be measurable, and `MeasureTheory.Measure.map_apply₀` (`:157`) asks
    it be null measurable for the image measure. The modulus sets are among those
    this roadmap never asserts measurable.
  - The only statement over an **arbitrary** set is
    `MeasureTheory.Measure.le_map_apply` (`:218`),
    `μ (f ⁻¹' s) ≤ μ.map f s`, and it runs the **wrong way**: a producer who has
    a bound on the preimage does not thereby have one on the image law.
  - **One of the two layers is nevertheless free.**
    `MeasurableEmbedding.map_apply` (`:271`) holds for arbitrary sets, and
    `SkorokhodSpace.extendNNReal` is a measurable embedding because it is a
    closed one (`SkorokhodSpace.isClosedEmbedding_extendNNReal` with
    `Topology.IsClosedEmbedding.measurableEmbedding`,
    `MeasureTheory/Constructions/BorelSpace/Basic.lean:684`). So the index
    crossing costs nothing here, and what remains is the layer
    `SkorokhodSpace.postcomp g ∘ Φ i`, which is no embedding, `g` not being
    injective.

  **The measurability is decided, 2026-09-21, and the answer is the first of the
  two: the second option is not needed and the criterion is not to be restated.**
  `SkorokhodSpace.measurable_iInf_modulusBased` of **SkorokhodSpace**,
  Milestone 7, is the Borel function, and it is *not*
  `fun f ↦ SkorokhodSpace.modulusBased t₀ u f δ` itself but the right limit of
  that in the window radius,
  `fun f ↦ ⨅ u' ∈ Set.Ioi u, SkorokhodSpace.modulusBased t₀ u' f δ`. The
  sandwich `SkorokhodSpace.setOf_le_modulusBased_subset` and
  `SkorokhodSpace.setOf_le_iInf_modulusBased_subset` puts the set the criterion
  reads between two sets of the Borel function, so a producer who holds a bound
  at radius `u'` pays for the passage with the single step from `u` to `u'` and
  with nothing else. The consumer here quantifies over all `m : ℕ`, so the step
  is `m ↦ m + 1` and is free.

  What makes the right limit necessary rather than an artefact: the time change
  that carries a subdivision from one path to a nearby one *moves the window*, so
  the subdivision has to cover a strictly larger radius than the conclusion
  speaks of. The loss in the **sparseness** — the other loss of
  `SkorokhodSpace.modulusBased_le_of_edist_le` — does go away, a fixed
  subdivision having finitely many gaps each strictly wider than `δ`.

  **And the route through a countable family is closed, which is why this one is
  taken.** Restricting the nodes to a countable dense set computes a strictly
  larger infimum for a path that jumps outside that set: every such subdivision
  has the jump in the interior of a cell.

  **The passage is carried out, 2026-09-21, and the criterion is closed on the
  sample side.** `SkorokhodSpace.measure_map_postcomp_setOf_le_modulusBased_le`
  is the change of measure --- a bound on the modulus set at radius `u'` over
  `P` is a bound at every `u < u'` under
  `((P.map Φ).map (postcomp g)).map extendNNReal` --- and
  `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le`
  is that in the shape the criterion reads: a bound at `(m : ℝ) + 1` for every
  `m : ℕ` gives `IsTightMeasureSet {(P.map (Φ i)).map (postcomp g) | i}` with no
  further hypothesis. Both layers are pushed forward at once by
  `MeasureTheory.Measure.map_map`, the two orders of `postcomp` and
  `extendNNReal` being definitionally equal by
  `SkorokhodSpace.postcomp_extendNNReal`.

  **The two halves are joined, 2026-09-21**, by
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_isApproximable`: from
  approximability at every window radius follows the tightness of the image laws
  `{(P.map (Φ i)).map (postcomp g) | i}`. The measurability of the path map is
  not among its hypotheses, being implied by the progressivity
  (`MeasureTheory.measurable_pathOfProcess`).

  Two seams were crossed there, and neither is analytic. The first is the
  **threshold**: the sample bound reads `ofReal ε₀ < modulusBased …` and the
  criterion `η ≤ modulusBased …`, so an `ε₀` below `η` is chosen and
  `measure_mono` closes; `ENNReal.lt_iff_exists_real_btwn` produces it for every
  `η > 0` including `η = ⊤`, carrying no finiteness hypothesis. The change of
  measure carries `η` through unchanged and puts no condition on it, which is why
  the strictness is settled at this seam and not at the other.

  The second is the **horizon**, and it is the one that shapes the statement: the
  criterion quantifies `m : ℕ` unboundedly while `MeasureTheory.IsApproximable`
  carries a fixed `T` with `u < T`, so a single triple `(q, T, K)` serves only
  finitely many `m`. The hypothesis therefore quantifies over the window --- to
  every radius its own `q`, `T`, `K` --- which is not a strengthening but the
  form this milestone states above, „for all `ε, T > 0` there are
  `(Y n, Z n) ∈ 𝓐 n`". The fixed-`T` statement is wrapped, not altered.

  **The condition of this item and `MeasureTheory.IsApproximable` are not the
  same condition, 2026-09-21, and the difference is the right endpoint.** The
  display above reads its errors over `Set.Iic T ∩ D` for a countable `D`, which
  is the form under which the quantity is measurable; `IsApproximable` reads them
  over the whole window `Set.Iic T`, which is the form the assembly needs, the
  times substituted into it being hitting times. For a right continuous path the
  window supremum is determined by a dense set **together with the value at the
  right end** — that is the `insert T` of
  `biSup_enorm_Iic_eq_of_isRightContinuous` — so a path that jumps exactly at `T`
  is seen by the second condition and not by the first. The condition at horizon
  `T` therefore does **not** give `IsApproximable` at `T`.

  **What closes that gap is the quantifier this item already carries**, and it
  costs nothing: the condition holds „for all `ε, T > 0`", so it is available at
  a strictly larger horizon `T' > T`, and there the dense set reaches past `T`
  from the right. That is
  `MeasureTheory.biSup_enorm_Iic_le_biSup_enorm_inter_dense`, whose whole proof
  is `SkorokhodSpace.mem_of_continuousWithinAt_of_forall_mem_dense` at the closed
  set `Set.Iic c` — the **half open** window, which reads no endpoint at all, and
  it is why the lemma needs no `OrderBot` on the index. Enlarging the horizon
  is free on the other side too, an approximating pair at `T'` being one at `T`
  with the same `q` and the same `K`
  (`MeasureTheory.IsApproximatingPair.mono_horizon`), and the consumer asks
  `u < T` anyway, so `u < T < T'` comes from `exists_between`.

  **The countable set `D` of the display and the `S` of the tightness estimate
  are two roles of one object, and the roles read different things of it.** `S`
  enters the début of the oscillation sets, where its **countability** makes the
  Aldous hitting times stopping times; `D` enters nowhere but the error suprema,
  and of it the passage reads only **density** — its countability is what makes
  the milestone's quantity measurable and is nowhere used in this direction.
  `MeasureTheory.isApproximable_of_forall_exists_pair` keeps them apart and
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_exists_pair` takes them
  equal, a consumer having no use for the distinction. The naming follows the
  rule already recorded at
  `mul_measure_setOf_lt_modulusBased_le_lintegral_dist`: the set is `S` wherever
  the path space notation `D(ℝ≥0, E)` occurs and `D` everywhere else.

  **The passage is carried out, 2026-09-21**, as
  `MeasureTheory.isApproximable_of_forall_exists_pair`, and composed with the
  two seams above it gives the item with `IsApproximable` no longer in its
  statement:
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_exists_pair` — from
  the condition of this display, at every window radius and at a horizon
  exceeding it, follows the tightness of the image laws
  `{(P.map (Φ i)).map (postcomp g) | i}`.

  **Right continuity of `Y - f ∘ X` is a hypothesis of the general statement and
  is carried inside the existential**, `Y` depending on the error. It is the same
  price `MeasureTheory.lintegral_enorm_sub_le_of_biSup_Iic_le` pays and at the
  same place — \EK's (9.27) holds for all real times and not merely for rational
  ones by right continuity.

  **It is derived from the data in the bounded form, 2026-09-21, and the derivation
  costs a window.** `IsApproximatingPair.rightContinuous` gives the right
  continuity of `Y - C`, so what is missing is the continuity of the indefinite
  integral `C`, and that is
  `MeasureTheory.IsApproximatingPair.continuousWithinAt_compensator`: Mathlib's
  `intervalIntegral.continuousOn_primitive`
  (`MeasureTheory/Integral/DominatedConvergence.lean:439` — the statement lives
  in namespace `intervalIntegral`, not in `MeasureTheory`) at the path of `Z`,
  whose integrability on the horizon is `IsApproximatingPair.ae_integrableOn`,
  followed by `ContinuousWithinAt.mono_of_mem_nhdsWithin` to pass from
  `Set.Icc 0 T` to `Set.Ioi t` and by the coercion `ℝ≥0 → ℝ`.

  **The window is not an artefact of the proof.** `C t ω` is `∫_{(0,t]} Z s ω`
  for every `t`, and the integrability of the path of `Z` is known only on the
  horizon; past it the integral is a Bochner junk value and `C` need not be
  continuous anywhere. So
  `MeasureTheory.IsApproximatingPair.ae_continuousWithinAt_sub` gives the right
  continuity of `Y - V` **strictly inside the horizon** and cannot give more.
  That is why the statements of this item read right continuity on `Set.Iic T`
  rather than on the line, and why the dense window lemma had to be restated
  pointwise: the windows `Set.Ico t T'` it takes reach past `T`.

  **What the derivation asks of `V` is already in the signature**: continuity
  from the right of every path, which is what the oscillation hitting times need
  anyway and what a càdlàg path composed with a continuous `f` delivers. For the
  squared error it is `ContinuousWithinAt.pow`.

  **The four integrabilities are discharged from a bound on the approximants,
  2026-09-21, and that bound is what the class was always meant to supply.** The
  docstring of `MeasureTheory.IsApproximatingPair` records under „What is *not* a
  field, and why" that no integrability of the stopped values belongs to the
  class, „a consumer holding them from a bounded `f`";
  `MeasureTheory.IsApproximatingPair.integrable_stoppedValue_of_bounded` is that
  sentence as a theorem — a bounded approximant has an integrable stopped value
  at every stopping time bounded by an index — and its whole proof is Mathlib's
  `MeasureTheory.stronglyMeasurable_stoppedValue_of_le`
  (`Probability/Process/Stopping.lean:1016`) against `integrable_const`. Of the
  measure it reads finiteness and not normalisation.

  **And the bound is a majorant, 2026-09-22**, not a constant:
  `MeasureTheory.IsApproximatingPair.integrable_stoppedValue_of_dominated` asks
  only for an integrable `g` with `‖Y t ω‖ ≤ g ω` for `t ≤ j`, and the bounded
  case is its instance at `g` constant. The generalisation is not for its own
  sake and the acceptance test is what asks for it: a rescaled random walk is
  **not** bounded, its value at stage `k` being a partial sum of independent
  summands, while on a bounded stretch of time it is dominated by the sum of the
  finitely many stage values it can take there, which is integrable. With a
  constant majorant the class reaches no unbounded approximant, and
  `MeasureTheory.IsApproximable` demands the four integrabilities of every
  member of it. The domination is asked **only up to `j`**, `WithTop.untopA_le`
  putting the reading point of the stopped value below `j`, so nothing is
  hypothesised about values the statement never looks at.

  **Both Aldous times carry the bound the statement needs, and they carried it
  before the question was asked.** The capped time is below `u` by
  `min_le_right`; the gapped time is below `((u + δ : ℝ≥0) : WithTop ℝ≥0)` by
  `MeasureTheory.oscHitSeqGap_le_coe`, which has stood since the times were
  built. So the capped and the gapped case are one statement applied twice
  (`MeasureTheory.IsApproximatingPair.integrable_stoppedValue_oscHitSeqCap`,
  `…_oscHitSeqGap`) and not two shapes: the sum `α + δ` is formed in
  `WithTop ℝ≥0` throughout, and the split between that type and `ℝ≥0∞` recorded
  at `setOf_lt_modulusBased_subset_oscHitSeq` does not arise.

  **Ten obligations per error become six.**
  `MeasureTheory.isApproximable_of_forall_exists_bounded_pair` and
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_exists_bounded_pair`
  are the two statements above with the four families of integrabilities
  replaced by one bound on each approximant and the two right continuities
  discharged from the data; the two bounds are separate and nothing compares
  them. What is left is what (9.26) asks for and nothing else: **two pairs, two
  bounds, two errors**. In the general form the dense set of the errors and the
  countable dense set of the times are kept apart — density alone is read of the
  first, countability alone of the second — and the tightness statement takes
  them equal, as it does already.

  **The bound is not derivable from the bound on `f`.** `Y` approximates `f ∘ X`
  in `L¹` of a supremum, which constrains no path of `Y` pointwise. It is a
  condition on the class the approximants are drawn from, and this milestone
  states it there.

  **The step above the pairs** is what produces them: for an *exact* solution it
  is the martingale hypothesis read twice, at `f` and at `f²`, and that is
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_martingale` below. For
  *approximants* it is the martingale approximation together with the closure of
  the approximable functions under products, which is what makes the **second**
  pair approximate `f²` and not `f`. That closure is a witness and not a
  convenience — the second approximant is not the square of the first — and it is
  where the continuous time Doob inequalities of Milestone 9 are used.
  Everything below it is built.

  **The class is inhabited, 2026-09-21.**
  `MeasureTheory.isApproximatingPair_of_martingale`: a process `X` that is
  strongly progressive with right continuous paths and for which
  `fun t ω ↦ f (X t ω) - ∫ s in Set.Ioc 0 t, g (X s.toNNReal ω)` is a martingale
  gives a pair of the class, with `Y = f ∘ X`, density `Z = g ∘ X`, compensator
  the indefinite integral, and constant `K = T ^ q.toReal⁻¹ * ‖g‖₊` — a
  **formula** in the data, which is the uniformity this item rests on: a family
  of processes tested with one `g` has one `K`. The error against `f ∘ X` is
  zero, so the approximation condition is met by the process itself whenever `f`
  and `g` are bounded continuous, which is what a bounded generator supplies. The
  hypothesis is the martingale problem, and the conclusion is membership in
  \EK's class `𝓐 n`.

  **`E` carries a topology and nothing else** — no σ-algebra, no metric, no
  completeness. Every object read is a *real* functional of the path, so the
  joint measurability of the `E` valued path is never needed; that is what
  `measurable_uncurry_min_of_rightContinuous`, stated for real valued processes
  for exactly this reason, buys.

  Four statements of general use carry it, and three of them are about no
  filtration and no measure:

  * `MeasureTheory.tendsto_nhdsGE_comp_toNNReal` — right continuity survives the
    clamp `Real.toNNReal`, which is what turns a process indexed by `ℝ≥0` into a
    density indexed by `ℝ`.
  * `MeasureTheory.measurable_of_tendsto_nhdsGE` — a right continuous real
    function of a real variable is Borel measurable. **Mathlib has this in no
    shape**, checked 2026-09-21 against
    `94ef6b89544e58e90f119da869f3fb48d1da0f4c`:
    `Mathlib/Topology/Order/Cadlag.lean`, where `IsRightContinuous` and
    `IsCadlag` live, carries no measurability at all, and the occurrences of
    `IsRightContinuous` outside it are about filtrations. What Mathlib has is
    `Monotone.measurable`, which is how a `StieltjesFunction` becomes
    measurable — monotonicity, not right continuity — and a càdlàg path is
    neither monotone nor continuous. It is a named Mathlib gap and belongs in
    `TODO.md` item 8.
  * `MeasureTheory.continuous_setIntegral_Ioc_zero_real_of_bounded` — the
    previous item's continuity at a *real* upper end, where the dyadic argument
    reads it and where negative times occur.
  * `MeasureTheory.stronglyMeasurable_integral_uncurry` —
    `StronglyMeasurable.integral_prod_left` packaged for a σ-algebra that is not
    an instance. It is the companion of
    `MeasureTheory.stronglyMeasurable_integral_comp`, and the difference decides
    the hypotheses of the whole item: that one asks for a **measurable** map into
    a measurable space, this one for a **strongly measurable** real valued
    integrand, and only the second is available over an `E` with no σ-algebra.

  **The one field that is work is `progressive_sub`**, and it is two steps. Below
  a fixed `t` the window `Set.Ioc 0 r` lies in `Set.Ioc 0 t`, so the integrand
  may be replaced by the **cut** integrand `g (X (min s.toNNReal t) ω)`, jointly
  strongly measurable for `Borel ℝ ⊗ 𝓕 t` because `IsStronglyProgressive` says
  exactly that on `Set.Iic t × Ω`; the packaging above integrates it out. That
  gives measurability at each fixed time below `t`, and
  `measurable_uncurry_min_of_rightContinuous` turns it into joint measurability,
  its second hypothesis being the right continuity of the paths — the same one
  the field `rightContinuous` asks for.

  **Three of its eight fields were settled separately, and they are the ones a
  bounded density gives.** Every statement of this item before that *consumed*
  `MeasureTheory.IsApproximatingPair` and none produced one, which is the
  emptiness question `Shift` was held to in Milestone 6. The intended inhabitant
  is \EK's own: for `f` in the domain and `g` its image under the generator,
  `Y = f ∘ X`, `Z = g ∘ X`, `C` the indefinite integral of `Z`, the martingale
  field being the martingale problem itself and the error **zero**. Three fields
  are then statements about a bounded measurable density and about nothing else:

  * `MeasureTheory.continuous_setIntegral_Ioc_zero_of_bounded` — the indefinite
    integral of a bounded measurable function is continuous in its upper end over
    `ℝ≥0`. This is what meets `IsApproximatingPair.rightContinuous`, and it is
    needed in this shape: that field is quantified over **all** `s : ℝ≥0`, while
    `IsApproximatingPair.continuousWithinAt_compensator` stops at the horizon
    because its density is known integrable only there. **Boundedness is what
    buys the line**, integrability then holding on every window.
  * `MeasureTheory.eLpNorm_le_of_bounded_Ioc` — the `L^q` norm over the horizon is
    at most `T ^ q.toReal⁻¹ * c`. So the constant `K` is a **formula** in the
    bound and the horizon and not a hypothesis, which is what the uniformity of
    this item needs: one `K` for the whole family.
  * `MeasureTheory.memLp_of_bounded_Ioc` — the field `ae_memLp`, and it holds at
    *every* sample point, so that field's almost sure quantifier is not used by
    this source.

  The density of the class is indexed by `ℝ` and every process of this milestone
  by `ℝ≥0`, so a consumer writes `Z s ω = g (X s.toNNReal ω)`; the junk on
  `s ≤ 0` is never read, the integral of `compensator_eq` running over
  `Set.Ioc 0 t`.

  **And a correction of the route to `progressive_sub`**, which is the one field
  the three above do not cover. The tool named for it was
  `MeasureTheory.stronglyMeasurable_integral_comp`, and it does not reach: that
  statement asks for `Measurable (uncurry W)` into a **measurable space** and a
  measurable function on it, which over an `E` with no σ-algebra is not
  available, and demanding one would make the whole item carry a hypothesis on
  `E` that nothing in its proof reads.
  `MeasureTheory.stronglyMeasurable_integral_uncurry` is the same packaging of
  the same Mathlib lemma with the integrand **strongly measurable and real
  valued** instead, and it costs the construction nothing.

  **The item stands for a family of solutions, 2026-09-21.**
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_martingale`: a family
  `X i` of processes on one filtered probability space, strongly progressive
  with right continuous paths, for which **both**
  `f ∘ X i - ∫ g ∘ X i` and `(f ∘ X i)² - ∫ g' ∘ X i` are martingales, has tight
  laws for `postcomp f ∘ X i` in `D(ℝ≥0, ℝ)`. Read at a generator, `g = A f` and
  `g' = A (f²)`; the second hypothesis is not implied by the first, and `g'` is
  not `g²`.

  **This is the first item's own shape — a martingale hypothesis in, tightness
  out — and what it adds over
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_forall_exists_bounded_pair`
  is that the approximation error is zero.** `Y` is `f ∘ X i` itself and `Y'` is
  `(f ∘ X i)²`, so both errors vanish identically and the `ε` of the criterion is
  never spent. A consumer whose processes only *approximately* solve the problem
  — Donsker's, whose random walks solve no martingale problem at all — calls the
  bounded pair form directly; this one is the exact case, and it is the one the
  acceptance examples of Milestone 4 meet.

  **The two pairs come from one statement, and no product on `E →ᵇ ℝ` is used.**
  `MeasureTheory.isApproximatingPair_of_martingale` is stated for a **merely
  continuous** tested function, boundedness of it being read in no field of the
  class: `progressive` and `progressive_sub` are measurability, `rightContinuous`
  is continuity, `martingale` is the hypothesis, and the three fields carrying a
  bound read the **density** alone. So it applies at `f` and at `f²` alike, the
  second through `Continuous.pow`, and the closure of the approximable functions
  under products — which the paragraph above names as what the second pair
  needs — is not what an exact solution requires. What the consumer does need is
  a bound on each approximant, and there `‖f‖` and `‖f‖²` are read; that is the
  one place boundedness of `f` enters.

  **What the two pairs do not share is the constant**: they are
  `T' ^ q.toReal⁻¹ * ‖g‖₊` and `T' ^ q.toReal⁻¹ * ‖g'‖₊`, while the criterion
  asks for one `K`. `MeasureTheory.IsApproximatingPair.mono_K` at the maximum
  joins them, and it is the whole dependence of the class on that parameter: `K`
  occurs in exactly one field and there as an upper bound. No monotonicity in `T`
  or `q` holds in its place — the horizon is the measure of the window in two
  fields at once, and the exponent is read in `one_lt_exponent`. The three
  quantities the criterion leaves free are then **chosen**: `q = 2`, the horizon
  `u + 1` for the window `u` handed down, and `K` the maximum above.

  **And the seam to the next item, the same day.**
  `MeasureTheory.isTightMeasureSet_map_of_forall_martingale`: under compact
  containment of `{P.map (Φ i)}` at `0`, and with the two martingale hypotheses
  available at **every** `f : E →ᵇ ℝ`, the laws of the `E` valued paths
  themselves are tight in `D(ℝ≥0, E)`. That is what
  `isRelativelyCompact_of_approx` consumes; the real images are not. The proof is
  one application of `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp_nnreal`
  of **SkorokhodSpace** Milestone 8, whose right hand side is literally the
  conclusion of the previous statement quantified over `h`, and no new estimate
  occurs in it.

  **The price is the quantifier, and it is paid, 2026-09-21.**
  `MeasureTheory.isTightMeasureSet_map_of_dense_forall_martingale`: the two
  martingale hypotheses are read on a class `H : Set (E →ᵇ ℝ)` that is merely
  **dense in the supremum norm**, and the conclusion is unchanged. The statement
  above is the case `H = Set.univ`, kept because it is the form in which the
  hypothesis is checked when a problem is posed at every test function. The class
  `H` is asked to be closed under nothing: `g` and `g'` are quantified inside, so
  `g'` answers for `f²` without `f²` having to lie in `H`.

  **And the density a generator really has, the same day.**
  `MeasureTheory.isTightMeasureSet_map_of_denseOnCompacts_forall_martingale`: the
  class `H` is asked to be dense for **uniform convergence on compact sets**
  only. That correction is not cosmetic — the domain of a generator is *not*
  dense in the supremum norm: `Cc^∞(ℝ)` is not dense in `ℝ →ᵇ ℝ`, a uniform limit
  of compactly supported functions vanishing at infinity while the constant `1`
  does not. So the sup-norm form above is met by no diffusion, and this one is
  the statement the acceptance examples use.

  **What pays for the weaker density is compact containment**, and it is read
  twice in the same hypothesis: once to lift the tightness of the real images
  back to the family, and once to hold the values of the path on a window inside
  a compact `Γ ⊆ E` up to mass `ε`, where the approximation is good. Outside the
  window the Skorokhod metric is damped by `exp (−u)`, and that is the whole
  estimate: `SkorokhodSpace.dist_postcomp_le_of_forall_mem_exhaustion` compares
  two post-compositions on the values of the path in a window alone, at the price
  `exp (−M)`. The general engine underneath is
  `MeasureTheory.isTightMeasureSet_map_of_forall_exists_measure_dist_gt_le` of
  **WeakConvergence**, which asks for the approximation only **in measure and
  uniformly in the index**; the sup-norm form is its special case with an empty
  exceptional set.

  **And the data a martingale problem is actually posed with, the same day.**
  `MeasureTheory.isTightMeasureSet_map_of_subalgebra_forall_martingale`: no
  density hypothesis at all, but a point separating subalgebra
  `A : Subalgebra ℝ (E →ᵇ ℝ)` — the domain of the generator. Its density on
  compact sets is supplied by
  `MeasureTheory.exists_mem_subalgebra_forall_dist_le_of_isCompact` of
  **WeakConvergence**, which is Stone–Weierstrass on a compact set carried from
  `C(E, ℝ)` back to the bounded functions.

  **The first item of the chain is therefore complete at the quantifier the
  acceptance examples meet**, and the three weakenings it took are not three
  conveniences: a generator gives the martingale property on an *algebra*, an
  algebra is dense only on *compact sets*, and density on compact sets suffices
  only because *compact containment* holds the paths there. The countable dense
  set `S` of times is unrelated to any of this — it lives in the index, not in
  the test class. What remains of the item is the `Fin k` valued form.

  **What made the first of the three weakenings possible is one estimate and one
  general fact**, both outside this file.
  `SkorokhodSpace.dist_postcomp_le` of **SkorokhodSpace** Milestone 8: two
  post-compositions of *one* path are at most as far apart as the two maps are on
  the value space, because the time change may be taken to be the identity, its
  logarithmic norm is `0`, and `∫₀^∞ exp (−u) du = 1`. That is a **uniform**
  approximation of the map `postcomp`, and
  `MeasureTheory.isTightMeasureSet_map_of_forall_exists_dist_le` of
  **WeakConvergence** turns a uniform approximation of a map into tightness of
  its image laws. The compact set there has to be built rather than transported:
  the closed thickening of a compact set by the approximation error is compact
  for no reason at all, and the set that works is the intersection over all error
  scales, `⋂ k, cthickening (1/(k+1)) (K k)`.

  **A naming correction made at the same time, 2026-09-21.** The class and all
  of `namespace IsApproximatingPair` stood at the **root** namespace while
  twenty-two docstrings in the file cited them as
  `MeasureTheory.IsApproximatingPair…` — a name a reader could not look up. The
  section now opens `namespace MeasureTheory`, which is where the rest of the
  milestone lives, and the citations are true. Nothing of the mathematics
  changed; the file builds with 0 errors and 0 `sorry` as before.

* `isRelativelyCompact_of_approx`: if `E` is Polish, the domain of `A` contains
  an algebra separating points and vanishing nowhere, the approximation holds
  for each `(f,g) ∈ A`, and `{X n}` satisfies compact containment, then `{X n}`
  is relatively compact; hence every limit point solves the martingale problem
  for `A`, and the martingale problem has a solution with càdlàg paths. What
  the algebra is used for here is density for uniform convergence on compact
  sets, and that is Stone–Weierstrass proper, from separation of points alone:
  `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`
  (`Topology/ContinuousMap/StoneWeierstrass.lean:323`), which needs neither the
  vanishing-nowhere clause nor any measure theory. The algebra is separating by
  `IsSeparating.of_subalgebra` of **WeakConvergence**, Milestone 1; it is not
  thereby convergence determining, that notion asking strong separation of
  points. The previous item makes each `postcomp f ∘ X n` tight; and
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` of Milestone 8 there
  lifts that back to `{X n}`.

  **The item stands in the exact case, 2026-09-21.**
  `MeasureTheory.isCompact_closure_of_subalgebra_forall_martingale`: under the
  hypotheses of the previous item — a point separating subalgebra, the martingale
  property on it, and compact containment — the laws of the paths have compact
  closure in the weak topology of `ProbabilityMeasure D(ℝ≥0, E)`. There is no new
  estimate in it: the tightness is the previous item, and the passage from
  tightness to compact closure is Prokhorov, which Mathlib has as
  `isCompact_closure_of_isTightMeasureSet`
  (`MeasureTheory/Measure/Prokhorov.lean:530`) and which asks only `T2` of the
  space. Neither Polishness of the path space nor completeness is read there;
  they are read upstream, in the tightness.

  **What the item costs is the crossing of two types.** Tightness is stated for a
  set of `Measure`, Prokhorov concludes about a set of `ProbabilityMeasure`, and
  the set is therefore written as a comprehension over `ProbabilityMeasure` — the
  coercion is matched rather than constructed.

  **And a junk value that happens to say the truth.** Mathlib's instance
  `IsProbabilityMeasure (Measure.map f μ)`
  (`MeasureTheory/Measure/Typeclasses/Probability.lean:124`) carries no
  measurability hypothesis: where `f` is not a.e. measurable, `Measure.map`
  returns a Dirac measure, and a Dirac measure is a probability measure. So the
  instance is free for a reason that has nothing to do with the path map. What
  makes `P.map (Φ i)` the law of the path rather than that Dirac is
  `MeasureTheory.measurable_pathOfProcess`, and it is read in the tightness.

  **The item stands in the approximate case too, 2026-09-21** —
  `MeasureTheory.isCompact_closure_of_subalgebra_forall_exists_bounded_pair`
  and, in the shape the fourth item reads,
  `MeasureTheory.isCompact_closure_range_of_subalgebra_forall_exists_bounded_pair`.
  Processes that only nearly solve the problem, Donsker's rescaled random walks
  among them, have no exact martingale property at any scale and are reached by
  no statement above; what they have is the two approximating pairs with their
  bound and their two errors, and that is the hypothesis these carry. The four
  liftings of the first item are drawn a second time from it —
  `isTightMeasureSet_map_of_forall_exists_bounded_pair`,
  `…_of_dense_forall_…`, `…_of_denseOnCompacts_forall_…`,
  `…_of_subalgebra_forall_exists_bounded_pair` — and the exact case stays proved
  where it is: the two already share their one estimate at
  `isTightMeasureSet_map_postcomp_of_forall_exists_bounded_pair`, into which the
  martingale form feeds through `isApproximatingPair_of_martingale` with the
  error `0`. Nothing is re-derived; each of the four is the same one line of
  lifting as its exact counterpart.

  **Why the liftings tolerate the weaker hypothesis at all**, and it was read off
  the source rather than assumed: all three density statements of Milestone 8
  take their hypothesis as `∀ g ∈ H, IsTightMeasureSet {…}`, one self-contained
  conclusion per test function with nothing shared between two of them. So the
  exponent, the horizon and the constant of the approximation may be chosen
  **after** the test function, and the density step — which compares test
  functions in the supremum distance and never looks at their approximants —
  does not notice. Had it been otherwise, the family would have needed one
  horizon for the whole algebra, and a generator does not supply that.

  **A hypothesis that was asked and never read, removed the same day.** The
  bounded pair form carried `∀ ε₀ : ℝ, 0 < ε₀ →` in front of its data although
  `ε₀` occurs nowhere in the body: `isApproximable_of_forall_exists_bounded_pair`
  takes the modulus error implicitly and constrains it nowhere, the pairs and the
  two errors already giving `IsApproximable … ε₀ u` for every `ε₀`. The two
  readings are equivalent, so nothing is weakened or strengthened; what is gone
  is data a consumer had to supply four times over and that no proof looks at.
  Only `isTightMeasureSet_map_postcomp_of_forall_isApproximable`, one step
  further down, genuinely needs its triple per `ε₀`, because
  `IsApproximable` carries the error in its own signature.

  What remains of the item is the identification of the limit points, which is
  the next item.
* `tendsto_of_isRelativelyCompact_of_unique`: with uniqueness from Milestone 6
  or Milestone 8, relative compactness upgrades to convergence. **Proved
  2026-09-21.**

  **It carries no measure theory**, and it is stated for an arbitrary space and
  an arbitrary predicate `Sol`: the second item supplies the compact closure,
  the third supplies "every limit of a convergent subsequence is a solution",
  Milestone 6 supplies "there is at most one solution", and nothing else of the
  chain enters. The separation is what makes the two probabilistic inputs
  replaceable.

  **Two hypotheses a first reading expects and that are not there.** There is
  **no metrizability**: `Filter.tendsto_of_subseq_tendsto` holds over an
  arbitrary filter on an arbitrary type and asks only that the *index* filter
  be countably generated, and the sequential compactness of a compact set is
  `IsCompact.tendsto_subseq` under `FirstCountableTopology`, strictly weaker.
  And there is **no monotonicity of the extracted subsequence**: the hypothesis
  quantifies over every map `ℕ → ℕ` that tends to infinity, which is the weaker
  thing for the consumer to prove, the third item knowing nothing about the
  order of its index — only that the index escapes, which is what carries a
  hypothesis like `‖f - f' n‖ → 0` from the family to the subsequence.
* `tendstoInDistribution_id_of_tendsto` — the bridge between the fourth item
  and the third. The fourth speaks of the *laws* and the third of the
  *processes*, asking for `TendstoInDistribution`, which names a limiting
  random variable; a compactness argument produces a measure and no process.
  The identity of the path space under the limiting law is that process,
  because `Measure.map id` is the measure itself. **Nothing is constructed** —
  the canonical space is the path space, which is already there. **Proved
  2026-09-21.**
* `mpSolution_of_tendsto_cadlag_of_subseq` — the seam between the fourth item
  and the third, and it is `hlim` of the fourth written out for the càdlàg
  chain: if the path laws of an approximating family converge along a
  subsequence to `ν`, then the identity of the path space, read under `ν`,
  satisfies the martingale identity to `(f, g)` along a countable dense set of
  times. **Proved 2026-09-21.**

  **Three of the inputs of `mpSolution_of_tendsto_cadlag_of_approx` are produced
  here rather than asked of the consumer.** The *process* of the limit is the
  identity, by the bridge above; its *filtration* is `cadlagFiltration`, and
  the hypothesis is `MeasurableSpace.comap_id` at `cadlagFiltration_eq`, which
  is what `naturalFiltration_comp_eq_comap` says at the identity; and the
  *times* come from `SkorokhodSpace.exists_countable_dense_continuity` at the
  **limit law**, with `rightDense_of_dense` turning their density into right
  density.

  **That is why `T` is existentially quantified in the conclusion** rather than
  being a parameter: the limit is known only after the extraction, so no set of
  times can be fixed before it. The shape costs nothing at the fourth item,
  whose uniqueness input from Milestone 6 reads `IsMPSolution` and asks nothing
  about the times.

  **A subsequence of an approximating family is again one**, and that is the
  whole of the remaining bookkeeping — the data are composed with `ns`, and the
  hypotheses transport by substitution. The two norm convergences transport
  because the index escapes, and that is the single place at which
  `Tendsto ns atTop atTop` of the fourth item is paid out.
* `mpSolution_of_tendsto_cadlag_of_subseq_of_zero` — the same seam at the
  **vanishing martingale gap** instead of at exact martingality of a moving test
  pair, and the form Donsker's acceptance test reads. **Proved 2026-09-22.**

  **Why the existing seam does not serve there, and it is read off three
  signatures rather than suspected.** `mpSolution_of_tendsto_cadlag` asks no
  martingale property at all: its hypothesis `hzero` is the convergence to `0`
  of `∫ (mpTest f g t - mpTest f g s) · Z` along the family, that is, a gap that
  vanishes. `mpSolution_of_tendsto_cadlag_of_approx` and
  `mpSolution_of_tendsto_cadlag_of_subseq` are its specialisations at *exact*
  martingality of a pair `(f' n, g' n)` converging to `(f, g)` in the supremum
  norm — the approximation sitting in the **test function** and not in the
  error. A rescaled random walk is an exact martingale to no pair of bounded
  continuous functions, its own exact martingales being itself and its square,
  both unbounded; what it has is the vanishing gap, which is the Lindeberg–
  Taylor expansion.

  The statement is `mpSolution_of_tendsto_cadlag_of_subseq` with `hzero` along
  `ns` in place of `hmart`, `hf`, `hg`, and the same conclusion. It rests on
  `mpSolution_of_tendsto_cadlag` and on the three inputs that seam already
  assembles and that do not depend on `hmart`:
  `SkorokhodSpace.exists_countable_dense_continuity`,
  `tendstoInDistribution_id_of_tendsto` and `cadlagFiltration_eq`.

  **Two things the statement settles that the plan had left open.**

  * **The test functions are indexed by `Set.Iic s`** and not by the class
    `insert s (T ∩ Set.Iic s)` the underlying statement reads. `T` is produced
    inside the proof, from `SkorokhodSpace.exists_countable_dense_continuity` at
    the limit law, and the limit is known only after the extraction; no consumer
    can name it. `Set.Iic s` is the smallest set of times independent of that
    choice, `SkorokhodSpace.evalFuns_mono` is the passage, and the price is that
    the hypothesis is asked of more test functions than the proof reads.
  * **`Tendsto ns atTop atTop` is not carried.** The seam it mirrors spends that
    hypothesis at exactly one place, the transport of `‖f - f' n‖ → 0` and
    `‖g - g' n‖ → 0` to the subsequence; with the gap stated along `ns` from the
    start there is nothing to transport. A consumer holding the gap along the
    whole family composes with the escape itself, one `Filter.Tendsto.comp`.
    The fourth item still hands the escape over — it is simply not read here.
* `mpSolution_of_tendsto_cadlag_of_subseq_of_zero_pathOfProcess` — the vanishing
  gap at the data the **second** item produces, and the form the Donsker
  assembly reads: one probability space, a sequence of processes with their path
  maps, one pair `(f, g)`. **Proved 2026-09-22.**

  It is the previous item with the tested functional written out at a path built
  from a process, one `simp only [SkorokhodSpace.mpTest, hΦ]`, and there is no
  analysis in it. What is worth recording is what it does **not** carry:
  `mpSolution_of_tendsto_cadlag_of_subseq_pathOfProcess` needs a filtration, the
  adaptedness of the processes to it, and `CompleteSpace E` — the first two
  because a *martingale* hypothesis has to name the past, the third because it
  derives the measurability of the path map from the adaptedness through
  `SkorokhodSpace.measurable_of_measurable_eval`. **A vanishing gap names no
  past**: all that is read of the path map is its measurability, and that is
  asked for directly. This is the one place in the pair of seams where the gap
  form is cheaper and not merely different.
* `mpSolution_of_tendsto_cadlag_of_subseq_pathOfProcess` — the same seam at the
  data the **second** item produces, and the form the Donsker assembly reads:
  one probability space, one right continuous filtration, a sequence of adapted
  processes with their path maps, and one pair `(f, g)` throughout.
  **Proved 2026-09-21.**

  Three substitutions and no analysis. The spaces being constant, the
  approximating pairs are constant and the two norm convergences are `‖f - f‖`;
  the filtration hypothesis is `comap_pathOfProcess_le_of_stronglyAdapted`,
  which is where the inclusion form is spent; and the tested functional at a
  path built from a process is the martingale of the second item on the nose,
  `SkorokhodSpace.mpTest` being the evaluation minus the compensator.

  Two things it does **not** ask, both checked at the source. Progressivity: the
  second item states `IsStronglyProgressive` because its tightness needs it,
  while this item reads only `StronglyAdapted`, for the measurability of the
  path map and for the filtration inclusion. And a hypothesis it does carry:
  `CompleteSpace E`, entering here for the first time in the chain and only
  through `SkorokhodSpace.measurable_of_measurable_eval` — the second item
  carries it for the same reason, so it is not a new demand.

  **The bookkeeping of the set between the second item and the fourth is done
  too**, and it is one statement rather than one per route:
  `isCompact_closure_range_probabilityMeasure_of_isTightMeasureSet` carries a
  tight family of measures to compact closure of the corresponding `Set.range`
  in `ProbabilityMeasure`, which is what the fourth item reads.
  `isCompact_closure_range_of_subalgebra_forall_martingale`,
  `isCompact_closure_range_of_subalgebra_forall_exists_bounded_pair` and
  `isCompact_closure_range_map_rescaledWalk` are its three instances. No
  hypothesis is added or dropped, and the general statement asks `BorelSpace`
  and `T2` of the space alone. The type ascription on the range is not
  decoration — `ProbabilityMeasure` is a `def` on a subtype, and the anonymous
  constructor folds back to it, whereupon `closure` finds no topology; it is
  the same trap as the `β :=` at `tendstoInDistribution_id_of_tendsto`.

  With it **the four items join, and between them nothing is left to write**:
  the second delivers the compact closure in the shape the fourth consumes, the
  fourth extracts a subsequence, the seams above turn its limit into a process
  with a filtration and a set of times, and the third reads the martingale
  identity off it.

  **What Donsker still needs is not a seam**, and it is named here so that the
  joining is not mistaken for the acceptance test. One item: the **uniqueness**
  for `f ↦ f''/2`, which is the self-contained Fourier point stated below. The
  **compact containment** for the rescaled random walks stood beside it until
  2026-09-21 and is now proved, as `isCompactContained_rescaledWalk`. A
  smaller one: the predicate `Sol` of the fourth item has to be quantified
  over the algebra, the seams above being stated for one pair `(f, g)`. The
  **approximate** case of the second item stood in this list until 2026-09-21
  and is now proved, as
  `isCompact_closure_range_of_subalgebra_forall_exists_bounded_pair`; what is
  left for the walks is to exhibit their approximating pairs, which is an
  instance and not an item.

  **The compact containment is done, 2026-09-21, and in twelve statements, of
  which only four name path space at all: five are probability over `ℕ` and
  Mathlib has none of them, and three are the seam between the two descriptions
  of the walk.**
  `SkorokhodSpace.isCompactContained_of_forall_exists_bound`
  of **SkorokhodSpace** Milestone 8 turns the hypothesis `hcc` — which every
  statement of this milestone carries and which until then had only the
  constant family as a witness — into a uniform bound on the **path maximum
  over a window**, for `E` a `ProperSpace` and hence for `E = ℝ`. Eleven
  statements carry it the rest of the way, and the family of the walks is the
  first witness of the predicate that is not constant:

  * `Martingale.submartingale_abs` — the absolute value of a martingale is a
    submartingale, which Mathlib does not have. It is `Submartingale.sup` read
    at `f ⊔ (-f)`.
  * `Martingale.measure_exists_abs_ge_le` — Doob's maximal inequality in event
    form, `ε · P {∃ k ≤ N, ε ≤ |f k|} ≤ ∫ |f N|`. Mathlib's
    `MeasureTheory.maximal_ineq`
    (`Mathlib/Probability/Martingale/OptionalStopping.lean:144`) states it about
    `Finset.sup'` and bounds it by the integral over the event; both shapes cost
    a consumer a step, and neither corollary is in Mathlib.
  * `isCompactContained_map_stepPath` — the reduction of the window maximum to
    the maximum over the nodes, for a family of step path laws with
    deterministic nodes. It is an **equality of events** and not an estimate: a
    time of the window lies below the node past the window, so `stepIndex_le`
    puts its index among the finitely many named ones. No monotonicity of the
    nodes and no non explosion enter.
  * `isCompactContained_map_stepPath_of_martingale` — the two composed, and the
    form the acceptance example meets: nodes, a martingale at them, and an `L¹`
    bound on the martingale at the last node, uniformly in the index.
  * `martingale_partialSum_of_iIndepFun` — the partial sums `n ↦ ∑ k < n, ξ k`
    of independent centred integrable summands are a martingale, which Mathlib
    does not have. **The filtration is the natural one of the sums and not of
    the summands**, and the difference decides the statement:
    `MeasureTheory.Filtration.natural ξ`
    (`Mathlib/Probability/Process/Filtration.lean:395`) at `n` is
    `σ (ξ 0, …, ξ n)` and so holds the increment that the step from `n` to
    `n + 1` adds, over which the conditional expectation at `n + 1` is
    `∑ k < n, ξ k + ξ n`. The step is
    `ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt`
    (`Mathlib/Probability/BorelCantelli.lean:43`) together with
    `MeasureTheory.condExp_indep_eq`
    (`Mathlib/Probability/ConditionalExpectation.lean:42`), carried from the one
    filtration to the other by the inclusion
    `𝒢 (m + 1) ≤ Filtration.natural ξ m`.
  * `integral_abs_le_sqrt_integral_sq` — `∫ |f| ≤ √(∫ f ^ 2)` on a probability
    space, which Mathlib carries about `eLpNorm`
    (`MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`,
    `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:115`) and about
    `(∫ f ^ p) ^ (1 / p)`
    (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`,
    `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1225`) but not in this
    shape. It is **the nonnegativity of the variance of `|f|`** and not
    Cauchy–Schwarz, which saves the whole `ENNReal.rpow` computation the other
    two shapes would cost.
  * `integral_abs_sum_le_sqrt_of_iIndepFun` — `∫ |∑ k < N, ξ k| ≤ √N` for
    independent centred summands of variance at most `1`. It is the previous
    read at the sum together with
    `ProbabilityTheory.IndepFun.variance_sum`
    (`Mathlib/Probability/Moments/Variance.lean:424`), the centring killing the
    second summand of `ProbabilityTheory.variance_eq_sub` (`:226`) so that the
    variance of the sum is `∫ (∑ k < N, ξ k) ^ 2`. **No martingale enters**,
    which is why it and the martingale above are two statements.
  * `isCompactContained_rescaledWalk` — **the instance, proved 2026-09-21**: for
    independent centred `ξ j` of variance at most `1` and the walk of index `n`
    with nodes `k / (n + 1)` and values `(n + 1)⁻¹ᐟ² ∑ j < k, ξ j`, the family of
    path laws is compactly contained. Every hypothesis of
    `isCompactContained_map_stepPath_of_martingale` is discharged by one of the
    statements above it, and no new estimate is made. The martingale is taken at
    the **scaled** increments and the `L¹` bound at the **unscaled** ones, the
    factor being pulled out of the integral; feeding the scaled increments to the
    bound as well would give `√N` in place of `√N / √(n + 1)` and lose the
    uniformity in `n`, which is the whole content of the predicate.
  * `stepIndex_natCast_div`, `stepPath_natCast_div` and
    `stepPath_rescaledWalk_eq` — **the seam Donsker runs across**, proved
    2026-09-21. The compact containment reads the walk as a **step path**,
    because the bound on the window maximum is a bound over the nodes; every
    tightness statement of this milestone reads it as a **process**
    `fun t ω ↦ X n t ω`, because progressivity and right continuity are
    properties of a process. One `Φ` has to meet both, and this identity is what
    lets it: over the grid `T k = k / c` with `c > 0` the step index is the floor
    `⌊t · c⌋`, so the step path of the walk **is**
    `(n + 1)⁻¹ᐟ² ∑ j < ⌊t (n + 1)⌋, ξ j`, the classical Donsker process written
    without `sInf`. It is not an instance of `stepIndex_div_const`, which
    rescales an arbitrary sequence of nodes and leaves a step index standing;
    what reads the index off is that the nodes are the natural numbers. The junk
    value `sInf ∅ = 0` is not reached and no hypothesis says so — the grid is
    unbounded, so the set is inhabited by the answer itself.

  **The node past the window is `(n + 1) * m` and the constant is `√m`**, not the
  `⌈n · m⌉` and `√(m + 1)` this milestone predicted, and the reason is that the
  window ends at the **integer** `m`: then `(n + 1) * m` is itself a node, the
  next one is already past the window, and `√((n + 1) * m) / √(n + 1) = √m` is an
  equality with no rounding to pay for. The family is indexed by `ℕ` with the
  scaling `(n + 1)⁻¹ᐟ²`, so that the stage at which the denominator vanishes
  never occurs — at `n = 0` the junk values would make every node and every value
  `0`, and the statement would hold of a family that is not the walks.

  **And the walk is a process, 2026-09-21, which is the other half of what the
  milestone asks of it.** Compact containment is the whole of what the
  **tightness of the laws** needs from the walks; what
  `isTightMeasureSet_map_postcomp_of_forall_exists_bounded_pair` asks besides the
  approximating pairs is that the walk be a process — strongly progressive for a
  right continuous filtration, with right continuous paths. Neither is about
  approximation, and five statements pay both, so that the remaining item of the
  acceptance test is the pairs alone:

  * `floorFiltration` and `floorFiltration_apply` — the filtration of an
    arithmetic grid, at `t` the σ-algebra of the stage `⌊t · c⌋`. **Mathlib has
    no reindexing of a filtration along a monotone map**: the constructions in
    `Mathlib/Probability/Process/Filtration.lean` are `const`, `filtrationOfSet`,
    `natural`, `piLE`, `piFinset` and `cylinderEventsCompl`, and none of them
    changes the index (checked at the source 2026-09-21). What a `Filtration`
    asks of the reindexing is monotonicity and nothing else.
  * `isRightContinuous_floorFiltration` — and it is right continuous, which is
    the hypothesis the tightness side carries and the one a reindexed filtration
    is least likely to have. It holds because the floor is right continuous and
    not by a limit argument: a single `s > t` below `(⌊t · c⌋ + 1) / c` already
    realises `⨅ s > t, 𝓕 s`, a grid point being no exception since its cell is
    half open to the right.
  * `continuousWithinAt_stepPath_nnreal` — a step path over `ℝ≥0` is right
    continuous in the `ContinuousWithinAt … (Set.Ici t) t` shape the tightness
    statements read. It is not `IsStepPath.isCadlag` again: a step path is
    **locally constant** from the right, which is stronger and cheaper, and
    `eventuallyEq_nhdsGE_stepPath_comp` is it. No hypothesis on the nodes enters.
  * `stepIndex_coe_nnreal` — the step index of the grid is the same over `ℝ` and
    over `ℝ≥0`. The bookkeeping is not idle: the only route to joint
    measurability a locally constant process has,
    `measurable_uncurry_min_of_eventuallyEq`, is stated over `ℝ`, while the
    filtration and the path space are over `ℝ≥0`.
  * `isStronglyProgressive_stepPath_natCastDiv` — a step path over an arithmetic
    grid is strongly progressive for `floorFiltration`, asking of the values only
    that they be adapted as a discrete process. **No exact formula for the index
    is used in the measurability step**, only the bound
    `stepIndex T r ≤ ⌊t · c⌋` for `r ≤ t`, so the statement would survive a grid
    that is merely increasing; the exact formula is spent on matching the two
    time axes and nowhere else.
  * `continuousWithinAt_rescaledWalk` and `isStronglyProgressive_rescaledWalk` —
    the two instances, and the second is over the **same** filtration the
    martingale of `martingale_partialSum_of_iIndepFun` lives on, reindexed by the
    floor. That is not an accident of spelling: had the tightness side asked for
    a filtration the compact containment cannot carry, the walk would meet the
    two halves of this milestone with two different objects.
  * `martingale_floorFiltration_of_martingale` and `martingale_rescaledWalk` — a
    discrete martingale reindexed along the floor is a martingale in continuous
    time, and the walk is one. Nothing is needed of the reindexing but
    monotonicity: the two fields of `MeasureTheory.Martingale` are adaptedness,
    which is the discrete one read at `⌊t · c⌋`, and the tower identity, which is
    the discrete one read at a pair of stages the floor already orders. No
    uniform integrability and no limit enter, the process taking only the
    countably many values it took before.
  * `martingale_sq_partialSum_of_iIndepFun` and `martingale_sq_rescaledWalk`,
    **2026-09-22** — the compensated square,
    `(∑ k < n, ξ k) ^ 2 - ∑ k < n, 𝔼[ξ k ^ 2]`, is a martingale for the same
    filtration, and so is its floor reindexing. It is the second of the two
    processes the approximability condition asks for: `IsApproximable` wants an
    approximant of the walk **and** one of its square, and a square is no
    martingale. **Mathlib has it in no form** — there is no declaration named
    for the predictable quadratic variation of a discrete martingale, no
    `sq_sub` lemma about `Martingale`, and no compensator of a square anywhere
    under `Mathlib/Probability/` (searched at the source of `master`
    `09712d488fd`; `Mathlib/Probability/Moments/Variance.lean` mentions
    `Martingale` not once). What Mathlib has is
    `ProbabilityTheory.IndepFun.variance_sum`, which is this statement read at
    one time and with the conditioning thrown away. The compensator is the sum
    of the **second moments**, which under the centring hypothesis are the
    variances; second moments are what the proof produces. The centring is spent
    on the cross term and the square integrability on its integrability, one
    place each, and the *same* independence serves the increment and its square,
    `ξ n ^ 2` being measurable for the σ-algebra of `ξ n`.

  **And here is the shape the acceptance test needs, measured and not guessed.**
  The compensator above is a **step function of the time**, while
  `MeasureTheory.IsApproximatingPair` asks its compensator to be
  `∫_{(0,t]} Z s ω` for a density in `L^q` — and no step function is one. The
  approximant of the square is therefore not the compensated square itself but
  the compensated square plus an *absolutely continuous* compensator, the error
  being the gap between the two. For increments of one common second moment `σ`
  the absolutely continuous compensator is `t · σ`, its density the constant
  `σ`, and the gap is `(t - ⌊t (n + 1)⌋ / (n + 1)) · σ ≤ σ / (n + 1)` — uniform
  in `ω` and in `t`, and vanishing **along the family** and not at a fixed
  member. That is the reason this milestone carries
  `MeasureTheory.IsEventuallyApproximable` at all, and it is measured rather
  than asserted.

  * `isApproximatingPair_rescaledWalk`, **2026-09-22** — and the first pair is
    free, which is the other half of the same measurement. The walk approximates
    itself with the zero compensator, the zero density and the constant `K = 0`,
    error exactly `0`. It is **an instance of
    `MeasureTheory.isApproximatingPair_of_martingale` and not a new statement**,
    read at `F = id` and at the zero generator `g = 0`: that statement asks a
    process, a continuous `F` and a bounded `g` making `F ∘ X` compensated by
    the integral of `g ∘ X` a martingale, and a martingale is that with `F` the
    identity and `g` zero. The walk solves no martingale problem, but `(id, 0)`
    is admissible data for the statement — **a martingale needs no
    approximating, being its own approximant.** So the whole cost of the
    acceptance test sits in the second pair, the square, and a consumer joining
    the two raises `K` with `MeasureTheory.IsApproximatingPair.mono_K`.
  * `isApproximatingPair_sq_rescaledWalk`, **2026-09-22** — the second pair, in
    the shape the paragraph above prescribes: `V ^ 2 - ⟨V⟩ + t σ` with the
    linear compensator `t σ`, the constant density `σ` and the constant
    `K = T ^ q⁻¹ · ‖σ‖`. **`σ` is free**: no hypothesis says it is the common
    second moment, because the martingale field reads `Y - C = V ^ 2 - ⟨V⟩`,
    where the constant cancels, and the three fields that read the density read
    a constant. The second moment enters only in the error, and is asked where
    it is used.
    It is **not** an instance of `isApproximatingPair_of_martingale`, and the
    exchange is favourable: there the compensator is an integral along the path
    and `progressive_sub` is the one real price; here the compensator is a
    function of the time alone, so `progressive_sub` is `V ^ 2 - ⟨V⟩`, two step
    paths and `IsStronglyProgressive.sub`. The deterministic step `⟨V⟩` is
    progressive by `isStronglyProgressive_stepPath_natCastDiv` at a **constant**
    value sequence — the statement asks the values to be adapted, and a constant
    is.
    **The constant does not move with `n`**, which is where a uniformity could
    have failed and does not: `K` is read off the density alone, and `n` occurs
    in neither the density nor the horizon.
  * `enorm_sub_sq_rescaledWalk_le` and
    `lintegral_biSup_enorm_sub_sq_rescaledWalk_le`, **2026-09-22** — the error of
    that pair in closed form, `σ (t - ⌊t (n + 1)⌋ / (n + 1)) ≤ σ / (n + 1)`, and
    the same bound in the shape `IsEventuallyApproximable` reads, a mean over `Ω`
    of a supremum over the horizon. Both quantifiers are free, the pointwise
    bound holding at every time and every sample point, so **the horizon `T` is
    not read at all**: the error of this family grows with the mesh and not with
    the window. `0 ≤ σ` is no hypothesis either — it is the second moment read
    against `integral_nonneg`, which needs no integrability.
  * `abs_rescaledWalk_le_of_le` and `integrable_majorant_rescaledWalk`,
    **2026-09-22** — the integrable majorant that
    `IsApproximatingPair.integrable_stoppedValue_of_dominated` asks of an
    unbounded approximant: below `j` the walk is dominated by
    `(n+1)^{-1/2} ∑_{k < ⌊j (n+1)⌋} |ξ k|`, a finite sum of integrable terms.
    **Past `j` the domination is false**, the majorant growing with the number
    of stages — which is why that statement asks for it only up to the bound of
    the stopping time. Only integrability of the increments is read.
  * `abs_sq_rescaledWalk_le_of_le` and `integrable_majorant_sq_rescaledWalk`,
    **2026-09-22** — the same majorant question for the *square's* approximant.
    Below `j`, `V ^ 2 - ⟨V⟩ + t σ` is dominated by `g ^ 2 + ⟨V⟩ j + j |σ|`, with
    `g` the very majorant `abs_rescaledWalk_le_of_le` already names: each of the
    three summands is bounded at `j` by itself — `V t` by `g` (so `V t ^ 2 ≤
    g ^ 2`, squaring a bound between nonnegatives), `⟨V⟩ t` by `⟨V⟩ j` (it is a
    sum of integrals of squares, hence nonnegative and increasing in `t`, no
    integrability needed for either fact), and `t σ` by `j |σ|`. The majorant is
    integrable because `∑_{k < ⌊j (n+1)⌋} |ξ k|` is `MemLp` at `2` (a finite sum
    of `MemLp.abs`), so its square is integrable by `MemLp.integrable_sq` — the
    one place the square integrability of the increments is spent — and the two
    remaining summands are constants at fixed `j`. **Past `j` this is false**
    for the same reason as the walk's own majorant: the discrete compensator
    keeps growing with the number of stages.

  * `isEventuallyApproximable_rescaledWalk`, **2026-09-22** — the assembly, and
    with it the approximability half of the acceptance test. The two pairs are
    joined at the common constant `T ^ q.toReal⁻¹ * ‖σ‖₊` by
    `IsApproximatingPair.mono_K`, the walk's own constant being `0`; the first
    error is exactly `0` and the second is
    `lintegral_biSup_enorm_sub_sq_rescaledWalk_le`, so the error along the
    family is `σ / (n + 1)` and goes to zero, which is
    `isEventuallyApproximable_of_tendsto_zero_cofinite` through
    `Nat.cofinite_eq_atTop`.

    **The four integrabilities are read at two different bounds**, and that is
    the one place care is needed: the structure stops at `min (τ k) u` and at
    `min (τ (k+1)) (min (τ k) u + δ)`, whose bounds are `u` and `u + δ`, while
    the two majorants grow with the bound. An assembly with one bound for both
    pairs of times does not close. The times are
    `isStoppingTime_oscHitSeqCap` and `isStoppingTime_oscHitSeqGap`, their
    bounds `min_le_right` and `oscHitSeqGap_le_coe`.

    **No countable dense set is asked for**: the hitting times need one to be
    stopping times, and `ℝ≥0` being separable,
    `TopologicalSpace.exists_countable_dense` produces it inside the proof.

  With these the walk carries, over the filtration of **its own mesh**,
  everything the two halves of this milestone ask of a process: the martingale
  property, progressivity, right continuous paths, and a right continuous
  filtration. It carries them over no coarser one and over no filtration shared
  with the other members, which is the reason
  `MeasureTheory.IsEventuallyApproximable` indexes its filtration. What the walk
  does not carry is a solution of a martingale problem — a rescaled walk solves
  none, and that is why this milestone has an approximate case at all.

  **And it does not yet reach the chain, for a reason measured at the source on
  2026-09-22 and not foreseen when the pairs were built.** Every tightness
  statement of this milestone reads a process that is **uniformly bounded**, and
  the rescaled walk is not. The bound is not a convenience of one statement but
  runs the whole depth of the estimate:

  * `MeasureTheory.enorm_integral_mul_sub_le_of_biSup_le` carries
    `hUb : ∀ ω, ‖U ω‖ ≤ c` at the weight of the cross term;
  * `MeasureTheory.ofReal_integral_sq_sub_le` reads it as `hVb : ∀ t ω, ‖V t ω‖ ≤ c`
    and hands `c` on as the coefficient of the approximation error, its own
    docstring saying "a consumer with `f : E →ᵇ ℝ` holds all five, `c = ‖f‖`";
  * `MeasureTheory.lintegral_ofReal_dist_le_sqrt_of_biSup_le` reads it a second
    time, to make the square of the increment integrable without a hypothesis;
  * and it survives unchanged through
    `MeasureTheory.sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair`,
    `MeasureTheory.measure_setOf_oscHitSeq_lt_le_div_of_isApproximatingPair` and
    `MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair`
    up to
    `MeasureTheory.mul_measure_setOf_lt_modulusBased_postcomp_le_of_isApproximatingPair`,
    where it is discharged as `c = ‖g‖` for `g : E →ᵇ ℝ`.

  **Counted at the source on 2026-09-22, seventh run, so that no run re-derives
  it.** Of the statements between `lintegral_ofReal_dist_le_sqrt_of_biSup_le` and
  the end of the chain, **four** merely pass the bound on --
  `measure_setOf_oscHitSeq_lt_le_of_isApproximatingPair`,
  `measure_setOf_oscHitSeq_lt_le_div_of_isApproximatingPair`,
  `sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair`,
  `mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair` -- and **two**
  read it themselves, `lintegral_ofReal_dist_sq_le_of_isApproximatingPair` and
  `lintegral_ofReal_dist_le_sqrt_of_isApproximatingPair`.

  **And `lintegral_ofReal_dist_le_sqrt_of_biSup_le` is not one of the six: it has
  no consumer at all.** The chain runs through
  `lintegral_ofReal_dist_sq_le_of_isApproximatingPair`, which calls
  `ofReal_integral_sq_sub_le` directly; the unused statement is the same
  passage packaged for a consumer holding `a`, `b` and a window, and nothing in
  this file holds those without also holding an approximating pair. Weakening it
  therefore moves nothing in the chain, which is why the weakening below is
  stated where the chain actually reads the bound.

  **The decisive place is one level lower than the list above suggests**, and it
  is not a side condition but the **conclusion**: from
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le_lintegral` onward
  the bound stands in the right hand side, as `ENNReal.ofReal c` in front of the
  compensator integral and finally as the constant `1 + 2 * ENNReal.ofReal c` of
  `mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair`. It enters at
  exactly one point, `integral_mul_stoppedValue_eq`, where the pull-out property
  of the conditional expectation is used in its **bounded** form,
  `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound`
  (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean:260`).

  Consequently the `V` slot of every consumer is a **post-composition**:
  `MeasureTheory.isTightMeasureSet_map_postcomp_of_isEventuallyApproximable`
  asks for `IsEventuallyApproximable 𝓕 P q T K (fun i t ω ↦ g (X i t ω)) ε₀ u`,
  while `MeasureTheory.isEventuallyApproximable_rescaledWalk` supplies it for
  `X i` itself. The two meet only at `g = id`, and `id : ℝ → ℝ` is not a
  `ℝ →ᵇ ℝ`. **`isEventuallyApproximable_rescaledWalk` therefore has no consumer
  as it stands**, and the statement
  `MeasureTheory.isTight_map_postcomp_rescaledWalk` cannot be assembled from it.
  This is a statement about the *walk*, not about the weakening: the family of
  scaled deterministic steps takes its values in `[0, 1]`, so there a `g : ℝ →ᵇ ℝ`
  agreeing with the identity on `[0, 1]` closes the same gap.

  **The repair, named and not guessed: the bound on the weight is only ever read
  against the error.** In `enorm_integral_mul_sub_le_of_biSup_le` the two occur
  exclusively in the product `ENNReal.ofReal c * (2 * ε)`, and the walk's first
  pair has `ε = 0` exactly. The statement therefore holds with the pointwise
  bound replaced by a **weighted error**,

  ```
  MeasureTheory.enorm_integral_mul_sub_le_of_lintegral_mul_biSup_le :
    (hγ : ∫⁻ ω, ‖U ω‖ₑ * ⨆ t ∈ W, ‖Y t ω - V t ω‖ₑ ∂P ≤ γ) → … + 2 * γ,
  ```

  of which the bounded version is the instance at `γ = ENNReal.ofReal c * ε`.
  It is a genuine weakening and not a restatement: a weight of infinite supremum
  against an error that vanishes gives `γ = 0`, which no `c` produces.

  The second reading, at the integrability of the square, is weakened the same
  way:
  `MeasureTheory.lintegral_ofReal_dist_le_sqrt_of_lintegral_mul_biSup_le` carries
  `hsq : Integrable (fun ω ↦ (V (b ω) ω - V (a ω) ω) ^ 2) P` instead of the
  bound, which the walk has from `MemLp (ξ k) 2 P` by
  `MeasureTheory.MemLp.integrable_sq`; the bounded statement is its instance,
  producing both the weighted error and the square integrability out of `c`.

  **And the bound at the bottom of the chain is removable too, which is what
  makes the route viable at all.** Mathlib has the pull-out property of the
  conditional expectation in an unbounded form,
  `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`
  (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean:245`), which asks
  `StronglyMeasurable[m] f`, `Integrable (f * g) μ` and `Integrable g μ` and no
  bound; it is proved by exhausting the space along the sets where `f` is
  bounded. Three statements carry that trade upward —

  ```
  MeasureTheory.integral_mul_stoppedValue_eq_of_integrable_mul
  MeasureTheory.integral_mul_stoppedValue_sub_eq_zero_of_integrable_mul
  MeasureTheory.integral_mul_stoppedValue_sub_eq_compensator_of_integrable_mul
  ```

  — and
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le_lintegral_mul`
  is the form in which the chain reads them, with the weight left **under** the
  lower integral,

  ```
  ‖∫ ω, W ω * (stoppedValue Y β ω - stoppedValue Y α ω) ∂P‖ₑ
    ≤ ∫⁻ ω, ‖W ω‖ₑ * ‖C ((β ω).untopA) ω - C ((α ω).untopA) ω‖ₑ ∂P,
  ```

  so that no constant is taken out of it. The price is four integrability
  hypotheses about products with `W` in place of one bound, and the two
  integrabilities of the stopped values of `Y` fall away; for a weight in `L²`
  against an increment in `L²` the four are Cauchy–Schwarz.

  **Carried through the chain, 2026-09-22, eighth run — the cell and the
  horizon.** Three statements, the two that read the bound themselves being the
  first of them:

  ```
  MeasureTheory.lintegral_ofReal_dist_sq_le_of_isApproximatingPair_of_integrable_mul
  IsApproximatingPair.sum_lintegral_mul_enorm_compensator_sub_le
  MeasureTheory.measure_setOf_oscHitSeq_lt_le_of_isApproximatingPair_of_integrable_mul
  ```

  The first replaces the seven uses of `hVb` inside
  `lintegral_ofReal_dist_sq_le_of_isApproximatingPair` by square integrability:
  `MeasureTheory.MemLp.integrable_sq`
  (`MeasureTheory/Function/L2Space.lean:42`) for the three squares, and
  `MeasureTheory.MemLp.fun_mul`
  (`MeasureTheory/Function/LpSeminorm/CompareExp.lean:537`) at the instance
  `ENNReal.HolderTriple.instTwoTwo` (`Mathlib/Basic/ENNReal/Holder.lean:133`)
  followed by `MeasureTheory.memLp_one_iff_integrable` for the four products.
  The `L²` hypotheses fall on `V`, `Y` **and** `C`, because the compensator
  identity asks for products of the weight with the stopped values of both; in
  exchange the two plain integrabilities of the stopped values of `Y` are gone.

  **What the weight costs, named at the one place it costs anything.** The
  second summand becomes `2 * ∫⁻ ‖V (α ·) ·‖ₑ * ‖ΔC‖ₑ` with the weight *under*
  the integral, so `MeasureTheory.lintegral_const_mul'` — the last step of
  `IsApproximatingPair.sum_lintegral_enorm_compensator_sub_le` — is no longer
  available when the weight changes with the cell. The weighted chain sum is
  therefore stated against a **parameter** `Kw` bounding
  `∫⁻ ω, M ω * eLpNorm (Z (·, ω)) q (volume.restrict (Ioc 0 T)) ∂P`, with `M`
  any dominant of the cell weights; the consumer takes `M` to be the running
  maximum `⨆ t ∈ Set.Iic u, ‖V t ω‖ₑ`, which dominates every cell because the
  capped hitting times satisfy `untopA_oscHitSeqCap_le`.

  `Kw` is discharged without a new field of the class in the two cases that
  matter: `Kw = 0` for a vanishing compensator — the rescaled random walk, which
  is its own martingale, so that the weighted summand is zero whatever the
  weight — and `Kw = ‖Z‖ * ∫⁻ M` for a deterministic density. Only a random
  density against an unbounded weight would need an `L²` bound on
  `eLpNorm (Z (·, ω))`, that is, a new field; that is a question for general
  kernels and not for Donsker, and the place where it would enter is the
  `lintegral_const_mul'` step named above.

  The horizon statement is then the bounded one with `c` replaced at exactly two
  places — by the weighted error `γ` in the cell and by `Kw` in the chain — and
  everything else unchanged, the increment of the square being read at the
  weight `1`.

  **The gap cell, 2026-09-22, ninth run — and with it the second and last
  statement that reads the bound itself.** Two more declarations:

  ```
  IsApproximatingPair.lintegral_mul_enorm_compensator_sub_le
  MeasureTheory.lintegral_ofReal_dist_le_sqrt_of_isApproximatingPair_of_integrable_mul
  ```

  ```
  ∫⁻ ω, ofReal (dist (V β ω) (V α ω)) ∂P
    ≤ ofReal √((ofReal δ ^ (1 - 1/q) * (K + 2 Kw) + (2 ε' + 4 γ)).toReal)
  ```

  The bound is replaced at two places and by two different things: the increment
  of the square is read at the weight `1`, so the summand `ofReal δ ^ (1 - 1/q) * K`
  and the hypothesis on `ε'` are unchanged, while the cross term is read at the
  weight `V (α ·) ·`, and there `2 c * (ofReal δ ^ (1 - 1/q) * K)` becomes
  `2 * (ofReal δ ^ (1 - 1/q) * Kw)`. The constant `1 + 2 c` of the bounded
  statement is therefore no longer a factor but the sum `K + 2 Kw`.

  **The gap block needs no weighted form of
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le`**, and that is
  the finding of the run, decided at the source and not guessed. That statement
  is the composition of
  `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le_lintegral` with
  `IsApproximatingPair.lintegral_enorm_compensator_sub_le`, and what a cell
  reads are its two factors separately: the square identity leaves the
  compensator increments standing and they are discharged one per cell. So the
  only weighted statement the gap block needs is the weighted *second* factor,
  `IsApproximatingPair.lintegral_mul_enorm_compensator_sub_le`, and the
  Hölder-shaped composite — in which `c` stands in front of the product — is
  never called. The prose above, which names the composite as "the right
  estimate", names the *passage* and not a statement the proof invokes.

  **The single-cell weighted compensator bound is not the chain sum at `N = 1`.**
  The chain sum reads its window through a monotone family `σ : ℕ → Ω → ℝ≥0`
  between `σ 0` and `σ N` and bounds it by the horizon `u`; the single cell
  bounds its window by its *length* `δ`. That is precisely the difference
  between the two blocks of this milestone, so the weighted forms of the two
  unweighted statements are both needed, for the reason those two are. `Kw` is
  the same parameter in both and is discharged the same way — `Kw = 0` for a
  vanishing compensator, `Kw = ‖Z‖ * ∫⁻ M` for a deterministic density.

  **The three pass-through statements, 2026-09-22, tenth run — and with them the
  chain is weakened end to end.** The last three declarations:

  ```
  MeasureTheory.measure_setOf_oscHitSeq_lt_le_div_of_isApproximatingPair_of_integrable_mul
  MeasureTheory.sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair_of_integrable_mul
  MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair_of_integrable_mul
  ```

  ```
  ofReal ε₀ * P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ ω)) δ}
    ≤ N * ofReal √((ofReal δ ^ (1 - 1/q) * (K + 2 Kw) + A).toReal)
      + ((ofReal u ^ (1 - 1/q) * K + 2 * (ofReal u ^ (1 - 1/q) * Kw)) / N + A)
          / ofReal ε₀,   A = 2 ε' + 4 γ
  ```

  **`hVb` now occurs in no statement of the chain that does not have a twin
  without it.** The bounded versions stay, since a consumer who has a bound wants
  the shorter hypothesis list. A bounded `V` recovers the bounded right hand side
  from the weighted one: `γ ≤ ofReal c * ε`, and `Kw ≤ ofReal c * K` by
  `lintegral_const_mul'` against `IsApproximatingPair.lintegral_eLpNorm_le`, and
  `ofReal δ ^ (1 - 1/q) * (K + 2 c K)` is `(1 + 2 c) * (ofReal δ ^ (1 - 1/q) * K)`.

  **The gap sum needed the running maximum too, and the reason it works there is
  not the reason it works at the horizon.** At the horizon every cell endpoint is
  a capped time and lies under `u`. A gap cell overshoots the horizon by up to
  `δ` at its *right* end — that is why its window is `Set.Iic (u + δ)` — but its
  **weight sits at the left end**, which is capped, so `untopA_oscHitSeqCap_le`
  still puts the weight under `u` and one hypothesis about
  `⨆ t ∈ Set.Iic u, ‖V t ω‖ₑ` serves all `N` cells. The statement therefore
  carries two different windows, `Set.Iic u` for the weight and
  `Set.Iic (u + δ)` for the errors, and this is the one asymmetry the weakening
  adds.

  **In the assembly the three windows collapse to two hypotheses**, as the two
  did in the bounded version: the weight is read on `Set.Iic u` by both blocks,
  and the horizon block's errors follow from the gap block's by `biSup_mono`
  under `lintegral_mono` — at the unweighted error directly, at the weighted one
  through `mul_le_mul_right`, the weight being the factor that does not move.

  **Where the weakening is *not* consumed, measured at the source and worth
  saying, because the list of six suggested otherwise.** One statement stands
  above the assembly,
  `mul_measure_setOf_lt_modulusBased_postcomp_le_of_isApproximatingPair`, and it
  needs **no** twin: it reads `V = g ∘ X` for `g : E →ᵇ ℝ` and discharges the
  bound itself with `BoundedContinuousFunction.norm_coe_le_norm`, `c = ‖g‖`. The
  weighted chain is therefore consumed not through the postcomposition route but
  at the assembly directly, at a `V` that is the process itself — which is the
  case of the rescaled walk, whose two pairs
  (`isApproximatingPair_rescaledWalk`, `isApproximatingPair_sq_rescaledWalk`)
  approximate an unbounded `V` with error `0`.

  **One elaboration detail, so that no run pays for it twice.** In the weighted
  cell `{W}` stands *before* `γ` and its hypothesis, whereas in the bounded cell
  `{W}` is fixed by `hε`, which stands first. Applying the weighted cell with
  `hαW`/`hβW` therefore leaves `W` a metavariable and the elaborator runs into an
  `isDefEq` timeout; `(W := Set.Iic (u + δ))` at the call site is the fix, and
  the gap sum passes `(M := fun ω ↦ ⨆ t ∈ Set.Iic u, ‖V t ω‖ₑ)` with it for the
  same reason.

  **The condition and the three limits, 2026-09-22, tenth run — and with them
  the weakening reaches the shape a consumer meets.** Four declarations:

  ```
  MeasureTheory.IsApproximableMul
  MeasureTheory.IsApproximableMul.one_lt_exponent
  MeasureTheory.mul_measure_setOf_lt_modulusBased_le_of_isApproximableMul
  MeasureTheory.tendsto_measure_setOf_lt_modulusBased_of_isApproximableMul
  ```

  ```
  Tendsto (fun δ : ℝ≥0 ↦ P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ ω)) δ})
    (𝓝[>] 0) (𝓝 0)
  ```

  `IsApproximableMul` is `IsApproximable` with the bound removed at the two
  places the chain reads it: the error of the first pair becomes the **weighted**
  error, and `K` is joined by a second constant `Kw` for the weighted
  compensator. The order of the three limits — `N`, then `δ`, then `ε` — is
  unchanged, and the window limit is
  `tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero` at `c = 0` with `K + 2 Kw` in
  place of `K`.

  **Three design points, each decided and not defaulted.**

  * **The weight is the running maximum at the full horizon `T`, in both
    weighted fields, and not at `u`.** The assembly reads the weight at `u ≤ T`
    and the error of the first pair at `u + δ ≤ T`; stating the condition at `T`
    makes the field dominate the hypothesis, so both narrowings go the right way
    and `mul_le_mul'` supplies the weighted one in a single step. Stating it at
    `u` would make the condition too weak for its own consumer.
  * **`Kw` is an `ℝ≥0` and a parameter of the condition, not of a pair.** It
    plays the role `K` plays — a constant every pair produced at every error must
    respect — and being in `ℝ≥0` it makes the finiteness of the first summand
    free, which matters because `Real.sqrt S.toReal` reads `toReal`. It is also
    what lets `tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero` be applied at
    `K + 2 Kw`, that lemma taking its constant in `ℝ≥0`.
  * **The two square integrabilities of `V` are fields of their own, outside the
    existential**, because `V` is fixed and they say nothing about the
    approximants; the six that do belong to the pairs stay inside.

  **What the weighted route consumes next, and it is *not* the postcomposition
  criterion.** `SkorokhodSpace.isTightMeasureSet_map_postcomp_of_forall_measure_setOf_le`
  asks for a bound on the modulus of `postcomp g ∘ path`, and reaching it needs
  approximating pairs for `g ∘ X`, which pairs for `X` do not give: composing
  with `g` destroys the martingale property. The weighted chain bounds the
  modulus of the **unpostcomposed** real path, and the criterion that consumes
  that is `SkorokhodSpace.isTightMeasureSet_iff_modulusBased_nnreal`, whose only
  further input is `SkorokhodSpace.IsCompactContained` — which for the rescaled
  walk stands as `isCompactContained_rescaledWalk`.

  **One window for the whole family, weighted** —
  `MeasureTheory.exists_forall_measure_setOf_lt_modulusBased_le_of_forall_isApproximableMul`:

  ```
  ∃ δ > 0, ∀ i, P {ω | ofReal ε₀ < modulusBased 0 u (extendNNReal (Φ i ω)) δ} ≤ η
  ```

  for a family whose members share `q`, `T`, `K`, `Kw`. The uniformity is carried
  by the constants and by nothing else: `B` and the window bound are built from
  `q`, `T`, `K`, `Kw`, `u` and `ε₀`, so all three choices — count, window, error
  — are made before the member is named. The empty index is disposed of first,
  the exponent `1 < q` being read off a member.

  **And the tightness itself** —
  `MeasureTheory.isTightMeasureSet_map_pathOfProcess_of_isApproximableMul`,
  which needed one new brick in **SkorokhodSpace**,
  `SkorokhodSpace.measure_map_setOf_le_modulusBased_le`: the passage from a bound
  over the sample space to one on the image law **without** a value change,
  `Measure.map_map` composing one layer instead of two. Both were built on
  2026-09-22, tenth run.

  ```
  IsTightMeasureSet {P.map (Φ i) | i}
  ```

  for a family of right continuous progressive real processes, weighted
  approximable at every horizon with constants depending on the horizon alone,
  and with the image laws compactly contained.

  **This is the first tightness statement of the milestone that reads no bound
  on the process**, and it is what the whole weakening was for.

  **The compact containment is a hypothesis here and is not one on the
  post-composed route**, and the difference is the same one twice: the
  post-composed image laws are compactly contained for free, the range of a
  bounded `g` being bounded; the laws of the paths themselves are not. For the
  rescaled walk it is `isCompactContained_rescaledWalk`.

  **The acceptance case is not reachable from here, and that is measured and not
  suspected** (2026-09-22, eleventh run). The rescaled walk does **not** satisfy
  `IsApproximableMul` at a fixed mesh, so the hypothesis of the statement above
  is unsatisfiable on Donsker's data:

  ```
  MeasureTheory.integral_eq_of_eqOn_Ico_of_exists_approximatingPair
  MeasureTheory.IsApproximable.integral_sq_eq_of_eqOn_Ico
  MeasureTheory.IsApproximableMul.integral_sq_eq_of_eqOn_Ico
  MeasureTheory.not_isApproximableMul_of_eqOn_Ico_of_integral_sq_ne
  MeasureTheory.aestronglyMeasurable_sq_rescaledWalk
  MeasureTheory.rescaledWalk_eqOn_Ico_zero
  MeasureTheory.integral_sq_rescaledWalk_inv_ne
  MeasureTheory.not_isApproximable_rescaledWalk
  MeasureTheory.not_isApproximableMul_rescaledWalk
  MeasureTheory.not_forall_isApproximableMul_rescaledWalk
  ```

  **Where the earlier reading went wrong.** The error of the walk's own pair is
  exactly `0`, and that is true; but `IsApproximableMul` carries **two** pairs,
  and the second approximates `V ^ 2` with the plain, unweighted error. The
  weakening touches the first pair only. The second is subject to the cell
  obstruction word for word, and the walk fails it: the walk rests on
  `Set.Ico 0 (n + 1)⁻¹` as a function of time *and* of the sample point, its mean
  does not move there — it is centred, which is why
  `IsApproximable.integral_eq_of_eqOn_Ico` says nothing about it — but its
  **mean square** climbs from `0` to `σ / (n + 1)`. Hence the refutation needs
  `σ ≠ 0` and nothing else: no independence, no `L²`, no filtration.

  **Two weakenings, and they are independent.** `IsApproximableMul` removes the
  **bound on the process**; `IsEventuallyApproximable` moves the **error outside
  the index**. The walk needs both, and neither implies the other:
  `isEventuallyApproximable_rescaledWalk` is the second one alone and lives on a
  process the estimate then reads through a bounded `g`.

  **The conjunction of the two weakenings**, which is the condition the walks do
  meet, and the chain over it:

  ```
  MeasureTheory.IsEventuallyApproximableMul
  MeasureTheory.isEventuallyApproximableMul_of_forall_isApproximableMul
  MeasureTheory.exists_finite_forall_measure_setOf_lt_modulusBased_le_of_isEventuallyApproximableMul
  MeasureTheory.isTightMeasureSet_map_pathOfProcess_of_isEventuallyApproximableMul
  ```

  `IsEventuallyApproximableMul` is: to every error a finite exceptional set, off
  which every member is square integrable at the capped and at the gap times and
  has two pairs over **its own** filtration, the first with the **weighted**
  error and the second with the plain error of the square, at common constants
  `q`, `T`, `K`, `Kw`. It is `IsEventuallyApproximable` with the two weighted
  fields of `IsApproximableMul` in place of their plain neighbours, and
  `isEventuallyApproximableMul_of_forall_isApproximableMul` is what says it is a
  weakening of the latter and not a different condition.

  The modulus estimate is taken in the order `N`, `ε`, `δ`, which is the order of
  `exists_finite_forall_measure_setOf_lt_modulusBased_postcomp_le_of_isEventuallyApproximable`
  and **not** that of
  `exists_forall_measure_setOf_lt_modulusBased_le_of_forall_isApproximableMul`:
  the error survives into the estimate, so the window is chosen last and at that
  error, from `tendsto_mul_ofReal_sqrt_toReal_nhdsGT_zero` at `A = a₀`. The two
  errors are asked at one and the same `ε = a₀ / 6`, the combination
  `2 ε' + 4 γ` of
  `mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair_of_integrable_mul`
  being `a₀` at that choice; the divisor `2 + 4 ‖g‖` of the bounded twin has
  disappeared with the bound, the weight being carried inside the error.

  The tightness goes through `SkorokhodSpace.isTightMeasureSet_iff_modulusBased_nnreal`
  and `SkorokhodSpace.measure_map_setOf_le_modulusBased_le`; the exceptional
  members are not dropped but paid for, each by `isTightMeasureSet_singleton`
  read back through that **equivalence** at the same `(ε, m, η)`, with
  `SkorokhodSpace.modulusBased_mono` and `Set.Finite.exists_pos_forall_le`
  putting the finitely many windows and the common one under one positive
  minimum. The compact containment of a singleton subfamily is read off the
  family's at the same compact set.

  **The acceptance case is paid, and with it the whole tightness side of
  Donsker** (2026-09-22, thirteenth run):

  ```
  MeasureTheory.isEventuallyApproximableMul_of_tendsto_zero_cofinite
  MeasureTheory.isEventuallyApproximableMul_rescaledWalk
  MeasureTheory.isTightMeasureSet_map_rescaledWalk
  ```

  `isEventuallyApproximableMul_rescaledWalk` is
  `isEventuallyApproximable_rescaledWalk` with `Kw = 0` and the same constant
  `T ^ q.toReal⁻¹ * ‖σ‖₊`, and it differs from it at exactly three places: the
  two weighted fields are free — the walk is its own approximant, so the weight
  is integrated against `0`, and the compensator of that pair is `0`, so
  `eLpNorm (fun s ↦ Z s ω) q = 0` and `Kw = 0` carries; integrability becomes
  `MemLp … 2` at four of the six places, through
  `IsApproximatingPair.memLp_stoppedValue_of_dominated` against
  `memLp_majorant_rescaledWalk`; and the two `MemLp` fields of the zero
  compensator are `MemLp.zero`, which `simp` does **not** reach, that lemma
  being stated at `(0 : α → ε)` while the stopped value of a constant process is
  `fun ω ↦ 0`. The two square integrabilities of the member itself are the same
  two statements as those of the first approximant and are supplied twice from
  one proof.

  `isTightMeasureSet_map_rescaledWalk` is then
  `isTightMeasureSet_map_pathOfProcess_of_isEventuallyApproximableMul` at
  `isCompactContained_rescaledWalk` and the above, with `T = u + 1`, `q = 2`,
  `Kw = 0`, and `stepPath_rescaledWalk_eq` as the seam between the step-path
  description the containment reads and the process description the
  approximability reads. `hvar` is read only by the first and `hsq` only by the
  second.

  **The third item on Donsker's data, and the one computation the acceptance
  test still owes.** The seam is
  `mpSolution_of_tendsto_cadlag_of_subseq_of_zero_pathOfProcess`, whose one
  hypothesis is the vanishing of
  `𝔼[(mpTest f g t − mpTest f g s) · Z]` along the family. `mpTest` is the
  evaluation minus the **compensator**, and the compensator has to be resolved
  before the evaluation part can be expanded against it:

  * `integral_Ioc_comp_floor_mul` — the integral of a step function over an
    arithmetic grid, in closed form and **exactly**. **Proved 2026-09-22.** For
    `c > 0`, `t ≥ 0` and an arbitrary `v : ℕ → ℝ`,

    ```
    ∫ u in Set.Ioc (0 : ℝ) t, v ⌊u c⌋
      = ∑ j < ⌊t c⌋, c⁻¹ · v j + (t − ⌊t c⌋/c) · v ⌊t c⌋
    ```

    — `⌊t c⌋` full cells of length `c⁻¹`, and the broken cell at the right end.
    `fun u ↦ v ⌊u c⌋` is the shape of every path over an arithmetic grid:
    `stepPath_natCast_div` says a step path with nodes `k/c` *is* this function.

    **Nothing is asked of `v`** — no bound and no measurability. The integrand
    is constant on the interior of each cell, so the interval integrability
    there is `intervalIntegrable_const`
    (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:176`) carried
    across by `IntervalIntegrable.congr_uIoo` (`:110`), and a hypothesis on `v`
    would be read nowhere. That is what the consumer needs: the node values of a
    walk are unbounded in the sample point.

    It rests on `intervalIntegral.sum_integral_adjacent_intervals`
    (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1116`) at the
    partition `a k = min (k/c) t` — **and not at `k/c`**, so that the last cell
    is already cut at `t` and the telescoping reaches `∫ in 0..t` with no case
    split afterwards. That `a k = k/c` up to `⌊t c⌋` and `a (⌊t c⌋ + 1) = t` are
    `Nat.floor_le` and `Nat.lt_floor_add_one`
    (`Mathlib/Algebra/Order/Floor/Semiring.lean:47` and `:63`), and they are the
    whole of the arithmetic. `⌊u c⌋ = j` fails at the **right** endpoint of the
    cell, so the passage there is
    `intervalIntegral.integral_congr_Ioo_of_le`
    (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1253`) over the
    **open** cell
    and not a rewrite.

  * `integral_comp_rescaledWalk_eq_sum` — the same at the rescaled walk, which
    is the form the compensator of `SkorokhodSpace.mpTest` has there.
    **Proved 2026-09-22.**

    ```
    ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), g (V n u.toNNReal ω)
      = ∑ j < ⌊t (n+1)⌋, (n+1)⁻¹ · g (S n j ω)
        + (t − ⌊t (n+1)⌋/(n+1)) · g (S n ⌊t (n+1)⌋ ω)
    ```

    with `S n j ω = (n+1)⁻¹ᐟ² ∑ i < j, ξ i ω` the node values. There is no
    approximation in it and no probability: it is a statement about one sample
    point, and the only item of the computation independent of the independence
    of the `ξ`. It is the previous statement at `c = n + 1`, and the one
    crossing is `Nonneg.nat_floor_coe`
    (`Mathlib/Algebra/Order/Nonneg/Floor.lean:41`) — the compensator runs over a
    **real** time variable and the walk over an `ℝ≥0` one, and on `(0, t]` the
    floor of the first is the floor of the second, `Real.toNNReal` being the
    identity there.

    **The test function need not be bounded and need not be continuous.**
    `SkorokhodSpace.mpTest` supplies a `g : ℝ →ᵇ ℝ` and the coercion of one meets
    the statement, but neither field of that bundle is read, so `g` is a bare
    `ℝ → ℝ`. Of the walk only the shape of its paths enters — no measurability
    of the increments, no independence, no integrability.

  * `integral_Ioc_sub_Ioc_comp_floor_mul` and
    `integral_comp_rescaledWalk_sub_eq_sum` — the same over a **window**, which
    is the shape the gap actually reads. **Proved 2026-09-22.** `mpTest t −
    mpTest s` subtracts two compensators, each taken from `0`, and never
    integrates over `(s, t]`; so the statement is the difference of the two
    closed forms,

    ```
    ∑ j ∈ Finset.Ico ⌊s (n+1)⌋ ⌊t (n+1)⌋, (n+1)⁻¹ · g (S n j ω)
      + (t − ⌊t (n+1)⌋/(n+1)) · g (S n ⌊t (n+1)⌋ ω)
      − (s − ⌊s (n+1)⌋/(n+1)) · g (S n ⌊s (n+1)⌋ ω)
    ```

    — the cells strictly between the two floors with their full weight, and
    what is left of the two broken cells at the ends. The cardinality of that
    `Finset.Ico` is what the Lindeberg estimate is summed over.

    **No integrability crosses here either**, and that is the point of stating
    the window as a difference: the passage is `Finset.sum_Ico_eq_sub` — the
    additive twin of `Finset.prod_Ico_eq_div`
    (`Mathlib/Algebra/BigOperators/Intervals.lean:94`), generated by
    `@[to_additive]` and therefore carrying no `theorem` line of its own — and
    `ring`. Written as `∫ u in Set.Ioc s t` the window would have had to produce
    the integrability of the integrand in order to be split, and that is exactly
    what the statements above were arranged not to need.

  * `sub_comp_rescaledWalk_eq_sum` — the **evaluation** part of the gap over the
    same index set. **Proved 2026-09-22.** `mpTest` is evaluation minus
    compensator, and the two halves have to stand over *one* index set before
    the cell by cell expansion is writable at all. It is a telescoping sum and
    nothing else, `Finset.sum_Ico_sub` — the additive twin of
    `Finset.prod_Ico_div` (`Mathlib/Algebra/BigOperators/Intervals.lean:226`),
    generated by `@[to_additive]` and carrying no `theorem` line of its own.
    There is no integral in it and no null set, which is why the right endpoint
    costs nothing here and did cost something at the compensator: the evaluation
    reads the floor **at** `t`, where the cell identity holds.

  * `mpTest_sub_rescaledWalk_eq_sum` — the **whole** gap, cell by cell, which is
    what the Lindeberg expansion is carried out on. **Proved 2026-09-22.**

    ```
    (mpTest f g t − mpTest f g s)(walk n, ω)
      = ∑ k ∈ Finset.Ico ⌊s (n+1)⌋ ⌊t (n+1)⌋,
          (f (S n (k+1) ω) − f (S n k ω) − (n+1)⁻¹ · g (S n k ω))
        − (t − ⌊t (n+1)⌋/(n+1)) · g (S n ⌊t (n+1)⌋ ω)
        + (s − ⌊s (n+1)⌋/(n+1)) · g (S n ⌊s (n+1)⌋ ω)
    ```

    One summand per cell — the increment of `f` across it **minus** the
    compensator's weight at its left node, which is exactly the shape a second
    order Taylor expansion is held against, the increment being
    `(n+1)⁻¹ᐟ² ξ k` — and two boundary terms, each of size at most
    `(n+1)⁻¹ ‖g‖`, which is the part of the gap that vanishes with no expansion
    at all.

    **Still no probability in it.** It is an identity at one sample point,
    assembled from the two previous ones by `Finset.sum_sub_distrib` and `ring`.
    The centring, the second moment and the independence enter only when the
    expectation of this is taken — which is where the acceptance test now
    stands, and the first place in the computation where they are read.

  * `indep_comap_natural_partialSum` — **an increment is independent of the past
    of the partial sums**. **Proved 2026-09-22.**

    ```
    Indep (comap (ξ n)) (Filtration.natural (fun m ω ↦ ∑ k < m, c · ξ k ω) _ n) P
    ```

    Mathlib's `ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt`
    (`Mathlib/Probability/BorelCantelli.lean:43`) states it against the past of
    the **summands**; what every consumer holds is the past of the **sums**, and
    the passage is the inclusion `𝒢 (m+1) ≤ Filtration.natural ξ m`. The scaling
    factor `c` is carried and costs nothing, because the rescaled walk is
    written over the filtration of `c · S` — and no `c ≠ 0` is asked, the
    filtration collapsing to `⊥` at `c = 0`, where independence is only easier.
    `IsProbabilityMeasure P` is a conclusion and not a hypothesis.

    It is the one probabilistic input of the walk that is read **twice**, by
    `martingale_partialSum_of_iIndepFun` at `c = 1` and by
    `integral_mul_comp_rescaledWalk_mul_eq_zero` at `c = (n+1)⁻¹ᐟ²`.

  * `integral_mul_eq_mul_integral_of_indep_comap` — **a factor decouples from
    everything measurable for a σ-algebra it is independent of**:
    `∫ W · X = (∫ W) · (∫ X)` when `σ (X)` is independent of a σ-algebra `W` is
    measurable for. **Proved 2026-09-22.** It is Mathlib's product formula with
    the independence read off **σ-algebras** rather than off the pair of
    functions, which is the shape a filtration hands it over in.

    `integral_mul_eq_zero_of_indep_comap` is it at `∫ X = 0` and is what the
    first order term reads; the second order term reads the product formula
    itself, at `∫ X = σ²`. That it is an **identity** and not a null statement
    is what lets both consumers stand on one hypothesis set: the degenerate
    branch is the same `0 = 0` in either.

    **No integrability is asked.**
    `ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral`
    (`Mathlib/Probability/Independence/Integration.lean:423`) gives
    `∫ W · X = P[W] · P[X]` from bare `AEStronglyMeasurable`, its proof running
    through `ProbabilityTheory.IndepFun.integral_bilin'` (`:335`), which splits
    on the integrability of the product and observes that where it fails, one of
    the factors fails too and **both sides are the Bochner junk value `0`**.

    The junk value is therefore read here, and on purpose: in the degenerate
    case the identity is empty rather than false. A consumer that wants content
    supplies boundedness of `W` and integrability of `X`, whence
    `ProbabilityTheory.IndepFun.integrable_mul` (`:358`). This is the one place
    in the milestone where a hypothesis is left out because the junk values on
    the two sides agree.

  * `abs_sub_natCast_floor_div_le` — **what is left of a broken cell is shorter
    than a cell**: `|t − ⌊t c⌋/c| ≤ c⁻¹` for `0 ≤ t` and `0 < c`. **Proved
    2026-09-22.** `Nat.floor_le` for the lower bound and `Nat.lt_floor_add_one`
    for the upper, and that is the whole of it. `0 ≤ t` is read and cannot be
    dropped: at a negative `t` the floor is `0`, the remainder is `t` itself,
    and the bound fails for every `t < −c⁻¹`.

  * `abs_mpTest_sub_rescaledWalk_sub_sum_le` — **the two boundary terms are of
    order `(n+1)⁻¹`, uniformly in the sample point**: the gap differs from its
    cell sum by at most `2 (n+1)⁻¹ ‖g‖`. **Proved 2026-09-22.** They carry no
    increment of `f` and are therefore never touched by the expansion; this is
    the part of the gap that goes away by counting, and what is left after it is
    the cell sum.

    The estimate is uniform in `ω`, which is what lets a consumer take it under
    the integral against a bounded weight with no integrability argument of its
    own. **Only `g` is asked to be bounded and `f` is asked nothing**, `f`
    cancelling out of the two boundary terms — the reverse of what the cell sum
    asks, where `f` is expanded and `g` only has to match `½ σ² f''`.

  * `abs_sub_taylor_two_le` — **the second order Taylor expansion with its
    remainder bounded by the third derivative**. **Proved 2026-09-22.**

    ```
    |f (x + h) − f x − f' x · h − f'' x · h² / 2| ≤ M · |h|³ / 6   for |f'''| ≤ M
    ```

    It is what turns the increment of `f` across a cell into the two terms the
    expansion is held against plus something estimable, and the last ingredient
    of the cell computation that asks anything of `f` beyond boundedness. The
    acceptance test affords it: its class is `A = {(f, f''/2) | f ∈ Cc^∞(ℝ)}`.

    **Both signs of `h` are covered with no case split**, Mathlib's
    `taylor_mean_remainder_lagrange_iteratedDeriv`
    (`Mathlib/Analysis/Calculus/Taylor.lean:348`) being stated over `Set.uIcc`
    and not over an ordered `Set.Icc`; only `h = 0` is taken separately, and
    there both sides are `0`. And the passage from `iteratedDerivWithin` to
    `iteratedDeriv` **at the endpoint** costs nothing —
    `iteratedDerivWithin_eq_iteratedDeriv`
    (`Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:70`) asks `UniqueDiffOn`
    of the set and `ContDiffAt` of the function, not that the set be a
    neighbourhood. That is the thing to know before reaching for a reflection
    argument.

  * `integral_mul_comp_rescaledWalk_mul_eq_zero` — **the first order term of
    Donsker's expansion vanishes, cell by cell**, and this is where probability
    enters the acceptance test for the first time. **Proved 2026-09-22.**

    ```
    ∫ ω, h (S n k ω) · ξ k ω · Z ω ∂P = 0
    ```

    for `h` measurable and `Z` measurable for the past at `k`. The second order
    Taylor expansion of `f` splits the increment of the cell into a term of
    first order `f' (S n k) · (n+1)⁻¹ᐟ² ξ k`, a term of second order and a
    remainder; the second is held against the compensator and the third is
    estimated, but the first **has to vanish exactly** — it is of order
    `(n+1)⁻¹ᐟ²` and no estimate removes it. This is it, with `h = f'` and `Z`
    the weight the gap is tested against.

    **There are two factors in front of `ξ k` and not one**, the path piece
    `h (S n k)` and the weight `Z`, both measurable for the past at `k`; they
    are merged into a single such factor **before** independence is asked, since
    asking it of `ξ k` against `h (S n k)` alone leaves `Z` to be carried
    through afterwards.

    Of the three hypotheses of the acceptance test this is the first statement
    to read any: `hind` and `hcent` enter here, everything above being an
    identity at one sample point. Integrability is read at neither `ξ k` nor the
    product, and neither `h` nor `Z` need be bounded, for the reason set out at
    `integral_mul_eq_zero_of_indep_comap`.

    **The filtration is not `Filtration.natural ξ` at `k`** but that of the
    scaled sums, which `martingale_rescaledWalk` and
    `isStronglyProgressive_rescaledWalk` already carry. Over the first the
    statement is false: that σ-algebra holds `ξ k` itself, and `h = 1`, `Z = ξ k`
    turn the left hand side into `∫ ξ k ^ 2`.

  * `integral_mul_comp_rescaledWalk_sq_mul_eq_smul` — **the second order term of
    Donsker's expansion**, where the second moment enters and where it is decided
    whether the compensator is met. **Proved 2026-09-22.**

    ```
    ∫ ω, h (S n k ω) · ξ k ω ^ 2 · Z ω ∂P = v · ∫ ω, h (S n k ω) · Z ω ∂P
    ```

    for `∫ ξ k ² = v`, `h` measurable and `Z` measurable for the past at `k`.
    After the first order term has vanished, the cell carries
    `½ f'' (S n k) · (n+1)⁻¹ ξ k ² − (n+1)⁻¹ g (S n k) + remainder`, and this
    replaces `ξ k ²` by its constant `σ²` under the integral; for
    `g = ½ σ² f''`, the generator of Brownian motion, the two **cancel exactly**,
    the factor `(n+1)⁻¹ ` being the same on both sides.

    **The second moment is a bare real `v` and not a square**, nothing in the
    proof reading positivity, and it is asked of the single index `k`: the cells
    are treated one at a time and only the consumer that sums them needs the
    moments to agree.

    **Neither `h` nor `Z` need be bounded and `ξ k` need not be square
    integrable**, contrary to what an identity with a non-zero right hand side
    leads one to expect. `integral_mul_eq_mul_integral_of_indep_comap` is a
    **product** formula: where the product fails to be integrable all three
    integrals are the Bochner junk value `0`, the left hand side is `0` and the
    right hand side is `v · 0`. Boundedness returns at the consumer.

    **Centring is not read.** Of the three hypotheses of the acceptance test
    this statement carries `hind` alone. And the filtration is again that of the
    scaled sums: over `Filtration.natural ξ` at `k` the statement is false,
    `h = 1` and `Z = ξ k ²` giving `∫ ξ k ⁴` against `(∫ ξ k ²)²`, which differ
    by the variance of `ξ k ²`. `Z = ξ k` is **not** a witness — it gives
    `∫ ξ k ³` against `σ² · ∫ ξ k`, and for a symmetric increment both are `0`.

  **Prokhorov, with the crossing of the two types done once**, and the second
  item of the chain on Donsker's data:

  ```
  MeasureTheory.isCompact_closure_range_probabilityMeasure_of_isTightMeasureSet
  MeasureTheory.isCompact_closure_range_map_rescaledWalk
  ```

  The first is `isCompact_closure_of_isTightMeasureSet` with the passage from a
  set of `Measure` to a set of `ProbabilityMeasure` and on to a `Set.range`,
  which is the shape `tendsto_of_isRelativelyCompact_of_unique` reads. It asks
  `BorelSpace` and `T2` of the space and nothing else — no Polishness, no
  completeness; those are read upstream, in the tightness. That crossing had been
  written out inline twice, in
  `isCompact_closure_range_of_subalgebra_forall_martingale` and in
  `isCompact_closure_range_of_subalgebra_forall_exists_bounded_pair`; both are
  now four lines through it, with no hypothesis added or dropped.

  **The alternative, and why it is the more expensive one.** The acceptance
  example below states Donsker with `A = {(f, f''/2) | f ∈ Cc^∞(ℝ)}`, that is,
  with the martingale hypothesis at `f ∘ X n` for bounded `f`. Building the
  pairs there is the Lindeberg–Taylor computation and not a corollary of the two
  pairs above, whose approximants are the walk and its square. Either route
  closes the item; the conjunction of the two weakenings reuses what is built,
  the other does not.

* Convergence in measure as a second mode: the space of càdlàg paths with the
  topology of convergence in Lebesgue measure, in which the coordinates are
  nowhere continuous, and `mpSolution_of_tendsto_inMeasure`, obtained from
  Milestone 10 by supplying hypothesis (a) through the Skorokhod representation
  theorem of **WeakConvergence** and Fubini. State also the tightness criterion
  in that topology: a uniform bound on the conditional variation
  `sup over subdivisions of 𝔼[∑ ‖𝔼[X (t (i+1)) - X (t i) | 𝓕 (t i)]‖]`.

**Acceptance examples.**

* **Donsker, assembled from the items in order.** `E = ℝ`,
  `X n t = (1/√n) * ∑ k ≤ ⌊n t⌋, ξ k` for i.i.d. centred `ξ k` of variance `1`,
  and `A = {(f, f''/2) | f ∈ Cc^∞(ℝ)}`. `isTight_map_postcomp_of_exists_martingale`
  gives tightness of each `postcomp f ∘ X n`,
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` lifts it to `{X n}`,
  `isRelativelyCompact_of_approx` makes the family relatively compact,
  `mpSolution_of_tendsto_cadlag` identifies every limit point as a solution for
  `A`, and `tendsto_of_isRelativelyCompact_of_unique` upgrades relative
  compactness to convergence once Milestone 6 supplies uniqueness. Each of the
  five items is used exactly once and in this order, which is the acceptance
  test for the milestone as a chain.

  **What the five items reach, stated exactly, 2026-09-20.** They give
  tightness, relative compactness, and that *every limit point solves the
  martingale problem for* `f ↦ f''/2`. They do **not** give `X n ⇒ Brownian
  motion`, and the two missing steps are named here so that no run reports the
  weaker statement under the stronger name.

  * **Uniqueness for `f ↦ f''/2` is not available from anything built here.**
    The obstruction is *not* that `f''` is unbounded — it is not, and
    `mpFamily` takes pairs of bounded functions, so the family is in order. It
    is that `integral_mul_eq_expJumpApply_of_isMPSolution`, the route to
    `honedim` in Milestone 4, runs on the exponential series `∑ tᵏ Aᵏ f / k!`
    and needs `‖A f‖ ≤ C ‖f‖` **uniformly**, so that iteration gives
    `abs_iterate_jumpApply_le`, `‖Aᵏ f‖ ≤ (2L)ᵏ ‖f‖`. For `A = d²/dx² / 2` one
    has `Aᵏ f = 2⁻ᵏ f⁽²ᵏ⁾` and no such `C` exists over `Cc^∞`: a function small
    in sup norm may have a large second derivative. The series does not
    converge and the proof fails at its first step. That is the whole content
    of calling the generator unbounded, and it is why Hille--Yosida replaces
    the series by the resolvent.

    Three routes to the missing `honedim`, of which the third is the one this
    roadmap can take:

    1. **Hille--Yosida** (Ethier--Kurtz 4.4.1) — excluded by design, see
       `rem:noch1`; it belongs to the **OneParameterSemigroups** roadmap.
    2. **Duality** — Milestone 8, unstarted.
    3. **Directly, through the Fourier transform.** `honedim` asks only that
       two solutions with the same initial law have the same one-dimensional
       distributions. Under the Fourier transform `A` becomes multiplication by
       `-ξ²/2`, and the martingale property turns the identification into an
       ordinary differential equation in `t` for each fixed `ξ`, whose solution
       is `exp (-t ξ² / 2)` times the initial characteristic function. This
       avoids both the series and the semigroup theory. Mathlib supplies
       `Real.fourierIntegral` and `ProbabilityTheory.gaussianReal`
       (`Mathlib/Probability/Distributions/Gaussian/Real.lean:222`), and the
       characteristic function of `gaussianReal 0 t` is the needed one. **This
       is a self-contained point and is not part of the chain above**; state it
       as its own item rather than letting Donsker depend on an unpaid input.

  * **Identifying the limit with Brownian motion is a second step, and Mathlib
    meets it halfway. Checked at the source 2026-09-21.** Mathlib `master`
    carries `Mathlib/Probability/BrownianMotion/` (548 lines) and it defines
    Brownian motion exactly by the covariance the author asked about:

    ```lean
    def covMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := .of fun s t ↦ min s t
    lemma covMatrix_apply (s t : I) : covMatrix I s t = min s.1 t.1 := rfl

    structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
      hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P

    structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop
        extends IsPreBrownianReal X P where
      cont : ∀ᵐ ω ∂P, Continuous (X · ω)
    ```

    So `IsBrownianReal` is *all finite dimensional laws are centred Gaussian
    with covariance `s ⊓ t`, plus almost surely continuous paths*, with
    `IsGaussianProcess.isPreBrownianReal_of_covariance` as the entry point and
    `IsBrownianReal.smul`, `.shift`, `.neg` available. **Nothing there mentions
    a martingale problem**, so the bridge is ours; but what it has to produce is
    named, not vague.

    **The bridge is the Fourier computation, applied once more.** To be shown:
    a solution of the martingale problem for `f ↦ f''/2` started at `0` has all
    finite dimensional laws centred Gaussian with covariance `s ⊓ t`.

    1. *One time.* With `f = fun x ↦ exp (I * ξ * x)` the martingale property
       becomes `d/dt (μ t).charFun ξ = -(ξ^2/2) * (μ t).charFun ξ`, so
       `(μ t).charFun ξ = exp (-t * ξ^2 / 2)`, which is `gaussianReal 0 t`.
       This is literally the uniqueness item above; one computation serves both.
    2. *Finitely many times.* The same equation between consecutive times,
       together with the Markov property — which Milestone 6 supplies **as a
       conclusion** once the uniqueness of (1) is in hand — gives independent
       increments with `X t - X s ~ gaussianReal 0 (t - s)`, hence
       `Cov (X s) (X t) = s ⊓ t`. That is `IsPreBrownianReal`.
    3. *Continuity of the paths* is the one part the Fourier computation does
       **not** give. Our limit points live in `D(ℝ≥0, ℝ)` and are a priori only
       càdlàg, so `IsBrownianReal.cont` needs the jump heights to vanish in the
       limit. That is \EK, Section 3.10, "Convergence to a process in
       `C_E[0,∞)`", through the functional
       `J x = ∫ e^{-u} (sup_{t ≤ u} r (x t) (x (t-)) ⊓ 1) du`, which is
       continuous on `D_E[0,∞)` by \EK, Proposition 3.5.3 and vanishes exactly
       on the continuous paths. **This is its own item** and is not part of the
       chain; a run must not report `IsPreBrownianReal` under the name
       `IsBrownianReal`.
* **The times `D` must avoid the fixed discontinuities.** In
  `mpSolution_of_tendsto_cadlag`, `D` is taken to be the set of times at which
  the limit has no fixed discontinuity. On the pair
  `X n = Set.indicator (Set.Ici (1 + 1/n)) 1` and
  `X = Set.indicator (Set.Ici 1) 1` of **SkorokhodSpace** Milestone 4, `X n → X`
  in `D ι ℝ` while the finite dimensional distributions at `t = 1` do not
  converge; so a version of the item with `D` an arbitrary dense set is false,
  and `SkorokhodSpace.exists_countable_dense_continuity` is what supplies the
  right `D`.
* **The pathwise form is weaker where it matters.** Take `f n = f` and
  `g n = g + n * Set.indicator {x n} 1` for points `x n` that the processes
  `X n` visit with probability at most `1/n²`. Then `‖g n - g‖ = n` does not
  tend to `0`, so `mpSolution_of_tendsto_cadlag` does not apply, while
  `𝔼^{P n} ∫_0^t ‖(g n - g) (X n u)‖ du → 0` and
  `mpSolution_of_tendsto_cadlag_of_pathwise` does. This is the instance that
  shows the second item is not a restatement of the first.
* **Separating is not convergence determining, and the milestone must not
  confuse them.** In `isRelativelyCompact_of_approx` the algebra in the domain
  of `A` is used twice: for density in the topology of uniform convergence on
  compacts, which is Stone–Weierstrass proper, and for being separating, which
  is `IsSeparating.of_subalgebra`. On `E = ℝ` the trigonometric algebra of
  **WeakConvergence** Milestone 1 is separating and does **not** strongly
  separate points, so it is not convergence determining by that route; the item
  must therefore not claim the stronger property, and this is the instance on
  which such a claim would be checked.

## Milestone 12: existence from a dual process

> **This milestone is a roadmap-for-a-roadmap, and is not to be attempted as
> stated.** Its last step rests on the Kolmogorov extension theorem, which is
> the separate `KolmogorovExtension` roadmap and does not yet exist in Mathlib;
> and the fibred state space of its last point is a design change that no other
> milestone here needs. It is recorded so that the shape of the argument is not
> lost, not as work to attempt now.

Index `[0,∞)` or `ℕ`, state spaces `E₁`, `E₂` Polish, a shift invariant clock.

* Data: a Markov semigroup of kernels `(P t)` on `E₂`, a measurable
  `F : E₁ × E₂ → ℝ`, and a family of operators, subject to a balance condition
  stated in integrated form — no strong continuity, no generator and no domain
  theory.
* `dualSemigroup`: the family `t ↦ ∫ F (x, y) ∂(P t z)` and its
  Chapman–Kolmogorov identity, from the Markov property, Fubini and the
  additivity `Clock.interval_union` of Milestone 1.
* `exists_projectiveFamily_of_dual`: the balance condition together with a
  separation condition on `F` determines a consistent family of finite
  dimensional distributions.
* `exists_mpSolution_of_dual`: the Kolmogorov extension theorem of the roadmap
  **KolmogorovExtension** turns that family into a measure, and the resulting
  coordinate process solves the martingale problem. Together with Milestone 8
  this gives existence and uniqueness from one dual process.
* The representability condition, that a positive linear functional is given by
  a kernel, from `RealRMK.integral_rieszMeasure`
  (`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:345`, for
  `f : C_c(X, ℝ)`), with `NNRealRMK.integral_rieszMeasure` and
  `NNRealRMK.lintegral_rieszMeasure` (`NNReal.lean:47,56`) as the non-negative
  forms.
* The fibred state space: state Milestone 12 for `E : ι → Type*` with
  `[∀ t, MeasurableSpace (E t)]` and paths in `Π t, E t`, the test pairs becoming
  sections. The abstract layer of Milestones 2, 3, 5, 6, 8 and 10 never mentions
  the state space and applies unchanged; Milestones 9 and 11 are stated for a
  constant fibre. The historical process, whose state at time `t` is the path up
  to `t`, is the instance that needs the fibred form.

## Milestone 13: the full generator, and which operators are generators

> **This milestone is a roadmap-for-a-roadmap, and is not to be attempted as
> stated.** It names one proposition and its converse, and it names them because
> `rem:fullgenerator` of the manuscript rests on them; it does not develop the
> theory they belong to. Contributors should not follow it. What a full treatment
> would need is the subject of the `OneParameterSemigroups` roadmap, and the
> boundary between the two is drawn in the next paragraph.

**Relation to `OneParameterSemigroups`, and an offer.** The overlap is large,
but it is with Ethier--Kurtz rather than with this roadmap. Their Chapter 1 is
semigroup theory --- Hille--Yosida, cores, resolvents, dissipativity, the
exponential formula --- and the `OneParameterSemigroups` roadmap covers exactly
that ground. The manuscript behind this roadmap deliberately does not use any of
it: uniqueness is obtained from the abstract theorem together with duality, and
the semigroup-based criteria of Ethier--Kurtz, Theorem 4.4.1 and Corollary
4.4.4, are left out by design. So the two roadmaps do not collide; they abut,
and `OneParameterSemigroups` is the natural home for the chapter this one
declines to use.

What does **not** stand there, and is the reason this milestone exists at all,
is the *measurable* branch. Their Part A builds strongly continuous semigroups
on a Banach space with the generator a densely defined `LinearPMap`, and it
notes in passing that a strongly continuous semigroup need not be
norm-measurable; it does not treat measurable semigroups, the full generator, or
a multivalued generator. But the transition semigroup of a Markov process on the
bounded measurable functions is **not strongly continuous**, and its full
generator is **multivalued** --- a relation, not a `LinearPMap`. That is
Ethier--Kurtz, Proposition 1.5.1, and it is the object below.

The right resolution is therefore not to keep this milestone here but to offer
it there: the measurable semigroup and its full generator belong in
`OneParameterSemigroups` as a branch of Part A, whose stated audience already
includes researchers in Markov semigroups. Until that is agreed, the statements
below record what is needed, and they are not to be implemented from here.

Mathlib has no semigroup of operators. The word `dissipative` occurs nowhere in
it, there is no strongly continuous or measurable one parameter semigroup, and
the Hille–Yosida theorem stands in `docs/1000.yaml` as `Q974405` without a
`decl`. What is needed here is one proposition about the full generator and its
converse; cores, the exponential formula and Hille–Yosida are not used and are
not part of this milestone. Fix `[RCLike 𝕂]`, a state space `E` with
`[MeasurableSpace E]`, and let `L` be the `𝕂`-valued bounded measurable
functions on `E` with the sup norm.

* `IsDissipative (A : Set (L × L))`, defined as
  `∀ p ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖p.1‖ ≤ ‖lam • p.1 - p.2‖`. The relation
  is the primitive and a single valued operator is its graph, matching the
  convention of this roadmap. `IsDissipative.mono` and the stability under
  `Submodule.span 𝕂`.
* `MeasurableContractionSemigroup T`: `T : ℝ≥0 → L →L[𝕂] L` with `T 0 = 1`,
  `T (s + t) = (T s).comp (T t)`, `‖T t‖ ≤ 1`, and `t ↦ T t f` measurable for
  every `f`. Measurability, not strong continuity: the transition semigroup of a
  Markov process on the bounded measurable functions is not strongly continuous,
  and nothing below needs it to be.
* `fullGenerator T : Set (L × L)`, the pairs `(f,g)` with
  `T t f - f = ∫ s in Set.Ioc 0 t, T s g` for every `t : ℝ≥0`, the integral
  being the Bochner integral of `Mathlib/MeasureTheory/Integral/Bochner/`;
  together with `fullGenerator_isSubmodule`, that it is a `𝕂`-submodule of
  `L × L`.
* `fullGenerator_isDissipative` and `inv_sub_fullGenerator_eq_integral`: the
  full generator is dissipative, and
  `(lam • 1 - Â)⁻¹ h = ∫ t in Set.Ioi 0, Real.exp (-lam * t) • T t h` on the
  range of `lam • 1 - Â` for `lam > 0` (Ethier–Kurtz, Proposition 1.5.1). This
  is the whole of the semigroup theory the manuscript uses.
* `mpSolution_resolvent_repr`: for `ι = [0,∞)` with the Lebesgue clock, if `X`
  solves the martingale problem for `A` with respect to `𝓖` and `(f,g) ∈ A`,
  then for `lam > 0` and `t : ι`,
  `Real.exp (-lam * t) • f (X t) =ᵐ P[∫ s in Set.Ioi 0, Real.exp (-lam * (t + s)) • (lam • f - g) (X (t + s)) | 𝓖 t]`.
  The proof is the optional sampling of Milestone 9 together with a Fubini
  rearrangement, and it is the only place where the index set is `[0,∞)` and the
  clock is Lebesgue measure — for the exponential, which solves `φ' = -lam • φ`,
  and for the rearrangement. State it in its own right; it is the input to the
  next item.
* `isDissipative_of_forall_exists_mpSolution`: if `A` is a `𝕂`-submodule of
  `L × L` and the martingale problem for `(A, Measure.dirac x)` has a solution
  for every `x : E`, then `A` is dissipative (Ethier–Kurtz, Proposition 4.3.5).
  Evaluate the previous item at `t = 0` and bound the integrand by
  `‖lam • f - g‖`.
* `isMPSolutionFor_fullGenerator`: a Markov process with measurable transition
  semigroup `T` solves the martingale problem for `fullGenerator T`
  (Ethier–Kurtz, Proposition 4.1.7), by the Markov property and Fubini against
  the clock of Milestone 1. With `fullGenerator_isDissipative` this is the
  converse of the previous item, and the two together say that the operators
  arising from Markov processes are exactly the dissipative ones.
