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
  `Filtration ℕ` as well. Doob's `Lᵖ` inequality is absent for every index.
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
* For `[AddMonoid ι]` with a compatible order, `Clock.IsShiftInvariant q`,
  defined as `q ((r + ·) ⁻¹' B) = q B`, and `Clock.interval_add` expressing
  `interval q c (r + s) (r + t) = (r + ·) '' interval q c s t` up to a null set.
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
  `Q.measurableSpace ⊗ 𝓕 t`-measurable. This is `IsStronglyProgressive` in the
  shape a `Clock` forces — the clock carries its `MeasurableSpace ι` as a field
  and not as an instance, so the subtype of `Set.Iic t` cannot be written without
  `@` — and it is a hypothesis of `isMPSolutionFor_iff_forall_fdd` in both its
  forms. It is a hypothesis on `X` and the clock alone, never on `P`.
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
  be handed to it; and `integrableOn_of_bounded`, a bounded measurable function
  is integrable on a set of finite measure. Together they are what turns
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
  metrizable. This is the statement that turns every later theorem into a
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

## Milestone 4: jump processes

A concrete family of solutions, built without any of the theory above. Index
`[0,∞)`, state space `E` with `[MeasurableSpace E]`.

* `IsStepPath`, **proved** on 2026-09-09, sixteenth run, together with
  `IsStepPath.isCadlagPath` and
  `IsStepPath.finite_setOf_not_continuousAt_inter`: the paths the construction
  below delivers, isolated first, because three otherwise awkward steps are easy
  on them — the joint measurability in `(t, ω)` is a sum over finitely many
  pieces instead of a limit argument, the assignment `t ↦ n` of a time to its
  jump index is a `Nat.find`, and càdlàg is immediate. It is a **predicate** and
  not a type class: it is a property of a term, so instance search has nothing to
  key on, and Mathlib's fallback `Fact` is expressly not meant for it
  (`Logic/Basic.lean`, library note "fact non-instances"). Only when more than
  two theorems carry it does it become a bundled structure after the pattern of
  `D(ι, E)`. The manuscript calls this set of paths `F` in `set:pathjump`.

  **The definition is constancy on one sided neighbourhoods and not local
  finiteness of the jump set, and the difference is a counterexample and not a
  preference.** Asking for
  `∀ K, IsCompact K → ({x | Function.leftLim f x ≠ f x} ∩ K).Finite` and
  deriving càdlàg from it does **not** work:
  `exists_finite_setOf_leftLim_ne_not_isCadlagPath` exhibits
  `f = Set.indicator {0} 1` on `ℝ`, whose jump set is `{0}` — finite on every
  compact set — and which is not right continuous at `0`. `Function.leftLim` is
  *total* (`Topology/Order/LeftRightLim.lean:50`): where no left limit exists it
  returns the value, so a path with no left limits anywhere has an **empty** jump
  set and passes such a test vacuously. A condition on the jump set alone sees
  neither half of càdlàg. The definition is therefore

  ```
  def IsStepPath (f : ι → E) : Prop :=
    (∀ x, ∀ᶠ y in 𝓝[≥] x, f y = f x) ∧ ∀ x, ∃ c, ∀ᶠ y in 𝓝[<] x, f y = c
  ```

  — between two consecutive jump times the path does not move — and the local
  finiteness of the discontinuities is a *theorem* on it,
  `IsStepPath.finite_setOf_not_continuousAt_inter`, proved by
  `IsCompact.elim_nhds_subcover` as in
  `IsCadlag.finite_largeLeftJumpSet_inter` of **SkorokhodSpace** Milestone 2.
  That proof needs **no** case distinction on `IsMax x` or `IsMin x`:
  `mem_nhdsWithin` returns its witnesses already open, and `Set.Ioi x`,
  `Set.Iio x` are open, so the two sides are open sets on which `f` is constant
  and every point of `V ∩ W` other than `x` lies in one of them. What carries the
  argument is that the two sides are open, not that they have endpoints.
* Data: a measurable rate `lam : E → [0,∞)` and a Markov kernel `mu : Kernel E E`.
  The operator is `A f x = lam x * ∫ y, (f y - f x) ∂(mu x)` with
  `A = {(f, A f) | f bounded measurable}`.
* `jumpProcess lam mu nu`: the process with initial law `nu` that waits an
  exponential time of rate `lam (X t)` and then jumps according to `mu`,
  constructed from a Markov chain with kernel `mu` and an independent sequence
  of exponential variables. Give the construction on an explicit probability
  space and prove that its paths are càdlàg and piecewise constant. **Proved**
  on 2026-09-09, seventeenth run, in thirty three declarations of
  `Suggested.lean`. The sample space is `(ℕ → E) × (ℕ → ℝ)` — the trajectory of
  the embedded chain and the sequence of its waiting times — carrying
  `jumpMeasure mu nu = (chainKernel mu ∘ₘ nu).prod waitingMeasure`, a probability
  measure. `chainKernel` is `ProbabilityTheory.Kernel.traj`
  (`IonescuTulcea/Traj.lean:518`) applied to the family that reads the **last**
  coordinate, which is what makes it a chain rather than the product
  `exists_kernel_pi_of_markov` of **KolmogorovExtension**; `waitingMeasure` is
  `MeasureTheory.Measure.infinitePi` of `ProbabilityTheory.expMeasure 1`. Neither
  needs a topology on `E`; only the path statements do.
  `jumpMeasure_map_chain_zero` says the initial law is `nu`,
  `measurable_jumpProcess` gives the joint measurability in `(t, ω)`, and
  `isStepPath_jumpProcess`, `isCadlagPath_jumpProcess` give the paths.

  **The deterministic core is separated from the probabilistic one, and the
  separation is where the work is.** `stepIndex T t = sInf {n | t < T (n+1)}` is
  the index of the window containing `t` — `Nat.find` made total by
  `sInf ∅ = 0`, the junk value being returned exactly on the explosion set. All
  path statements are about `stepPath T y` under two hypotheses,
  `StrictMono T` and `∀ s, ∃ n, s < T (n+1)`, the second of which *is* non
  explosion; `tendsto_jumpTime_atTop` is the only place a bound on the rate is
  used, and it goes through the single inequality
  `(∑_{k<n} ξ k) / L ≤ jumpTime lam y ξ n` (`sum_div_le_jumpTime`).

  **`StrictMono` and not `Monotone`, and the difference is one case of the
  proof.** The left hand conjunct of `IsStepPath` at a point `x = T (m+1)` that
  is itself a jump time needs the constant `y m` on `Set.Ioo (T m) x`, which is
  a left neighbourhood only because `T m < T (m+1)`. Under `Monotone` alone the
  argument has to descend to the least `k` with `T k = x`, and that is a second
  induction for no gain: the construction delivers strict monotonicity.

  **The positivity of the rate is a restriction of the signature and not a
  convenience.** `x / 0 = 0` in Lean, so at a state with `lam x = 0` — which the
  model intends to be absorbing, with an infinite holding time — the holding time
  computes to `0` and the path leaves at once. `strictMono_jumpTime` therefore
  carries `∀ x, 0 < lam x`. Carrying the absorbing case means giving the jump
  times values in `ℝ≥0∞`; the bounded case does not need it, since `lam` bounded
  away from `0` and from `∞` is exactly the hypothesis of
  `jumpProcess_isMPSolution`, and the local case does.
* `jumpTimeE`, `jumpProcessE`: the same construction with jump times in `ℝ≥0∞`,
  where `a / 0 = ⊤` for `a ≠ 0` (`ENNReal.div_zero`) is already the intended
  convention, so that an absorbing state has an infinite holding time and the
  step index stops advancing of its own accord. **Proved** on 2026-09-10,
  seventh run, in forty two declarations. `jumpProcessE_of_absorbing` says the
  path stays at `y n` for all time once `lam (y n) = 0`,
  `isStepPath_jumpProcessE` and `isCadlagPath_jumpProcessE` give the paths, and
  `jumpProcessE_eq_jumpProcess` says the two constructions agree wherever the
  rate is positive — so this is an extension of the bounded construction and not
  a competitor to it.

  **The witness comes before the theorem, and it is sharper than "unproved".**
  `jumpProcess_absorbing_const` exhibits `E = Bool` with `lam false = 0`,
  `lam true = 1`, a chain absorbed at `false` from index `1` and waiting times
  all equal to `1`, and proves that the path of `jumpProcess` on that data is
  **constantly `true`**: it never takes the absorbing value at any time
  whatever. The reason is that `T n = 1` for every `n ≥ 1`, so past the radius
  `1` the set `{n | t < T (n+1)}` is empty and `sInf ∅ = 0` returns the junk
  index. **For the real valued jump times the absorbing state and the explosion
  set are the same event**, and the junk value that is harmless on a null set is
  the answer to every question on the other.

  **`StrictMono` is not merely unproved in the local case but false**, since
  after absorption every jump time is `⊤`. What the proof of
  `isStepPath_stepPath` actually used is downward propagation of strictness,
  `T (n+1) < T (n+2) → T n < T (n+1)`, and in `ℝ≥0∞` that is free:
  `T (n+1) < T (n+2)` forces `T (n+1) ≠ ⊤`, hence `T n ≠ ⊤`, hence
  `lt_jumpTimeE_succ`. `isStepPath_stepPath_ofReal` carries that hypothesis, and
  it asks for non explosion at **real** times only — at `⊤` it is false as soon
  as the path is absorbed, which is the whole purpose of the construction.
  `stepIndex` and `stepPath` are stated over an arbitrary
  `ConditionallyCompleteLinearOrder` for exactly this reason, and
  `exists_stepIndex_window` asks for non explosion at the single point it is
  applied to.
* `measurable_stepIndex_comp`, `measurable_stepPath_comp`: the step index and
  the step path are measurable over an arbitrary measurable ordered time axis
  and along an arbitrary measurable time map `u`. **Proved** on 2026-09-10,
  eighth run. The time map is carried rather than eliminated, and that is what
  makes the statement reach the local construction: there the jump times live in
  `ℝ≥0∞` while the process is read at real times, so `u` is
  `ENNReal.ofReal ∘ Prod.fst`. Joint measurability in `(t, ω)` is the case
  `γ = ℝ × Ω`, `u = Prod.fst`, and `measurable_stepIndex`, `measurable_stepPath`
  are that corollary. The proof is `stepIndex_eq_iff` and nothing else: a
  description of the preimage of `{n}`, with no limit.
* `measurable_jumpTimeE`, `measurable_jumpProcessE`,
  `measurable_jumpProcessE_apply`: the local construction is a process and not
  merely a family of maps. **Proved** on 2026-09-10, eighth run. Without joint
  measurability in `(t, ω)` no integral over the local process is defined and no
  statement of Milestone 2 can be written down for it.
* `jumpTimeE_eq_sum`, `NonExplosiveE`, `mem_nonExplosiveE_iff_tsum_eq_top`: **non
  explosion of the local construction is a single series identity in `ℝ≥0∞`**,
  `∑' k, ENNReal.ofReal (ξ k) / ENNReal.ofReal (lam (y k)) = ⊤`, with no
  hypothesis whatever on the rate or on the waiting times. **Proved** on
  2026-09-10, eighth run, together with `measurableSet_nonExplosiveE` and
  `mem_nonExplosiveE_iff_of_pos`, which says the condition is the same one
  `NonExplosive` states wherever both constructions are the same process.

  This is more than a convenience. In `ℝ` the two ways a path can fail to
  explode — the holding times summing to `∞`, and a state the path never leaves
  — are different conditions and need a case distinction at every use. In
  `ℝ≥0∞` they are the same condition: an absorbing state contributes a single
  term equal to `⊤`, and `⊤` is how a divergent series of nonnegative terms is
  recorded. Every criterion for non explosion therefore has one form, and the
  probabilistic content of the local case is the single question when this
  series diverges.
* `mem_nonExplosiveE_of_rate_zero`, `mem_nonExplosiveE_of_traj`: the two
  deterministic criteria. **Proved** on 2026-09-10, eighth run, with
  `jumpTime_nonneg_of_traj`, `jumpTimeE_eq_ofReal_of_traj` and
  `sum_div_le_jumpTime_of_traj`. The first is absorption, one term equal to `⊤`.
  The second bounds the rate **along the trajectory** and not on all of `E`, and
  that weakening is what the local case needs rather than a tidiness: a locally
  bounded rate is by definition unbounded on `E`, so the uniform hypothesis of
  `tendsto_jumpTime_atTop` is unavailable, while the trajectory bound is exactly
  what a criterion has to deliver. The jump times of one sample point read the
  rate at the states that sample point visits and nowhere else.
* `ae_tendsto_sum_smul_waiting_atTop`: for `c : ℕ → ℝ` with `0 ≤ c n` and `c` not
  summable, `waitingMeasure`-almost every `ξ` has
  `Tendsto (fun N ↦ ∑ n ∈ Finset.range N, c n * ξ n) atTop atTop`. This is the
  probabilistic core of the local case, and it is what turns
  `mem_nonExplosiveE_iff_tsum_eq_top` into a criterion on the chain alone: by
  Fubini on `jumpMeasure mu nu = (chainKernel mu ∘ₘ nu).prod waitingMeasure` the
  chain is frozen first, and what remains is this statement with
  `c n = (lam (y n))⁻¹`. `tendsto_sum_waiting_atTop` is the case `c ≡ 1`, and it
  does not generalise: its proof is that a summable sequence tends to `0` while
  infinitely many `ξ n` exceed `1`, and the events `{c n · ξ n > ε}` are
  summable as soon as `c n → 0`, so the second Borel--Cantelli lemma alone does
  not reach it. Divergence here comes from accumulation and not from single
  large terms. The route is Chebyshev on the truncation `b n = min (c n) 1`:
  `¬ Summable b` follows from `¬ Summable c`, and with
  `X n = (Set.Ioi 1).indicator 1 ∘ eval n` the partial sums
  `Y N = ∑ n < N, b n * X n` have mean `exp (-1) · B N` and variance at most
  `B N / 4`, where `B N = ∑ n < N, b n → ∞`, so
  `ProbabilityTheory.meas_ge_le_variance_div_sq`
  (`Probability/Moments/Variance.lean:397`) gives
  `P (Y N < exp (-1) · B N / 2) ≤ 1 / (exp (-1) ^ 2 · B N) → 0`;
  `c n * ξ n ≥ b n * X n ξ` pointwise on
  `{∀ n, 0 ≤ ξ n}`, and the partial sums are monotone. The independence enters
  as `ProbabilityTheory.IndepFun.variance_sum` (`:422`) on the indicators, and
  that is `iIndepFun` of the coordinates, which
  `ProbabilityTheory.iIndepFun_infinitePi`
  (`Independence/InfinitePi.lean:127`) supplies at the identity.

  Its two ends are not probabilistic and are **proved** on 2026-09-10, eighth
  run. `not_summable_min_one` says the truncation preserves divergence, and it
  carries no sign hypothesis: `Summable (min c 1)` forces `min (c n) 1 < 1`
  eventually, hence `c n = min (c n) 1` eventually. `ae_tendsto_atTop_of_monotone`
  is the assembly, and the reason it is not immediate is the order of the
  quantifiers — Chebyshev gives one level at a time a set of full measure, while
  divergence asks for one set serving all levels; countably many levels suffice
  because the reals are archimedean.

  **Proved** on 2026-09-10, ninth run, together with its whole middle:
  `iIndepFun_waiting`, the indicator `waitBig` with its bounds and its mean
  `integral_waitBig`, the three inputs of Chebyshev (`memLp_mul_waitBig`,
  `integral_sum_waitBig`, `variance_sum_waitBig_le`) and the estimate
  `measure_sum_waitBig_lt_le`.

  **The truncation is not a convenience of the variance bound, it is the
  argument.** Integrability needs no upper bound on `b n` — a weighted indicator
  is bounded by its weight — and `b n ≤ 1` is spent at exactly one place,
  `b n ^ 2 ≤ b n` in `variance_sum_waitBig_le`. Without it the bound would read
  `∑ b n ^ 2`, which can converge while `∑ b n` diverges (`c n = 1 / n`), and the
  estimate would say nothing.

  **The route to the independence was shorter than announced, and the earlier
  negative finding is one directional.** `iIndepSet.iIndepFun_indicator` is not
  needed: `iIndepFun_infinitePi` at the identity *is* the independence of the
  coordinates as functions. What Mathlib lacks — the passage from `iIndepFun` of
  the coordinates to `iIndepSet` of events about them, which the second
  Borel--Cantelli lemma at `tendsto_sum_waiting_atTop` wants — is the other
  direction. A negative finding about two notions is a finding about a
  *direction*.
* `ae_mem_nonExplosiveE`: `waitingMeasure`-almost every sample point of a chain
  along which `∑ (lam (y n))⁻¹` diverges is non explosive, and the
  `jumpMeasure`-almost sure form of it. This is
  `ae_tendsto_sum_smul_waiting_atTop` read through
  `mem_nonExplosiveE_iff_tsum_eq_top`, and it is the hypothesis of the local
  branch of Milestone 7. **Proved** on 2026-09-10, ninth run, with the pointwise
  `mem_nonExplosiveE_of_tendsto_sum` below it and
  `ae_mem_nonExplosiveE_jumpMeasure` above it. The last is two lines:
  `MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem`
  (`MeasureTheory/Measure/Prod.lean:449`) splits the almost sure statement over
  `(chainKernel mu ∘ₘ nu).prod waitingMeasure` into one about the chain and one
  about the waiting times, and its only hypothesis is that `NonExplosiveE lam`
  be measurable.

  **It is strictly weaker than `mem_nonExplosiveE_of_traj`**, and the gap is the
  case the local branch exists for: the linear birth and death chain has
  `lam (y k) = β · k`, unbounded along *every* trajectory, so no bound `L` is
  available, while `∑ 1 / (β k)` diverges all the same.
* `tendsto_sum_waiting_atTop`: the partial sums of the waiting times diverge
  `waitingMeasure`-almost surely. **Proved** on 2026-09-09, eighteenth run,
  together with `ae_pos_waiting`, `frequently_one_lt_waiting`,
  `iIndepSet_waiting`, `waitingMeasure_eval_preimage`, `expMeasure_one_Iic_zero`
  and `expMeasure_one_Ioi_one_ne_zero`. This is the one probabilistic input the
  path statements above take as a hypothesis, and it is what makes
  `isCadlagPath_jumpProcess` an almost sure statement about `jumpMeasure mu nu`
  rather than a conditional one. It is the second Borel--Cantelli lemma,
  `ProbabilityTheory.measure_limsup_eq_one`
  (`Mathlib/Probability/BorelCantelli.lean:69`), on the independent events
  `{ξ n > 1}`, whose common probability `expMeasure 1 (Set.Ioi 1) = exp (-1)` is
  positive — `expMeasure_one_Ioi_one_ne_zero` states the positivity alone, which
  is all `ENNReal.tsum_const_eq_top_of_ne_zero` consumes. Together with `∀ n, 0 < ξ n` almost surely — the exponential law has
  no atom at `0`, which is `cdf_expMeasure_eq` at `0` — it discharges both
  hypotheses of `isStepPath_jumpProcess` at once.

  **The independence is the product formula and not the independence API.** The
  route through `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map`
  (`Independence/InfinitePi.lean:103`) is a detour: it produces `iIndepFun` of
  the coordinates, from which `iIndepSet` of the events `{ξ n > 1}` still has to
  be extracted, and Mathlib has no lemma in that direction. What
  `measure_limsup_eq_one` wants is `iIndepSet`, and
  `ProbabilityTheory.iIndepSet_iff_meas_biInter`
  (`Independence/Basic.lean:623`) says it *is* the product formula for finite
  intersections — which for coordinate events is `Set.pi` and therefore
  `MeasureTheory.Measure.infinitePi_pi` (`Probability/ProductMeasure.lean:405`)
  in one step. The general lesson is the file's own: ask for the statement the
  consumer needs, not for the named concept nearest to it.
* `ae_isStepPath_jumpProcess`, `ae_isCadlagPath_jumpProcess`: the two path
  statements of the previous item with their hypotheses discharged, so that they
  hold for `jumpMeasure mu nu`-almost every `ω` under `0 < lam ≤ L` alone.
  **Proved** in the same run, over `jumpMeasure_map_snd`: the waiting times are
  the second marginal of a product measure, so `MeasureTheory.ae_of_ae_map`
  carries every almost sure statement about `waitingMeasure` to the sample
  space.
* `expMeasure_Ioi`, `expMeasure_Ioi_add`: the tail `exp (-(r * x))` of the
  exponential law and its memorylessness. **Proved** on 2026-09-09, eighteenth
  run. Mathlib has the distribution function (`cdf_expMeasure_eq`) and neither of
  these, in v4.33.1 nor on `upstream/master`; a search for `memoryless` over
  `Mathlib/` returns nothing. This is the one distributional property of the
  waiting times that the martingale property below rests on, and it is the reason
  the holding time at a state can be given by a rate rather than by a clock.
* `jumpProcess_zero`, `jumpMeasure_map_jumpProcess_zero`: the *process* starts
  with law `nu`, and not merely the chain that drives it.
  **Proved** on 2026-09-09, eighteenth run. The zeroth window contains `0` as
  soon as the first holding time is positive, so the two statements differ by an
  almost sure equality and `Measure.map_congr`.
* `lebesgueClock : Clock ℝ≥0`: the clock of the jump martingale problem.
  **Proved** on 2026-09-09, eighteenth run. **The index is `ℝ≥0` and not `ℝ`**,
  because `mpFamily` needs `[OrderBot ι]`, and the process of the martingale
  problem is therefore `fun t ω ↦ jumpProcess lam (t : ℝ) ω`. `ℝ≥0` has a
  `MeasurableSpace` instance
  (`MeasureTheory/Constructions/BorelSpace/Basic.lean:717`) but **no**
  `MeasureSpace` instance and hence no `volume`; Mathlib gives subtypes their
  measure through `MeasureTheory.Measure.Subtype.measureSpace`, which is
  deliberately not an instance (`MeasureTheory/Measure/Restrict.lean:843`). That
  costs nothing, because `Clock` carries its measurable space and its measure as
  *fields*, which is what that design decision was for: the clock is
  `((volume : Measure ℝ).restrict (Set.Ici 0)).map Real.toNNReal`.
* `jumpOperator lam mu = {p | Measurable p.1 ∧ (∃ C, ∀ x, |p.1 x| ≤ C) ∧`
  `p.2 = jumpApply lam mu p.1}`: the generator as a *set of pairs*, which is the
  shape `mpFamily` consumes. **Defined** on 2026-09-09, nineteenth run, together
  with `mem_jumpOperator` and `measurable_jumpApply`. Boundedness and
  measurability are carried by the members and not by an ambient hypothesis,
  because `mpFamily` quantifies over `p ∈ A` and every statement about a member
  has to be able to reproduce them.
* `naturalFiltration X hX`: the natural filtration of a measurable process,
  **without a topology on the state space**. **Defined** on 2026-09-09,
  nineteenth run, with `measurable_naturalFiltration`. Mathlib's
  `MeasureTheory.Filtration.natural` (`Probability/Process/Filtration.lean:395`)
  is the same σ-algebra, but it carries
  `[TopologicalSpace (β i)] [MetrizableSpace (β i)] [BorelSpace (β i)]`, so over
  a bare `[MeasurableSpace E]` it cannot even be *stated*. None of that is used:
  the field `le'` needs each `u i` to be measurable and nothing more.
  `jumpFiltration lam hlam : Filtration ℝ≥0 _` is its instance at the jump
  process.
* `eventuallyEq_nhdsGE_stepPath`: **the step path is right continuous at every
  time, for every sequence of jump times** — neither monotonicity nor non
  explosion. **Proved** on 2026-09-09, nineteenth run. The hypothesis-free form
  is not generality for its own sake: `MeasureTheory.Martingale` asks for
  `StronglyAdapted`, which is not an almost sure notion, so the measurability of
  the compensator has to hold at *every* sample point — the explosion set is a
  null set but not the empty set, and `ae_isStepPath_jumpProcess` is therefore
  of no use there. If some window contains `t` then the least such window is a
  right neighbourhood of `t` on which the index is constant; if none does, the
  index is the junk value `0` at `t` and at every later time as well.
* `measurable_uncurry_min_of_rightContinuous`: **a right continuous real process is
  jointly measurable in `(t, ω)` for the σ-algebra of the past.** **Proved** on
  2026-09-09, nineteenth run, with `dyadicUp`, `le_dyadicUp`, `dyadicUp_le_add`,
  `tendsto_dyadicUp` and `eventuallyEq_nhdsGE_comp_max`; the instances for the
  jump process are `measurable_uncurry_jumpProcess` and
  `measurable_compensator`.

  The hypothesis is a **convergence** and not an eventual equality, and the
  difference is not cosmetic: the state process is locally constant from the
  right, but the *compensator* is continuous in `t` and therefore constant on no
  interval, so the locally constant form does not reach the test process
  `Y t = h (X t) − ∫₀ᵗ (A h)(X s) ds` as a whole. `measurable_uncurry_min_of_eventuallyEq`
  is the locally constant case and is a three line corollary; the hypothesis was
  used at exactly one place in the proof, to turn `tendsto_dyadicUp` into an
  eventual equality, and a convergence does the same work there.
* `isStronglyProgressive_of_measurable_uncurry_min`: the bridge from the
  statement above to Mathlib's `MeasureTheory.IsStronglyProgressive`, which asks
  for strong measurability on `Set.Iic i × Ω` where the dyadic argument gives
  measurability on `ℝ≥0 × Ω` for the process cut down at `i`.
* `continuous_intervalIntegral_of_bounded`: the primitive of a bounded measurable
  real function is continuous, through `intervalIntegral.continuous_primitive`.
  This is the right continuity of the compensator and the only place a hypothesis
  on the integrand is spent.

  **This is not `Clock.IsProgressive` for the jump process, and the difference
  is a theorem that is false rather than a convenience.** The argument
  approximates `X s` by `X r` with `r` slightly above `s` and passes to the
  limit. A limit of **`E` valued** measurable maps is measurable only when the
  diagonal of `E` is a measurable set, which for an arbitrary σ-algebra it is
  not; so the `E` valued joint measurability is not available over a bare
  `[MeasurableSpace E]`. Every **real** functional `h ∘ X` of the process is
  jointly measurable, by the same argument run in `ℝ`, and the compensator of
  `mpFamily` is such a functional. Whoever wants
  `isMPSolution_iff_forall_fdd` at the jump process must first weaken its
  `Clock.IsProgressive` hypothesis to this shape;
  `mpFamily_sub_of_measurable_path` already takes `g ∘ X` and not `X`.
  The approximation uses `Int.floor` and not `Nat.floor`, because a negative
  time has to be approximated too, and `Nat.floor` sends every negative number
  to `0`.
* `stronglyAdapted_mpFamily_jumpProcess`: the test processes of the jump
  martingale problem are adapted to the natural filtration of the jump process.
  **Proved** on 2026-09-09, nineteenth run. This is the first of the two
  conjuncts of `MeasureTheory.Martingale`, and the one that does not mention the
  measure.
* `jumpMeasure_integral_eq_of_firstJump`: the first jump decomposition
  `E[h (X t)] = ∫ e^{-lam z * t} h z dnu + E[h (X t) ; T 1 ≤ t]`, the renewal
  equation before the Markov property is used on its second term. **Proved** on
  2026-09-09, twentieth run, for a general initial law and over
  `[MeasurableSpace E]` alone.
* `jumpShift`, `jumpTime_jumpShift`, `stepIndex_shift`, `jumpProcess_jumpShift`:
  the shift at the first jump, pathwise. On `{T 1 ≤ t}` and at a time the path
  reaches, `jumpProcess lam t ω = jumpProcess lam (t - T 1) (jumpShift ω)`.
  **Proved** on 2026-09-09, twenty first run. Both hypotheses of
  `stepIndex_shift` are needed: on the explosion set the two sides are the junk
  values `0` and `0 + 1`, so the identity is false there.
* `waitingMeasure_map_shift`: the law of the waiting times is invariant under
  the shift. **Proved** on 2026-09-09, twenty first run, from
  `Measure.eq_infinitePi` on boxes.
* `chainFam`, `shiftIic`, `piSingleton_apply_const`,
  `partialTraj_succ_map_shiftIic`, `partialTraj_map_shiftIic`,
  `ext_of_map_frestrictLe`, `traj_map_shift`, `chainKernel_map_shift`: the
  **Markov property of the embedded chain**,
  `(chainKernel mu z).map (· ∘ Nat.succ) = chainKernel mu ∘ₘ mu z`.
  **Proved** on 2026-09-09, twenty first run.
  `ProbabilityTheory.Kernel.traj` is built for an arbitrary family of kernels
  and therefore carries no time homogeneity; neither v4.33.1 nor
  `upstream/master` has any statement saying that shifting a trajectory of a
  homogeneous chain gives a trajectory of the same chain. The proof runs over
  the finite dimensional distributions: the whole of the homogeneity is the one
  step `partialTraj_succ_map_shiftIic`, where
  `chainFam mu b (shiftIic b w) = chainFam mu (b + 1) w` holds by `rfl`, and the
  passage from `partialTraj` to `traj` is the uniqueness of the projective
  limit.
* `map_prodMk_of_map_eq_dirac`: if one marginal of a probability measure is a
  Dirac measure, the joint law is the product of that Dirac measure and the
  other marginal. **Proved** on 2026-09-09, twenty second run. Over a bare
  `[MeasurableSpace E]` this cannot be had from `f =ᵐ[μ] z`, which needs `{z}`
  to be measurable; the proof works on measurable rectangles and uses only
  `μ (f ⁻¹' s) ∈ {0, 1}`.
* `natCons`, `measurable_natCons`, `infinitePi_map_natCons`,
  `infinitePi_map_split`: **the zeroth coordinate of an infinite product over
  `ℕ` is independent of its tail**,
  `(infinitePi μ).map (fun x ↦ (x 0, x ∘ Nat.succ)) = μ.prod (infinitePi μ)`.
  **Proved** on 2026-09-09, twenty second run. Mathlib has the reindexings along
  injections (`Measure.map_infinitePi_infinitePi_of_inj`), the law of a pair of
  coordinates (`Measure.infinitePi_map_eval_prod`) and the independence of the
  coordinates (`iIndepFun_infinitePi`), but `iIndepFun.indepFun_finset` splits
  only two *finite* index sets, so none of them separates a coordinate from an
  infinite tail. The proof goes in the composing direction, where the statement
  is one about boxes and `Measure.eq_infinitePi` applies: the preimage of a box
  under `natCons` is again a rectangle.
* `chainKernel_map_split`, `comp_chainKernel_map_split`,
  `waitingMeasure_map_split`, `jumpMeasure_map_split`,
  `prod_comp_chainKernel_eq_jumpMeasure`, `jumpShift_eq_split`: **the splitting
  of the driving data at the first jump**,
  ```
  (jumpMeasure mu nu).map (fun ω ↦ ((ω.1 0, ω.1 ∘ succ), (ω.2 0, ω.2 ∘ succ)))
    = (nu ⊗ₘ (chainKernel mu ∘ₖ mu)).prod ((expMeasure 1).prod waitingMeasure),
  ```
  with `((chainKernel mu ∘ₖ mu) z).prod waitingMeasure = jumpMeasure mu (mu z)`.
  **Proved** on 2026-09-09, twenty second run. The initial state has law `nu`,
  the zeroth waiting time is an independent standard exponential — together they
  carry the first jump time `T 1 = ξ 0 / lam (y 0)` — and given the initial
  state the shifted data is again a jump construction, started from one step of
  `mu`. The two shift statements alone do not give this: what the renewal
  equation reads is the *joint* law of `y 0` and `y ∘ succ`, and marginals do
  not determine it. The statement is in the unordered form, on
  `(E × (ℕ → E)) × (ℝ × (ℕ → ℝ))`; collapsing the four integrals to
  `∫ nu, ∫ expMeasure 1, ∫ jumpMeasure mu (mu z)` interchanges `y ∘ succ` with
  `ξ 0` once by Fubini.
* `integrable_of_abs_le`, `abs_integral_le_of_abs_le`,
  `integral_jumpMeasure_eq_of_split`: **the restart at the first jump as an
  integral identity**. For `G` bounded measurable,
  ```
  ∫ G ((ω.1 0, ω.2 0), jumpShift ω) d(jumpMeasure mu nu)
    = ∫ nu, ∫ expMeasure 1, ∫ jumpMeasure mu (mu z), G ((z, s), ω').
  ```
  **Proved** on 2026-09-09, twenty third run. This is the Fubini interchange the
  previous item names, performed once and for all, and it is what makes
  `jumpMeasure_map_split` usable: the bundling of the two tails
  `y ∘ succ` and `ξ ∘ succ` into a single point of `(ℕ → E) × (ℕ → ℝ)` — so that
  `prod_comp_chainKernel_eq_jumpMeasure` can recognise their law as a jump
  construction again — *is* the interchange of `y ∘ succ` with `ξ 0`. A single
  constant bound supplies the integrability of all five nested integrals, through
  the two tools; the swap itself is `MeasureTheory.integral_integral_swap` and the
  separation of `nu` from the shifted chain is `Measure.integral_compProd`.
* `expMeasure_eq_withDensity`, `toReal_exponentialPDF_one`,
  `integral_expMeasure_one`: **integration against the standard exponential law is
  integration of `exp (-s) * ·` over `Set.Ioi 0`**. **Proved** on 2026-09-09,
  twenty third run, with **no** hypothesis on the integrand: the identity is the
  definition of `expMeasure` as a density, and both sides are the same junk value
  when the integrand fails to be integrable. Mathlib has the distribution
  function of `expMeasure` (`cdf_expMeasure_eq`) but no statement of this shape,
  and it is the step that turns the renewal equation into a statement about an
  integral in the *time* variable against Lebesgue measure, which is what the
  differentiation of the backward equation acts on.
* `ae_exists_lt_jumpTime`: almost surely the jump times exhaust the half line.
  **Proved** on 2026-09-09, twenty third run. This is non explosion in the form
  `jumpProcess_jumpShift` asks for, and unlike `ae_isStepPath_jumpProcess` it
  carries **no topology on `E`**: the statement is about the jump times alone, and
  `tendsto_jumpTime_atTop` never looks at the state space.
* `jumpMeasure_integral_eq_renewal`: **the renewal equation**,
  ```
  ∫ h (X t) d(jumpMeasure mu nu)
    = ∫ nu, e^{-(lam z * t)} * h z
      + ∫ nu, ∫_{Ioc 0 (lam z * t)} e^{-s} * ∫ h (X (t - s / lam z)) d(jumpMeasure mu (mu z)) ds.
  ```
  **Proved** on 2026-09-09, twenty third run, for `h` bounded measurable, `lam`
  measurable with `0 < lam ≤ L`, and `0 ≤ t`. It is the last purely measure
  theoretic step of `thm:jumpMP`: on `{T 1 > t}` the path has not moved and the
  factor is the exponential tail; on `{T 1 ≤ t}` the process restarts from a
  state drawn by `mu` after a holding time `s / lam z`. Both halves stand as
  integrals against `nu` rather than combined under one, exactly as
  `jumpMeasure_integral_eq_of_firstJump` states them.
* `abs_integral_jumpProcess_sub_le`: for `h` bounded by `C` and `0 < lam ≤ L`,
  ```
  |∫ h (X t) d(jumpMeasure mu nu) − ∫ h dnu| ≤ 2 * C * L * t   for 0 ≤ t.
  ```
  **Proved** on 2026-09-09, twenty fourth run. The state can only have moved if
  the first jump has happened, and `measureReal_jumpTime_one_le` prices that at
  `L * t`; the two terms of the first jump decomposition each pay it once. The
  constant does not mention `nu`, and that is what lets the statement be applied
  to the **restarted** law `mu z` inside the proof of the estimate below.
* `abs_integral_jumpProcess_sub_sub_le`: **the backward equation at second
  order**, for `h` bounded by `C`, `0 < lam ≤ L`, `0 ≤ t` and `L * t ≤ 1`,
  ```
  |∫ h (X t) d(jumpMeasure mu nu) − ∫ h dnu − t * ∫ A h dnu| ≤ 4 * C * L ^ 2 * t ^ 2.
  ```
  **Proved** on 2026-09-09, twenty fourth run. It is a quantitative statement and
  not a limit, and its constant mentions only `C` and `L`.
* `jumpMeasure_hasDerivWithinAt_integral`: **the backward equation in
  differential form at time zero**,
  ```
  HasDerivWithinAt (fun t ↦ ∫ h (X t) d(jumpMeasure mu nu)) (∫ A h dnu) (Set.Ici 0) 0.
  ```
  **Proved** on 2026-09-09, twenty fourth run, from the estimate above.
* `integral_jumpProcess_of_nonpos` and
  `eq_zero_of_hasDerivAt_integral_jumpProcess`: **the derivative is one sided of
  necessity.** Before the first jump the path sits at its initial state, so
  `t ↦ ∫ h (X t) d(jumpMeasure mu nu)` is constant on `Set.Iic 0` and its left
  derivative at `0` is `0`; a two sided `HasDerivAt` at `0` therefore forces
  `∫ A h dnu = 0`. Both **proved** on 2026-09-09, twenty fourth run. Nothing is
  lost by this: the martingale problem of the jump process is indexed by `ℝ≥0`,
  because `mpFamily` needs `[OrderBot ι]`.
* `expMeasure_one_real_Iic`: `(expMeasure 1).real (Set.Iic a) = 1 − exp (−a)` for
  `0 ≤ a`. **Proved** on 2026-09-09, twenty fourth run. Mathlib has the
  distribution function of `expMeasure` in `ℝ≥0∞` (`cdf_expMeasure_eq`) but not
  in `ℝ`, and every weight of the first jump decomposition is a real number.
* `jumpProcess_isMPSolution`: for `lam` bounded, `jumpProcess lam mu nu` solves
  the martingale problem for `(A, nu)` with respect to its natural filtration.
  This is `IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock`
  `Clock.Conv.optional (fun t ω ↦ jumpProcess lam (t : ℝ) ω))`
  `(jumpFiltration lam hlam) (jumpMeasure mu nu)`, **proved** on 2026-09-10,
  third run; it is the first solution of a martingale problem in this file that
  is a solution and not a counterexample. It was stated on 2026-09-09,
  nineteenth run, with its adaptedness half proved, and the conditional
  expectation `P[Y t | 𝓕 s] =ᵐ Y s` took the eight runs between. Of its three
  steps the first is
  the Markov property of the process at a fixed time,
  `jumpMeasure_integral_eq_of_firstJump` together with `jumpProcess_jumpShift`
  and `jumpMeasure_map_split`, complete on 2026-09-09, twenty second run, and
  assembled into `jumpMeasure_integral_eq_renewal` on the twenty third. What
  remains is the expectation identity
  `E_x[f (X t)] - f x = ∫_0^t E_x[A f (X s)] ds`, which is the backward
  equation and the only step needing analysis beyond bookkeeping. Its value at
  `t = 0` is `jumpMeasure_hasDerivWithinAt_integral`, proved on 2026-09-09,
  twenty fourth run, and the time homogeneous Markov property that moves the
  derivative from `0` to every `s` is `jumpMeasure_integral_jumpProcess_add`,
  proved on 2026-09-09, twenty sixth run. The identity itself follows from them
  and is `jumpMeasure_integral_sub_eq_intervalIntegral`, proved in the same run.
  Its conditional form on a set of the past is
  `setIntegral_jumpProcess_sub_eq_intervalIntegral` (2026-09-10, first run), and
  the matching identity for the compensator term is
  `setIntegral_compensator_sub_eq_intervalIntegral` (2026-09-10, second run);
  the two have the **same** interval integral on the right, so the increment of
  `Y` integrates to zero over every set of the past and
  `ae_eq_condExp_of_forall_setIntegral_eq` names that the conditional
  expectation.

  **Two hypotheses of the assembly are supplied inside the proof and are not in
  the statement.** The set of the past is cut down to `NonExplosive lam ∩ S`,
  because `isPastFunctional_indicator` produces a functional of the past only
  after that cut; the cut changes no integral (`indicator_nonExplosive_ae_eq`),
  and `Measure.restrict_congr_set` carries the result back to `S`. And `0 < L`
  is **derived, not assumed**: `nu` is a probability measure, so `E` is nonempty
  — were it empty, `nu Set.univ` would be both `0` and `1` — and `0 < lam x ≤ L`
  at any of its points. Adding `0 < L` to the statement would have been a
  hypothesis that no instance has to check separately, and that is the reason it
  is not there.

  The integrability that `ae_eq_condExp_of_forall_setIntegral_eq` asks of the
  later time is `integrable_mpFamily_jumpProcess`, with the explicit bound
  `|Y t ω| ≤ C + 2 L C · t`: `C` from the member of the operator, `2 L C` from
  `abs_jumpApply_le`, and the factor `t` from
  `abs_setIntegral_compensator_le`, which is the exact mass
  `lebesgueClock_apply_Ioc` of the compensating window and not a mere finiteness
  bound. The bound grows with `t` and that is harmless: a martingale needs
  finiteness at each `t`, not uniformity.

  **The Markov property is a statement about the initial *state* and not about an
  initial law, and that is why `jumpKernel` exists.** The form announced on
  2026-09-09, twenty fourth run,
  ```
  ∫ h (X (s + t)) d(jumpMeasure mu nu)
    = ∫ h (X t) d(jumpMeasure mu ((jumpMeasure mu nu).map (jumpProcess lam s)))
  ```
  is true, but it is a *corollary* and not a usable primitive: its right hand
  side names a measure that is not the composition of anything with anything, so
  the identity cannot be applied to itself, and an induction over the number of
  jumps -- which is what carries the proof -- has nothing to induct on. The
  primitive is the semigroup identity `P (s + t) h = P s (P t h)` at a fixed
  initial state,
  ```
  ∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpKernel mu z)
    = ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpKernel mu z),
  ```
  and the announced form follows from it by `integral_jumpSemigroup_eq`.
* `IsPastFunctional lam s G`: **what a functional of the past is allowed to
  depend on**, and the property the induction of the *conditional* Markov
  property carries. **Proved** on 2026-09-09, twenty seventh run, in twenty five
  declarations of `Suggested.lean`.

  Two of them are about a natural filtration and nothing else.
  `eq_of_measurable_naturalFiltration` says that a `𝓕 s`-measurable real function
  takes the same value at two sample points whose coordinates agree below `s`,
  and `measurable_comp_of_measurable_naturalFiltration` says that composing such
  a function with a substitution that carries every coordinate below `s` into a
  σ-algebra `n` lands in `n`. **Neither needs a factorisation theorem**, and none
  is available: Doob--Dynkin factors through *one* comap, while `𝓕 s` is a
  supremum of comaps, and over a bare `[MeasurableSpace F]` nothing turns the
  supremum into the comap of a joint map. The proof of the first is that the sets
  which fail to separate a *fixed* pair form a σ-algebra; the proof of the second
  is `MeasurableSpace.comap_iSup` and `MeasurableSpace.comap_comp`.

  The rest is the two substitutions. `jumpConst lam s x = (fun _ ↦ x,`
  `fun _ ↦ lam x * s + 1)` is the datum that sits at `x` and whose first jump is
  at `s + 1 / lam x`, hence after `s`; `jumpPrepend x a ω` puts a state and a
  waiting time in front of `ω` and is the inverse of `jumpShift`
  (`jumpShift_jumpPrepend`, `jumpPrepend_self`). With them
  `eq_jumpConst_of_isPastFunctional` says that before the first jump a functional
  of the past **is a function of the initial state**, `G ω = G (jumpConst lam s`
  `(ω.1 0))`, and `IsPastFunctional.comp_jumpPrepend` says that after the first
  jump it **restarts as one**, at the horizon `s - a / lam x`. Those are the two
  branches of the induction, and they are the reason the property is stated as it
  is rather than as `Measurable[jumpFiltration lam hlam s] G`.

  **The definition carries `NonExplosive lam`, and that is forced by a
  counterexample and not by convenience.** `jumpProcess_jumpPrepend` — the
  identity `X r (jumpPrepend x a ω) = X (r - a / lam x) ω` for
  `a / lam x ≤ r`, on which `IsPastFunctional.comp_jumpPrepend` rests — is
  **false** past the explosion time of `ω`: there `stepIndex` is the junk value
  `0`, so the left hand side is `x` and the right hand side is `ω.1 0`. A
  functional of the past defined by measurability alone therefore does *not*
  restart as one. `IsPastFunctional` asks instead that `G` vanish off
  `NonExplosive lam` and be constant on the paths that agree below `s` *within*
  that set; `jumpPrepend_mem_nonExplosive_iff` is what makes the set survive the
  restart, and `indicator_nonExplosive_ae_eq` is what makes the restriction cost
  nothing — `isPastFunctional_indicator` turns any bounded
  `𝓕 s`-measurable `G` into one at the price of a null set. **`StronglyAdapted`
  could not have been treated this way**: it is not an almost sure notion, which
  is why `eventuallyEq_nhdsGE_stepPath` was proved without hypotheses. The
  conditional expectation *is* an almost sure notion, and here the difference
  pays.
* `jumpKernel mu = (chainKernel mu).prod (Kernel.const E waitingMeasure)`: the
  jump construction as a **kernel in the initial state**, with
  `jumpMeasure_eq_comp : jumpMeasure mu nu = jumpKernel mu ∘ₘ nu`. **Proved** on
  2026-09-09, twenty fifth run. It is what makes
  `jumpSemigroup lam mu h t z = ∫ ω, h (jumpProcess lam t ω) ∂(jumpKernel mu z)`
  measurable in `z` (`measurable_jumpSemigroup`) and jointly measurable in
  `(t, z)` (`measurable_uncurry_jumpSemigroup`); over a bare
  `[MeasurableSpace E]` no statement about a fixed initial law delivers that, and
  without it the right hand side of the Markov property cannot even be written
  down.
* `integral_chainKernel_zero_eq` and `integral_jumpKernel_zero_eq`: under
  `jumpKernel mu z` a bounded measurable functional may read `z` in place of
  `ω.1 0`. **Proved** on 2026-09-09, twenty fifth run. The almost sure statement
  `ω.1 0 = z` is *not* available over a bare `[MeasurableSpace E]` -- it needs
  `{z}` measurable -- so the substitution is proved on the splitting of the chain
  at its first step (`chainKernel_map_split`), where only `Measure.dirac z` as a
  factor is used.
* `waitShift a ω = (ω.1, fun n ↦ if n = 0 then ω.2 0 - a else ω.2 n)` and
  `jumpProcess_waitShift`: shortening the zeroth waiting time by `lam (ω.1 0) * s`
  **is** the shift of the time axis by `s`,
  `jumpProcess lam t (waitShift (lam (ω.1 0) * s) ω) = jumpProcess lam (s + t) ω`.
  **Proved** on 2026-09-09, twenty fifth run, and it carries **no hypothesis
  beyond `lam (ω.1 0) ≠ 0`**: no monotonicity of the jump times, no non
  explosion, and no sign of `s`. The reason is that `jumpTime_waitShift` moves
  *every* jump time `T (n+1)` back by exactly `s` and leaves `T 0 = 0` and the
  chain alone, while `stepIndex` reads only the times `T (n+1)`. This is the
  combinatorial half of the restart at a deterministic time, and unlike the
  restart at the first jump (`jumpProcess_jumpShift`, `stepIndex_shift`) it is
  not a reindexing of the driving data but a change of one coordinate.
* `integral_waitingMeasure_waitShift`: for `0 ≤ a` and `F` bounded measurable,
  ```
  ∫ ξ in {ξ | a < ξ 0}, F (fun n ↦ if n = 0 then ξ 0 - a else ξ n) d(waitingMeasure)
    = exp (-a) * ∫ ξ, F ξ d(waitingMeasure).
  ```
  **Proved** on 2026-09-09, twenty fifth run. This is the memorylessness of the
  exponential law in the form the restart needs, and it is **not**
  `expMeasure_Ioi_add`: that identity is a statement about the *sets* `Ioi`, and
  it does not say that the law of the residual waiting time is again exponential
  and still independent of the whole tail. The proof runs on the density
  (`integral_expMeasure_one`) and the translation invariance of Lebesgue measure,
  and it uses `infinitePi_map_natCons` to put the shortened coordinate back in
  front of the untouched tail.
* `integral_jumpKernel_waitShift` and
  `integral_jumpKernel_add_of_lt_jumpTime_one`: the **base case of the Markov
  property at a fixed time**, on the event `{s < T 1}` that the first jump has not
  yet happened. **Proved** on 2026-09-09, twenty fifth run. Both sides of the
  semigroup identity restricted to that event are
  `exp (-(lam z * s)) * jumpSemigroup lam mu h t z`.
* `abs_integral_jumpMeasure_add_sub_le`: the **induction over the number of
  jumps** in `[0, s]`, which carries the base case to the whole space,
  ```
  |∫ h (X (s + t)) d(jumpMeasure mu nu) - ∫ (P t h) (X s) d(jumpMeasure mu nu)|
    ≤ 2 * C * (jumpMeasure mu nu).real {ω | T n ω ≤ s}
  ```
  for every `n` and every initial law `nu`. **Proved** on 2026-09-09, twenty
  sixth run. The initial law is quantified *inside* the statement and not fixed
  as a parameter, because on `{T 1 ≤ s}` the split
  `integral_jumpMeasure_eq_of_split` restarts the construction from `mu z` at
  time `s - σ / lam z`, and that is where the inductive hypothesis is used. The
  two branches differ in kind: on `{s < T 1}` there is no error at all, and on
  `{T 1 ≤ s}` the error is the inherited one. Adding the first jump to the
  further `n` gives `{T 1 ≤ s} ∩ {T (n+1) ≤ s}`, and only its **inclusion** in
  `{T (n+1) ≤ s}` is used: over a bare `[MeasurableSpace E]` the two sets are
  not equal, because `T n ∘ jumpShift` is only almost surely nonnegative.
* `integral_jumpMeasure_eq_of_split_prod`: the splitting with its two outer
  integrals joined into one measure `nu.prod (expMeasure 1)` on `E × ℝ`.
  **Proved** on 2026-09-09, twenty sixth run. The estimate above compares two
  integrals, and the monotonicity of the Bochner integral is a statement about
  **one** measure; the iterated form of `integral_jumpMeasure_eq_of_split` would
  need the measurability of the inner integral in the initial state as a separate
  step at every use. That measurability is
  `measurable_integral_jumpMeasure_step`, and it rests on
  `jumpMeasure_step_eq_comp : jumpMeasure mu (mu z) = (jumpKernel mu ∘ₖ mu) z` --
  over a bare `[MeasurableSpace E]` nothing but the kernel supplies it.
* `tendsto_measureReal_jumpTime_le`: the probability of `n` jumps before a fixed
  time goes to zero. **Proved** on 2026-09-09, twenty sixth run, from non
  explosion (`ae_exists_lt_jumpTime`) and the strict monotonicity of the jump
  times. The family `{T n ≤ s}` is only **almost surely** decreasing, so the
  continuity of the measure from above does not apply and the argument is run on
  the indicators by dominated convergence. No Chernoff bound and no Gamma
  distribution is needed.
* `jumpMeasure_integral_jumpProcess_add`: the **Markov property of the jump
  process at a fixed time**, `P (s + t) h = P s (P t h)` averaged over the
  initial law. **Proved** on 2026-09-09, twenty sixth run, as the two preceding
  items combined. `jumpMeasure_integral_jumpProcess_add'` is the corollary in the
  form announced on the twenty fourth run.
* `jumpMeasure_integral_sub_eq_intervalIntegral`: the **expectation identity**
  `E[h (X t)] - E[h (X 0)] = ∫_0^t E[A h (X r)] dr`. **Proved** on 2026-09-09,
  twenty sixth run. The theorem of the calculus it takes is
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, and that choice is
  forced: `jumpMeasure_hasDerivWithinAt_integral` is one sided by necessity, and
  `eq_zero_of_hasDerivAt_integral_jumpProcess` says that a two sided derivative
  at `0` does not exist. Its three hypotheses are supplied by three statements
  about the construction and by no assumption: the derivative from the right at
  `r` is the derivative at `0` of the construction restarted from the law at time
  `r`, which is `jumpMeasure_integral_jumpProcess_add'` composed with the shift
  `x ↦ x - r`; the continuity on the closed interval is the Lipschitz estimate
  `abs_integral_jumpProcess_sub_le`, read from the law at time `a` instead of
  from `nu`; and the integrability of the compensator is `abs_jumpApply_le`
  together with the joint measurability of `(r, ω) ↦ jumpProcess lam r ω`.
* `abs_integral_jumpMeasure_add_sub_le_past` and
  `jumpMeasure_integral_jumpProcess_add_past`: the **Markov property tested
  against the past**,
  ```
  ∫ G · h (X (s + t)) d(jumpMeasure mu nu) = ∫ G · (P t h) (X s) d(jumpMeasure mu nu)
  ```
  for every `G` with `Measurable G`, `|G| ≤ 1` and `IsPastFunctional lam s G`.
  **Proved** on 2026-09-10, first run, as the induction over the number of jumps
  carrying the factor along and its limit. The initial law, the horizon **and the
  functional** are quantified inside the induction, because the branch
  `{T 1 ≤ s}` applies the inductive hypothesis to `mu z`, to `s - σ / lam z` and
  to the restarted functional at once. Two steps are new and both are the two
  theorems of `IsPastFunctional`: on `{s < T 1}` the factor leaves the integral
  because it is a function of the initial state there
  (`eq_jumpConst_of_isPastFunctional`, then `integral_jumpKernel_zero_eq`), and
  on `{T 1 ≤ s}` it restarts as a functional of the past
  (`IsPastFunctional.comp_jumpPrepend`), the identification `G ω = G (jumpPrepend
  (ω.1 0) (ω.2 0) (jumpShift ω))` being `jumpPrepend_self` and hence pointwise.
  The first branch runs under `jumpKernel mu z` and not under `jumpMeasure`, so
  non explosion is needed there in its kernel form
  (`ae_mem_nonExplosive_jumpKernel`, from `jumpKernel_map_snd`): non explosion is
  a statement about the waiting times alone, and they are the second marginal of
  the kernel just as they are of the measure.
* `setIntegral_jumpProcess_sub_eq_intervalIntegral`: the **expectation identity
  tested against a set of the past**,
  ```
  ∫_S h (X (s + t)) dP - ∫_S h (X s) dP = ∫_0^t ∫_S (A h) (X (s + r)) dP dr
  ```
  for every measurable `S` whose indicator is a functional of the past up to `s`.
  **Proved** on 2026-09-10, first run. It is not a new statement about the
  process: with the item above the left hand side is an expectation of the
  semigroup at time `s`, and the semigroup at time `s` is an expectation under
  the construction restarted from the law of `X s` conditioned on `S`, that is
  from `ν = (P S)⁻¹ • ((P.restrict S).map (X s))`; on `ν` the identity is
  literally `jumpMeasure_integral_sub_eq_intervalIntegral`, and the normalising
  factors cancel. The functional is an **indicator** and not a general bounded
  one, because that is what makes `ν` a measure -- for a general one the density
  would need `withDensity`, and a signed one gives no measure at all. The
  conditional expectation asks only for sets, so this costs nothing.
* `jumpApply lam mu f x = lam x * ∫ y, (f y - f x) ∂(mu x)`: the operator `A`,
  **defined** on 2026-09-09, eighteenth run, over `[MeasurableSpace E]` alone.
* `norm_apply_le`: for `lam` bounded by `L`, `‖A f‖ ≤ 2 * L * ‖f‖`, so `A` is a
  bounded linear map on bounded measurable functions. **Proved** on 2026-09-09,
  eighteenth run, as `abs_jumpApply_le`, in the pointwise shape
  `(∀ x, |f x| ≤ C) → |jumpApply lam mu f x| ≤ 2 * L * C`. The pointwise shape is
  deliberate: it needs no normed space of bounded measurable functions, and it
  needs no integrability of `f` either, because
  `MeasureTheory.norm_integral_le_of_norm_le` dominates by a constant, which is
  integrable for a Markov kernel whether `f` is or not. The bundled form is the
  same statement read in `E →ᵇ ℝ` and is what the Picard iteration of the next
  item will take.
* `exists_unique_of_bounded`: for `lam` bounded the martingale problem for
  `(A, nu)` has exactly one solution, and its one dimensional distributions are
  `nu.map (exp (t • A))` given by the exponential series of the bounded operator.
  This is the Picard iteration and needs no analysis beyond `NormedSpace`.
  **The one dimensional half is proved** on 2026-09-10, fourth run, in fourteen
  declarations of `Suggested.lean`, section `Uniqueness`.
  `expJumpApply lam mu t f x = ∑' n, t^n/n! * (A^[n] f) x` is the exponential
  series, defined pointwise and not on a normed space of bounded measurable
  functions -- the same decision as for `abs_jumpApply_le`, and for the same
  reason: `abs_series_term_le` dominates its `n`-th term by
  `(2L|t|)^n/n! * C`, so `Real.summable_pow_div_factorial` gives summability,
  `abs_expJumpApply_le` gives the bound `exp (2L|t|) * C`, and
  `measurable_expJumpApply` gives measurability as a pointwise limit of partial
  sums.  `integral_eq_expJumpApply_of_isMPSolution` is the theorem:
  `∫ f (X t) dP = ∫ expJumpApply lam mu t f d(P.map (X 0))` for **every**
  solution `P`, and `integral_eq_of_isMPSolution_of_map_eq` reads it as
  uniqueness -- two solutions with the same initial law, on two different
  spaces, agree at every time.  The two steps are
  `integral_sub_eq_intervalIntegral_of_isMPSolution`, which turns the martingale
  property into `u_f(t) = ν(f) + ∫_0^t u_{Af}(s) ds` (constant expectation plus
  Fubini), and `abs_integral_sub_sum_le_of_isMPSolution`, which iterates it with
  remainder `(2Lt)^n/n! * C`.  Over `E` nothing is assumed but
  `[MeasurableSpace E]`.

  Two hypotheses on the process, and neither is decoration.  `hX` is the joint
  measurability in `(u, ω)` of the **real functionals** `h ∘ X`, not of `X`
  itself -- the `E` valued form is not available and is not needed, exactly as
  in `measurable_uncurry_jumpProcess`.  `hX0 : Measurable (X 0)` is what turns
  `∫ · (X 0 ω) dP` into an integral against `P.map (X 0)`.

  **The constructed process meets both**, and the law of the construction is
  therefore the series: `jumpMeasure_integral_jumpProcess_eq_expJumpApply`
  (2026-09-10, fifth run) says
  `∫ f (X t) d(jumpMeasure mu nu) = ∫ expJumpApply lam mu t f dnu`, which is the
  clause "its one dimensional distributions are `nu.map (exp (t • A))`" of this
  item, now about a named process.  It costs two lines: the initial law is
  `jumpMeasure_map_jumpProcess_zero`, and `hX` is
  `measurable_uncurry_comp_jumpProcess`, which is `measurable_jumpProcess`
  composed with the coercion `ℝ≥0 → ℝ` -- the uniqueness theorem asks for joint
  measurability for the **full** σ-algebra, and the filtered
  `measurable_uncurry_jumpProcess`, which the compensator consumes, is a
  different and strictly harder statement that is not needed here.

  **The finite dimensional distributions are proved** on 2026-09-10, sixth run,
  in sixteen further declarations, and with them the clause "exactly one
  solution".  The chain is three steps.

  First, `integral_mul_sub_eq_intervalIntegral_of_isMPSolution`: the martingale
  identity tested against a bounded `𝓕 s`-measurable factor `K` and read from an
  arbitrary starting time,
  `∫ K · f(X (s+t)) - ∫ K · f(X s) = ∫_0^t ∫ K · (A f)(X (s+r)) dr`.  Its one
  step that is not bookkeeping is `integral_mul_eq_of_martingale`, which carries
  `K` across a martingale increment through
  `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound` and
  `MeasureTheory.integral_condExp`.

  Second, `abs_sub_sum_le_of_recursion`: the Picard iteration in the abstract,
  over a functional `I : ℝ≥0 → (E → ℝ) → ℝ` with a bound, a joint measurability
  in the time, and that recursion.  Both the unconditional
  `abs_integral_sub_sum_le_of_isMPSolution` (the case `K = 1`, `s = 0`) and the
  conditional `abs_integral_mul_sub_sum_le_of_isMPSolution` are corollaries of
  it, so the induction is written once.  Summing the series gives
  `integral_mul_eq_expJumpApply_of_isMPSolution`:
  `∫ K · f(X (s+t)) dP = ∫ K · (exp (t • A) f)(X s) dP`, which is the Markov
  property of *every* solution.

  Third, the induction over the number of coordinates.  A finite dimensional
  test variable is recorded as a **list of increments**
  `[(t₀, g₀), (t₁, g₁), …]` read from a starting time -- `fddProd` for the
  variable on `Ω`, `fddExp` for the nested semigroup value on `E` -- because
  peeling the first factor leaves a list of the same kind read from the later
  time, whereas a `Fin n`-indexed family would have to reindex at every step.
  `integral_mul_fddProd_eq_of_isMPSolution` is the induction; the peeled factor
  is absorbed into `K`, which is where the conditional form is spent.
  `integral_fddProd_eq_of_isMPSolution` reads it at `K = 1`, `s = 0`, and
  `integral_fddProd_eq_of_isMPSolution_of_map_eq` is uniqueness: two solutions
  with the same initial law, on two different spaces, have the same finite
  dimensional distributions.  `jumpMeasure_integral_fddProd_eq_fddExp` says the
  same of the constructed process against `nu`.

  The induction needs one hypothesis the one dimensional statement did not:
  `hXad`, that every bounded measurable functional of the current state is
  adapted.  It is not decoration -- the peeled factor `g (X (s+t))` has to be
  `𝓕 (s+t)`-measurable for the next step to be a factor of the past at all --
  and `IsMPSolution` does not supply it, since the `StronglyAdapted` it carries
  is about the *compensated* processes.  For the constructed process it is
  `stronglyMeasurable_jumpFiltration`, one line from
  `measurable_naturalFiltration` read at `j = i`.
* `jumpFiltrationE`: the natural filtration of the local process, the
  counterpart of `jumpFiltration`, indexed by `ℝ≥0` so that a localizing
  sequence drawn from `jumpTimeE` needs no coercion — `ℝ≥0∞` *is* `WithTop ℝ≥0`,
  which is where `MeasureTheory.IsStoppingTime` takes its values. **Proved** on
  2026-09-10, tenth run.
* `not_isStoppingTime_min_jumpTimeE`: **the jump times are not stopping times
  for the filtration of the process.** Stated at the first index of the sequence
  `τ n ω = min (jumpTimeE lam ω.1 ω.2 n) n`, under the single hypothesis
  `0 < lam x₀` for one state `x₀`. **Proved** on 2026-09-10, tenth run, together
  with `jumpProcessE_const_chain` and `jumpTimeE_const_chain`.
  The witness is the constant chain at `x₀`
  with the two constant waiting times `lam x₀ / 4` and `lam x₀`: both have
  strictly positive holding times, their paths are equal — both constantly `x₀`
  — and their first jump times, `1/4` and `1`, are separated by the threshold
  `1/2`. The mechanism is `jumpProcessE_const_chain`: `stepPath` reads the chain
  at the step index, so a chain that does not move leaves no trace of the
  waiting times in the path.
* `eq_of_measurable_jumpFiltrationE_const_chain`: two constant chains are
  separated by **no** functional of the process, at **any** time — the hypothesis
  is not `r ≤ s` but nothing at all, the two paths being equal everywhere.
  **Proved** on 2026-09-10, tenth run. This is what forbids the usual repair for
  a debut: the right continuous filtration `⨅ s > t, 𝓕 s` lies below `𝓕 s` for
  every `s > t`, and the statement holds at each of them. The waiting times are
  not late in the path, they are absent from it.
* `eq_of_measurable_jumpFiltrationE_of_subsingleton`: on a one point state space
  no `𝓕 t`-measurable real function separates any two sample points. This is
  what forbids repairing the previous point by completing the filtration or by
  discarding a null set: the failing set is then the whole sample space, while
  the rate `1` there satisfies every hypothesis of `jumpProcess_isMPSolution`.
  `IsStoppingTime` is not an almost sure notion, for the same reason
  `StronglyAdapted` is not. **Proved** on 2026-09-10, tenth run.
* `rateSup`, `rateTime`: the repair, and it is the one Milestone 7 already
  prescribes. **Proved** on 2026-09-10, eleventh run. `rateSup lam t ω` is the
  running supremum
  `⨆ s ∈ Set.Icc 0 t, ENNReal.ofReal (lam (jumpProcessE lam s ω))`, and
  `rateTime lam n ω = ⨅ t : ℝ≥0, ⨅ _ : (n : ℝ≥0∞) ≤ rateSup lam t ω, (t : ℝ≥0∞)`
  — the infimum is taken **in `ℝ≥0∞`** over an index ranging in `ℝ≥0`, so that a
  path whose rate never reaches `n` gets `⊤` and not the junk value `0` that
  `sInf ∅` would give in `ℝ≥0`. These are functionals of the **path**, so they
  are visible to `jumpFiltrationE` (`measurable_rateSup`, `isStoppingTime_rateTime`),
  and `rateTime_le_iff` says `{rateTime lam n ≤ t} = {n ≤ rateSup lam t}`. Both
  properties rest on `eventuallyEq_nhdsGE_jumpProcessE`, right local constancy of
  the path, which carries **no hypothesis at all**: it turns the uncountable
  supremum into a countable one over the rationals of `[0, t]` together with `t`
  itself (`rateSup_eq_sup_rat`), and it makes the running supremum locally
  constant to the right (`eventuallyEq_nhdsGE_rateSup`).
* `isLocalizingSequence_rateTime`: the three fields, under almost sure non
  explosion. **Proved** on 2026-09-10, eleventh run. `isStoppingTime` is the
  previous point; `mono` is `monotone_rateTime`, monotonicity in the **level**;
  `tendsto_top` is non explosion read through `exists_stepIndex_window` — before a
  fixed time the path takes finitely many values, so the running supremum of the
  rate is finite there (`rateSup_lt_top_of_mem_nonExplosiveE`) and every level is
  eventually exceeded (`tendsto_rateTime_atTop`). The hypothesis is
  `∀ᵐ ω ∂P, ω ∈ NonExplosiveE lam` and nothing else, so
  `ae_mem_nonExplosiveE_jumpMeasure` discharges it for the constructed process.
* `eventuallyEq_nhdsGE_stepPath_comp`: a step path is locally constant to the
  right at **every** time, with no hypothesis on the jump times whatever, and
  along an arbitrary monotone continuous time map. **Proved** on 2026-09-10,
  eleventh run. The time map is carried for the reason it is carried in
  `measurable_stepIndex_comp`: the local construction reads jump times in `ℝ≥0∞`
  at real times, so it is `ENNReal.ofReal` there, and `eventuallyEq_nhdsGE_stepPath`
  is the case of the identity — which is how the old declaration is now proved.
* `truncRate lam n = min lam n`, the rate truncated at a level, with
  `truncRate_le` (bounded by `n` on all of `E`), `truncRate_pos` (positive from
  the level `1` on, at a positive rate) and `measurable_truncRate`. **Proved** on
  2026-09-10, twelfth run. It is the data of the bounded case, manufactured out of
  the data of the local one.
* `jumpTimeE_le_of_rate_le`: lowering the rate delays every jump time, at every
  sample point and under no hypothesis. **Proved** on 2026-09-10, twelfth run.
* `jumpProcessE_eq_truncRate_of_le_rateTime`: **up to the hitting time of the
  level `n`, the local jump process is the jump process of the truncated rate.**
  **Proved** on 2026-09-10, twelfth run, together with
  `stoppedProcess_jumpProcessE_truncRate`, the same identity read as an identity
  of stopped processes. The hypotheses are non explosion at the sample point and
  `ENNReal.ofReal t ≤ rateTime lam n ω`, and nothing else; in particular no
  positivity and no bound on `lam`. This answers what Point 5 of this milestone
  was left with: the stopped process does not merely satisfy the same martingale
  identities as a process of bounded rate — it **is** one, term for term, driven
  by the same chain and the same waiting times on the same space. The two steps
  are `jumpTimeE_truncRate_eq`, an induction over the index in which the truncated
  rate is only ever read at a state the path has already **left** (so the state at
  the time itself, where the rate may exceed the level, never enters), and
  `jumpTimeE_le_of_rate_le`, which carries the right endpoint of the window.
  `exists_jumpProcessE_truncRate_ne` is the witness that the hitting time
  hypothesis cannot be dropped, and `rateTime_zero` says why its level is `0`
  there.
* `jumpProcessE_eq_of_rate_eq_on_path`: **two rates that agree at every state the
  path has visited give the same process**, at every sample point and with no non
  explosion hypothesis, no positivity, no bound, no measurability and no
  comparison between the two rates. **Proved** on 2026-09-10, thirteenth run,
  with `jumpTimeE_eq_of_rate_eq_on_path` and `jumpProcessE_toReal_jumpTimeE`. It
  is the hypothesis free form of `jumpProcessE_eq_truncRate_of_le_rateTime`, and
  the filtrations need it in that form: a natural filtration is not an almost
  sure notion, so a comparison that discards the explosion set cannot compare
  σ-algebras. Non explosion was needed to *name* a window, and where there is no
  window every jump time lies below the time, so the two sequences of jump times
  are equal outright and the two step indices are the same junk value. The
  monotonicity `jumpTimeE_le_of_rate_le` is not needed either once the hypothesis
  is read at the closed end `s = t`: the state the path occupies **at** `t` is
  visited at `t`. The one hypothesis is `0 ≤ t`, and it is not cosmetic — below
  `0` the hypothesis is vacuous while the conclusion still claims something.
* `rateSup_truncRate_lt_iff`: **the level is passed by the running supremum of
  the rate exactly when it is passed by that of the truncated rate**. **Proved**
  on 2026-09-10, thirteenth run, from the comparison read from each of the two
  sides in turn (`jumpProcessE_truncRate_eq_of_rateSup_lt`,
  `jumpProcessE_eq_truncRate_of_rateSup_truncRate_lt`, and the two identities of
  the suprema `rateSup_truncRate_eq_of_lt`, `rateSup_eq_of_rateSup_truncRate_lt`
  behind them). Neither direction is free; each is the comparison of the paths
  read from its own side, and the second is the only place in the milestone where
  the truncated path is the given one. With `lt_rateTime_iff_rateSup_lt` it gives
  `setOf_lt_rateTime_eq`, the identity
  `{s < rateTime lam n} = {rateSup (truncRate lam n) s < n}`, and hence
  `measurableSet_lt_rateTime_truncRate`: the set on which the local process has
  not yet reached the level is an event of the **truncated** filtration, which is
  what the σ-algebra argument below needs and what a comparison of paths alone
  does not give.
* `naturalFiltration_inter_le`: **the trace of one natural filtration on a set
  where the two processes agree is seen by the other**, with no topology, no
  measure and no relation between the two processes beyond that agreement.
  **Proved** on 2026-09-10, thirteenth run. The set has to belong to the *target*
  σ-algebra and not merely be measurable: the family `{A | A ∩ N ∈ 𝓖}` is closed
  under complements because `Aᶜ ∩ N = N \ (A ∩ N)`, and that is where the
  membership is spent. It is the general form of the passage from the generating
  evaluations to the whole σ-algebra.
* `jumpFiltrationE_inter_lt_rateTime`: **the two natural filtrations agree before
  the hitting time**: for `A ∈ jumpFiltrationE lam s`, the set
  `A ∩ {ω | (s : ℝ≥0∞) < rateTime lam n ω}` lies in
  `jumpFiltrationE (truncRate lam n) s`, and conversely
  (`jumpFiltrationE_truncRate_inter_lt_rateTime`). **Proved** on 2026-09-10,
  thirteenth run, from the three points above. This is what
  `jumpProcessE_eq_truncRate_of_le_rateTime` does **not** give: a process identity
  before a time is not an identity of the σ-algebras of that time, and the two
  differ after it. It is the step that lets the conditional expectation of the
  bounded problem be read as one of the local filtration, on the set where the
  stopping has not yet happened; off that set the increment of the stopped process
  vanishes and there is nothing to prove. The second inclusion is not a
  formality: before the hitting time the truncated filtration sees no more than
  the local one, and after it the two paths part company, so the inclusion holds
  in this cut down form and in no other.
* `clipWait`, `jumpProcessE_eq_jumpProcess_clipWait`: **the local construction is
  the old one composed with a measurable map.** `clipWait ω = (ω.1, fun k ↦ max (ω.2 k) 0)`
  clips the waiting times at zero, and at a positive rate
  `jumpProcessE lam t ω = jumpProcess lam t (clipWait ω)` at **every** sample point
  and every `0 ≤ t`. **Proved** on 2026-09-10, fourteenth run. The reason there is
  no exceptional set is that `jumpTimeE` reads `ENNReal.ofReal (xi n)`, and
  `ENNReal.ofReal` has already clipped (`jumpTimeE_clipWait`); the only thing the
  restriction to `0 ≤ t` buys is
  `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` in place of
  `ENNReal.ofReal_lt_ofReal_iff`, which is what lets the waiting times be merely
  nonnegative (`jumpProcessE_eq_jumpProcess_of_nonneg`).
* `naturalFiltration_comp`: **the natural filtration of a process that factors
  through a map is the pull back of the natural filtration of the factor.**
  **Proved** on 2026-09-10, fourteenth run; it is the commutation of
  `MeasurableSpace.comap` with `⨆`, twice, and needs nothing about the map beyond
  the factorisation.
* `martingale_comp_of_map_eq`: **a martingale pulls back along a map that carries
  the measure to the measure**, the filtration downstairs being the pull back of
  the one upstairs. **Proved** on 2026-09-10, fourteenth run. A set of the past
  downstairs is then a preimage, `MeasureTheory.setIntegral_map` is the change of
  variables, and `MeasureTheory.Martingale.setIntegral_eq` is the identity
  upstairs. No topology on the index.
* `jumpProcessE_isMPSolution`: `jumpProcess_isMPSolution` for the **local**
  construction. **Proved** on 2026-09-10, fourteenth run, under `0 < lam ≤ L`, by
  the three points above: the test process of the local family is the test process
  of the old family composed with `clipWait`, `clipWait` preserves `jumpMeasure`
  because it is almost surely the identity (`map_clipWait_jumpMeasure`), and
  `jumpFiltrationE` is the pull back of `jumpFiltration` along it.
  **Under `0 ≤ lam ≤ L` it is open**, and the route above does not reach it: at a
  vanishing rate the extended jump times are `⊤`, so no clipping of the waiting
  times makes the two constructions agree, and freezing the chain instead — which
  does match the laws — fails at the sample points where the frozen data explode,
  a null set, and a natural filtration is not an almost sure notion.
* `martingale_stoppedProcess`: **the stopped process of a martingale is a
  martingale**, for an index that is not `ℕ`. **Proved** on 2026-09-10, in
  `section StoppedMartingale`, over `ℝ≥0` and for a stopping time with values in
  `ℝ≥0∞`, under three hypotheses on the process: `IsStronglyProgressive`, right
  continuity of the paths at every time, and boundedness on each window
  `[0, j]`. Mathlib has the discrete case only:
  `MeasureTheory.Submartingale.stoppedProcess`
  (`Probability/Martingale/OptionalStopping.lean:95` on master `403547feec1`,
  `:104` in v4.33.1) is stated in a section with `{𝒢 : Filtration ℕ m0}`, and there
  is no `IsStable 𝓕 (fun Y ↦ Martingale Y 𝓕 P)` anywhere in either version. What
  *is* available for a general `[LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]`
  is the optional sampling theorem for stopping times of **countable range**,
  `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_of_countable_range`
  and `…_of_le_const_of_countable_range`
  (`Probability/Martingale/OptionalSampling.lean:121` and `:90`, the same lines in
  v4.33.1 and on master); the passage from there to an arbitrary stopping time is
  what this section supplies.
* `dyadStop`, `isStoppingTime_dyadStop`, `countable_range_dyadStop`,
  `tendsto_dyadStop`: the dyadic approximation **from above** of a stopping time
  capped at `j`, `min j (⌈ρ·2ⁿ⌉/2ⁿ)`. The ceiling and not the strict upper dyadic:
  with the ceiling `{dyadStop ≤ t}` is `{ρ ≤ ⌊t·2ⁿ⌋/2ⁿ}`, a **non strict**
  condition at a dyadic level below `t`, and that is what the filtration sees
  through `hρ.measurableSet_le` alone; the strict upper dyadic would give
  `{ρ < ⌊t·2ⁿ⌋/2ⁿ}` and demand `measurableSet_lt`, which carries
  `[FirstCountableTopology]` and a first countability argument that is not needed.
* `integral_stoppedValue_eq_of_countable_range`, `integral_stoppedValue_eq`:
  `E[Y_ρ] = E[Y_j]` for a bounded stopping time `ρ ≤ j`, first for countable range
  (optional sampling plus `MeasureTheory.integral_condExp`), then in general by
  dominated convergence along `dyadStop`. **Boundedness on the window, and not
  uniform integrability**, is what pays the limit: the classical hypothesis is
  uniform integrability of `{Y_ρ}`, but the test processes of the jump
  construction are bounded by `C + 2LC·t` on `[0, t]`
  (`integrable_mpFamily_jumpProcess`), so the dominating function is a constant.
* `martingale_stoppedProcess_zero` and
  `martingale_of_martingale_stoppedProcess_top`: the two probes on the statement —
  the hypotheses are jointly satisfiable, and at `τ = ⊤` the conclusion is the
  hypothesis again, which is where an inverted `min` in the `stoppedProcess`
  bookkeeping would show.
* `jumpProcess_isLocalMPSolution`: for `lam` unbounded but with the process not
  exploding, the local martingale problem is solved, with `rateTime` as the
  localizing sequence; and the explosion criterion in terms of the jump times.
  Note what the localization buys and what it does not: on `{t < rateTime lam n}`
  the rate along the path is at most `n`, which is a bound of the same kind
  `jumpProcess_isMPSolution` asks for, but it is a bound along the path and not a
  bound on `lam`, so the global theorem does not apply to the stopped process by
  substitution. The route around that is the three points above: the stopped
  process is the process of `truncRate lam n`, which **is** of bounded rate; that
  process solves the bounded problem for its own filtration
  (`jumpProcessE_isMPSolution`); and before the hitting time that filtration is
  the one asked for. **In Lean** on 2026-09-10, eighteenth run, in
  `section LocalSolution` of `Suggested.lean`, under `Measurable lam`,
  `∀ x, 0 < lam x` and `∀ᵐ ω ∂(jumpMeasure mu nu), ω ∈ NonExplosiveE lam`; the
  third of those is discharged at the data by `ae_mem_nonExplosiveE_jumpMeasure`.
  The localizing sequence is `fun n ↦ rateTime lam (n + 1)` and not `rateTime lam`,
  and the shift is not cosmetic: `truncRate lam 0` is the zero rate, at which no
  bounded theorem applies, while `rateTime_zero` says the level `0` stops at once
  in any case. A subsequence of a localizing sequence is one, so the shift costs
  nothing.
* `jumpProcessE_isMPSolution_of_nonneg`: **`thm:jumpMP` for the local construction
  at a rate with zeros**, that is under `0 ≤ lam ≤ L` in place of `0 < lam ≤ L`,
  together with `∀ x, lam x = 0 → mu x = Measure.dirac x` and `[MeasurableEq E]`.
  **Proved** on 2026-09-10, nineteenth run. The positivity was inherited at a
  single place — the transport of `jumpProcess_isMPSolution` along `clipWait`
  (`jumpProcessE_eq_jumpProcess_clipWait`), which identifies the two constructions
  only where the holding times are positive — and it is exactly what kept the
  linear birth and death chain out of the local theorem, its rate `b x + d x`
  vanishing at the absorbing state `0` (`birthDeathRate_linear_zero`).

  The proof replaces the rate rather than the transport. `posRate lam` is
  `lam + {x | lam x = 0}.indicator 1`: positive everywhere, bounded by `max L 1`,
  and with the **same generator** (`jumpApply_posRate`, `jumpOperator_posRate`),
  because `jumpApply lam mu f x = lam x * ∫ (f y - f x) ∂(mu x)` vanishes at
  `lam x = 0` whatever `mu x` is. The jump kernel at an absorbing state is
  therefore data the generator cannot see, and prescribing it to be the Dirac
  measure there is a normalisation and not a restriction — `birthDeathKernel`
  already makes that choice. It is spent in exactly one lemma,
  `ae_absorb_jumpMeasure`.
* `aeCompletion`, `martingale_of_ae_eq_of_le_aeCompletion`,
  `naturalFiltration_le_aeCompletion`: **the almost sure comparison of two natural
  filtrations**, none of them mentioning the jump construction. The sets that agree
  with a set of `m` up to a `P`-null set form a σ-algebra; the natural filtration
  of a process lands in the one built over a second process as soon as the two
  agree almost surely at every index; and over a filtration that is almost surely
  smaller in that sense an almost surely equal process is again a martingale,
  because the martingale property is an identity between **integrals**. This is
  what makes an almost sure identity of processes usable where a natural
  filtration — which is not an almost sure notion — is the conclusion.
* `ae_absorb_jumpMeasure`: **at a state of vanishing rate the embedded chain does
  not move**, `jumpMeasure mu nu`-almost surely, under
  `∀ x, lam x = 0 → mu x = Measure.dirac x`. It rests on `chainKernel_map_one` —
  the law of the first step, a corollary of `chainKernel_map_shift` and
  `comp_chainKernel_map_zero` — and on `comp_chainKernel_map_shift`, which carries
  the induction on the index by moving the initial law. `[MeasurableEq E]`,
  Mathlib's class for a measurable diagonal, is what makes "the chain does not
  move" a measurable statement, and it is used nowhere else.
* `jumpProcessE_posRate_eq`: **the lifted rate gives the same path**, at every
  time and at every sample point at which the waiting times are positive, the
  chain does not move at a state of vanishing rate, and the waiting times diverge.
  Past the first absorbing index `N` the two constructions agree for two different
  reasons: the original path stops because its `(N+1)`-st jump time is `⊤`
  (`jumpTimeE_succ_eq_top`), the lifted one keeps jumping but every state it jumps
  to is `y N` (`chain_const_of_absorb`). The divergence of the waiting times is
  what makes the lifted step index exist; without it `stepIndex` returns its junk
  value on one side and not on the other.
* `jumpProcessE_posRate_eq_of_mem`: **the same, with the bound on the rate
  removed**. **Proved** on 2026-09-10, twenty third run. `hlam0` and `hL` enter
  `jumpProcessE_posRate_eq` at exactly one place, the non explosion of the lifted
  construction (`mem_nonExplosiveE_of_traj`), so where that is available on other
  grounds neither is needed; `jumpProcessE_posRate_eq` is now this statement with
  the non explosion produced from the bound, and no proof was rewritten. The Yule
  rate is what forces the weaker form: it is unbounded
  (`not_bddAbove_birthDeathRate_linear`), so no `L` exists.
* `martingale_stoppedProcess_mpFamily_jumpProcessE_of_nonneg` and
  `jumpProcess_isLocalMPSolution_of_nonneg`: the two theorems above under
  `0 ≤ lam` and the same normalisation of the jump kernel. **Proved** on
  2026-09-10, nineteenth run. The truncated rate has the same zeros as the rate
  from the level `1` on (`truncRate_eq_zero_iff`), so the normalisation is
  inherited by every level of the localization and the only line of either proof
  that changes is the one calling the bounded theorem.
* `mem_nonExplosiveE_of_absorb_or_tendsto_sum`, `ae_mem_nonExplosiveE_of_absorb_or`
  and `ae_mem_nonExplosiveE_jumpMeasure_of_absorb_or`: **non explosion at a rate
  with zeros**, that is at a sample point whose chain either reaches a state of
  vanishing rate — where `mem_nonExplosiveE_of_rate_zero` applies, the next jump
  time being `⊤` — or has non summable reciprocal rates, where
  `mem_nonExplosiveE_of_tendsto_sum` applies. **Proved** on 2026-09-10, twentieth
  run. The disjunction is not a convenience: `ae_mem_nonExplosiveE` and
  `ae_mem_nonExplosiveE_jumpMeasure` both ask `∀ k, 0 < lam (y k)` along the
  chain, and the linear birth and death chain fails that hypothesis on the
  extinction event, which has positive probability. The first branch rests on
  nothing but the positivity of the waiting time at the absorbing index — a state
  is only reached if the path spends time there — and the second on nothing new;
  `chain_const_of_absorb` does not enter, because the criterion asks for one
  absorbing index and not for the path beyond it.
* `ae_mem_nonExplosiveE_linearBirthDeath` and
  `linearBirthDeath_isLocalMPSolution`: the linear birth and death chain as an
  instance of `jumpProcess_isLocalMPSolution_of_nonneg`. **Proved** on 2026-09-10,
  twentieth run. Its rate is
  `birthDeathRate (fun x ↦ β * x) (fun x ↦ δ * x)`, unbounded
  (`not_bddAbove_birthDeathRate_linear`) and vanishing at `0`
  (`birthDeathRate_linear_zero`), so it is the one acceptance example of this
  milestone that exercises the local branch on both counts. The normalisation of
  the jump kernel at the absorbing state is `birthDeathKernel_apply` read at
  `b x + d x = 0`, where the kernel is the Dirac measure by construction. **Away
  from the extinction event the divergence is deterministic**, and no
  probabilistic estimate enters: a birth and death chain moves up by at most one
  step, so `y k ≤ y 0 + k` (`le_add_of_step_le_succ`) and the reciprocal rates
  dominate a tail of the harmonic series
  (`not_summable_inv_birthDeathRate_linear`). The hypothesis is `0 ≤ β + δ` and
  an arbitrary initial law on `ℕ` — only the sum of the two rates ever appears,
  the separate nonnegativity being what `isMarkovKernel_birthDeathKernel` asks
  for and therefore asked at the call site. The degenerate case `β + δ = 0` is
  the process that never moves and falls in the absorbing branch at the index
  `0`; the case `δ = 0` is the Yule process.
* `linearDeath_zero`, `birthDeathRate_yule_apply`, `isMarkovKernel_yuleKernel`,
  `yuleKernel_apply`, `jumpApply_yule`, `ae_mem_nonExplosiveE_yule` and
  `yule_isLocalMPSolution`: **the Yule process**, the linear birth and death
  chain at `δ = 0`, as a local solution. **Proved** on 2026-09-10, twenty second
  run, in seven declarations and forty six lines of code. Six of the seven are
  substitution into `section LinearBirthDeath` and cost one line each; the
  seventh, `yuleKernel_apply`, is the only statement with content of its own, and
  it says that away from the absorbing state the embedded chain of a pure birth
  process is **deterministic**, the two mixture weights of `birthDeathKernel`
  being `1` and `0` there. The one thing that is not free is the
  `IsMarkovKernel` instance: it occurs in the *statement*, inside `jumpMeasure`,
  so it cannot be discharged inside a proof and is an instance hypothesis here as
  it is for the linear chain; `isMarkovKernel_yuleKernel` discharges it at the
  call site under `0 ≤ β` alone.
* `stateIndicator`, `stateIndicator_apply`, `measurable_stateIndicator`,
  `abs_stateIndicator_le_one`, `jumpLaw`, `jumpLaw_eq_measureReal`,
  `jumpLaw_zero` and `jumpMeasure_masterEquation`: **the master equation of a
  jump process in integrated form**, `p n t = p n 0 + ∫_0^t E[(A 1_n)(X r)] dr`
  with `p n t = P (X t = n)`. **Proved** on 2026-09-10, twenty second run. It is
  `jumpMeasure_integral_sub_eq_intervalIntegral` at the test function
  `stateIndicator n`, and the two properties that identity asks of a test
  function are `measurable_stateIndicator` and `abs_stateIndicator_le_one`;
  nothing about the identity is reproved. `jumpLaw_eq_measureReal` says that
  `jumpLaw` is the one dimensional law and not merely an integral shaped like
  one, and `jumpLaw_zero` is the initial value, which is the initial law because
  the path has not moved before the first jump
  (`integral_jumpProcess_of_nonpos`). The hypotheses are those of the expectation
  identity and no others: a measurable rate, positive and **bounded**.
* `jumpApply_yule_indicator` and `jumpApply_yule_indicator_zero`: **the generator
  of the Yule process on an indicator**, `A 1_{n+1} = β n 1_n - β (n+1) 1_{n+1}`
  and `A 1_0 = 0`. **Proved** on 2026-09-10, twenty second run. This is the right
  hand side of the master equation of that process, and it is the concrete case
  of the remark on a domain with compact support below: the generator carries an
  indicator to a **finitely supported**, hence bounded, function although `lam`
  is unbounded. `A 1_0 = 0` for two reasons at once, and both are needed: the
  state `0` has rate `0`, and no other state can leave towards `0`.
* `jumpMeasure_hasDerivWithinAt_integral_Ici` and `hasDerivWithinAt_jumpLaw`:
  **the backward equation and the master equation in differential form**,
  `(d/dt) E[h (X t)] = E[(A h)(X t)]` and `(d/dt) p n t = E[(A 1_n)(X t)]`, from
  the right at every nonnegative time. **Proved** on 2026-09-10, twenty second
  run. The first is the block that was buried inside the proof of
  `jumpMeasure_integral_sub_eq_intervalIntegral`, lifted out: the derivative at
  `r` is the derivative at `0` of the construction restarted from the law at time
  `r` (`jumpMeasure_integral_jumpProcess_add'`), composed with the shift
  `x ↦ x - r`, and that composition is where the Markov property is spent. The
  identity now *uses* it instead of reproving it, and is twenty seven lines
  shorter. The second is the first at the test function `stateIndicator n`, and
  it is the input `eq_exp_add_integral_of_hasDerivWithinAt` asks for: the
  integrated form is what the identity gives, the differential form is what the
  induction on `n` consumes.
* `eq_exp_add_integral_of_hasDerivWithinAt`: **the scalar linear equation of
  first order, solved by the integrating factor**. From `f' = g - c f` from the
  right on `(0, t)` follows `f t = exp (-c t) f 0 + ∫_0^t exp (-c (t - r)) g r dr`.
  **Proved** on 2026-09-10, twenty second run. It is the step of the induction on
  `n` that solves the master equation, and it is written here because **Mathlib
  has no first order linear equation and no integrating factor**: the string
  `integrating factor` occurs in Mathlib nowhere, and `Mathlib/Analysis/ODE/` has
  six files — `Basic`, `DiscreteGronwall`, `ExistUnique`, `Gronwall`,
  `PicardLindelof`, `Transform` — none of them about the linear case. What
  Mathlib does have and this proof uses is
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, the same theorem of
  the calculus that carries `jumpMeasure_integral_sub_eq_intervalIntegral`. The
  derivative is one sided of necessity, since
  `eq_zero_of_hasDerivAt_integral_jumpProcess` says a two sided derivative at `0`
  does not exist.
* `mm1_masterEquation`: **the emptiness probe of the master equation**. **Proved**
  on 2026-09-10, twenty second run. The M/M/1 rate is positive and bounded
  (`birthDeathRate_mm1_mem`), so every hypothesis of `jumpMeasure_masterEquation`
  is discharged on data and no assumption is left standing. What the probe does
  **not** exhibit is an unbounded rate, which is the case the Yule process needs.
* `abs_jumpApply_truncRate_le`, `jumpApply_congr_rate`,
  `eventually_jumpProcess_truncRate_eq` and
  `jumpMeasure_masterEquation_of_ae_nonExplosive`: **the master equation at an
  unbounded rate**. **Proved** on 2026-09-10, twenty third run. The hypothesis
  `∀ x, lam x ≤ L` of `jumpMeasure_masterEquation` is gone; in its place stand
  almost sure non explosion and a bound `|A 1_n| ≤ K` on the **value of the
  generator** at the single test function — the remark on a domain with compact
  support turned into a hypothesis, which `jumpApply_yule_indicator` discharges on
  data where `lam` itself is unbounded. The proof truncates at `truncRate lam m`
  and passes to the limit, and every one of the three limits is dominated by a
  constant: the law by `1` (`abs_stateIndicator_le_one`), the compensator by `K`,
  and its time integral by `K`. That second domination is
  `abs_jumpApply_truncRate_le`, and it is uniform in the level although the bound
  `2 * m * C` of `abs_jumpApply_le` at the level `m` is not: the rate enters
  `jumpApply` as a factor and in no other place, so lowering it lowers the
  generator pointwise. `eventually_jumpProcess_truncRate_eq` is the
  identification at a fixed time, and it is where the localizing sequence is
  spent. The truncation runs along `m + 1`, since `truncRate lam 0` is the zero
  rate.
* `tsum_jumpLaw_eq_one`: **the one dimensional laws sum to one, and they do so
  with no hypothesis of non explosion.** **Proved** on 2026-09-10, twenty third
  run. `jumpProcess` takes its values in `E` at every time and at every sample
  point, so its law at a fixed time is a probability measure on `E` whatever the
  rate does. This is a **negative** result about the second route to non
  explosion. That route solves the master equation, sums the solution, and reads
  `∑ k, p k t = 1` as the assertion that the process has not left the state space;
  over a state space with a cemetery the reading is right, and here it is empty,
  because past an explosion time `stepIndex` returns the junk value `0` and the
  path sits at the initial state of its own chain, so the mass that should have
  escaped is still counted. It is at that same point that the master equation
  itself fails, no equation generated by `A` describing a return from infinity —
  which is why non explosion is a hypothesis of
  `jumpMeasure_masterEquation_of_ae_nonExplosive` and not a conclusion of it.
* A **cemetery state** for the jump construction, `E ⊕ Unit` or `Option E`, with
  the rate `0` and the Dirac kernel at the adjoined point, `jumpProcessOption` the
  path that takes the adjoined value from the explosion time on, and
  `mem_nonExplosiveE_iff_tsum_jumpLawOption_eq_one`: non explosion holds if and
  only if the one dimensional laws of the adjoined process sum to one over `E`
  alone. It rests on `tsum_jumpLaw_eq_one`, which shows the statement to be
  vacuous without the adjoined point, and on `jumpTimeE_succ_eq_top`, which is
  already the mechanism by which a state of vanishing rate absorbs a path forever.
  It is what turns the master equation into a route to non explosion rather than a
  consequence of one.
* `mem_nonExplosiveE_posRate_of_mem`, `ae_mem_nonExplosiveE_posRate` and
  `ae_mem_nonExplosiveE_posRate_linearBirthDeath`: **the lifted construction does
  not explode either**, for a measurable nonnegative rate whose jump kernel is the
  Dirac measure at every state of vanishing rate. **Proved** on 2026-09-11, fifth
  run. It is the transfer of non explosion **from a proof about `lam`**, and as
  such it is what the series route needs; the Lyapunov criterion proves non
  explosion of `posRate lam` outright
  (`ae_mem_nonExplosiveE_posRate_of_jumpApply_le`) and does not use it.

  Non explosion of `lam` is worthless in exactly the branch where the conclusion
  is not free. In the series `∑ ξ_k / lam (y k)` of
  `mem_nonExplosiveE_iff_tsum_eq_top` a state of vanishing rate contributes a
  single term `⊤`, so the series diverges for nothing, and the lift replaces that
  term by the finite `ξ_k`. What the transfer pays with instead is
  `chain_const_of_absorb`: past the first absorbing index the chain stands still,
  so the lifted rate is `1` at every state the path visits from there on and the
  waiting times alone carry the divergence — `ae_tendsto_sum_snd_jumpMeasure`
  through `mem_nonExplosiveE_of_tendsto_sum`. Where the chain never meets an
  absorbing state nothing is spent at all: the two rates agree along the
  trajectory, so `jumpTimeE_congr_of_lt` makes the two families of jump times the
  **same function** and the hypothesis passes through unchanged. The almost sure
  form adds the three standing facts of the construction,
  `ae_pos_snd_jumpMeasure`, `ae_tendsto_sum_snd_jumpMeasure` and
  `ae_absorb_jumpMeasure`, the last being the only place the hypothesis on the
  jump kernel is spent.

  With it the identification is free: `jumpProcessE_posRate_eq_of_mem` says the
  two constructions have the same path, `jumpApply_posRate` says they have the
  same generator, `jumpLaw_posRate_eq` says they have the same one dimensional
  laws, and none of them asks for a bound on the rate.
  `ae_mem_nonExplosiveE_posRate_linearBirthDeath` is the instance on the data of
  the one acceptance example that probes the local branch, and it is the series
  route standing where `ae_mem_nonExplosiveE_posRate_birthDeath_of_birth_le` puts
  the Lyapunov route.
* `ae_mem_nonExplosiveE_posRate_of_jumpApply_le`,
  `ae_mem_nonExplosiveE_posRate_birthDeath_of_birth_le` and
  `ae_mem_nonExplosiveE_posRate_yule`: **the Lyapunov criterion across the lift of
  the rate.** **Proved** on 2026-09-11, third run. Same hypotheses as
  `ae_mem_nonExplosiveE_jumpMeasure_of_jumpApply_le` together with the jump kernel
  of an absorbing state being the Dirac measure there, and the conclusion is non
  explosion of `posRate lam`. Both hypotheses of the criterion are insensitive to
  the lift and in different ways: the generator is unchanged by it
  (`jumpApply_posRate`), and a bound `B` for `lam` on a sublevel set is the bound
  `max B 1` for `posRate lam` on the same set. At a state of vanishing rate the
  generator is `0`, so the inequality `A f ≤ C * f` holds there for free and
  nothing has to be assumed about the states the criterion did not see before.
  No trajectory is looked at and no divergence of the waiting times is used, which
  is what distinguishes this from `ae_mem_nonExplosiveE_posRate`.
* `integrable_stateIndicator_jumpProcess`, `integral_comp_jumpProcess_eq_sub` and
  `jumpLaw_posRate_eq`: **the bridge from the lifted rate to the process.**
  **Proved** on 2026-09-11, third run. The master equation is written in `jumpLaw`,
  which reads `jumpProcess` and therefore asks a positive rate, while the process
  the statement is about is `jumpProcessE lam`, which does not.
  `jumpLaw_posRate_eq` identifies the two: `jumpLaw (posRate lam) mu nu t k` is the
  law of `jumpProcessE lam t` under `jumpMeasure mu nu`, for a measurable
  nonnegative rate whose jump kernel is the Dirac measure at every state of
  vanishing rate and whose lift does not explode. It rests on
  `jumpProcessE_posRate_eq_of_mem` and on `jumpProcessE_eq_jumpProcess` for the
  lifted rate, which has the positivity that `lam` lacks.
  `integral_comp_jumpProcess_eq_sub` is the other half of the bridge: a generator
  that is a combination of two state indicators integrates along the process to
  that combination of one dimensional laws, which is what turns the compensator of
  `jumpMeasure_masterEquation_of_ae_nonExplosive` into the right hand side of a
  master equation.
* `yule_masterEquation`: **the master equation of the Yule process.** **Proved** on
  2026-09-11, third run. With `p k r = jumpLaw (posRate lam) mu nu r k` for the
  Yule data it reads
  `p (n+1) t = p (n+1) 0 + ∫_0^t (β n p n r - β (n+1) p (n+1) r) dr`, for every
  `t ≥ 0` and every `n`. It is the **first** master equation in this file at a rate
  that is not bounded, and it discharges each of the two hypotheses of
  `jumpMeasure_masterEquation_of_ae_nonExplosive` on the data: the bound is asked
  of the generator at the test function and not of the rate, and
  `jumpApply_yule_indicator` gives it as `β n + β (n+1)`; the non explosion is
  `ae_mem_nonExplosiveE_posRate_yule`. The index `n + 1` is not a convenience —
  `jumpApply_yule_indicator_zero` says the generator annihilates `stateIndicator 0`,
  so the equation at `0` is `p 0 t = p 0 0` and carries no integral.
  It does **not** yield non explosion, and `tsum_jumpLaw_eq_one` says why.
* `jumpApply_linearBirthDeath_indicator`,
  `jumpApply_linearBirthDeath_indicator_zero`,
  `jumpApply_yule_indicator_of_linearBirthDeath`,
  `integral_comp_jumpProcess_eq_add_sub` and `linearBirthDeath_masterEquation`:
  **the master equation of the linear birth and death chain.** **Proved** on
  2026-09-11, fifth run. With
  `p k r = jumpLaw (posRate (birthDeathRate (linearBirth β) (linearDeath δ))) mu nu r k`
  it reads
  `p (n+1) t = p (n+1) 0 + ∫_0^t (β n · p n r + δ (n+2) · p (n+2) r − (β+δ)(n+1) · p (n+1) r) dr`,
  for every `t ≥ 0` and every `n`, under `0 ≤ β` and `0 ≤ δ`.

  The generator at a state indicator has **three** terms and not two, one for
  each way the state `n+1` is entered or left: a birth from `n`, a death from
  `n+2`, and the departure at the total rate. That is not a cosmetic
  generalisation of `yule_masterEquation` — it is why the system is an infinite
  coupled system and not a chain of scalar equations, so
  `eq_yuleDensity_of_masterEquation` does not carry over and the closed form does
  not follow. What does carry over is the whole supply: the generator is a finite
  combination of state indicators and therefore bounded although the rate is not,
  `jumpApply_posRate` says the lift is invisible to it, and non explosion of the
  lifted rate is `ae_mem_nonExplosiveE_posRate_linearBirthDeath` — the **series**
  route, where `yule_masterEquation` takes the Lyapunov route.

  `integral_comp_jumpProcess_eq_add_sub` is `integral_comp_jumpProcess_eq_sub`
  with a third indicator and is free of the birth and death data.
  `jumpApply_linearBirthDeath_indicator_zero` is the equation at the absorbing
  state, where a single term remains, the death from `1` — the mass extinction
  accumulates, which the pure birth chain does not have
  (`jumpApply_yule_indicator_zero`).
  `jumpApply_yule_indicator_of_linearBirthDeath` derives
  `jumpApply_yule_indicator` back out at `δ = 0`, and the term that vanishes is
  the one that reads the state above.
* `linearBirthDeath_masterEquation_zero`: **the equation at the absorbing
  state**, `p 0 t = p 0 0 + ∫_0^t δ · p 1 r dr`, the extinction probability as an
  integral over the probability of sitting at `1`. It rests on
  `jumpApply_linearBirthDeath_indicator_zero`, which leaves a single term there,
  and on `integral_comp_jumpProcess_eq_sub` in its two term form. It is the first
  statement of this branch the pure birth chain cannot make: there the generator
  annihilates `stateIndicator 0` and `p 0` is constant.
* `hasDerivAt_generatingFunction_linearBirthDeath` and `jumpLaw_linearBirthDeath`:
  **the generating function of the linear birth and death chain, and the one
  dimensional law it yields.** With `G s t = ∑' n, p n t * s ^ n` for `|s| ≤ 1`,
  `∂_t G s t = (β s − δ) (s − 1) · ∂_s G s t` and `G s 0 = s` from a start at `1`;
  the solution gives the law, an atom at `0` with a geometric tail above it. It
  rests on `linearBirthDeath_masterEquation` and
  `linearBirthDeath_masterEquation_zero` — multiply by `s ^ n` and sum — on
  `abs_jumpLaw_le_one` for the convergence of the series on the closed unit disc,
  and on `tsum_jumpLaw_eq_one`.

  This is the point at which the birth and death case parts from the pure birth
  case. `eq_yuleDensity_of_masterEquation` solves a **chain** of scalar linear
  equations there, because the generator at a state indicator sees the state
  below and the state itself; the death term adds the state above, the system is
  coupled, and the induction on the level has no counterpart. The generating
  function is the tool that replaces it, and its equation is a **first order
  partial differential equation**. Mathlib has nothing of it: a search for
  `partial differential equation`, `method of characteristics`,
  `characteristicCurve` and `characteristic curve` over `Mathlib/` of
  `upstream/master` `1192d624` returns two hits, and both are bibliography
  entries (`Mathlib/Analysis/Distribution/Sobolev.lean:47`,
  `Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean:25`). The method of
  characteristics for a scalar linear equation in two variables therefore belongs
  to this point and is written here, as
  `eq_exp_add_integral_of_hasDerivWithinAt` is written here for the ordinary
  linear case. `scripts/check_negatives.py` carries the statement under
  `first-order-pde`.
* `measurable_jumpLaw`, `abs_jumpLaw_le_one`, `intervalIntegrable_jumpLaw` and
  `abs_sub_mul_jumpLaw_le`: **the one dimensional law as a function of time.**
  **Proved** on 2026-09-11, fourth run. The law is measurable in the time
  argument, it is bounded by `1`, and a difference of two multiples of laws is
  bounded by the sum of the absolute values of the coefficients; a bounded
  measurable function of time is interval integrable. These four are what the
  passage from the *integrated* master equation to the *differential* one
  consumes, and `measurable_jumpLaw` is the only one of them that touches the
  jump construction — it is the joint measurability `measurable_jumpProcess`
  pushed through the integral over the sample point.
* `eq_of_masterEquation`: **an integrated first order linear equation determines
  its solution.** **Proved** on 2026-09-11, fourth run. If `f` satisfies
  `f s = f 0 + ∫_0^s (g - c f)` for every `s ≥ 0` with a measurable and bounded
  right hand side, `g` is continuous on `[0, ∞)`, and `F` satisfies the same
  equation in differential form with `F 0 = f 0`, then `f t = F t` for every
  `t ≥ 0`. It is `eq_exp_add_integral_of_hasDerivWithinAt` applied **twice and
  never evaluated**: both functions equal the same variation of constants
  expression, which therefore does not have to be computed.
  The bootstrap is the content: the right hand side is bounded and measurable,
  so it is interval integrable and its primitive is continuous
  (`intervalIntegral.continuous_primitive`), so `f` is continuous, so the right
  hand side is continuous at every positive time, and only then does the
  fundamental theorem of calculus (`intervalIntegral.integral_hasDerivAt_right`)
  turn the equation into a derivative. This is why the hypothesis on the right
  hand side is measurability and a bound and not continuity: continuity of the
  right hand side is a *conclusion*, since the right hand side contains the
  unknown.
* `hasDerivAt_expNeg` and `hasDerivAt_yuleDensity_succ`: **the candidate solves
  the equation.** **Proved** on 2026-09-11, fourth run. With
  `e s = exp (-(β s))` the function `F n s = e s * (1 - e s) ^ n` satisfies
  `(F (n+1))' r = β (n+1) F n r - β (n+2) F (n+1) r`, which is one step of the
  induction over the level. One differentiation and one `ring`; no measure and
  no process occur.
* `eq_yuleDensity_of_masterEquation`: **the master equation of the Yule process
  started at one has exactly one solution.** **Proved** on 2026-09-11, fourth
  run. For any family `p : ℕ → ℝ → ℝ` that is measurable in time, bounded by
  `1`, has `p k 0 = δ_{k,1}`, and satisfies
  `p (m+1) s = p (m+1) 0 + ∫_0^s (β m p m r - β (m+1) p (m+1) r) dr` for every
  `m` and every `s ≥ 0`, one has
  `p (n+1) t = exp (-β t) (1 - exp (-β t))^n` for every `n` and every `t ≥ 0`.
  The statement names no jump process: what is proved is that the *equation*
  determines the law, and the construction enters only at `jumpLaw_yule_succ`.
  The induction is over the level; at the level `0` the inhomogeneity carries
  the factor `β * 0` and vanishes, at every further level it is the level below.
* `yule_masterEquation_zero`, `jumpLaw_yule_init`, `jumpLaw_yule_zero`,
  `jumpLaw_yule_succ` and `tsum_jumpLaw_yule_succ`: **the one dimensional law of
  the Yule process is geometric.** **Proved** on 2026-09-11, fourth run. Started
  at one individual, `P (X t = n + 1) = exp (-β t) (1 - exp (-β t))^n` and
  `P (X t = 0) = 0`, for every `t ≥ 0`. This is the independent control the
  construction is measured against, as `poissonMeasure` is for the Poisson
  process: the geometric distribution does not come out of this construction.
  `yule_masterEquation_zero` is the equation at the absorbing state, where the
  compensator vanishes identically (`jumpApply_yule_indicator_zero`) and a pure
  birth process never returns to `0`; `jumpLaw_yule_init` is `jumpLaw_zero` on
  `ν = δ₁`. `tsum_jumpLaw_yule_succ` sums the solution to `1` as a geometric
  series, and it is a **check of the formula and not a non explosion
  statement** — `tsum_jumpLaw_eq_one` proves the same total mass without any
  hypothesis whatever.
* `mem_nonExplosiveE_of_rate_le`, `nonExplosiveE_subset_of_rate_le` and
  `mem_nonExplosiveE_yule_of_linearBirthDeath`: **non explosion is antitone in
  the rate.** **Proved** on 2026-09-11, fourth run. If `lam ≤ lam'` pointwise
  then `NonExplosiveE lam' ⊆ NonExplosiveE lam`, at **every** sample point and
  not almost everywhere: `mem_nonExplosiveE_iff_tsum_eq_top` makes non explosion
  the single identity `∑ k, ofReal (ξ k) / ofReal (lam (y k)) = ⊤`, the series
  is antitone in the rate term by term, and a divergent series of nonnegative
  terms keeps diverging when its terms grow. The chain and the waiting times are
  the same on both sides; only the rate changes.
  `mem_nonExplosiveE_yule_of_linearBirthDeath` is what that gives on the linear
  data, and it gives it **in the direction nobody needs**: the Yule rate `β x`
  is below the total rate `(β + δ) x` of the linear chain, so the non explosion
  of the linear chain implies that of the Yule process and not conversely,
  because a death raises the total rate. The domination the coupling route means
  is between the **states** and not between the rates, and two processes whose
  states are compared do not share an embedded chain — a coupling is a measure
  on a common space, not a rate inequality. That is the cost of the coupling
  route, and it is named here rather than discovered halfway through it.
* `le_mul_exp_sum_of_lyapunov`, `not_summable_inv_of_lyapunov`,
  `ae_mem_nonExplosiveE_jumpMeasure_of_lyapunov` and `jumpApply_le_of_lyapunov`:
  **the Lyapunov criterion for non explosion, in its pathwise form.** **Proved**
  on 2026-09-11, first run.
  Given `f : E → ℝ` nonnegative and measurable, a constant `C ≥ 0` with
  `f z ≤ f x * (1 + C / lam x)` for `mu x`-almost every `z` at every state of
  positive rate, and a bound on `lam` over every sublevel set `{f ≤ N}`, almost
  every sample point of `jumpMeasure mu nu` is in `NonExplosiveE lam`. The
  mechanism is one estimate: iterating the growth condition and `1 + t ≤ exp t`
  gives `f (y k) ≤ f (y 0) exp (C ∑_{j<k} 1/lam (y j))`, so summable reciprocal
  rates confine the chain to **one** sublevel set, the rate there is below a
  bound `B`, and the reciprocal rates stay above `B⁻¹` — which no summable
  series of nonnegative terms does. Nothing is asked at a state of vanishing
  rate, where the path is absorbed and non explosion is free; that branch is
  `ae_mem_nonExplosiveE_jumpMeasure_of_absorb_or`, and it is what lets the
  criterion reach the birth and death chains.

  **The second hypothesis is a boundedness and not an exhaustion.** What the
  proof consumes is that `lam` is bounded on `{f ≤ N}` and nothing else about
  that set; that the sublevel sets exhaust `E` is neither used nor enough. The
  classical wording — sublevel sets compact — implies it through the continuity
  of the rate, and is therefore the stronger hypothesis.
* `lyapunovWeight`, `measurable_lyapunovWeight`, `prod_lyapunovWeight_of_pos`,
  `lintegral_chainKernel_lyapunov_le`,
  `ae_absorb_or_not_summable_of_lintegral_le`,
  `summable_iff_tsum_ofReal_ne_top`, `measurableSet_summable_inv_comp`,
  `measurableSet_absorb_or_not_summable`,
  `ae_mem_nonExplosiveE_jumpMeasure_of_lintegral_le`,
  `ae_mem_nonExplosiveE_jumpMeasure_of_lintegral_le_of_ne_top`,
  `lintegral_ofReal_le_of_jumpApply_le` and
  `ae_mem_nonExplosiveE_jumpMeasure_of_jumpApply_le`: **the same criterion under
  the generator inequality** `jumpApply lam mu f x ≤ C * f x`, that is
  `lam x * (∫ f dmu x - f x) ≤ C * f x`, with the same bound on `lam` over the
  sublevel sets. **Proved** on 2026-09-11, second run.

  It does **not** follow from the pathwise form: the pathwise inequality implies
  the generator inequality by integration — that implication is
  `jumpApply_le_of_lyapunov`, and it asks only `0 < lam x` and
  `Integrable f (mu x)` — and is strictly stronger, since an average below a
  bound says nothing about the values. What replaces the pointwise iteration is
  the discounted Lyapunov function on the embedded chain,
  `M k = f (y k) * exp (-C ∑_{j<k} 1/lam (y j))`, whose one step estimate is the
  generator inequality; `lyapunovWeight` is its one step discount, `0` at a
  state of vanishing rate, and killing the discount there is what frees the
  criterion of every hypothesis at an absorbing state, exactly as in the
  pathwise form.

  **The supermartingale is never built, and that is the finding.**
  `lintegral_chainKernel_lyapunov_le` states only what the argument uses —
  `∫ M k ≤ ∫ f dnu` for every `k` — and proves it by induction on `k` in which
  the initial law moves along, `comp_chainKernel_map_shift` carrying one step of
  the chain into one step of the law. That is `ae_step_comp_chainKernel` with an
  integral in place of an almost sure statement, and it needs neither a
  filtration nor a conditional expectation: no `MeasureTheory.Filtration.piLE`,
  no `ProbabilityTheory.Kernel.condExp_traj`, no `Supermartingale`. The
  generator hypothesis is spent exactly once, at the head of the chain, where it
  reads `exp (-C/lam z) * (1 + C/lam z) ≤ 1` — which is `1 + t ≤ exp t`.

  The passage to the limit is Fatou (`lintegral_liminf_le`) and one implication
  at a sample point: where the clock converges the discount stays above a
  positive constant, so a finite `liminf` of `M` forces a finite `liminf` of `f`
  along the chain, the chain meets a sublevel set of `f` infinitely often, the
  rate is bounded there — and reciprocal rates that do not tend to zero are not
  summable. Everything is carried in `ENNReal`, where the estimate needs no
  integrability and Fatou is unconditional; the bridge to the real valued
  generator is `lintegral_ofReal_le_of_jumpApply_le`, and integrability is asked
  there and nowhere else, of the kernel and not of the chain.

  **The hypothesis that `f` has a finite mean under the initial law is not
  needed, and removing it is a statement about the explosion event.** The Fatou
  bound does need it, so the estimate is proved one starting state at a time,
  where the mean is the value, and carried back to an arbitrary initial law by
  `Measure.ae_comp_of_ae_ae`. That passage needs the explosion event to be a
  **measurable** subset of `ℕ → E`, and `Summable` is not by itself a measurable
  property of the terms: `summable_iff_tsum_ofReal_ne_top` reads it as the
  finiteness of the series in `ℝ≥0∞`, where the sum is a limit of measurable
  partial sums with no convergence hypothesis to check, and
  `measurableSet_summable_inv_comp` is that observation applied to
  `{y | Summable fun k ↦ (lam (y k))⁻¹}`. This is why
  `ae_absorb_or_not_summable_of_lintegral_le` is stated at the level of the
  chain and not in terms of `jumpMeasure`: an almost sure statement about
  `chainKernel mu ∘ₘ nu` conditions on the starting state, one about
  `jumpMeasure mu nu` does not. What is left over `nu` is nothing at all, and
  `ae_mem_nonExplosiveE_jumpMeasure_of_jumpApply_le` therefore asks no more of
  the initial law than the pathwise form does.

  **The difference to the pathwise form is visible on a birth and death chain
  and is not a technicality.** With `f x = x + 1` the pathwise form asks
  `b x + d x ≤ C * (x+1)` and the generator form asks `b x ≤ C * (x+1)` alone,
  the death term being `≤ 0` in `A f x = b x - d x`. So the generator form is
  what carries the statement *the birth rate grows at most linearly, the death
  rate is free*, and the pathwise form does not.
* `exists_bound_of_le_nat`, `integrable_birthDeathKernel`,
  `ae_mem_nonExplosiveE_birthDeath_of_birth_le` and
  `ae_mem_nonExplosiveE_yule_of_jumpApply_le`: **the birth and death instances
  of the generator form.** **Proved** on 2026-09-11, second run. On `ℕ` every
  sublevel set of the identity is finite, so the bound on the rate is free
  (`exists_bound_of_le_nat`) whatever the death rate is, and the birth and death
  kernel is a finite combination of Dirac measures, so every function is
  integrable against it (`integrable_birthDeathKernel`). What is left is the
  generator inequality alone: `b x ≤ C * (x + 1)`, with `d` free — a death rate
  `d x = 2 ^ x` is covered here and by no pathwise form.

  **The Lyapunov function is `f x = x + 1` and not `f x = x`, and the shift is
  not cosmetic.** At the state `0` the generator of `f x = x` is `b 0`, so the
  condition would read `b 0 ≤ 0`; the shift is what lets the criterion see a
  state from which the chain can only go up. The Yule process is then the
  constant `C = β` and the inequality `β x ≤ β (x+1)`, and it is the probe of
  the generator form for the same reason it is the probe of the pathwise form:
  without a death term the two coincide on it, so what is gained here is gained
  not on Yule but on its neighbours.
* `ae_mem_nonExplosiveE_birthDeath_of_rate_le`,
  `ae_mem_nonExplosiveE_linearBirthDeath_of_lyapunov` and
  `ae_mem_nonExplosiveE_yule_of_lyapunov`: **the birth and death instances of the
  criterion.** **Proved** on 2026-09-11, first run. The Lyapunov function is the
  state itself, `f x = x`, and both hypotheses are read off the data in one line
  each: the kernel moves the chain up by at most one
  (`ae_le_succ_birthDeathKernel`), so the pathwise inequality
  `x + 1 ≤ x (1 + C / lam x)` is exactly `lam x ≤ C * x`, and the rate on
  `{f ≤ N}` is bounded by `C * N` for the same reason. The linear chain and the
  Yule process are then the constant `C = β + δ` and nothing else.

  It is the **general** birth and death statement and not one more instance:
  every total rate with `b x + d x ≤ C * x` is covered, and the hypothesis is
  sharp in its order of growth. At `b x = x ^ (1 + ε)` the chain explodes, and
  what fails is not the pathwise inequality — which holds with no `C` at all,
  the chain still moving by one step — but the bound on the sublevel set. That
  is the one place in the criterion where the growth of the rate is seen.
* `ae_step_chainKernel`, `ae_step_comp_chainKernel` and
  `ae_forall_step_comp_chainKernel`: **a property of consecutive states of the
  chain, carried from the kernel to the trajectory**. **Proved** on 2026-09-10,
  twentieth run. They are the general form of `ae_absorb_chainKernel` and
  `ae_absorb_comp_chainKernel`, whose argument — the law of the first step, then
  an induction on the index in which the initial law moves along
  (`comp_chainKernel_map_shift`) — uses nothing about the property. They ask less
  than their absorbing predecessors: `MeasurableSingletonClass E` in place of
  `MeasurableEq E`, and no measurability of the step relation at all in the one
  step form. `ae_le_succ_birthDeathKernel` is the birth and death instance, and
  it needs no positivity of the two rates: where their sum vanishes the kernel is
  the Dirac measure, and where it does not the kernel is carried by `{x+1, x-1}`.
* `martingale_stoppedProcess_mpFamily_jumpProcessE`: **the stopped test process of
  the local jump problem is a martingale**, at every stopping time of its natural
  filtration and under the hypotheses of `jumpProcessE_isMPSolution`. This is the
  first of the two hinges of the assembly, and it discharges all three hypotheses
  of `martingale_stoppedProcess` on the jump construction:
  `isStronglyProgressive_mpFamily_jumpProcessE`,
  `tendsto_nhdsGE_mpFamily_jumpProcessE` and the window bound
  `abs_setIntegral_compensatorE_le`. Uniform integrability does not occur: the
  window bound is `C + 2LC·j`, a constant, so the passage to the limit inside
  `martingale_stoppedProcess` is dominated convergence with a constant majorant.
  It is stated for an arbitrary stopping time and not for `rateTime`, because that
  is what it proves — the localization enters only through the *rate* it is
  applied to; `isStoppingTime_rateTime_truncRate` says that `rateTime lam n` is a
  stopping time of `jumpFiltrationE (truncRate lam n)`, which is the filtration
  it is applied over.
* `stronglyAdapted_mpFamily_jumpProcessE`, `measurable_uncurry_jumpProcessE`,
  `measurable_compensatorE`, `compensatorE_eq_intervalIntegral`,
  `tendsto_nhdsGE_sub_intervalIntegral_jumpProcessE`, `mpFamily_jumpProcessE_eq`:
  the counterparts for `jumpProcessE` of the corresponding statements for
  `jumpProcess`, none of them carrying a hypothesis on the rate beyond its
  measurability, and the passage from the compensating window of `lebesgueClock`
  to a genuine `intervalIntegral` of `ℝ` — which both properties of the test
  process are properties of, because both are properties of the *upper end* of
  the window.
* `jumpProcessE_truncRate_eq_of_rate_le` and
  `jumpProcessE_eq_truncRate_of_le_rateTime'`: **the comparison with the truncated
  rate needs no non explosion.** The window hypothesis of
  `jumpProcessE_truncRate_eq` is discharged by the case distinction of
  `jumpProcessE_eq_of_rate_eq_on_path`: where no window contains the time, every
  jump time lies below it, `jumpTimeE_truncRate_eq` applies at every index at once,
  and the two step indices are computed from one and the same sequence. What
  remains is `ENNReal.ofReal t ≤ rateTime lam n ω`, at every sample point.
  `stoppedProcess_jumpProcessE_truncRate'` reads it as an identity of stopped
  processes. This is what lets the identification of the two stopped test
  processes be an equality of **functions** rather than an almost sure one, which
  is what `StronglyAdapted` and `IsStoppingTime` — neither an almost sure notion —
  require of it.
* `stoppedProcess_mpFamily_truncRate_eq`: **the two stopped test processes are the
  same function**, with no hypothesis on the sample point and none on the rate.
  The identity of the *paths* is the point above; what is added is the identity of
  the *generators*: `jumpApply (truncRate lam n) mu f` and `jumpApply lam mu f`
  agree at a state of rate below `n`, which along the stopped path holds at every
  time **strictly** below the hitting time and may fail at the hitting time
  itself, where the running supremum has already reached the level. That one time
  is a single point of the compensating window, and
  `lebesgueClock_apply_singleton` says it is a null set of the clock, so
  `setIntegral_congr_ae` closes the gap.
* `martingale_indicator_bot`: an event of `𝓕 ⊥` may be cut out of a martingale.
  This is what `Locally` asks for and it is not cosmetic — its test object carries
  the indicator of `{ω | ⊥ < τ n ω}`, and at the level `n = 0` of the localizing
  sequence of the local jump problem that set is empty (`rateTime_zero`).
* `martingale_of_martingale_of_stopped`: **the tower step**, with no reference to
  the jump construction. A process that is a martingale for one filtration,
  strongly adapted to a second, constant after a stopping time `τ` of the second,
  and whose events of the second filtration cut down by `{i < τ}` are events of
  the first, is a martingale for the second. The decomposition is
  `S = (S ∩ {i < τ}) ∪ (S ∩ {τ ≤ i})`: on the second piece the process takes the
  same value at `i` and at `j` pointwise, and the first piece is where the
  martingale property of the first filtration is spent, through
  `MeasureTheory.Martingale.setIntegral_eq` and
  `ae_eq_condExp_of_forall_setIntegral_eq`. `jumpFiltrationE_inter_lt_rateTime`
  is the fourth hypothesis on the jump construction.
* `stronglyAdapted_stoppedProcess_mpFamily_jumpProcessE`: **the stopped test
  process of the local problem is adapted to the local filtration**, under
  `Measurable lam` and nothing else about the rate. **In Lean** on 2026-09-10,
  eighteenth run. It is not
  `IsStronglyProgressive.stronglyAdapted_stoppedProcess` applied to
  `isStronglyProgressive_mpFamily_jumpProcessE`: that statement carries a bound on
  the rate, and the bound is not a convenience there. For an unbounded rate the
  *unstopped* test process has no reason to be right continuous at an explosive
  sample point: the compensator over a window containing the explosion time
  integrates a function whose absolute value is `lam(X_u)` times a constant, and
  the integral of `lam(X_u)` over `[0, T_∞)` is `∑ ξ_k`, which diverges at almost
  every sample point of the explosion set, so Bochner returns the junk value `0`
  there. The stopped process has no such defect, because
  below `rateTime lam n` the rate along the path is below `n`; the statement is
  therefore about the stopped process and has to be proved of it. The route: the
  first summand `p.1 (X_{i∧τ})` is `stoppedProcess` of the state process and is
  reached by `measurable_uncurry_jumpProcessE`, which asks nothing of the rate; the
  compensator is the **fixed** window `∫_{(⊥, i]} g(u, ·) dq` with
  `g(u, ω) = {q | q.1 ≤ σ q.2}.indicator (fun q ↦ p.2 (X_{min q.1 i} q.2)) (u, ω)`
  and `σ ω = (min i (τ ω)).untopA`, jointly measurable because
  `IsStoppingTime.measurable_of_le` makes `min i τ`, unlike `τ`, measurable for
  `𝓖 i`. A window whose *upper end* is random is a window of fixed length with a
  cut off integrand, because `σ ≤ i`: that identity, `Set.Ioc_inter_Iic` and
  `MeasureTheory.setIntegral_indicator` are the whole of the second summand. **No
  bound on the integrand is spent**, and none is available: the cut off is what
  replaces it, and the bound `2 n C` that the rate along the stopped path would
  give is not needed, because measurability of a Bochner integral in a parameter
  (`stronglyMeasurable_integral_comp`) asks for joint measurability alone.
* The path dependent variant, where the rate at time `t` is a predictable
  functional of the path rather than a function of the current state, with the
  same two statements. This is the family that supplies the examples for
  Milestones 7 and 9. Its ground is the construction of the jump times, and that
  is where it differs from everything above: at a state dependent rate the
  `(n+1)`-st jump time is `T n + ξ n / lam (y n)`, a division, while at a path
  dependent rate `Λ` it is the solution `s` of
  `∫ u in Set.Ioc (T n) (T n + s), Λ u ω = ξ n`, an inverse.
  * `cumulativeRateF Λ ω t = ∫ u in Set.Ioc 0 t, Λ u ω` and
    `strictMono_cumulativeRateF`: the cumulated compensator along one sample
    point, strictly monotone and continuous where `Λ` is positive and locally
    integrable, hence invertible.
  * `jumpTimeF_succ_spec`: the defining equation of the `(n+1)`-st jump time as
    that inverse point. Everything the state dependent case builds on the jump
    times — the renewal decomposition, the progressive measurability, the tower
    argument — reads from them only that they increase and are measurable, so
    this equation is what the whole variant rests on.

**Acceptance examples.**

* **A single spike is a step path and is not càdlàg.**
  `f = Set.indicator {0} 1 : ℝ → ℝ` satisfies the *naive* condition — its jump
  set is `{0}`, finite on every compact set — and fails `IsCadlagPath`, because
  `f` is `0` on `Set.Ioi 0` and `1` at `0`. It also fails `IsStepPath`, at the
  first conjunct and at `x = 0`, which is exactly what the definition has to
  achieve. Moving the spike to the *left* of the value, `Set.indicator (Set.Ici 0) 1`,
  gives a path that satisfies both. This pair is the acceptance test for the
  definition, and it is in Lean as
  `exists_finite_setOf_leftLim_ne_not_isCadlagPath`.
* **The Poisson process as the degenerate jump process.** `E = ℕ`,
  `lam x = 1`, `mu x = Measure.dirac (x + 1)`. **In Lean** on 2026-09-10, third
  run, as `section PoissonExample` of `Suggested.lean`, in seven declarations.
  `jumpApply_poisson` is the computation the milestone asks for first, and it
  comes out as it should: `A f x = f (x + 1) - f x`, the rate cancelling
  because it is `1` and the integral against the kernel being an evaluation
  because the kernel is a Dirac measure. `poissonProcess_isMPSolution`
  discharges **every** hypothesis of `jumpProcess_isMPSolution` on this data —
  which is what shows that theorem to have an instance and not to be vacuous —
  and `martingale_compensated_poisson` turns it into an actual
  `MeasureTheory.Martingale`: for every bounded `f : ℕ → ℝ` the compensated
  increment `f (X t) - ∫_0^t (f (X u + 1) - f (X u)) du` is a martingale for the
  natural filtration. The same data are the emptiness probe of the **local**
  theorem (`poissonProcess_isLocalMPSolution`, `ae_mem_nonExplosiveE_poisson`, in
  Lean on 2026-09-10, eighteenth run): all three hypotheses of
  `jumpProcess_isLocalMPSolution` discharged on data, the non explosion at *every*
  chain because a constant rate turns the criterion into the divergence of `∑ 1`.
  What that probe does **not** exhibit is an unbounded rate, which is the case the
  local branch exists for; it is a witness against vacuity and not one of sharpness.

  **The one dimensional laws are Mathlib's Poisson laws**, in Lean on
  2026-09-10, fifth run, as `jumpMeasure_map_jumpProcess_poisson`:
  `(jumpMeasure poissonKernel δ₀).map (jumpProcess poissonRate t) = Po(t)`, with
  `Po` the `ProbabilityTheory.poissonMeasure`
  (`Mathlib/Probability/Distributions/Poisson/Basic.lean:41`) into whose
  definition nothing of `jumpTime`, `stepIndex` or `waitingMeasure` enters.
  This is the independent control on the construction, and it is the only place
  where an error in those three would show; it comes out right.

  It goes by **uniqueness** and not by the Erlang law, and the route is the one
  named below as the cheaper of the two. Written out: the law is read off
  `jumpMeasure_integral_jumpProcess_eq_expJumpApply`, and the exponential series
  is summed by the **Gregory--Newton formula**. The generator here *is* Mathlib's
  forward difference operator (`jumpApply_poisson_eq_fwdDiff`,
  `iterate_jumpApply_poisson`), so `Algebra/Group/ForwardDiff.lean` applies:
  `shift_eq_sum_fwdDiff_iter` expands `f (x + k)` in the iterated differences,
  and one Cauchy product with `exp t = ∑ t^m/m!`
  (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`) turns the finite
  expansion into the Poisson sum: `tsum_fwdDiff_iter_eq`,
  `∑' n, t^n/n! * (Δ^[n] f) x = ∑' k, exp (-t) * t^k/k! * f (x + k)`, for every
  real `t` and every bounded `f`. Comparing with `poissonMeasure_real_singleton`
  on the indicator of `{n}` and `Measure.ext_of_singleton` closes it.

  **The classical route is not available in Mathlib, and it was not needed.**
  It would go through the Erlang law of the `n`-th jump time: `T n` is a sum of
  `n` independent `Exp(1)`, hence `Gamma(n, 1)`, and
  `{X t = n} = {T n ≤ t < T (n+1)}`. But `ProbabilityTheory.gammaMeasure`
  (`Probability/Distributions/Gamma.lean:128`) and `expMeasure` are densities
  and distribution functions only: neither `v4.33.1` nor `upstream/master`
  has their **convolution**, and neither file mentions `conv`, `HasLaw` or
  `IndepFun` at all — in contrast to the Poisson side, which has
  `poissonMeasure_conv_poissonMeasure` and `IndepFun.hasLaw_add_poissonMeasure`.
  The other route that remains open is the **renewal induction** on
  `jumpMeasure_integral_eq_renewal`, giving `p 0 t = exp (-t)` and
  `p n t = ∫_0^t exp (-s) * p (n-1) (t-s) ds` hence `p n t = exp (-t) * t^n/n!`;
  it is not needed either, and it would prove the same thing.
* **A two state chain, where the exponential series is a matrix exponential.**
  `E = Bool`, `lam ≡ 1`, `mu x = Measure.dirac (!x)`. Then `A` is the matrix
  `!![-1, 1; 1, -1]` on `E → ℝ`, `‖A f‖ ≤ 2 * ‖f‖` is `norm_apply_le` at
  `L = 1`, and the one dimensional law from `false` is
  `((1 + exp (-2*t))/2, (1 - exp (-2*t))/2)`. This is the smallest instance on
  which `exists_unique_of_bounded` produces a number, and a sign error in the
  operator is visible in it. **In Lean** on 2026-09-10, fifth run, as
  `section TwoStateExample` of `Suggested.lean`, in seven declarations:
  `jumpApply_flip` is the generator, `iterate_jumpApply_flip` says the iterates
  cycle with the factor `-2` -- the eigenvalue on the antisymmetric part, and
  the reason the answer carries `exp (-2t)` and not `exp (-t)` --,
  `expJumpApply_flip` sums the series in closed form, and
  `jumpMeasure_map_jumpProcess_flip` is the number:
  `((jumpMeasure flipKernel δ_false).map (X t)).real {true} = (1 - exp (-2t))/2`.
  It checks what the Poisson example cannot: there the generator is a shift and
  a sign error would propagate into a Poisson law of another mean, here the
  state space has two points and the value must be `0` at `t = 0` and tend to
  `1/2` rather than to `1`. The `t = 0` probe is in the file as an `example`.
  The same instance carries the **two coordinate** probe, added on 2026-09-10,
  sixth run: `jumpMeasure_integral_fddProd_flip` gives
  `(1 - exp (-2t))/2 · (1 + exp (-2u))/2` for being at `true` at `t` and again
  at `t + u`. It is the only check on the *order* in which `fddExp` nests the
  semigroup -- one coordinate cannot see it, and the reversed nesting would give
  `(1 - exp (-2u))/2 · (1 + exp (-2t))/2`, a different number as soon as
  `t ≠ u`. Its two degenerations, `u = 0` back to the one dimensional law and
  `t = 0` to `0`, are in the file as `example`s.
* **Explosion, which is what the unbounded case is about.** `E = ℕ`,
  `lam n = 2 ^ n`, `mu n = Measure.dirac (n + 1)`. The jump times have
  `∑ n, 2 ^ (-n) < ∞` in expectation, so the process explodes almost surely, the
  global martingale problem has **no** solution with values in `ℕ`, and
  `jumpProcess_isLocalMPSolution` is what survives. With `lam n = n` instead the
  sum diverges, there is no explosion, and the global statement holds. This pair
  is the acceptance test for the explosion criterion.

  The deterministic half of it is in the file since 2026-09-10, eighth run, and
  it is what keeps `NonExplosiveE` from being a decoration: on `explodeRate`,
  `explodeChain`, `explodeWait` — the rate `2 ^ n` read along `y n = n` with all
  waiting times equal to `1` — the jump times are `2 - 2 / 2 ^ m`
  (`jumpTime_explode`), so they never reach `2` and
  `notMem_nonExplosiveE_explode` says the sample point is **not** in
  `NonExplosiveE`. It is paired with `mem_nonExplosiveE_absorb`, which is in the
  set. Note which defect this is **not**: the rate is positive at every state, so
  it is not the one `jumpProcessE` was built to repair, and the only hypothesis
  of `mem_nonExplosiveE_of_traj` this data fails is the bound `L`.

  **The other half of the pair is in the file since 2026-09-10, ninth run**, and
  it is what keeps the criterion from being one that only ever refuses:
  `ae_mem_nonExplosiveE_linear`, on `linearRate n = n` read along
  `linearChain n = n + 1`. Almost every sample point **is** in `NonExplosiveE`,
  because `not_summable_linearRate` is the harmonic series. The two data differ
  in nothing but the growth of the rate, `2 ^ n` against `n`, which is exactly
  what a criterion for non explosion has to see; and the linear one is reachable
  only through `ae_mem_nonExplosiveE`, since its rate is unbounded along the
  trajectory and `mem_nonExplosiveE_of_traj` does not apply. The shift by one in
  `linearChain` is not a trick: at `y n = n` the rate vanishes at the state `0`,
  which is the absorbing case `mem_nonExplosiveE_of_rate_zero` already settles,
  and this example is about the other defect.
* **The generator of a birth and death chain, and the two branches it splits
  into.** `b, d : ℕ → ℝ`, total rate `b + d`, jump kernel the mixture with
  weights `b / (b + d)` and `d / (b + d)`. **In Lean** on 2026-09-10, ninth run,
  as `section BirthDeathExample`, in fourteen declarations. The computation the
  milestone asks for first comes out as it should: `jumpApply_birthDeath` is
  `A f x = b x * (f (x + 1) - f x) + d x * (f (x - 1) - f x)`, the total rate
  cancelling, so the form of `set:jumpdata` — one rate and one kernel — carries
  two competing rates without distortion and there is no finding against it.

  **There is a finding, and it is about the absorbing state.** Where
  `b x + d x = 0` the two weights are `0 / 0`, the mixture is the *zero measure*,
  and `IsMarkovKernel` fails — at the state the model means to be absorbing.
  `jumpProcessE` repairs the *rate* there, but it cannot repair the *kernel*,
  because the kernel is what the next state is read from and a jump chain has to
  have one. So the absorbing case needs **two** repairs and not one: jump times
  in `ℝ≥0∞` and a convention in the kernel. The convention is `Measure.dirac x`,
  and it is the only one that changes no generator: with both rates `0` the
  operator is `0` at `x` whatever the kernel says. With it,
  `isMarkovKernel_birthDeathKernel` and `jumpApply_birthDeath` carry **no**
  positivity hypothesis, and only that makes the linear chain writable at all.

  The two instances are in the file, each at its own branch. **M/M/1**
  (`mm1Birth`, `mm1Death`, `jumpApply_mm1`) has, by `birthDeathRate_mm1_mem`, a
  rate in `(0, β + δ]`, which is exactly what `jumpProcess_isMPSolution` and
  `exists_unique_of_bounded` ask of a rate — and it does not stop at the
  generator: `mm1_isMPSolution` discharges every hypothesis of that theorem on the
  data and `martingale_compensated_mm1` is an actual `MeasureTheory.Martingale`,
  `f (X t) - ∫_0^t (β (f(X u +1) - f(X u)) + δ 1_{X u ≥ 1} (f(X u -1) - f(X u))) du`.
  **It is the first solution in the file whose generator is state dependent**: the
  Poisson process has a constant rate and a shift for a kernel, so the state sees
  nothing there. The one hypothesis that is not free is the Markov property of the
  kernel, which holds under a condition on the data and is therefore carried as an
  instance hypothesis and discharged by `isMarkovKernel_birthDeathKernel` at the
  call site. **The linear chain** (`linearBirth`,
  `linearDeath`, `jumpApply_linearBirthDeath`) breaks both, and breaks them
  separately: `birthDeathRate_linear_zero` is the absorbing state and
  `not_bddAbove_birthDeathRate_linear` the unboundedness. It is therefore the only
  one of the three examples that exercises the local branch, and its non explosion
  is `mem_nonExplosiveE_of_absorb_or_tendsto_sum`. `ae_mem_nonExplosiveE` alone
  does not reach it: that criterion asks `∀ k, 0 < lam (y k)` along the chain, and
  the extinction event — which has positive probability — violates it. What the
  disjunctive criterion adds is the branch the extinction event falls in, where
  the next jump time is `⊤` (`mem_nonExplosiveE_of_rate_zero`) and no series has
  to diverge at all. **In the file since 2026-09-10, twentieth run**, and it does
  not stop at non explosion: `linearBirthDeath_isLocalMPSolution` discharges every
  hypothesis of `jumpProcess_isLocalMPSolution_of_nonneg` on this data, so the
  linear chain is a **local** solution in Lean and not a description of one. It is
  the first instance in the file for which the bounded theorem is unavailable.
* **The path dependent variant is not a state dependent one.** The Hawkes
  process of the manuscript's `ex:hawkes`: `E = ℕ`,
  `mu (t, ω, ·) = Measure.dirac (ω t⁻ + 1)` and the rate
  `Λ t ω = μ₀ + ∫ s in Set.Ico 0 t, φ (t - s) ∂ω`, a predictable functional of
  the whole past and not a function of `ω t`. It is a jump process in the sense
  of the last item of this milestone and of none of the earlier ones, which is
  why the variant is stated separately; and it never explodes, whatever the mass
  of `φ`, so it is an instance of the **global** statement and not only of the
  local one.

### Bemerkung: die Nichtexplosion des linearen Geburt-Tod-Prozesses, und ein Kontrollbeispiel

*(Frage des Nutzers, 2026-09-10.)* Der Vorschlag war, den linearen
Geburt-Tod-Prozeß **nach oben durch einen reinen Geburtsprozeß** abzuschätzen,
dessen Wert zu fester Zeit geometrisch verteilt und damit f.s. endlich ist.

**Das Argument stimmt, ist aber der teurere Weg.** Es verlangt eine *Kopplung*
zweier Sprungprozesse — in Lean eine gemeinsame Konstruktion auf einem Raum samt
pfadweisem Vergleich — und die geometrische Verteilung des Yule-Prozesses zur
festen Zeit, die selbst erst zu beweisen wäre.

**Was statt dessen genügt und seit dem 2026-09-10, zwanzigster Lauf, bewiesen
dasteht:** `ae_mem_nonExplosiveE_linearBirthDeath`, und der Weg dorthin ist noch
kürzer als hier zunächst angesagt. Zwei Berichtigungen an diesem Absatz, beide am
fertigen Beweis abgelesen:

* **`ae_mem_nonExplosiveE` allein reicht nicht.** Dieses Kriterium verlangt
  `∀ k, 0 < lam (y k)` **längs der Kette**, und das Aussterbeereignis — positiver
  Wahrscheinlichkeit — verletzt es. Zu nehmen ist die disjunktive Fassung
  `ae_mem_nonExplosiveE_jumpMeasure_of_absorb_or`; auf dem Aussterbeereignis
  greift der absorbierende Zweig, wo die nächste Sprungzeit `⊤` ist und gar keine
  Reihe zu divergieren braucht.
* **Eine Fallunterscheidung nach den Regimen `δ ≥ β` und `β > δ` gibt es
  nicht.** Sie wäre eine Aussage über die Rekurrenz beziehungsweise die Drift der
  eingebetteten Irrfahrt und damit selbst ein Stück Wahrscheinlichkeitstheorie.
  Gebraucht wird nur, daß die Kette **Nachbarschritte** macht: `y k ≤ y 0 + k`
  (`le_add_of_step_le_succ`), also dominieren die reziproken Raten einen Schwanz
  der harmonischen Reihe (`not_summable_inv_birthDeathRate_linear`). Auf dem
  Zweig, auf dem etwas zu divergieren hat, ist der Nachweis damit
  **deterministisch**; probabilistisch ist allein die Aussage, daß die Kette
  Nachbarschritte macht, und die kommt aus dem Kern
  (`ae_le_succ_birthDeathKernel`, `ae_forall_step_comp_chainKernel`).

**Eine Falle, die auf Papier unsichtbar ist.** „Zu fester Zeit geometrisch
verteilt, also f.s. endlich, also keine Explosion" ist so **zirkulär**: um von
`X t` zu sprechen, muß der Prozeß bei `t` bereits definiert sein. Über einem
Zustandsraum **mit Friedhof** ist der Ausweg `∑ k, P (X t = k) = 1` für den
*minimalen* Prozeß, also „es entweicht keine Masse nach unendlich".

**Dieser Zustandsraum hat keinen Friedhof, und dort ist der Ausweg zu.**
`tsum_jumpLaw_eq_one` (2026-09-10, dreiundzwanzigster Lauf) sagt, daß
`∑ k, P (X t = k) = 1` hier **ohne jede Voraussetzung** gilt: jenseits einer
Explosionszeit liefert `stepIndex` den Müllwert `0`, der Pfad sitzt am
Anfangszustand seiner eigenen Kette und ist immer noch ein Zustand von `E`. Die
Gleichung ist damit ein Satz über die Konstruktion und **nicht** die
Nichtexplosion. An derselben Stelle bricht auch die Mastergleichung selbst — keine
von `A` erzeugte Gleichung beschreibt eine Rückkehr aus dem Unendlichen —, und
deshalb ist die Nichtexplosion eine **Voraussetzung** von
`jumpMeasure_masterEquation_of_ae_nonExplosive` und keine Folgerung daraus. Der
zweite Weg liefert auf dieser Konstruktion die eindimensionale Verteilung und nur
sie; die Nichtexplosion, die er braucht, kommt vom ersten. Was ihn zu einem
eigenen Weg zur Nichtexplosion machen würde, ist der Friedhofszustand, und der
steht als benannter Punkt oben in Meilenstein 4.

**Als Akzeptanzbeispiel ist die Rechnung dennoch wertvoll, und sie steht.** Der
Yule-Prozeß (`b x = β * x`, `d ≡ 0`) hat eine geschlossene eindimensionale
Verteilung — von `1` gestartet ist `X t` geometrisch mit Parameter `exp (−β t)` —,
und ein Leser prüft das Ergebnis der Konstruktion gegen etwas Bekanntes, so wie
beim Poissonprozeß gegen `ProbabilityTheory.poissonMeasure`. Das ist
`jumpLaw_yule_succ` und `jumpLaw_yule_zero` (2026-09-11, vierter Lauf). Die
Rechnung gehört zu Punkt 5 und steht **nach** `jumpProcess_isLocalMPSolution`:
sie prüft die Konstruktion, sie trägt sie nicht.

**Der gemessene Vergleich, Stand 2026-09-11, fünfter Lauf.** Bis zum
zweiundzwanzigsten Lauf des 2026-09-10 stand hier die *Behauptung*, die Reihe sei
der billigere Weg. Was davon gezählt ist (`scripts/_citations/count_yule.py`,
`scripts/_citations/count_lyapunov.py`,
`scripts/_citations/count_yule_master.py`, `scripts/_citations/count_yule_law.py`,
`scripts/_citations/count_coupling.py`,
`scripts/_citations/count_posrate_transfer.py` und
`scripts/_citations/count_bd_master.py`):

| Weg | Deklarationen | Codezeilen | Stand |
| --- | --- | --- | --- |
| Reihe längs der eingebetteten Kette | 12 (`section LinearBirthDeath`) + 1 (`ae_mem_nonExplosiveE_yule`) | 236 Zeilen mit Dokumentation | **fertig** |
| Übergang über die gehobene Rate | 3 | 57 Codezeilen | **fertig** |
| Mastergleichung, allgemein | 18 (`section YuleProcess`, ohne die Yule-Instanz) + 1 (`jumpMeasure_hasDerivWithinAt_integral_Ici`) | 278 | **liefert die Verteilung, nicht die Nichtexplosion** |
| Mastergleichung, auf der Yule-Rate | 3 (Brücke) + 1 (`yule_masterEquation`) | 42 + 61 = 103 Codezeilen | **fertig** |
| Mastergleichung, auf der linearen Geburt-Tod-Rate | 3 (Erzeuger) + 1 (Integrationsschritt) + 1 (`linearBirthDeath_masterEquation`) | 48 + 26 + 75 = 149 Codezeilen | **fertig** |
| Lösung der Mastergleichung, bis zur Verteilung | 8 (Analysis) + 5 (Yule-Instanz) | 182 + 71 = 253 Codezeilen | **fertig, nur im reinen Geburtsfall** |
| Lyapunov, pfadweise Form | 4 (Kriterium) + 3 (Geburt-Tod-Instanzen) | 85 + 36 = 121 Codezeilen | **fertig** |
| Lyapunov, Erzeugerform | 12 (Kriterium) + 4 (Geburt-Tod-Instanzen) | 258 + 52 = 310 Codezeilen | **fertig** |
| Lyapunov über die gehobene Rate | 3 | 67 Codezeilen | **fertig** |
| Kopplung, Ratendominierung | 2 + 1 | 13 + 8 = 21 Codezeilen | **die Dominierung steht, sie zeigt in die andere Richtung** |

(Die ganze `section Lyapunov` sind 500 Codezeilen, 761 mit Dokumentation; die
ganze `section YuleMasterEquation` 105 Codezeilen, 175 mit Dokumentation; die
ganze `section YuleLaw` 255 Codezeilen, 395 mit Dokumentation; die ganze
`section RateMonotone` 23 Codezeilen, 82 mit Dokumentation; die ganze
`section LinearBirthDeathMasterEquation` 151 Codezeilen, 220 mit Dokumentation.
Die drei Deklarationen des Übergangs bilden keinen eigenen Abschnitt und stehen
bei den Aussagen, von denen sie handeln.)

**Der Reihenweg kommt an der Mastergleichung an, und der Übergang kostet 57
Zeilen.** Bis zum vierten Lauf des 2026-09-11 stand in dieser Tabelle, der
Reihenweg erreiche sie nicht: die Gleichung ist in der *gehobenen* Rate
geschrieben, und die Nichtexplosion der gehobenen Rate folgt nicht formal aus
der der Rate selbst. `ae_mem_nonExplosiveE_posRate` schließt die Lücke. Die
Voraussetzung wird dabei in **einem** der beiden Zweige gebraucht und ist im
anderen wertlos, und zwar aus demselben Grund, aus dem der Übergang nötig ist:
an einem absorbierenden Zustand divergiert die Reihe `∑ ξ_k / lam (y k)` wegen
eines einzigen Terms `⊤`, und die Hebung ersetzt genau diesen Term durch das
endliche `ξ_k`. Bezahlt wird statt dessen mit `chain_const_of_absorb` — hinter
dem ersten absorbierenden Index steht die Kette still, die gehobene Rate ist
dort `1`, und die Wartezeiten allein tragen die Divergenz.

**Und die Mastergleichung trägt den Todesterm, aber nicht ihre Lösung.**
`linearBirthDeath_masterEquation` kostet 149 Codezeilen gegen die 103 des reinen
Geburtsfalls, und der Zuwachs sitzt im Erzeuger: drei Terme statt zweier, weil
der Zustand `n+1` auch von `n+2` aus durch einen Sterbeschritt betreten wird. Die
**Lösung** aber überträgt sich nicht, und das ist keine Frage des Aufwands: mit
dem dritten Term ist das System ein unendliches gekoppeltes System und keine
Kette skalarer Gleichungen mehr, so daß die Induktion über die Stufe in
`eq_yuleDensity_of_masterEquation` keine Entsprechung hat. Die 253 Zeilen der
Lösung stehen damit weiter nur für den reinen Geburtsfall.

**Der Kopplungsweg kostet 21 Zeilen und kommt damit nicht an.** Die Dominierung,
die diese Konstruktion trägt, ist die in der *Rate* an festem Stichprobenpunkt,
und sie ist billig — `mem_nonExplosiveE_of_rate_le`, 13 Codezeilen. Sie
dominiert aber die falsche Größe: die Gesamtrate des Geburt-Tod-Prozesses ist
`(β + δ) x` und damit **größer** als die Yule-Rate `β x`, weil ein Sterbeschritt
die Gesamtrate hebt. Was der Weg meint, ist die Dominierung der *Zustände*, und
zwei Prozesse, deren Zustände verglichen werden, teilen sich keine eingebettete
Kette. Die Kopplung ist damit ein **neues Maß auf einem gemeinsamen Raum** und
keine Ungleichung zwischen Raten — das ist die benannte Bruchstelle, und sie
steht fest, bevor Zeilen dafür ausgegeben sind.

**Was die Lösung der Gleichung kostet, und wo das Geld hingeht.** Die
Mastergleichung *aufzustellen* kostet 103 Codezeilen, sie zu *lösen* noch einmal
253 — die Gleichung ist also die kleinere Hälfte. Von den 253 sind 182 frei von
der Sprungkonstruktion: die Eindeutigkeit der skalaren linearen Gleichung (30),
die Ableitung der geschlossenen Formel (34) und die Induktion über die Stufe
(84). Nur 34 Zeilen sind über `jumpLaw` und 71 sind Einsetzen der Yule-Daten.
Der teuerste Einzelposten ist der **Aufstieg von der integrierten zur
differentiellen Form**: die rechte Seite enthält die Unbekannte, ihre Stetigkeit
ist also nicht vorauszusetzen, sondern über Meßbarkeit und Beschränktheit erst zu
erschließen. Das ist der Grund, aus dem `eq_of_masterEquation` eine meßbare und
beschränkte rechte Seite verlangt und keine stetige, und es ist derselbe Grund,
aus dem `measurable_jumpLaw` überhaupt gebraucht wird.

**Der vierte Weg ist der billigste, und er ist der einzige allgemeine.** 121
Codezeilen gegen 236 der Reihe, und was dabei herauskommt, ist nicht dasselbe:
die Reihe beweist die Nichtexplosion **einer** Kette, das Kriterium die jeder
Geburt-Tod-Kette mit `b x + d x ≤ C * x`, und der Beweis der linearen Instanz ist
danach die Konstante `C = β + δ` und sonst nichts. Der Reihenweg ist damit, wie
angesagt, ein Sonderfall und kein gleichrangiger Weg — aber es ist der Sonderfall
des Kriteriums und nicht der der Nachbarschritte: die Nachbarschritte braucht das
Kriterium auch, es liest sie nur an *einer* Stelle
(`ae_le_succ_birthDeathKernel`) statt an dreien.

**Und die Erzeugerform kostet das Zweieinhalbfache des pfadweisen Kriteriums,
311 gegen 121 Codezeilen.** Das ist der Preis dafür, daß der Todesterm frei wird:
die pfadweise Form ist eine Iteration an einem einzelnen Pfad und braucht kein
Maß, die Erzeugerform ist eine Integralabschätzung längs der Kette und ein
Grenzübergang. Wer nur `b x + d x ≤ C * x` braucht, nimmt die pfadweise Form; wer
eine Sterberate will, die schneller wächst als die Geburtsrate — und das ist der
Normalfall eines rekurrenten Modells —, zahlt die 190 Zeilen. Der Vergleich
zwischen beiden ist damit dieselbe Frage wie der zwischen Reihe und Kriterium,
eine Stufe höher: was zusätzlich bewiesen wird, ist nicht dieselbe Aussage.

**Und die Voraussetzungen sind am Ende dieselben.** Von den 311 Zeilen sind 62
allein dafür da, die Endlichkeit des Mittelwerts unter der Anfangsverteilung
wieder loszuwerden — die Meßbarkeit des Explosionsereignisses und das Bedingen
auf den Startzustand. Sie sind gut angelegt: ohne sie stünde neben der stärkeren
Aussage eine zusätzliche Voraussetzung, und ein Vergleich zweier Sätze, die nicht
dasselbe voraussetzen, mißt nichts.

Der Zuwachs von 126 auf 278 Zeilen sind genau die fünf neuen Deklarationen, 152
Codezeilen: der Wegfall der Schranke an die Rate
(`jumpMeasure_masterEquation_of_ae_nonExplosive` mit den drei Aussagen, auf denen
er ruht) und `tsum_jumpLaw_eq_one`, der Befund, der den Zweck dieses Weges neu
bestimmt.

Dazu kommen für jeden Weg die Voraussetzungen, die er teilt: die Reihe ruht auf
`ae_mem_nonExplosiveE_jumpMeasure_of_absorb_or` und dem Divergenzkriterium
darunter, die Mastergleichung auf `jumpMeasure_integral_sub_eq_intervalIntegral`
und damit auf der ganzen Rückwärtsgleichung.

**Was die Zahlen bisher sagen, und was sie nicht sagen.** Die Reihe ist für
*diese* Rate billiger, aber nicht aus dem Grund, den man vermutet: ihr Beweis ist
auf dem Zweig, auf dem etwas zu divergieren hat, **deterministisch**, weil die
Kette Nachbarschritte macht. Genau diese Eigenschaft hat eine allgemeinere Rate
nicht. Die Mastergleichung dagegen benutzt von der Rate nur, daß der Erzeuger
einen Indikator auf eine endlich getragene Funktion abbildet
(`jumpApply_yule_indicator`), und das gilt für jede Sprungrate mit
Nachbarschaftskern. **Für eine allgemeinere Ratenfunktion ist daher die
Mastergleichung der bessere Weg**, und die Reihe ist der billigere für
Ratenfunktionen mit einer Wachstumsschranke längs der Kette.

**Das Urteil, berichtigt im dreiundzwanzigsten Lauf.** Der Satz oben gilt für
das, wofür die Mastergleichung gebaut ist — die **eindimensionale Verteilung**.
Als Weg zur **Nichtexplosion** ist sie auf dieser Konstruktion überhaupt kein
Weg: `tsum_jumpLaw_eq_one` zeigt, daß ihre Schlußzeile leer ist, solange `E`
keinen Friedhof hat, und `jumpMeasure_masterEquation_of_ae_nonExplosive` verlangt
die Nichtexplosion als Voraussetzung. Die Reihe ist damit auf dieser Konstruktion
nicht der billigere, sondern der **einzige** fertige Weg zur Nichtexplosion, und
der Vergleich der beiden ist ein Vergleich zweier verschiedener Aussagen. Was das
Urteil nicht ändert: die Abschwächung der Voraussetzung ist beim
Mastergleichungsweg gelungen, ohne die Rate anzufassen — es reicht, daß der
Erzeuger *einen Indikator* beschränkt abbildet (`abs_jumpApply_truncRate_le`),
und diese Eigenschaft hat jeder Sprungkern mit endlichem Träger.

**Was Mathlib jedem Weg gab und was fehlte.** Der Reihe: `Real.not_summable_natCast_inv`,
`summable_nat_add_iff` und `Summable.of_nonneg_of_le` — die harmonische Reihe und
der Vergleichssatz, alles vorhanden (`not_summable_inv_birthDeathRate_linear`).
Der Mastergleichung:
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, `HasDerivAt.exp`,
`integral_indicator_one` — vorhanden; **nicht** vorhanden ist die lineare
Differentialgleichung erster Ordnung, siehe
`eq_exp_add_integral_of_hasDerivWithinAt` oben. Der Kopplung: nichts geprüft, weil
sie nicht angefangen ist.

### Bemerkung: was eine Domäne mit kompaktem Träger ändern würde

*(Frage des Nutzers, 2026-09-10. Sie ist hier festgehalten, weil sie erklärt,
wozu die Lokalisierung überhaupt da ist — nicht, weil dieser Weg gegangen werden
soll.)*

Ließe man in `A` nur Funktionen mit kompaktem Träger zu — auf `E = ℕ` also
endlichem Träger —, so kehrte sich der Aufwand um.

**Die Existenz würde billig.** Für `f` mit endlichem Träger ist `A f` außerhalb
von `supp f ∪ (supp f ± 1)` gleich null, also selbst endlich getragen und damit
**beschränkt**, obwohl `lam` es nicht ist. Dann ist
`f (X t) − ∫₀ᵗ A f (X s) ds` auf beschränkten Intervallen beschränkt, und der
ganze Lokalisierungsapparat — `rateSup`, `rateTime`,
`isLocalizingSequence_rateTime`, `martingale_stoppedProcess` — entfiele.

**Die Eindeutigkeit würde schwer**, und zwar aus zwei Gründen. Erstens ist `A`
auf dieser Domäne **unbeschränkt**: für `f = indicator {n}` ist
`‖A f‖ = max (β n) (δ n) → ∞`, also trägt die Picard-Iteration von
`exists_unique_of_bounded` nicht mehr und man wäre bei Hille--Yosida, was
`rem:noch1` des Manuskripts ausschließt. Zweitens, und das ist keine technische
Hürde: bei einem **explodierenden** Prozeß hat das Martingalproblem über dieser
Domäne *mehrere* Lösungen — nach der Explosionszeit darf man neu starten, und
Testfunktionen mit endlichem Träger sehen das nicht. Eindeutigkeit über der
Domäne mit kompaktem Träger ist daher gleichwertig zur **Nichtexplosion**, der
klassische Punkt bei minimalen Ketten. Für den linearen Geburt-Tod-Prozeß mit
`β, δ > 0` ist sie erfüllt (`∑ 1/(β n)` divergiert), aber ihr Beweis wäre dann
der Kern der Sache statt eines Nebenprodukts.

**Warum dieser Weg nicht gegangen wird.** Das Manuskript hält bei `:333` fest,
daß es auf einem allgemeinen polnischen Raum **kein `C_c(E)`** gibt; die ganze
Konstruktion hier steht über bloßem `[MeasurableSpace E]`. Die Domäne mit
kompaktem Träger wäre ein Rückschritt in der Allgemeinheit für einen Gewinn, der
nur bei diskretem `E` eintritt. Wer sie dennoch untersuchen will, hat mit
`mem_nonExplosiveE_iff_tsum_eq_top` und `ae_mem_nonExplosiveE` (2026-09-10) die
Nichtexplosion schon bewiesen daliegen — es wäre eine zweite, unabhängige Route
zum selben Beispiel, und der Vergleich beider wäre für sich lehrreich.

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
  `κ`. Prove that `mpFamily A q c` carries a shift system when the clock is
  shift invariant, with `κ` the compensator up to `r`.
* `restart`: let `X` solve the martingale problem for `𝓧°` with respect to `𝓖`,
  let `r : ι`, and let `Z ≥ 0` be bounded, `𝓖 r`-measurable with `𝔼[Z] = 1`.
  Then the law of `X (r + ·)` under `Z • P` solves the martingale problem for
  `𝓧° r`. The proof is the definition of a shift system plus the martingale
  property; it is four lines and everything in Milestone 6 rests on it.
* `restart_canonical`, the special case `Ω = F`, `X = id`, where the conclusion
  reads `(Z • P).map (θ r) ∈ MPSolutions (𝓧° r)`.

**Acceptance examples.**

* **The shifted problem of the manuscript's `ex:shiftXA`.** For the family
  `mpFamily A q c X` with a shift invariant clock, the shifted family `𝓧° r` is
  again `mpFamily A q c X` up to the `𝓕° r`-measurable constant `κ` = the
  compensator up to `r`. Instantiated at the Poisson process of Milestone 4 and
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

Hypotheses: a shift system, a determining set for every `𝓧° r`, and uniqueness
of the one dimensional distributions of the shifted problems.

* `isMarkov_of_unique_onedim`: every solution is Markov, in general time
  inhomogeneously — for `f` bounded measurable and `r, t : ι`,
  `𝔼[f (X (r + t)) | 𝓖 r] =ᵐ 𝔼[f (X (r + t)) | X r]`.
* `subsingleton_mpSolutions_of_unique_onedim`: when `ι` is linearly ordered, the
  set of solutions with a given initial law has at most one element.
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

**Acceptance examples.**

* **The two state chain of Milestone 4, all the way through.** `E = {0,1}`,
  `lam ≡ 1`, `mu x = Measure.dirac (1 - x)`. `exists_unique_of_bounded` supplies
  uniqueness of the one dimensional distributions for every initial law, so
  `isMarkov_of_unique_onedim` must return the Markov property and
  `subsingleton_mpSolutions_of_unique_onedim` uniqueness, with transition
  operator `T t = exp (t • A)` — which is the `T t f x = ∫ f (ω t) ∂(P x)` of
  `isStrongMarkov` computed. Every hypothesis of the milestone is discharged by
  Milestone 4 on this instance, so it is the one that checks the interfaces
  between the two match.
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
  `Matrix.vecMulVec` (`Data/Matrix/Mul.lean:616`) for the outer product,
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
  `ProbabilityTheory.IsStable 𝓕 (fun Z ↦ Martingale Z 𝓕 P ∧ ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (Z · ω) (Set.Ici t) t)`.
  The conjunction is what is stable, because right continuity is preserved by
  stopping and is the hypothesis under which the martingale half holds. Then
  `ProbabilityTheory.IsStable.locally` of
  `Mathlib/Probability/Process/LocalProperty.lean` gives at once that a stopped
  local martingale is a local martingale, and `IsStable.locally_and_iff` splits
  the conjunction again; so `IsLocalMPSolution` of Milestone 2 is preserved by
  stopping without any further work, and no localizing sequence is constructed
  by hand. Mathlib has the localization scaffolding but nothing about the
  martingale property in it: `Submartingale.stoppedProcess` of
  `Mathlib/Probability/Martingale/OptionalStopping.lean` is stated for
  `Filtration ℕ` and real valued processes, and `Locally` is never instantiated
  at a martingale. The proof is the first item applied at the bounded stopping
  times `σ ⊓ τ`, and the same argument gives the submartingale form.
* Doob's inequalities in continuous time. The supremum
  `fun ω ↦ ⨆ t ∈ Set.Iic T, ‖Y t ω‖` is measurable because right continuity
  makes it the supremum over `Set.Iic T ∩ D`; state that reduction as a lemma of
  its own. Then `MeasureTheory.maximal_ineq_of_rightContinuous`, the continuous
  time form of `MeasureTheory.maximal_ineq` for a non-negative right continuous
  submartingale, and `Submartingale.eLpNorm_iSup_le`, Doob's `Lᵖ` inequality
  `eLpNorm (fun ω ↦ ⨆ t ∈ Set.Iic T, Y t ω) p P ≤ (p / (p - 1)) * eLpNorm (Y T) p P`
  for `1 < p < ∞` and `Y` a non-negative submartingale. Mathlib has neither, and
  the `Lᵖ` inequality is to be proved for `Filtration ℕ` from `maximal_ineq`
  first and then transferred by the same approximation. The form the manuscript
  uses is the corollary for a right continuous martingale `X`, applied to the
  non-negative submartingale `‖X ·‖`; state `Martingale.measure_iSup_norm_le` and
  `Martingale.eLpNorm_iSup_norm_le` for it.
* Submartingale regularization, which Mathlib does not have, although the
  ingredient does. For a submartingale `Y` indexed by `ι`, the restriction to
  `D` has almost surely finite one sided limits along `D` at every point. The
  input is the Doob upcrossing estimate, in Mathlib as
  `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
  and `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part`, together
  with `upcrossings_lt_top_iff`. State `Submartingale.exists_rightLim_along` and
  `Submartingale.exists_leftLim_along`, phrased through `Function.leftLim` and
  `Function.rightLim` as in the roadmap **SkorokhodSpace**.
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
  `RemyDegenne/brownian-motion` (Apache-2.0) carries a development of this for
  quasimartingales in `BrownianMotion/StochasticIntegral/Quasimartingale/`, in
  the shape described above and with four remaining gaps. An implementer may
  consult it and, the licence permitting, draw on it with its copyright header
  preserved; nothing here should be accepted merely because it matches that
  file.
* `IsRegularizingClass Φ X 𝓧`: a set `Φ` of bounded continuous functions on `E`
  such that for every `f ∈ Φ` there are `Y ∈ 𝓧` and a `StronglyAdapted`
  `𝕂`-valued `C`
  with `f (X t) = Y t + C t` almost surely for every `t`, with `C` almost surely
  having one sided limits along `D`, and with `C` right continuous in `L¹`.
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
* `exists_cadlag_modification_of_isRegularizingClass`: if `Φ` is a regularizing
  class containing a countable subset that separates points, `Φ` is separating
  in the sense of the roadmap **WeakConvergence**, and `X` satisfies compact
  containment, then `X` has a modification with paths in the càdlàg space.
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
  the second half of `IsCadlagPath`, assumed by Ethier–Kurtz here anyway —
  supplies.
* `isQuasiLeftContinuous_of_isRegularizingClass`, the abstract form of
  Ethier–Kurtz, Theorem 4.3.12, with no operator and no compensator of any
  special shape. Let `Φ` be a regularizing class for `(X, 𝓧)` with `X` càdlàg,
  let `Φ` be separating in the sense of the roadmap **WeakConvergence**, and let
  the compensator `C` attached to each `f ∈ Φ` be almost surely right continuous
  and **left continuous in `L¹` along stopping times**: for every nondecreasing
  sequence `τ` of stopping times, with `τ' = ⨆ n, τ n`, and every `t`,
  ```
  Tendsto (fun n ↦ ∫ ω, ‖C (min (τ' ω) t) ω - C (min (τ n ω) t) ω‖ ∂P)
    atTop (𝓝 0) .
  ```
  Then `IsQuasiLeftContinuous X 𝓕 P`. The proof is four steps and each of them
  is a named item already, here or in **WeakConvergence**. Optional sampling at
  the bounded stopping times `min (τ n) t ≤ min τ' t`, the first item of this
  milestone, gives
  `Y (min (τ n) t) =ᵐ[P] P[Y (min τ' t) | (hτ n).measurableSpace]`. The
  decomposition `f (X t) = Y t + C t` of `IsRegularizingClass` is then needed at
  a stopping time and not only at each fixed `t`; it upgrades because both sides
  are right continuous and it holds on the countable dense `D`, and that upgrade
  is a lemma of `IsRegularizingClass` of its own, because the càdlàg theorem
  uses the decomposition `t` by `t` and this theorem cannot. Substituting it,
  ```
  f (X (min (τ n) t)) =ᵐ[P] P[f (X (min τ' t)) | (hτ n).measurableSpace]
      - P[C (min τ' t) - C (min (τ n) t) | (hτ n).measurableSpace] ,
  ```
  whose second term tends to `0` in `L¹` by the hypothesis on `C` and
  conditional Jensen. The first term is handled by **Lévy's upward theorem**,
  `MeasureTheory.tendsto_ae_condExp` and `MeasureTheory.tendsto_eLpNorm_condExp`
  of `Mathlib/Probability/Martingale/Convergence.lean` (`:426`, `:439`), read at the filtration
  `n ↦ (hτ n).measurableSpace`, which is a `Filtration ℕ` by
  `MeasureTheory.IsStoppingTime.measurableSpace_mono` and
  `MeasureTheory.IsStoppingTime.measurableSpace_le` of
  `Mathlib/Probability/Process/Stopping.lean` (`:464`, `:477`). Both Lévy
  statements are stated for a real valued
  integrand and a finite measure — they sit in `section L1Convergence`, whose
  variable block at `Convergence.lean:243` is `[IsFiniteMeasure μ] {g : Ω → ℝ}` —
  so the `𝕂` valued case is the two components.
  The left side converges to `f ∘ L` with
  `L ω = limUnder atTop (fun n ↦ X (τ n ω) ω)`, which exists because the paths
  are càdlàg and `τ` is monotone, and which is measurable for
  `⨆ n, (hτ n).measurableSpace`. So
  `f ∘ L = P[f (X (min τ' t)) | ⨆ n, (hτ n).measurableSpace]` for every
  `f ∈ Φ`, and `IsSeparating.ae_eq_of_forall_condExp_eq` of **WeakConvergence**
  Milestone 1 gives `L =ᵐ[P] X (min τ' t)`. That last step is the one that also
  closes `exists_cadlag_modification_of_isRegularizingClass`, and being
  separating is the only hypothesis on `Φ` the two theorems share: no countable
  subset separating the points of `E` is used here, and no compact containment.
* `isQuasiLeftContinuous_of_isMPSolutionFor`, the classical instance
  (Ethier–Kurtz, Theorem 4.3.12). For `A ⊆ Cb(E) × Bdd(E)` with separating
  domain and a solution `X` with càdlàg paths, `IsQuasiLeftContinuous X 𝓕 P`
  **provided the clock has no atoms**, `∀ u, q {u} = 0`. The compensator is
  `C t = ∫ u in Clock.interval q c ⊥ t, g (X u) ∂q`, so
  `‖C (min τ' t) - C (min (τ n) t)‖ ≤ ‖g‖ * q (Clock.interval q c (min (τ n) t) (min τ' t))`,
  the sets on the right decrease to the single point `min τ' t`, and continuity
  from above of the clock on `Clock.interval q c ⊥ t`, which has finite measure,
  finishes it.
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
  every hypothesis of `isQuasiLeftContinuous_of_isMPSolutionFor` except `hQ` —
  `IsProbabilityMeasure P`, the bounds and the continuity of `hA`,
  `IsSeparating (Prod.fst '' A)` and the almost sure càdlàg paths — because
  without them the example is empty: for `A = ∅` the family `mpFamily A Q c X`
  is empty, `IsMPSolution` holds of every measure, and any process that fails
  quasi-left-continuity settles the statement while saying nothing about atoms.
  `IsSeparating (Prod.fst '' A)` is what forces `A ≠ ∅`, since on `Bool` the
  empty class does not separate `Measure.dirac true` from `Measure.dirac false`.
  The witness is built in the namespace `AtomWitness`: `coinMeasure`, the fair
  coin `2⁻¹ • (Measure.dirac true + Measure.dirac false)` on `Bool` with
  `coinMeasure {true} = 2⁻¹`; `atomClock u`, the clock whose index σ-algebra is
  `⊤` and whose measure is `Measure.dirac u`, with
  `atomClock_apply_singleton : (atomClock u).q {u} = 1`, so that the atom is
  there and every down-set is measurable for free, together with
  `not_isAtomless_atomClock : ¬ (atomClock u).IsAtomless`, which is what binds
  the sharpness to the hypothesis it is sharp against: without it the example
  might still satisfy `hQ` of `isQuasiLeftContinuous_of_isMPSolutionFor` and
  contradict that theorem instead of delimiting it. It is `measure_mono` from
  the singleton into the degenerate interval `{v | u ≤ v ∧ v ≤ u}`;
  `coinProcess u t ω = if u ≤ t then ω else false`,
  the path over `Ω = E = Bool`, where the coin is both the sample point and the
  state; `isCadlagPath_coinProcess`, which holds for every `u` and every `ω`
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
  `p = 2`, `Martingale.eLpNorm_iSup_norm_le` must give
  `𝔼[(⨆ t ∈ Set.Iic T, |Y t|) ^ 2] ≤ 4 * 𝔼[Y T ^ 2] = 4 * T`. The measurability
  of the supremum here is exactly the reduction to `Set.Iic T ∩ ℚ` that the
  milestone states as a lemma of its own; without right continuity the supremum
  over an uncountable set need not be measurable, which is why that reduction is
  an item and not a step.
* **The coin at an atom, which separates the two theorems of this milestone.**
  `E = Bool`, `q = Measure.dirac 1`, and the solution that flips a fair coin at
  time `1` and is constant on either side. It **has** a càdlàg modification —
  `exists_cadlag_modification_of_isRegularizingClass` asks nothing of the clock
  — and it is **not** quasi-left-continuous, since `X (s n) → X 1⁻ ≠ X 1` with
  probability `1/2` for any `s n ↑ 1`. This is
  `not_isQuasiLeftContinuous_of_atom`, and the same process with `q = volume` is
  quasi-left-continuous by `isQuasiLeftContinuous_of_isMPSolutionFor`. The pair
  fixes where atomlessness is a hypothesis and where it is not.
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

* `PContinuous ψ X`, for `ψ : F → ℝ` Borel: there is a Borel `C` with
  `P {X ∈ C} = 1` such that `ψ` is continuous at every point of `C` along
  convergent sequences with limit in `C`.
* `mpSolution_of_tendsto`: assume `𝓧` is canonical for `X` with determining set
  `𝓩°`, and that for every `Y ∈ 𝓧` with canonical version `Y°`, every `t ∈ D`,
  `s ∈ D ∩ Iic t` and `Z ∈ 𝓩° s`:
  (a) the real random variables `Y° r (X n)` for `r ∈ D ∩ Iic t` and
  `(Y° t - Y° s) * Z (X n)` converge in distribution to their counterparts under
  `X`; (b) `{Y° r (X n) | r ∈ D ∩ Iic t, n}` is uniformly integrable;
  (c) `𝔼^{P n}[(Y° t (X n) - Y° s (X n)) * Z (X n)] → 0`.
  Then `P[Y t | 𝓕 s] =ᵐ Y s` for all `s ≤ t` in `D`; and when `ι` carries the
  order topology with `D` countable dense, `D` contains the greatest element if
  there is one, and every `Y ∈ 𝓧` is right continuous, `P` is a solution.
  State hypothesis (a) in this form. It carries no topology on `F`: it is a
  statement about finitely many real random variables, and the versions where
  `F` is metrizable and the coordinates are continuous are corollaries.
* `mpSolution_of_tendsto_of_pContinuous`: the corollary in which (a) is replaced
  by `X n → X` weakly on a separable metric `F` together with `P`-continuity of
  `Y° t` and `Y° t * Z`. Uses the continuous mapping theorem of the roadmap
  **WeakConvergence**.
* `mpSolution_of_tendsto_augmented`: the corollary in which the coordinates at
  finitely many exceptional times are adjoined to the path space, so that a
  functional discontinuous at those times becomes continuous. It is the previous
  statement on a larger space and costs nothing once that one is proved.
* Uniform integrability of the limit family under `P`, as a separate lemma; it
  is what makes the passage from `D` to the whole index work.

**Acceptance examples.**

* **The rescaled Markov chain of the manuscript's `ex:invariance`.**
  `E = ℝ^d`, `q n = (1/n) * ∑ k ≥ 1, δ (k/n)` with the optional convention,
  `X n t = Ξ n ⌊n * t⌋` for a chain with one step kernel `P n`, and
  `Y n t = f (Ξ n ⌊n t⌋) - ∑ j < ⌊n t⌋, (P n f - f) (Ξ n j)` — the Doob
  decomposition read along the embedded grid. Hypothesis (c) of
  `mpSolution_of_tendsto` is that the tested increments vanish, and it holds
  because each `Y n` is an exact martingale; (a) and (b) are the convergence and
  uniform integrability of finitely many real variables. The conclusion is that
  the limit solves the martingale problem for the limiting operator. This is the
  invariance principle, and it instantiates every hypothesis of the milestone at
  once.
* **Hypothesis (a) is about real random variables and carries no topology.** In
  the example above the path space `F` is `D ι E` and the functionals
  `Y° t` are evaluations, but the statement of (a) never mentions `F`'s
  topology: it asks for convergence in distribution of `Y° r (X n)` and of
  `(Y° t - Y° s) * Z (X n)`, finitely many real variables at a time. The
  acceptance test is that `mpSolution_of_tendsto` can be applied with `F` a bare
  measurable space, and that `mpSolution_of_tendsto_of_pContinuous` — which does
  need a separable metric `F` — is derived from it and not the other way round.
* **`PContinuous` is not continuity**, and the manuscript's
  `ex:atomicdiscontinuity` is why. The evaluation `ψ = π 1` on `D ℝ ℝ` is
  discontinuous at every path jumping at `1`; it is nevertheless `PContinuous`
  for every `P` with `P {ω | ω 1⁻ = ω 1} = 1`, the certifying set `C` being that
  event. For a limit law charging paths that jump at `1` — the generic case when
  the clock has an atom there — no `C` works, and
  `mpSolution_of_tendsto_augmented` is what remains: adjoining the coordinate at
  `1` to the path space makes the functional continuous. This pair fixes the
  division of labour between the two corollaries.

## Milestone 11: the Skorokhod instances

Now `ι = [0,∞)`, `E` Polish, and paths in the càdlàg space `D ι E` of the
roadmap **SkorokhodSpace**.

* `mpSolution_of_tendsto_cadlag`: let `A ⊆ Cb(E) × Cb(E)` and let `A n` be
  relations between bounded measurable functions such that for every `(f,g) ∈ A`
  there are `(f n, g n) ∈ A n` with `‖f n - f‖ → 0` and `‖g n - g‖ → 0`. If `X n`
  solves the martingale problem for `A n` with càdlàg paths and `X n → X` in
  `D ι E`, then `X` solves the martingale problem for `A`. Derive it from
  Milestone 10, taking for `D` the set of times at which the limit has no fixed
  discontinuity.
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
  `⨆ n, 𝔼[⨆ t ∈ Set.Iic T ∩ D, |Y n t - f (X n t)|] < ε` and
  `⨆ n, 𝔼[eLpNorm (Set.Iic T).indicator (Z n) p] < ∞` for some `1 < p ≤ ∞`.
  Then for every `f` in the sup-norm closure of the approximable functions the
  laws of `postcomp f ∘ X n` are tight in `D ι ℝ`, and the laws of
  `(f 1, …, f k) ∘ X n` are tight in `D ι (Fin k → ℝ)`. The `𝕂`-valued case is
  the real one applied to `Re f` and `Im f` together with the `Fin k` form.
  This is where the continuous time Doob inequalities of Milestone 9 are used.
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
* `tendsto_of_isRelativelyCompact_of_unique`: with uniqueness from Milestone 6
  or Milestone 8, relative compactness upgrades to convergence.
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
