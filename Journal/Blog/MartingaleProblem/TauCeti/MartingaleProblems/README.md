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
* `isMPSolutionFor_iff_forall_fdd`: `X` solves the martingale problem for `A` if
  and only if for all `s ≤ t`, all finite families `t 1 ≤ ... ≤ t n ≤ s` and all
  bounded measurable `h 1, ..., h n`,
  ```
  𝔼[(f (X t) - f (X s) - ∫ u in Clock.interval q c s t, g (X u) ∂q) * ∏ k, h k (X (t k))] = 0
  ```
  for every `(f,g) ∈ A`; and the same with `h k` bounded continuous when `E` is
  metrizable. This is the statement that turns every later theorem into a
  statement about finite dimensional distributions, and it is the reason the
  index needs no order structure beyond a preorder.
* The consequence that the solution property depends only on the finite
  dimensional distributions of `X`.

## Milestone 4: jump processes

A concrete family of solutions, built without any of the theory above. Index
`[0,∞)`, state space `E` with `[MeasurableSpace E]`.

* Data: a measurable rate `lam : E → [0,∞)` and a Markov kernel `mu : Kernel E E`.
  The operator is `A f x = lam x * ∫ y, (f y - f x) ∂(mu x)` with
  `A = {(f, A f) | f bounded measurable}`.
* `jumpProcess lam mu nu`: the process with initial law `nu` that waits an
  exponential time of rate `lam (X t)` and then jumps according to `mu`,
  constructed from a Markov chain with kernel `mu` and an independent sequence
  of exponential variables. Give the construction on an explicit probability
  space and prove that its paths are càdlàg and piecewise constant.
* `jumpProcess_isMPSolution`: for `lam` bounded, `jumpProcess lam mu nu` solves
  the martingale problem for `(A, nu)` with respect to its natural filtration.
* `norm_apply_le`: for `lam` bounded by `L`, `‖A f‖ ≤ 2 * L * ‖f‖`, so `A` is a
  bounded linear map on bounded measurable functions.
* `exists_unique_of_bounded`: for `lam` bounded the martingale problem for
  `(A, nu)` has exactly one solution, and its one dimensional distributions are
  `nu.map (exp (t • A))` given by the exponential series of the bounded operator.
  This is the Picard iteration and needs no analysis beyond `NormedSpace`.
* `jumpProcess_isLocalMPSolution`: for `lam` unbounded but with the process not
  exploding, the local martingale problem is solved; and the explosion criterion
  in terms of the jump times.
* The path dependent variant, where the rate at time `t` is a predictable
  functional of the path rather than a function of the current state, with the
  same two statements. This is the family that supplies the examples for
  Milestones 7 and 9.

## Milestone 5: mixtures, shifts and the restart lemma

* `MPSolutions.isConvex` and, more generally,
  `MPSolutions.integral_mem`: if `ϑ ↦ P ϑ` is a measurable family of solutions
  and `∫ 𝔼^{P ϑ}|Y t| ∂ν < ∞` for every `Y` and `t`, then `∫ P ϑ ∂ν` is a
  solution. Both directions of the corresponding disintegration statement when
  `E` is standard Borel.
* Fix `[AddCommMonoid ι]` with a compatible order. A `Shift` on `F` is a family
  `θ r : F → F` of measurable maps with `π t ∘ θ r = π (r + t)`.
* `ShiftSystem 𝓧°`: a family `𝓧° r` of families of adapted processes with
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

## Milestone 6: uniqueness and the Markov property, without an operator

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
  `duality_of_atomic_blockStack_of_bounded` and
  `duality_of_atomic_chain_of_integrable` this covers every clock that is
  atomless, or has finitely many atoms below the point in question, or is mixed
  with finitely many atoms there, or whose atoms below the point form an
  interval-finite chain, or a discrete chain with interval-finite block
  quotient and `Φ` bounded, or an arbitrary chain with `γ` integrable for
  `m ⊗ m` on atom pairs. The last of the seven asks nothing of the order type
  and everything of the density; the two before it ask nothing of the density
  and something of the order type or of the value `Φ`. What none of the seven
  reaches is a chain of atoms carrying a `γ` that is neither
  `m ⊗ m`-integrable nor attached to a bounded `Φ`, and, beyond chains,
  infinitely many incomparable atoms.
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
* `duality_discrete`: the case `ι = ℕ` with counting measure, which follows from
  `chain_identity` alone and needs none of the analysis, and is the case
  `m ≡ 1` of `duality_of_atomic`.
* `uniqueness_of_duality`: a dual process determines the one dimensional
  distributions, hence, with Milestone 6, gives uniqueness. This is the standard
  application and is the reason the milestone exists.

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
  The repository `RemyDegenne/brownian-motion`, Apache License 2.0, carries this
  development for quasimartingales in
  `BrownianMotion/StochasticIntegral/Quasimartingale/`, in the shape described
  above and with four remaining gaps; it may be taken over with its copyright
  headers and author attribution preserved. `IsRealQuasimartingale` and the
  regularity sets it is built on belong to the material taken over.
* `IsRegularizingClass Φ X 𝓧`: a set `Φ` of bounded continuous functions on `E`
  such that for every `f ∈ Φ` there are `Y ∈ 𝓧` and an adapted `𝕂`-valued `C`
  with `f (X t) = Y t + C t` almost surely for every `t`, with `C` almost surely
  having one sided limits along `D`, and with `C` right continuous in `L¹`.
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
  stopping times `τ n = s n` for `s n ↑ t` gives
  `∀ᵐ ω ∂P, Function.leftLim (X · ω) t = X t ω` for every `t` that is not
  minimal. This is the sharpening of Ethier–Kurtz, Lemma 3.7.7, which says only
  that the set of `t` failing it is countable; that lemma is
  `SkorokhodSpace.exists_countable_dense_continuity` in **SkorokhodSpace**
  Milestone 8.
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
* `not_isQuasiLeftContinuous_of_atom`, the sharpness, as a named example and not
  as a remark. Atomlessness is not a convenience of the proof, and it is not a
  hypothesis of `exists_cadlag_modification_of_isRegularizingClass`, which holds
  for every clock: an atom of `q` at `u` is a fixed time of discontinuity. On
  `E = Bool` with `q = Measure.dirac u` there is a solution that flips a fair
  coin at `u` and is constant on either side of it, and for `s n ↑ u` its paths
  have `X (s n) → X (u-) ≠ X u` on an event of probability one half. The
  existence of a càdlàg modification and quasi-left-continuity therefore
  separate exactly at the atoms of the clock, and the example is what makes the
  separation checkable.

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
  for `A`, and the martingale problem has a solution with càdlàg paths. The
  algebra is convergence determining by the Stone–Weierstrass criterion of
  **WeakConvergence**, Milestone 1, and hence dense for uniform convergence on
  compact sets; the previous item makes each `postcomp f ∘ X n` tight; and
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

## Milestone 12: existence from a dual process

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
