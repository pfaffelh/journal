# Martingale problems

A martingale problem specifies a process by requiring a family of functionals of
it to be martingales. The classical form fixes an operator `A` on functions on a
state space `E` and asks that `f (X t) - ∫ s in Ioc 0 t, (A f) (X s)` be a
martingale for every `f` in the domain of `A`. The theory of uniqueness, of the
Markov property, of path regularity and of convergence does not use the operator
and does not use the state space; it uses only the family of martingales. This
roadmap develops the abstract form first and obtains the classical statements as
instances.

Mathlib supplies the probabilistic base: `MeasureTheory.Filtration`,
`MeasureTheory.Adapted`, `MeasureTheory.ProgMeasurable`,
`MeasureTheory.IsStoppingTime` in `Mathlib/Probability/Process/`,
`MeasureTheory.Martingale` and `MeasureTheory.Submartingale` in
`Mathlib/Probability/Martingale/Basic.lean` with optional stopping and Doob's
inequalities, conditional expectation, `MeasureTheory.UniformIntegrable`, and
Polish spaces with weak convergence and Prokhorov's theorem. Note that
`MeasureTheory.Martingale` is stated for values in a real Banach space, so
complex-valued martingales need no separate development.

This roadmap depends on **WeakConvergence** for separating classes, the
continuous mapping theorem and the Skorokhod representation theorem; on
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
  optional interval `Set.Ioc 0 t` or the predictable interval `Set.Ico 0 t`. It
  is a parameter of the definition, not a global choice; the same Markov chain
  needs one convention on `ℕ` and the other after its grid is embedded in
  `[0,∞)`.

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

Fix `[Preorder ι]`, a measurable space `Ω`, a filtration `𝓕`, and `[RCLike 𝕂]`.

* `IsMPSolution (𝓧 : Set (ι → Ω → 𝕂)) (𝓕 : Filtration ι m) (P : Measure Ω)`,
  defined as `∀ Y ∈ 𝓧, Martingale Y 𝓕 P`, and the local variant
  `IsLocalMPSolution` with `∀ Y ∈ 𝓧, ∃ σ, IsLocalizingSequence σ ∧ ...`.
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
  canonical space.
* `IsMPSolutionFor` with an initial law: `IsMPSolutionFor A q c X 𝓖 P ∧ P.map (X 0) = μ`.

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
  `F` is generated by the coordinates, together with a monotone class argument.
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

Fix `[Preorder ι]` with a countable dense subset and `[AddCommMonoid ι]`.

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
  `Φ t 0 = Φ 0 t` for `q`-almost every `t`, by the time change
  `Q t = q (Set.Iio t)` and its right inverse. State the time change as a lemma
  in its own right.
* `duality_discrete`: the case `ι = ℕ` with counting measure, which follows from
  `chain_identity` alone and needs none of the analysis.
* `uniqueness_of_duality`: a dual process determines the one dimensional
  distributions, hence, with Milestone 6, gives uniqueness. This is the standard
  application and is the reason the milestone exists.

## Milestone 9: the càdlàg modification

Fix `[LinearOrder ι]` with the order topology and a countable dense `D ⊆ ι`, and
`E` metrizable.

* Submartingale regularization, which Mathlib does not have. For a submartingale
  `Y` indexed by `ι`, the restriction to `D` has almost surely finite one sided
  limits along `D` at every point, by the upcrossing inequality
  `MeasureTheory.Submartingale.upcrossing_le` already in Mathlib. State
  `Submartingale.exists_rightLim_along` and `Submartingale.exists_leftLim_along`.
* `Submartingale.exists_cadlag_modification_iff_rightContinuous`: a submartingale
  has a càdlàg modification if and only if `t ↦ 𝔼[Y t]` is right continuous.
* `Martingale.exists_cadlag_modification`: a martingale always has one.
  The repository `RemyDegenne/brownian-motion`, Apache License 2.0, contains a
  development of these two statements for quasimartingales in
  `BrownianMotion/Quasimartingale/`; it may be taken over with its copyright
  headers and author attribution preserved.
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
* `isRelativelyCompact_of_approx`: if `E` is Polish, the domain of `A` contains
  an algebra separating points and vanishing nowhere, the approximation holds
  for each `(f,g) ∈ A`, and `{X n}` satisfies compact containment, then `{X n}`
  is relatively compact; hence every limit point solves the martingale problem
  for `A`, and the martingale problem has a solution with càdlàg paths.
  Combine the Stone–Weierstrass criterion of **WeakConvergence** with the
  tightness criterion of **SkorokhodSpace**.
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
  a kernel, from `integral_rieszMeasure` in
  `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/`.
* The fibred state space: state Milestone 12 for `E : ι → Type*` with
  `[∀ t, MeasurableSpace (E t)]` and paths in `Π t, E t`, the test pairs becoming
  sections. The abstract layer of Milestones 2, 3, 5, 6, 8 and 10 never mentions
  the state space and applies unchanged; Milestones 9 and 11 are stated for a
  constant fibre. The historical process, whose state at time `t` is the path up
  to `t`, is the instance that needs the fibred form.
