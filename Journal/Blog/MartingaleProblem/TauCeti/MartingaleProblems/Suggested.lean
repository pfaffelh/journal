/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.CDF
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Suggested signatures for the martingale problems roadmap

Prototypes only. The abstract layer takes a family of test processes and never
mentions a state space; the Markovian layer specialises it.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-10.  Every declaration elaborates; 9 declarations carry `sorry`, and
Five more the same day, in `section JumpFiltration`, are the four bookkeeping
facts about `lebesgueClock` that the conditional expectation of
`jumpProcess_isMPSolution` still needed, plus their assembly:
`lebesgueClock_interval_optional_eq` identifies the compensating window with
`Set.Ioc`, `lebesgueClock_apply_Ioc` gives its exact mass (via
`lebesgueClock_preimage_Ioc`), `integral_lebesgueClock_Ioc` reindexes a
compensating integral as a genuine `ℝ`-interval integral starting at `0`, and
`setIntegral_compensator_sub_eq_intervalIntegral` assembles all of it with
`Clock.interval_union` and `intervalIntegral_integral_swap` into: the
difference of two nested compensating windows, integrated over a set of paths,
equals the interval integral of the set integral of the shifted process. That
is steps two through four of the four steps `jumpProcess_isMPSolution` names at
the end of its docstring.  Three more the same day close it: the bound
`abs_setIntegral_compensator_le` on a compensating window, the integrability
`integrable_mpFamily_jumpProcess` of a test process, and
`jumpProcess_isMPSolution` itself -- **`thm:jumpMP`, the first solution of a
martingale problem in this file that is a solution and not a counterexample**.
Seven more the same day are the acceptance example of Milestone 4, the Poisson
process (`section PoissonExample`): `jumpApply_poisson` is the computation that
the generator of this data is the forward difference `f (x + 1) - f x`, and
`poissonProcess_isMPSolution` discharges every hypothesis of `thm:jumpMP` on
data, so that the theorem is shown to have an instance.
`martingale_compensated_poisson` is a concrete martingale and not a solution
predicate.  Fourteen more the same day are `section Uniqueness`, the Picard
iteration: `expJumpApply` is the exponential series of the bounded generator,
and `integral_eq_expJumpApply_of_isMPSolution` shows that **every** solution of
the martingale problem has that series for its one dimensional distributions,
`integral_eq_of_isMPSolution_of_map_eq` reading it as uniqueness across two
different spaces.  Nothing in that section mentions `jumpProcess`.
Eight more the same day join the two halves and check them against Mathlib:
`jumpMeasure_integral_jumpProcess_eq_expJumpApply` computes the one dimensional
distributions of the *constructed* process from `nu` alone (its second
hypothesis is `measurable_uncurry_comp_jumpProcess`, joint measurability for the
full σ-algebra, which is not the filtered `measurable_uncurry_jumpProcess`), and
`jumpMeasure_map_jumpProcess_poisson` identifies them, on the Poisson data, with
`ProbabilityTheory.poissonMeasure`.  That identification rests on
`tsum_fwdDiff_iter_eq`, the Gregory--Newton summation of the exponential series
of Mathlib's forward difference operator, which is a statement about `ℝ` alone.
Seven more the same day are the **second** acceptance example of Milestone 4,
the two state chain on `Bool` (`section TwoStateExample`): the iterates of its
generator cycle with the factor `-2` (`iterate_jumpApply_flip`), so the series
has a closed form (`expJumpApply_flip`) and the law is a number,
`jumpMeasure_map_jumpProcess_flip : … .real {true} = (1 - exp (-2t))/2`.  The
two examples check different things: the Poisson one against Mathlib, the two
state one against a value a reader can compute, and a sign error in `jumpApply`
survives neither.
Sixteen more the same day carry the uniqueness from one coordinate to finitely
many, which is what "exactly one solution" says.
`integral_mul_sub_eq_intervalIntegral_of_isMPSolution` is the martingale
identity tested against a bounded `𝓕 s`-measurable factor and read from an
arbitrary starting time; `abs_sub_sum_le_of_recursion` is the Picard iteration
written once, over an abstract functional, with the unconditional and the
conditional forms as corollaries; and `integral_mul_fddProd_eq_of_isMPSolution`
inducts over a finite dimensional test variable recorded as a **list of
increments** (`fddProd`, `fddExp`), peeling the first factor into the past
factor.  `integral_fddProd_eq_of_isMPSolution_of_map_eq` is the uniqueness, and
`jumpMeasure_integral_fddProd_eq_fddExp` the same statement for the constructed
process.  That induction is the one place that needs `X` itself to be adapted --
the `StronglyAdapted` of `Martingale` is about the *compensated* processes --
which for the construction is `stronglyMeasurable_jumpFiltration`.
every one of those `sorry`s is a **proof**.  The last two blocks of the file are
Milestone 4, and they carry **no** `sorry`.  The first, `IsStepPath`, was added on 2026-09-09:
its three declarations are proved, and one of them,
`exists_finite_setOf_leftLim_ne_not_isCadlagPath`, is the witness that the
roadmap's first proposal for that predicate -- local finiteness of the jump set
-- does not imply càdlàg.  The second, `JumpConstruction`, was added the same
day: thirty three proved declarations building `jumpProcess` on the explicit space
`(ℕ → E) × (ℕ → ℝ)` with the measure `jumpMeasure mu nu`, and showing its paths
to be step paths, hence càdlàg, and jointly measurable in `(t, ω)`.  Ten more
came the same day: the waiting times are almost surely positive with divergent
partial sums (`ae_pos_waiting`, `tendsto_sum_waiting_atTop`, the second
Borel--Cantelli lemma on `{ξ n > 1}`), so that `ae_isStepPath_jumpProcess` and
`ae_isCadlagPath_jumpProcess` hold for `jumpMeasure mu nu`-almost every `ω`
under `0 < lam ≤ L` alone.  Four more the same day: the tail of the exponential
law and its memorylessness (`expMeasure_Ioi`, `expMeasure_Ioi_add`, neither of
which is in Mathlib), the generator `jumpApply` and its bound
`abs_jumpApply_le`.  And four more: `jumpProcess_zero` with
`jumpMeasure_map_jumpProcess_zero`, which say that the *process* -- and not
merely the chain driving it -- starts with law `nu`, and `lebesgueClock`, the
clock of the jump martingale problem, on the index `ℝ≥0` that `[OrderBot ι]`
forces.  Eight more the same day close the measure theory of the first jump:
`integral_jumpMeasure_eq_of_split` performs the Fubini swap that turns
`jumpMeasure_map_split` into a restart -- three nested integrals, against `nu`,
against `expMeasure 1` and against `jumpMeasure mu (mu z)` -- and
`jumpMeasure_integral_eq_renewal` is the renewal equation, with the second term
an integral over `Set.Ioc 0 (lam z * t)` against Lebesgue measure, which is the
shape the differentiation of the backward equation acts on.  With them
`integral_expMeasure_one` (the exponential law as a density, which Mathlib does
not state), `ae_exists_lt_jumpTime` (non explosion without a topology on `E`) and
the two bounded-integrand tools `integrable_of_abs_le` and
`abs_integral_le_of_abs_le`.  Twelve more the same day are the **backward equation**:
`abs_integral_jumpProcess_sub_sub_le` bounds the second order remainder of
`t ↦ E[h(X_t)]` at `t = 0` by `4 * C * L ^ 2 * t ^ 2`, and
`jumpMeasure_hasDerivWithinAt_integral` reads the generator off it.  The derivative is one sided
by necessity: `integral_jumpProcess_of_nonpos` says the function is constant on `Set.Iic 0`, and
`eq_zero_of_hasDerivAt_integral_jumpProcess` is the theorem that a two sided `HasDerivAt` at `0`
would force `∫ A h ∂nu = 0`.  Nine more the same day are the **Markov property at a fixed
time** and the **expectation identity**: `jumpMeasure_integral_jumpProcess_add` is an induction
on the number of jumps in `[0, s]` (`abs_integral_jumpMeasure_add_sub_le`) whose error term is
the probability of `n` jumps before `s`, sent to zero by `tendsto_measureReal_jumpTime_le`; and
`jumpMeasure_integral_sub_eq_intervalIntegral` is
`E[h (X t)] - E[h (X 0)] = ∫_0^t E[A h (X r)] dr`, which the Markov property produces from the
derivative at `0` by the one sided fundamental theorem of calculus.  Twenty five more the same
day are the **structure of the past**, which is what the conditional expectation of
`jumpProcess_isMPSolution` needs and what the unconditional Markov property does not have:
`eq_of_measurable_naturalFiltration` says that a `𝓕 s`-measurable real function does not separate
two sample points whose paths agree below `s`, `NonExplosive` names the set on which the
substitutions of the past are valid, `jumpConst` and `jumpPrepend` are those substitutions, and
`IsPastFunctional` is the property of a functional that survives the restart --
`IsPastFunctional.comp_jumpPrepend` -- and makes it a function of the initial state before the
first jump -- `eq_jumpConst_of_isPastFunctional`.  Five more, on 2026-09-10, are the **Markov
property with a factor from the past**, in `section ConditionalMarkov`:
`abs_integral_jumpMeasure_add_sub_le_past` is the induction of
`abs_integral_jumpMeasure_add_sub_le` carrying a bounded functional of the past along, and
`jumpMeasure_integral_jumpProcess_add_past` is its limit,
`E[G · h (X (s + t))] = E[G · (P t h) (X s)]` for every `G` with `|G| ≤ 1` that is a functional of
the past up to `s`.  With them `jumpKernel_map_snd` and `ae_mem_nonExplosive_jumpKernel`, the two
statements about the kernel that the branch `{s < T 1}` of that induction is run under, and
`setIntegral_jumpProcess_sub_eq_intervalIntegral`, the expectation identity tested against a set
of the past -- the shape the conditional expectation of `jumpProcess_isMPSolution` consumes.  The
first
proof of the
file is `IsQuasiLeftContinuous.ae_eq_leftLim`, and it needed the statement
corrected first: under `¬ IsMin t` alone it is false.  On 2026-09-07 twelve more
proofs came in: `Clock.interval_union`, the additivity every compensator
argument rests on; `not_isQuasiLeftContinuous_of_not_ae_tendsto`, the half of
`not_isQuasiLeftContinuous_of_atom` that does not depend on the martingale
problem; and the `AtomWitness` block, which builds the coin, the clock with an
atom at `u`, the path, the càdlàg property of that path and the failure of
quasi-left-continuity for it.
The statement of `not_isQuasiLeftContinuous_of_atom` was corrected in the same
run: it admitted the vacuous witness `A = ∅`.  Ten further declarations closed
it later the same day -- the operator `coinPair`, the class `coinClass` and its
separation, the filtration, the two clock masses, the two integrals, the
integrability of everything on `Bool`, and `isMPSolution_coinProcess` -- so that
`not_isQuasiLeftContinuous_of_atom` itself now carries a proof.  The eighth run
of that day added `not_isAtomless_atomClock`, which is what makes the sharpness
a delimitation rather than a contradiction: the clock of the witness fails the
hypothesis `hQ` of `isQuasiLeftContinuous_of_isMPSolutionFor`, and that is now a
theorem instead of an observation about the definition.  No statement in this
file is `True` or `sorry` any more: the drafts of Milestones 3, 5, 9 and 10 were
turned into propositions on 2026-09-06.  `Shift` now takes the coordinate maps
`π` as a parameter, so that its compatibility field can be stated at all;
`IsDetermining`, `IsRegularizingClass` and `IsQuasiLeftContinuous` say what the
roadmap says; and the hypothesis (a) of `mpSolution_of_tendsto` is convergence
in distribution one variable at a time, as the manuscript's remark on the
topology free form of the theorem prescribes.

The tenth run of 2026-09-07 added the clock's interval calculus
(`Clock.interval_subset_Iic`, `Clock.measurableSet_interval`,
`Clock.measure_interval_ne_top`), the two measure theoretic tools
`stronglyMeasurable_integral_comp` and `integrableOn_of_bounded`, and the
increment identity `mpFamily_sub_of_measurable_path`, all proved; and it
corrected both forms of `isMPSolution_iff_forall_fdd`, which were **not
provable** as they stood.  They now carry `Clock.IsProgressive Q X 𝓕`.
-/

open Filter Topology MeasureTheory ProbabilityTheory Set

open scoped NNReal

/-! ## Milestone 1: the clock -/

/-- The two conventions for the compensating interval. -/
inductive Clock.Conv | optional | predictable

variable {ι : Type*} [Preorder ι]

/-- A measure on the index whose down-sets are measurable and of finite mass. -/
structure Clock (ι : Type*) [Preorder ι] where
  measurableSpace : MeasurableSpace ι
  q : @Measure ι measurableSpace
  measurableSet_Iic : ∀ t : ι, @MeasurableSet ι measurableSpace (Set.Iic t)
  measurableSet_Iio : ∀ t : ι, @MeasurableSet ι measurableSpace (Set.Iio t)
  measure_Iic_ne_top : ∀ t : ι, q (Set.Iic t) ≠ ⊤

/-- The compensating interval selected by the convention. -/
def Clock.interval (_Q : Clock ι) (c : Clock.Conv) (s t : ι) : Set ι :=
  match c with
  | .optional => Set.Iic t \ Set.Iic s
  | .predictable => Set.Iio t \ Set.Iio s

theorem Clock.interval_union (Q : Clock ι) (c : Clock.Conv) {s t u : ι}
    (hst : s ≤ t) (htu : t ≤ u) :
    Q.interval c s u = Q.interval c s t ∪ Q.interval c t u ∧
      Disjoint (Q.interval c s t) (Q.interval c t u) := by
  cases c with
  | optional =>
    refine ⟨?_, ?_⟩
    · ext x
      simp only [Clock.interval, Set.mem_sdiff, Set.mem_union, Set.mem_Iic]
      constructor
      · rintro ⟨hxu, hxs⟩
        by_cases hxt : x ≤ t
        · exact Or.inl ⟨hxt, hxs⟩
        · exact Or.inr ⟨hxu, hxt⟩
      · rintro (⟨hxt, hxs⟩ | ⟨hxu, hxt⟩)
        · exact ⟨hxt.trans htu, hxs⟩
        · exact ⟨hxu, fun h => hxt (h.trans hst)⟩
    · simp only [Clock.interval]
      rw [Set.disjoint_left]
      rintro x ⟨hxt, -⟩ ⟨-, hxt'⟩
      exact hxt' hxt
  | predictable =>
    refine ⟨?_, ?_⟩
    · ext x
      simp only [Clock.interval, Set.mem_sdiff, Set.mem_union, Set.mem_Iio]
      constructor
      · rintro ⟨hxu, hxs⟩
        by_cases hxt : x < t
        · exact Or.inl ⟨hxt, hxs⟩
        · exact Or.inr ⟨hxu, hxt⟩
      · rintro (⟨hxt, hxs⟩ | ⟨hxu, hxt⟩)
        · exact ⟨hxt.trans_le htu, hxs⟩
        · exact ⟨hxu, fun h => hxt (h.trans_le hst)⟩
    · simp only [Clock.interval]
      rw [Set.disjoint_left]
      rintro x ⟨hxt, -⟩ ⟨-, hxt'⟩
      exact hxt' hxt

theorem Clock.interval_subset_Iic (Q : Clock ι) (c : Clock.Conv) (s t : ι) :
    Q.interval c s t ⊆ Set.Iic t := by
  cases c with
  | optional => exact Set.sdiff_subset
  | predictable => exact fun _ hx => le_of_lt hx.1

theorem Clock.measurableSet_interval (Q : Clock ι) (c : Clock.Conv) (s t : ι) :
    MeasurableSet[Q.measurableSpace] (Q.interval c s t) := by
  cases c with
  | optional => exact (Q.measurableSet_Iic t).diff (Q.measurableSet_Iic s)
  | predictable => exact (Q.measurableSet_Iio t).diff (Q.measurableSet_Iio s)

/-- Every compensating interval has finite mass.  This is the only place where
`Clock.measure_Iic_ne_top` is used, and it is what makes the compensator of
`mpFamily` a bounded function of `ω` for a bounded `p.2`. -/
theorem Clock.measure_interval_ne_top (Q : Clock ι) (c : Clock.Conv) (s t : ι) :
    Q.q (Q.interval c s t) ≠ ⊤ :=
  ne_top_of_le_ne_top (Q.measure_Iic_ne_top t)
    (measure_mono (Q.interval_subset_Iic c s t))

/-- The two conventions agree exactly for an atomless clock. -/
def Clock.IsAtomless (Q : Clock ι) : Prop := ∀ t : ι, Q.q {u | t ≤ u ∧ u ≤ t} = 0

/-! ## Milestone 2: the abstract martingale problem -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝕂 : Type*} [RCLike 𝕂]

/-- `P` solves the martingale problem for the family `𝓧` of test processes. -/
def IsMPSolution (𝓧 : Set (ι → Ω → 𝕂)) (F : Filtration ι m) (P : Measure Ω) : Prop :=
  ∀ Y ∈ 𝓧, Martingale Y F P

/-- The set of solutions. -/
def mpSolutions (𝓧 : Set (ι → Ω → 𝕂)) (F : Filtration ι m) : Set (Measure Ω) :=
  {P | IsMPSolution 𝓧 F P}

section Local

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι]

/-- The local problem, through Mathlib's `ProbabilityTheory.Locally`.  Do not
introduce a localizing sequence by hand: `IsLocalizingSequence` and the whole
`Locally` API are in `Mathlib/Probability/Process/LocalProperty.lean`, including
the idempotence `IsStable.locally_locally_iff`.

This is stage (L) of Milestone 2.  `Locally` is declared in `section LinearOrder`
under `variable [LinearOrder ι]` (`LocalProperty.lean:77`) and
`variable [OrderBot ι]` (`:88`), with its own binders
`[TopologicalSpace ι] [OrderTopology ι] [Zero E]` (`:93`); the file-level
`[Preorder ι]` above is not enough for it, and `⊥` occurs in the definition
itself.  The index is rebound in this section rather than given an extra
instance binder, so that no declaration carries both `[Preorder ι]` and
`[LinearOrder ι]`. -/
def IsLocalMPSolution (𝓧 : Set (ι → Ω → 𝕂)) (F : Filtration ι m)
    (P : Measure Ω) : Prop :=
  ∀ Y ∈ 𝓧, Locally (fun Z ↦ Martingale Z F P) F Y P

theorem isLocalMPSolution_of_isMPSolution
    {𝓧 : Set (ι → Ω → 𝕂)} {F : Filtration ι m} {P : Measure Ω}
    (h : IsMPSolution 𝓧 F P) : IsLocalMPSolution 𝓧 F P :=
  fun Y hY => Locally.of_prop (h Y hY)

end Local

variable {E : Type*} [MeasurableSpace E]

/-- The test processes attached to an operator, a clock and a convention.
The operator is a relation, not a function.

The lower end of the compensating integral is `⊥`, not `0`: the index of the
abstract layer carries no `Zero`, and the roadmap's index bundle asks for an
order, so `[OrderBot ι]` is the hypothesis that makes `Q.interval c ⊥ t` — which
is `Set.Ioc ⊥ t` in the optional convention — the right-hand analogue of
`∫_0^t`. -/
def mpFamily [OrderBot ι] (A : Set ((E → 𝕂) × (E → 𝕂))) (Q : Clock ι) (c : Clock.Conv)
    (X : ι → Ω → E) : Set (ι → Ω → 𝕂) :=
  {Y | ∃ p ∈ A, ∀ t ω, Y t ω =
    p.1 (X t ω) - ∫ s in Q.interval c ⊥ t, p.2 (X s ω) ∂Q.q}

/-! ## Milestone 3: canonical families, determining sets and the finite
dimensional criterion -/

/-- Every `Y ∈ 𝓧` is a measurable functional of the path: `Y t = Y₀ t ∘ X` with
`Y₀ t` drawn from the given family `𝓧₀ t`.  `StronglyMeasurable` rather than
`Measurable`, because `𝕂` carries a topology but no `MeasurableSpace` instance.

The roadmap writes `𝓧°` and `Y°` for the canonical versions; `°` is not an
identifier character in Lean, so they are `𝓧₀` and `Y₀` here. -/
def IsCanonical {F : Type*} [MeasurableSpace F] (𝓧₀ : ι → Set (F → 𝕂))
    (𝓧 : Set (ι → Ω → 𝕂)) (X : Ω → F) : Prop :=
  ∀ Y ∈ 𝓧, ∃ Y₀ : ι → F → 𝕂, (∀ t, Y₀ t ∈ 𝓧₀ t) ∧ (∀ t, StronglyMeasurable (Y₀ t)) ∧
    ∀ t ω, Y t ω = Y₀ t (X ω)

/-- A family of bounded real test variables strong enough to detect the
martingale property: if the increments of `Y` are orthogonal to `𝓩 s`, then `Y`
has the martingale property from `s` to `t`.  Real valued whatever `𝕂` is.

The members of `𝓩 s` are meant to be bounded and measurable with respect to the
coordinates up to `s`; that is a property of the instantiation --
`isDetermining_products` supplies it -- and not of this definition, which is a
hypothesis wherever it occurs and is therefore stated as the bare implication. -/
def IsDetermining {F : Type*} [MeasurableSpace F] (𝓩 : ι → Set (F → ℝ))
    (𝓧 : Set (ι → Ω → 𝕂)) (X : Ω → F) (𝓕 : Filtration ι m) : Prop :=
  ∀ (P : Measure Ω) [IsProbabilityMeasure P], ∀ Y ∈ 𝓧, ∀ s t : ι, s ≤ t →
    Integrable (Y s) P → Integrable (Y t) P →
    (∀ Z ∈ 𝓩 s, ∫ ω, Y t ω * (Z (X ω) : 𝕂) ∂P = ∫ ω, Y s ω * (Z (X ω) : 𝕂) ∂P) →
      P[Y t | 𝓕 s] =ᵐ[P] Y s

/-- Joint measurability of the path up to each time, relative to the filtration.

This is Mathlib's `IsStronglyProgressive` in the shape a `Clock` forces: the
clock carries its `MeasurableSpace ι` as a *field* and not as an instance, so the
subtype `Set.Iic t` of that structure cannot be written without `@`; the
equivalent formulation by a jointly measurable extension `Z`, which agrees with
`X` below `t` and is `Q.measurableSpace ⊗ 𝓕 t`-measurable everywhere, is used
instead.

It is a hypothesis on `X` and the clock alone, never on `P`, and it is not
cosmetic.  Without it neither side of `isMPSolution_iff_forall_fdd` is reachable
from the other: `Martingale` unfolds to `StronglyAdapted ℱ Y ∧ …`, the
compensator `fun ω ↦ ∫ u in Q.interval c ⊥ t, p.2 (X u ω) ∂Q.q` is
`𝓕 t`-measurable for no reason coming from `∀ t, Measurable (X t)` alone, and
for a fixed `ω` the integrand `fun u ↦ p.2 (X u ω)` need not even be
`Q.measurableSpace`-measurable, so that the compensator is the junk value `0` and
`Clock.interval_union` does not make the two compensators subtract. -/
def Clock.IsProgressive (Q : Clock ι) (X : ι → Ω → E) (𝓕 : Filtration ι m) : Prop :=
  ∀ t : ι, ∃ Z : ι → Ω → E, (∀ u, u ≤ t → Z u = X u) ∧
    Measurable[Q.measurableSpace.prod (𝓕 t)] (Function.uncurry Z)

/-- The parametrised Bochner integral is strongly measurable in the parameter.
This is `MeasureTheory.StronglyMeasurable.integral_prod_left`, packaged so that a
clock's field `Q.measurableSpace` and a filtration's value `𝓕 t` — neither of
which is an instance — can be handed to it. -/
theorem stronglyMeasurable_integral_comp {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β] {γ : Type*} [MeasurableSpace γ]
    {𝕜 : Type*} [RCLike 𝕜] (μ : Measure α) [SFinite μ] {W : α → β → γ}
    (hW : Measurable (Function.uncurry W)) {g : γ → 𝕜} (hg : Measurable g) :
    StronglyMeasurable fun y => ∫ x, g (W x y) ∂μ :=
  MeasureTheory.StronglyMeasurable.integral_prod_left
    (f := fun x y => g (W x y)) ((hg.comp hW).stronglyMeasurable)

/-- A bounded measurable function is integrable on every set of finite measure.
The compensator of `mpFamily` is exactly of this shape, by
`Clock.measure_interval_ne_top`. -/
theorem integrableOn_of_bounded {α : Type*} [MeasurableSpace α] {𝕜 : Type*}
    [RCLike 𝕜] (μ : Measure α) {s : Set α} (hs : μ s ≠ ⊤) {f : α → 𝕜}
    (hf : Measurable f) {b : ℝ} (hb : ∀ x, ‖f x‖ ≤ b) : IntegrableOn f s μ := by
  have : IsFiniteMeasure (μ.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hs⟩
  exact Integrable.mono' (integrable_const b) hf.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- A bounded measurable real function is integrable against a finite measure.  The unbundled
companion of `integrableOn_of_bounded`, for the whole space and in absolute value; the renewal
equation of the jump construction uses it at every one of its five nested integrals. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)

/-- A bound on the integrand of a probability measure is a bound on the integral.  This is what
makes the boundedness hypothesis of the renewal equation propagate inwards through the iterated
integrals of `integral_jumpMeasure_eq_of_split`. -/
theorem abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
  simpa [Real.norm_eq_abs, measureReal_def, measure_univ] using h

omit [MeasurableSpace E] in
/-- The increment of a member of `mpFamily` over `[s,t]` is the compensated
increment that `isMPSolution_iff_forall_fdd` tests.  `Clock.interval_union` is
what makes the two compensators subtract, and the integrability of the integrand
on each half is `integrableOn_of_bounded` through
`Clock.measure_interval_ne_top`.  The hypothesis `hZ` is the path measurability
that `Clock.IsProgressive` supplies below `t`; it is not decoration, for without
it both compensators are the junk value `0` and the identity is false. -/
theorem mpFamily_sub_of_measurable_path [OrderBot ι] {Q : Clock ι} {c : Clock.Conv}
    {X : ι → Ω → E} {f g : E → 𝕂} {Y : ι → Ω → 𝕂}
    (hY : ∀ t ω, Y t ω = f (X t ω) - ∫ u in Q.interval c ⊥ t, g (X u ω) ∂Q.q)
    {b : ℝ} (hgb : ∀ x, ‖g x‖ ≤ b) {s t : ι} (hst : s ≤ t) {ω : Ω}
    (hZ : Measurable[Q.measurableSpace] fun u => g (X u ω)) :
    Y t ω - Y s ω =
      f (X t ω) - f (X s ω) - ∫ u in Q.interval c s t, g (X u ω) ∂Q.q := by
  obtain ⟨hunion, hdisj⟩ := Q.interval_union c (bot_le : ⊥ ≤ s) hst
  have hint := fun s' t' : ι =>
    @integrableOn_of_bounded ι Q.measurableSpace 𝕂 _ Q.q (Q.interval c s' t')
      (Q.measure_interval_ne_top c s' t') (fun u => g (X u ω)) hZ b
      (fun u => hgb (X u ω))
  rw [hY t ω, hY s ω, hunion,
    setIntegral_union hdisj (Q.measurableSet_interval c s t) (hint ⊥ s) (hint s t)]
  ring

/-- The finite dimensional criterion, `isMPSolutionFor_iff_forall_fdd` of the
roadmap: solving the martingale problem is an identity among finitely many
coordinates.  It is what turns every later theorem into a statement about finite
dimensional distributions, and it is the reason the index needs no order
structure beyond a preorder.

The filtration must be the natural one of `X`: the right hand side tests only
against the coordinates, so for a larger filtration the equivalence fails in the
direction from right to left.  That hypothesis is `h𝓕`.

`hXprog` is the second hypothesis that cannot be dropped, and it was missing
until 2026-09-07: the right hand side is a family of vanishing integrals and
says nothing about measurability, while the left hand side unfolds to
`StronglyAdapted 𝓕 Y ∧ …`.  See `Clock.IsProgressive`. -/
theorem isMPSolution_iff_forall_fdd [OrderBot ι] {A : Set ((E → 𝕂) × (E → 𝕂))}
    {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E} {𝓕 : Filtration ι m}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hA : ∀ p ∈ A, (Measurable p.1 ∧ ∃ b, ∀ x, ‖p.1 x‖ ≤ b) ∧
      Measurable p.2 ∧ ∃ b, ∀ x, ‖p.2 x‖ ≤ b)
    (hX : ∀ t, Measurable (X t)) (hXprog : Q.IsProgressive X 𝓕)
    (h𝓕 : ∀ s : ι, 𝓕 s = ⨆ r ∈ Set.Iic s, MeasurableSpace.comap (X r) inferInstance) :
    IsMPSolution (mpFamily A Q c X) 𝓕 P ↔
      ∀ p ∈ A, ∀ s t : ι, s ≤ t → ∀ (n : ℕ) (r : Fin n → ι), (∀ k, r k ≤ s) →
        ∀ h : Fin n → E → ℝ, (∀ k, Measurable (h k)) →
        (∀ k, ∃ b, ∀ x, ‖h k x‖ ≤ b) →
        ∫ ω, (p.1 (X t ω) - p.1 (X s ω)
              - ∫ u in Q.interval c s t, p.2 (X u ω) ∂Q.q) *
            ∏ k, (h k (X (r k) ω) : 𝕂) ∂P = 0 := sorry

/-- The same criterion with bounded **continuous** test functions, which is what
a weak convergence argument delivers.  It is the previous statement together with
the functional monotone class theorem `induction_on_mulSystem` of the roadmap
**WeakConvergence**, Milestone 5, and it needs the Borel structure of a
metrizable state space, where the previous one needs no topology at all. -/
theorem isMPSolution_iff_forall_fdd_continuous [OrderBot ι] [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
    {A : Set ((E → 𝕂) × (E → 𝕂))} {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E}
    {𝓕 : Filtration ι m} {P : Measure Ω} [IsProbabilityMeasure P]
    (hA : ∀ p ∈ A, (Measurable p.1 ∧ ∃ b, ∀ x, ‖p.1 x‖ ≤ b) ∧
      Measurable p.2 ∧ ∃ b, ∀ x, ‖p.2 x‖ ≤ b)
    (hX : ∀ t, Measurable (X t)) (hXprog : Q.IsProgressive X 𝓕)
    (h𝓕 : ∀ s : ι, 𝓕 s = ⨆ r ∈ Set.Iic s, MeasurableSpace.comap (X r) inferInstance) :
    IsMPSolution (mpFamily A Q c X) 𝓕 P ↔
      ∀ p ∈ A, ∀ s t : ι, s ≤ t → ∀ (n : ℕ) (r : Fin n → ι), (∀ k, r k ≤ s) →
        ∀ h : Fin n → E → ℝ, (∀ k, Continuous (h k)) →
        (∀ k, ∃ b, ∀ x, ‖h k x‖ ≤ b) →
        ∫ ω, (p.1 (X t ω) - p.1 (X s ω)
              - ∫ u in Q.interval c s t, p.2 (X u ω) ∂Q.q) *
            ∏ k, (h k (X (r k) ω) : 𝕂) ∂P = 0 := sorry

/-! ## Milestone 5: shifts and the restart lemma -/

section Restart

variable {ι : Type*} [Preorder ι] [AddCommMonoid ι] [AddLeftMono ι]
variable {E : Type*} [MeasurableSpace E]

/-- A shift on a path space: measurable maps `θ r` that move the coordinates by
`r`.

The coordinate maps `π` are a **parameter** of the structure.  Without them the
compatibility field cannot be stated at all -- that is why it stood as
`(sorry : Prop)` -- and it is the field that makes `θ` a shift rather than an
arbitrary measurable self map. -/
structure Shift (F : Type*) [MeasurableSpace F] (π : ι → F → E) where
  θ : ι → F → F
  measurable : ∀ r, Measurable (θ r)
  eval_comp : ∀ (r t : ι) (f : F), π t (θ r f) = π (r + t) f

variable {F : Type*} [mF : MeasurableSpace F] {π : ι → F → E}

/-- A shift system for the shift `S`: the family `𝓧₀ r` posed at time `r`
becomes, after composition with `θ r`, an increment of the base family `𝓧₀ 0`
up to a `𝓕₀ r`-measurable summand.  `mpFamily A Q c` carries one when the clock
is shift invariant, with `κ` the compensator up to `r`. -/
structure IsShiftSystem (S : Shift F π) (𝓕₀ : Filtration ι mF)
    (𝓧₀ : ι → Set (ι → F → 𝕂)) : Prop where
  stronglyAdapted : ∀ r : ι, ∀ Y' ∈ 𝓧₀ r, StronglyAdapted 𝓕₀ Y'
  increment : ∀ r : ι, ∀ Y' ∈ 𝓧₀ r, ∃ Y ∈ 𝓧₀ 0, ∃ κ : F → 𝕂,
    StronglyMeasurable[𝓕₀ r] κ ∧
      ∀ (t : ι) (f : F), Y' t (S.θ r f) = Y (r + t) f - Y r f + κ f

/-- The restart lemma: under a change of measure by a bounded non-negative
`𝓖 r`-measurable density of expectation one, the law of the path shifted by `r`
solves the martingale problem posed at `r`.  Everything in Milestone 6 rests on
it, and the proof is the definition of a shift system plus the martingale
property. -/
theorem restart {S : Shift F π} {𝓕₀ : Filtration ι mF}
    {𝓧₀ : ι → Set (ι → F → 𝕂)} (hS : IsShiftSystem S 𝓕₀ 𝓧₀)
    {X : Ω → F} (hX : Measurable X) {𝓖 : Filtration ι m} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hsol : IsMPSolution ((fun (Y : ι → F → 𝕂) t ω ↦ Y t (X ω)) '' 𝓧₀ 0) 𝓖 P)
    (r : ι) {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω) (hZb : ∃ b, ∀ ω, Z ω ≤ b)
    (hZm : StronglyMeasurable[𝓖 r] Z) (hZ1 : ∫ ω, Z ω ∂P = 1) :
    IsMPSolution (𝓧₀ r) 𝓕₀
      ((P.withDensity fun ω ↦ ENNReal.ofReal (Z ω)).map fun ω ↦ S.θ r (X ω)) := sorry

/-- The canonical case `Ω = F`, `X = id`, where the conclusion reads that the
image of `Z • P` under `θ r` solves the problem posed at `r`. -/
theorem restart_canonical {S : Shift F π} {𝓕₀ : Filtration ι mF}
    {𝓧₀ : ι → Set (ι → F → 𝕂)} (hS : IsShiftSystem S 𝓕₀ 𝓧₀)
    {P : Measure F} [IsProbabilityMeasure P] (hsol : IsMPSolution (𝓧₀ 0) 𝓕₀ P)
    (r : ι) {Z : F → ℝ} (hZ0 : ∀ f, 0 ≤ Z f) (hZb : ∃ b, ∀ f, Z f ≤ b)
    (hZm : StronglyMeasurable[𝓕₀ r] Z) (hZ1 : ∫ f, Z f ∂P = 1) :
    IsMPSolution (𝓧₀ r) 𝓕₀
      ((P.withDensity fun f ↦ ENNReal.ofReal (Z f)).map (S.θ r)) := sorry

end Restart

/-! ## Milestone 9: the regularizing class and quasi-left-continuity

The index is the one the milestone fixes for its last block: a linear order with
the order topology, `[OrderBot ι]`, and the conditionally complete lattice
structure, which is what the suprema of stopping times are taken in.  A stopping
time is `WithTop ι`-valued, its supremum is taken in `WithTop ι` through
`SupSet (WithTop α)` (`Order/ConditionallyCompleteLattice/Basic.lean:52`), and a
process is read at one through `MeasureTheory.stoppedValue`
(`Probability/Process/Stopping.lean:801`, `fun ω ↦ u (τ ω).untopA ω` under
`[Nonempty ι]`). -/

section Regularizing

variable {ι : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- Separating, as `IsSeparating` of the roadmap **WeakConvergence**,
Milestone 1 -- there over `Set (E → ℝ)`, here over `Set (E → 𝕂)`.  Restated so
that this file stands against Mathlib alone; it is the same proposition. -/
def IsSeparating (Γ : Set (E → 𝕂)) : Prop :=
  ∀ (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ f ∈ Γ, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν

/-- Right continuous with left limits: `IsCadlag` of the roadmap
**SkorokhodSpace**, Milestone 2, unfolded.  Mathlib has neither predicate, and
the path space itself is not available here, so the path property is stated and
not the membership in `D(ι, E)`. -/
def IsCadlagPath (g : ι → E) : Prop :=
  (∀ t, ContinuousWithinAt g (Set.Ioi t) t) ∧ ∀ t, ∃ l, Tendsto g (𝓝[<] t) (𝓝 l)

/-- The decomposition attached to one `f` of a regularizing class: `f ∘ X` splits
into a member of `𝓧` and a compensator `C` that is adapted, has one sided limits
along `D` almost surely, and is right continuous in `L¹`.

The decomposition itself is not a hypothesis -- `C := f ∘ X - Y` satisfies it --
so the content is the choice of `Y` in `𝓧` together with the last two fields.
`C` is `StronglyAdapted`, not `Adapted`: since 2026-01-13 Mathlib's `Adapted`
(`Probability/Process/Adapted.lean:60`) is measurability with respect to `f i`
and asks for `[MeasurableSpace 𝕂]`, while the notion the roadmap means, and the
one `Martingale` is built from (`Probability/Martingale/Basic.lean:53`), is
`StronglyAdapted` (`ibid.:105`). -/
structure IsCompensatorFor (X : ι → Ω → E) (𝓕 : Filtration ι m) (P : Measure Ω)
    (D : Set ι) (f : E → 𝕂) (Y C : ι → Ω → 𝕂) : Prop where
  stronglyAdapted : StronglyAdapted 𝓕 C
  decomposition : ∀ t : ι, ∀ᵐ ω ∂P, f (X t ω) = Y t ω + C t ω
  exists_limits : ∀ᵐ ω ∂P, ∀ t : ι,
    (∃ l : 𝕂, Tendsto (fun s ↦ C s ω) (𝓝[D ∩ Set.Iio t] t) (𝓝 l)) ∧
      ∃ l : 𝕂, Tendsto (fun s ↦ C s ω) (𝓝[D ∩ Set.Ioi t] t) (𝓝 l)
  l1_rightContinuous : ∀ t : ι,
    Tendsto (fun s ↦ ∫ ω, ‖C s ω - C t ω‖ ∂P) (𝓝[>] t) (𝓝 0)

/-- A class of functions that forces a càdlàg modification: every `f ∈ Φ` admits
a compensated decomposition along some `Y ∈ 𝓧`. -/
def IsRegularizingClass (Φ : Set (E → 𝕂)) (X : ι → Ω → E) (𝓧 : Set (ι → Ω → 𝕂))
    (𝓕 : Filtration ι m) (P : Measure Ω) (D : Set ι) : Prop :=
  ∀ f ∈ Φ, ∃ Y ∈ 𝓧, ∃ C : ι → Ω → 𝕂, IsCompensatorFor X 𝓕 P D f Y C

/-- For every `ε` and `T` a compact set that the path meets on `Iic T ∩ D` with
probability more than `1 - ε`. -/
def CompactContainment (X : ι → Ω → E) (P : Measure Ω) (D : Set ι) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ T : ι, ∃ K : Set E, IsCompact K ∧
    1 - ε < (P {ω | ∀ t ∈ Set.Iic T ∩ D, X t ω ∈ K}).toReal

/-- A regularizing class whose countable subset separates the points of `E`, and
compact containment, give a modification with càdlàg paths.  The conclusion is
the path property rather than membership in `D(ι, E)`, which is the object of the
roadmap **SkorokhodSpace**. -/
theorem exists_cadlag_modification_of_isRegularizingClass {Φ : Set (E → 𝕂)}
    {X : ι → Ω → E} {𝓧 : Set (ι → Ω → 𝕂)} {𝓕 : Filtration ι m} {P : Measure Ω}
    {D : Set ι} (hD : D.Countable) (hD' : Dense D)
    (hΦ : IsRegularizingClass Φ X 𝓧 𝓕 P D) (hΦsep : IsSeparating Φ)
    (hΦcount : ∃ Φ₀ ⊆ Φ, Φ₀.Countable ∧ ∀ x y : E, x ≠ y → ∃ f ∈ Φ₀, f x ≠ f y)
    (hcc : CompactContainment X P D) :
    ∃ X' : ι → Ω → E, (∀ t : ι, ∀ᵐ ω ∂P, X' t ω = X t ω) ∧
      ∀ᵐ ω ∂P, IsCadlagPath (fun t ↦ X' t ω) := sorry

/-- A càdlàg process reaches its left limits along every nondecreasing sequence
of stopping times. The bound `t` keeps the stopping times bounded, which is what
optional sampling needs, and is why the statement is quantified over `t` rather
than over the event `{τ < ∞}`. -/
def IsQuasiLeftContinuous (X : ι → Ω → E) (𝓕 : Filtration ι m)
    (P : Measure Ω) : Prop :=
  ∀ τ : ℕ → Ω → WithTop ι, (∀ n, IsStoppingTime 𝓕 (τ n)) → Monotone τ → ∀ t : ι,
    ∀ᵐ ω ∂P, (⨆ n, τ n ω) ≤ (t : WithTop ι) →
      Tendsto (fun n ↦ stoppedValue X (τ n) ω) atTop
        (𝓝 (stoppedValue X (fun ω ↦ ⨆ n, τ n ω) ω))

omit [MeasurableSpace E] in
/-- Read at the constant stopping times `τ n = s n` with `s n ↑ t`, the
definition says that the path reaches its left limit at every `t` that is a limit
from the left.  This sharpens Ethier--Kurtz, Lemma 3.7.7, which says only that
the set of failing `t` is countable.

Two hypotheses that the roadmap text does not name are indispensable, and both
were found by writing the proof.

* `¬ IsMin t` is **not** enough, and the statement under it is false: on `ι = ℕ`
  and `t = 1` every monotone sequence of stopping times bounded by `1` is
  eventually constant, so quasi-left-continuity is vacuous, while
  `𝓝[<] (1 : ℕ) = pure 0` and hence `leftLim (X · ω) 1 = X 0 ω`, which for
  `Ω` a point and `X 0 ω ≠ X 1 ω` is not `X 1 ω`.  What is needed is that `t` is
  approached from the left by a sequence, exactly the hypothesis that
  `not_isQuasiLeftContinuous_of_atom` carries.
* Quasi-left-continuity alone gives convergence along **one** sequence at a time,
  and the almost sure quantifier sits inside, so the exceptional set depends on
  the sequence and uncountably many sequences may not be combined.  The passage
  from a sequence to the filter `𝓝[<] t` therefore needs the existence of the
  left limit as a hypothesis -- the second half of `IsCadlagPath`, which is what
  Ethier--Kurtz assume at this point anyway. -/
theorem IsQuasiLeftContinuous.ae_eq_leftLim [T2Space E] {X : ι → Ω → E}
    {𝓕 : Filtration ι m} {P : Measure Ω} (h : IsQuasiLeftContinuous X 𝓕 P) {t : ι}
    {s : ℕ → ι} (hmono : Monotone s) (hlt : ∀ n, s n < t)
    (hs : Tendsto s atTop (𝓝 t))
    (hX : ∀ᵐ ω ∂P, ∃ l, Tendsto (fun r ↦ X r ω) (𝓝[<] t) (𝓝 l)) :
    ∀ᵐ ω ∂P, Function.leftLim (fun r ↦ X r ω) t = X t ω := by
  have hs' : Tendsto s atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs (.of_forall hlt)
  have : (𝓝[<] t).NeBot := hs'.neBot
  have hbdd : BddAbove (Set.range s) := ⟨t, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  have hsup : ⨆ n, s n = t := tendsto_nhds_unique (tendsto_atTop_ciSup hmono hbdd) hs
  have hsupT : (⨆ n, ((s n : WithTop ι))) = (t : WithTop ι) := by
    rw [← WithTop.coe_iSup s hbdd, hsup]
  have hq := h (fun n _ ↦ (s n : WithTop ι)) (fun n ↦ isStoppingTime_const 𝓕 _)
    (fun a b hab _ ↦ WithTop.coe_le_coe.2 (hmono hab)) t
  filter_upwards [hq, hX] with ω hω hlω
  obtain ⟨l, hl⟩ := hlω
  have h1 : Tendsto (fun n ↦ X (s n) ω) atTop (𝓝 l) := hl.comp hs'
  have h2 : Tendsto (fun n ↦ X (s n) ω) atTop (𝓝 (X t ω)) := by
    have := hω (le_of_eq hsupT)
    simpa only [stoppedValue, hsupT, WithTop.untopD_coe] using this
  rw [leftLim_eq_of_tendsto hl, tendsto_nhds_unique h1 h2]

omit [MeasurableSpace E] [TopologicalSpace ι] [OrderTopology ι] in
/-- The contrapositive half of the previous lemma, and the only half a
counterexample needs: a single nondecreasing sequence `s n` with supremum `t`
along which the path fails, almost surely, to reach `X t`, refutes
quasi-left-continuity.

It is the reusable part of `not_isQuasiLeftContinuous_of_atom`: the constant
stopping times `τ n = s n` are the ones the definition is tested on, no left
limit has to exist, and neither `T2Space E` nor a topology on the index beyond
the order one enters.  What the counterexample still has to supply after this
lemma is the martingale problem, not the failure of convergence. -/
theorem not_isQuasiLeftContinuous_of_not_ae_tendsto {X : ι → Ω → E}
    {𝓕 : Filtration ι m} {P : Measure Ω} {t : ι} {s : ℕ → ι} (hmono : Monotone s)
    (hlt : ∀ n, s n ≤ t) (hsup : ⨆ n, s n = t)
    (hX : ¬ ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (s n) ω) atTop (𝓝 (X t ω))) :
    ¬ IsQuasiLeftContinuous X 𝓕 P := by
  intro h
  refine hX ?_
  have hbdd : BddAbove (Set.range s) := ⟨t, by rintro _ ⟨n, rfl⟩; exact hlt n⟩
  have hsupT : (⨆ n, ((s n : WithTop ι))) = (t : WithTop ι) := by
    rw [← WithTop.coe_iSup s hbdd, hsup]
  have hq := h (fun n _ ↦ (s n : WithTop ι)) (fun n ↦ isStoppingTime_const 𝓕 _)
    (fun a b hab _ ↦ WithTop.coe_le_coe.2 (hmono hab)) t
  filter_upwards [hq] with ω hω
  have := hω (le_of_eq hsupT)
  simpa only [stoppedValue, hsupT, WithTop.untopD_coe] using this

/-- Left continuity in `L¹` along stopping times: along every nondecreasing
sequence `τ` of stopping times with supremum `τ'`, the increments of `C` between
`min (τ n) t` and `min τ' t` tend to `0` in `L¹`.  This is the hypothesis on the
compensator that quasi-left-continuity needs and the càdlàg theorem does not. -/
def IsL1LeftContinuousAlongStoppingTimes (C : ι → Ω → 𝕂) (𝓕 : Filtration ι m)
    (P : Measure Ω) : Prop :=
  ∀ τ : ℕ → Ω → WithTop ι, (∀ n, IsStoppingTime 𝓕 (τ n)) → Monotone τ → ∀ t : ι,
    Tendsto (fun n ↦ ∫ ω,
        ‖stoppedValue C (fun ω ↦ min (⨆ k, τ k ω) (t : WithTop ι)) ω -
          stoppedValue C (fun ω ↦ min (τ n ω) (t : WithTop ι)) ω‖ ∂P)
      atTop (𝓝 0)

/-- The abstract form of Ethier--Kurtz, Theorem 4.3.12: no operator and no
compensator of any special shape.  Being separating is the only hypothesis on `Φ`
this shares with `exists_cadlag_modification_of_isRegularizingClass`; no
countable subset separating the points of `E` is used, and no compact
containment.  The compensator is quantified inside the hypothesis rather than
recovered from `IsRegularizingClass`, because it is *the* compensator attached to
`f` that must be right continuous and `L¹` left continuous. -/
theorem isQuasiLeftContinuous_of_isRegularizingClass {Φ : Set (E → 𝕂)}
    {X : ι → Ω → E} {𝓧 : Set (ι → Ω → 𝕂)} {𝓕 : Filtration ι m} {P : Measure Ω}
    {D : Set ι} (hΦsep : IsSeparating Φ)
    (hX : ∀ᵐ ω ∂P, IsCadlagPath (fun t ↦ X t ω))
    (hΦ : ∀ f ∈ Φ, ∃ Y ∈ 𝓧, ∃ C : ι → Ω → 𝕂, IsCompensatorFor X 𝓕 P D f Y C ∧
      (∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ C s ω) (Set.Ioi t) t) ∧
      IsL1LeftContinuousAlongStoppingTimes C 𝓕 P) :
    IsQuasiLeftContinuous X 𝓕 P := sorry

/-- The classical instance (Ethier--Kurtz, Theorem 4.3.12), for an operator with
separating domain and a solution with càdlàg paths, **provided the clock has no
atoms**.  The compensator is `∫ u in Q.interval c ⊥ t, g (X u) ∂q`, and it is
continuity from above of the clock along the shrinking intervals that gives the
`L¹` hypothesis of the abstract form. -/
theorem isQuasiLeftContinuous_of_isMPSolutionFor {A : Set ((E → 𝕂) × (E → 𝕂))}
    {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E} {𝓕 : Filtration ι m}
    {P : Measure Ω}
    (hA : ∀ p ∈ A, Continuous p.1 ∧ (∃ b, ∀ x, ‖p.1 x‖ ≤ b) ∧ ∃ b, ∀ x, ‖p.2 x‖ ≤ b)
    (hsep : IsSeparating (Prod.fst '' A))
    (hsol : IsMPSolution (mpFamily A Q c X) 𝓕 P)
    (hX : ∀ᵐ ω ∂P, IsCadlagPath (fun t ↦ X t ω))
    (hQ : Q.IsAtomless) :
    IsQuasiLeftContinuous X 𝓕 P := sorry

/-! ### The witness of `not_isQuasiLeftContinuous_of_atom`

The pieces of the counterexample that do not mention the martingale problem: the
fair coin, the path that flips it at `u`, that its paths are càdlàg for **every**
clock, and that it is not quasi-left-continuous.  What the counterexample needs
beyond this block is that the path solves the martingale problem for a separating
`A` -- and nothing else. -/

namespace AtomWitness

/-- The fair coin on `Bool`, the law of the witness. -/
noncomputable def coinMeasure : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance isProbabilityMeasure_coinMeasure : IsProbabilityMeasure coinMeasure := by
  constructor
  simp [coinMeasure, ENNReal.inv_two_add_inv_two]

theorem coinMeasure_singleton_true : coinMeasure {true} = (2 : ENNReal)⁻¹ := by
  simp [coinMeasure]

/-- The clock with an atom at `u` and nowhere else.  The σ-algebra of the index
is `⊤`, so every down-set is measurable for free; that is the cheapest clock
that exists, and it is the point of the example that even it is a clock. -/
noncomputable def atomClock (u : ι) : Clock ι where
  measurableSpace := ⊤
  q := @Measure.dirac ι ⊤ u
  measurableSet_Iic := fun _ ↦ trivial
  measurableSet_Iio := fun _ ↦ trivial
  measure_Iic_ne_top := fun t ↦ by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ (Set.Iic t)))
    simp

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
theorem atomClock_apply_singleton (u : ι) : (atomClock u).q {u} = 1 := by
  let _ : MeasurableSpace ι := ⊤
  exact Measure.dirac_apply_of_mem rfl

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
theorem atomClock_apply_singleton_ne_zero (u : ι) : (atomClock u).q {u} ≠ 0 := by
  rw [atomClock_apply_singleton]
  exact one_ne_zero

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
/-- The clock of the witness is **not** atomless, and at the very point where it
carries its mass.  This is what makes the sharpness claim a theorem instead of a
remark: `not_isQuasiLeftContinuous_of_atom` and
`isQuasiLeftContinuous_of_isMPSolutionFor` do not overlap, because the clock of
the first fails the hypothesis `hQ` of the second.  The proof is the singleton
inside the degenerate interval `{v | u ≤ v ∧ v ≤ u}` and `measure_mono`; note
that the interval is the same set for a preorder as for a partial order only
because nothing here needs antisymmetry. -/
theorem not_isAtomless_atomClock (u : ι) : ¬ (atomClock u).IsAtomless := by
  intro h
  refine atomClock_apply_singleton_ne_zero u (nonpos_iff_eq_zero.1 ?_)
  refine (measure_mono ?_).trans (h u).le
  rintro x rfl
  exact ⟨le_rfl, le_rfl⟩

/-- The path that is `false` strictly before `u` and shows the coin from `u` on.
Over `Ω = E = Bool` the coin is both the sample point and the state. -/
def coinProcess (u : ι) (t : ι) (ω : Bool) : Bool := if u ≤ t then ω else false

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
theorem coinProcess_of_le {u t : ι} (h : u ≤ t) (ω : Bool) :
    coinProcess u t ω = ω := if_pos h

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
theorem coinProcess_of_not_le {u t : ι} (h : ¬ u ≤ t) (ω : Bool) :
    coinProcess u t ω = false := if_neg h

omit [OrderBot ι] in
/-- The paths are càdlàg, whatever the clock does: they are locally constant on
either side of `u`.  This is the half of the example that
`exists_cadlag_modification_of_isRegularizingClass` predicts. -/
theorem isCadlagPath_coinProcess (u : ι) (ω : Bool) :
    IsCadlagPath fun t ↦ coinProcess u t ω := by
  constructor
  · intro t
    by_cases h : u ≤ t
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [coinProcess_of_le h, coinProcess_of_le (h.trans (le_of_lt hs))]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (not_le.1 h))]
        with s hs
      rw [coinProcess_of_not_le h, coinProcess_of_not_le (not_le.2 hs)]
  · intro t
    by_cases h : u < t
    · refine ⟨ω, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds h)] with s hs
      exact (coinProcess_of_le (le_of_lt hs) ω).symm
    · refine ⟨false, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (coinProcess_of_not_le (not_le.2 (lt_of_lt_of_le hs (not_lt.1 h))) ω).symm

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- The path is not quasi-left-continuous along any sequence increasing to `u`:
it is `false` at every `s n` and the coin at `u`, so the almost sure convergence
would say that the coin is almost surely `false`.  The filtration is arbitrary --
quasi-left-continuity fails for every one of them, because the constant stopping
times used by `not_isQuasiLeftContinuous_of_not_ae_tendsto` are stopping times
for every filtration. -/
theorem not_isQuasiLeftContinuous_coinProcess (u : ι) {s : ℕ → ι}
    (hmono : Monotone s) (hlt : ∀ n, s n < u) (hsup : ⨆ n, s n = u)
    (𝓕 : Filtration ι (inferInstance : MeasurableSpace Bool)) :
    ¬ IsQuasiLeftContinuous (coinProcess u) 𝓕 coinMeasure := by
  refine not_isQuasiLeftContinuous_of_not_ae_tendsto hmono (fun n ↦ (hlt n).le) hsup ?_
  intro hae
  have hfalse : ∀ᵐ ω ∂coinMeasure, ω = false := by
    filter_upwards [hae] with ω hω
    have h1 : (fun n : ℕ ↦ coinProcess u (s n) ω) = fun _ ↦ false := by
      funext n
      exact coinProcess_of_not_le (not_le.2 (hlt n)) ω
    rw [h1, coinProcess_of_le le_rfl] at hω
    exact (tendsto_const_nhds_iff.1 hω).symm
  rw [ae_iff] at hfalse
  have hset : {ω : Bool | ¬ ω = false} = {true} := by
    ext ω; cases ω <;> simp
  rw [hset, coinMeasure_singleton_true] at hfalse
  exact (by simp : ((2 : ENNReal)⁻¹ ≠ 0)) hfalse

/-- Every real function on the coin is integrable: `Bool` is finite, so every
function on it is measurable and bounded, and the measure is finite. -/
theorem integrable_bool {μ : Measure Bool} [IsFiniteMeasure μ] (f : Bool → ℝ) :
    Integrable f μ :=
  (memLp_top_of_bound (measurable_of_finite f).aestronglyMeasurable
    (max ‖f true‖ ‖f false‖) (.of_forall fun b ↦ by
      cases b
      · exact le_max_right _ _
      · exact le_max_left _ _)).integrable le_top

/-- The integral against the fair coin is the mean of the two values. -/
theorem integral_coinMeasure (f : Bool → ℝ) :
    ∫ ω, f ω ∂coinMeasure = 2⁻¹ * f true + 2⁻¹ * f false := by
  rw [coinMeasure, integral_smul_measure,
    integral_add_measure (integrable_bool f) (integrable_bool f),
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The test pair of the witness: the indicator of `true`, and the constant
density `2⁻¹` of the compensator.  The constant is not a choice: the martingale
property across `u` is exactly `p.1 true - p.1 false = p.2 true + p.2 false`. -/
noncomputable def coinPair : (Bool → ℝ) × (Bool → ℝ) :=
  (fun b ↦ if b then (1 : ℝ) else 0, fun _ ↦ (2 : ℝ)⁻¹)

/-- The one element operator of the witness. -/
noncomputable def coinClass : Set ((Bool → ℝ) × (Bool → ℝ)) := {coinPair}

/-- A single indicator separates the probability measures on `Bool`: it pins the
mass of `{true}`, and the mass of `{false}` is what is left of the total mass.
This is what forces `A ≠ ∅` in `not_isQuasiLeftContinuous_of_atom`. -/
theorem isSeparating_coinClass : IsSeparating (Prod.fst '' coinClass) := by
  have key : ∀ ρ : Measure Bool, ∫ ω, coinPair.1 ω ∂ρ = ρ.real {true} := by
    intro ρ
    have hind : coinPair.1 = Set.indicator {true} fun _ ↦ (1 : ℝ) := by
      funext b; cases b <;> simp [coinPair]
    rw [hind, integral_indicator_const _ (measurableSet_singleton true)]
    simp
  intro μ ν _ _ h
  have h1 : μ.real {true} = ν.real {true} := by
    rw [← key μ, ← key ν]
    exact h coinPair.1 ⟨coinPair, rfl, rfl⟩
  refine MeasureTheory.ext_iff_measureReal_singleton.2 fun b ↦ ?_
  cases b
  · have hc : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
    have hμ := measureReal_add_measureReal_compl (μ := μ) (measurableSet_singleton true)
    have hν := measureReal_add_measureReal_compl (μ := ν) (measurableSet_singleton true)
    rw [hc] at hμ hν
    simp only [probReal_univ] at hμ hν
    linarith
  · exact h1

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
/-- The mass the clock puts on a set containing its atom.  Two lemmas rather than
one with an `if`, because membership in the compensating interval carries no
`Decidable` instance. -/
theorem atomClock_real_of_mem (u : ι) {S : Set ι} (h : u ∈ S) :
    (atomClock u).q.real S = 1 := by
  let _ : MeasurableSpace ι := ⊤
  have hq : (atomClock u).q S = S.indicator 1 u := Measure.dirac_apply' u trivial
  rw [measureReal_def, hq, Set.indicator_of_mem h]
  simp

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
/-- The mass the clock puts on a set avoiding its atom. -/
theorem atomClock_real_of_notMem (u : ι) {S : Set ι} (h : u ∉ S) :
    (atomClock u).q.real S = 0 := by
  let _ : MeasurableSpace ι := ⊤
  have hq : (atomClock u).q S = S.indicator 1 u := Measure.dirac_apply' u trivial
  rw [measureReal_def, hq, Set.indicator_of_notMem h]
  simp

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- The compensator of the witness: it fires once, at `u`, and it fires in the
optional convention only.  `hu` says that `u` is not the bottom of the index,
which is what `Q.interval c ⊥ t` needs in order to see the atom at all. -/
theorem integral_coinPair_snd (u : ι) (hu : ¬ u ≤ (⊥ : ι)) (t : ι) (ω : Bool) :
    ∫ s in (atomClock u).interval Clock.Conv.optional ⊥ t,
        coinPair.2 (coinProcess u s ω) ∂(atomClock u).q
      = if u ≤ t then (2 : ℝ)⁻¹ else 0 := by
  have hconst : ∀ s : ι, coinPair.2 (coinProcess u s ω) = (2 : ℝ)⁻¹ := fun _ ↦ rfl
  simp_rw [hconst]
  rw [setIntegral_const]
  have hmem : u ∈ (atomClock u).interval Clock.Conv.optional ⊥ t ↔ u ≤ t := by
    simp only [Clock.interval, Set.mem_sdiff, Set.mem_Iic]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hu⟩⟩
  by_cases h : u ≤ t
  · rw [atomClock_real_of_mem u (hmem.2 h), if_pos h]
    simp
  · rw [atomClock_real_of_notMem u fun hc ↦ h (hmem.1 hc), if_neg h]
    simp

/-- The filtration of the witness: nothing before `u`, everything from `u` on.
It is the natural filtration of `coinProcess u`. -/
def coinFiltration (u : ι) : Filtration ι (inferInstance : MeasurableSpace Bool) where
  seq t := if u ≤ t then (inferInstance : MeasurableSpace Bool) else ⊥
  mono' := fun a b hab ↦ by
    show (if u ≤ a then (inferInstance : MeasurableSpace Bool) else ⊥) ≤
      (if u ≤ b then (inferInstance : MeasurableSpace Bool) else ⊥)
    by_cases ha : u ≤ a
    · simp only [if_pos ha, if_pos (ha.trans hab), le_refl]
    · simp only [if_neg ha]
      exact bot_le
  le' := fun t ↦ by
    show (if u ≤ t then (inferInstance : MeasurableSpace Bool) else ⊥) ≤
      (inferInstance : MeasurableSpace Bool)
    by_cases ht : u ≤ t
    · simp only [if_pos ht, le_refl]
    · simp only [if_neg ht]
      exact bot_le

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- The coin flipped at `u` solves the martingale problem for `coinClass`, the
clock with its atom at `u` and the optional convention.  Two computations and no
theory: the compensator is `2⁻¹` from `u` on and `0` before it, so the process is
`0` before `u` and centred afterwards, and the conditional expectation across `u`
is the mean of the coin. -/
theorem isMPSolution_coinProcess (u : ι) (hu : ¬ u ≤ (⊥ : ι)) :
    IsMPSolution (mpFamily coinClass (atomClock u) Clock.Conv.optional (coinProcess u))
      (coinFiltration u) coinMeasure := by
  rintro Y ⟨p, hp, hY⟩
  simp only [coinClass, Set.mem_singleton_iff] at hp
  subst hp
  have hval : ∀ (t : ι) (ω : Bool),
      Y t ω = if u ≤ t then ((if ω then (1 : ℝ) else 0) - 2⁻¹) else 0 := by
    intro t ω
    rw [hY t ω, integral_coinPair_snd u hu t ω]
    by_cases h : u ≤ t
    · simp only [if_pos h, coinProcess_of_le h]
      rfl
    · simp only [if_neg h, coinProcess_of_not_le h]
      norm_num [coinPair]
  have hbefore : ∀ t : ι, ¬ u ≤ t → Y t = fun _ ↦ (0 : ℝ) :=
    fun t ht ↦ funext fun ω ↦ by rw [hval t ω, if_neg ht]
  have hzero : ∀ t : ι, ∫ ω, Y t ω ∂coinMeasure = 0 := by
    intro t
    simp only [hval t]
    by_cases ht : u ≤ t
    · simp only [if_pos ht]
      rw [integral_coinMeasure]
      norm_num
    · simp only [if_neg ht]
      simp
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · by_cases ht : u ≤ t
    · have hf : (coinFiltration u) t = (inferInstance : MeasurableSpace Bool) := if_pos ht
      rw [hf]
      exact (measurable_of_finite _).stronglyMeasurable
    · have hf : (coinFiltration u) t = ⊥ := if_neg ht
      rw [hf, hbefore t ht]
      exact stronglyMeasurable_const
  · by_cases hs : u ≤ s
    · have hYts : Y t = Y s := funext fun ω ↦ by
        rw [hval t ω, hval s ω, if_pos (hs.trans hst), if_pos hs]
      have hle : (coinFiltration u) s ≤ (inferInstance : MeasurableSpace Bool) :=
        (coinFiltration u).le' s
      have hsm : StronglyMeasurable[(coinFiltration u) s] (Y s) := by
        rw [show (coinFiltration u) s = (inferInstance : MeasurableSpace Bool) from if_pos hs]
        exact (measurable_of_finite _).stronglyMeasurable
      rw [hYts, condExp_of_stronglyMeasurable hle hsm (integrable_bool _)]
    · have hf : (coinFiltration u) s = ⊥ := if_neg hs
      rw [hf, hbefore s hs, condExp_bot]
      exact Filter.Eventually.of_forall fun _ ↦ hzero t

end AtomWitness

/-- The sharpness, as a named example and not as a remark: an atom of the clock
at a point `u` approachable from the left is a fixed time of discontinuity, so
the existence of a càdlàg modification -- which holds for **every** clock -- and
quasi-left-continuity separate exactly at the atoms.  The witness is a fair coin
flipped at `u`, constant on either side of it, over `E = Bool`.

**The witness must satisfy every hypothesis of
`isQuasiLeftContinuous_of_isMPSolutionFor` except `hQ`, and the statement says
so.**  Without that the example is empty: with `A = ∅` the family
`mpFamily A Q c X` is empty, `IsMPSolution` holds of everything, and any process
that is not quasi-left-continuous -- a fair coin over the one point index, with
`Q.q = Measure.dirac u` -- proves the statement while showing nothing about
atoms.  A sharpness claim that admits a vacuous witness is not a sharpness
claim, so `hA`, `hsep` and the càdlàg paths are carried in the conclusion.
`hsep` is what forces `A ≠ ∅`: on `Bool` the empty class does not separate,
since the two probability measures `Measure.dirac true` and `Measure.dirac
false` are distinct.  `IsProbabilityMeasure P` rules out `P = 0` for the same
reason.  Found on 2026-09-07, sixth run of the day. -/
theorem not_isQuasiLeftContinuous_of_atom (u : ι)
    (hu : ∃ s : ℕ → ι, StrictMono s ∧ (∀ n, s n < u) ∧ Tendsto s atTop (𝓝 u)) :
    ∃ (Ω' : Type) (m' : MeasurableSpace Ω') (P : @Measure Ω' m')
      (_ : @IsProbabilityMeasure Ω' m' P)
      (𝓕 : @Filtration Ω' ι _ m') (Q : Clock ι) (c : Clock.Conv)
      (A : Set ((Bool → ℝ) × (Bool → ℝ))) (X : ι → Ω' → Bool),
      Q.q {u} ≠ 0 ∧
        (∀ p ∈ A, Continuous p.1 ∧ (∃ b, ∀ x, ‖p.1 x‖ ≤ b) ∧
          ∃ b, ∀ x, ‖p.2 x‖ ≤ b) ∧
        IsSeparating (Prod.fst '' A) ∧
        (∀ᵐ ω ∂P, IsCadlagPath fun t ↦ X t ω) ∧
        @IsMPSolution ι _ Ω' m' ℝ _ (mpFamily A Q c X) 𝓕 P ∧
        ¬ IsQuasiLeftContinuous X 𝓕 P := by
  obtain ⟨s, hmono, hlt, hs⟩ := hu
  have hbot : ¬ u ≤ (⊥ : ι) := fun h ↦ not_lt_bot ((hlt 0).trans_le h)
  have hbdd : BddAbove (Set.range s) := ⟨u, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  have hsup : ⨆ n, s n = u :=
    tendsto_nhds_unique (tendsto_atTop_ciSup hmono.monotone hbdd) hs
  refine ⟨Bool, inferInstance, AtomWitness.coinMeasure, inferInstance,
    AtomWitness.coinFiltration u, AtomWitness.atomClock u, Clock.Conv.optional,
    AtomWitness.coinClass, AtomWitness.coinProcess u,
    AtomWitness.atomClock_apply_singleton_ne_zero u, ?_, AtomWitness.isSeparating_coinClass,
    Filter.Eventually.of_forall (AtomWitness.isCadlagPath_coinProcess u),
    AtomWitness.isMPSolution_coinProcess u hbot,
    AtomWitness.not_isQuasiLeftContinuous_coinProcess u hmono.monotone hlt hsup _⟩
  rintro p hp
  simp only [AtomWitness.coinClass, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨continuous_of_discreteTopology, ⟨1, fun x ↦ ?_⟩, ⟨2⁻¹, fun _ ↦ ?_⟩⟩
  · cases x <;> norm_num [AtomWitness.coinPair]
  · norm_num [AtomWitness.coinPair]

/-- The hypothesis of `not_isQuasiLeftContinuous_of_atom` is satisfiable, and the
witness is exhibited rather than asserted: `ι = ENNReal` carries all four instances
the section asks of the index -- `ConditionallyCompleteLinearOrder`, `OrderBot`,
`TopologicalSpace`, `OrderTopology` -- and `u = ⊤` is approached strictly from
the left by `n ↦ (n : ENNReal)`.

This is the check the two empty statements of 2026-09-05 and 2026-09-07 would
have failed: a theorem whose hypotheses no instance satisfies proves nothing,
however honest its proof.  Added 2026-09-07, tenth run. -/
theorem exists_index_witness_for_atom :
    ∃ s : ℕ → ENNReal, StrictMono s ∧ (∀ n, s n < (⊤ : ENNReal)) ∧
      Tendsto s atTop (𝓝 (⊤ : ENNReal)) :=
  ⟨fun n => (n : ENNReal), Nat.strictMono_cast (α := ENNReal),
    fun n => lt_top_iff_ne_top.2 (ENNReal.natCast_ne_top n),
    ENNReal.tendsto_nat_nhds_top⟩

end Regularizing

/-! ## Milestone 10: the abstract convergence theorem

Stated without any topology on the path space: the hypothesis is convergence in
distribution of real random variables, one at a time.  That it is one at a time
and not jointly is what the manuscript's remark on the topology free form says --
the proof uses the continuous mapping theorem only to know that `Y₀ r (Xⁿ)` and
`(Y₀ t - Y₀ s) * Z (Xⁿ)` converge in distribution, "and nothing else", so no
joint law occurs anywhere in it. -/

section AbstractConvergence

variable {F : Type*} [MeasurableSpace F]

/-- Convergence in distribution of random variables that live on **different**
probability spaces, written by testing against bounded continuous functions.
Mathlib's `MeasureTheory.TendstoInDistribution`
(`MeasureTheory/Function/ConvergenceInDistribution.lean`) is the same notion for
one fixed space; here the `n`-th variable lives on `Ω' n`, which is what a
sequence of solutions of martingale problems gives. -/
def TendstoLaw {V : Type*} [TopologicalSpace V] {Ω' : ℕ → Type*}
    (m' : ∀ n, MeasurableSpace (Ω' n)) (P' : ∀ n, @Measure (Ω' n) (m' n))
    (ξ : ∀ n, Ω' n → V) (P : Measure Ω) (ξ₀ : Ω → V) : Prop :=
  ∀ φ : V → ℝ, Continuous φ → (∃ b, ∀ x, ‖φ x‖ ≤ b) →
    Tendsto (fun n ↦ ∫ ω, φ (ξ n ω) ∂(P' n)) atTop (𝓝 (∫ ω, φ (ξ₀ ω) ∂P))

/-- The abstract convergence theorem.  The three hypotheses are (a) convergence
in distribution of the two families of real random variables, (b) their uniform
integrability across the spaces, and (c) that the tested increments vanish in the
limit; the conclusion is the martingale identity along `D`.

The canonical version is bound inside the hypothesis, as in the manuscript's
`(C3)`: it is *a* canonical version of `Y` for which (a), (b) and (c) hold, not
every one. -/
theorem mpSolution_of_tendsto {𝓧 : Set (ι → Ω → 𝕂)} {𝓧₀ : ι → Set (F → 𝕂)}
    {𝓩 : ι → Set (F → ℝ)} {X : Ω → F} {𝓕 : Filtration ι m} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Set ι} {Ω' : ℕ → Type*}
    {m' : ∀ n, MeasurableSpace (Ω' n)} {P' : ∀ n, @Measure (Ω' n) (m' n)}
    {X' : ∀ n, Ω' n → F}
    (hdet : IsDetermining 𝓩 𝓧 X 𝓕)
    (hY : ∀ Y ∈ 𝓧, ∃ Y₀ : ι → F → 𝕂, (∀ t, Y₀ t ∈ 𝓧₀ t) ∧
      (∀ t, StronglyMeasurable (Y₀ t)) ∧ (∀ t ω, Y t ω = Y₀ t (X ω)) ∧
      ∀ t ∈ D, ∀ s ∈ D ∩ Set.Iic t, ∀ Z ∈ 𝓩 s,
        (∀ r ∈ D ∩ Set.Iic t,
            TendstoLaw m' P' (fun n ω ↦ Y₀ r (X' n ω)) P fun ω ↦ Y₀ r (X ω)) ∧
        TendstoLaw m' P'
            (fun n ω ↦ (Y₀ t (X' n ω) - Y₀ s (X' n ω)) * (Z (X' n ω) : 𝕂)) P
            (fun ω ↦ (Y₀ t (X ω) - Y₀ s (X ω)) * (Z (X ω) : 𝕂)) ∧
        (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ (n : ℕ), ∀ r ∈ D ∩ Set.Iic t,
            ∫ ω in {ω | c ≤ ‖Y₀ r (X' n ω)‖}, ‖Y₀ r (X' n ω)‖ ∂(P' n) ≤ ε) ∧
        Tendsto (fun n ↦ ∫ ω, (Y₀ t (X' n ω) - Y₀ s (X' n ω)) * (Z (X' n ω) : 𝕂)
            ∂(P' n)) atTop (𝓝 0)) :
    ∀ Y ∈ 𝓧, ∀ s ∈ D, ∀ t ∈ D, s ≤ t → P[Y t | 𝓕 s] =ᵐ[P] Y s := sorry

end AbstractConvergence

section FromDense

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

/-- From the martingale identity along a countable dense `D` to the whole index:
right continuity of the members of `𝓧` and the uniform integrability of Step 2
of the proof carry it across.  `D` must contain the greatest element of `ι` if
there is one, because no sequence in `D` approaches it from the right. -/
theorem isMPSolution_of_forall_condExp_eq_of_dense {𝓧 : Set (ι → Ω → 𝕂)}
    {𝓕 : Filtration ι m} {P : Measure Ω} [IsProbabilityMeasure P] {D : Set ι}
    (hD : D.Countable) (hD' : Dense D) (hDmax : ∀ t : ι, IsMax t → t ∈ D)
    (hadapt : ∀ Y ∈ 𝓧, StronglyAdapted 𝓕 Y)
    (hint : ∀ Y ∈ 𝓧, ∀ t : ι, Integrable (Y t) P)
    (hright : ∀ Y ∈ 𝓧, ∀ᵐ ω ∂P, ∀ t : ι,
      ContinuousWithinAt (fun s ↦ Y s ω) (Set.Ioi t) t)
    (h : ∀ Y ∈ 𝓧, ∀ s ∈ D, ∀ t ∈ D, s ≤ t → P[Y t | 𝓕 s] =ᵐ[P] Y s) :
    IsMPSolution 𝓧 𝓕 P := sorry

end FromDense

/-! ## Milestone 4: the paths the jump construction delivers

The jump process of Milestone 4 is built to have paths that are constant between
consecutive jumps and jump only finitely often in finite time.  Three otherwise
awkward steps of that construction are easy on such paths: the joint
measurability in `(t, ω)` is a sum over finitely many pieces instead of a limit
argument, the assignment `t ↦ n` of a time to its jump index is a `Nat.find`,
and the càdlàg property is immediate.  The property is therefore isolated first,
as a **predicate** and not as a type class -- it is a property of a term, so
instance search would have nothing to key on, and Mathlib's fallback `Fact` is
expressly not meant for this (`Logic/Basic.lean`, library note "fact
non-instances"). -/

section StepPath

variable {ι : Type*} [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
variable {E : Type*} [TopologicalSpace E]

/-- **A step path**: constant on a right neighbourhood of every point, and
constant on some left neighbourhood of every point.

**This is not the condition the roadmap first proposed, and the difference is
not a matter of taste.**  The proposal was to ask for the *jump set* to be
locally finite,

```
∀ K : Set ι, IsCompact K → ({x | Function.leftLim f x ≠ f x} ∩ K).Finite
```

and to derive right continuity and the existence of left limits from it.  That
implication is **false**, and the witness is one line:
`exists_finite_setOf_leftLim_ne_not_isCadlagPath` below exhibits
`f = Set.indicator {0} 1` on `ℝ`, whose jump set is the single point `0` -- so
the condition holds on every compact set -- and which is not right continuous at
`0`.  The reason is that `Function.leftLim` is *total*
(`Topology/Order/LeftRightLim.lean:50`): where no left limit exists it returns
the value `f x`, so a path with no left limits anywhere has an **empty** jump
set and passes the test vacuously.  A condition on the jump set alone therefore
cannot see either half of càdlàg.

Constancy on a one sided neighbourhood sees both, and it is what the
construction actually produces: between two consecutive jump times the path does
not move.  Right continuity is the first conjunct read as a limit, the left
limit is the constant of the second, and the local finiteness of the jumps is a
*consequence* (`IsStepPath.finite_setOf_not_continuousAt_inter`) rather than the
definition. -/
def IsStepPath (f : ι → E) : Prop :=
  (∀ x : ι, ∀ᶠ y in 𝓝[≥] x, f y = f x) ∧ ∀ x : ι, ∃ c, ∀ᶠ y in 𝓝[<] x, f y = c

omit [OrderTopology ι] in
/-- **A step path is càdlàg.**  Both halves are the same two lines: a function
that is eventually constant along a filter converges along it to that constant.
Right continuity uses `𝓝[>] x ≤ 𝓝[≥] x`, which is where the first conjunct is
stated on the *closed* right neighbourhood -- that is the form the construction
delivers, since the path takes the value `f x` at `x` itself and keeps it. -/
theorem IsStepPath.isCadlagPath {f : ι → E} (hf : IsStepPath f) : IsCadlagPath f := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have h : ∀ᶠ y in 𝓝[>] t, f y = f t :=
      (hf.1 t).filter_mono (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
    exact Filter.Tendsto.congr' (h.mono fun y hy => hy.symm) tendsto_const_nhds
  · obtain ⟨c, hc⟩ := hf.2 t
    exact ⟨c, Filter.Tendsto.congr' (hc.mono fun y hy => hy.symm) tendsto_const_nhds⟩

/-- **A step path is discontinuous at only finitely many points of a compact
set.**  This is the property the construction is built for, and on the present
definition it is a theorem rather than a hypothesis.

The proof is `IsCompact.elim_nhds_subcover` against a punctured neighbourhood of
continuity, exactly as in `IsCadlag.finite_largeLeftJumpSet_inter` of the
roadmap **SkorokhodSpace**.  The punctured neighbourhood costs nothing and needs
**no case distinction on `IsMax x` or `IsMin x`**: `mem_nhdsWithin` returns the
two witnesses already *open*, so the two conjuncts give open `V, W ∋ x` with
`f = f x` on `V ∩ Set.Ici x` and `f = c` on `W ∩ Set.Iio x`.  Since `Set.Ioi x`
and `Set.Iio x` are open in the order topology, `V ∩ Set.Ioi x` and
`W ∩ Set.Iio x` are open sets on which `f` is constant, so `f` is continuous at
every point of either; and by trichotomy every `y ∈ V ∩ W` other than `x` lies in
one of them.  Extracting intervals `Set.Ico x u` and `Set.Ioo l x` instead --
which is what a max or a min would make awkward -- is therefore not needed: what
carries the argument is that the two *sides* are open, not that they have
endpoints. -/
theorem IsStepPath.finite_setOf_not_continuousAt_inter {f : ι → E} (hf : IsStepPath f)
    {K : Set ι} (hK : IsCompact K) : ({x | ¬ ContinuousAt f x} ∩ K).Finite := by
  have key : ∀ x : ι, ∃ U ∈ 𝓝 x, ∀ y ∈ U, y ≠ x → ContinuousAt f y := by
    intro x
    obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.1 (hf.1 x)
    obtain ⟨c, hc⟩ := hf.2 x
    obtain ⟨W, hWo, hxW, hWsub⟩ := mem_nhdsWithin.1 hc
    refine ⟨V ∩ W, (hVo.inter hWo).mem_nhds ⟨hxV, hxW⟩, fun y hy hyx => ?_⟩
    rcases lt_trichotomy y x with hlt | heq | hgt
    · have hOpen : IsOpen (W ∩ Set.Iio x) := hWo.inter isOpen_Iio
      have hmem : y ∈ W ∩ Set.Iio x := ⟨hy.2, hlt⟩
      have hconst : ∀ z ∈ W ∩ Set.Iio x, f z = f y := by
        intro z hz
        rw [hWsub hz, hWsub hmem]
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hOpen.mem_nhds hmem] with z hz using (hconst z hz).symm
    · exact absurd heq hyx
    · have hOpen : IsOpen (V ∩ Set.Ioi x) := hVo.inter isOpen_Ioi
      have hmem : y ∈ V ∩ Set.Ioi x := ⟨hy.1, hgt⟩
      have hconst : ∀ z ∈ V ∩ Set.Ioi x, f z = f y := by
        intro z hz
        rw [hVsub ⟨hz.1, hz.2.le⟩, hVsub ⟨hmem.1, hmem.2.le⟩]
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hOpen.mem_nhds hmem] with z hz using (hconst z hz).symm
  choose U hU hUsub using key
  obtain ⟨s, -, hcover⟩ := hK.elim_nhds_subcover U fun x _ => hU x
  refine Set.Finite.subset s.finite_toSet ?_
  rintro y ⟨hy1, hy2⟩
  obtain ⟨x, hxs, hx⟩ := Set.mem_iUnion₂.1 (hcover hy2)
  by_contra hys
  exact hy1 (hUsub x y hx (by rintro rfl; exact hys hxs))

/-- **The witness against the jump set as a definition.**  There is an
`f : ℝ → ℝ` whose jump set meets every compact set in a finite set and which is
not càdlàg: `f = Set.indicator {0} 1`.

Its jump set is `{0}`, and the reason it is not bigger is the totality of
`Function.leftLim`: away from `0` the left limit is `0` and so is the value.  Its
failure is on the *other* side -- `f` is `0` on `Set.Ioi 0` and `1` at `0`, so it
is not right continuous at `0` -- and the jump set is blind to that, since the
jump set is defined from the left limit alone.

This is why `IsStepPath` is stated by constancy on one sided neighbourhoods and
not by a condition on the jump set. -/
theorem exists_finite_setOf_leftLim_ne_not_isCadlagPath :
    ∃ f : ℝ → ℝ, (∀ K : Set ℝ, IsCompact K →
        ({x : ℝ | Function.leftLim f x ≠ f x} ∩ K).Finite) ∧ ¬ IsCadlagPath f := by
  classical
  set f : ℝ → ℝ := Set.indicator {(0 : ℝ)} (fun _ => (1 : ℝ)) with hf_def
  have hf0 : f 0 = 1 := by simp [hf_def]
  have hfne : ∀ x : ℝ, x ≠ 0 → f x = 0 := by
    intro x hx
    simp [hf_def, hx]
  have hjump : {x : ℝ | Function.leftLim f x ≠ f x} ⊆ {0} := by
    intro x hx
    by_contra hx0
    refine hx ?_
    have hev : ∀ᶠ y in 𝓝[<] x, f y = 0 :=
      ((eventually_ne_nhds (by simpa using hx0)).filter_mono nhdsWithin_le_nhds).mono
        fun y hy => hfne y hy
    have htend : Tendsto f (𝓝[<] x) (𝓝 0) :=
      Filter.Tendsto.congr' (hev.mono fun y hy => hy.symm) tendsto_const_nhds
    rw [_root_.leftLim_eq_of_tendsto htend, hfne x (by simpa using hx0)]
  refine ⟨f, fun K hK => Set.Finite.subset (Set.finite_singleton (0 : ℝ)) ?_, ?_⟩
  · exact fun x hx => hjump hx.1
  · rintro ⟨hr, -⟩
    have h1 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := hr 0
    have h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hfne y (ne_of_gt hy)
    have hone := tendsto_nhds_unique h1 h0
    rw [hf0] at hone
    exact one_ne_zero hone

end StepPath

/-! ## Milestone 4: the jump process itself

The construction of `jumpProcess lam mu nu`, on an explicit probability space, and the proof
that its paths are the step paths of the block above.

The sample space is `(ℕ → E) × (ℕ → ℝ)`: the trajectory of the embedded Markov chain, and the
sequence of its waiting times.  The chain is Mathlib's Ionescu--Tulcea kernel
`ProbabilityTheory.Kernel.traj` with the family that reads the *last* coordinate -- unlike
`ProbabilityTheory.exists_kernel_pi_of_markov` of the roadmap **KolmogorovExtension**, whose
kernels read only the base point and which is therefore a product and not a chain.  The waiting
times are `MeasureTheory.Measure.infinitePi` of `ProbabilityTheory.expMeasure 1`.  Neither
carries a topology on `E`; only the path statements do.

The deterministic core is separated from the probabilistic one, and that separation is the point
of the block.  `stepIndex T t` is the index of the window `[T n, T (n+1))` containing `t`,
defined as `sInf {n | t < T (n+1)}` -- `Nat.find` made total by `sInf ∅ = 0`, which is what makes
the joint measurability in `(t, ω)` a description of countably many preimages rather than a
limit argument.  Everything about the paths is then a statement about `stepPath`, under the two
hypotheses `StrictMono T` and `∀ s, ∃ n, s < T (n+1)`; the second is exactly non explosion, and
`tendsto_jumpTime_atTop` is the only place where a bound on the rate is used. -/

section JumpConstruction

variable {E : Type*}

/-! ### The step index -/

/-- The index of the window a time belongs to: the least `n` with `t < T (n + 1)`.

`Nat.find` would need a proof of existence at every call.  `sInf` on `ℕ` is the same function
made total by `sInf ∅ = 0`, and the junk value is harmless: it is returned exactly on the
explosion set, where no window contains `t`. -/
noncomputable def stepIndex (T : ℕ → ℝ) (t : ℝ) : ℕ := sInf {n | t < T (n + 1)}

variable {T : ℕ → ℝ} {t : ℝ} {n : ℕ}

theorem lt_stepIndex_succ (hex : ∃ n, t < T (n + 1)) : t < T (stepIndex T t + 1) :=
  Nat.sInf_mem hex

theorem le_of_lt_stepIndex (h : n < stepIndex T t) : T (n + 1) ≤ t :=
  not_lt.1 (Nat.notMem_of_lt_sInf h)

theorem stepIndex_le (h : t < T (n + 1)) : stepIndex T t ≤ n := Nat.sInf_le h

/-- The characterisation of the step index by the window it names. -/
theorem stepIndex_eq_of (h1 : n = 0 ∨ T n ≤ t) (h2 : t < T (n + 1)) (hT : Monotone T) :
    stepIndex T t = n := by
  refine le_antisymm (stepIndex_le h2) ?_
  by_contra hlt
  push_neg at hlt
  rcases h1 with rfl | h1
  · exact Nat.not_lt_zero _ hlt
  · exact absurd (lt_stepIndex_succ ⟨n, h2⟩)
      (not_lt.2 ((h1.trans' (hT (Nat.succ_le_of_lt hlt))).trans_eq rfl))

/-- The left endpoint of the window is below the time, unless the index is `0`. -/
theorem T_stepIndex_le (h : stepIndex T t ≠ 0) : T (stepIndex T t) ≤ t := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [hm]
  exact le_of_lt_stepIndex (hm ▸ Nat.lt_succ_self m)

/-! ### The step path -/

/-- The path that takes the value `y n` on `[T n, T (n + 1))`. -/
noncomputable def stepPath (T : ℕ → ℝ) (y : ℕ → E) (t : ℝ) : E := y (stepIndex T t)

/-- Every time lies in a window: the index it receives has its left endpoint below it (or is
`0`) and its right endpoint above it. -/
theorem exists_stepIndex_window (hex : ∀ s : ℝ, ∃ n, s < T (n + 1)) (x : ℝ) :
    ∃ n, (n = 0 ∨ T n ≤ x) ∧ x < T (n + 1) := by
  refine ⟨stepIndex T x, ?_, lt_stepIndex_succ (hex x)⟩
  by_cases h : stepIndex T x = 0
  · exact Or.inl h
  · exact Or.inr (T_stepIndex_le h)

/-- **The path built from a strictly increasing, unbounded sequence of jump times is a step
path**, hence càdlàg by `IsStepPath.isCadlagPath`.

The two conjuncts are the two sides of a jump time and they are not symmetric.  On the right,
the window `Set.Ico x (T (n + 1))` of the index `n` of `x` itself works, because the path takes
the value `y n` *at* `x`.  On the left there are three cases, and the third is the only one that
uses `StrictMono` rather than `Monotone`: when `x = T (m + 1)` is itself a jump time, the
constant is `y m` and the neighbourhood is `Set.Ioo (T m) x`, which is a neighbourhood only
because `T m < T (m + 1)`.  The other two are `T n < x`, where the same window serves, and
`x ≤ T 0`, where the path is constant `y 0` on all of `Set.Iio x`. -/
theorem isStepPath_stepPath [TopologicalSpace E] (hT : StrictMono T)
    (hex : ∀ s : ℝ, ∃ n, s < T (n + 1)) (y : ℕ → E) : IsStepPath (stepPath T y) := by
  have hmono : Monotone T := hT.monotone
  have key : ∀ (s : ℝ) (m : ℕ), (m = 0 ∨ T m ≤ s) → s < T (m + 1) → stepPath T y s = y m := by
    intro s m h1 h2
    simp only [stepPath, stepIndex_eq_of h1 h2 hmono]
  constructor
  · intro x
    obtain ⟨n, hx1, hx2⟩ := exists_stepIndex_window hex x
    have hmem : Set.Ico x (T (n + 1)) ∈ 𝓝[≥] x := by
      refine mem_nhdsWithin.2 ⟨Set.Iio (T (n + 1)), isOpen_Iio, hx2, ?_⟩
      rintro z ⟨hz1, hz2⟩
      exact ⟨hz2, hz1⟩
    filter_upwards [hmem] with z hz
    rw [key z n (hx1.imp id (fun h => h.trans hz.1)) hz.2, key x n hx1 hx2]
  · intro x
    obtain ⟨n, hx1, hx2⟩ := exists_stepIndex_window hex x
    by_cases hlt : T n < x
    · refine ⟨y n, ?_⟩
      have hmem : Set.Ioo (T n) x ∈ 𝓝[<] x :=
        mem_nhdsWithin.2 ⟨Set.Ioi (T n), isOpen_Ioi, hlt, fun z hz => ⟨hz.1, hz.2⟩⟩
      filter_upwards [hmem] with z hz
      exact key z n (Or.inr hz.1.le) (hz.2.trans hx2)
    · push_neg at hlt
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · refine ⟨y 0, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with z (hz : z < x)
        exact key z 0 (Or.inl rfl) (hz.trans hx2)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        have hxeq : T (m + 1) = x :=
          le_antisymm (hx1.resolve_left (Nat.succ_ne_zero m)) hlt
        refine ⟨y m, ?_⟩
        have hmlt : T m < x := hxeq ▸ hT (Nat.lt_succ_self m)
        have hmem : Set.Ioo (T m) x ∈ 𝓝[<] x :=
          mem_nhdsWithin.2 ⟨Set.Ioi (T m), isOpen_Ioi, hmlt, fun z hz => ⟨hz.1, hz.2⟩⟩
        filter_upwards [hmem] with z hz
        exact key z m (Or.inr hz.1.le) (hxeq ▸ hz.2)

/-! ### Joint measurability in `(t, ω)` -/

/-- The step index, decided.  The second disjunct is the explosion set, on which the index is
`0` by the convention `sInf ∅ = 0` and not because the time lies in the zeroth window. -/
theorem stepIndex_eq_iff : stepIndex T t = n ↔
    ((t < T (n + 1) ∧ ∀ m < n, T (m + 1) ≤ t) ∨ (n = 0 ∧ ∀ k, T (k + 1) ≤ t)) := by
  constructor
  · intro h
    by_cases hne : ∃ k, t < T (k + 1)
    · exact Or.inl ⟨h ▸ lt_stepIndex_succ hne, fun m hm => le_of_lt_stepIndex (h ▸ hm)⟩
    · push_neg at hne
      refine Or.inr ⟨?_, hne⟩
      rw [← h]
      exact Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_iff_forall_notMem.2
        fun k hk => absurd hk (not_lt.2 (hne k))))
  · rintro (⟨h1, h2⟩ | ⟨rfl, h⟩)
    · refine le_antisymm (stepIndex_le h1) (not_lt.1 fun hc => ?_)
      exact absurd (lt_stepIndex_succ ⟨n, h1⟩) (not_lt.2 (h2 _ hc))
    · exact Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_iff_forall_notMem.2
        fun k hk => absurd hk (not_lt.2 (h k))))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The step index is jointly measurable in the time and the sample point.**  The proof is a
description of the preimage of `{n}` and needs no limit: it is the set on which the `n`-th
window contains the time, together, for `n = 0`, with the explosion set. -/
theorem measurable_stepIndex {T : Ω → ℕ → ℝ} (hT : ∀ n, Measurable fun ω => T ω n) :
    Measurable fun p : ℝ × Ω => stepIndex (T p.2) p.1 := by
  refine measurable_to_countable' fun n => ?_
  have hset : (fun p : ℝ × Ω => stepIndex (T p.2) p.1) ⁻¹' {n} =
      ({p : ℝ × Ω | p.1 < T p.2 (n + 1)} ∩ ⋂ m ∈ Set.Iio n, {p : ℝ × Ω | T p.2 (m + 1) ≤ p.1})
        ∪ {p : ℝ × Ω | n = 0 ∧ ∀ k, T p.2 (k + 1) ≤ p.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Iio]
    rw [stepIndex_eq_iff]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) ?_
  · exact measurableSet_lt measurable_fst ((hT (n + 1)).comp measurable_snd)
  · exact MeasurableSet.biInter (Set.to_countable _) fun m _ =>
      measurableSet_le ((hT (m + 1)).comp measurable_snd) measurable_fst
  · by_cases hn : n = 0
    · have : {p : ℝ × Ω | n = 0 ∧ ∀ k, T p.2 (k + 1) ≤ p.1}
          = ⋂ k, {p : ℝ × Ω | T p.2 (k + 1) ≤ p.1} := by ext p; simp [hn]
      rw [this]
      exact MeasurableSet.iInter fun k =>
        measurableSet_le ((hT (k + 1)).comp measurable_snd) measurable_fst
    · have : {p : ℝ × Ω | n = 0 ∧ ∀ k, T p.2 (k + 1) ≤ p.1} = (∅ : Set (ℝ × Ω)) := by
        ext p; simp [hn]
      rw [this]
      exact MeasurableSet.empty

/-- **The step path is jointly measurable in the time and the sample point.**  This is the first
of the three steps the roadmap says are easy on step paths: countably many pieces, and no limit
argument. -/
theorem measurable_stepPath [MeasurableSpace E] {T : Ω → ℕ → ℝ} {y : Ω → ℕ → E}
    (hT : ∀ n, Measurable fun ω => T ω n) (hy : ∀ n, Measurable fun ω => y ω n) :
    Measurable fun p : ℝ × Ω => stepPath (T p.2) (y p.2) p.1 :=
  (measurable_from_prod_countable_left (α := Ω) (β := ℕ) (f := fun q => y q.1 q.2) hy).comp
    (measurable_snd.prodMk (measurable_stepIndex hT))

/-! ### The jump times -/

/-- The jump times of the construction: `T 0 = 0`, and the `n`-th holding time is the `n`-th
waiting time divided by the rate at the `n`-th state. -/
noncomputable def jumpTime (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => jumpTime lam y xi n + xi n / lam (y n)

@[simp] theorem jumpTime_zero (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) :
    jumpTime lam y xi 0 = 0 := rfl

theorem jumpTime_succ (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) (n : ℕ) :
    jumpTime lam y xi (n + 1) = jumpTime lam y xi n + xi n / lam (y n) := rfl

variable {lam : E → ℝ} {y : ℕ → E} {xi : ℕ → ℝ}

/-- **The jump times increase strictly** as soon as every waiting time and every rate is
positive.

The positivity of the rate is **not** cosmetic, and it is a genuine restriction of the present
signature: `x / 0 = 0` in Lean, so at a state with `lam x = 0` -- which the model intends to be
absorbing, with an infinite holding time -- the holding time computes to `0` and the path leaves
at once.  Carrying the absorbing case means giving the jump times values in `ℝ≥0∞`, and the
statements below say instead what is true of the construction as it stands. -/
theorem strictMono_jumpTime (hxi : ∀ n, 0 < xi n) (hlam : ∀ x, 0 < lam x) :
    StrictMono (jumpTime lam y xi) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [jumpTime_succ]
    exact lt_add_of_pos_right _ (div_pos (hxi n) (hlam _))

/-- The `n`-th jump time is at least the `n`-th partial sum of the waiting times divided by a
bound on the rate.  This inequality is the whole of the non explosion argument for a bounded
rate. -/
theorem sum_div_le_jumpTime {L : ℝ} (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L)
    (hxi : ∀ n, 0 ≤ xi n) (n : ℕ) :
    (∑ k ∈ Finset.range n, xi k) / L ≤ jumpTime lam y xi n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_div, jumpTime_succ]
      refine add_le_add ih ?_
      gcongr
      · exact hxi n
      · exact hlam _
      · exact hL _

/-- **Non explosion for a bounded rate**, given that the waiting times have divergent partial
sums.  The second hypothesis is what an independent sequence of exponential waiting times
supplies almost surely, and it is the only probabilistic input the path statements need. -/
theorem tendsto_jumpTime_atTop {L : ℝ} (hL0 : 0 < L) (hlam : ∀ x, 0 < lam x)
    (hL : ∀ x, lam x ≤ L) (hxi : ∀ n, 0 ≤ xi n)
    (hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, xi k) atTop atTop) :
    Tendsto (jumpTime lam y xi) atTop atTop :=
  tendsto_atTop_mono (fun n => sum_div_le_jumpTime hlam hL hxi n) (hsum.atTop_div_const hL0)

theorem exists_lt_succ_of_tendsto_atTop (h : Tendsto T atTop atTop) (s : ℝ) :
    ∃ n, s < T (n + 1) :=
  ((h.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop s).exists

/-- **The jump process**, as a process in the roadmap's convention `ι → Ω → E`: the state at
time `t` is the state of the embedded chain at the index of the window containing `t`. -/
noncomputable def jumpProcess (lam : E → ℝ) (t : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) : E :=
  stepPath (jumpTime lam ω.1 ω.2) ω.1 t

/-- **The paths of the jump process are step paths**, for a rate bounded above and below and
waiting times whose partial sums diverge. -/
theorem isStepPath_jumpProcess [TopologicalSpace E] {L : ℝ} (hL0 : 0 < L)
    (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (hxi : ∀ n, 0 < xi n)
    (hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, xi k) atTop atTop) :
    IsStepPath (fun t => jumpProcess lam t (y, xi)) :=
  isStepPath_stepPath (strictMono_jumpTime hxi hlam)
    (exists_lt_succ_of_tendsto_atTop
      (tendsto_jumpTime_atTop hL0 hlam hL (fun n => (hxi n).le) hsum)) y

/-- **The paths of the jump process are càdlàg.** -/
theorem isCadlagPath_jumpProcess [TopologicalSpace E] {L : ℝ} (hL0 : 0 < L)
    (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (hxi : ∀ n, 0 < xi n)
    (hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, xi k) atTop atTop) :
    IsCadlagPath (fun t => jumpProcess lam t (y, xi)) :=
  (isStepPath_jumpProcess hL0 hlam hL hxi hsum).isCadlagPath

/-- **The jump process starts at the initial state of the embedded chain.**  The zeroth window
`[0, T 1)` contains `0` as soon as the first holding time is positive, and then the step index of
`0` is `0`. -/
theorem jumpProcess_zero (hxi : ∀ n, 0 < xi n) (hlam : ∀ x, 0 < lam x) :
    jumpProcess lam 0 (y, xi) = y 0 := by
  have h1 : (0 : ℝ) < jumpTime lam y xi 1 := by
    rw [jumpTime_succ, jumpTime_zero, zero_add]
    exact div_pos (hxi 0) (hlam _)
  simp only [jumpProcess, stepPath,
    stepIndex_eq_of (Or.inl rfl) h1 (strictMono_jumpTime hxi hlam).monotone]

/-- **The first jump time reads only the initial state and the zeroth waiting time.**  This is
what makes the law of `T 1` explicit under `jumpMeasure mu nu`: the chain contributes `y 0` and
the waiting times contribute `ξ 0`, and the two are independent because the measure is a
product. -/
theorem jumpTime_one (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) :
    jumpTime lam y xi 1 = xi 0 / lam (y 0) := by
  rw [jumpTime_succ, jumpTime_zero, zero_add]

/-- **Before the first jump the path sits at its initial state.**  No monotonicity and no non
explosion are needed: `t < T 1` bounds the step index by `0` outright. -/
theorem jumpProcess_of_lt_jumpTime_one {t : ℝ} {ω : (ℕ → E) × (ℕ → ℝ)}
    (h : t < jumpTime lam ω.1 ω.2 1) : jumpProcess lam t ω = ω.1 0 := by
  have h0 : stepIndex (jumpTime lam ω.1 ω.2) t = 0 := Nat.le_zero.1 (stepIndex_le h)
  simp [jumpProcess, stepPath, h0]

/-! ### The shift at the first jump

The combinatorial half of the Markov property: after the first jump the path is the path of the
shifted data, restarted.  It is bookkeeping on `stepIndex` and it separates the combinatorics from
the measure theory of the restart. -/

/-- **The shift of the driving data**: forget the initial state and the zeroth waiting time. -/
def jumpShift (ω : (ℕ → E) × (ℕ → ℝ)) : (ℕ → E) × (ℕ → ℝ) :=
  (fun n ↦ ω.1 (n + 1), fun n ↦ ω.2 (n + 1))

/-- **The jump times of the shifted data are the jump times of the original**, shifted by one and
recentred at the first of them. -/
theorem jumpTime_jumpShift (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) (n : ℕ) :
    jumpTime lam (fun k ↦ y (k + 1)) (fun k ↦ xi (k + 1)) n
      = jumpTime lam y xi (n + 1) - jumpTime lam y xi 1 := by
  induction n with
  | zero => simp [jumpTime]
  | succ n ih =>
      rw [jumpTime_succ, ih, jumpTime_succ lam y xi (n + 1)]
      ring

/-- **The step index after the first jump.**  Both hypotheses are needed and neither is
monotonicity: `T 1 ≤ t` says that `0` is not a candidate index, and the existence says that the
infimum is attained -- on the explosion set both sides are the junk value `0` and `0 + 1`, and the
identity fails. -/
theorem stepIndex_shift {T : ℕ → ℝ} {t : ℝ} (h1 : T 1 ≤ t) (hex : ∃ n, t < T (n + 1)) :
    stepIndex T t = stepIndex (fun n ↦ T (n + 1) - T 1) (t - T 1) + 1 := by
  set S := {n | t < T (n + 1)} with hS
  set S' := {n | t - T 1 < T (n + 1 + 1) - T 1} with hS'
  have hSne : S.Nonempty := hex
  have hzero : 0 ∉ S := by simp [hS, not_lt, h1]
  have hmem : ∀ m : ℕ, m ∈ S' ↔ m + 1 ∈ S := by
    intro m
    simp only [hS', hS, Set.mem_setOf_eq, sub_lt_sub_iff_right]
  have hs'ne : S'.Nonempty := by
    obtain ⟨n, hn⟩ := hSne
    have hn0 : n ≠ 0 := by rintro rfl; exact hzero hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ⟨m, (hmem m).2 hn⟩
  have hinfS : sInf S ∈ S := Nat.sInf_mem hSne
  have hinfS' : sInf S' ∈ S' := Nat.sInf_mem hs'ne
  have h1' : sInf S ≠ 0 := fun h ↦ hzero (h ▸ hinfS)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h1'
  have hkS : k + 1 ∈ S := by rw [← Nat.succ_eq_add_one, ← hk]; exact hinfS
  have hle : sInf S' ≤ k := Nat.sInf_le ((hmem k).2 hkS)
  have hge : sInf S ≤ sInf S' + 1 := Nat.sInf_le ((hmem _).1 hinfS')
  have : stepIndex T t = sInf S := rfl
  have : stepIndex (fun n ↦ T (n + 1) - T 1) (t - T 1) = sInf S' := rfl
  omega

/-- **After the first jump the path is the path of the shifted data, restarted.** -/
theorem jumpProcess_jumpShift {lam : E → ℝ} {t : ℝ} {ω : (ℕ → E) × (ℕ → ℝ)}
    (h1 : jumpTime lam ω.1 ω.2 1 ≤ t) (hex : ∃ n, t < jumpTime lam ω.1 ω.2 (n + 1)) :
    jumpProcess lam t ω = jumpProcess lam (t - jumpTime lam ω.1 ω.2 1) (jumpShift ω) := by
  have hT : jumpTime lam (jumpShift ω).1 (jumpShift ω).2
      = fun n ↦ jumpTime lam ω.1 ω.2 (n + 1) - jumpTime lam ω.1 ω.2 1 :=
    funext fun n ↦ jumpTime_jumpShift lam ω.1 ω.2 n
  simp only [jumpProcess, stepPath]
  rw [hT, stepIndex_shift h1 hex]
  rfl

/-! ### The explicit probability space -/

section Space

variable {E : Type*} [MeasurableSpace E]

/-- **The law of the embedded chain**: Mathlib's Ionescu--Tulcea kernel specialised to a
sequence of kernels each of which reads only the *last* coordinate.  Unlike the product kernel
`ProbabilityTheory.exists_kernel_pi_of_markov` of the roadmap **KolmogorovExtension**, whose
kernels read only the base point, this is the Markov chain proper.  It carries no topology on
`E`. -/
noncomputable def chainFam (mu : Kernel E E) (n : ℕ) : Kernel ((i : Finset.Iic n) → E) E :=
  mu.comap (fun x : (i : Finset.Iic n) → E ↦ x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance instIsMarkovKernelChainFam (mu : Kernel E E) [IsMarkovKernel mu] (n : ℕ) :
    IsMarkovKernel (chainFam mu n) := by unfold chainFam; infer_instance

noncomputable def chainKernel (mu : Kernel E E) [IsMarkovKernel mu] : Kernel E (ℕ → E) :=
  (Kernel.traj (X := fun _ ↦ E) (chainFam mu) 0).comap
    (fun z (_ : Finset.Iic 0) ↦ z) (measurable_pi_lambda _ fun _ ↦ measurable_id)

instance instIsMarkovKernelChainKernel (mu : Kernel E E) [IsMarkovKernel mu] :
    IsMarkovKernel (chainKernel mu) := by
  unfold chainKernel; infer_instance

/-- **The chain starts where it is told to.** -/
theorem chainKernel_map_zero (mu : Kernel E E) [IsMarkovKernel mu] (z : E) :
    (chainKernel mu z).map (fun x ↦ x 0) = Measure.dirac z := by
  have h0 : (fun x : ℕ → E ↦ x 0)
      = (fun w : (i : Finset.Iic 0) → E ↦ w ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
        Preorder.frestrictLe 0 := rfl
  rw [chainKernel, Kernel.comap_apply, h0, ← Measure.map_map
    (measurable_pi_apply (X := fun _ : Finset.Iic 0 ↦ E) ⟨0, Finset.mem_Iic.2 le_rfl⟩)
    (Preorder.measurable_frestrictLe 0), ← Kernel.map_apply _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe_of_le (le_refl 0), Kernel.deterministic_apply,
    Measure.map_dirac' (measurable_pi_apply _)]
  rfl

instance instIsProbabilityMeasureExpMeasureOne : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- **The waiting times**: an independent sequence of standard exponential variables. -/
noncomputable def waitingMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure 1

instance : IsProbabilityMeasure waitingMeasure := by unfold waitingMeasure; infer_instance

/-- **The law of a single waiting time.**  This is the only property of `Measure.infinitePi` the
divergence argument needs beyond the independence of the coordinates. -/
theorem waitingMeasure_eval_preimage {A : Set ℝ} (hA : MeasurableSet A) (n : ℕ) :
    waitingMeasure {ω : ℕ → ℝ | ω n ∈ A} = expMeasure 1 A := by
  have h : waitingMeasure {ω : ℕ → ℝ | ω n ∈ A}
      = (waitingMeasure.map (fun ω : ℕ → ℝ ↦ ω n)) A := by
    rw [Measure.map_apply (measurable_pi_apply n) hA]; rfl
  rw [h]
  unfold waitingMeasure
  rw [Measure.infinitePi_map_eval]

/-- **The waiting times are invariant under the shift.**  This is the second of the two shift
statements the Markov property at the first jump rests on; the first is `chainKernel_map_shift`. -/
theorem waitingMeasure_map_shift :
    waitingMeasure.map (fun xi : ℕ → ℝ ↦ fun n ↦ xi (n + 1)) = waitingMeasure := by
  unfold waitingMeasure
  refine Measure.eq_infinitePi (fun _ : ℕ ↦ expMeasure 1) fun s t ht ↦ ?_
  classical
  have hpre : (fun (xi : ℕ → ℝ) (n : ℕ) ↦ xi (n + 1)) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.image Nat.succ)) (fun j ↦ t (j - 1)) := by
    ext xi
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro h j ⟨i, hi, rfl⟩
      simpa using h i hi
    · intro h i hi
      simpa using h (i + 1) ⟨i, hi, rfl⟩
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i), hpre,
    Measure.infinitePi_pi (μ := fun _ : ℕ ↦ expMeasure 1) (fun j _ ↦ ht (j - 1)),
    Finset.prod_image (fun x _ y _ h ↦ Nat.succ_injective h)]
  simp

/-- The standard exponential law has no atom at `0` and no mass below it. -/
theorem expMeasure_one_Iic_zero : expMeasure 1 (Set.Iic 0) = 0 := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos]
  norm_num

/-- **The tail of the exponential law.**  Mathlib has the distribution function
(`cdf_expMeasure_eq`) but not the tail, and not the memorylessness below; neither is in
v4.33.1 nor on `upstream/master`. -/
theorem expMeasure_Ioi {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  have hprob : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hpos : (0 : ℝ) ≤ Real.exp (-(r * x)) := (Real.exp_pos _).le
  have hle : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h1 : expMeasure r (Set.Iic x) = 1 - ENNReal.ofReal (Real.exp (-(r * x))) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx, ENNReal.ofReal_sub _ hpos,
      ENNReal.ofReal_one]
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h1,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top]
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hle

/-- **The exponential law is memoryless**, in the multiplicative form of its tail.  This is the
one distributional property of the waiting times the martingale property of the jump process
rests on. -/
theorem expMeasure_Ioi_add {r : ℝ} (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi (s + t)) = expMeasure r (Set.Ioi s) * expMeasure r (Set.Ioi t) := by
  rw [expMeasure_Ioi hr (by linarith), expMeasure_Ioi hr hs, expMeasure_Ioi hr ht,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    show -(r * s) + -(r * t) = -(r * (s + t)) from by ring]

/-- A single waiting time exceeds `1` with the positive probability `exp (-1)`.  Only the
positivity is used; the value is what makes the series of the Borel--Cantelli lemma diverge. -/
theorem expMeasure_one_Ioi_one_ne_zero : expMeasure 1 (Set.Ioi (1 : ℝ)) ≠ 0 := by
  rw [expMeasure_Ioi one_pos zero_le_one, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Real.exp_pos _

/-- **The exponential law is a density against Lebesgue measure**, unfolded to the shape the
density lemma of the Bochner integral wants: `Measure.withDensity` applied to a function written
as `ENNReal.ofReal ∘ exponentialPDFReal` and not as `exponentialPDF`.  The two differ by nothing
but a definitional unfolding, and `rw` needs the unfolded one. -/
theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (fun x ↦ ENNReal.ofReal (exponentialPDFReal r x)) := rfl

theorem toReal_exponentialPDF_one (s : ℝ) :
    (exponentialPDF 1 s).toReal = if 0 ≤ s then Real.exp (-s) else 0 := by
  by_cases hs : (0 : ℝ) ≤ s
  · rw [exponentialPDF_of_nonneg hs, if_pos hs, ENNReal.toReal_ofReal (by positivity)]
    simp
  · rw [exponentialPDF_of_neg (not_le.1 hs), if_neg hs, ENNReal.toReal_zero]

/-- **Integration against the standard exponential law is integration of `exp (-s) * ·` over the
positive half line.**  There is no hypothesis on `F` at all: the identity is the definition of
`expMeasure` as a density, and both sides are the same junk value when `F` fails to be integrable.

This is the step that turns the renewal equation into a statement about an integral in the *time*
variable, which is what the differentiation of the backward equation acts on; Mathlib has the
distribution function of `expMeasure` but not this. -/
theorem integral_expMeasure_one (F : ℝ → ℝ) :
    ∫ s, F s ∂(expMeasure 1) = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s) * F s := by
  rw [expMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_exponentialPDFReal 1).ennreal_ofReal
      (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top) F]
  have hfun : (fun s ↦ (ENNReal.ofReal (exponentialPDFReal 1 s)).toReal • F s)
      = (Set.Ici (0 : ℝ)).indicator (fun s ↦ Real.exp (-s) * F s) := by
    funext s
    rw [show ENNReal.ofReal (exponentialPDFReal 1 s) = exponentialPDF 1 s from rfl,
      toReal_exponentialPDF_one, Set.indicator_apply, smul_eq_mul]
    by_cases hs : (0 : ℝ) ≤ s
    · simp [hs]
    · simp [hs]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- **The coordinates of `waitingMeasure` are independent events.**  The product formula for
cylinder sets of `Measure.infinitePi` is exactly the characterisation
`iIndepSet_iff_meas_biInter`. -/
theorem iIndepSet_waiting {A : ℕ → Set ℝ} (hA : ∀ n, MeasurableSet (A n)) :
    iIndepSet (fun n ↦ {ω : ℕ → ℝ | ω n ∈ A n}) waitingMeasure := by
  refine (iIndepSet_iff_meas_biInter
    (fun n ↦ (hA n).preimage (measurable_pi_apply n))).2 fun S ↦ ?_
  have hset : (⋂ i ∈ S, ((fun f : ℕ → ℝ ↦ f i) ⁻¹' A i)) = Set.pi (S : Set ℕ) A := by
    ext ω; simp [Set.mem_pi]
  rw [hset]
  unfold waitingMeasure
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ ↦ expMeasure 1) (fun i _ ↦ hA i)]
  exact Finset.prod_congr rfl fun i _ ↦ (waitingMeasure_eval_preimage (hA i) i).symm

/-- **Almost every waiting time is positive**, which is the first of the two hypotheses of
`isStepPath_jumpProcess`. -/
theorem ae_pos_waiting : ∀ᵐ ω ∂waitingMeasure, ∀ n, 0 < ω n := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have h : {ω : ℕ → ℝ | ¬ 0 < ω n} = {ω : ℕ → ℝ | ω n ∈ Set.Iic 0} := by
    ext ω; simp [not_lt]
  rw [h, waitingMeasure_eval_preimage measurableSet_Iic n, expMeasure_one_Iic_zero]

/-- **Infinitely many waiting times exceed one**, almost surely: the second Borel--Cantelli lemma
on the independent events `{ω n > 1}`, whose common probability `exp (-1)` is positive, so that
the series of their measures diverges. -/
theorem frequently_one_lt_waiting :
    ∀ᵐ ω ∂waitingMeasure, ∃ᶠ n in atTop, 1 < ω n := by
  set s : ℕ → Set (ℕ → ℝ) := fun n ↦ {ω : ℕ → ℝ | ω n ∈ Set.Ioi (1 : ℝ)} with hs
  have hm : ∀ n : ℕ, MeasurableSet (s n) :=
    fun n ↦ measurableSet_Ioi.preimage (measurable_pi_apply n)
  have hsum : (∑' n : ℕ, waitingMeasure (s n)) = ⊤ := by
    simp_rw [hs, fun n ↦ waitingMeasure_eval_preimage (measurableSet_Ioi (a := (1 : ℝ))) n]
    exact ENNReal.tsum_const_eq_top_of_ne_zero expMeasure_one_Ioi_one_ne_zero
  have hone := measure_limsup_eq_one hm (iIndepSet_waiting fun _ ↦ measurableSet_Ioi) hsum
  have hmeas : MeasurableSet (limsup s atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
    exact MeasurableSet.iInter fun n ↦
      MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ hm i
  have hae : ∀ᵐ ω ∂waitingMeasure, ω ∈ limsup s atTop :=
    (ae_mem_iff_measure_eq hmeas.nullMeasurableSet).2 (by rw [hone, measure_univ])
  filter_upwards [hae] with ω hω
  exact mem_limsup_iff_frequently_mem.1 hω

/-- **The partial sums of the waiting times diverge**, almost surely.  This is the second and
last hypothesis of `isStepPath_jumpProcess`, and it is the whole probabilistic content of non
explosion: a summable sequence of nonnegative terms tends to `0`, which no sequence exceeding
`1` infinitely often does. -/
theorem tendsto_sum_waiting_atTop :
    ∀ᵐ ω ∂waitingMeasure, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ω k) atTop atTop := by
  filter_upwards [ae_pos_waiting, frequently_one_lt_waiting] with ω hpos hfreq
  refine (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦ (hpos n).le).1 fun hsum ↦ ?_
  have hev : ∀ᶠ n in atTop, ω n < 1 :=
    hsum.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, h1, h2⟩ := (hfreq.and_eventually hev).exists
  exact absurd h1 (not_lt.2 h2.le)

/-- **The explicit probability space of the jump construction.**  A point is a trajectory of the
embedded chain together with the sequence of its waiting times, and the two are independent
because the measure is a product. -/
noncomputable def jumpMeasure (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) :
    Measure ((ℕ → E) × (ℕ → ℝ)) :=
  (chainKernel mu ∘ₘ nu).prod waitingMeasure

instance (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (jumpMeasure mu nu) := by unfold jumpMeasure; infer_instance

/-- **The chain started from `nu` has initial law `nu`.**  Stated for the law of the chain alone,
because the first jump decomposition integrates a function of the initial state against it and
not against `jumpMeasure`. -/
theorem comp_chainKernel_map_zero (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) :
    (chainKernel mu ∘ₘ nu).map (fun x : ℕ → E ↦ x 0) = nu := by
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have hker : (chainKernel mu).map (fun x : ℕ → E ↦ x 0) = Kernel.id := by
    ext z s hs
    rw [Kernel.map_apply _ (measurable_pi_apply 0), chainKernel_map_zero, Kernel.id_apply]
  rw [hker, Measure.id_comp]

/-! ### The Markov property of the embedded chain

`ProbabilityTheory.Kernel.traj` is built for an arbitrary family of kernels and therefore carries
no time homogeneity: neither v4.33.1 nor `upstream/master` has a statement saying that shifting a
trajectory of a homogeneous chain gives a trajectory of the same chain.  That statement is proved
here for `chainFam`, by induction on the finite dimensional distributions. -/

/-- The shift on finite trajectories: forget the coordinate `0` and renumber. -/
def shiftIic (b : ℕ) (w : (i : Finset.Iic (b + 1)) → E) : (i : Finset.Iic b) → E :=
  fun i ↦ w ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.1 i.2))⟩

theorem measurable_shiftIic (b : ℕ) : Measurable (shiftIic (E := E) b) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem kernel_comp_comap {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (η : Kernel β γ) (ρ : Kernel α β) {δ : Type*}
    {mδ : MeasurableSpace δ} {g : δ → α} (hg : Measurable g) :
    η ∘ₖ (ρ.comap g hg) = (η ∘ₖ ρ).comap g hg := by
  ext x s hs
  rw [Kernel.comap_apply, Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs,
    Kernel.comap_apply]

theorem map_dirac_prod_left {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (x : α) (ν : Measure β) [SFinite ν] {f : α × β → γ}
    (hf : Measurable f) : ((Measure.dirac x).prod ν).map f = ν.map (fun v ↦ f (x, v)) := by
  rw [Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

/-- On a constant family of state spaces the identification of `{a + 1}` with `Ioc a (a + 1)`
carries no information: it returns the value it was given. -/
theorem piSingleton_apply_const (a : ℕ) (v : E) (j : ↥(Finset.Ioc a (a + 1))) :
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) a) v j = v := by
  cases Nat.mem_Ioc_succ' j
  rfl

/-- **One step of the chain commutes with the shift.**  This is the whole of the time homogeneity:
the kernel at time `b + 1` reads the last coordinate, which the shift carries to the last
coordinate of the shifted tuple. -/
theorem partialTraj_succ_map_shiftIic (mu : Kernel E E) [IsMarkovKernel mu] (b : ℕ) :
    (Kernel.partialTraj (X := fun _ ↦ E) (chainFam mu) (b + 1) (b + 2)).map (shiftIic (b + 1))
      = (Kernel.partialTraj (X := fun _ ↦ E) (chainFam mu) b (b + 1)).comap (shiftIic b)
          (measurable_shiftIic b) := by
  ext w : 1
  rw [Kernel.map_apply _ (measurable_shiftIic _), Kernel.comap_apply,
    Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self,
    Kernel.map_apply _ (measurable_IicProdIoc (X := fun _ : ℕ ↦ E)),
    Kernel.map_apply _ (measurable_IicProdIoc (X := fun _ : ℕ ↦ E)),
    Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) _).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) _).measurable,
    map_dirac_prod_left _ _ (measurable_IicProdIoc (X := fun _ : ℕ ↦ E)),
    map_dirac_prod_left _ _ (measurable_IicProdIoc (X := fun _ : ℕ ↦ E))]
  have hf1 : Measurable (fun v : (i : Finset.Ioc (b + 1) (b + 1 + 1)) → E ↦
      IicProdIoc (X := fun _ : ℕ ↦ E) (b + 1) (b + 1 + 1) (w, v)) :=
    (measurable_IicProdIoc (X := fun _ : ℕ ↦ E)).comp measurable_prodMk_left
  have hf2 : Measurable (fun v : (i : Finset.Ioc b (b + 1)) → E ↦
      IicProdIoc (X := fun _ : ℕ ↦ E) b (b + 1) (shiftIic b w, v)) :=
    (measurable_IicProdIoc (X := fun _ : ℕ ↦ E)).comp measurable_prodMk_left
  have hrate : chainFam mu b (shiftIic b w) = chainFam mu (b + 1) w := rfl
  rw [Measure.map_map (measurable_shiftIic (b + 1)) hf1,
    Measure.map_map ((measurable_shiftIic (b + 1)).comp hf1)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) (b + 1)).measurable,
    Measure.map_map hf2 (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) b).measurable, hrate]
  congr 1
  funext v
  funext i
  by_cases hi : i.1 ≤ b
  · simp only [Function.comp_apply, shiftIic, IicProdIoc, dif_pos hi,
      dif_pos (Nat.succ_le_succ hi)]
  · have hib : i.1 = b + 1 := le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt (not_le.1 hi))
    simp only [Function.comp_apply, shiftIic, IicProdIoc, dif_neg hi,
      dif_neg (fun h : i.1 + 1 ≤ b + 1 ↦ hi (Nat.succ_le_succ_iff.1 h))]
    rw [piSingleton_apply_const, piSingleton_apply_const]

/-- **The finite dimensional distributions of the chain commute with the shift.** -/
theorem partialTraj_map_shiftIic (mu : Kernel E E) [IsMarkovKernel mu] (b : ℕ) :
    (Kernel.partialTraj (X := fun _ ↦ E) (chainFam mu) 1 (b + 1)).map (shiftIic b)
      = (Kernel.partialTraj (X := fun _ ↦ E) (chainFam mu) 0 b).comap (shiftIic 0)
          (measurable_shiftIic 0) := by
  induction b with
  | zero =>
      ext x : 1
      rw [Kernel.map_apply _ (measurable_shiftIic _), Kernel.comap_apply,
        Kernel.partialTraj_self, Kernel.partialTraj_self, Kernel.id_apply, Kernel.id_apply,
        Measure.map_dirac' (measurable_shiftIic _)]
  | succ b ih =>
      rw [Kernel.partialTraj_succ_eq_comp (by omega), Kernel.map_comp,
        partialTraj_succ_map_shiftIic mu b, ← Kernel.comp_map _ _ (measurable_shiftIic b), ih,
        kernel_comp_comap, ← Kernel.partialTraj_succ_eq_comp (Nat.zero_le b)]

/-- **Two probability measures on `ℕ → E` with the same finite dimensional distributions along the
initial segments are equal.** -/
theorem ext_of_map_frestrictLe {μ ν : Measure (ℕ → E)} [IsProbabilityMeasure ν]
    (h : ∀ b, μ.map (Preorder.frestrictLe b) = ν.map (Preorder.frestrictLe b)) : μ = ν := by
  set P : (I : Finset ℕ) → Measure ((i : I) → E) := fun I ↦ ν.map I.restrict with hP
  have hproj : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ E) P := by
    intro I J hJI
    rw [hP]
    simp only
    rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (Finset.measurable_restrict I),
      Finset.restrict₂_comp_restrict]
  have : ∀ I, IsProbabilityMeasure (P I) := fun I ↦
    Measure.isProbabilityMeasure_map (Finset.measurable_restrict I).aemeasurable
  have hν : IsProjectiveLimit (α := fun _ : ℕ ↦ E) ν P := fun I ↦ rfl
  have hμ : IsProjectiveLimit (α := fun _ : ℕ ↦ E) μ P :=
    (isProjectiveLimit_nat_iff (X := fun _ : ℕ ↦ E) hproj μ).2 fun n ↦ by rw [h n]; rfl
  exact hμ.unique hν

/-- **The trajectory of the chain from time one, shifted, is the trajectory from time zero started
at the second coordinate.**  This is the time homogeneity of `Kernel.traj` for `chainFam`. -/
theorem traj_map_shift (mu : Kernel E E) [IsMarkovKernel mu] (w : (i : Finset.Iic 1) → E) :
    (Kernel.traj (X := fun _ ↦ E) (chainFam mu) 1 w).map (fun x : ℕ → E ↦ fun n ↦ x (n + 1))
      = Kernel.traj (X := fun _ ↦ E) (chainFam mu) 0 (shiftIic 0 w) := by
  have hmeas : Measurable (fun x : ℕ → E ↦ fun n ↦ x (n + 1)) :=
    measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  refine ext_of_map_frestrictLe fun b ↦ ?_
  have hcomp : (Preorder.frestrictLe (π := fun _ : ℕ ↦ E) b) ∘ (fun x : ℕ → E ↦ fun n ↦ x (n + 1))
      = (shiftIic b) ∘ (Preorder.frestrictLe (π := fun _ : ℕ ↦ E) (b + 1)) := rfl
  have hstep := congrArg (fun κ ↦ κ w) (partialTraj_map_shiftIic mu b)
  simp only [Kernel.map_apply _ (measurable_shiftIic b), Kernel.comap_apply] at hstep
  rw [Measure.map_map (Preorder.measurable_frestrictLe b) hmeas, hcomp,
    ← Measure.map_map (measurable_shiftIic b) (Preorder.measurable_frestrictLe (b + 1)),
    Kernel.traj_map_frestrictLe_apply, hstep, Kernel.traj_map_frestrictLe_apply]

theorem comap_comp_measure {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (η : Kernel α β) {g : γ → α} (hg : Measurable g) (μ : Measure γ)
    [SFinite μ] [IsSFiniteKernel η] :
    (η.comap g hg) ∘ₘ μ = η ∘ₘ (μ.map g) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (η.measurable_coe hs) hg]
  simp_rw [Kernel.comap_apply]

/-- **The Markov property of the embedded chain**: shifting the trajectory by one step gives the
chain started from one step of `mu`.  With `waitingMeasure_map_shift` and `jumpProcess_jumpShift`
this is what the second term of `jumpMeasure_integral_eq_of_firstJump` needs. -/
theorem chainKernel_map_shift (mu : Kernel E E) [IsMarkovKernel mu] (z : E) :
    (chainKernel mu z).map (fun x : ℕ → E ↦ fun n ↦ x (n + 1)) = chainKernel mu ∘ₘ (mu z) := by
  have hmeas : Measurable (fun x : ℕ → E ↦ fun n ↦ x (n + 1)) :=
    measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  have hconst : Measurable (fun y : E ↦ fun _ : Finset.Iic 0 ↦ y) :=
    measurable_pi_lambda _ fun _ ↦ measurable_id
  have hker : (Kernel.traj (X := fun _ ↦ E) (chainFam mu) 1).map
        (fun x : ℕ → E ↦ fun n ↦ x (n + 1))
      = (Kernel.traj (X := fun _ ↦ E) (chainFam mu) 0).comap (shiftIic 0)
          (measurable_shiftIic 0) := by
    ext w : 1
    rw [Kernel.map_apply _ hmeas, Kernel.comap_apply]
    exact traj_map_shift mu w
  have hshift0 : (shiftIic (E := E) 0)
      = (fun y (_ : Finset.Iic 0) ↦ y) ∘
        (fun x : (i : Finset.Iic 1) → E ↦ x ⟨1, Finset.mem_Iic.2 le_rfl⟩) := by
    funext w i
    simp only [shiftIic, Function.comp_apply]
    congr 1
    exact Subtype.ext (by simp [Nat.le_zero.1 (Finset.mem_Iic.1 i.2)])
  have hone : (Kernel.partialTraj (X := fun _ ↦ E) (chainFam mu) 0 1 (fun _ ↦ z)).map (shiftIic 0)
      = (mu z).map (fun y ↦ fun _ : Finset.Iic 0 ↦ y) := by
    rw [hshift0, ← Measure.map_map hconst (measurable_pi_apply _),
      ← Kernel.map_apply _ (measurable_pi_apply (⟨1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 1)),
      Kernel.map_partialTraj_succ_self]
    rfl
  conv_lhs => rw [chainKernel, Kernel.comap_apply,
    ← Kernel.traj_comp_partialTraj (Nat.zero_le 1), Kernel.comp_apply,
    Measure.map_comp _ _ hmeas, hker, comap_comp_measure, hone]
  rw [chainKernel, comap_comp_measure]

/-! ### The splitting of the driving data at the first jump

`chainKernel_map_shift` and `waitingMeasure_map_shift` describe the shifted data alone.  The
renewal equation needs the *joint* law of the initial state, the zeroth waiting time and the
shifted data, because its integrand reads all three: the first jump time is
`ξ 0 / lam (y 0)` and the restarted path is a path of `jumpShift ω`.  That joint law is the
content of `jumpMeasure_map_split`, and it says that under `jumpMeasure mu nu` the shifted data
is again a jump construction, started from one step of `mu`
(`prod_comp_chainKernel_eq_jumpMeasure`). -/

/-- **A marginal that is a Dirac measure splits off as a product.**  This is the step that makes
the initial state independent of the shifted chain, and it is stated for a general `μ` because
over a bare `[MeasurableSpace E]` one cannot pass to the almost sure statement `f =ᵐ[μ] z`: that
would need `{z}` to be measurable.  The proof therefore works on measurable rectangles, where
only `μ (f ⁻¹' s) ∈ {0, 1}` is used. -/
theorem map_prodMk_of_map_eq_dirac {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) {z : β} (hfz : μ.map f = Measure.dirac z) :
    μ.map (fun x ↦ (f x, g x)) = (Measure.dirac z).prod (μ.map g) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.map_apply (hf.prodMk hg) (hs.prod ht), Measure.dirac_apply' z hs,
    Measure.map_apply hg ht]
  have hpre : (fun x ↦ (f x, g x)) ⁻¹' (s ×ˢ t) = f ⁻¹' s ∩ g ⁻¹' t := rfl
  have hval : μ (f ⁻¹' s) = s.indicator 1 z := by
    rw [← Measure.map_apply hf hs, hfz, Measure.dirac_apply' z hs]
  rw [hpre]
  by_cases hz : z ∈ s
  · have hone : μ (f ⁻¹' s) = 1 := by rw [hval, Set.indicator_of_mem hz]; rfl
    have hc : μ (f ⁻¹' s)ᶜ = 0 := by
      rw [measure_compl (hf hs) (measure_ne_top _ _), hone, measure_univ, tsub_self]
    have hsub : g ⁻¹' t ⊆ (f ⁻¹' s ∩ g ⁻¹' t) ∪ (f ⁻¹' s)ᶜ := by
      intro x hx
      by_cases h : x ∈ f ⁻¹' s
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr h
    have h1 : μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (g ⁻¹' t) :=
      le_antisymm (measure_mono Set.inter_subset_right)
        (le_trans (measure_mono hsub)
          (le_trans (measure_union_le _ _) (by rw [hc, add_zero])))
    rw [h1, Set.indicator_of_mem hz]
    simp
  · have hnull : μ (f ⁻¹' s) = 0 := by rw [hval, Set.indicator_of_notMem hz]
    rw [measure_mono_null Set.inter_subset_left hnull, Set.indicator_of_notMem hz]
    simp

/-- **Prepending a value to a sequence indexed by `ℕ`.** -/
def natCons {X : Type*} (p : X × (ℕ → X)) : ℕ → X :=
  fun n ↦ if n = 0 then p.1 else p.2 (n - 1)

theorem measurable_natCons {X : Type*} [MeasurableSpace X] :
    Measurable (natCons : X × (ℕ → X) → ℕ → X) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  by_cases h : n = 0
  · simpa [natCons, h] using measurable_fst
  · simp only [natCons, if_neg h]
    fun_prop

/-- **An infinite product over `ℕ` of one and the same law is invariant under prepending an
independent copy.**  Mathlib has the reindexings of `Measure.infinitePi` along injections
(`Measure.map_infinitePi_infinitePi_of_inj`) and the independence of the coordinates, but not the
independence of a single coordinate from the whole tail; that statement is not a reindexing, and
it is what the splitting of the waiting times needs. -/
theorem infinitePi_map_natCons {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    (μ.prod (Measure.infinitePi fun _ : ℕ ↦ μ)).map natCons
      = Measure.infinitePi fun _ : ℕ ↦ μ := by
  classical
  refine Measure.eq_infinitePi (fun _ : ℕ ↦ μ) fun s t ht ↦ ?_
  set s' : Finset ℕ := (s.erase 0).image (fun i ↦ i - 1) with hs'
  set A : Set X := if 0 ∈ s then t 0 else Set.univ with hA
  have hpre : (natCons : X × (ℕ → X) → ℕ → X) ⁻¹' (Set.pi (↑s) t)
      = A ×ˢ Set.pi (↑s') (fun j ↦ t (j + 1)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, hs',
      Finset.coe_image, Set.mem_image, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · by_cases h0 : 0 ∈ s
        · have := h 0 h0
          simpa [hA, h0, natCons] using this
        · simp [hA, h0]
      · rintro j ⟨i, ⟨hi0, his⟩, rfl⟩
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have := h (k + 1) his
        simpa [natCons] using this
    · rintro ⟨h1, h2⟩ i hi
      by_cases hi0 : i = 0
      · subst hi0
        simpa [natCons] using (by simpa [hA, hi] using h1 : p.1 ∈ t 0)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have := h2 k ⟨k + 1, ⟨Nat.succ_ne_zero k, hi⟩, rfl⟩
        simpa [natCons] using this
  have hinj : ∀ x ∈ s.erase 0, ∀ y ∈ s.erase 0, x - 1 = y - 1 → x = y := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := (Finset.mem_erase.1 hx).1
    have hy0 : y ≠ 0 := (Finset.mem_erase.1 hy).1
    omega
  rw [Measure.map_apply measurable_natCons
      (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i), hpre, Measure.prod_prod,
    Measure.infinitePi_pi (μ := fun _ : ℕ ↦ μ) (fun j _ ↦ ht (j + 1)), hs',
    Finset.prod_image hinj]
  have hcongr : ∀ i ∈ s.erase 0, μ (t (i - 1 + 1)) = μ (t i) := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
    have : i - 1 + 1 = i := by omega
    rw [this]
  rw [Finset.prod_congr rfl hcongr]
  by_cases h0 : 0 ∈ s
  · rw [hA, if_pos h0, Finset.mul_prod_erase s (fun i ↦ μ (t i)) h0]
  · rw [hA, if_neg h0, Finset.erase_eq_of_notMem h0, measure_univ, one_mul]

/-- **The zeroth coordinate and the tail are independent** under an infinite product of one and
the same law. -/
theorem infinitePi_map_split {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    (Measure.infinitePi fun _ : ℕ ↦ μ).map (fun x : ℕ → X ↦ (x 0, fun n ↦ x (n + 1)))
      = μ.prod (Measure.infinitePi fun _ : ℕ ↦ μ) := by
  have hsplit : Measurable (fun x : ℕ → X ↦ (x 0, fun n ↦ x (n + 1))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)
  conv_lhs => rw [← infinitePi_map_natCons μ]
  rw [Measure.map_map hsplit measurable_natCons]
  have hid : (fun x : ℕ → X ↦ (x 0, fun n ↦ x (n + 1))) ∘ natCons = id := by
    funext p
    refine Prod.ext ?_ ?_
    · simp [natCons]
    · funext n; simp [natCons]
  rw [hid, Measure.map_id]

theorem measurable_natSplit {X : Type*} [MeasurableSpace X] :
    Measurable (fun x : ℕ → X ↦ (x 0, fun n ↦ x (n + 1))) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)

/-- **The chain splits at its first step.**  The initial state is independent of the shifted
chain because the former is deterministic under `chainKernel mu z`. -/
theorem chainKernel_map_split (mu : Kernel E E) [IsMarkovKernel mu] (z : E) :
    (chainKernel mu z).map (fun x : ℕ → E ↦ (x 0, fun n ↦ x (n + 1)))
      = (Measure.dirac z).prod (chainKernel mu ∘ₘ (mu z)) := by
  rw [← chainKernel_map_shift mu z]
  exact map_prodMk_of_map_eq_dirac (measurable_pi_apply 0)
    (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _) (chainKernel_map_zero mu z)

/-- **The law of the chain, split at its first step**: the initial state has law `nu` and the
shifted chain is the chain started from one step of `mu`.  This is the composition-with-`nu`
form of `chainKernel_map_split`, and the `Measure.compProd` on the right is exactly the
disintegration the renewal equation integrates against. -/
theorem comp_chainKernel_map_split (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [SFinite nu] :
    (chainKernel mu ∘ₘ nu).map (fun x : ℕ → E ↦ (x 0, fun n ↦ x (n + 1)))
      = nu ⊗ₘ (chainKernel mu ∘ₖ mu) := by
  rw [Measure.map_comp _ _ measurable_natSplit, Measure.compProd_eq_comp_prod]
  congr 1
  ext z : 1
  rw [Kernel.map_apply _ measurable_natSplit, Kernel.prod_apply, Kernel.id_apply,
    Kernel.comp_apply]
  exact chainKernel_map_split mu z

/-- **The waiting times split at the zeroth one.** -/
theorem waitingMeasure_map_split :
    waitingMeasure.map (fun xi : ℕ → ℝ ↦ (xi 0, fun n ↦ xi (n + 1)))
      = (expMeasure 1).prod waitingMeasure :=
  infinitePi_map_split (expMeasure 1)

/-- **The jump construction splits at the first jump.**  Reading the initial state, the zeroth
waiting time and the shifted data at once: the pair `(y 0, ξ 0)` carries the first jump time
`ξ 0 / lam (y 0)`, and the shifted data `jumpShift ω = (fun n ↦ y (n + 1), fun n ↦ ξ (n + 1))` is
the second component of each factor.  Together with `prod_comp_chainKernel_eq_jumpMeasure` this
is the Markov property at the first jump. -/
theorem jumpMeasure_map_split (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] :
    (jumpMeasure mu nu).map (fun ω : (ℕ → E) × (ℕ → ℝ) ↦
        ((ω.1 0, fun n ↦ ω.1 (n + 1)), (ω.2 0, fun n ↦ ω.2 (n + 1))))
      = (nu ⊗ₘ (chainKernel mu ∘ₖ mu)).prod ((expMeasure 1).prod waitingMeasure) := by
  rw [← comp_chainKernel_map_split mu nu, ← waitingMeasure_map_split,
    Measure.map_prod_map _ _ measurable_natSplit measurable_natSplit, jumpMeasure]
  rfl

/-- **What the shifted data is**: a jump construction started from one step of `mu`.  This is the
statement that makes `jumpMeasure_map_split` a *restart* and not merely a factorisation. -/
theorem prod_comp_chainKernel_eq_jumpMeasure (mu : Kernel E E) [IsMarkovKernel mu] (z : E) :
    ((chainKernel mu ∘ₖ mu) z).prod waitingMeasure = jumpMeasure mu (mu z) := by
  rw [jumpMeasure, Kernel.comp_apply]

omit [MeasurableSpace E] in
/-- The shift of the driving data, read off the splitting: what `jumpMeasure_map_split` computes
is the joint law of `(y 0, ξ 0)` and `jumpShift ω`. -/
theorem jumpShift_eq_split (ω : (ℕ → E) × (ℕ → ℝ)) :
    jumpShift ω = ((ω.1 0, fun n ↦ ω.1 (n + 1)).2, (ω.2 0, fun n ↦ ω.2 (n + 1)).2) := rfl

/-- **The initial law is the one prescribed.**  This is the only place where `nu` enters, and it
is what makes the construction one *of* `nu` and not merely one indexed by it. -/
theorem jumpMeasure_map_chain_zero (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] : (jumpMeasure mu nu).map (fun ω ↦ ω.1 0) = nu := by
  have hmap : (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ ω.1 0)
      = (fun x : ℕ → E ↦ x 0) ∘ Prod.fst := rfl
  rw [jumpMeasure, hmap, ← Measure.map_map (measurable_pi_apply 0) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, comp_chainKernel_map_zero]

theorem measurable_jumpTime {lam : E → ℝ} (hlam : Measurable lam) (n : ℕ) :
    Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpTime lam ω.1 ω.2 n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      simp only [jumpTime_succ]
      exact ih.add (((measurable_pi_apply n).comp measurable_snd).div
        (hlam.comp ((measurable_pi_apply n).comp measurable_fst)))

/-- **The jump process is jointly measurable in `(t, ω)`.** -/
theorem measurable_jumpProcess {lam : E → ℝ} (hlam : Measurable lam) :
    Measurable fun p : ℝ × ((ℕ → E) × (ℕ → ℝ)) ↦ jumpProcess lam p.1 p.2 :=
  measurable_stepPath (fun n ↦ measurable_jumpTime hlam n)
    (fun n ↦ (measurable_pi_apply n).comp measurable_fst)

/-- **The waiting times of the jump construction have the law `waitingMeasure`.**  The measure is
a product, so its second marginal is the second factor. -/
theorem jumpMeasure_map_snd (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] : (jumpMeasure mu nu).map Prod.snd = waitingMeasure := by
  rw [jumpMeasure, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Almost every path of the jump process is a step path**, unconditionally: the two hypotheses
of `isStepPath_jumpProcess` are the two almost sure statements about the waiting times, and they
hold under `jumpMeasure mu nu` because the waiting times are its second marginal. -/
theorem ae_isStepPath_jumpProcess [TopologicalSpace E] {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L)
    (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu]
    (nu : Measure E) [IsProbabilityMeasure nu] :
    ∀ᵐ ω ∂(jumpMeasure mu nu), IsStepPath (fun t ↦ jumpProcess lam t ω) := by
  have h : ∀ᵐ ω ∂(jumpMeasure mu nu), (∀ n, 0 < ω.2 n) ∧
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ω.2 k) atTop atTop := by
    refine ae_of_ae_map (f := fun ω : (ℕ → E) × (ℕ → ℝ) ↦ ω.2)
      (p := fun xi : ℕ → ℝ ↦ (∀ n, 0 < xi n) ∧
        Tendsto (fun n ↦ ∑ k ∈ Finset.range n, xi k) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [jumpMeasure_map_snd]
    exact ae_pos_waiting.and tendsto_sum_waiting_atTop
  filter_upwards [h] with ω hω
  exact isStepPath_jumpProcess (y := ω.1) (xi := ω.2) hL0 hlam hL hω.1 hω.2

/-- **Almost every path of the jump process is càdlàg**, unconditionally. -/
theorem ae_isCadlagPath_jumpProcess [TopologicalSpace E] {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L)
    (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu]
    (nu : Measure E) [IsProbabilityMeasure nu] :
    ∀ᵐ ω ∂(jumpMeasure mu nu), IsCadlagPath (fun t ↦ jumpProcess lam t ω) := by
  filter_upwards [ae_isStepPath_jumpProcess hL0 hlam hL mu nu] with ω hω
  exact hω.isCadlagPath

/-- The waiting times of the jump construction are almost surely positive. -/
theorem ae_pos_snd_jumpMeasure (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] : ∀ᵐ ω ∂(jumpMeasure mu nu), ∀ n, 0 < ω.2 n := by
  refine ae_of_ae_map (f := fun ω : (ℕ → E) × (ℕ → ℝ) ↦ ω.2)
    (p := fun xi : ℕ → ℝ ↦ ∀ n, 0 < xi n) measurable_snd.aemeasurable ?_
  rw [jumpMeasure_map_snd]
  exact ae_pos_waiting

/-- **Almost surely the jump times exhaust the half line**, which is non explosion in the form
the shift at the first jump needs: `jumpProcess_jumpShift` asks for a window index above `t`, and
without one both sides of that identity are the junk value of `stepIndex`.

Unlike `ae_isStepPath_jumpProcess` this carries **no topology on `E`**: the statement is about the
jump times alone, and `tendsto_jumpTime_atTop` never looks at the state space. -/
theorem ae_exists_lt_jumpTime {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L) (hlam : ∀ x, 0 < lam x)
    (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] :
    ∀ᵐ ω ∂(jumpMeasure mu nu), ∀ s : ℝ, ∃ n, s < jumpTime lam ω.1 ω.2 (n + 1) := by
  have h : ∀ᵐ ω ∂(jumpMeasure mu nu), (∀ n, 0 < ω.2 n) ∧
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ω.2 k) atTop atTop := by
    refine ae_of_ae_map (f := fun ω : (ℕ → E) × (ℕ → ℝ) ↦ ω.2)
      (p := fun xi : ℕ → ℝ ↦ (∀ n, 0 < xi n) ∧
        Tendsto (fun n ↦ ∑ k ∈ Finset.range n, xi k) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [jumpMeasure_map_snd]
    exact ae_pos_waiting.and tendsto_sum_waiting_atTop
  filter_upwards [h] with ω hω
  exact fun s ↦ exists_lt_succ_of_tendsto_atTop
    (tendsto_jumpTime_atTop (y := ω.1) (xi := ω.2) hL0 hlam hL (fun n ↦ (hω.1 n).le) hω.2) s

/-- **The jump process has the prescribed initial law.**  Together with
`ae_isCadlagPath_jumpProcess` this is what makes `jumpProcess lam mu nu` a construction *of*
`nu`: the process itself, and not merely the chain that drives it, starts with law `nu`. -/
theorem jumpMeasure_map_jumpProcess_zero {lam : E → ℝ} (hlam : ∀ x, 0 < lam x)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu] :
    (jumpMeasure mu nu).map (jumpProcess lam 0) = nu := by
  have h : (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpProcess lam 0 ω)
      =ᵐ[jumpMeasure mu nu] fun ω ↦ ω.1 0 := by
    filter_upwards [ae_pos_snd_jumpMeasure mu nu] with ω hω
    exact jumpProcess_zero (y := ω.1) (xi := ω.2) hω hlam
  rw [Measure.map_congr h, jumpMeasure_map_chain_zero]

/-! ### The jump construction as a kernel in the initial state

`jumpMeasure mu nu` fixes an initial law, and no statement about it says that the
expectation of a bounded functional is measurable in the initial *state* -- which is what
the Markov property at a fixed time needs, since there the initial state is itself random.
The construction is a kernel, and `jumpKernel` is that kernel; over a bare
`[MeasurableSpace E]` it is the only source of that measurability. -/

section JumpKernel

variable (mu : Kernel E E) [IsMarkovKernel mu]

/-- **The jump construction as a kernel in the initial state.** -/
noncomputable def jumpKernel : Kernel E ((ℕ → E) × (ℕ → ℝ)) :=
  (chainKernel mu).prod (Kernel.const E waitingMeasure)

instance instIsMarkovKernelJumpKernel : IsMarkovKernel (jumpKernel mu) := by
  unfold jumpKernel; infer_instance

theorem jumpKernel_apply (z : E) :
    jumpKernel mu z = (chainKernel mu z).prod waitingMeasure := by
  rw [jumpKernel, Kernel.prod_apply, Kernel.const_apply]

/-- **The jump construction is the composition of its kernel with the initial law.** -/
theorem jumpMeasure_eq_comp (nu : Measure E) [IsProbabilityMeasure nu] :
    jumpMeasure mu nu = jumpKernel mu ∘ₘ nu := by
  rw [jumpMeasure]
  refine Measure.prod_eq fun s t hs ht ↦ ?_
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _)]
  simp_rw [jumpKernel_apply, Measure.prod_prod]
  rw [lintegral_mul_const' _ _ (measure_ne_top _ _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]


/-- **Integration against the jump construction, disintegrated over the initial state.** -/
theorem integral_jumpMeasure_eq_integral_jumpKernel (nu : Measure E) [IsProbabilityMeasure nu]
    {F : (ℕ → E) × (ℕ → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂(jumpMeasure mu nu) = ∫ z, (∫ ω, F ω ∂(jumpKernel mu z)) ∂nu := by
  rw [jumpMeasure_eq_comp, Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp (integrable_of_abs_le hF hC), Kernel.const_apply]

/-- **The expectation of a bounded functional is measurable in the initial state.** -/
theorem measurable_integral_jumpKernel {F : (ℕ → E) × (ℕ → ℝ) → ℝ} (hF : Measurable F) :
    Measurable fun z ↦ ∫ ω, F ω ∂(jumpKernel mu z) :=
  (StronglyMeasurable.integral_kernel_prod_right' (κ := jumpKernel mu)
    (f := fun p : E × ((ℕ → E) × (ℕ → ℝ)) ↦ F p.2)
    (hF.comp measurable_snd).stronglyMeasurable).measurable

/-- **Under `jumpKernel mu z` the initial state of the chain may be replaced by `z`.**  Over a
bare `[MeasurableSpace E]` the almost sure statement `ω.1 0 = z` is not available -- it would need
`{z}` to be measurable -- so the substitution is stated for a bounded measurable functional and
proved on the splitting of the chain at its first step. -/
theorem integral_chainKernel_zero_eq {H : E × (ℕ → E) → ℝ} (hH : Measurable H) {C : ℝ}
    (hC : ∀ p, |H p| ≤ C) (z : E) :
    ∫ y, H (y 0, y) ∂(chainKernel mu z) = ∫ y, H (z, y) ∂(chainKernel mu z) := by
  have hsplit : Measurable (fun x : ℕ → E ↦ (x 0, fun n ↦ x (n + 1))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)
  have hnc : ∀ y : ℕ → E, natCons (y 0, fun n ↦ y (n + 1)) = y := by
    intro y; funext n
    by_cases h : n = 0
    · simp [natCons, h]
    · simp only [natCons, if_neg h]
      congr 1
      omega
  have key : ∀ K : E × (ℕ → E) → ℝ, Measurable K → (∀ p, |K p| ≤ C) →
      (∫ y, K (y 0, y) ∂(chainKernel mu z))
        = ∫ tail, K (z, natCons (z, tail)) ∂(chainKernel mu ∘ₘ (mu z)) := by
    intro K hK hKb
    have hΨ : Measurable fun p : E × (ℕ → E) ↦ K (p.1, natCons p) :=
      hK.comp (measurable_fst.prodMk measurable_natCons)
    have h1 : (∫ y, K (y 0, y) ∂(chainKernel mu z))
        = ∫ y, (fun p : E × (ℕ → E) ↦ K (p.1, natCons p))
            ((fun x : ℕ → E ↦ (x 0, fun n ↦ x (n + 1))) y) ∂(chainKernel mu z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [hnc y]
    rw [h1, ← integral_map hsplit.aemeasurable hΨ.aestronglyMeasurable, chainKernel_map_split,
      integral_prod _ (integrable_of_abs_le hΨ fun p ↦ hKb _),
      integral_dirac' _ z ((hΨ.stronglyMeasurable).integral_prod_right')]
  rw [key H hH hC, key (fun p ↦ H (z, p.2)) (hH.comp (measurable_const.prodMk measurable_snd))
    (fun p ↦ hC _)]


/-- **The same substitution for the whole jump construction.** -/
theorem integral_jumpKernel_zero_eq {F : E × ((ℕ → E) × (ℕ → ℝ)) → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ p, |F p| ≤ C) (z : E) :
    ∫ ω, F (ω.1 0, ω) ∂(jumpKernel mu z) = ∫ ω, F (z, ω) ∂(jumpKernel mu z) := by
  have hm1 : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ F (ω.1 0, ω) :=
    hF.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_id)
  have hm2 : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ F (z, ω) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hG : Measurable fun q : (E × (ℕ → E)) × (ℕ → ℝ) ↦ F (q.1.1, (q.1.2, q.2)) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hH : Measurable fun p : E × (ℕ → E) ↦ ∫ xi, F (p.1, (p.2, xi)) ∂waitingMeasure :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := waitingMeasure)).measurable
  have hHb : ∀ p : E × (ℕ → E), |∫ xi, F (p.1, (p.2, xi)) ∂waitingMeasure| ≤ C :=
    fun p ↦ abs_integral_le_of_abs_le fun xi ↦ hC _
  rw [jumpKernel_apply, integral_prod _ (integrable_of_abs_le hm1 fun _ ↦ hC _),
    integral_prod _ (integrable_of_abs_le hm2 fun _ ↦ hC _)]
  exact integral_chainKernel_zero_eq mu hH hHb z

/-! ### The transition semigroup -/

/-- **The transition semigroup of the jump construction**, as a function of the initial state.
This is the object that `jumpKernel` exists for: over a bare `[MeasurableSpace E]` the expectation
of a bounded functional started at `z` is measurable in `z` because the construction is a kernel,
and no statement about a fixed initial law delivers that. -/
noncomputable def jumpSemigroup (lam : E → ℝ) (mu : Kernel E E) [IsMarkovKernel mu] (h : E → ℝ) (t : ℝ)
    (z : E) : ℝ :=
  ∫ ω, h (jumpProcess lam t ω) ∂(jumpKernel mu z)

theorem measurable_uncurry_jumpSemigroup {lam : E → ℝ} (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) : Measurable fun p : ℝ × E ↦ jumpSemigroup lam mu h p.1 p.2 := by
  have hf : Measurable fun q : (ℝ × E) × ((ℕ → E) × (ℕ → ℝ)) ↦ h (jumpProcess lam q.1.1 q.2) :=
    hh.comp ((measurable_jumpProcess hlam).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have heq : ∀ p : ℝ × E, (Kernel.prodMkLeft ℝ (jumpKernel mu)) p = jumpKernel mu p.2 := by
    rintro ⟨r, z⟩
    rw [Kernel.prodMkLeft_apply]
  have key : Measurable fun p : ℝ × E ↦ ∫ ω, (fun q : (ℝ × E) × ((ℕ → E) × (ℕ → ℝ)) ↦
      h (jumpProcess lam q.1.1 q.2)) (p, ω) ∂(Kernel.prodMkLeft ℝ (jumpKernel mu) p) :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (κ := Kernel.prodMkLeft ℝ (jumpKernel mu))
      (f := fun q : (ℝ × E) × ((ℕ → E) × (ℕ → ℝ)) ↦ h (jumpProcess lam q.1.1 q.2))
      hf.stronglyMeasurable).measurable
  simp only [heq] at key
  exact key

theorem measurable_jumpSemigroup {lam : E → ℝ} (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) (t : ℝ) : Measurable (jumpSemigroup lam mu h t) := by
  have key : Measurable fun z : E ↦
      (fun p : ℝ × E ↦ jumpSemigroup lam mu h p.1 p.2) (t, z) :=
    (measurable_uncurry_jumpSemigroup mu hlam hh).comp'
      (measurable_const.prodMk measurable_id)
  exact key

theorem abs_jumpSemigroup_le {lam : E → ℝ} {h : E → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (t : ℝ)
    (z : E) : |jumpSemigroup lam mu h t z| ≤ C :=
  abs_integral_le_of_abs_le fun ω ↦ hC _

theorem integral_jumpSemigroup_eq (nu : Measure E) [IsProbabilityMeasure nu] {lam : E → ℝ}
    (hlam : Measurable lam) {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (t : ℝ) :
    ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu) = ∫ z, jumpSemigroup lam mu h t z ∂nu :=
  integral_jumpMeasure_eq_integral_jumpKernel mu nu
    (hh.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)))
    (fun ω ↦ hC _)

end JumpKernel

/-! ### The shift of the clock before the first jump -/

/-- **Advancing the clock by a fixed amount of the zeroth waiting time.**  The chain is untouched
and only the zeroth waiting time is shortened; `jumpProcess_waitShift` says that this is exactly
a shift of the time axis by `s` when `a = lam (ω.1 0) * s`. -/
def waitShift (a : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) : (ℕ → E) × (ℕ → ℝ) :=
  (ω.1, fun n ↦ if n = 0 then ω.2 0 - a else ω.2 n)

theorem measurable_waitShift (a : ℝ) : Measurable (waitShift (E := E) a) := by
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun n ↦ ?_)
  by_cases h : n = 0
  · simp only [waitShift, if_pos h]
    exact ((measurable_pi_apply 0).comp measurable_snd).sub measurable_const
  · simp only [waitShift, if_neg h]
    exact (measurable_pi_apply n).comp measurable_snd

/-- **The jump times of the shortened data**: every one of them, except the trivial `T 0`, is
moved back by `a / lam (y 0)`.  Note that no positivity is used -- the identity is an identity of
real numbers, and it holds also where the shortened waiting time has become negative. -/
theorem jumpTime_waitShift (lam : E → ℝ) (y : ℕ → E) (xi : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    jumpTime lam y (fun k ↦ if k = 0 then xi 0 - a else xi k) (n + 1)
      = jumpTime lam y xi (n + 1) - a / lam (y 0) := by
  induction n with
  | zero =>
      have h0 : jumpTime lam y (fun k ↦ if k = 0 then xi 0 - a else xi k) 1
          = (xi 0 - a) / lam (y 0) := by simp [jumpTime]
      have h1 : jumpTime lam y xi 1 = xi 0 / lam (y 0) := by simp [jumpTime]
      rw [h0, h1, sub_div]
  | succ n ih =>
      rw [jumpTime_succ, ih, jumpTime_succ lam y xi (n + 1)]
      simp only [if_neg (Nat.succ_ne_zero n)]
      ring

/-- **Shortening the zeroth waiting time by `lam (y 0) * s` is a shift of the time axis by `s`.**
It needs nothing but `lam (ω.1 0) ≠ 0`: no monotonicity, no non explosion, and no sign of `s`.
The chain is untouched, and every window of the shortened data is the corresponding window of the
original moved back by `s`. -/
theorem jumpProcess_waitShift {lam : E → ℝ} {ω : (ℕ → E) × (ℕ → ℝ)} (hlam : lam (ω.1 0) ≠ 0)
    (s t : ℝ) :
    jumpProcess lam t (waitShift (lam (ω.1 0) * s) ω) = jumpProcess lam (s + t) ω := by
  have hdiv : lam (ω.1 0) * s / lam (ω.1 0) = s := by
    field_simp
  have hT : ∀ n : ℕ, jumpTime lam (waitShift (lam (ω.1 0) * s) ω).1
      (waitShift (lam (ω.1 0) * s) ω).2 (n + 1) = jumpTime lam ω.1 ω.2 (n + 1) - s := by
    intro n
    rw [show (waitShift (lam (ω.1 0) * s) ω).1 = ω.1 from rfl]
    rw [show (waitShift (lam (ω.1 0) * s) ω).2
      = (fun k ↦ if k = 0 then ω.2 0 - lam (ω.1 0) * s else ω.2 k) from rfl,
      jumpTime_waitShift, hdiv]
  have hset : {n | t < jumpTime lam (waitShift (lam (ω.1 0) * s) ω).1
        (waitShift (lam (ω.1 0) * s) ω).2 (n + 1)}
      = {n | s + t < jumpTime lam ω.1 ω.2 (n + 1)} := by
    ext n
    simp only [Set.mem_setOf_eq, hT n]
    constructor <;> intro h <;> linarith
  simp only [jumpProcess, stepPath, stepIndex, hset]
  rfl




/-! ### The memorylessness of the waiting times -/

/-- Prepending an independent standard exponential variable to the waiting times reproduces
them.  This is `infinitePi_map_natCons` for the one product the construction uses. -/
theorem waitingMeasure_map_natCons :
    ((expMeasure 1).prod waitingMeasure).map natCons = waitingMeasure := by
  unfold waitingMeasure
  exact infinitePi_map_natCons (expMeasure 1)


/-- **The memorylessness of the standard exponential law, in the form the restart at a fixed time
needs.**  Cutting `a` off the zeroth waiting time and keeping only the paths on which it survives
reproduces `waitingMeasure` itself, at the price of the factor `exp (-a)`.

Mathlib has the distribution function of `expMeasure` but neither its tail nor this identity, and
`expMeasure_Ioi_add` -- the multiplicative form of the tail -- is a statement about *sets*: it does
not by itself say that the law of the residual waiting time is again exponential and independent
of everything else.  That is what is proved here. -/
theorem integral_waitingMeasure_waitShift {a : ℝ} (ha : 0 ≤ a) {F : (ℕ → ℝ) → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    (∫ xi in {xi : ℕ → ℝ | a < xi 0},
        F (fun n ↦ if n = 0 then xi 0 - a else xi n) ∂waitingMeasure)
      = Real.exp (-a) * ∫ xi, F xi ∂waitingMeasure := by
  classical
  have h0C : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ ↦ 0))
  set Ψ : ℝ → ℝ := fun v ↦ ∫ tail, F (natCons (v, tail)) ∂waitingMeasure with hΨdef
  set Φ : ℝ × (ℕ → ℝ) → ℝ := fun p ↦ if a < p.1 then F (natCons (p.1 - a, p.2)) else 0 with hΦdef
  have hΦ : Measurable Φ := by
    refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
    exact hF.comp (measurable_natCons.comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd))
  have hΦb : ∀ p, |Φ p| ≤ C := by
    intro p
    by_cases hp : a < p.1
    · simpa [hΦdef, hp] using hC _
    · simpa [hΦdef, hp] using h0C
  have hsplitm : Measurable (fun x : ℕ → ℝ ↦ (x 0, fun n ↦ x (n + 1))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)
  have hset : MeasurableSet {xi : ℕ → ℝ | a < xi 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  -- Step A: the integrand is a function of the zeroth coordinate and the tail.
  have stepA : (∫ xi in {xi : ℕ → ℝ | a < xi 0},
        F (fun n ↦ if n = 0 then xi 0 - a else xi n) ∂waitingMeasure)
      = ∫ xi, Φ ((fun x : ℕ → ℝ ↦ (x 0, fun n ↦ x (n + 1))) xi) ∂waitingMeasure := by
    rw [← integral_indicator hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun xi ↦ ?_)
    by_cases hx : a < xi 0
    · rw [Set.indicator_of_mem (show xi ∈ {xi : ℕ → ℝ | a < xi 0} from hx)]
      simp only [hΦdef, if_pos hx]
      congr 1
      funext n
      by_cases hn : n = 0
      · simp [natCons, hn]
      · simp only [natCons, if_neg hn]
        congr 1
        omega
    · rw [Set.indicator_of_notMem (show xi ∉ {xi : ℕ → ℝ | a < xi 0} from hx)]
      simp only [hΦdef, if_neg hx]
  -- Step B: the zeroth coordinate is independent of the tail.
  have stepB : (∫ xi, Φ ((fun x : ℕ → ℝ ↦ (x 0, fun n ↦ x (n + 1))) xi) ∂waitingMeasure)
      = ∫ u, (∫ tail, Φ (u, tail) ∂waitingMeasure) ∂(expMeasure 1) := by
    rw [← integral_map hsplitm.aemeasurable hΦ.aestronglyMeasurable, waitingMeasure_map_split,
      integral_prod _ (integrable_of_abs_le hΦ hΦb)]
  have hinner : ∀ u : ℝ, (∫ tail, Φ (u, tail) ∂waitingMeasure) = if a < u then Ψ (u - a) else 0 := by
    intro u
    by_cases hu : a < u
    · simp only [hΦdef, if_pos hu, hΨdef]
    · simp only [hΦdef, if_neg hu, integral_zero, if_neg hu]
  -- Step C: the translation of the half line, which is where the factor `exp (-a)` appears.
  have stepC : (∫ u, (if a < u then Ψ (u - a) else 0) ∂(expMeasure 1))
      = Real.exp (-a) * ∫ v, Ψ v ∂(expMeasure 1) := by
    rw [integral_expMeasure_one, integral_expMeasure_one, ← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioi,
      ← integral_add_right_eq_self (fun u ↦ (Set.Ioi (0 : ℝ)).indicator
        (fun u ↦ Real.exp (-u) * (if a < u then Ψ (u - a) else 0)) u) a, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    show (Set.Ioi (0:ℝ)).indicator
          (fun u ↦ Real.exp (-u) * (if a < u then Ψ (u - a) else 0)) (v + a)
        = Real.exp (-a) * (Set.Ioi (0:ℝ)).indicator (fun s ↦ Real.exp (-s) * Ψ s) v
    by_cases hv : (0 : ℝ) < v
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hv),
        Set.indicator_of_mem (Set.mem_Ioi.2 (show (0:ℝ) < v + a by linarith)),
        if_pos (show a < v + a by linarith)]
      simp only [add_sub_cancel_right]
      rw [show -(v + a) = -a + -v from by ring, Real.exp_add]
      ring
    · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0:ℝ) from by simpa using hv), mul_zero]
      by_cases hva : (0 : ℝ) < v + a
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hva),
          if_neg (not_lt.2 (by simp only [not_lt] at hv; linarith)), mul_zero]
      · rw [Set.indicator_of_notMem (show v + a ∉ Set.Ioi (0:ℝ) from by simpa using hva)]
  -- Step D: prepending an independent exponential variable recovers `waitingMeasure`.
  have stepD : (∫ v, Ψ v ∂(expMeasure 1)) = ∫ xi, F xi ∂waitingMeasure := by
    have h1 : (∫ v, Ψ v ∂(expMeasure 1))
        = ∫ p, F (natCons p) ∂((expMeasure 1).prod waitingMeasure) :=
      (integral_prod _ (integrable_of_abs_le (hF.comp measurable_natCons) fun p ↦ hC _)).symm
    rw [h1, ← integral_map measurable_natCons.aemeasurable hF.aestronglyMeasurable,
      waitingMeasure_map_natCons]
  rw [stepA, stepB]
  simp_rw [hinner]
  rw [stepC, stepD]



/-! ### The restart at a fixed time, before the first jump -/

section Restart

variable (mu : Kernel E E) [IsMarkovKernel mu]

/-- **The restart of the jump construction at a fixed time `s`, on the event that the first jump
has not yet happened.**  This is the base case of the Markov property: given `{s < T 1}` the
driving data restarted at `s` is again the driving data of a jump construction from the same
initial state, and the price is the survival factor `exp (-(lam z * s))`.

Both ingredients are used exactly once: `integral_waitingMeasure_waitShift` for the residual
waiting time, and `integral_chainKernel_zero_eq` to turn `lam (ω.1 0)` into `lam z` -- the latter
is needed because over a bare `[MeasurableSpace E]` the identity `ω.1 0 = z` is not available
almost surely. -/
theorem integral_jumpKernel_waitShift {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) (z : E) {F : (ℕ → E) × (ℕ → ℝ) → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ ω, |F ω| ≤ C) {s : ℝ} (hs : 0 ≤ s) :
    (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
        F (waitShift (lam (ω.1 0) * s) ω) ∂(jumpKernel mu z))
      = Real.exp (-(lam z * s)) * ∫ ω, F ω ∂(jumpKernel mu z) := by
  classical
  have hSeq : {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}
      = {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, jumpTime_one]
    rw [lt_div_iff₀ (hlam0 _), mul_comm s (lam (ω.1 0))]
  have hS : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0} :=
    measurableSet_lt ((hlam.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      measurable_const) ((measurable_pi_apply 0).comp measurable_snd)
  have hmap : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ F (waitShift (lam (ω.1 0) * s) ω) := by
    refine hF.comp (measurable_fst.prodMk (measurable_pi_lambda _ fun n ↦ ?_))
    by_cases hn : n = 0
    · simp only [waitShift, if_pos hn]
      exact ((measurable_pi_apply 0).comp measurable_snd).sub
        ((hlam.comp ((measurable_pi_apply 0).comp measurable_fst)).mul measurable_const)
    · simp only [waitShift, if_neg hn]
      exact (measurable_pi_apply n).comp measurable_snd
  -- The inner integral over the waiting times, for a fixed path of the chain.
  have hG : Measurable fun p : (ℕ → E) × (ℕ → ℝ) ↦ F (p.1, p.2) := hF
  have hGmeas : Measurable fun y : ℕ → E ↦ ∫ xi, F (y, xi) ∂waitingMeasure :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := waitingMeasure)).measurable
  have hGb : ∀ y : ℕ → E, |∫ xi, F (y, xi) ∂waitingMeasure| ≤ C :=
    fun y ↦ abs_integral_le_of_abs_le fun xi ↦ hC _
  have hinner : ∀ y : ℕ → E,
      (∫ xi in {xi : ℕ → ℝ | lam (y 0) * s < xi 0},
          F (y, fun n ↦ if n = 0 then xi 0 - lam (y 0) * s else xi n) ∂waitingMeasure)
        = Real.exp (-(lam (y 0) * s)) * ∫ xi, F (y, xi) ∂waitingMeasure :=
    fun y ↦ integral_waitingMeasure_waitShift (mul_nonneg (hlam0 _).le hs)
      (hF.comp (measurable_const.prodMk measurable_id)) (fun xi ↦ hC _)
  -- Assemble: first the product structure, then the substitution of `z` for `ω.1 0`.
  have hprod : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0},
        F (waitShift (lam (ω.1 0) * s) ω) ∂(jumpKernel mu z))
      = ∫ y, Real.exp (-(lam (y 0) * s)) * (∫ xi, F (y, xi) ∂waitingMeasure)
          ∂(chainKernel mu z) := by
    rw [← integral_indicator hS, jumpKernel_apply,
      integral_prod _ ((integrable_of_abs_le hmap (fun ω ↦ hC _)).indicator hS)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    show (∫ xi, {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0}.indicator
          (fun ω ↦ F (waitShift (lam (ω.1 0) * s) ω)) (y, xi) ∂waitingMeasure)
        = Real.exp (-(lam (y 0) * s)) * ∫ xi, F (y, xi) ∂waitingMeasure
    rw [← hinner y, ← integral_indicator (measurableSet_lt measurable_const
      (measurable_pi_apply 0))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun xi ↦ ?_)
    show {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0}.indicator
          (fun ω ↦ F (waitShift (lam (ω.1 0) * s) ω)) (y, xi)
        = {xi : ℕ → ℝ | lam (y 0) * s < xi 0}.indicator
            (fun xi ↦ F (y, fun n ↦ if n = 0 then xi 0 - lam (y 0) * s else xi n)) xi
    by_cases hx : lam (y 0) * s < xi 0
    · rw [Set.indicator_of_mem (show (y, xi) ∈ {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0}
        from hx), Set.indicator_of_mem (show xi ∈ {xi : ℕ → ℝ | lam (y 0) * s < xi 0} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show (y, xi) ∉ {ω : (ℕ → E) × (ℕ → ℝ) | lam (ω.1 0) * s < ω.2 0}
        from hx), Set.indicator_of_notMem (show xi ∉ {xi : ℕ → ℝ | lam (y 0) * s < xi 0} from hx)]
  have hH : Measurable fun p : E × (ℕ → E) ↦
      Real.exp (-(lam p.1 * s)) * ∫ xi, F (p.2, xi) ∂waitingMeasure :=
    (Real.measurable_exp.comp (((hlam.comp measurable_fst).mul measurable_const).neg)).mul
      (hGmeas.comp measurable_snd)
  have hHb : ∀ p : E × (ℕ → E),
      |Real.exp (-(lam p.1 * s)) * ∫ xi, F (p.2, xi) ∂waitingMeasure| ≤ C := by
    intro p
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-(lam p.1 * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [(hlam0 p.1).le, hs])
    calc Real.exp (-(lam p.1 * s)) * |∫ xi, F (p.2, xi) ∂waitingMeasure|
        ≤ 1 * |∫ xi, F (p.2, xi) ∂waitingMeasure| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ C := by rw [one_mul]; exact hGb _
  rw [hSeq, hprod, integral_chainKernel_zero_eq mu hH hHb z]
  show (∫ y, Real.exp (-(lam z * s)) * ∫ xi, F (y, xi) ∂waitingMeasure ∂(chainKernel mu z))
      = Real.exp (-(lam z * s)) * ∫ ω, F ω ∂(jumpKernel mu z)
  rw [integral_const_mul, jumpKernel_apply, integral_prod _ (integrable_of_abs_le hF hC)]

/-- **The Markov property of the jump process at a fixed time, on the event that the first jump
has not yet happened.**  Both sides are `exp (-(lam z * s)) * jumpSemigroup lam mu h t z`. -/
theorem integral_jumpKernel_add_of_lt_jumpTime_one {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) (z : E) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) {s t : ℝ} (hs : 0 ≤ s) :
    (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
        h (jumpProcess lam (s + t) ω) ∂(jumpKernel mu z))
      = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
          jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpKernel mu z) := by
  have hFmeas : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam t ω) :=
    hh.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
  have hgmeas : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpSemigroup lam mu h t (ω.1 0) :=
    (measurable_jumpSemigroup mu hlam hh t).comp
      ((measurable_pi_apply 0).comp measurable_fst)
  have hS : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1} :=
    measurableSet_lt measurable_const (measurable_jumpTime hlam 1)
  -- the left hand side
  have hleft : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
        h (jumpProcess lam (s + t) ω) ∂(jumpKernel mu z))
      = Real.exp (-(lam z * s)) * jumpSemigroup lam mu h t z := by
    show (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
          h (jumpProcess lam (s + t) ω) ∂(jumpKernel mu z))
        = Real.exp (-(lam z * s)) * ∫ ω, h (jumpProcess lam t ω) ∂(jumpKernel mu z)
    rw [← integral_jumpKernel_waitShift mu hlam hlam0 z hFmeas (fun ω ↦ hC _) hs]
    refine setIntegral_congr_fun hS (fun ω _ ↦ ?_)
    rw [jumpProcess_waitShift (ne_of_gt (hlam0 _))]
  -- the right hand side
  have hright : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
        jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpKernel mu z))
      = Real.exp (-(lam z * s)) * jumpSemigroup lam mu h t z := by
    have hcongr : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
          jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpKernel mu z))
        = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
            jumpSemigroup lam mu h t ((waitShift (lam (ω.1 0) * s) ω).1 0) ∂(jumpKernel mu z) := by
      refine setIntegral_congr_fun hS (fun ω hω ↦ ?_)
      rw [jumpProcess_of_lt_jumpTime_one hω]
      rfl
    rw [hcongr, integral_jumpKernel_waitShift mu hlam hlam0 z hgmeas
      (fun ω ↦ abs_jumpSemigroup_le mu hC t _) hs]
    congr 1
    have hsub := integral_jumpKernel_zero_eq mu
      (F := fun p : E × ((ℕ → E) × (ℕ → ℝ)) ↦ jumpSemigroup lam mu h t p.1)
      ((measurable_jumpSemigroup mu hlam hh t).comp measurable_fst)
      (fun p ↦ abs_jumpSemigroup_le mu hC t _) z
    rw [hsub]
    show (∫ _ω : (ℕ → E) × (ℕ → ℝ), jumpSemigroup lam mu h t z ∂(jumpKernel mu z))
        = jumpSemigroup lam mu h t z
    rw [integral_const]
    simp
  rw [hleft, hright]

end Restart

/-! ### The first jump decomposition

The renewal equation of the construction, before the Markov property is used on its second term.
Splitting the expectation at the first jump costs no analysis at all: the event `{t < T 1}` is
`{ξ 0 > lam (y 0) * t}` by `jumpTime_one`, on it the path has not moved
(`jumpProcess_of_lt_jumpTime_one`), and its probability is the tail `expMeasure_Ioi` of a single
exponential variable, computed on the second factor of the product measure.

The statement is for a general initial law `nu`, not for `Measure.dirac x`, and the first term is
therefore an integral against `nu` rather than a single exponential factor.  That is not
generality for its own sake: pinning `nu` to a Dirac measure and reading off `ω.1 0 = x` almost
surely would need `{x}ᶜ` to be measurable, and `E` carries nothing but a `MeasurableSpace`. -/
theorem jumpMeasure_integral_eq_of_firstJump {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
      = (∫ z, Real.exp (-(lam z * t)) * h z ∂nu)
        + ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t},
            h (jumpProcess lam t ω) ∂(jumpMeasure mu nu) := by
  have hS : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} :=
    measurableSet_le (measurable_jumpTime hlam 1) measurable_const
  have hXmeas : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam t ω) :=
    hh.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
  have hzmeas : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (ω.1 0) :=
    hh.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hXint : Integrable (fun ω ↦ h (jumpProcess lam t ω)) (jumpMeasure mu nu) :=
    Integrable.mono' (integrable_const C) hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ hC _)
  have hind : Integrable
      ({ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ.indicator fun ω ↦ h (ω.1 0))
      ((chainKernel mu ∘ₘ nu).prod waitingMeasure) :=
    (Integrable.mono' (integrable_const C) hzmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ hC _)).indicator hS.compl
  have hEq : Set.EqOn (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam t ω))
      (fun ω ↦ h (ω.1 0)) {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [jumpProcess_of_lt_jumpTime_one hω]
  have hinner : ∀ yy : ℕ → E,
      (∫ ξ : ℕ → ℝ, {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ.indicator
          (fun ω ↦ h (ω.1 0)) (yy, ξ) ∂waitingMeasure)
        = Real.exp (-(lam (yy 0) * t)) * h (yy 0) := by
    intro yy
    have hiff : ∀ ξ : ℕ → ℝ,
        ((yy, ξ) ∈ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ)
          ↔ ξ 0 ∈ Set.Ioi (lam (yy 0) * t) := by
      intro ξ
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, jumpTime_one, Set.mem_Ioi]
      rw [lt_div_iff₀ (hlam0 _), mul_comm t (lam (yy 0))]
    have hset : (fun ξ : ℕ → ℝ ↦ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ.indicator
        (fun ω ↦ h (ω.1 0)) (yy, ξ))
        = {ξ : ℕ → ℝ | ξ 0 ∈ Set.Ioi (lam (yy 0) * t)}.indicator (fun _ ↦ h (yy 0)) := by
      funext ξ
      simp only [Set.indicator_apply, hiff ξ, Set.mem_setOf_eq]
    rw [hset, integral_indicator_const (h (yy 0))
        (s := {ξ : ℕ → ℝ | ξ 0 ∈ Set.Ioi (lam (yy 0) * t)})
        (measurableSet_Ioi.preimage (measurable_pi_apply 0)), measureReal_def,
      waitingMeasure_eval_preimage measurableSet_Ioi 0,
      expMeasure_Ioi one_pos (mul_nonneg (hlam0 _).le ht),
      ENNReal.toReal_ofReal (Real.exp_pos _).le, one_mul, smul_eq_mul]
  have key : ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t}ᶜ,
      h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
      = ∫ z, Real.exp (-(lam z * t)) * h z ∂nu := by
    rw [setIntegral_congr_fun hS.compl hEq, ← integral_indicator hS.compl, jumpMeasure,
      integral_prod _ hind]
    simp_rw [hinner]
    conv_rhs => rw [← comp_chainKernel_map_zero mu nu]
    rw [integral_map (measurable_pi_apply 0).aemeasurable
      (((Real.measurable_exp.comp ((hlam.mul measurable_const).neg)).mul hh)).aestronglyMeasurable]
  rw [← integral_add_compl hS hXint, key]
  exact add_comm _ _

/-! ### The restart at the first jump, and the renewal equation

`jumpMeasure_map_split` gives the joint law of the initial state, the zeroth waiting time and the
shifted data, but on the *unordered* space `(E × (ℕ → E)) × (ℝ × (ℕ → ℝ))`: the shifted chain sits
in the first factor and the shifted waiting times in the second.  The renewal equation wants the
two tails bundled into a single point of `(ℕ → E) × (ℕ → ℝ)`, so that
`prod_comp_chainKernel_eq_jumpMeasure` can recognise their law as a jump construction again.  That
bundling is a Fubini swap of the shifted chain against the zeroth waiting time, and
`integral_jumpMeasure_eq_of_split` performs it once and for all. -/

/-- **The restart at the first jump, as an integral identity.**  A bounded measurable function of
the initial state, the zeroth waiting time and the shifted data integrates in three stages: the
initial state against `nu`, the zeroth waiting time against the standard exponential law, and the
shifted data against the jump construction started from **one step of `mu`**.

The boundedness is not decoration: the Fubini swap in the middle needs the integrand integrable on
a product, and `Measure.integral_compProd` needs it integrable against the composition.  A single
constant bound supplies all five, through `integrable_of_abs_le` and `abs_integral_le_of_abs_le`. -/
theorem integral_jumpMeasure_eq_of_split (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] {G : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ} (hG : Measurable G)
    {C : ℝ} (hC : ∀ p, |G p| ≤ C) :
    ∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)
      = ∫ z, ∫ s, ∫ ω', G ((z, s), ω') ∂(jumpMeasure mu (mu z)) ∂(expMeasure 1) ∂nu := by
  classical
  have hR : Measurable fun p : (E × (ℕ → E)) × (ℝ × (ℕ → ℝ)) ↦
      G ((p.1.1, p.2.1), (p.1.2, p.2.2)) :=
    hG.comp (((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hRb : ∀ p : (E × (ℕ → E)) × (ℝ × (ℕ → ℝ)), |G ((p.1.1, p.2.1), (p.1.2, p.2.2))| ≤ C :=
    fun p ↦ hC _
  -- Step 1: transport to the split space.
  have hΨ : Measurable (fun ω : (ℕ → E) × (ℕ → ℝ) ↦
      ((ω.1 0, fun n ↦ ω.1 (n + 1)), (ω.2 0, fun n ↦ ω.2 (n + 1)))) :=
    (((measurable_pi_apply 0).comp measurable_fst).prodMk
        (measurable_pi_lambda _ fun n ↦ (measurable_pi_apply (n + 1)).comp measurable_fst)).prodMk
      (((measurable_pi_apply 0).comp measurable_snd).prodMk
        (measurable_pi_lambda _ fun n ↦ (measurable_pi_apply (n + 1)).comp measurable_snd))
  have step1 : ∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)
      = ∫ p, G ((p.1.1, p.2.1), (p.1.2, p.2.2))
          ∂((nu ⊗ₘ (chainKernel mu ∘ₖ mu)).prod ((expMeasure 1).prod waitingMeasure)) := by
    rw [← jumpMeasure_map_split mu nu, integral_map hΨ.aemeasurable hR.aestronglyMeasurable]
    rfl
  -- Steps 2 and 3: unfold the two products.
  have step2 : ∫ p, G ((p.1.1, p.2.1), (p.1.2, p.2.2))
        ∂((nu ⊗ₘ (chainKernel mu ∘ₖ mu)).prod ((expMeasure 1).prod waitingMeasure))
      = ∫ q, (∫ s, ∫ xt, G ((q.1, s), (q.2, xt)) ∂waitingMeasure ∂(expMeasure 1))
          ∂(nu ⊗ₘ (chainKernel mu ∘ₖ mu)) := by
    rw [integral_prod _ (integrable_of_abs_le hR hRb)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q ↦ ?_)
    exact integral_prod _ (integrable_of_abs_le (hR.comp measurable_prodMk_left) fun _ ↦ hRb _)
  -- The inner double integral, as a measurable bounded function of the first factor.
  have hR2 : Measurable fun p : ((E × (ℕ → E)) × ℝ) × (ℕ → ℝ) ↦
      G ((p.1.1.1, p.1.2), (p.1.1.2, p.2)) :=
    hG.comp ((((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst)).prodMk
      (((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk measurable_snd))
  have hinner : Measurable fun p : (E × (ℕ → E)) × ℝ ↦
      ∫ xt, G ((p.1.1, p.2), (p.1.2, xt)) ∂waitingMeasure :=
    (hR2.stronglyMeasurable.integral_prod_right' (ν := waitingMeasure)).measurable
  have hHmeas : Measurable fun q : E × (ℕ → E) ↦
      ∫ s, ∫ xt, G ((q.1, s), (q.2, xt)) ∂waitingMeasure ∂(expMeasure 1) :=
    (hinner.stronglyMeasurable.integral_prod_right' (ν := expMeasure 1)).measurable
  have hHb : ∀ q : E × (ℕ → E),
      |∫ s, ∫ xt, G ((q.1, s), (q.2, xt)) ∂waitingMeasure ∂(expMeasure 1)| ≤ C :=
    fun q ↦ abs_integral_le_of_abs_le fun s ↦ abs_integral_le_of_abs_le fun xt ↦ hC _
  -- Step 4: the composition, which is where `nu` separates from the shifted chain.
  have step4 : ∫ q, (∫ s, ∫ xt, G ((q.1, s), (q.2, xt)) ∂waitingMeasure ∂(expMeasure 1))
        ∂(nu ⊗ₘ (chainKernel mu ∘ₖ mu))
      = ∫ z, ∫ yc, (∫ s, ∫ xt, G ((z, s), (yc, xt)) ∂waitingMeasure ∂(expMeasure 1))
          ∂((chainKernel mu ∘ₖ mu) z) ∂nu :=
    Measure.integral_compProd (integrable_of_abs_le hHmeas hHb)
  -- Step 5: the swap of the shifted chain against the zeroth waiting time, and the reassembly of
  -- the two tails into one point of the jump space.
  have step5 : ∀ z : E,
      (∫ yc, (∫ s, ∫ xt, G ((z, s), (yc, xt)) ∂waitingMeasure ∂(expMeasure 1))
          ∂((chainKernel mu ∘ₖ mu) z))
        = ∫ s, ∫ ω', G ((z, s), ω') ∂(jumpMeasure mu (mu z)) ∂(expMeasure 1) := by
    intro z
    have hf : Measurable (Function.uncurry fun (yc : ℕ → E) (s : ℝ) ↦
        ∫ xt, G ((z, s), (yc, xt)) ∂waitingMeasure) := by
      have hg : Measurable fun p : ((ℕ → E) × ℝ) × (ℕ → ℝ) ↦ G ((z, p.1.2), (p.1.1, p.2)) :=
        hG.comp ((measurable_const.prodMk (measurable_snd.comp measurable_fst)).prodMk
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      exact (hg.stronglyMeasurable.integral_prod_right' (ν := waitingMeasure)).measurable
    have hb : ∀ p : (ℕ → E) × ℝ, |(Function.uncurry fun (yc : ℕ → E) (s : ℝ) ↦
        ∫ xt, G ((z, s), (yc, xt)) ∂waitingMeasure) p| ≤ C :=
      fun p ↦ abs_integral_le_of_abs_le fun xt ↦ hC _
    rw [integral_integral_swap (integrable_of_abs_le hf hb)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
    rw [← prod_comp_chainKernel_eq_jumpMeasure mu z]
    exact (integral_prod _ (integrable_of_abs_le
      (hG.comp (measurable_const.prodMk measurable_id)) fun _ ↦ hC _)).symm
  rw [step1, step2, step4]
  exact integral_congr_ae (Filter.Eventually.of_forall step5)

/-- **The renewal equation of the jump construction.**  The expectation of a bounded measurable
functional of the state at time `t` splits at the first jump: on `{T₁ > t}` the path has not moved
and the factor is the exponential tail; on `{T₁ ≤ t}` the process restarts from a state drawn by
`mu`, after a holding time whose law is the standard exponential one read in the units of the
rate, so that the first jump time is `s / lam z` and the remaining time is `t - s / lam z`.

Both halves are stated as integrals against `nu` rather than combined under one, exactly as
`jumpMeasure_integral_eq_of_firstJump` states them: the decomposition delivers a sum of two
integrals, and joining them would need the integrability of the second integrand against `nu` as a
separate step without making the identity say more.

This is the last purely measure theoretic step of `thm:jumpMP`.  What remains for the backward
equation `E_x[f(X_t)] - f x = ∫_0^t E_x[Af(X_s)] ds` is the differentiation of this identity in
`t`, and the integral over `Set.Ioc 0 (lam z * t)` against Lebesgue measure -- rather than an
integral against `expMeasure 1` -- is the shape that differentiation acts on. -/
theorem jumpMeasure_integral_eq_renewal {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
      = (∫ z, Real.exp (-(lam z * t)) * h z ∂nu)
        + ∫ z, (∫ s in Set.Ioc 0 (lam z * t), Real.exp (-s) *
            ∫ ω', h (jumpProcess lam (t - s / lam z) ω') ∂(jumpMeasure mu (mu z))) ∂nu := by
  classical
  have h0C : 0 ≤ C := by
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  set G : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun p ↦
    if p.1.2 ≤ lam p.1.1 * t then h (jumpProcess lam (t - p.1.2 / lam p.1.1) p.2) else 0
    with hGdef
  have hGmeas : Measurable G := by
    rw [hGdef]
    refine Measurable.ite (measurableSet_le (measurable_snd.comp measurable_fst)
      ((hlam.comp (measurable_fst.comp measurable_fst)).mul measurable_const)) ?_
      measurable_const
    exact hh.comp ((measurable_jumpProcess hlam).comp
      ((measurable_const.sub ((measurable_snd.comp measurable_fst).div
        (hlam.comp (measurable_fst.comp measurable_fst)))).prodMk measurable_snd))
  have hGb : ∀ p, |G p| ≤ C := by
    intro p
    by_cases hp : p.1.2 ≤ lam p.1.1 * t
    · simpa [hGdef, hp] using hC _
    · simpa [hGdef, hp] using h0C
  have hSmeas : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} :=
    measurableSet_le (measurable_jumpTime hlam 1) measurable_const
  have key : ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t},
        h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
      = ∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu) := by
    rw [← integral_indicator hSmeas]
    refine integral_congr_ae ?_
    filter_upwards [ae_exists_lt_jumpTime hL0 hlam0 hL mu nu] with ω hω
    by_cases hcase : jumpTime lam ω.1 ω.2 1 ≤ t
    · have hcond : ω.2 0 ≤ lam (ω.1 0) * t := by
        rw [jumpTime_one, div_le_iff₀ (hlam0 _)] at hcase
        linarith
      rw [Set.indicator_of_mem
        (show ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} from hcase)]
      simp only [hGdef, if_pos hcond]
      rw [jumpProcess_jumpShift hcase (hω t), jumpTime_one]
    · have hcond : ¬ (ω.2 0 ≤ lam (ω.1 0) * t) := by
        intro hcon
        rw [jumpTime_one, div_le_iff₀ (hlam0 _)] at hcase
        exact hcase (by linarith)
      rw [Set.indicator_of_notMem
        (show ω ∉ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} from hcase)]
      simp only [hGdef, if_neg hcond]
  rw [jumpMeasure_integral_eq_of_firstJump hlam hlam0 mu nu hh hC ht, key,
    integral_jumpMeasure_eq_of_split mu nu hGmeas hGb]
  refine congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_))
  show (∫ s, ∫ ω', G ((z, s), ω') ∂(jumpMeasure mu (mu z)) ∂(expMeasure 1))
    = ∫ s in Set.Ioc 0 (lam z * t), Real.exp (-s) *
        ∫ ω', h (jumpProcess lam (t - s / lam z) ω') ∂(jumpMeasure mu (mu z))
  have hmul : (fun s : ℝ ↦ Real.exp (-s) * ∫ ω', G ((z, s), ω') ∂(jumpMeasure mu (mu z)))
      = (Set.Iic (lam z * t)).indicator (fun s ↦ Real.exp (-s) *
          ∫ ω', h (jumpProcess lam (t - s / lam z) ω') ∂(jumpMeasure mu (mu z))) := by
    funext s
    by_cases hs : s ≤ lam z * t
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hs)]
      exact congrArg _ (integral_congr_ae
        (Filter.Eventually.of_forall fun ω' ↦ by simp only [hGdef, if_pos hs]))
    · rw [Set.indicator_of_notMem (fun hmem ↦ hs (Set.mem_Iic.1 hmem))]
      have hzero : (∫ ω', G ((z, s), ω') ∂(jumpMeasure mu (mu z))) = 0 := by
        simp only [hGdef, if_neg hs, integral_zero]
      rw [hzero, mul_zero]
  rw [integral_expMeasure_one, hmul, setIntegral_indicator measurableSet_Iic,
    Set.Ioi_inter_Iic]

/-! ### The Markov property at a fixed time

`integral_jumpKernel_add_of_lt_jumpTime_one` is the Markov property on the event that the first
jump has not yet happened.  What carries it to the whole space is an induction on the number of
jumps in `[0, s]`: on `{T 1 ≤ s}` the construction restarts from a state drawn by `mu` at the
remaining time `s - σ / lam z`, which is where the induction hypothesis applies, and the error
after `n` steps is the probability of `n` jumps before `s`.  That probability goes to zero by non
explosion, and the Markov property follows.

The estimate compares two integrals, so it needs the two outer integrals of
`integral_jumpMeasure_eq_of_split` joined into **one** measure on `E × ℝ`: the monotonicity of the
Bochner integral is a statement about one measure, and the iterated form would need the
measurability of the inner integral in the initial state as a separate step at every use.  That
measurability is `measurable_integral_jumpMeasure_step`, and it comes from the construction being
a kernel -- over a bare `[MeasurableSpace E]` nothing else supplies it. -/

section MarkovProperty

variable (mu : Kernel E E) [IsMarkovKernel mu]

/-- **The jump construction started from one step of `mu` is a kernel in the initial state.** -/
theorem jumpMeasure_step_eq_comp (z : E) :
    jumpMeasure mu (mu z) = (jumpKernel mu ∘ₖ mu) z := by
  rw [jumpMeasure_eq_comp, Kernel.comp_apply]

/-- **The inner integral of the splitting is measurable in the pair (initial state, holding
time).**  This is the one place where the estimate below needs the construction to be a kernel:
the outer integration is against a fixed measure on `E × ℝ`, and its integrand is the expectation
of a functional under a measure that depends on the initial state. -/
theorem measurable_integral_jumpMeasure_step {G : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ}
    (hG : Measurable G) :
    Measurable fun p : E × ℝ ↦ ∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1)) := by
  have hk : ∀ p : E × ℝ, (Kernel.prodMkRight ℝ (jumpKernel mu ∘ₖ mu)) p
      = jumpMeasure mu (mu p.1) := by
    intro p
    rw [Kernel.prodMkRight_apply, jumpMeasure_step_eq_comp]
  have key : Measurable fun p : E × ℝ ↦ ∫ ω', G (p, ω')
      ∂((Kernel.prodMkRight ℝ (jumpKernel mu ∘ₖ mu)) p) :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (κ := Kernel.prodMkRight ℝ (jumpKernel mu ∘ₖ mu)) (f := G) hG.stronglyMeasurable).measurable
  simpa only [hk] using key

/-- **The splitting of the expectation, with the initial state and the holding time gathered into
a single product measure.**  This is `integral_jumpMeasure_eq_of_split` with its two outer
integrals joined, and it is what makes the estimate below a comparison of two integrals against
**one** measure. -/
theorem integral_jumpMeasure_eq_of_split_prod (nu : Measure E) [IsProbabilityMeasure nu]
    {G : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ} (hG : Measurable G) {C : ℝ} (hC : ∀ p, |G p| ≤ C) :
    ∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)
      = ∫ p, (∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1))) ∂(nu.prod (expMeasure 1)) := by
  rw [integral_jumpMeasure_eq_of_split mu nu hG hC,
    integral_prod _ (integrable_of_abs_le (measurable_integral_jumpMeasure_step mu hG)
      (fun p ↦ abs_integral_le_of_abs_le fun ω' ↦ hC _))]

/-- **Integration over a measurable set, disintegrated over the initial state.**  The set integral
form of `integral_jumpMeasure_eq_integral_jumpKernel`, which is what carries the base case of the
induction from `jumpKernel` to `jumpMeasure`. -/
theorem setIntegral_jumpMeasure_eq_integral_jumpKernel (nu : Measure E) [IsProbabilityMeasure nu]
    {S : Set ((ℕ → E) × (ℕ → ℝ))} (hS : MeasurableSet S) {F : (ℕ → E) × (ℕ → ℝ) → ℝ}
    (hF : Measurable F) {C : ℝ} (h0C : 0 ≤ C) (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω in S, F ω ∂(jumpMeasure mu nu) = ∫ z, (∫ ω in S, F ω ∂(jumpKernel mu z)) ∂nu := by
  have hCind : ∀ ω, |S.indicator F ω| ≤ C := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]; exact hC ω
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact h0C
  rw [← integral_indicator hS,
    integral_jumpMeasure_eq_integral_jumpKernel mu nu (hF.indicator hS) hCind]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z ↦ integral_indicator hS)

/-- **The Markov property at a fixed time, up to the probability of `n` jumps before it.**

The initial law is universally quantified inside the statement rather than fixed as a parameter,
because that is what the induction needs: on `{T 1 ≤ s}` the construction restarts from `mu z`,
and the induction hypothesis is applied to that law and to the remaining time.

The two branches of the induction step are of a different nature.  On `{s < T 1}` there is no
error at all -- `integral_jumpKernel_add_of_lt_jumpTime_one` makes both sides of the identity
equal there -- and on `{T 1 ≤ s}` the error is the one inherited from the induction hypothesis,
whose weight is exactly the probability of a further `n` jumps in the remaining time.  Adding the
first jump to those `n` gives the set `{T (n+1) ≤ s}` of the conclusion, and the inclusion
`{T 1 ≤ s} ∩ {T (n+1) ≤ s} ⊆ {T (n+1) ≤ s}` is all that is needed: over a bare
`[MeasurableSpace E]` the two sets are not equal, because `T n ∘ jumpShift` is only almost surely
nonnegative. -/
theorem abs_integral_jumpMeasure_add_sub_le {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∀ nu : Measure E, IsProbabilityMeasure nu → ∀ s : ℝ, 0 ≤ s →
      |(∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
          - ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)|
        ≤ 2 * C * (jumpMeasure mu nu).real {ω | jumpTime lam ω.1 ω.2 n ≤ s} := by
  classical
  have hCnonneg : ∀ nu : Measure E, IsProbabilityMeasure nu → 0 ≤ C := by
    intro nu hnu
    have := hnu
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  induction n with
  | zero =>
      intro nu hnu s hs
      have := hnu
      have hset : {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 0 ≤ s} = Set.univ := by
        ext ω
        simp [jumpTime_zero, hs]
      rw [hset, probReal_univ, mul_one]
      calc |(∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
              - ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)|
          ≤ |∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu)|
              + |∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)| :=
            abs_sub _ _
        _ ≤ C + C := add_le_add (abs_integral_le_of_abs_le fun ω ↦ hC _)
            (abs_integral_le_of_abs_le fun ω ↦ abs_jumpSemigroup_le mu hC t _)
        _ = 2 * C := by ring
  | succ n ih =>
      intro nu hnu s hs
      have := hnu
      have h0C : 0 ≤ C := hCnonneg nu hnu
      have hS : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1} :=
        measurableSet_lt measurable_const (measurable_jumpTime hlam 1)
      have hAm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam r ω) :=
        fun r ↦ hh.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
      have hBm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
          jumpSemigroup lam mu h t (jumpProcess lam r ω) :=
        fun r ↦ (measurable_jumpSemigroup mu hlam hh t).comp
          ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
      have hAi : ∀ (r : ℝ) (nu' : Measure E) (_ : IsProbabilityMeasure nu'),
          Integrable (fun ω ↦ h (jumpProcess lam r ω)) (jumpMeasure mu nu') := by
        intro r nu' hnu'
        have := hnu'
        exact integrable_of_abs_le (hAm r) fun ω ↦ hC _
      have hBi : ∀ (r : ℝ) (nu' : Measure E) (_ : IsProbabilityMeasure nu'),
          Integrable (fun ω ↦ jumpSemigroup lam mu h t (jumpProcess lam r ω))
            (jumpMeasure mu nu') := by
        intro r nu' hnu'
        have := hnu'
        exact integrable_of_abs_le (hBm r) fun ω ↦ abs_jumpSemigroup_le mu hC t _
      -- On `{s < T 1}` the two sides of the Markov property already agree.
      have hSeq : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
            h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
              jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu) := by
        rw [setIntegral_jumpMeasure_eq_integral_jumpKernel mu nu hS (hAm (s + t)) h0C
            (fun ω ↦ hC _),
          setIntegral_jumpMeasure_eq_integral_jumpKernel mu nu hS (hBm s) h0C
            (fun ω ↦ abs_jumpSemigroup_le mu hC t _)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z ↦
          integral_jumpKernel_add_of_lt_jumpTime_one mu hlam hlam0 z hh hC hs)
      have hred : (∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
            - ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}ᶜ,
              (h (jumpProcess lam (s + t) ω)
                - jumpSemigroup lam mu h t (jumpProcess lam s ω)) ∂(jumpMeasure mu nu) := by
        rw [integral_sub (hAi (s + t) nu hnu).restrict (hBi s nu hnu).restrict,
          ← integral_add_compl hS (hAi (s + t) nu hnu), ← integral_add_compl hS (hBi s nu hnu),
          hSeq]
        ring
      -- The functional of the split data, and its majorant.
      set G : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun q ↦
        if q.1.2 ≤ lam q.1.1 * s then
          h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)
            - jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)
        else 0 with hGdef
      set G' : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun q ↦
        if q.1.2 ≤ lam q.1.1 * s then
          (if jumpTime lam q.2.1 q.2.2 n ≤ s - q.1.2 / lam q.1.1 then 2 * C else 0)
        else 0 with hG'def
      have hcondm : MeasurableSet
          {q : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) | q.1.2 ≤ lam q.1.1 * s} :=
        measurableSet_le (measurable_snd.comp measurable_fst)
          ((hlam.comp (measurable_fst.comp measurable_fst)).mul measurable_const)
      have htimem : Measurable fun q : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) ↦ s - q.1.2 / lam q.1.1 :=
        measurable_const.sub ((measurable_snd.comp measurable_fst).div
          (hlam.comp (measurable_fst.comp measurable_fst)))
      have hGm : Measurable G := by
        rw [hGdef]
        refine Measurable.ite hcondm ?_ measurable_const
        exact (hh.comp ((measurable_jumpProcess hlam).comp
            ((htimem.add measurable_const).prodMk measurable_snd))).sub
          ((measurable_jumpSemigroup mu hlam hh t).comp
            ((measurable_jumpProcess hlam).comp (htimem.prodMk measurable_snd)))
      have hG'm : Measurable G' := by
        rw [hG'def]
        refine Measurable.ite hcondm ?_ measurable_const
        exact Measurable.ite (measurableSet_le
          ((measurable_jumpTime hlam n).comp measurable_snd) htimem)
          measurable_const measurable_const
      have hGb : ∀ q, |G q| ≤ 2 * C := by
        intro q
        by_cases hq : q.1.2 ≤ lam q.1.1 * s
        · simp only [hGdef, if_pos hq]
          calc |h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)
                  - jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)|
              ≤ |h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)|
                + |jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)| :=
                abs_sub _ _
            _ ≤ C + C := add_le_add (hC _) (abs_jumpSemigroup_le mu hC t _)
            _ = 2 * C := by ring
        · simp only [hGdef, if_neg hq, abs_zero]
          linarith
      have hG'b : ∀ q, |G' q| ≤ 2 * C := by
        intro q
        by_cases hq : q.1.2 ≤ lam q.1.1 * s
        · by_cases hq2 : jumpTime lam q.2.1 q.2.2 n ≤ s - q.1.2 / lam q.1.1
          · simp only [hG'def, if_pos hq, if_pos hq2]
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * C)]
          · simp only [hG'def, if_pos hq, if_neg hq2, abs_zero]
            linarith
        · simp only [hG'def, if_neg hq, abs_zero]
          linarith
      -- The first identification: the shifted functional is the integrand on `{T 1 ≤ s}`.
      have hGeq : (∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}ᶜ,
              (h (jumpProcess lam (s + t) ω)
                - jumpSemigroup lam mu h t (jumpProcess lam s ω)) ∂(jumpMeasure mu nu) := by
        rw [← integral_indicator hS.compl]
        refine integral_congr_ae ?_
        filter_upwards [ae_exists_lt_jumpTime hL0 hlam0 hL mu nu] with ω hω
        have hiff : ω.2 0 ≤ lam (ω.1 0) * s ↔ jumpTime lam ω.1 ω.2 1 ≤ s := by
          rw [jumpTime_one, div_le_iff₀ (hlam0 _), mul_comm s (lam (ω.1 0))]
        by_cases hωS : s < jumpTime lam ω.1 ω.2 1
        · rw [Set.indicator_of_notMem (by simpa using hωS)]
          simp only [hGdef, if_neg (fun hq ↦ absurd (hiff.1 hq) (not_le.2 hωS))]
        · have hT1 : jumpTime lam ω.1 ω.2 1 ≤ s := not_lt.1 hωS
          rw [Set.indicator_of_mem (by simpa using hωS)]
          have e1 : jumpProcess lam (s + t) ω
              = jumpProcess lam ((s - ω.2 0 / lam (ω.1 0)) + t) (jumpShift ω) := by
            rw [jumpProcess_jumpShift (by linarith) (hω (s + t))]
            congr 1
            rw [jumpTime_one]
            ring
          have e2 : jumpProcess lam s ω
              = jumpProcess lam (s - ω.2 0 / lam (ω.1 0)) (jumpShift ω) := by
            rw [jumpProcess_jumpShift hT1 (hω s)]
            congr 1
            rw [jumpTime_one]
          rw [e1, e2]
          simp only [hGdef, if_pos (hiff.2 hT1)]
      -- The second identification: the majorant is the indicator of two jump time conditions.
      have hG'eq : (∫ ω, G' ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
          ≤ 2 * C * (jumpMeasure mu nu).real
              {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s} := by
        have hWm : MeasurableSet ({ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ s}
            ∩ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s}) :=
          (measurableSet_le (measurable_jumpTime hlam 1) measurable_const).inter
            (measurableSet_le (measurable_jumpTime hlam (n + 1)) measurable_const)
        have hW : (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ G' ((ω.1 0, ω.2 0), jumpShift ω))
            = ({ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ s}
                ∩ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s}).indicator
                (fun _ ↦ 2 * C) := by
          funext ω
          have hiff : ω.2 0 ≤ lam (ω.1 0) * s ↔ jumpTime lam ω.1 ω.2 1 ≤ s := by
            rw [jumpTime_one, div_le_iff₀ (hlam0 _), mul_comm s (lam (ω.1 0))]
          have hiff2 : jumpTime lam (jumpShift ω).1 (jumpShift ω).2 n
                ≤ s - ω.2 0 / lam (ω.1 0)
              ↔ jumpTime lam ω.1 ω.2 (n + 1) ≤ s := by
            rw [show (jumpShift ω).1 = fun k ↦ ω.1 (k + 1) from rfl,
              show (jumpShift ω).2 = fun k ↦ ω.2 (k + 1) from rfl, jumpTime_jumpShift,
              ← jumpTime_one lam ω.1 ω.2, sub_le_sub_iff_right]
          by_cases h1 : jumpTime lam ω.1 ω.2 1 ≤ s
          · by_cases h2 : jumpTime lam ω.1 ω.2 (n + 1) ≤ s
            · rw [Set.indicator_of_mem (show ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) |
                  jumpTime lam ω.1 ω.2 1 ≤ s} ∩ {ω : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω.1 ω.2 (n + 1) ≤ s} from ⟨h1, h2⟩)]
              simp only [hG'def, if_pos (hiff.2 h1), if_pos (hiff2.2 h2)]
            · rw [Set.indicator_of_notMem (fun hmem ↦ h2 hmem.2)]
              simp only [hG'def, if_pos (hiff.2 h1),
                if_neg (fun hq ↦ h2 (hiff2.1 hq))]
          · rw [Set.indicator_of_notMem (fun hmem ↦ h1 hmem.1)]
            simp only [hG'def, if_neg (fun hq ↦ h1 (hiff.1 hq))]
        rw [hW, integral_indicator_const (2 * C) hWm, smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right)
          (by linarith)
      -- The estimate, on the product of the initial law and the holding time.
      have hcmp : ∀ p : E × ℝ, |∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1))|
          ≤ ∫ ω', G' (p, ω') ∂(jumpMeasure mu (mu p.1)) := by
        intro p
        by_cases hp : p.2 ≤ lam p.1 * s
        · have hs' : 0 ≤ s - p.2 / lam p.1 := by
            have h1 : p.2 / lam p.1 ≤ s :=
              (div_le_iff₀ (hlam0 p.1)).2 (by rw [mul_comm] at hp; exact hp)
            linarith
          have hL' : (∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1)))
              = (∫ ω', h (jumpProcess lam ((s - p.2 / lam p.1) + t) ω')
                    ∂(jumpMeasure mu (mu p.1)))
                - ∫ ω', jumpSemigroup lam mu h t (jumpProcess lam (s - p.2 / lam p.1) ω')
                    ∂(jumpMeasure mu (mu p.1)) := by
            rw [← integral_sub (hAi _ (mu p.1) inferInstance) (hBi _ (mu p.1) inferInstance)]
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω' ↦ ?_)
            simp only [hGdef, if_pos hp]
          have hR' : (∫ ω', G' (p, ω') ∂(jumpMeasure mu (mu p.1)))
              = 2 * C * (jumpMeasure mu (mu p.1)).real
                  {ω' : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} := by
            have hfun : (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ G' (p, ω'))
                = {ω' : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω'.1 ω'.2 n
                    ≤ s - p.2 / lam p.1}.indicator (fun _ ↦ 2 * C) := by
              funext ω'
              by_cases hq : jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1
              · rw [Set.indicator_of_mem (show ω' ∈ {ω' : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} from hq)]
                simp only [hG'def, if_pos hp, if_pos hq]
              · rw [Set.indicator_of_notMem (show ω' ∉ {ω' : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} from hq)]
                simp only [hG'def, if_pos hp, if_neg hq]
            rw [hfun, integral_indicator_const (2 * C)
              (measurableSet_le (measurable_jumpTime hlam n) measurable_const), smul_eq_mul,
              mul_comm]
          rw [hL', hR']
          exact ih (mu p.1) inferInstance _ hs'
        · have h0 : ∀ ω' : (ℕ → E) × (ℕ → ℝ), G (p, ω') = 0 := by
            intro ω'
            simp only [hGdef, if_neg hp]
          have h0' : ∀ ω' : (ℕ → E) × (ℕ → ℝ), G' (p, ω') = 0 := by
            intro ω'
            simp only [hG'def, if_neg hp]
          simp only [h0, h0', integral_zero, abs_zero, le_refl]
      have hfinal : |∫ ω, G ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)|
          ≤ ∫ ω, G' ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu) := by
        rw [integral_jumpMeasure_eq_of_split_prod mu nu hGm hGb,
          integral_jumpMeasure_eq_of_split_prod mu nu hG'm hG'b]
        calc |∫ p, (∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1))) ∂(nu.prod (expMeasure 1))|
            ≤ ∫ p, |∫ ω', G (p, ω') ∂(jumpMeasure mu (mu p.1))| ∂(nu.prod (expMeasure 1)) :=
              abs_integral_le_integral_abs
          _ ≤ ∫ p, (∫ ω', G' (p, ω') ∂(jumpMeasure mu (mu p.1))) ∂(nu.prod (expMeasure 1)) :=
              integral_mono
                (integrable_of_abs_le (measurable_integral_jumpMeasure_step mu hGm)
                  (fun p ↦ abs_integral_le_of_abs_le fun ω' ↦ hGb _)).abs
                (integrable_of_abs_le (measurable_integral_jumpMeasure_step mu hG'm)
                  (fun p ↦ abs_integral_le_of_abs_le fun ω' ↦ hG'b _)) hcmp
      rw [hred, ← hGeq]
      exact hfinal.trans hG'eq

/-- **The probability of `n` jumps before a fixed time goes to zero.**  Non explosion says that
almost every path has only finitely many jumps in `[0, s]`, and the jump times increase, so the
indicator of `{T n ≤ s}` is eventually zero along `n`; dominated convergence turns that into the
convergence of the probabilities.

The family `{T n ≤ s}` is only **almost surely** decreasing -- the jump times increase where the
waiting times are positive and nowhere else -- so the continuity of the measure from above is not
directly applicable, and the argument is run on the indicators instead. -/
theorem tendsto_measureReal_jumpTime_le {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L) (nu : Measure E)
    [IsProbabilityMeasure nu] (s : ℝ) :
    Tendsto (fun n ↦ (jumpMeasure mu nu).real {ω | jumpTime lam ω.1 ω.2 n ≤ s}) atTop (𝓝 0) := by
  have hAset : ∀ n : ℕ, MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s} :=
    fun n ↦ measurableSet_le (measurable_jumpTime hlam n) measurable_const
  have hae : ∀ᵐ ω ∂(jumpMeasure mu nu), Tendsto (fun n ↦
      {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s}.indicator (fun _ ↦ (1 : ℝ)) ω)
      atTop (𝓝 0) := by
    filter_upwards [ae_exists_lt_jumpTime hL0 hlam0 hL mu nu, ae_pos_snd_jumpMeasure mu nu]
      with ω hω hpos
    obtain ⟨N, hN⟩ := hω s
    have hmono : StrictMono (jumpTime lam ω.1 ω.2) := strictMono_jumpTime hpos hlam0
    refine tendsto_atTop_of_eventually_const (i₀ := N + 1) fun n hn ↦ ?_
    exact Set.indicator_of_notMem
      (fun hmem ↦ absurd (le_trans (hmono.monotone hn) hmem) (not_le.2 hN)) (fun _ ↦ (1 : ℝ))
  have hconv := tendsto_integral_of_dominated_convergence (μ := jumpMeasure mu nu)
    (F := fun n ω ↦ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s}.indicator
      (fun _ ↦ (1 : ℝ)) ω)
    (f := fun _ ↦ (0 : ℝ)) (bound := fun _ ↦ (1 : ℝ))
    (fun n ↦ (measurable_const.indicator (hAset n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n ↦ Filter.Eventually.of_forall fun ω ↦ by
      by_cases hm : ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s}
      · rw [Set.indicator_of_mem hm]; simp
      · rw [Set.indicator_of_notMem hm]; simp)
    hae
  simp only [integral_zero] at hconv
  refine hconv.congr fun n ↦ ?_
  rw [integral_indicator_const (1 : ℝ) (hAset n), smul_eq_mul, mul_one]

/-- **The Markov property of the jump process at a fixed time, in integrated form.**  This is the
semigroup identity `P (s + t) h = P s (P t h)` averaged over the initial law, and it is what
carries the derivative of the backward equation from `0` to an arbitrary time. -/
theorem jumpMeasure_integral_jumpProcess_add {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L) (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu)
      = ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu) := by
  have hlim : Tendsto (fun n ↦ 2 * C * (jumpMeasure mu nu).real
      {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s}) atTop (𝓝 0) := by
    simpa using (tendsto_measureReal_jumpTime_le mu hlam hlam0 hL0 hL nu s).const_mul (2 * C)
  have hzero : |(∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
      - ∫ ω, jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)| ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun n ↦
      abs_integral_jumpMeasure_add_sub_le mu hlam hlam0 hL0 hL hh hC ht n nu inferInstance s hs)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hzero)

/-- **The Markov property in the form the twenty fourth run announced it**: the law of the process
at time `s + t` is the law at time `t` of the construction restarted from the law at time `s`.
It is the statement above read through `integral_jumpSemigroup_eq`, and the detour through
`jumpSemigroup` is not avoidable -- the measure named on the right is a single measure and not a
kernel, so an induction cannot be run on this form directly. -/
theorem jumpMeasure_integral_jumpProcess_add' {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L) (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu)
      = ∫ ω, h (jumpProcess lam t ω)
          ∂(jumpMeasure mu ((jumpMeasure mu nu).map (jumpProcess lam s))) := by
  have hXm : Measurable (jumpProcess lam s (E := E)) :=
    (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)
  have : IsProbabilityMeasure ((jumpMeasure mu nu).map (jumpProcess lam s)) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  rw [jumpMeasure_integral_jumpProcess_add mu hlam hlam0 hL0 hL nu hh hC hs ht,
    integral_jumpSemigroup_eq mu ((jumpMeasure mu nu).map (jumpProcess lam s)) hlam hh hC t,
    integral_map hXm.aemeasurable
      (measurable_jumpSemigroup mu hlam hh t).aestronglyMeasurable]

end MarkovProperty

/-! ### The clock of the jump construction -/

/-- **Lebesgue measure as a clock on `ℝ≥0`.**  The index of the abstract layer needs
`[OrderBot ι]`, which `ℝ` has not, so the martingale problem of the jump process is indexed by
`ℝ≥0` and its process is `fun t ω ↦ jumpProcess lam (t : ℝ) ω`.

`ℝ≥0` carries a `MeasurableSpace` instance
(`MeasureTheory/Constructions/BorelSpace/Basic.lean:717`) but **no** `MeasureSpace` instance, so
there is no `volume` on it; Mathlib gives subtypes their measure through
`MeasureTheory.Measure.Subtype.measureSpace`, which is deliberately not an instance
(`MeasureTheory/Measure/Restrict.lean:843`).  That costs nothing here, because `Clock` carries
its measurable space and its measure as *fields* and not as instances -- which is what that
design decision was for. -/
noncomputable def lebesgueClock : Clock ℝ≥0 where
  measurableSpace := inferInstance
  q := ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).map Real.toNNReal
  measurableSet_Iic := fun _ ↦ measurableSet_Iic
  measurableSet_Iio := fun _ ↦ measurableSet_Iio
  measure_Iic_ne_top := fun t ↦ by
    rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iic,
      show Real.toNNReal ⁻¹' Set.Iic t = Set.Iic (t : ℝ) from by
        ext x; simp [Real.toNNReal_le_iff_le_coe],
      Measure.restrict_apply measurableSet_Iic]
    refine ne_top_of_le_ne_top (b := volume (Set.Icc (0 : ℝ) t)) ?_ (measure_mono ?_)
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · rintro x ⟨hx1, hx2⟩; exact ⟨hx2, hx1⟩

/-- **The compensating interval of `lebesgueClock` under the optional convention is an honest
half open interval of `ℝ≥0`.** This is what lets the four bookkeeping facts below speak of
`Set.Ioc` instead of unfolding `Clock.interval` at every step. -/
theorem lebesgueClock_interval_optional_eq (a b : ℝ≥0) :
    lebesgueClock.interval Clock.Conv.optional a b = Set.Ioc a b := by
  ext x
  simp [Clock.interval, Set.mem_diff, Set.mem_Iic, Set.mem_Ioc, not_le]

/-- The preimage of an `ℝ≥0` window under `Real.toNNReal`, intersected with the nonnegative reals
that `lebesgueClock.q` restricts to, is the corresponding real window: the fact that makes the
pushforward defining `lebesgueClock.q` computable on `Set.Ioc`. -/
theorem lebesgueClock_preimage_Ioc (a b : ℝ≥0) :
    (Real.toNNReal ⁻¹' Set.Ioc a b) ∩ Set.Ici (0 : ℝ) = Set.Ioc (a : ℝ) (b : ℝ) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage, Set.mem_Ioc,
    Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_le_iff_le_coe]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, a.coe_nonneg.trans h1.le⟩

/-- **The exact mass of a window under `lebesgueClock`.**  Unlike `measure_Iic_ne_top`, which only
bounds it, the compensator's difference over two nested windows needs the precise value. -/
theorem lebesgueClock_apply_Ioc (a b : ℝ≥0) :
    lebesgueClock.q (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
  show ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).map Real.toNNReal (Set.Ioc a b)
      = ENNReal.ofReal ((b : ℝ) - (a : ℝ))
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Ioc,
    Measure.restrict_apply (measurable_real_toNNReal measurableSet_Ioc),
    lebesgueClock_preimage_Ioc, Real.volume_Ioc]

/-- **A compensating integral over `lebesgueClock` is a genuine interval integral of `ℝ`, shifted
to start at `0`.**  This is the fourth of the four bookkeeping steps `jumpProcess_isMPSolution`
needs: it turns the outer integral of the martingale identity, which lives on `ℝ≥0` because
`mpFamily` needs `[OrderBot ι]`, into something `intervalIntegral_integral_swap` and the
fundamental theorem of calculus can consume. -/
theorem integral_lebesgueClock_Ioc {a b : ℝ≥0} (hab : a ≤ b) {F : ℝ≥0 → ℝ} (hF : Measurable F) :
    ∫ u in Set.Ioc a b, F u ∂lebesgueClock.q
      = ∫ r in (0 : ℝ)..((b : ℝ) - (a : ℝ)), F (Real.toNNReal ((a : ℝ) + r)) := by
  have hset : Set.Ici (0 : ℝ) ∩ (Real.toNNReal ⁻¹' Set.Ioc a b) = Set.Ioc (a : ℝ) (b : ℝ) := by
    rw [Set.inter_comm]; exact lebesgueClock_preimage_Ioc a b
  have h1 : ∫ u in Set.Ioc a b, F u ∂lebesgueClock.q
      = ∫ x in Set.Ici (0 : ℝ), (Set.Ioc a b).indicator F (Real.toNNReal x) ∂volume := by
    show ∫ u in Set.Ioc a b, F u
        ∂(((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).map Real.toNNReal)
      = ∫ x in Set.Ici (0 : ℝ), (Set.Ioc a b).indicator F (Real.toNNReal x) ∂volume
    rw [← integral_indicator measurableSet_Ioc,
      integral_map measurable_real_toNNReal.aemeasurable
        (hF.indicator measurableSet_Ioc).aestronglyMeasurable]
  have h2 : (Set.Ici (0 : ℝ)).indicator (fun x => (Set.Ioc a b).indicator F (Real.toNNReal x))
      = Set.indicator (Set.Ioc (a : ℝ) (b : ℝ)) (fun x => F (Real.toNNReal x)) := by
    funext x
    by_cases hmem : x ∈ Set.Ioc (a : ℝ) (b : ℝ)
    · have hx0 : x ∈ Set.Ici (0 : ℝ) := a.coe_nonneg.trans hmem.1.le
      have hxIoc : Real.toNNReal x ∈ Set.Ioc a b := by rw [← hset] at hmem; exact hmem.2
      rw [Set.indicator_of_mem hx0, Set.indicator_of_mem hxIoc, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      by_cases hx0 : x ∈ Set.Ici (0 : ℝ)
      · have hxIoc : Real.toNNReal x ∉ Set.Ioc a b := by
          intro hc; exact hmem (by rw [← hset]; exact ⟨hx0, hc⟩)
        rw [Set.indicator_of_mem hx0, Set.indicator_of_notMem hxIoc]
      · rw [Set.indicator_of_notMem hx0]
  rw [h1, ← integral_indicator measurableSet_Ici, h2, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by exact_mod_cast hab : (a : ℝ) ≤ (b : ℝ))]
  have hcomp := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := (b : ℝ) - (a : ℝ))
    (fun x => F (Real.toNNReal x)) (a : ℝ)
  simp only [add_zero, add_sub_cancel] at hcomp
  rw [← hcomp]

/-! ### The generator -/

/-- **The generator of the jump process**, `A f x = lam x * ∫ y, (f y - f x) ∂(mu x)`.  It is
`set:jumpdata` of the manuscript, and it needs no topology and no boundedness: those enter only
in the statements about it. -/
noncomputable def jumpApply (lam : E → ℝ) (mu : Kernel E E) (f : E → ℝ) (x : E) : ℝ :=
  lam x * ∫ y, (f y - f x) ∂(mu x)

/-- **The generator is bounded by `2 L` on the functions bounded by `C`.**  This is
`norm_apply_le` of the milestone, in the shape that avoids introducing a normed space of bounded
measurable functions: the hypothesis and the conclusion are pointwise bounds, and no
integrability of `f` is needed, because `norm_integral_le_of_norm_le` dominates by a constant
which is integrable for a probability measure whether `f` is or not. -/
theorem abs_jumpApply_le {lam : E → ℝ} {mu : Kernel E E} [IsMarkovKernel mu] {f : E → ℝ}
    {L C : ℝ} (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) (hf : ∀ x, |f x| ≤ C) (x : E) :
    |jumpApply lam mu f x| ≤ 2 * L * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf x)
  have hL0 : 0 ≤ L := (hlam0 x).trans (hL x)
  have hint : ‖∫ y, (f y - f x) ∂(mu x)‖ ≤ 2 * C := by
    refine (norm_integral_le_of_norm_le (μ := mu x) (f := fun y ↦ f y - f x)
      (g := fun _ ↦ 2 * C) (integrable_const _)
      (Filter.Eventually.of_forall fun y ↦ ?_)).trans ?_
    · calc ‖f y - f x‖ ≤ |f y| + |f x| := (abs_sub _ _).trans_eq rfl
        _ ≤ 2 * C := by have := hf y; have := hf x; linarith
    · simp
  calc |jumpApply lam mu f x| = |lam x| * ‖∫ y, (f y - f x) ∂(mu x)‖ := abs_mul _ _
    _ ≤ L * (2 * C) := by
        rw [abs_of_nonneg (hlam0 x)]
        exact mul_le_mul (hL x) hint (norm_nonneg _) hL0
    _ = 2 * L * C := by ring

/-! ### The operator as a relation -/

/-- **The generator as a set of pairs**, which is the shape `mpFamily` consumes: the graph of
`jumpApply` on the bounded measurable functions.  Boundedness and measurability are carried by
the *members* of the set and not by an ambient hypothesis, because `mpFamily` quantifies over
`p ∈ A` and every statement about a member has to be able to reproduce them. -/
def jumpOperator (lam : E → ℝ) (mu : Kernel E E) : Set ((E → ℝ) × (E → ℝ)) :=
  {p | Measurable p.1 ∧ (∃ C, ∀ x, |p.1 x| ≤ C) ∧ p.2 = jumpApply lam mu p.1}

theorem mem_jumpOperator {lam : E → ℝ} {mu : Kernel E E} {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : (f, jumpApply lam mu f) ∈ jumpOperator lam mu :=
  ⟨hf, ⟨C, hC⟩, rfl⟩

theorem measurable_jumpApply {lam : E → ℝ} (hlam : Measurable lam) {mu : Kernel E E}
    [IsMarkovKernel mu] {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Measurable (jumpApply lam mu f) := by
  have hb : ∀ x, ‖f x‖ ≤ C := fun x ↦ hC x
  have h1 : Measurable fun x ↦ ∫ y, f y ∂(mu x) :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (f := fun p : E × E ↦ f p.2) (hf.comp measurable_snd).stronglyMeasurable).measurable
  have h2 : (fun x ↦ ∫ y, (f y - f x) ∂(mu x)) = fun x ↦ (∫ y, f y ∂(mu x)) - f x := by
    funext x
    rw [integral_sub (Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)) (integrable_const _), integral_const]
    simp
  have h3 : Measurable fun x ↦ ∫ y, (f y - f x) ∂(mu x) := by rw [h2]; exact h1.sub hf
  exact hlam.mul h3

/-! ### The backward equation

The differentiation of the renewal equation, and the only step of `thm:jumpMP` that is analysis
rather than bookkeeping.  It is done as a **quantitative** estimate and not as a limit:
`abs_integral_jumpProcess_sub_sub_le` bounds the second order remainder of
`t \mapsto E[h(X_t)]` at `t = 0` by `4 * C * L ^ 2 * t ^ 2`, and the derivative follows from it in
a few lines.  The quantitative form is the one the general time will need, since the constant
does not mention `nu`.

Two remarks on the shape of the result, both of them corrections of what was announced.

First, the derivative is **one sided**, and it has to be.  Before the first jump the path sits at
its initial state, so `integral_jumpProcess_of_nonpos` says that
`t \mapsto E[h(X_t)]` is constant on `Set.Iic 0`; its left derivative at `0` is therefore `0`, and
`eq_zero_of_hasDerivAt_integral_jumpProcess` turns that into a theorem: a two sided
`HasDerivAt` at `0` forces `\int A h \, dnu = 0`.  The statement to prove is
`HasDerivWithinAt ... (Set.Ici 0) 0`.

Second, the renewal equation `jumpMeasure_integral_eq_renewal` is **not** what the proof
differentiates.  Differentiating it would need the measurability in `z` of its inner integral
`\int_{Ioc 0 (lam z * t)} ...`, which is not available: it is not produced by any statement of
the file, and over a bare `[MeasurableSpace E]` it would have to be built by hand.  The proof
goes one step further back, to `integral_jumpMeasure_eq_of_split`, and applies it to the
**difference** of the true integrand and its zeroth order comparison.  The difference is then a
single integral against `nu`, produced by the theorem itself, and `abs_integral_le_of_abs_le`
bounds it from a pointwise estimate alone -- no integrability of the inner integral is ever
needed. -/

/-- The distribution function of the standard exponential law, as a real number. -/
theorem expMeasure_one_real_Iic {a : ℝ} (ha : 0 ≤ a) :
    (expMeasure 1).real (Set.Iic a) = 1 - Real.exp (-a) := by
  have h := expMeasure_Ioi (r := 1) one_pos ha
  rw [one_mul] at h
  have hc : (expMeasure 1) (Set.Iic a) = 1 - ENNReal.ofReal (Real.exp (-a)) := by
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, h]
  have hle : ENNReal.ofReal (Real.exp (-a)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by linarith))
  rw [measureReal_def, hc, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_one]

/-- Reading a bounded measurable function of the initial state under `jumpMeasure`. -/
theorem integral_chain_zero_eq (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) :
    ∫ ω, h (ω.1 0) ∂(jumpMeasure mu nu) = ∫ z, h z ∂nu := by
  conv_rhs => rw [← jumpMeasure_map_chain_zero mu nu]
  exact (integral_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable
    hh.aestronglyMeasurable).symm

/-- `1 - exp (-a) ≤ a` for `0 ≤ a`. -/
theorem one_sub_exp_neg_le_self {a : ℝ} : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

theorem exp_neg_le_one_of_nonneg {a : ℝ} (ha : 0 ≤ a) : Real.exp (-a) ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-- **The probability of a jump before `t` is at most `L * t`.** -/
theorem measureReal_jumpTime_one_le {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {t : ℝ} (ht : 0 ≤ t) :
    (jumpMeasure mu nu).real {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} ≤ L * t := by
  have hdec := jumpMeasure_integral_eq_of_firstJump hlam hlam0 mu nu (h := fun _ ↦ (1 : ℝ))
    measurable_const (C := 1) (fun z ↦ by norm_num) ht
  rw [integral_const, setIntegral_const] at hdec
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at hdec
  have hexp : Integrable (fun z ↦ Real.exp (-(lam z * t))) nu :=
    integrable_of_abs_le (Real.measurable_exp.comp ((hlam.mul measurable_const).neg))
      (fun z ↦ by
        rw [abs_of_nonneg (Real.exp_pos _).le]
        exact exp_neg_le_one_of_nonneg (mul_nonneg (hlam0 z).le ht))
  have hmono : ∫ z, (1 - L * t) ∂nu ≤ ∫ z, Real.exp (-(lam z * t)) ∂nu := by
    refine integral_mono (integrable_const _) hexp (fun z ↦ ?_)
    have h1 := Real.add_one_le_exp (-(lam z * t))
    have h2 : lam z * t ≤ L * t := mul_le_mul_of_nonneg_right (hL z) ht
    linarith
  rw [integral_const] at hmono
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hmono
  rw [measureReal_def]
  linarith

/-- **The Lipschitz bound in time for a bounded functional of the jump process.**  The state can
only have moved if the first jump has happened, and that costs `L * t`; the two terms of the
first jump decomposition each pay it once. -/
theorem abs_integral_jumpProcess_sub_le {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) - ∫ z, h z ∂nu| ≤ 2 * C * L * t := by
  have h0C : 0 ≤ C := by
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  set S := {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} with hSdef
  have hS : MeasurableSet S := measurableSet_le (measurable_jumpTime hlam 1) measurable_const
  have hdec := jumpMeasure_integral_eq_of_firstJump hlam hlam0 mu nu hh hC ht
  -- the tail term
  have htail : |∫ ω in S, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)| ≤ C * (L * t) := by
    have hb := norm_setIntegral_le_of_norm_le_const
      (μ := jumpMeasure mu nu) (s := S) (f := fun ω ↦ h (jumpProcess lam t ω)) (C := C)
      (measure_lt_top _ _) (fun ω _ ↦ by simpa [Real.norm_eq_abs] using hC _)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_left
      (measureReal_jumpTime_one_le hlam hlam0 hL mu nu ht) h0C
  -- the surviving term
  have hint1 : Integrable (fun z ↦ Real.exp (-(lam z * t)) * h z) nu :=
    integrable_of_abs_le
      ((Real.measurable_exp.comp ((hlam.mul measurable_const).neg)).mul hh)
      (fun z ↦ by
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        have h1 : Real.exp (-(lam z * t)) ≤ 1 :=
          exp_neg_le_one_of_nonneg (mul_nonneg (hlam0 z).le ht)
        calc Real.exp (-(lam z * t)) * |h z| ≤ 1 * |h z| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |h z| := one_mul _
          _ ≤ C := hC z)
  have hint2 : Integrable h nu := integrable_of_abs_le hh hC
  have hhead : |(∫ z, Real.exp (-(lam z * t)) * h z ∂nu) - ∫ z, h z ∂nu| ≤ C * (L * t) := by
    rw [← integral_sub hint1 hint2]
    refine abs_integral_le_of_abs_le (fun z ↦ ?_)
    have hexp1 : Real.exp (-(lam z * t)) ≤ 1 := exp_neg_le_one_of_nonneg (mul_nonneg (hlam0 z).le ht)
    have hbound : 1 - Real.exp (-(lam z * t)) ≤ L * t := by
      have := one_sub_exp_neg_le_self (a := lam z * t)
      have h2 : lam z * t ≤ L * t := mul_le_mul_of_nonneg_right (hL z) ht
      linarith
    have hLt : (0 : ℝ) ≤ L * t := le_trans (mul_nonneg (hlam0 z).le ht)
      (mul_le_mul_of_nonneg_right (hL z) ht)
    have hrw : Real.exp (-(lam z * t)) * h z - h z
        = -((1 - Real.exp (-(lam z * t))) * h z) := by ring
    rw [hrw, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.exp (-(lam z * t)))]
    calc (1 - Real.exp (-(lam z * t))) * |h z| ≤ (L * t) * C :=
          mul_le_mul hbound (hC z) (abs_nonneg _) hLt
      _ = C * (L * t) := by ring
  rw [hdec]
  have hsplit : (∫ z, Real.exp (-(lam z * t)) * h z ∂nu)
      + (∫ ω in S, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) - ∫ z, h z ∂nu
      = ((∫ z, Real.exp (-(lam z * t)) * h z ∂nu) - ∫ z, h z ∂nu)
        + ∫ ω in S, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu) := by ring
  rw [hsplit]
  have hadd := abs_add_le ((∫ z, Real.exp (-(lam z * t)) * h z ∂nu) - ∫ z, h z ∂nu)
    (∫ ω in S, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu))
  linarith

theorem measurable_integral_kernel_apply {mu : Kernel E E} [IsMarkovKernel mu] {h : E → ℝ}
    (hh : Measurable h) : Measurable fun z ↦ ∫ y, h y ∂(mu z) :=
  (StronglyMeasurable.integral_kernel_prod_right'
    (f := fun p : E × E ↦ h p.2) (hh.comp measurable_snd).stronglyMeasurable).measurable

theorem jumpApply_eq {lam : E → ℝ} {mu : Kernel E E} [IsMarkovKernel mu] {h : E → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) (z : E) :
    jumpApply lam mu h z = lam z * ((∫ y, h y ∂(mu z)) - h z) := by
  rw [jumpApply, integral_sub (integrable_of_abs_le hh hC) (integrable_const _), integral_const]
  simp [measureReal_def]

/-- **The backward equation at second order.** -/
theorem abs_integral_jumpProcess_sub_sub_le {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) {t : ℝ} (ht : 0 ≤ t)
    (htL : L * t ≤ 1) :
    |(∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) - (∫ z, h z ∂nu)
        - t * ∫ z, jumpApply lam mu h z ∂nu| ≤ 4 * C * L ^ 2 * t ^ 2 := by
  classical
  have h0C : 0 ≤ C := by
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  have hat : ∀ z, 0 ≤ lam z * t := fun z ↦ mul_nonneg (hlam0 z).le ht
  have hatL : ∀ z, lam z * t ≤ L * t := fun z ↦ mul_le_mul_of_nonneg_right (hL z) ht
  set m : E → ℝ := fun z ↦ ∫ y, h y ∂(mu z) with hmdef
  have hmmeas : Measurable m := measurable_integral_kernel_apply hh
  have hmb : ∀ z, |m z| ≤ C := fun z ↦ abs_integral_le_of_abs_le hC
  have hmh : ∀ z, |m z - h z| ≤ 2 * C := fun z ↦ by
    have h1 := hmb z
    have h2 := hC z
    calc |m z - h z| ≤ |m z| + |h z| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hdec := jumpMeasure_integral_eq_of_firstJump hlam hlam0 mu nu hh hC ht
  set S := {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ t} with hSdef
  have hS : MeasurableSet S := measurableSet_le (measurable_jumpTime hlam 1) measurable_const
  -- the two comparison functionals
  set G1 : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun p ↦
    if p.1.2 ≤ lam p.1.1 * t then h (jumpProcess lam (t - p.1.2 / lam p.1.1) p.2) else 0
    with hG1def
  set G2 : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun p ↦
    if p.1.2 ≤ lam p.1.1 * t then h (p.2.1 0) else 0 with hG2def
  have hcond : MeasurableSet {p : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) | p.1.2 ≤ lam p.1.1 * t} :=
    measurableSet_le (measurable_snd.comp measurable_fst)
      ((hlam.comp (measurable_fst.comp measurable_fst)).mul measurable_const)
  have hG1meas : Measurable G1 := by
    rw [hG1def]
    refine Measurable.ite hcond ?_ measurable_const
    exact hh.comp ((measurable_jumpProcess hlam).comp
      ((measurable_const.sub ((measurable_snd.comp measurable_fst).div
        (hlam.comp (measurable_fst.comp measurable_fst)))).prodMk measurable_snd))
  have hG2meas : Measurable G2 := by
    rw [hG2def]
    refine Measurable.ite hcond ?_ measurable_const
    exact hh.comp ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd))
  have hG1b : ∀ p, |G1 p| ≤ C := by
    intro p
    by_cases hp : p.1.2 ≤ lam p.1.1 * t
    · simpa [hG1def, hp] using hC _
    · simpa [hG1def, hp] using h0C
  have hG2b : ∀ p, |G2 p| ≤ C := by
    intro p
    by_cases hp : p.1.2 ≤ lam p.1.1 * t
    · simpa [hG2def, hp] using hC _
    · simpa [hG2def, hp] using h0C
  have hΨ : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
      (((ω.1 0 : E), (ω.2 0 : ℝ)), jumpShift ω) :=
    (((measurable_pi_apply 0).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_pi_lambda _ fun n ↦ (measurable_pi_apply (n + 1)).comp
        measurable_fst).prodMk
       (measurable_pi_lambda _ fun n ↦ (measurable_pi_apply (n + 1)).comp measurable_snd))
  -- the first jump decomposition, rewritten through `G1`
  have key1 : ∫ ω in S, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
      = ∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu) := by
    rw [← integral_indicator hS]
    refine integral_congr_ae ?_
    filter_upwards [ae_exists_lt_jumpTime hL0 hlam0 hL mu nu] with ω hω
    by_cases hcase : jumpTime lam ω.1 ω.2 1 ≤ t
    · have hcnd : ω.2 0 ≤ lam (ω.1 0) * t := by
        rw [jumpTime_one, div_le_iff₀ (hlam0 _)] at hcase
        linarith
      rw [Set.indicator_of_mem (show ω ∈ S from hcase)]
      simp only [hG1def, if_pos hcnd]
      rw [jumpProcess_jumpShift hcase (hω t), jumpTime_one]
    · have hcnd : ¬ (ω.2 0 ≤ lam (ω.1 0) * t) := by
        intro hcon
        rw [jumpTime_one, div_le_iff₀ (hlam0 _)] at hcase
        exact hcase (by linarith)
      rw [Set.indicator_of_notMem (show ω ∉ S from hcase)]
      simp only [hG1def, if_neg hcnd]
  -- the comparison functional integrates in closed form
  have key2 : ∫ ω, G2 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)
      = ∫ z, (1 - Real.exp (-(lam z * t))) * m z ∂nu := by
    rw [integral_jumpMeasure_eq_of_split mu nu hG2meas hG2b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    have hinner : ∀ s : ℝ, (∫ ω', G2 ((z, s), ω') ∂(jumpMeasure mu (mu z)))
        = (Set.Iic (lam z * t)).indicator (fun _ ↦ m z) s := by
      intro s
      by_cases hs : s ≤ lam z * t
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hs)]
        simp only [hG2def, if_pos hs]
        exact integral_chain_zero_eq mu (mu z) hh
      · rw [Set.indicator_of_notMem (fun hmem ↦ hs (Set.mem_Iic.1 hmem))]
        simp only [hG2def, if_neg hs, integral_zero]
    simp_rw [hinner]
    rw [integral_indicator_const (m z) measurableSet_Iic,
      expMeasure_one_real_Iic (hat z), smul_eq_mul]
  -- the two functionals are quadratically close
  have key3 : |(∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
      - ∫ ω, G2 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)| ≤ 2 * C * L ^ 2 * t ^ 2 := by
    have hDb : ∀ p, |G1 p - G2 p| ≤ 2 * C := fun p ↦ by
      have h1 := hG1b p
      have h2 := hG2b p
      calc |G1 p - G2 p| ≤ |G1 p| + |G2 p| := abs_sub _ _
        _ ≤ 2 * C := by linarith
    have hsub : (∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
        - ∫ ω, G2 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)
        = ∫ ω, (G1 - G2) ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu) := by
      have hi1 : Integrable (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ G1 ((ω.1 0, ω.2 0), jumpShift ω))
          (jumpMeasure mu nu) := integrable_of_abs_le (hG1meas.comp hΨ) fun ω ↦ hG1b _
      have hi2 : Integrable (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ G2 ((ω.1 0, ω.2 0), jumpShift ω))
          (jumpMeasure mu nu) := integrable_of_abs_le (hG2meas.comp hΨ) fun ω ↦ hG2b _
      rw [← integral_sub hi1 hi2]
      rfl
    rw [hsub, integral_jumpMeasure_eq_of_split mu nu (hG1meas.sub hG2meas) hDb]
    refine abs_integral_le_of_abs_le (fun z ↦ ?_)
    set g : ℝ → ℝ := fun s ↦ ∫ ω', (G1 - G2) ((z, s), ω') ∂(jumpMeasure mu (mu z)) with hgdef
    have hpos : ∀ᵐ s ∂(expMeasure 1), (0 : ℝ) < s := by
      have hIic : (expMeasure 1) (Set.Iic (0:ℝ)) = 0 := by
        have h0 := expMeasure_Ioi (r := 1) one_pos (le_refl (0:ℝ))
        simp only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one] at h0
        rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, h0, tsub_self]
      rw [ae_iff]
      refine measure_mono_null (fun s (hs : ¬ (0 < s)) ↦ ?_) hIic
      exact Set.mem_Iic.2 (not_lt.1 hs)
    have hgb : ∀ᵐ s ∂(expMeasure 1), ‖g s‖
        ≤ (Set.Iic (lam z * t)).indicator (fun _ ↦ 2 * C * L * t) s := by
      filter_upwards [hpos] with s hs0
      by_cases hs : s ≤ lam z * t
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hs)]
        have hu : 0 ≤ t - s / lam z := by
          have h1 : s / lam z ≤ t := (div_le_iff₀ (hlam0 z)).2 (by linarith)
          linarith
        have hut : t - s / lam z ≤ t := by
          have : 0 ≤ s / lam z := div_nonneg hs0.le (hlam0 z).le
          linarith
        have hrw : (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ (G1 - G2) ((z, s), ω'))
            = fun ω' ↦ h (jumpProcess lam (t - s / lam z) ω') - h (ω'.1 0) := by
          funext ω'
          simp only [Pi.sub_apply, hG1def, hG2def, if_pos hs]
        have hia : Integrable
            (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam (t - s / lam z) ω'))
            (jumpMeasure mu (mu z)) :=
          integrable_of_abs_le (hh.comp ((measurable_jumpProcess hlam).comp
            (measurable_const.prodMk measurable_id))) fun _ ↦ hC _
        have hib : Integrable (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ h (ω'.1 0))
            (jumpMeasure mu (mu z)) :=
          integrable_of_abs_le (hh.comp ((measurable_pi_apply 0).comp measurable_fst))
            fun _ ↦ hC _
        rw [Real.norm_eq_abs, hgdef]
        simp only [hrw]
        rw [integral_sub hia hib, integral_chain_zero_eq mu (mu z) hh]
        have hA := abs_integral_jumpProcess_sub_le hlam hlam0 hL mu (mu z) hh hC hu
        have hLC : (0:ℝ) ≤ 2 * C * L := by positivity
        nlinarith [hA]
      · rw [Set.indicator_of_notMem (fun hmem ↦ hs (Set.mem_Iic.1 hmem)), hgdef]
        have hrw : (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ (G1 - G2) ((z, s), ω')) = fun _ ↦ (0:ℝ) := by
          funext ω'
          simp only [Pi.sub_apply, hG1def, hG2def, if_neg hs, sub_zero]
        simp only [hrw, integral_zero, norm_zero, le_refl]
    have hgint : Integrable
        ((Set.Iic (lam z * t)).indicator (fun _ ↦ 2 * C * L * t)) (expMeasure 1) :=
      (integrable_const _).indicator measurableSet_Iic
    have hle := norm_integral_le_of_norm_le hgint hgb
    rw [integral_indicator_const (2 * C * L * t) measurableSet_Iic,
      expMeasure_one_real_Iic (hat z), smul_eq_mul] at hle
    rw [← Real.norm_eq_abs]
    refine hle.trans ?_
    have h1 : 1 - Real.exp (-(lam z * t)) ≤ L * t :=
      le_trans (one_sub_exp_neg_le_self) (hatL z)
    have h2 : (0:ℝ) ≤ 2 * C * L * t := by positivity
    nlinarith [h1, h2]
  -- the generator in terms of `m`
  have hjA : ∫ z, jumpApply lam mu h z ∂nu = ∫ z, lam z * (m z - h z) ∂nu :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦ jumpApply_eq hh hC z)
  -- the four integrands are bounded and measurable
  have hIA : Integrable (fun z ↦ Real.exp (-(lam z * t)) * h z) nu :=
    integrable_of_abs_le
      ((Real.measurable_exp.comp ((hlam.mul measurable_const).neg)).mul hh)
      (fun z ↦ by
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        calc Real.exp (-(lam z * t)) * |h z| ≤ 1 * |h z| :=
              mul_le_mul_of_nonneg_right (exp_neg_le_one_of_nonneg (hat z)) (abs_nonneg _)
          _ = |h z| := one_mul _
          _ ≤ C := hC z)
  have hIB : Integrable (fun z ↦ (1 - Real.exp (-(lam z * t))) * m z) nu :=
    integrable_of_abs_le
      ((measurable_const.sub
        (Real.measurable_exp.comp ((hlam.mul measurable_const).neg))).mul hmmeas)
      (fun z ↦ by
        have h1 : Real.exp (-(lam z * t)) ≤ 1 := exp_neg_le_one_of_nonneg (hat z)
        have h2 : (0:ℝ) < Real.exp (-(lam z * t)) := Real.exp_pos _
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.exp (-(lam z * t)))]
        calc (1 - Real.exp (-(lam z * t))) * |m z| ≤ 1 * |m z| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ = |m z| := one_mul _
          _ ≤ C := hmb z)
  have hIC : Integrable h nu := integrable_of_abs_le hh hC
  have hID : Integrable (fun z ↦ t * (lam z * (m z - h z))) nu :=
    integrable_of_abs_le (measurable_const.mul (hlam.mul (hmmeas.sub hh)))
      (C := t * (L * (2 * C))) (fun z ↦ by
        rw [abs_mul, abs_of_nonneg ht, abs_mul, abs_of_nonneg (hlam0 z).le]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hL z) (hmh z) (abs_nonneg _) (le_trans (hlam0 z).le (hL z))) ht)
  -- the deterministic remainder
  have hΦ : (∫ z, Real.exp (-(lam z * t)) * h z ∂nu)
        + (∫ z, (1 - Real.exp (-(lam z * t))) * m z ∂nu) - (∫ z, h z ∂nu)
        - t * ∫ z, lam z * (m z - h z) ∂nu
      = ∫ z, ((1 - Real.exp (-(lam z * t))) - lam z * t) * (m z - h z) ∂nu := by
    have hIAB : Integrable (fun z ↦ Real.exp (-(lam z * t)) * h z
        + (1 - Real.exp (-(lam z * t))) * m z) nu := hIA.add hIB
    have hIABC : Integrable (fun z ↦ (Real.exp (-(lam z * t)) * h z
        + (1 - Real.exp (-(lam z * t))) * m z) - h z) nu := hIAB.sub hIC
    have e1 : (∫ z, ((1 - Real.exp (-(lam z * t))) - lam z * t) * (m z - h z) ∂nu)
        = ∫ z, ((Real.exp (-(lam z * t)) * h z + (1 - Real.exp (-(lam z * t))) * m z)
            - h z - t * (lam z * (m z - h z))) ∂nu :=
      integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by ring)
    rw [e1, integral_sub hIABC hID, integral_sub hIAB hIC, integral_add hIA hIB,
      integral_const_mul]
  have hΦb : |∫ z, ((1 - Real.exp (-(lam z * t))) - lam z * t) * (m z - h z) ∂nu|
      ≤ 2 * C * L ^ 2 * t ^ 2 := by
    refine abs_integral_le_of_abs_le fun z ↦ ?_
    have h1 : |(1 - Real.exp (-(lam z * t))) - lam z * t| ≤ (L * t) ^ 2 := by
      have hx : |(-(lam z * t))| ≤ 1 := by
        rw [abs_neg, abs_of_nonneg (hat z)]
        exact le_trans (hatL z) htL
      have hbnd := Real.abs_exp_sub_one_sub_id_le hx
      have hrw : (1 - Real.exp (-(lam z * t))) - lam z * t
          = -(Real.exp (-(lam z * t)) - 1 - (-(lam z * t))) := by ring
      rw [hrw, abs_neg]
      refine hbnd.trans ?_
      have h2 := hat z
      have h3 := hatL z
      nlinarith
    rw [abs_mul]
    calc |(1 - Real.exp (-(lam z * t))) - lam z * t| * |m z - h z| ≤ (L * t) ^ 2 * (2 * C) :=
          mul_le_mul h1 (hmh z) (abs_nonneg _) (by positivity)
      _ = 2 * C * L ^ 2 * t ^ 2 := by ring
  -- assembly
  rw [key2] at key3
  rw [hdec, key1, hjA]
  have heq : (∫ z, Real.exp (-(lam z * t)) * h z ∂nu)
        + (∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
        - (∫ z, h z ∂nu) - t * ∫ z, lam z * (m z - h z) ∂nu
      = (∫ z, ((1 - Real.exp (-(lam z * t))) - lam z * t) * (m z - h z) ∂nu)
        + ((∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
          - ∫ z, (1 - Real.exp (-(lam z * t))) * m z ∂nu) := by
    rw [← hΦ]; ring
  rw [heq]
  have hadd := abs_add_le
    (∫ z, ((1 - Real.exp (-(lam z * t))) - lam z * t) * (m z - h z) ∂nu)
    ((∫ ω, G1 ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
      - ∫ z, (1 - Real.exp (-(lam z * t))) * m z ∂nu)
  linarith

/-- **Before time zero the process has not started to move.** -/
theorem integral_jumpProcess_of_nonpos {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {t : ℝ} (ht : t ≤ 0) :
    ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu) = ∫ z, h z ∂nu := by
  have hae : (fun ω ↦ h (jumpProcess lam t ω)) =ᵐ[jumpMeasure mu nu] fun ω ↦ h (ω.1 0) := by
    filter_upwards [ae_pos_snd_jumpMeasure mu nu] with ω hω
    have h1 : t < jumpTime lam ω.1 ω.2 1 := by
      rw [jumpTime_one]
      exact lt_of_le_of_lt ht (div_pos (hω 0) (hlam0 _))
    rw [jumpProcess_of_lt_jumpTime_one h1]
  rw [integral_congr_ae hae, integral_chain_zero_eq mu nu hh]

/-- **The backward equation in differential form, at time zero.** -/
theorem jumpMeasure_hasDerivWithinAt_integral {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) :
    HasDerivWithinAt (fun t ↦ ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu))
      (∫ z, jumpApply lam mu h z ∂nu) (Set.Ici 0) 0 := by
  have h0C : 0 ≤ C := by
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  have hF0 : (∫ ω, h (jumpProcess lam 0 ω) ∂(jumpMeasure mu nu)) = ∫ z, h z ∂nu :=
    integral_jumpProcess_of_nonpos hlam0 mu nu hh (le_refl (0:ℝ))
  have hK : (0:ℝ) ≤ 4 * C * L ^ 2 := mul_nonneg (by linarith) (sq_nonneg L)
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set δ : ℝ := min (1 / L) (ε / (4 * C * L ^ 2 + 1)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε (by linarith))
  have hev : ∀ᶠ x in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), |x - 0| < δ :=
    (eventually_abs_sub_lt (0:ℝ) hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hev] with x hx0 hxδ
  have hx : (0:ℝ) ≤ x := hx0
  rw [sub_zero, abs_of_nonneg hx] at hxδ
  have hxL : L * x ≤ 1 := by
    have h1 : x ≤ 1 / L := le_of_lt (lt_of_lt_of_le hxδ (min_le_left _ _))
    calc L * x ≤ L * (1 / L) := by nlinarith
      _ = 1 := by field_simp
  have hB := abs_integral_jumpProcess_sub_sub_le hlam hlam0 hL0 hL mu nu hh hC hx hxL
  have hεx : 4 * C * L ^ 2 * x ^ 2 ≤ ε * x := by
    have h2 : x ≤ ε / (4 * C * L ^ 2 + 1) := le_of_lt (lt_of_lt_of_le hxδ (min_le_right _ _))
    have hKpos : (0:ℝ) < 4 * C * L ^ 2 + 1 := by linarith
    have h3 : (4 * C * L ^ 2 + 1) * x ≤ ε := by
      calc (4 * C * L ^ 2 + 1) * x ≤ (4 * C * L ^ 2 + 1) * (ε / (4 * C * L ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left h2 hKpos.le
        _ = ε := by field_simp
    nlinarith [hx, hK]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, smul_eq_mul, abs_of_nonneg hx, hF0]
  exact le_trans hB hεx

/-- **The two sided derivative at zero does not exist unless the generator integrates to zero.**
The path has not moved before the first jump, so the function is constant on `Set.Iic 0` and its
left derivative is `0`: `jumpMeasure_hasDerivWithinAt_integral` is one sided of necessity. -/
theorem eq_zero_of_hasDerivAt_integral_jumpProcess {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {D : ℝ}
    (hD : HasDerivAt (fun t ↦ ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) D 0) :
    D = 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hD
  have hsub : 𝓝[<] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono _ (fun x hx ↦ ne_of_lt hx)
  have hzero : ∀ᶠ x in 𝓝[<] (0:ℝ),
      slope (fun t ↦ ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) 0 x = (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field, integral_jumpProcess_of_nonpos hlam0 mu nu hh (le_of_lt hx),
      integral_jumpProcess_of_nonpos hlam0 mu nu hh (le_refl (0:ℝ)), sub_self, zero_div]
  exact tendsto_nhds_unique (hD.mono_left hsub)
    ((tendsto_congr' hzero).2 tendsto_const_nhds)

/-- **The expectation identity of the backward equation**,
`E[h (X t)] - E[h (X 0)] = ∫_0^t E[A h (X r)] dr`.

The derivative that `jumpMeasure_hasDerivWithinAt_integral` supplies is one sided and lives at
`0` only, and `eq_zero_of_hasDerivAt_integral_jumpProcess` says that a two sided one at `0` does
not exist.  The theorem of the calculus that takes exactly that much is
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`: a derivative from the right on the
open interval, continuity on the closed one, and the integrability of the derivative.

Each of the three is supplied by a statement about the construction and not by an assumption.
The derivative from the right at `r` is the derivative at `0` of the construction restarted from
the law at time `r` -- that is `jumpMeasure_integral_jumpProcess_add'`, composed with the shift
`x ↦ x - r`, which is where the Markov property is spent.  The continuity is the Lipschitz
estimate `abs_integral_jumpProcess_sub_le`, read from the law at time `a` instead of from `nu`.
And the integrability of the compensator is its bound `abs_jumpApply_le` together with the joint
measurability of `(r, ω) ↦ jumpProcess lam r ω`. -/
theorem jumpMeasure_integral_sub_eq_intervalIntegral {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)) - ∫ z, h z ∂nu
      = ∫ r in (0:ℝ)..t,
          ∫ ω, jumpApply lam mu h (jumpProcess lam r ω) ∂(jumpMeasure mu nu) := by
  have h0C : 0 ≤ C := by
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  set F : ℝ → ℝ := fun r ↦ ∫ ω, h (jumpProcess lam r ω) ∂(jumpMeasure mu nu) with hFdef
  set G : ℝ → ℝ := fun r ↦ ∫ ω, jumpApply lam mu h (jumpProcess lam r ω) ∂(jumpMeasure mu nu)
    with hGdef
  -- the law of the process at a fixed time
  set nuAt : ℝ → Measure E := fun r ↦ (jumpMeasure mu nu).map (jumpProcess lam r) with hnuAt
  have hXm : ∀ r : ℝ, Measurable (jumpProcess lam r (E := E)) :=
    fun r ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)
  have hprob : ∀ r : ℝ, IsProbabilityMeasure (nuAt r) :=
    fun r ↦ Measure.isProbabilityMeasure_map (hXm r).aemeasurable
  have hpush : ∀ (r : ℝ) (g : E → ℝ), Measurable g →
      (∫ z, g z ∂(nuAt r)) = ∫ ω, g (jumpProcess lam r ω) ∂(jumpMeasure mu nu) := by
    intro r g hg
    rw [hnuAt]
    exact integral_map (hXm r).aemeasurable hg.aestronglyMeasurable
  -- the Markov property in the shape the derivative needs
  have hshift : ∀ r u : ℝ, 0 ≤ r → 0 ≤ u →
      F (r + u) = ∫ ω, h (jumpProcess lam u ω) ∂(jumpMeasure mu (nuAt r)) := by
    intro r u hr hu
    have := hprob r
    exact jumpMeasure_integral_jumpProcess_add' mu hlam hlam0 hL0 hL nu hh hC hr hu
  -- the derivative from the right, at every nonnegative time
  have hderiv : ∀ r : ℝ, 0 ≤ r → HasDerivWithinAt F (G r) (Set.Ici r) r := by
    intro r hr
    have hpr := hprob r
    have hbase := jumpMeasure_hasDerivWithinAt_integral hlam hlam0 hL0 hL mu (nuAt r) hh hC
    have hsub : HasDerivWithinAt (fun x : ℝ ↦ x - r) 1 (Set.Ici r) r :=
      (hasDerivWithinAt_id r (Set.Ici r)).sub_const r
    have hmaps : Set.MapsTo (fun x : ℝ ↦ x - r) (Set.Ici r) (Set.Ici 0) := by
      intro x hx
      simpa using sub_nonneg.2 (Set.mem_Ici.1 hx)
    have hbase' : HasDerivWithinAt
        (fun u ↦ ∫ ω, h (jumpProcess lam u ω) ∂(jumpMeasure mu (nuAt r)))
        (∫ z, jumpApply lam mu h z ∂(nuAt r)) (Set.Ici 0) ((fun x : ℝ ↦ x - r) r) := by
      simpa using hbase
    have hcomp := HasDerivWithinAt.comp (h := fun x : ℝ ↦ x - r) r hbase' hsub hmaps
    rw [mul_one] at hcomp
    have hval : ∀ x ∈ Set.Ici r, F x = ((fun u ↦ ∫ ω, h (jumpProcess lam u ω)
        ∂(jumpMeasure mu (nuAt r))) ∘ fun x : ℝ ↦ x - r) x := by
      intro x hx
      have hx' : 0 ≤ x - r := sub_nonneg.2 hx
      show F x = ∫ ω, h (jumpProcess lam (x - r) ω) ∂(jumpMeasure mu (nuAt r))
      rw [← hshift r (x - r) hr hx']
      congr 1
      ring
    have hgoal := hcomp.congr hval (hval r (Set.mem_Ici.2 (le_refl r)))
    have hGr : (∫ z, jumpApply lam mu h z ∂(nuAt r)) = G r :=
      hpush r _ (measurable_jumpApply hlam hh hC)
    rwa [hGr] at hgoal
  -- the Lipschitz estimate, hence continuity
  have hlip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |F b - F a| ≤ 2 * C * L * (b - a) := by
    intro a b ha hab
    have hpa := hprob a
    have hkey := abs_integral_jumpProcess_sub_le hlam hlam0 hL mu (nuAt a) hh hC
      (t := b - a) (sub_nonneg.2 hab)
    rwa [← hshift a (b - a) ha (sub_nonneg.2 hab), add_sub_cancel, hpush a h hh] at hkey
  have hK : (0:ℝ) ≤ 2 * C * L := by positivity
  have hcont : ContinuousOn F (Set.Icc 0 t) := by
    intro a ha
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (2 * C * L + 1), by positivity, fun {b} hb hd ↦ ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have hden : (0:ℝ) < 2 * C * L + 1 := by linarith
    rcases le_total a b with hab | hab
    · have h1 := hlip a b ha.1 hab
      have h2 : b - a < ε / (2 * C * L + 1) := by
        rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
        exact hd
      have h3 : (b - a) * (2 * C * L + 1) < ε := (lt_div_iff₀ hden).1 h2
      nlinarith [abs_nonneg (F b - F a)]
    · have h1 := hlip b a hb.1 hab
      have h2 : a - b < ε / (2 * C * L + 1) := by
        rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b), abs_sub_comm]
        exact hd
      have h3 : (a - b) * (2 * C * L + 1) < ε := (lt_div_iff₀ hden).1 h2
      rw [abs_sub_comm]
      nlinarith [abs_nonneg (F a - F b)]
  -- the integrability of the compensator
  have hGm : Measurable G := by
    have hf : Measurable fun p : ℝ × ((ℕ → E) × (ℕ → ℝ)) ↦
        jumpApply lam mu h (jumpProcess lam p.1 p.2) :=
      (measurable_jumpApply hlam hh hC).comp (measurable_jumpProcess hlam)
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := jumpMeasure mu nu)).measurable
  have hGb : ∀ r : ℝ, ‖G r‖ ≤ 2 * L * C := by
    intro r
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_abs_le fun ω ↦ abs_jumpApply_le (fun x ↦ (hlam0 x).le) hL hC _
  have hGint : IntervalIntegrable G volume 0 t := by
    have hfin : volume (Set.uIoc (0:ℝ) t) ≠ ⊤ := by
      simp [Set.uIoc]
    rw [intervalIntegrable_iff]
    exact integrableOn_of_bounded volume hfin hGm hGb
  have hF0 : F 0 = ∫ z, h z ∂nu :=
    integral_jumpProcess_of_nonpos hlam0 mu nu hh (le_refl (0:ℝ))
  rw [← hF0]
  exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hcont
    (fun x hx ↦ (hderiv x (le_of_lt hx.1)).mono Set.Ioi_subset_Ici_self) hGint).symm

/-! ## Non explosion as a set -/

/-- **The non explosive sample points**, as a set rather than as an almost sure statement.  It is
needed as a set because the identities that carry the past through the restart are *false* on the
explosion set: there `stepIndex` is the junk value `0` and the path sits at the initial state of
whatever data it is read from. -/
def NonExplosive (lam : E → ℝ) : Set ((ℕ → E) × (ℕ → ℝ)) :=
  {ω | ∀ t : ℝ, ∃ n, t < jumpTime lam ω.1 ω.2 (n + 1)}

theorem measurableSet_nonExplosive {lam : E → ℝ} (hlam : Measurable lam) :
    MeasurableSet (NonExplosive lam) := by
  have hEq : NonExplosive lam
      = ⋂ m : ℕ, ⋃ n : ℕ, {ω : (ℕ → E) × (ℕ → ℝ) | (m : ℝ) < jumpTime lam ω.1 ω.2 (n + 1)} := by
    ext ω
    simp only [NonExplosive, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    refine ⟨fun h m ↦ h m, fun h t ↦ ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_gt t
    obtain ⟨n, hn⟩ := h m
    exact ⟨n, hm.trans hn⟩
  rw [hEq]
  exact MeasurableSet.iInter fun m ↦ MeasurableSet.iUnion fun n ↦
    measurableSet_lt measurable_const (measurable_jumpTime hlam (n + 1))

/-- **Almost every sample point is non explosive**, which is `ae_exists_lt_jumpTime` read as a
statement about the set.  The set and the almost sure statement are both needed and they are not
interchangeable: the identities of the past hold *pointwise* on the set, and it is the set that
survives the restart. -/
theorem ae_mem_nonExplosive {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L) (hlam0 : ∀ x, 0 < lam x)
    (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] : ∀ᵐ ω ∂(jumpMeasure mu nu), ω ∈ NonExplosive lam :=
  ae_exists_lt_jumpTime hL0 hlam0 hL mu nu

/-- **Cutting a functional down to the non explosive sample points changes no integral.**  This is
the price of `IsPastFunctional`, and it is nil. -/
theorem indicator_nonExplosive_ae_eq {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L) (hlam0 : ∀ x, 0 < lam x)
    (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E)
    [IsProbabilityMeasure nu] (G : (ℕ → E) × (ℕ → ℝ) → ℝ) :
    (NonExplosive lam).indicator G =ᵐ[jumpMeasure mu nu] G := by
  filter_upwards [ae_mem_nonExplosive hL0 hlam0 hL mu nu] with ω hω
  exact Set.indicator_of_mem hω G

/-! ## The two canonical substitutions -/

/-- **The datum that sits at `x` and does not jump before `s`.**  It is the canonical
representative of the past on the event `{s < T 1}`, and it is what makes a functional of the past
a function of the initial state there. -/
def jumpConst (lam : E → ℝ) (s : ℝ) (x : E) : (ℕ → E) × (ℕ → ℝ) :=
  (fun _ ↦ x, fun _ ↦ lam x * s + 1)

theorem measurable_jumpConst {lam : E → ℝ} (hlam : Measurable lam) (s : ℝ) :
    Measurable (jumpConst lam s : E → (ℕ → E) × (ℕ → ℝ)) :=
  (measurable_pi_lambda _ fun _ ↦ measurable_id).prodMk
    (measurable_pi_lambda _ fun _ ↦ (hlam.mul measurable_const).add measurable_const)

omit [MeasurableSpace E] in
theorem jumpTime_jumpConst (lam : E → ℝ) (s : ℝ) (x : E) (n : ℕ) :
    jumpTime lam (jumpConst lam s x).1 (jumpConst lam s x).2 n
      = n * ((lam x * s + 1) / lam x) := by
  induction n with
  | zero => simp [jumpTime_zero]
  | succ n ih =>
      rw [jumpTime_succ, ih]
      show (n : ℝ) * ((lam x * s + 1) / lam x) + (lam x * s + 1) / lam x = _
      push_cast
      ring

omit [MeasurableSpace E] in
theorem lt_jumpTime_one_jumpConst {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x) (s : ℝ)
    (x : E) : s < jumpTime lam (jumpConst lam s x).1 (jumpConst lam s x).2 1 := by
  rw [jumpTime_jumpConst lam s x 1, Nat.cast_one, one_mul, lt_div_iff₀ (hlam0 x)]
  nlinarith [hlam0 x]

omit [MeasurableSpace E] in
theorem jumpConst_mem_nonExplosive {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x) {s : ℝ} (hs : 0 ≤ s)
    (x : E) : jumpConst lam s x ∈ NonExplosive lam := by
  intro t
  have hd : 0 < (lam x * s + 1) / lam x := div_pos (by nlinarith [hlam0 x]) (hlam0 x)
  obtain ⟨n, hn⟩ := exists_nat_gt (t / ((lam x * s + 1) / lam x))
  refine ⟨n, ?_⟩
  rw [jumpTime_jumpConst lam s x (n + 1)]
  have h1 : t < (n : ℝ) * ((lam x * s + 1) / lam x) := (div_lt_iff₀ hd).1 hn
  push_cast
  nlinarith

theorem jumpProcess_jumpConst {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x) {s r : ℝ}
    (hr : r ≤ s) (x : E) : jumpProcess lam r (jumpConst lam s x) = x :=
  jumpProcess_of_lt_jumpTime_one (lt_of_le_of_lt hr (lt_jumpTime_one_jumpConst hlam0 s x))

/-- **Prepending a state and a waiting time to the driving data.**  It is the inverse of
`jumpShift`, and it is the change of variables in which the splitting of `jumpMeasure` at the
first jump reads the functionals of the past. -/
def jumpPrepend (x : E) (a : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) : (ℕ → E) × (ℕ → ℝ) :=
  (natCons (x, ω.1), natCons (a, ω.2))

theorem measurable_jumpPrepend :
    Measurable fun p : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) ↦ jumpPrepend p.1.1 p.1.2 p.2 :=
  (measurable_natCons.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).prodMk
    (measurable_natCons.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)))

omit [MeasurableSpace E] in
theorem jumpShift_jumpPrepend (x : E) (a : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) :
    jumpShift (jumpPrepend x a ω) = ω := by
  refine Prod.ext ?_ ?_ <;> funext n <;> simp [jumpShift, jumpPrepend, natCons]

omit [MeasurableSpace E] in
theorem jumpPrepend_self (ω : (ℕ → E) × (ℕ → ℝ)) :
    jumpPrepend (ω.1 0) (ω.2 0) (jumpShift ω) = ω := by
  refine Prod.ext ?_ ?_ <;> funext n <;> rcases n with _ | n <;>
    simp [jumpShift, jumpPrepend, natCons]

omit [MeasurableSpace E] in
theorem jumpTime_jumpPrepend (lam : E → ℝ) (x : E) (a : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) (n : ℕ) :
    jumpTime lam (jumpPrepend x a ω).1 (jumpPrepend x a ω).2 (n + 1)
      = a / lam x + jumpTime lam ω.1 ω.2 n := by
  induction n with
  | zero =>
      rw [jumpTime_succ, jumpTime_zero, jumpTime_zero, zero_add, add_zero]
      rfl
  | succ n ih =>
      rw [jumpTime_succ, ih, jumpTime_succ lam ω.1 ω.2 n]
      have h1 : (jumpPrepend x a ω).2 (n + 1) = ω.2 n := by simp [jumpPrepend, natCons]
      have h2 : (jumpPrepend x a ω).1 (n + 1) = ω.1 n := by simp [jumpPrepend, natCons]
      rw [h1, h2, add_assoc]

omit [MeasurableSpace E] in
theorem jumpTime_one_jumpPrepend (lam : E → ℝ) (x : E) (a : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) :
    jumpTime lam (jumpPrepend x a ω).1 (jumpPrepend x a ω).2 1 = a / lam x := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, jumpTime_jumpPrepend, jumpTime_zero, add_zero]

theorem jumpPrepend_mem_nonExplosive_iff {lam : E → ℝ} (x : E) (a : ℝ)
    (ω : (ℕ → E) × (ℕ → ℝ)) :
    jumpPrepend x a ω ∈ NonExplosive lam ↔ ω ∈ NonExplosive lam := by
  constructor
  · intro h t
    obtain ⟨n, hn⟩ := h (a / lam x + max t 0)
    rcases n with _ | n
    · rw [jumpTime_one_jumpPrepend] at hn
      exact absurd (le_max_right t 0) (by linarith)
    · refine ⟨n, ?_⟩
      rw [jumpTime_jumpPrepend] at hn
      exact lt_of_le_of_lt (le_max_left t 0) (by linarith)
  · intro h t
    obtain ⟨n, hn⟩ := h (t - a / lam x)
    refine ⟨n + 1, ?_⟩
    rw [jumpTime_jumpPrepend]
    linarith

/-- **The path of the prepended datum**: before `a / lam x` it sits at `x`, and afterwards it is
the path of `ω` moved forward by `a / lam x`.  Non explosion is not decoration -- past the
explosion time the left hand side is `x` and the right hand side is `ω.1 0`. -/
theorem jumpProcess_jumpPrepend {lam : E → ℝ} {x : E} {a : ℝ} {ω : (ℕ → E) × (ℕ → ℝ)}
    (hω : ω ∈ NonExplosive lam) (r : ℝ) :
    jumpProcess lam r (jumpPrepend x a ω)
      = if r < a / lam x then x else jumpProcess lam (r - a / lam x) ω := by
  by_cases hr : r < a / lam x
  · rw [if_pos hr, jumpProcess_of_lt_jumpTime_one (by rwa [jumpTime_one_jumpPrepend])]
    rfl
  · rw [if_neg hr]
    have hex : ∃ n, r < jumpTime lam (jumpPrepend x a ω).1 (jumpPrepend x a ω).2 (n + 1) :=
      (jumpPrepend_mem_nonExplosive_iff x a ω).2 hω r
    rw [jumpProcess_jumpShift (by rw [jumpTime_one_jumpPrepend]; exact not_lt.1 hr) hex,
      jumpTime_one_jumpPrepend, jumpShift_jumpPrepend]

/-! ## Functionals of the past -/

/-- **A functional of the past, in the form the induction of the Markov property preserves.**
It is the conclusion of `eq_of_measurable_naturalFiltration` taken as a hypothesis, restricted to
the non explosive sample points and vanishing off them.

The restriction is what makes the notion survive the restart: `jumpProcess_jumpPrepend` -- the
identity that turns a functional of the past of the prepended datum into one of the past of the
datum itself -- is false on the explosion set. -/
def IsPastFunctional (lam : E → ℝ) (s : ℝ) (G : (ℕ → E) × (ℕ → ℝ) → ℝ) : Prop :=
  (∀ ω ∉ NonExplosive lam, G ω = 0) ∧
    ∀ ω ∈ NonExplosive lam, ∀ ω' ∈ NonExplosive lam,
      (∀ r, 0 ≤ r → r ≤ s → jumpProcess lam r ω = jumpProcess lam r ω') → G ω = G ω'

/-- **On the event that the first jump has not happened, a functional of the past is a function of
the initial state**, namely of its value at the canonical datum `jumpConst`. -/
theorem eq_jumpConst_of_isPastFunctional {lam : E → ℝ} (hlam0 : ∀ x, 0 < lam x) {s : ℝ}
    (hs : 0 ≤ s) {G : (ℕ → E) × (ℕ → ℝ) → ℝ} (hG : IsPastFunctional lam s G)
    {ω : (ℕ → E) × (ℕ → ℝ)} (hω : ω ∈ NonExplosive lam)
    (h1 : s < jumpTime lam ω.1 ω.2 1) :
    G ω = G (jumpConst lam s (ω.1 0)) := by
  refine hG.2 ω hω _ (jumpConst_mem_nonExplosive hlam0 hs _) fun r hr0 hr ↦ ?_
  rw [jumpProcess_of_lt_jumpTime_one (lt_of_le_of_lt hr h1),
    jumpProcess_jumpConst hlam0 hr]

/-- **A functional of the past restarts as a functional of the past.**  The horizon drops by the
first jump time, and this is the step that lets the induction of the Markov property be applied to
the shifted data. -/
theorem IsPastFunctional.comp_jumpPrepend {lam : E → ℝ} {s : ℝ}
    {G : (ℕ → E) × (ℕ → ℝ) → ℝ} (hG : IsPastFunctional lam s G) (x : E) (a : ℝ) :
    IsPastFunctional lam (s - a / lam x) fun ω ↦ G (jumpPrepend x a ω) := by
  refine ⟨fun ω hω ↦ hG.1 _ fun hmem ↦ hω ((jumpPrepend_mem_nonExplosive_iff x a ω).1 hmem),
    fun ω hω ω' hω' hpath ↦ ?_⟩
  refine hG.2 _ ((jumpPrepend_mem_nonExplosive_iff x a ω).2 hω)
    _ ((jumpPrepend_mem_nonExplosive_iff x a ω').2 hω') fun r hr0 hr ↦ ?_
  rw [jumpProcess_jumpPrepend hω, jumpProcess_jumpPrepend hω']
  by_cases hlt : r < a / lam x
  · rw [if_pos hlt, if_pos hlt]
  · rw [if_neg hlt, if_neg hlt]
    exact hpath _ (by linarith [not_lt.1 hlt]) (by linarith)

/-- **The canonical representative of the past is measurable in the initial state.** -/
theorem measurable_comp_jumpConst {lam : E → ℝ} (hlam : Measurable lam) (s : ℝ)
    {G : (ℕ → E) × (ℕ → ℝ) → ℝ} (hG : Measurable G) :
    Measurable fun x : E ↦ G (jumpConst lam s x) :=
  hG.comp (measurable_jumpConst hlam s)


/-! ## The Markov property with a factor from the past

The conditional expectation of the jump martingale problem is an identity between integrals
against the bounded `𝓕 s`-measurable functionals, and the induction that proves it is
`abs_integral_jumpMeasure_add_sub_le` carrying such a functional along.  Two of its steps are new
and neither of them is bookkeeping: on `{s < T 1}` the functional is a function of the initial
state (`eq_jumpConst_of_isPastFunctional`), which is what lets `integral_jumpKernel_zero_eq` pull
it out of the integral against `jumpKernel mu z`; and on `{T 1 ≤ s}` it restarts as a functional of
the past of the shifted data (`IsPastFunctional.comp_jumpPrepend`), which is what the induction
hypothesis is applied to. -/

section ConditionalMarkov

variable (mu : Kernel E E) [IsMarkovKernel mu]

/-- The waiting times of the construction started at a fixed state have the law `waitingMeasure`;
the kernel counterpart of `jumpMeasure_map_snd`. -/
theorem jumpKernel_map_snd (z : E) : (jumpKernel mu z).map Prod.snd = waitingMeasure := by
  rw [jumpKernel_apply mu z, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Almost every sample point of `jumpKernel mu z` is non explosive.**  The kernel counterpart of
`ae_mem_nonExplosive`, and it is the form the first branch of the induction needs: the
identification of a functional of the past with a function of the initial state holds only off the
explosion set, and that branch is run under the kernel and not under a fixed initial law. -/
theorem ae_mem_nonExplosive_jumpKernel {lam : E → ℝ} {L : ℝ} (hL0 : 0 < L)
    (hlam : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (z : E) :
    ∀ᵐ ω ∂(jumpKernel mu z), ω ∈ NonExplosive lam := by
  have h : ∀ᵐ ω ∂(jumpKernel mu z), (∀ n, 0 < ω.2 n) ∧
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ω.2 k) atTop atTop := by
    refine ae_of_ae_map (f := fun ω : (ℕ → E) × (ℕ → ℝ) ↦ ω.2)
      (p := fun xi : ℕ → ℝ ↦ (∀ n, 0 < xi n) ∧
        Tendsto (fun n ↦ ∑ k ∈ Finset.range n, xi k) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [jumpKernel_map_snd mu z]
    exact ae_pos_waiting.and tendsto_sum_waiting_atTop
  filter_upwards [h] with ω hω
  show ∀ t : ℝ, ∃ n, t < jumpTime lam ω.1 ω.2 (n + 1)
  exact fun s ↦ exists_lt_succ_of_tendsto_atTop
    (tendsto_jumpTime_atTop (y := ω.1) (xi := ω.2) hL0 hlam hL (fun n ↦ (hω.1 n).le) hω.2) s

/-- **The Markov property at a fixed time with a factor from the past.** -/
theorem abs_integral_jumpMeasure_add_sub_le_past {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L)
    {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∀ nu : Measure E, IsProbabilityMeasure nu → ∀ s : ℝ, 0 ≤ s →
      ∀ G : (ℕ → E) × (ℕ → ℝ) → ℝ, Measurable G → (∀ ω, |G ω| ≤ 1) →
        IsPastFunctional lam s G →
      |(∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
          - ∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)|
        ≤ 2 * C * (jumpMeasure mu nu).real {ω | jumpTime lam ω.1 ω.2 n ≤ s} := by
  classical
  have hCnonneg : ∀ nu : Measure E, IsProbabilityMeasure nu → 0 ≤ C := by
    intro nu hnu
    have := hnu
    rcases isEmpty_or_nonempty E with hE | hne
    · exact absurd (measure_univ (μ := nu)) (by simp [Set.univ_eq_empty_iff.2 hE])
    · exact (abs_nonneg (h (Classical.arbitrary E))).trans (hC _)
  induction n with
  | zero =>
      intro nu hnu s hs G hGm hGb hGp
      have := hnu
      have h0C : 0 ≤ C := hCnonneg nu hnu
      have hset : {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 0 ≤ s} = Set.univ := by
        ext ω
        simp [jumpTime_zero, hs]
      rw [hset, probReal_univ, mul_one]
      calc |(∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
              - ∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)|
          ≤ |∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu)|
              + |∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω)
                  ∂(jumpMeasure mu nu)| := abs_sub _ _
        _ ≤ C + C := by
            refine add_le_add (abs_integral_le_of_abs_le fun ω ↦ ?_)
              (abs_integral_le_of_abs_le fun ω ↦ ?_)
            · rw [abs_mul]
              calc |G ω| * |h (jumpProcess lam (s + t) ω)|
                  ≤ 1 * C := mul_le_mul (hGb ω) (hC _) (abs_nonneg _) zero_le_one
                _ = C := one_mul C
            · rw [abs_mul]
              calc |G ω| * |jumpSemigroup lam mu h t (jumpProcess lam s ω)|
                  ≤ 1 * C := mul_le_mul (hGb ω) (abs_jumpSemigroup_le mu hC t _)
                    (abs_nonneg _) zero_le_one
                _ = C := one_mul C
        _ = 2 * C := by ring
  | succ n ih =>
      intro nu hnu s hs G hGm hGb hGp
      have := hnu
      have h0C : 0 ≤ C := hCnonneg nu hnu
      have hS : MeasurableSet {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1} :=
        measurableSet_lt measurable_const (measurable_jumpTime hlam 1)
      have hAm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ h (jumpProcess lam r ω) :=
        fun r ↦ hh.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
      have hBm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
          jumpSemigroup lam mu h t (jumpProcess lam r ω) :=
        fun r ↦ (measurable_jumpSemigroup mu hlam hh t).comp
          ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
      have hGAm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
          G ω * h (jumpProcess lam r ω) := fun r ↦ hGm.mul (hAm r)
      have hGBm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
          G ω * jumpSemigroup lam mu h t (jumpProcess lam r ω) := fun r ↦ hGm.mul (hBm r)
      -- the two integrands, with the factor from the past
      have hAb : ∀ (K : (ℕ → E) × (ℕ → ℝ) → ℝ), (∀ ω, |K ω| ≤ 1) → ∀ (f : (ℕ → E) × (ℕ → ℝ) → ℝ),
          (∀ ω, |f ω| ≤ C) → ∀ ω, |K ω * f ω| ≤ C := by
        intro K hK f hf ω
        rw [abs_mul]
        calc |K ω| * |f ω| ≤ 1 * C := mul_le_mul (hK ω) (hf ω) (abs_nonneg _) zero_le_one
          _ = C := one_mul C
      have hAi : ∀ (r : ℝ) (nu' : Measure E) (_ : IsProbabilityMeasure nu')
          (K : (ℕ → E) × (ℕ → ℝ) → ℝ), Measurable K → (∀ ω, |K ω| ≤ 1) →
          Integrable (fun ω ↦ K ω * h (jumpProcess lam r ω)) (jumpMeasure mu nu') := by
        intro r nu' hnu' K hKm hKb
        have := hnu'
        exact integrable_of_abs_le (hKm.mul (hAm r)) (hAb K hKb _ (fun ω ↦ hC _))
      have hBi : ∀ (r : ℝ) (nu' : Measure E) (_ : IsProbabilityMeasure nu')
          (K : (ℕ → E) × (ℕ → ℝ) → ℝ), Measurable K → (∀ ω, |K ω| ≤ 1) →
          Integrable (fun ω ↦ K ω * jumpSemigroup lam mu h t (jumpProcess lam r ω))
            (jumpMeasure mu nu') := by
        intro r nu' hnu' K hKm hKb
        have := hnu'
        exact integrable_of_abs_le (hKm.mul (hBm r))
          (hAb K hKb _ (fun ω ↦ abs_jumpSemigroup_le mu hC t _))
      -- On `{s < T 1}` the past functional is a function of the initial state, and the two
      -- sides of the Markov property agree there.
      set Ψ : E → ℝ := fun x ↦ G (jumpConst lam s x) with hΨdef
      have hΨm : Measurable Ψ := hGm.comp (measurable_jumpConst hlam s)
      have hΨb : ∀ x, |Ψ x| ≤ 1 := fun x ↦ hGb _
      have hpull : ∀ (z : E) (f : (ℕ → E) × (ℕ → ℝ) → ℝ), Measurable f → (∀ ω, |f ω| ≤ C) →
          (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}, G ω * f ω
              ∂(jumpKernel mu z))
            = Ψ z * ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}, f ω
                ∂(jumpKernel mu z) := by
        intro z f hfm hfb
        have hstep1 : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}, G ω * f ω
              ∂(jumpKernel mu z))
            = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}, Ψ (ω.1 0) * f ω
                ∂(jumpKernel mu z) := by
          refine setIntegral_congr_ae hS ?_
          filter_upwards [ae_mem_nonExplosive_jumpKernel mu hL0 hlam0 hL z] with ω hω hmem
          rw [eq_jumpConst_of_isPastFunctional hlam0 hs hGp hω hmem]
        set F : E × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun p ↦ Ψ p.1 *
          ({ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator f p.2) with hFdef
        have hFm : Measurable F :=
          (hΨm.comp measurable_fst).mul ((hfm.indicator hS).comp measurable_snd)
        have hindb : ∀ ω : (ℕ → E) × (ℕ → ℝ),
            |{ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator f ω| ≤ C := by
          intro ω
          by_cases hmem : ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}
          · rw [Set.indicator_of_mem hmem]; exact hfb ω
          · rw [Set.indicator_of_notMem hmem, abs_zero]; exact h0C
        have hFb : ∀ p, |F p| ≤ C := by
          intro p
          have hFp : F p = Ψ p.1 *
              {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator f p.2 := by
            rw [hFdef]
          rw [hFp, abs_mul]
          calc |Ψ p.1| * |{ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator f p.2|
              ≤ 1 * C := mul_le_mul (hΨb _) (hindb _) (abs_nonneg _) zero_le_one
            _ = C := one_mul C
        have hFapp : ∀ (x : E) (ω : (ℕ → E) × (ℕ → ℝ)), F (x, ω) = Ψ x *
            {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator f ω := by
          intro x ω
          rw [hFdef]
        have hind : ∀ (x : E) (ω : (ℕ → E) × (ℕ → ℝ)),
            {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}.indicator
              (fun ω ↦ Ψ x * f ω) ω = F (x, ω) := by
          intro x ω
          rw [hFapp]
          by_cases hmem : ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}
          · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
          · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
        have hstep2 : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
              Ψ (ω.1 0) * f ω ∂(jumpKernel mu z))
            = ∫ ω, F (ω.1 0, ω) ∂(jumpKernel mu z) := by
          rw [← integral_indicator hS]
          exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ hind (ω.1 0) ω)
        have hstep3 : (∫ ω, F (z, ω) ∂(jumpKernel mu z))
            = Ψ z * ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}, f ω
                ∂(jumpKernel mu z) := by
          simp only [hFapp]
          rw [integral_const_mul, integral_indicator hS]
        rw [hstep1, hstep2, integral_jumpKernel_zero_eq mu hFm hFb z, hstep3]
      have hSeq : (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
            G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
              G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu) := by
        rw [setIntegral_jumpMeasure_eq_integral_jumpKernel mu nu hS (hGAm (s + t)) h0C
            (hAb G hGb _ fun ω ↦ hC _),
          setIntegral_jumpMeasure_eq_integral_jumpKernel mu nu hS (hGBm s) h0C
            (hAb G hGb _ fun ω ↦ abs_jumpSemigroup_le mu hC t _)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
        show (∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
              G ω * h (jumpProcess lam (s + t) ω) ∂(jumpKernel mu z))
            = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1},
                G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpKernel mu z)
        rw [hpull z _ (hAm (s + t)) (fun ω ↦ hC _),
          hpull z _ (hBm s) (fun ω ↦ abs_jumpSemigroup_le mu hC t _),
          integral_jumpKernel_add_of_lt_jumpTime_one mu hlam hlam0 z hh hC hs]
      have hred : (∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
            - ∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}ᶜ,
              (G ω * h (jumpProcess lam (s + t) ω)
                - G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω)) ∂(jumpMeasure mu nu) := by
        rw [integral_sub (hAi (s + t) nu hnu G hGm hGb).restrict
            (hBi s nu hnu G hGm hGb).restrict,
          ← integral_add_compl hS (hAi (s + t) nu hnu G hGm hGb),
          ← integral_add_compl hS (hBi s nu hnu G hGm hGb), hSeq]
        ring
      -- The functional of the split data, and its majorant.
      set K : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun q ↦
        if q.1.2 ≤ lam q.1.1 * s then
          G (jumpPrepend q.1.1 q.1.2 q.2) *
            (h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)
              - jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2))
        else 0 with hKdef
      set K' : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) → ℝ := fun q ↦
        if q.1.2 ≤ lam q.1.1 * s then
          (if jumpTime lam q.2.1 q.2.2 n ≤ s - q.1.2 / lam q.1.1 then 2 * C else 0)
        else 0 with hK'def
      have hcondm : MeasurableSet
          {q : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) | q.1.2 ≤ lam q.1.1 * s} :=
        measurableSet_le (measurable_snd.comp measurable_fst)
          ((hlam.comp (measurable_fst.comp measurable_fst)).mul measurable_const)
      have htimem : Measurable fun q : (E × ℝ) × ((ℕ → E) × (ℕ → ℝ)) ↦ s - q.1.2 / lam q.1.1 :=
        measurable_const.sub ((measurable_snd.comp measurable_fst).div
          (hlam.comp (measurable_fst.comp measurable_fst)))
      have hKm : Measurable K := by
        rw [hKdef]
        refine Measurable.ite hcondm ?_ measurable_const
        refine (hGm.comp measurable_jumpPrepend).mul ?_
        exact (hh.comp ((measurable_jumpProcess hlam).comp
            ((htimem.add measurable_const).prodMk measurable_snd))).sub
          ((measurable_jumpSemigroup mu hlam hh t).comp
            ((measurable_jumpProcess hlam).comp (htimem.prodMk measurable_snd)))
      have hK'm : Measurable K' := by
        rw [hK'def]
        refine Measurable.ite hcondm ?_ measurable_const
        exact Measurable.ite (measurableSet_le
          ((measurable_jumpTime hlam n).comp measurable_snd) htimem)
          measurable_const measurable_const
      have hKb : ∀ q, |K q| ≤ 2 * C := by
        intro q
        by_cases hq : q.1.2 ≤ lam q.1.1 * s
        · simp only [hKdef, if_pos hq]
          rw [abs_mul]
          have hb2 : |h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)
                  - jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)|
              ≤ 2 * C := by
            calc |h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)
                    - jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)|
                ≤ |h (jumpProcess lam ((s - q.1.2 / lam q.1.1) + t) q.2)|
                  + |jumpSemigroup lam mu h t (jumpProcess lam (s - q.1.2 / lam q.1.1) q.2)| :=
                  abs_sub _ _
              _ ≤ C + C := add_le_add (hC _) (abs_jumpSemigroup_le mu hC t _)
              _ = 2 * C := by ring
          calc |G (jumpPrepend q.1.1 q.1.2 q.2)| * _
              ≤ 1 * (2 * C) := mul_le_mul (hGb _) hb2 (abs_nonneg _) zero_le_one
            _ = 2 * C := one_mul _
        · simp only [hKdef, if_neg hq, abs_zero]
          linarith
      have hK'b : ∀ q, |K' q| ≤ 2 * C := by
        intro q
        by_cases hq : q.1.2 ≤ lam q.1.1 * s
        · by_cases hq2 : jumpTime lam q.2.1 q.2.2 n ≤ s - q.1.2 / lam q.1.1
          · simp only [hK'def, if_pos hq, if_pos hq2]
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * C)]
          · simp only [hK'def, if_pos hq, if_neg hq2, abs_zero]
            linarith
        · simp only [hK'def, if_neg hq, abs_zero]
          linarith
      -- The first identification: the shifted functional is the integrand on `{T 1 ≤ s}`.
      have hKeq : (∫ ω, K ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
          = ∫ ω in {ω : (ℕ → E) × (ℕ → ℝ) | s < jumpTime lam ω.1 ω.2 1}ᶜ,
              (G ω * h (jumpProcess lam (s + t) ω)
                - G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω))
                ∂(jumpMeasure mu nu) := by
        rw [← integral_indicator hS.compl]
        refine integral_congr_ae ?_
        filter_upwards [ae_exists_lt_jumpTime hL0 hlam0 hL mu nu] with ω hω
        have hiff : ω.2 0 ≤ lam (ω.1 0) * s ↔ jumpTime lam ω.1 ω.2 1 ≤ s := by
          rw [jumpTime_one, div_le_iff₀ (hlam0 _), mul_comm s (lam (ω.1 0))]
        by_cases hωS : s < jumpTime lam ω.1 ω.2 1
        · rw [Set.indicator_of_notMem (by simpa using hωS)]
          simp only [hKdef, if_neg (fun hq ↦ absurd (hiff.1 hq) (not_le.2 hωS))]
        · have hT1 : jumpTime lam ω.1 ω.2 1 ≤ s := not_lt.1 hωS
          rw [Set.indicator_of_mem (by simpa using hωS)]
          have e1 : jumpProcess lam (s + t) ω
              = jumpProcess lam ((s - ω.2 0 / lam (ω.1 0)) + t) (jumpShift ω) := by
            rw [jumpProcess_jumpShift (by linarith) (hω (s + t))]
            congr 1
            rw [jumpTime_one]
            ring
          have e2 : jumpProcess lam s ω
              = jumpProcess lam (s - ω.2 0 / lam (ω.1 0)) (jumpShift ω) := by
            rw [jumpProcess_jumpShift hT1 (hω s)]
            congr 1
            rw [jumpTime_one]
          rw [e1, e2]
          simp only [hKdef, if_pos (hiff.2 hT1), jumpPrepend_self]
          ring
      -- The second identification: the majorant is the indicator of two jump time conditions.
      have hK'eq : (∫ ω, K' ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu))
          ≤ 2 * C * (jumpMeasure mu nu).real
              {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s} := by
        have hWm : MeasurableSet ({ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ s}
            ∩ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s}) :=
          (measurableSet_le (measurable_jumpTime hlam 1) measurable_const).inter
            (measurableSet_le (measurable_jumpTime hlam (n + 1)) measurable_const)
        have hW : (fun ω : (ℕ → E) × (ℕ → ℝ) ↦ K' ((ω.1 0, ω.2 0), jumpShift ω))
            = ({ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 1 ≤ s}
                ∩ {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 (n + 1) ≤ s}).indicator
                (fun _ ↦ 2 * C) := by
          funext ω
          have hiff : ω.2 0 ≤ lam (ω.1 0) * s ↔ jumpTime lam ω.1 ω.2 1 ≤ s := by
            rw [jumpTime_one, div_le_iff₀ (hlam0 _), mul_comm s (lam (ω.1 0))]
          have hiff2 : jumpTime lam (jumpShift ω).1 (jumpShift ω).2 n
                ≤ s - ω.2 0 / lam (ω.1 0)
              ↔ jumpTime lam ω.1 ω.2 (n + 1) ≤ s := by
            rw [show (jumpShift ω).1 = fun k ↦ ω.1 (k + 1) from rfl,
              show (jumpShift ω).2 = fun k ↦ ω.2 (k + 1) from rfl, jumpTime_jumpShift,
              ← jumpTime_one lam ω.1 ω.2, sub_le_sub_iff_right]
          by_cases h1 : jumpTime lam ω.1 ω.2 1 ≤ s
          · by_cases h2 : jumpTime lam ω.1 ω.2 (n + 1) ≤ s
            · rw [Set.indicator_of_mem (show ω ∈ {ω : (ℕ → E) × (ℕ → ℝ) |
                  jumpTime lam ω.1 ω.2 1 ≤ s} ∩ {ω : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω.1 ω.2 (n + 1) ≤ s} from ⟨h1, h2⟩)]
              simp only [hK'def, if_pos (hiff.2 h1), if_pos (hiff2.2 h2)]
            · rw [Set.indicator_of_notMem (fun hmem ↦ h2 hmem.2)]
              simp only [hK'def, if_pos (hiff.2 h1), if_neg (fun hq ↦ h2 (hiff2.1 hq))]
          · rw [Set.indicator_of_notMem (fun hmem ↦ h1 hmem.1)]
            simp only [hK'def, if_neg (fun hq ↦ h1 (hiff.1 hq))]
        rw [hW, integral_indicator_const (2 * C) hWm, smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right)
          (by linarith)
      -- The estimate, on the product of the initial law and the holding time.
      have hcmp : ∀ p : E × ℝ, |∫ ω', K (p, ω') ∂(jumpMeasure mu (mu p.1))|
          ≤ ∫ ω', K' (p, ω') ∂(jumpMeasure mu (mu p.1)) := by
        intro p
        by_cases hp : p.2 ≤ lam p.1 * s
        · have hs' : 0 ≤ s - p.2 / lam p.1 := by
            have h1 : p.2 / lam p.1 ≤ s :=
              (div_le_iff₀ (hlam0 p.1)).2 (by rw [mul_comm] at hp; exact hp)
            linarith
          set Gp : (ℕ → E) × (ℕ → ℝ) → ℝ := fun ω' ↦ G (jumpPrepend p.1 p.2 ω') with hGpdef
          have hGpm : Measurable Gp :=
            hGm.comp (measurable_jumpPrepend.comp (measurable_const.prodMk measurable_id))
          have hGpb : ∀ ω', |Gp ω'| ≤ 1 := fun ω' ↦ hGb _
          have hGpp : IsPastFunctional lam (s - p.2 / lam p.1) Gp :=
            hGp.comp_jumpPrepend p.1 p.2
          have hL' : (∫ ω', K (p, ω') ∂(jumpMeasure mu (mu p.1)))
              = (∫ ω', Gp ω' * h (jumpProcess lam ((s - p.2 / lam p.1) + t) ω')
                    ∂(jumpMeasure mu (mu p.1)))
                - ∫ ω', Gp ω' * jumpSemigroup lam mu h t (jumpProcess lam (s - p.2 / lam p.1) ω')
                    ∂(jumpMeasure mu (mu p.1)) := by
            rw [← integral_sub (hAi _ (mu p.1) inferInstance Gp hGpm hGpb)
              (hBi _ (mu p.1) inferInstance Gp hGpm hGpb)]
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω' ↦ ?_)
            simp only [hKdef, if_pos hp, hGpdef]
            ring
          have hR' : (∫ ω', K' (p, ω') ∂(jumpMeasure mu (mu p.1)))
              = 2 * C * (jumpMeasure mu (mu p.1)).real
                  {ω' : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} := by
            have hfun : (fun ω' : (ℕ → E) × (ℕ → ℝ) ↦ K' (p, ω'))
                = {ω' : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω'.1 ω'.2 n
                    ≤ s - p.2 / lam p.1}.indicator (fun _ ↦ 2 * C) := by
              funext ω'
              by_cases hq : jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1
              · rw [Set.indicator_of_mem (show ω' ∈ {ω' : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} from hq)]
                simp only [hK'def, if_pos hp, if_pos hq]
              · rw [Set.indicator_of_notMem (show ω' ∉ {ω' : (ℕ → E) × (ℕ → ℝ) |
                    jumpTime lam ω'.1 ω'.2 n ≤ s - p.2 / lam p.1} from hq)]
                simp only [hK'def, if_pos hp, if_neg hq]
            rw [hfun, integral_indicator_const (2 * C)
              (measurableSet_le (measurable_jumpTime hlam n) measurable_const), smul_eq_mul,
              mul_comm]
          rw [hL', hR']
          exact ih (mu p.1) inferInstance _ hs' Gp hGpm hGpb hGpp
        · have h0 : ∀ ω' : (ℕ → E) × (ℕ → ℝ), K (p, ω') = 0 := by
            intro ω'
            simp only [hKdef, if_neg hp]
          have h0' : ∀ ω' : (ℕ → E) × (ℕ → ℝ), K' (p, ω') = 0 := by
            intro ω'
            simp only [hK'def, if_neg hp]
          simp only [h0, h0', integral_zero, abs_zero, le_refl]
      have hfinal : |∫ ω, K ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu)|
          ≤ ∫ ω, K' ((ω.1 0, ω.2 0), jumpShift ω) ∂(jumpMeasure mu nu) := by
        rw [integral_jumpMeasure_eq_of_split_prod mu nu hKm hKb,
          integral_jumpMeasure_eq_of_split_prod mu nu hK'm hK'b]
        calc |∫ p, (∫ ω', K (p, ω') ∂(jumpMeasure mu (mu p.1))) ∂(nu.prod (expMeasure 1))|
            ≤ ∫ p, |∫ ω', K (p, ω') ∂(jumpMeasure mu (mu p.1))| ∂(nu.prod (expMeasure 1)) :=
              abs_integral_le_integral_abs
          _ ≤ ∫ p, (∫ ω', K' (p, ω') ∂(jumpMeasure mu (mu p.1))) ∂(nu.prod (expMeasure 1)) :=
              integral_mono
                (integrable_of_abs_le (measurable_integral_jumpMeasure_step mu hKm)
                  (fun p ↦ abs_integral_le_of_abs_le fun ω' ↦ hKb _)).abs
                (integrable_of_abs_le (measurable_integral_jumpMeasure_step mu hK'm)
                  (fun p ↦ abs_integral_le_of_abs_le fun ω' ↦ hK'b _)) hcmp
      rw [hred, ← hKeq]
      exact hfinal.trans hK'eq

/-- **The Markov property of the jump process at a fixed time, tested against a factor from the
past.** -/
theorem jumpMeasure_integral_jumpProcess_add_past {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L) (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {G : (ℕ → E) × (ℕ → ℝ) → ℝ} (hGm : Measurable G)
    (hGb : ∀ ω, |G ω| ≤ 1) (hGp : IsPastFunctional lam s G) :
    ∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu)
      = ∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu) := by
  have hlim : Tendsto (fun n ↦ 2 * C * (jumpMeasure mu nu).real
      {ω : (ℕ → E) × (ℕ → ℝ) | jumpTime lam ω.1 ω.2 n ≤ s}) atTop (𝓝 0) := by
    simpa using (tendsto_measureReal_jumpTime_le mu hlam hlam0 hL0 hL nu s).const_mul (2 * C)
  have hzero : |(∫ ω, G ω * h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
      - ∫ ω, G ω * jumpSemigroup lam mu h t (jumpProcess lam s ω) ∂(jumpMeasure mu nu)| ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun n ↦
      abs_integral_jumpMeasure_add_sub_le_past mu hlam hlam0 hL0 hL hh hC ht n nu inferInstance s
        hs G hGm hGb hGp)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hzero)

/-- **The expectation identity tested against a set of the past**, which is the shape the
conditional expectation of the martingale problem consumes:
```
∫_S h (X (s + t)) dP - ∫_S h (X s) dP = ∫_0^t ∫_S (A h) (X (s + r)) dP dr.
```
It is **not** a new statement about the process.  With
`jumpMeasure_integral_jumpProcess_add_past` the left hand side is an expectation of the semigroup
at time `s`, and the semigroup at time `s` is an expectation under the construction restarted from
the law of `X s` conditioned on `S` -- the measure `ν` below.  On that law the identity is
literally `jumpMeasure_integral_sub_eq_intervalIntegral`, and the two normalising factors `c` and
`c⁻¹` cancel.

The functional of the past is an **indicator** and not a general bounded one, and that is what
makes `ν` a measure: for a general `G` the density would have to be built with `withDensity`, and
for a signed `G` there is no measure at all.  The conditional expectation asks only for sets, so
the restriction costs nothing. -/
theorem setIntegral_jumpProcess_sub_eq_intervalIntegral {lam : E → ℝ} (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 < lam x) {L : ℝ} (hL0 : 0 < L) (hL : ∀ x, lam x ≤ L) (nu : Measure E)
    [IsProbabilityMeasure nu] {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {S : Set ((ℕ → E) × (ℕ → ℝ))} (hSm : MeasurableSet S)
    (hSp : IsPastFunctional lam s (S.indicator (fun _ ↦ (1 : ℝ)))) :
    (∫ ω in S, h (jumpProcess lam (s + t) ω) ∂(jumpMeasure mu nu))
        - ∫ ω in S, h (jumpProcess lam s ω) ∂(jumpMeasure mu nu)
      = ∫ r in (0:ℝ)..t, ∫ ω in S, jumpApply lam mu h (jumpProcess lam (s + r) ω)
          ∂(jumpMeasure mu nu) := by
  classical
  set P : Measure ((ℕ → E) × (ℕ → ℝ)) := jumpMeasure mu nu with hPdef
  set G : (ℕ → E) × (ℕ → ℝ) → ℝ := S.indicator (fun _ ↦ (1 : ℝ)) with hGdef
  have hGm : Measurable G := measurable_const.indicator hSm
  have hGb : ∀ ω, |G ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [hGdef, Set.indicator_of_mem hω]; norm_num
    · rw [hGdef, Set.indicator_of_notMem hω, abs_zero]; norm_num
  have hXm : ∀ r : ℝ, Measurable (jumpProcess lam r (E := E)) :=
    fun r ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)
  have hgXm : ∀ (g : E → ℝ), Measurable g → ∀ r : ℝ,
      Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ g (jumpProcess lam r ω) :=
    fun g hg r ↦ hg.comp (hXm r)
  -- the bridge between a set integral and the factor from the past
  have hbridge : ∀ g : (ℕ → E) × (ℕ → ℝ) → ℝ, Measurable g →
      (∫ ω in S, g ω ∂P) = ∫ ω, G ω * g ω ∂P := by
    intro g hg
    rw [← integral_indicator hSm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    by_cases hω : ω ∈ S
    · simp only [hGdef, Set.indicator_of_mem hω, one_mul]
    · simp only [hGdef, Set.indicator_of_notMem hω, zero_mul]
  -- the Markov property on the set
  have hmark : ∀ (g : E → ℝ), Measurable g → ∀ D : ℝ, (∀ x, |g x| ≤ D) → ∀ u : ℝ, 0 ≤ u →
      (∫ ω in S, g (jumpProcess lam (s + u) ω) ∂P)
        = ∫ ω in S, jumpSemigroup lam mu g u (jumpProcess lam s ω) ∂P := by
    intro g hg D hD u hu
    rw [hbridge _ (hgXm g hg (s + u)),
      hbridge _ (hgXm _ (measurable_jumpSemigroup mu hlam hg u) s),
      jumpMeasure_integral_jumpProcess_add_past mu hlam hlam0 hL0 hL nu hg hD hs hu hGm hGb hSp]
  by_cases hzero : P S = 0
  · have hnull : ∀ g : (ℕ → E) × (ℕ → ℝ) → ℝ, (∫ ω in S, g ω ∂P) = 0 := by
      intro g
      rw [Measure.restrict_eq_zero.2 hzero, integral_zero_measure]
    simp only [hnull, sub_zero, sub_self, intervalIntegral.integral_zero]
  · have hSlt : P S ≠ ⊤ := measure_ne_top P S
    have hc0 : P.real S ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.2 ⟨hzero, hSlt⟩
    set c : ℝ := P.real S with hcdef
    set ν : Measure E := (P S)⁻¹ • ((P.restrict S).map (jumpProcess lam s)) with hνdef
    have hνuniv : ν Set.univ = 1 := by
      rw [hνdef, Measure.smul_apply, Measure.map_apply (hXm s) MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply_univ, smul_eq_mul,
        ENNReal.inv_mul_cancel hzero hSlt]
    haveI hνprob : IsProbabilityMeasure ν := ⟨hνuniv⟩
    have hnu : ∀ (g : E → ℝ), Measurable g → ∀ D : ℝ, (∀ x, |g x| ≤ D) →
        (∫ z, g z ∂ν) = c⁻¹ * ∫ ω in S, g (jumpProcess lam s ω) ∂P := by
      intro g hg D hD
      rw [hνdef, integral_smul_measure,
        integral_map (hXm s).aemeasurable hg.aestronglyMeasurable, smul_eq_mul,
        ENNReal.toReal_inv, hcdef, measureReal_def]
    have hsemi : ∀ (g : E → ℝ), Measurable g → ∀ D : ℝ, (∀ x, |g x| ≤ D) → ∀ u : ℝ, 0 ≤ u →
        (∫ ω, g (jumpProcess lam u ω) ∂(jumpMeasure mu ν))
          = c⁻¹ * ∫ ω in S, g (jumpProcess lam (s + u) ω) ∂P := by
      intro g hg D hD u hu
      rw [integral_jumpSemigroup_eq mu ν hlam hg hD u,
        hnu _ (measurable_jumpSemigroup mu hlam hg u) D
          (fun x ↦ abs_jumpSemigroup_le mu hD u x),
        hmark g hg D hD u hu]
    have hAm : Measurable (jumpApply lam mu h) := measurable_jumpApply hlam hh hC
    have hAb : ∀ x, |jumpApply lam mu h x| ≤ 2 * L * C :=
      fun x ↦ abs_jumpApply_le (fun y ↦ (hlam0 y).le) hL hC x
    have hmain := jumpMeasure_integral_sub_eq_intervalIntegral hlam hlam0 hL0 hL mu ν hh hC ht
    rw [hsemi h hh C hC t ht, hnu h hh C hC] at hmain
    have hrhs : (∫ r in (0:ℝ)..t, ∫ ω, jumpApply lam mu h (jumpProcess lam r ω)
          ∂(jumpMeasure mu ν))
        = ∫ r in (0:ℝ)..t, c⁻¹ * ∫ ω in S, jumpApply lam mu h (jumpProcess lam (s + r) ω) ∂P := by
      refine intervalIntegral.integral_congr fun r hr ↦ ?_
      have hr0 : 0 ≤ r := by
        rw [Set.uIcc_of_le ht] at hr
        exact hr.1
      exact hsemi _ hAm (2 * L * C) hAb r hr0
    rw [hrhs, intervalIntegral.integral_const_mul] at hmain
    have hfin : c * (c⁻¹ * (∫ ω in S, h (jumpProcess lam (s + t) ω) ∂P)
          - c⁻¹ * ∫ ω in S, h (jumpProcess lam s ω) ∂P)
        = c * (c⁻¹ * ∫ r in (0:ℝ)..t,
            ∫ ω in S, jumpApply lam mu h (jumpProcess lam (s + r) ω) ∂P) := by
      rw [← mul_sub] at hmain ⊢
      rw [hmain]
    field_simp at hfin
    linarith [hfin]

end ConditionalMarkov

end Space

/-! ### The natural filtration

The two pieces that `jumpProcess_isMPSolution` was missing on 2026-09-09, eighteenth run: the
operator as a set — above — and the filtration.  Mathlib's `MeasureTheory.Filtration.natural`
(`Probability/Process/Filtration.lean:395`) cannot be used, and the reason is a hypothesis and
not an inconvenience: it asks for `StronglyMeasurable (u i)`, which over a bare
`[MeasurableSpace E]` cannot even be *stated*, the declaration carrying
`[TopologicalSpace (β i)] [MetrizableSpace (β i)] [BorelSpace (β i)]`.  Nothing in the
construction uses any of that — the field `le'` needs each `u i` to be measurable and nothing
more — so the version here takes `Measurable` and no topology. -/

/-- **The natural filtration of a measurable process**, without a topology on the state space. -/
def naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {F : Type*} [mF : MeasurableSpace F] (X : ι' → Ω' → F) (hX : ∀ i, Measurable (X i)) :
    Filtration ι' m' where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (X j) mF
  mono' _ _ hij := biSup_mono fun _ ↦ ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j - s ⟨u, hu, rfl⟩
    exact hX j hu

/-- Every coordinate below `i` is measurable for the `i`-th σ-algebra of the natural
filtration. -/
theorem measurable_naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*}
    {m' : MeasurableSpace Ω'} {F : Type*} [mF : MeasurableSpace F] {X : ι' → Ω' → F}
    (hX : ∀ i, Measurable (X i)) {i j : ι'} (hji : j ≤ i) :
    Measurable[naturalFiltration (m' := m') X hX i] (X j) :=
  Measurable.mono (comap_measurable (X j))
    (le_iSup₂ (f := fun j (_ : j ≤ i) ↦ MeasurableSpace.comap (X j) mF) j hji) le_rfl

/-! ## What a functional of the past can see -/

/-- **A functional of the past sees nothing but the path up to `s`.**  Two sample points whose
paths agree below `s` are not separated by any `𝓕 s`-measurable real function.

The proof needs no factorisation theorem: the sets that fail to separate a *fixed* pair form a
σ-algebra, it contains every coordinate below `s`, hence the whole of `𝓕 s`, and a real function
that took two values would separate the pair by a half line. -/
theorem eq_of_measurable_naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*}
    {m' : MeasurableSpace Ω'} {F : Type*} [mF : MeasurableSpace F] {X : ι' → Ω' → F}
    (hX : ∀ i, Measurable (X i)) {s : ι'} {G : Ω' → ℝ}
    (hG : Measurable[naturalFiltration (m' := m') X hX s] G) {ω ω' : Ω'}
    (h : ∀ r ≤ s, X r ω = X r ω') : G ω = G ω' := by
  set 𝓜 : MeasurableSpace Ω' :=
    { MeasurableSet' := fun A ↦ (ω ∈ A ↔ ω' ∈ A)
      measurableSet_empty := by simp
      measurableSet_compl := fun A hA ↦ by
        simp only [Set.mem_compl_iff, not_iff_not]
        exact hA
      measurableSet_iUnion := fun f hf ↦ by
        simp only [Set.mem_iUnion]
        exact exists_congr hf } with h𝓜
  have hle : (naturalFiltration (m' := m') X hX s : MeasurableSpace Ω') ≤ 𝓜 := by
    refine iSup₂_le ?_
    rintro j hj A ⟨u, -, rfl⟩
    show (ω ∈ X j ⁻¹' u ↔ ω' ∈ X j ⁻¹' u)
    simp only [Set.mem_preimage, h j hj]
  rcases lt_trichotomy (G ω) (G ω') with hlt | heq | hlt
  · have hm := hle _ (hG (measurableSet_Iio (a := G ω')))
    exact absurd (show G ω' < G ω' from hm.1 hlt) (lt_irrefl _)
  · exact heq
  · have hm := hle _ (hG (measurableSet_Ioi (a := G ω')))
    exact absurd (show G ω' < G ω' from hm.1 hlt) (lt_irrefl _)

/-- **Composing a functional of the past with a map that shifts the past.**  If every coordinate
below `s` becomes, after the substitution, a coordinate measurable for a σ-algebra `n`, then so
does every `𝓕 s`-measurable functional.  This is the step that carries the induction hypothesis
of the Markov property through the restart. -/
theorem measurable_comp_of_measurable_naturalFiltration {ι' : Type*} [Preorder ι'] {Ω' : Type*}
    {m' : MeasurableSpace Ω'} {F : Type*} [mF : MeasurableSpace F] {X : ι' → Ω' → F}
    (hX : ∀ i, Measurable (X i)) {s : ι'} {𝕜 : Type*} [MeasurableSpace 𝕜] {G : Ω' → 𝕜}
    (hG : Measurable[naturalFiltration (m' := m') X hX s] G)
    {Ω'' : Type*} {n : MeasurableSpace Ω''} {P : Ω'' → Ω'}
    (hP : ∀ r ≤ s, Measurable[n] fun w ↦ X r (P w)) :
    Measurable[n] fun w ↦ G (P w) := by
  have hPm : @Measurable _ _ n (naturalFiltration (m' := m') X hX s) P := by
    rw [measurable_iff_comap_le]
    show MeasurableSpace.comap P (⨆ j, ⨆ (_ : j ≤ s), MeasurableSpace.comap (X j) mF) ≤ n
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun j ↦ ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hj ↦ ?_
    rw [MeasurableSpace.comap_comp]
    exact measurable_iff_comap_le.1 (hP j hj)
  exact hG.comp hPm

/-! ### Right continuity, and progressive measurability

`MeasureTheory.Martingale` asks for `StronglyAdapted` and not for an almost sure version of it,
so the measurability of the compensator has to hold at **every** sample point, the explosion set
included.  That is why the right continuity of `stepPath` is isolated here without any
hypothesis at all, and it is why the argument below runs over the *real valued* process
`h ∘ X` rather than over `X` itself. -/

section Progressive

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The step path is right continuous at every time, for every sequence of jump times.**
Neither monotonicity nor non explosion is needed: if some window contains `t`, then the least
such window is a right neighbourhood of `t` on which the index is constant, and if none does,
then the index is the junk value `0` at `t` and at every later time as well.

This is the half of `IsStepPath` that survives on the explosion set, and it is the half the
progressive measurability below consumes. -/
theorem eventuallyEq_nhdsGE_stepPath {E : Type*} (T : ℕ → ℝ) (y : ℕ → E) (t : ℝ) :
    ∀ᶠ r in 𝓝[≥] t, stepPath T y r = stepPath T y t := by
  by_cases hex : ∃ n, t < T (n + 1)
  · have hlt : t < T (stepIndex T t + 1) := lt_stepIndex_succ hex
    have hmem : Set.Ico t (T (stepIndex T t + 1)) ∈ 𝓝[≥] t :=
      mem_nhdsWithin.2 ⟨Set.Iio (T (stepIndex T t + 1)), isOpen_Iio, hlt,
        fun z hz ↦ ⟨hz.2, hz.1⟩⟩
    filter_upwards [hmem] with r hr
    have h1 : stepIndex T r ≤ stepIndex T t := stepIndex_le hr.2
    have h2 : stepIndex T t ≤ stepIndex T r := by
      by_contra hc
      push_neg at hc
      have h3 : T (stepIndex T r + 1) ≤ t := le_of_lt_stepIndex hc
      have h4 : r < T (stepIndex T r + 1) := lt_stepIndex_succ ⟨stepIndex T t, hr.2⟩
      exact absurd (h4.trans_le (h3.trans hr.1)) (lt_irrefl r)
    simp only [stepPath, le_antisymm h1 h2]
  · push_neg at hex
    filter_upwards [self_mem_nhdsWithin] with r (hr : t ≤ r)
    have ht0 : stepIndex T t = 0 := stepIndex_eq_iff.2 (Or.inr ⟨rfl, hex⟩)
    have hr0 : stepIndex T r = 0 :=
      stepIndex_eq_iff.2 (Or.inr ⟨rfl, fun k ↦ (hex k).trans hr⟩)
    simp only [stepPath, ht0, hr0]

/-- Right continuity is preserved by clamping the time at `0` from below.  The clamp is what
makes the index of the martingale problem — which is `ℝ≥0` — reach the process, which is defined
on `ℝ`: at a negative time the process may be anything at all, and the σ-algebras of the
filtration know nothing about it. -/
theorem eventuallyEq_nhdsGE_comp_max {α : Type*} {g : ℝ → α}
    (hg : ∀ s : ℝ, ∀ᶠ r in 𝓝[≥] s, g r = g s) (s : ℝ) :
    ∀ᶠ r in 𝓝[≥] s, g (max r 0) = g (max s 0) := by
  rcases le_or_gt 0 s with hs | hs
  · filter_upwards [hg s, self_mem_nhdsWithin] with r hr (hrs : s ≤ r)
    rw [max_eq_left (hs.trans hrs), max_eq_left hs, hr]
  · have hmem : Set.Ico s 0 ∈ 𝓝[≥] s :=
      mem_nhdsWithin.2 ⟨Set.Iio 0, isOpen_Iio, hs, fun z hz ↦ ⟨hz.2, hz.1⟩⟩
    filter_upwards [hmem] with r hr
    rw [max_eq_right hr.2.le, max_eq_right hs.le]

/-- The dyadic approximation from the right, capped at `t`: `Int.floor` and not `Nat.floor`,
because a negative time must be approximated too — `Nat.floor` sends every negative number to
`0` and the approximation would jump to `2⁻ⁿ`. -/
noncomputable def dyadicUp (t : ℝ) (n : ℕ) (k : ℤ) : ℝ := min t ((k + 1 : ℤ) / 2 ^ n)

theorem dyadicUp_le (t : ℝ) (n : ℕ) (k : ℤ) : dyadicUp t n k ≤ t := min_le_left _ _

theorem le_dyadicUp (t s : ℝ) (n : ℕ) : min s t ≤ dyadicUp t n ⌊s * 2 ^ n⌋ := by
  have h : s ≤ ((⌊s * 2 ^ n⌋ + 1 : ℤ) : ℝ) / 2 ^ n := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
    push_cast
    exact (Int.lt_floor_add_one (s * 2 ^ n)).le
  rw [dyadicUp, min_comm s t]
  exact min_le_min le_rfl h

theorem dyadicUp_le_add (t s : ℝ) (n : ℕ) :
    dyadicUp t n ⌊s * 2 ^ n⌋ ≤ min s t + (2 : ℝ)⁻¹ ^ n := by
  have hx : ((⌊s * 2 ^ n⌋ + 1 : ℤ) : ℝ) / 2 ^ n ≤ s + (2 : ℝ)⁻¹ ^ n := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
    have h1 : ((⌊s * 2 ^ n⌋ : ℤ) : ℝ) ≤ s * 2 ^ n := Int.floor_le _
    have h2 : ((2 : ℝ)⁻¹) ^ n * 2 ^ n = 1 := by
      rw [← mul_pow]; norm_num
    push_cast
    nlinarith [h1, h2]
  have h3 : dyadicUp t n ⌊s * 2 ^ n⌋ ≤ min t (s + (2 : ℝ)⁻¹ ^ n) :=
    min_le_min le_rfl hx
  have h4 : min t (s + (2 : ℝ)⁻¹ ^ n) ≤ min s t + (2 : ℝ)⁻¹ ^ n := by
    rcases le_total s t with h | h
    · rw [min_eq_left h]
      exact (min_le_right _ _).trans le_rfl
    · rw [min_eq_right h]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right (by positivity))
  exact h3.trans h4

theorem tendsto_dyadicUp (t s : ℝ) :
    Tendsto (fun n : ℕ ↦ dyadicUp t n ⌊s * 2 ^ n⌋) atTop (𝓝[≥] (min s t)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall fun n ↦ le_dyadicUp t s n)
  have h0 : Tendsto (fun n : ℕ ↦ min s t + (2 : ℝ)⁻¹ ^ n) atTop (𝓝 (min s t + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun n ↦ le_dyadicUp t s n) (fun n ↦ dyadicUp_le_add t s n)

/-- **A right continuous real process is jointly measurable in `(t, ω)` up to a fixed time.**

There is no hypothesis on a state space here, and that is the point.  The `E` valued process of
the jump construction is *not* jointly measurable in this sense over a bare
`[MeasurableSpace E]` — the argument approximates `X s` by `X r` for `r` slightly above `s` and
passes to the limit, and a limit of `E` valued measurable maps is measurable only when the
diagonal of `E` is, which for an arbitrary σ-algebra it is not.  Every *real* functional
`h ∘ X` of it is jointly measurable, by the same argument run in `ℝ`, and the compensator of
`mpFamily` is such a functional.  Hence this statement and not a `Clock.IsProgressive` for the
jump process itself. -/
theorem measurable_uncurry_min_of_eventuallyEq {ι' : Type*} [MeasurableSpace ι'] {φ : ι' → ℝ}
    (hφ : Measurable φ) {G : ℝ → Ω → ℝ} {t : ℝ}
    {𝓖 : MeasurableSpace Ω} (hmeas : ∀ r, r ≤ t → Measurable[𝓖] (G r))
    (hrc : ∀ (ω : Ω) (s : ℝ), ∀ᶠ r in 𝓝[≥] s, G r ω = G s ω) :
    Measurable[(inferInstance : MeasurableSpace ι').prod 𝓖]
      fun p : ι' × Ω ↦ G (min (φ p.1) t) p.2 := by
  let _ : MeasurableSpace Ω := 𝓖
  have hstep : ∀ n : ℕ, Measurable fun p : ι' × Ω ↦ G (dyadicUp t n ⌊φ p.1 * 2 ^ n⌋) p.2 := by
    intro n
    have hF : Measurable fun q : Ω × ℤ ↦ G (dyadicUp t n q.2) q.1 :=
      measurable_from_prod_countable_left fun k ↦ hmeas _ (dyadicUp_le t n k)
    exact hF.comp (measurable_snd.prodMk
      (Int.measurable_floor.comp ((hφ.comp measurable_fst).mul_const _)))
  refine measurable_of_tendsto_metrizable hstep (tendsto_pi_nhds.2 fun p ↦ ?_)
  have hev : ∀ᶠ n in atTop, G (dyadicUp t n ⌊φ p.1 * 2 ^ n⌋) p.2 = G (min (φ p.1) t) p.2 :=
    (tendsto_dyadicUp t (φ p.1)).eventually (hrc p.2 (min (φ p.1) t))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  exact hn.symm

end Progressive

/-! ### The filtration of the jump process, and its compensator -/

section JumpFiltration

variable {E : Type*} [MeasurableSpace E]

/-- **The natural filtration of the jump process**, indexed by `ℝ≥0` because `mpFamily` needs
`[OrderBot ι]`. -/
noncomputable def jumpFiltration (lam : E → ℝ) (hlam : Measurable lam) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ((ℕ → E) × (ℕ → ℝ))) :=
  naturalFiltration (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (t : ℝ) ω)
    fun _ ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)

/-- **Every bounded `𝓕 s`-measurable functional is one of the past**, after being cut down to the
non explosive sample points -- which changes no integral, the explosion set being null. -/
theorem isPastFunctional_indicator {lam : E → ℝ} (hlam : Measurable lam) {s : ℝ≥0}
    {G : (ℕ → E) × (ℕ → ℝ) → ℝ} (hG : Measurable[jumpFiltration lam hlam s] G) :
    IsPastFunctional lam (s : ℝ) ((NonExplosive lam).indicator G) := by
  refine ⟨fun ω hω ↦ Set.indicator_of_notMem hω G, fun ω hω ω' hω' hpath ↦ ?_⟩
  rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω']
  refine eq_of_measurable_naturalFiltration _ hG fun r hr ↦ ?_
  exact hpath (r : ℝ) r.coe_nonneg (by exact_mod_cast hr)

/-- The jump process is right continuous at every time and at every sample point, the explosion
set included: `eventuallyEq_nhdsGE_stepPath` read through the definition. -/
theorem eventuallyEq_nhdsGE_jumpProcess {lam : E → ℝ} (ω : (ℕ → E) × (ℕ → ℝ)) (s : ℝ) :
    ∀ᶠ r in 𝓝[≥] s, jumpProcess lam r ω = jumpProcess lam s ω :=
  eventuallyEq_nhdsGE_stepPath (jumpTime lam ω.1 ω.2) ω.1 s

/-- **Every real functional of the jump process is jointly measurable in `(u, ω)` for the
σ-algebra of the past up to `t`.**  This is the progressive measurability that the compensator
of `mpFamily` consumes, and the right continuity of the paths is the only input. -/
theorem measurable_uncurry_jumpProcess {lam : E → ℝ} (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) (t : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace ℝ≥0).prod (jumpFiltration lam hlam t)]
      fun p : ℝ≥0 × ((ℕ → E) × (ℕ → ℝ)) ↦
        h (jumpProcess lam (min (p.1 : ℝ) (t : ℝ)) p.2) := by
  have hmeas : ∀ r, r ≤ (t : ℝ) →
      Measurable[jumpFiltration lam hlam t] fun ω ↦ h (jumpProcess lam (max r 0) ω) := by
    intro r hr
    have hu : Real.toNNReal r ≤ t := Real.toNNReal_le_iff_le_coe.2 hr
    have hX := measurable_naturalFiltration
      (X := fun s : ℝ≥0 ↦ fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpProcess lam (s : ℝ) ω)
      (fun _ ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)) hu
    rw [Real.coe_toNNReal'] at hX
    exact hh.comp hX
  have hrc : ∀ (ω : (ℕ → E) × (ℕ → ℝ)) (s : ℝ),
      ∀ᶠ r in 𝓝[≥] s, h (jumpProcess lam (max r 0) ω) = h (jumpProcess lam (max s 0) ω) :=
    fun ω s ↦ eventuallyEq_nhdsGE_comp_max (g := fun r ↦ h (jumpProcess lam r ω))
      (fun s' ↦ (eventuallyEq_nhdsGE_jumpProcess ω s').mono fun r hr ↦ by rw [hr]) s
  have key := measurable_uncurry_min_of_eventuallyEq (φ := fun u : ℝ≥0 ↦ (u : ℝ))
    measurable_coe_nnreal_real hmeas hrc
  have heq : ∀ p : ℝ≥0 × ((ℕ → E) × (ℕ → ℝ)),
      h (jumpProcess lam (max (min (p.1 : ℝ) (t : ℝ)) 0) p.2)
        = h (jumpProcess lam (min (p.1 : ℝ) (t : ℝ)) p.2) := fun p ↦ by
    rw [max_eq_left (le_min p.1.coe_nonneg t.coe_nonneg)]
  simpa only [heq] using key

/-- **The compensator of the jump martingale problem is measurable for the past.**  This is the
half of `MeasureTheory.Martingale` that is not a conditional expectation, and it is the half
that has to hold at *every* sample point: `StronglyAdapted` is not an almost sure notion, so the
explosion set — a null set, but not the empty set — may not be discarded here. -/
theorem measurable_compensator {lam : E → ℝ} (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) (c : Clock.Conv) (t : ℝ≥0) :
    Measurable[jumpFiltration lam hlam t] fun ω ↦
      ∫ u in lebesgueClock.interval c ⊥ t, h (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q := by
  set S := lebesgueClock.interval c ⊥ t with hS
  haveI hfin : IsFiniteMeasure (lebesgueClock.q.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (lebesgueClock.measure_Iic_ne_top t)
      (measure_mono (lebesgueClock.interval_subset_Iic c ⊥ t)))
  have hW := measurable_uncurry_jumpProcess hlam hh t
  have hsm : StronglyMeasurable[jumpFiltration lam hlam t] fun ω : (ℕ → E) × (ℕ → ℝ) ↦
      ∫ u in S, h (jumpProcess lam (min (u : ℝ) (t : ℝ)) ω) ∂lebesgueClock.q :=
    @stronglyMeasurable_integral_comp ℝ≥0 lebesgueClock.measurableSpace
      ((ℕ → E) × (ℕ → ℝ)) (jumpFiltration lam hlam t) ℝ _ ℝ _
      (lebesgueClock.q.restrict S) _
      (fun u ω ↦ h (jumpProcess lam (min (u : ℝ) (t : ℝ)) ω)) hW id measurable_id
  have hcongr : (fun ω : (ℕ → E) × (ℕ → ℝ) ↦
        ∫ u in S, h (jumpProcess lam (min (u : ℝ) (t : ℝ)) ω) ∂lebesgueClock.q)
      = fun ω ↦ ∫ u in S, h (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q := by
    funext ω
    refine setIntegral_congr_fun (lebesgueClock.measurableSet_interval c ⊥ t) fun u hu ↦ ?_
    rw [min_eq_left]
    exact_mod_cast lebesgueClock.interval_subset_Iic c ⊥ t hu
  rw [← hcongr]
  exact hsm.measurable

/-- **A compensating window is bounded by the bound of its integrand times the length of the
window.**  The clock is Lebesgue measure, so the length is `t` itself; the exact mass
`lebesgueClock_apply_Ioc` and not a mere finiteness bound is what makes the constant explicit,
and the explicit constant is what `integrable_mpFamily_jumpProcess` needs. -/
theorem abs_setIntegral_compensator_le {lam : E → ℝ} {g : E → ℝ} {D : ℝ} (hD : ∀ x, |g x| ≤ D)
    (t : ℝ≥0) (ω : (ℕ → E) × (ℕ → ℝ)) :
    |∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
        g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q| ≤ D * (t : ℝ) := by
  rw [lebesgueClock_interval_optional_eq]
  have hlt : lebesgueClock.q (Set.Ioc (⊥ : ℝ≥0) t) < ⊤ := by
    rw [lebesgueClock_apply_Ioc]; exact ENNReal.ofReal_lt_top
  have hle := norm_setIntegral_le_of_norm_le_const (μ := lebesgueClock.q)
    (s := Set.Ioc (⊥ : ℝ≥0) t) (f := fun u : ℝ≥0 => g (jumpProcess lam (u : ℝ) ω)) (C := D) hlt
    (fun u _ => by simpa using hD (jumpProcess lam (u : ℝ) ω))
  rwa [Real.norm_eq_abs, measureReal_def, lebesgueClock_apply_Ioc,
    show ((⊥ : ℝ≥0) : ℝ) = 0 from rfl, sub_zero,
    ENNReal.toReal_ofReal (NNReal.coe_nonneg t)] at hle

/-- **The difference of two nested compensating windows is the compensating integral of what lies
between them, turned into a genuine interval integral of the shifted process with the set
integral moved to the outside.**  This assembles the second, third and fourth of the four
bookkeeping steps `jumpProcess_isMPSolution` needs: `Clock.interval_union` splits the windows,
`integral_lebesgueClock_Ioc` reindexes the remainder as a real interval integral, and
`intervalIntegral_integral_swap` is Fubini between that interval integral and the set integral. -/
theorem setIntegral_compensator_sub_eq_intervalIntegral {lam : E → ℝ} (hlam : Measurable lam)
    {i j : ℝ≥0} (hij : i ≤ j) {g : E → ℝ} (hg : Measurable g) {D : ℝ} (hD : ∀ x, |g x| ≤ D)
    (mu : Kernel E E) [IsMarkovKernel mu] (nu : Measure E) [IsProbabilityMeasure nu]
    {S : Set ((ℕ → E) × (ℕ → ℝ))} (hSm : MeasurableSet S) :
    (∫ ω in S, (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j,
          g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q) ∂(jumpMeasure mu nu))
      - ∫ ω in S, (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ i,
          g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q) ∂(jumpMeasure mu nu)
    = ∫ r in (0 : ℝ)..((j : ℝ) - (i : ℝ)), ∫ ω in S, g (jumpProcess lam ((i : ℝ) + r) ω)
        ∂(jumpMeasure mu nu) := by
  set μ0 := jumpMeasure mu nu with hμ0def
  have hWm : Measurable fun p : ℝ≥0 × ((ℕ → E) × (ℕ → ℝ)) => jumpProcess lam (p.1 : ℝ) p.2 :=
    (measurable_jumpProcess hlam).comp
      ((measurable_coe_nnreal_real.comp measurable_fst).prodMk measurable_snd)
  have hgXu : ∀ ω, Measurable fun u : ℝ≥0 => g (jumpProcess lam (u : ℝ) ω) := fun ω =>
    hg.comp (hWm.comp (measurable_id.prodMk measurable_const))
  have hmeas_win : ∀ t : ℝ≥0, Measurable fun ω =>
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
        g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q := fun t =>
    Measurable.mono (measurable_compensator hlam hg Clock.Conv.optional t)
      ((jumpFiltration lam hlam).le' t) le_rfl
  have houterbound : ∀ (t : ℝ≥0) (ω : (ℕ → E) × (ℕ → ℝ)),
      |∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
        g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q| ≤ D * (t : ℝ) :=
    abs_setIntegral_compensator_le hD
  have hInt_i : IntegrableOn (fun ω => ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ i,
      g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q) S μ0 :=
    integrableOn_of_bounded μ0 (measure_ne_top μ0 S) (hmeas_win i) (houterbound i)
  have hInt_j : IntegrableOn (fun ω => ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j,
      g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q) S μ0 :=
    integrableOn_of_bounded μ0 (measure_ne_top μ0 S) (hmeas_win j) (houterbound j)
  rw [← integral_sub hInt_j hInt_i]
  have habij : (0 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have := (NNReal.coe_le_coe).2 hij; linarith
  have hpt : ∀ ω, (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j,
        g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
      - (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ i,
        g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
      = ∫ r in (0 : ℝ)..((j : ℝ) - (i : ℝ)), g (jumpProcess lam ((i : ℝ) + r) ω) := by
    intro ω
    obtain ⟨hunion, hdisj⟩ := lebesgueClock.interval_union Clock.Conv.optional
      (bot_le : (⊥ : ℝ≥0) ≤ i) hij
    have hIa : IntegrableOn (fun u : ℝ≥0 => g (jumpProcess lam (u : ℝ) ω))
        (lebesgueClock.interval Clock.Conv.optional ⊥ i) lebesgueClock.q :=
      integrableOn_of_bounded lebesgueClock.q
        (lebesgueClock.measure_interval_ne_top Clock.Conv.optional ⊥ i) (hgXu ω) (fun u => hD _)
    have hIb : IntegrableOn (fun u : ℝ≥0 => g (jumpProcess lam (u : ℝ) ω))
        (lebesgueClock.interval Clock.Conv.optional i j) lebesgueClock.q :=
      integrableOn_of_bounded lebesgueClock.q
        (lebesgueClock.measure_interval_ne_top Clock.Conv.optional i j) (hgXu ω) (fun u => hD _)
    rw [hunion,
      setIntegral_union hdisj (lebesgueClock.measurableSet_interval Clock.Conv.optional i j)
        hIa hIb]
    rw [show (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ i,
            g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
          + (∫ u in lebesgueClock.interval Clock.Conv.optional i j,
            g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
        - ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ i,
            g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q
        = ∫ u in lebesgueClock.interval Clock.Conv.optional i j,
            g (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q from by ring,
      lebesgueClock_interval_optional_eq, integral_lebesgueClock_Ioc hij (hgXu ω)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le habij] at hr
    rw [Real.coe_toNNReal ((i : ℝ) + r) (by linarith [hr.1, NNReal.coe_nonneg i])]
  simp_rw [hpt]
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) ((j : ℝ) - (i : ℝ)))) := by
    rw [Set.uIoc_of_le habij]; infer_instance
  have hIntSwap : Integrable (Function.uncurry fun (r : ℝ) (ω : (ℕ → E) × (ℕ → ℝ)) =>
      g (jumpProcess lam ((i : ℝ) + r) ω))
      ((volume.restrict (Set.uIoc (0 : ℝ) ((j : ℝ) - (i : ℝ)))).prod (μ0.restrict S)) := by
    refine integrable_of_abs_le ?_ (fun p => hD _)
    exact hg.comp ((measurable_jumpProcess hlam).comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd))
  exact (intervalIntegral_integral_swap hIntSwap).symm

/-- **The test processes of the jump martingale problem are adapted to the natural filtration of
the jump process.**  This is the first of the two conjuncts of `MeasureTheory.Martingale`, and it
is the one that does not mention the measure at all. -/
theorem stronglyAdapted_mpFamily_jumpProcess {lam : E → ℝ} (hlam : Measurable lam)
    {mu : Kernel E E} [IsMarkovKernel mu] (c : Clock.Conv)
    {Y : ℝ≥0 → ((ℕ → E) × (ℕ → ℝ)) → ℝ}
    (hY : Y ∈ mpFamily (jumpOperator lam mu) lebesgueClock c
      (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (t : ℝ) ω)) :
    StronglyAdapted (jumpFiltration lam hlam) Y := by
  obtain ⟨p, ⟨hf, ⟨C, hC⟩, hp2⟩, hYeq⟩ := hY
  intro t
  have h1 : Measurable[jumpFiltration lam hlam t] fun ω ↦ p.1 (jumpProcess lam (t : ℝ) ω) :=
    hf.comp (measurable_naturalFiltration
      (X := fun s : ℝ≥0 ↦ fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpProcess lam (s : ℝ) ω)
      (fun _ ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
      (le_refl t))
  have h2 : Measurable[jumpFiltration lam hlam t] fun ω ↦
      ∫ u in lebesgueClock.interval c ⊥ t, p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q := by
    rw [hp2]
    exact measurable_compensator hlam (measurable_jumpApply hlam hf hC) c t
  have hYt : Y t = fun ω ↦ p.1 (jumpProcess lam (t : ℝ) ω) -
      ∫ u in lebesgueClock.interval c ⊥ t, p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q :=
    funext fun ω ↦ hYeq t ω
  rw [hYt]
  exact (h1.sub h2).stronglyMeasurable

/-- **The test processes of the jump martingale problem are integrable**, which is the hypothesis
`ae_eq_condExp_of_forall_setIntegral_eq` asks of the later time.  The bound is `C + 2LC·t`: the
first summand is the bound on `p.1`, the second is `abs_setIntegral_compensator_le` applied to
`abs_jumpApply_le`.  The bound grows with `t`, but it is finite at every `t`, and that is all a
martingale needs. -/
theorem integrable_mpFamily_jumpProcess {lam : E → ℝ} (hlam : Measurable lam) {L : ℝ}
    (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) {mu : Kernel E E} [IsMarkovKernel mu]
    (nu : Measure E) [IsProbabilityMeasure nu] {Y : ℝ≥0 → ((ℕ → E) × (ℕ → ℝ)) → ℝ}
    (hY : Y ∈ mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional
      (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (t : ℝ) ω)) (t : ℝ≥0) :
    Integrable (Y t) (jumpMeasure mu nu) := by
  have hadp := stronglyAdapted_mpFamily_jumpProcess hlam Clock.Conv.optional hY
  obtain ⟨p, ⟨hf, ⟨C, hC⟩, hp2⟩, hYeq⟩ := hY
  have hYm : Measurable (Y t) := ((hadp t).mono ((jumpFiltration lam hlam).le t)).measurable
  refine integrable_of_abs_le hYm (C := C + 2 * L * C * (t : ℝ)) fun ω ↦ ?_
  have hb : |∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
      p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q| ≤ 2 * L * C * (t : ℝ) := by
    rw [hp2]
    exact abs_setIntegral_compensator_le (fun x ↦ abs_jumpApply_le hlam0 hL hC x) t ω
  have h1 := hC (jumpProcess lam (t : ℝ) ω)
  have h2 := abs_sub (p.1 (jumpProcess lam (t : ℝ) ω))
    (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
      p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
  rw [hYeq t ω]
  linarith

/-- **`thm:jumpMP`: the jump process solves the martingale problem of its generator.**  This is
the goal of Milestone 4, and it is the first solution of a martingale problem in this file that
is a solution and not a counterexample.

The proof is the assembly of the two expectation identities, and nothing probabilistic is left in
it.  `stronglyAdapted_mpFamily_jumpProcess` is the adaptedness;
`setIntegral_jumpProcess_sub_eq_intervalIntegral` turns the increment of `p.1 ∘ X` over a set of
the past into the interval integral of `A p.1 ∘ X`, and
`setIntegral_compensator_sub_eq_intervalIntegral` turns the increment of the compensator into the
same interval integral, so the two cancel and the increment of `Y` integrates to zero over every
set of the past.  `ae_eq_condExp_of_forall_setIntegral_eq` then names that the conditional
expectation.

Two hypotheses of the two identities are supplied here and are not in the statement.  The set of
the past is cut down to `NonExplosive lam ∩ S`, because `isPastFunctional_indicator` produces a
functional of the past only after that cut; the cut changes no integral
(`indicator_nonExplosive_ae_eq`).  And `0 < L` is not assumed but derived: `nu` is a probability
measure, so `E` is nonempty, and `0 < lam x ≤ L` at any of its points. -/
theorem jumpProcess_isMPSolution {lam : E → ℝ} (hlam : Measurable lam) {L : ℝ}
    (hlam0 : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu]
    (nu : Measure E) [IsProbabilityMeasure nu] :
    IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional
        (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (t : ℝ) ω))
      (jumpFiltration lam hlam) (jumpMeasure mu nu) := by
  classical
  -- the state space is nonempty, because `nu` is a probability measure; hence `0 < L`
  have hne : Nonempty E := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : nu Set.univ = 0 := by rw [Set.univ_eq_empty_iff.2 hcon, measure_empty]
    rw [measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨x0⟩ := hne
  have hL0 : 0 < L := lt_of_lt_of_le (hlam0 x0) (hL x0)
  intro Y hY
  refine ⟨stronglyAdapted_mpFamily_jumpProcess hlam Clock.Conv.optional hY, ?_⟩
  have hadp := stronglyAdapted_mpFamily_jumpProcess hlam Clock.Conv.optional hY
  have hint := integrable_mpFamily_jumpProcess hlam (fun x ↦ (hlam0 x).le) hL nu hY
  obtain ⟨p, ⟨hf, ⟨C, hC⟩, hp2⟩, hYeq⟩ := hY
  have hgm : Measurable p.2 := by rw [hp2]; exact measurable_jumpApply hlam hf hC
  have hgb : ∀ x, |p.2 x| ≤ 2 * L * C := by
    rw [hp2]; exact fun x ↦ abs_jumpApply_le (fun y ↦ (hlam0 y).le) hL hC x
  have hwin : ∀ t : ℝ≥0, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
        p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q := fun t ↦
    Measurable.mono (measurable_compensator hlam hgm Clock.Conv.optional t)
      ((jumpFiltration lam hlam).le' t) le_rfl
  have hXm : ∀ r : ℝ, Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ p.1 (jumpProcess lam r ω) := fun r ↦
    hf.comp ((measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
  intro i j hij
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((jumpFiltration lam hlam).le i) (hint j)
    (fun S _ _ ↦ (hint i).integrableOn) ?_ (hadp i).aestronglyMeasurable).symm
  intro S hS _
  -- the non explosive part of `S`, on which the indicator is a functional of the past
  have hSm : MeasurableSet S := (jumpFiltration lam hlam).le i S hS
  have hSm' : MeasurableSet (NonExplosive lam ∩ S) :=
    (measurableSet_nonExplosive hlam).inter hSm
  have hrestrict : (jumpMeasure mu nu).restrict (NonExplosive lam ∩ S)
      = (jumpMeasure mu nu).restrict S := by
    refine Measure.restrict_congr_set ?_
    filter_upwards [ae_mem_nonExplosive hL0 hlam0 hL mu nu] with ω hω
    exact propext ⟨fun h ↦ h.2, fun h ↦ ⟨hω, h⟩⟩
  have hSp : IsPastFunctional lam (i : ℝ)
      ((NonExplosive lam ∩ S).indicator fun _ ↦ (1 : ℝ)) := by
    have hGm : Measurable[jumpFiltration lam hlam i] (S.indicator fun _ ↦ (1 : ℝ)) :=
      measurable_const.indicator hS
    have h := isPastFunctional_indicator hlam hGm
    rwa [Set.indicator_indicator] at h
  -- the two expectation identities, whose right hand sides are the same interval integral
  have hji : (0 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have := (NNReal.coe_le_coe).2 hij; linarith
  have h1 := setIntegral_jumpProcess_sub_eq_intervalIntegral mu hlam hlam0 hL0 hL nu hf hC
    (s := (i : ℝ)) (t := (j : ℝ) - (i : ℝ)) i.coe_nonneg hji hSm' hSp
  rw [show (i : ℝ) + ((j : ℝ) - (i : ℝ)) = (j : ℝ) by ring] at h1
  have h2 := setIntegral_compensator_sub_eq_intervalIntegral hlam hij hgm hgb mu nu hSm'
  rw [hp2] at h2
  -- the increment of `Y` over the set is the difference of the two
  have hsplit : ∀ t : ℝ≥0, (∫ ω in NonExplosive lam ∩ S, Y t ω ∂(jumpMeasure mu nu))
      = (∫ ω in NonExplosive lam ∩ S, p.1 (jumpProcess lam (t : ℝ) ω) ∂(jumpMeasure mu nu))
        - ∫ ω in NonExplosive lam ∩ S, (∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
            p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q) ∂(jumpMeasure mu nu) := by
    intro t
    have hIa : IntegrableOn (fun ω ↦ p.1 (jumpProcess lam (t : ℝ) ω))
        (NonExplosive lam ∩ S) (jumpMeasure mu nu) :=
      integrableOn_of_bounded _ (measure_ne_top _ _) (hXm (t : ℝ)) fun ω ↦ hC _
    have hIb : IntegrableOn (fun ω ↦ ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
        p.2 (jumpProcess lam (u : ℝ) ω) ∂lebesgueClock.q)
        (NonExplosive lam ∩ S) (jumpMeasure mu nu) :=
      integrableOn_of_bounded _ (measure_ne_top _ _) (hwin t)
        (abs_setIntegral_compensator_le hgb t)
    simp only [hYeq t]
    exact integral_sub hIa hIb
  simp only [hp2] at hsplit
  rw [← hrestrict, hsplit i, hsplit j]
  linarith

end JumpFiltration

end JumpConstruction

/-! ## Milestone 4, uniqueness: the Picard iteration

The exponential series of the bounded generator, and the theorem that fixes the one dimensional
distributions of **every** solution of the martingale problem to be that series applied to the
initial law.  This is the uniqueness half of `exists_unique_of_bounded`; the existence half is
`jumpProcess_isMPSolution` above.

Three remarks on the shape of what follows.

First, the abstract layer is kept: nothing here mentions `jumpProcess`, and the process `X` is
an arbitrary family of maps `ℝ≥0 → Ω → E`.  That is what makes the statement a *uniqueness*
statement -- it applies to any solution, not to the one that was constructed.

Second, the only regularity asked of `X` is `hX`, the joint measurability in `(u, ω)` of the real
functionals `h ∘ X`, and `hX0`, the measurability of the initial value.  Neither is the joint
measurability of `X` itself, which is not available: a limit of `E` valued measurable maps is
measurable only if the diagonal of `E` is, and the jump process supplies the real functional form
(`measurable_uncurry_jumpProcess`) and not the `E` valued one.

Third, the whole argument is the Picard iteration and uses no analysis beyond the Bochner
integral: `integral_sub_eq_intervalIntegral_of_isMPSolution` turns the martingale property into
the integral equation `u_f(t) = ν(f) + ∫_0^t u_{Af}(s) ds`, and
`abs_integral_sub_sum_le_of_isMPSolution` iterates it, the remainder after `n` steps being
`(2Lt)^n / n!` times the bound of `f`.
-/

section Uniqueness

variable {lam : E → ℝ} {mu : Kernel E E} {f : E → ℝ} {L C : ℝ}

/-- **The iterates of the generator are bounded by the powers of its bound.** -/
theorem abs_iterate_jumpApply_le [IsMarkovKernel mu] (hlam0 : ∀ x, 0 ≤ lam x)
    (hL : ∀ x, lam x ≤ L) (hC : ∀ x, |f x| ≤ C) (n : ℕ) (x : E) :
    |(jumpApply lam mu)^[n] f x| ≤ (2 * L) ^ n * C := by
  induction n generalizing x with
  | zero => simpa using hC x
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc |jumpApply lam mu ((jumpApply lam mu)^[n] f) x|
          ≤ 2 * L * ((2 * L) ^ n * C) := abs_jumpApply_le hlam0 hL ih x
        _ = (2 * L) ^ (n + 1) * C := by ring

/-- The iterates of the generator are measurable. -/
theorem measurable_iterate_jumpApply [IsMarkovKernel mu] (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) (hf : Measurable f) (hC : ∀ x, |f x| ≤ C)
    (n : ℕ) : Measurable ((jumpApply lam mu)^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact measurable_jumpApply hlam ih (abs_iterate_jumpApply_le hlam0 hL hC n)

/-- **The exponential series of the generator**, `exp (t • A) f`. -/
noncomputable def expJumpApply (lam : E → ℝ) (mu : Kernel E E) (t : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∑' n : ℕ, (t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x

/-- A term of the exponential series, bounded by the corresponding term of the exponential
series of `2 L |t|`.  Stated for a scalar, because it is used both pointwise and under an
integral sign. -/
theorem abs_series_term_le {a : ℝ} {n : ℕ} (h : |a| ≤ (2 * L) ^ n * C) (t : ℝ) :
    |(t ^ n / n.factorial) * a| ≤ (2 * L * |t|) ^ n / n.factorial * C := by
  rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
  have h2 : (0:ℝ) ≤ |t| ^ n / n.factorial :=
    div_nonneg (pow_nonneg (abs_nonneg t) n) (Nat.cast_nonneg _)
  calc |t| ^ n / n.factorial * |a|
      ≤ |t| ^ n / n.factorial * ((2 * L) ^ n * C) := mul_le_mul_of_nonneg_left h h2
    _ = (2 * L * |t|) ^ n / n.factorial * C := by
        rw [mul_pow, mul_comm (2*L) |t|]; ring

/-- Each term of the exponential series is bounded by the corresponding term of the exponential
series of `2 L |t|`. -/
theorem abs_term_expJumpApply_le [IsMarkovKernel mu] (hlam0 : ∀ x, 0 ≤ lam x)
    (hL : ∀ x, lam x ≤ L) (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : E) (n : ℕ) :
    |(t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x|
      ≤ (2 * L * |t|) ^ n / n.factorial * C :=
  abs_series_term_le (abs_iterate_jumpApply_le hlam0 hL hC n x) t

/-- The exponential series converges absolutely at every point. -/
theorem summable_expJumpApply [IsMarkovKernel mu] (hlam0 : ∀ x, 0 ≤ lam x)
    (hL : ∀ x, lam x ≤ L) (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : E) :
    Summable fun n : ℕ ↦ (t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial (2 * L * |t|)).mul_right C)
    fun n ↦ abs_term_expJumpApply_le hlam0 hL hC t x n

/-- **The exponential series is bounded by `exp (2 L |t|) C`.** -/
theorem abs_expJumpApply_le [IsMarkovKernel mu] (hlam0 : ∀ x, 0 ≤ lam x)
    (hL : ∀ x, lam x ≤ L) (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : E) :
    |expJumpApply lam mu t f x| ≤ Real.exp (2 * L * |t|) * C := by
  have hexp : Real.exp (2 * L * |t|) = ∑' n : ℕ, (2 * L * |t|) ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have habs : Summable fun n : ℕ ↦ |(t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x| :=
    Summable.of_nonneg_of_le (fun n ↦ abs_nonneg _)
      (fun n ↦ abs_term_expJumpApply_le hlam0 hL hC t x n)
      ((Real.summable_pow_div_factorial (2 * L * |t|)).mul_right C)
  rw [expJumpApply, hexp, ← tsum_mul_right]
  refine le_trans ?_ (habs.tsum_le_tsum (fun n ↦ abs_term_expJumpApply_le hlam0 hL hC t x n)
    ((Real.summable_pow_div_factorial (2 * L * |t|)).mul_right C))
  simpa only [Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm (f := fun n : ℕ ↦ (t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x)
      (by simpa only [Real.norm_eq_abs] using habs)

/-- The exponential series is measurable in the state. -/
theorem measurable_expJumpApply [IsMarkovKernel mu] (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) (hf : Measurable f) (hC : ∀ x, |f x| ≤ C)
    (t : ℝ) : Measurable (expJumpApply lam mu t f) :=
  measurable_of_tendsto_metrizable' atTop
    (f := fun N x ↦ ∑ n ∈ Finset.range N, (t ^ n / n.factorial) * (jumpApply lam mu)^[n] f x)
    (fun _ ↦ Finset.measurable_sum _ fun n _ ↦
      measurable_const.mul (measurable_iterate_jumpApply hlam hlam0 hL hf hC n))
    (tendsto_pi_nhds.mpr fun x ↦ (summable_expJumpApply hlam0 hL hC t x).hasSum.tendsto_sum_nat)

variable {P : Measure Ω} {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

/-- **The martingale identity, integrated**: the expectation of a bounded functional of the
state at time `t` is its initial expectation plus the time integral of the expectation of its
image under the generator. -/
theorem integral_sub_eq_intervalIntegral_of_isMPSolution [IsProbabilityMeasure P]
    [IsMarkovKernel mu] (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    (∫ ω, f (X t ω) ∂P) - ∫ ω, f (X 0 ω) ∂P
      = ∫ r in (0:ℝ)..(t:ℝ), ∫ ω, jumpApply lam mu f (X (Real.toNNReal r) ω) ∂P := by
  set g := jumpApply lam mu f with hgdef
  have hgm : Measurable g := measurable_jumpApply hlam hf hC
  have hgb : ∀ x, |g x| ≤ 2 * L * C := fun x ↦ abs_jumpApply_le hlam0 hL hC x
  set S : Set ℝ≥0 := lebesgueClock.interval Clock.Conv.optional ⊥ t with hSdef
  have hSeq : S = Set.Ioc (⊥ : ℝ≥0) t := lebesgueClock_interval_optional_eq ⊥ t
  haveI hfinS : IsFiniteMeasure (lebesgueClock.q.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hSeq, lebesgueClock_apply_Ioc]
    exact ENNReal.ofReal_lt_top
  have hsftest : SFinite (lebesgueClock.q.restrict S) := inferInstance
  -- the compensated test process
  set Y : ℝ≥0 → Ω → ℝ := fun s ω ↦ f (X s ω) -
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ s, g (X u ω) ∂lebesgueClock.q with hYdef
  have hmart : Martingale Y F P :=
    hsol Y ⟨(f, g), mem_jumpOperator hf hC, fun s ω ↦ rfl⟩
  -- the two integrability facts
  have hintf : ∀ s : ℝ≥0, Integrable (fun ω ↦ f (X s ω)) P := fun s ↦
    integrable_of_abs_le ((hX f hf).comp (measurable_const.prodMk measurable_id))
      (fun ω ↦ hC (X s ω))
  have hcompm : StronglyMeasurable fun ω ↦ ∫ u in S, g (X u ω) ∂lebesgueClock.q :=
    @stronglyMeasurable_integral_comp ℝ≥0 lebesgueClock.measurableSpace Ω m ℝ _ ℝ _
      (lebesgueClock.q.restrict S) hsftest (fun u ω ↦ g (X u ω)) (hX g hgm) id measurable_id
  have hStop : lebesgueClock.q S < ⊤ := by
    rw [hSeq, lebesgueClock_apply_Ioc]; exact ENNReal.ofReal_lt_top
  have hcompb : ∀ ω, |∫ u in S, g (X u ω) ∂lebesgueClock.q| ≤ 2 * L * C * (t : ℝ) := by
    intro ω
    have hmass : lebesgueClock.q.real S = (t : ℝ) := by
      rw [measureReal_def, hSeq, lebesgueClock_apply_Ioc]
      simp
    have := norm_setIntegral_le_of_norm_le_const (μ := lebesgueClock.q) (s := S)
      (f := fun u ↦ g (X u ω)) (C := 2 * L * C) hStop
      (fun u _ ↦ by simpa only [Real.norm_eq_abs] using hgb (X u ω))
    rw [Real.norm_eq_abs, hmass] at this
    exact this
  have hintc : Integrable (fun ω ↦ ∫ u in S, g (X u ω) ∂lebesgueClock.q) P :=
    integrable_of_abs_le hcompm.measurable hcompb
  -- the martingale has constant expectation
  have hexp : ∫ ω, Y t ω ∂P = ∫ ω, Y 0 ω ∂P :=
    calc ∫ ω, Y t ω ∂P = ∫ ω, (P[Y t | F 0]) ω ∂P := (integral_condExp (F.le 0)).symm
      _ = ∫ ω, Y 0 ω ∂P := integral_congr_ae (hmart.2 0 t (by simp))
  have hY0 : ∀ ω, Y 0 ω = f (X 0 ω) := by
    intro ω
    simp [hYdef, lebesgueClock_interval_optional_eq]
  have hYt : ∫ ω, Y t ω ∂P
      = (∫ ω, f (X t ω) ∂P) - ∫ ω, (∫ u in S, g (X u ω) ∂lebesgueClock.q) ∂P :=
    integral_sub (hintf t) hintc
  -- Fubini
  have hswap : ∫ ω, (∫ u in S, g (X u ω) ∂lebesgueClock.q) ∂P
      = ∫ u in S, (∫ ω, g (X u ω) ∂P) ∂lebesgueClock.q := by
    haveI hprodfin : IsFiniteMeasure (P.prod (lebesgueClock.q.restrict S)) :=
      @MeasureTheory.Measure.prod.instIsFiniteMeasure Ω ℝ≥0 m lebesgueClock.measurableSpace
        P (lebesgueClock.q.restrict S) inferInstance hfinS
    refine integral_integral_swap (μ := P) (ν := lebesgueClock.q.restrict S)
      (f := fun (ω : Ω) (u : ℝ≥0) ↦ g (X u ω)) ?_
    exact @integrable_of_abs_le _ _ _ hprodfin _ ((hX g hgm).comp measurable_swap) _
      (fun p ↦ hgb (X p.2 p.1))
  have hmeasF : Measurable fun u : ℝ≥0 ↦ ∫ ω, g (X u ω) ∂P :=
    (stronglyMeasurable_integral_comp (α := Ω) (β := ℝ≥0) (γ := ℝ) (𝕜 := ℝ) P
      (W := fun ω u ↦ g (X u ω)) ((hX g hgm).comp measurable_swap) measurable_id).measurable
  have hclock : ∫ u in S, (∫ ω, g (X u ω) ∂P) ∂lebesgueClock.q
      = ∫ r in (0:ℝ)..(t:ℝ), ∫ ω, g (X (Real.toNNReal r) ω) ∂P := by
    rw [hSeq, integral_lebesgueClock_Ioc bot_le hmeasF]
    norm_num
  rw [← hclock, ← hswap]
  have := hexp
  rw [hYt] at this
  rw [integral_congr_ae (Filter.Eventually.of_forall hY0)] at this
  linarith [this]

/-- **A bounded factor of the past passes through a martingale increment.**  This is the only
step of the conditional argument that is not bookkeeping:
`condExp_stronglyMeasurable_mul_of_bound` pulls the factor out of the conditional expectation,
and `integral_condExp` -- which asks for no integrability, both sides being `0` when there is
none -- puts the expectation back. -/
theorem integral_mul_eq_of_martingale [IsFiniteMeasure P] {Y : ℝ≥0 → Ω → ℝ}
    (hmart : Martingale Y F P) {s u : ℝ≥0} (hsu : s ≤ u) (hint : Integrable (Y u) P)
    {K : Ω → ℝ} {B : ℝ} (hK : StronglyMeasurable[F s] K) (hKb : ∀ ω, |K ω| ≤ B) :
    ∫ ω, K ω * Y u ω ∂P = ∫ ω, K ω * Y s ω ∂P := by
  have hpull : P[(K * Y u : Ω → ℝ) | F s] =ᵐ[P] K * P[Y u | F s] :=
    condExp_stronglyMeasurable_mul_of_bound (F.le s) hK hint B
      (Filter.Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hKb ω)
  calc ∫ ω, K ω * Y u ω ∂P
      = ∫ ω, (P[(K * Y u : Ω → ℝ) | F s]) ω ∂P := (integral_condExp (F.le s)).symm
    _ = ∫ ω, K ω * (P[Y u | F s]) ω ∂P := integral_congr_ae hpull
    _ = ∫ ω, K ω * Y s ω ∂P :=
        integral_congr_ae ((hmart.2 s u hsu).mono fun ω hω ↦ by simp only [hω])

/-- **The martingale identity against a bounded factor of the past, read from an arbitrary
starting time.**  This is the conditional form of
`integral_sub_eq_intervalIntegral_of_isMPSolution`, and it is what carries the Picard iteration
from the one dimensional distributions to the finite dimensional ones: `K` is any bounded
`𝓕 s`-measurable functional, and the increment is read from `s` onwards.  The unconditional
statement is the case `K = 1`, `s = 0`. -/
theorem integral_mul_sub_eq_intervalIntegral_of_isMPSolution [IsProbabilityMeasure P]
    [IsMarkovKernel mu] (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) {s : ℝ≥0} {K : Ω → ℝ} {B : ℝ}
    (hK : StronglyMeasurable[F s] K) (hKb : ∀ ω, |K ω| ≤ B) (t : ℝ≥0) :
    (∫ ω, K ω * f (X (s + t) ω) ∂P) - ∫ ω, K ω * f (X s ω) ∂P
      = ∫ r in (0:ℝ)..(t:ℝ), ∫ ω, K ω * jumpApply lam mu f (X (s + Real.toNNReal r) ω) ∂P := by
  have hKm : Measurable K := (hK.mono (F.le s)).measurable
  set g := jumpApply lam mu f with hgdef
  have hgm : Measurable g := measurable_jumpApply hlam hf hC
  have hgb : ∀ x, |g x| ≤ 2 * L * C := fun x ↦ abs_jumpApply_le hlam0 hL hC x
  -- the compensating windows, measurable and bounded by the length of the window
  have hfin : ∀ a b : ℝ≥0, IsFiniteMeasure
      (lebesgueClock.q.restrict (lebesgueClock.interval Clock.Conv.optional a b)) := fun a b ↦
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.2 (lebesgueClock.measure_interval_ne_top _ _ _)⟩
  have hwinm : ∀ a b : ℝ≥0, Measurable fun ω ↦
      ∫ u in lebesgueClock.interval Clock.Conv.optional a b, g (X u ω) ∂lebesgueClock.q := by
    intro a b
    haveI := hfin a b
    exact (@stronglyMeasurable_integral_comp ℝ≥0 lebesgueClock.measurableSpace Ω m ℝ _ ℝ _
      (lebesgueClock.q.restrict (lebesgueClock.interval Clock.Conv.optional a b)) inferInstance
      (fun u ω ↦ g (X u ω)) (hX g hgm) id measurable_id).measurable
  have hwinb : ∀ (a b : ℝ≥0), a ≤ b → ∀ ω : Ω,
      |∫ u in lebesgueClock.interval Clock.Conv.optional a b,
        g (X u ω) ∂lebesgueClock.q| ≤ 2 * L * C * ((b : ℝ) - (a : ℝ)) := by
    intro a b hab ω
    have hab' : (0:ℝ) ≤ (b : ℝ) - (a : ℝ) := by
      have := (NNReal.coe_le_coe).2 hab; linarith
    have hlt : lebesgueClock.q (lebesgueClock.interval Clock.Conv.optional a b) < ⊤ :=
      lt_top_iff_ne_top.2 (lebesgueClock.measure_interval_ne_top _ _ _)
    have hmass : lebesgueClock.q.real (lebesgueClock.interval Clock.Conv.optional a b)
        = (b : ℝ) - (a : ℝ) := by
      rw [measureReal_def, lebesgueClock_interval_optional_eq, lebesgueClock_apply_Ioc,
        ENNReal.toReal_ofReal hab']
    have hle := norm_setIntegral_le_of_norm_le_const (μ := lebesgueClock.q)
      (s := lebesgueClock.interval Clock.Conv.optional a b) (f := fun u ↦ g (X u ω))
      (C := 2 * L * C) hlt (fun u _ ↦ by simpa only [Real.norm_eq_abs] using hgb (X u ω))
    rwa [Real.norm_eq_abs, hmass] at hle
  -- the compensated test process
  set Y : ℝ≥0 → Ω → ℝ := fun j ω ↦ f (X j ω) -
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j, g (X u ω) ∂lebesgueClock.q with hYdef
  have hmart : Martingale Y F P := hsol Y ⟨(f, g), mem_jumpOperator hf hC, fun j ω ↦ rfl⟩
  set V : Ω → ℝ := fun ω ↦
    ∫ u in lebesgueClock.interval Clock.Conv.optional s (s + t), g (X u ω) ∂lebesgueClock.q
    with hVdef
  have hVm : Measurable V := hwinm s (s + t)
  have hVb : ∀ ω, |V ω| ≤ 2 * L * C * (t : ℝ) := fun ω ↦
    (hwinb s (s + t) le_self_add ω).trans_eq (by push_cast; ring)
  -- the integrability bookkeeping
  have hintf : ∀ j : ℝ≥0, Integrable (fun ω ↦ f (X j ω)) P := fun j ↦
    integrable_of_abs_le ((hX f hf).comp (measurable_const.prodMk measurable_id))
      (fun ω ↦ hC (X j ω))
  have hintw : ∀ j : ℝ≥0, Integrable (fun ω ↦
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j, g (X u ω) ∂lebesgueClock.q) P :=
    fun j ↦ integrable_of_abs_le (hwinm ⊥ j) (hwinb ⊥ j bot_le)
  have hintY : ∀ j : ℝ≥0, Integrable (Y j) P := fun j ↦ (hintf j).sub (hintw j)
  have hmulb : ∀ (a b : ℝ) (u v : ℝ), |u| ≤ a → |v| ≤ b → 0 ≤ a → |u * v| ≤ a * b := by
    intro a b u v hu hv ha
    rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) ha
  have hintKf : ∀ j : ℝ≥0, Integrable (fun ω ↦ K ω * f (X j ω)) P := fun j ↦
    integrable_of_abs_le (hKm.mul ((hX f hf).comp (measurable_const.prodMk measurable_id)))
      (fun ω ↦ hmulb B C _ _ (hKb ω) (hC _) ((abs_nonneg _).trans (hKb ω)))
  have hintKw : ∀ j : ℝ≥0, Integrable (fun ω ↦ K ω *
      ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j, g (X u ω) ∂lebesgueClock.q) P :=
    fun j ↦ integrable_of_abs_le (hKm.mul (hwinm ⊥ j))
      (fun ω ↦ hmulb B _ _ _ (hKb ω) (hwinb ⊥ j bot_le ω) ((abs_nonneg _).trans (hKb ω)))
  have hintKV : Integrable (fun ω ↦ K ω * V ω) P :=
    integrable_of_abs_le (hKm.mul hVm) (fun ω ↦ hmulb B _ _ _ (hKb ω) (hVb ω) ((abs_nonneg _).trans (hKb ω)))
  have hintKY : ∀ j : ℝ≥0, Integrable (fun ω ↦ K ω * Y j ω) P := fun j ↦ by
    have hrw : (fun ω ↦ K ω * Y j ω) = fun ω ↦ K ω * f (X j ω) - K ω *
        ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ j, g (X u ω) ∂lebesgueClock.q := by
      funext ω; simp only [hYdef]; ring
    rw [hrw]; exact (hintKf j).sub (hintKw j)
  -- the increment of the test process, at every sample point
  have hZ : ∀ ω : Ω, Measurable[lebesgueClock.measurableSpace] fun u ↦ g (X u ω) := fun ω ↦
    (hX g hgm).comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ω : Ω, Y (s + t) ω - Y s ω = f (X (s + t) ω) - f (X s ω) - V ω := fun ω ↦
    mpFamily_sub_of_measurable_path (Q := lebesgueClock) (fun j ω ↦ rfl)
      (fun x ↦ by simpa only [Real.norm_eq_abs] using hgb x) le_self_add (hZ ω)
  -- the martingale property, tested against `K`
  have hkey : ∫ ω, K ω * Y (s + t) ω ∂P = ∫ ω, K ω * Y s ω ∂P :=
    integral_mul_eq_of_martingale hmart le_self_add (hintY (s + t)) hK hKb
  have hcalc : (∫ ω, K ω * f (X (s + t) ω) ∂P) - (∫ ω, K ω * f (X s ω) ∂P)
      = ∫ ω, K ω * V ω ∂P := by
    have h1 : ∫ ω, (K ω * Y (s + t) ω - K ω * Y s ω) ∂P = 0 := by
      rw [integral_sub (hintKY (s + t)) (hintKY s), hkey, sub_self]
    have h2 : ∀ ω, K ω * Y (s + t) ω - K ω * Y s ω
        = (K ω * f (X (s + t) ω) - K ω * f (X s ω)) - K ω * V ω := fun ω ↦ by
      calc K ω * Y (s + t) ω - K ω * Y s ω = K ω * (Y (s + t) ω - Y s ω) := by ring
        _ = K ω * (f (X (s + t) ω) - f (X s ω) - V ω) := by rw [hpt ω]
        _ = (K ω * f (X (s + t) ω) - K ω * f (X s ω)) - K ω * V ω := by ring
    have hI1 : Integrable (fun ω ↦ K ω * f (X (s + t) ω) - K ω * f (X s ω)) P :=
      (hintKf (s + t)).sub (hintKf s)
    rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_sub hI1 hintKV,
      integral_sub (hintKf (s + t)) (hintKf s)] at h1
    linarith
  -- the remainder, as a genuine interval integral
  have hΦm : Measurable fun u : ℝ≥0 ↦ ∫ ω, K ω * g (X u ω) ∂P :=
    (stronglyMeasurable_integral_comp (α := Ω) (β := ℝ≥0) (γ := ℝ) (𝕜 := ℝ) P
      (W := fun ω u ↦ K ω * g (X u ω))
      ((hKm.comp measurable_fst).mul ((hX g hgm).comp measurable_swap)) measurable_id).measurable
  have hVfub : ∫ ω, K ω * V ω ∂P
      = ∫ r in (0:ℝ)..(t:ℝ), ∫ ω, K ω * g (X (s + Real.toNNReal r) ω) ∂P := by
    haveI := hfin s (s + t)
    haveI hprodfin : IsFiniteMeasure (P.prod (lebesgueClock.q.restrict
        (lebesgueClock.interval Clock.Conv.optional s (s + t)))) :=
      @MeasureTheory.Measure.prod.instIsFiniteMeasure Ω ℝ≥0 m lebesgueClock.measurableSpace
        P _ inferInstance (hfin s (s + t))
    have hin : ∀ ω, K ω * V ω
        = ∫ u in lebesgueClock.interval Clock.Conv.optional s (s + t), K ω * g (X u ω)
            ∂lebesgueClock.q := fun ω ↦ (integral_const_mul _ _).symm
    rw [integral_congr_ae (Filter.Eventually.of_forall hin)]
    have hswap : ∫ ω, (∫ u in lebesgueClock.interval Clock.Conv.optional s (s + t),
          K ω * g (X u ω) ∂lebesgueClock.q) ∂P
        = ∫ u in lebesgueClock.interval Clock.Conv.optional s (s + t),
          (∫ ω, K ω * g (X u ω) ∂P) ∂lebesgueClock.q := by
      refine integral_integral_swap (μ := P)
        (ν := lebesgueClock.q.restrict (lebesgueClock.interval Clock.Conv.optional s (s + t)))
        (f := fun (ω : Ω) (u : ℝ≥0) ↦ K ω * g (X u ω)) ?_
      exact @integrable_of_abs_le _ _ _ hprodfin _
        ((hKm.comp measurable_fst).mul ((hX g hgm).comp measurable_swap)) (B * (2 * L * C))
        (fun p ↦ hmulb B _ _ _ (hKb p.1) (hgb _) ((abs_nonneg _).trans (hKb p.1)))
    rw [hswap, lebesgueClock_interval_optional_eq, integral_lebesgueClock_Ioc le_self_add hΦm,
      show ((s + t : ℝ≥0) : ℝ) - (s : ℝ) = (t : ℝ) by push_cast; ring]
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hr
    rw [Real.toNNReal_add s.coe_nonneg hr.1, Real.toNNReal_coe]
  rw [hcalc, hVfub]

/-- A bounded measurable real function is interval integrable. -/
theorem intervalIntegrable_of_abs_le {F : ℝ → ℝ} (hF : Measurable F) {b : ℝ}
    (hb : ∀ x, |F x| ≤ b) (a c : ℝ) : IntervalIntegrable F volume a c :=
  ⟨integrableOn_of_bounded _ (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hF
      (fun x ↦ by simpa only [Real.norm_eq_abs] using hb x),
   integrableOn_of_bounded _ (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hF
      (fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)⟩

/-- The primitive of a monomial, in the shape the Picard iteration consumes. -/
theorem intervalIntegral_pow_div_factorial (T : ℝ) (hT : 0 ≤ T) (k : ℕ) (a : ℝ) :
    ∫ r in (0:ℝ)..T, (r ^ k / k.factorial) * a
      = (T ^ (k + 1) / (k + 1).factorial) * a := by
  have h1 : (fun r : ℝ ↦ (r ^ k / k.factorial) * a) = fun r : ℝ ↦ r ^ k * (a / k.factorial) := by
    funext r; ring
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [h1, intervalIntegral.integral_mul_const, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **The Picard iteration, in the abstract.**  The functional `I` stands for
`φ ↦ ∫ K · φ (X (s + ·))`, the expectation of a bounded functional of the state tested against a
bounded factor of the past; the three hypotheses are the bound, the joint measurability in the
time, and the recursion of the martingale identity.  Isolating them is what lets the *same*
induction serve the one dimensional distributions (`K = 1`, `s = 0`) and the conditional ones,
which is the whole of the step from one dimension to finitely many.

The induction runs over `n` and is generalised over `φ` and its bound, because its step applies
the hypothesis to `A φ` with the bound `2 L D`. -/
theorem abs_sub_sum_le_of_recursion [IsMarkovKernel mu] (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) {I : ℝ≥0 → (E → ℝ) → ℝ} {M : ℝ}
    (hIb : ∀ (φ : E → ℝ) (D : ℝ), (∀ x, |φ x| ≤ D) → ∀ t : ℝ≥0, |I t φ| ≤ M * D)
    (hIm : ∀ φ : E → ℝ, Measurable φ → Measurable fun r : ℝ ↦ I (Real.toNNReal r) φ)
    (hIrec : ∀ (φ : E → ℝ) (D : ℝ), Measurable φ → (∀ x, |φ x| ≤ D) → ∀ t : ℝ≥0,
      I t φ - I 0 φ = ∫ r in (0:ℝ)..(t:ℝ), I (Real.toNNReal r) (jumpApply lam mu φ))
    (n : ℕ) : ∀ (φ : E → ℝ) (D : ℝ), Measurable φ → (∀ x, |φ x| ≤ D) → ∀ t : ℝ≥0,
      |I t φ - ∑ k ∈ Finset.range n,
          ((t : ℝ) ^ k / k.factorial) * I 0 ((jumpApply lam mu)^[k] φ)|
        ≤ (2 * L * (t : ℝ)) ^ n / n.factorial * (M * D) := by
  induction n with
  | zero =>
      intro φ D hφ hD t
      simpa using hIb φ D hD t
  | succ n ih =>
      intro φ D hφ hD t
      have hAm : Measurable (jumpApply lam mu φ) := measurable_jumpApply hlam hφ hD
      have hAb : ∀ x, |jumpApply lam mu φ x| ≤ 2 * L * D := fun x ↦ abs_jumpApply_le hlam0 hL hD x
      have hT : (0:ℝ) ≤ (t : ℝ) := t.coe_nonneg
      -- the integrand of the remainder
      set w : ℝ → ℝ := fun r ↦ I (Real.toNNReal r) (jumpApply lam mu φ) with hwdef
      set c : ℕ → ℝ := fun k ↦ I 0 ((jumpApply lam mu)^[k] (jumpApply lam mu φ)) with hcdef
      have hwm : Measurable w := hIm _ hAm
      have hwb : ∀ r, |w r| ≤ M * (2 * L * D) := fun r ↦ hIb _ _ hAb _
      have hrec := hIrec φ D hφ hD t
      have hIH := ih (jumpApply lam mu φ) (2 * L * D) hAm hAb
      have hwint : IntervalIntegrable w volume 0 (t : ℝ) := intervalIntegrable_of_abs_le hwm hwb _ _
      have hpint : ∀ k : ℕ, IntervalIntegrable (fun r : ℝ ↦ (r ^ k / k.factorial) * c k)
          volume 0 (t : ℝ) := fun k ↦ (by fun_prop : Continuous _).intervalIntegrable _ _
      have hsint : IntervalIntegrable
          (fun r : ℝ ↦ ∑ k ∈ Finset.range n, (r ^ k / k.factorial) * c k) volume 0 (t : ℝ) :=
        (continuous_finset_sum _ fun k _ ↦ (by fun_prop : Continuous _)).intervalIntegrable _ _
      have hsplit : ∑ k ∈ Finset.range n, ((t : ℝ) ^ (k + 1) / (k + 1).factorial) * c k
          = ∫ r in (0:ℝ)..(t : ℝ), ∑ k ∈ Finset.range n, (r ^ k / k.factorial) * c k := by
        rw [intervalIntegral.integral_finset_sum (fun k _ ↦ hpint k)]
        exact Finset.sum_congr rfl fun k _ ↦ (intervalIntegral_pow_div_factorial _ hT k (c k)).symm
      have hgoal : I t φ - ∑ k ∈ Finset.range (n + 1),
            ((t : ℝ) ^ k / k.factorial) * I 0 ((jumpApply lam mu)^[k] φ)
          = ∫ r in (0:ℝ)..(t : ℝ), (w r - ∑ k ∈ Finset.range n, (r ^ k / k.factorial) * c k) := by
        rw [intervalIntegral.integral_sub hwint hsint, ← hsplit, Finset.sum_range_succ']
        simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, pow_zero,
          Nat.factorial_zero, Nat.cast_one, div_one, one_mul, ← hcdef]
        rw [show (∫ r in (0:ℝ)..(t : ℝ), w r) = I t φ - I 0 φ from hrec.symm]
        ring
      rw [hgoal]
      have hdom : ∀ r ∈ Set.Ioc (0:ℝ) (t : ℝ),
          |w r - ∑ k ∈ Finset.range n, (r ^ k / k.factorial) * c k|
            ≤ (r ^ n / n.factorial) * ((2 * L) ^ n * (M * (2 * L * D))) := by
        intro r hr
        have hr0 : (0:ℝ) ≤ r := le_of_lt hr.1
        have := hIH (Real.toNNReal r)
        rw [Real.coe_toNNReal r hr0] at this
        refine this.trans_eq ?_
        rw [mul_pow]
        ring
      have hgint : IntervalIntegrable
          (fun r : ℝ ↦ (r ^ n / n.factorial) * ((2 * L) ^ n * (M * (2 * L * D)))) volume
          0 (t : ℝ) := (by fun_prop : Continuous _).intervalIntegrable _ _
      have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ))
        (b := (t : ℝ)) (f := fun r ↦ w r - ∑ k ∈ Finset.range n, (r ^ k / k.factorial) * c k)
        (g := fun r ↦ (r ^ n / n.factorial) * ((2 * L) ^ n * (M * (2 * L * D)))) hT
        (Filter.Eventually.of_forall fun r hr ↦ by
          simpa only [Real.norm_eq_abs] using hdom r hr) hgint
      rw [Real.norm_eq_abs] at hle
      refine hle.trans_eq ?_
      rw [intervalIntegral_pow_div_factorial _ hT n ((2 * L) ^ n * (M * (2 * L * D)))]
      rw [mul_pow]
      ring

/-- **The Picard iteration.**  Any solution of the martingale problem has one dimensional
expectations agreeing with the exponential series up to the `n`-th remainder.  This is
`abs_sub_sum_le_of_recursion` for `K = 1` and `s = 0`. -/
theorem abs_integral_sub_sum_le_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    (n : ℕ) : ∀ (φ : E → ℝ) (D : ℝ), Measurable φ → (∀ x, |φ x| ≤ D) → ∀ t : ℝ≥0,
      |(∫ ω, φ (X t ω) ∂P) - ∑ k ∈ Finset.range n,
          ((t : ℝ) ^ k / k.factorial) * ∫ ω, ((jumpApply lam mu)^[k] φ) (X 0 ω) ∂P|
        ≤ (2 * L * (t : ℝ)) ^ n / n.factorial * D := by
  have key := abs_sub_sum_le_of_recursion (I := fun j ψ ↦ ∫ ω, ψ (X j ω) ∂P) (M := 1)
    hlam hlam0 hL
    (fun φ D hD j ↦ by simpa using abs_integral_le_of_abs_le (fun ω ↦ hD (X j ω)))
    (fun φ hφ ↦ (stronglyMeasurable_integral_comp (α := Ω) (β := ℝ) (γ := ℝ) (𝕜 := ℝ) P
        (W := fun ω r ↦ φ (X (Real.toNNReal r) ω))
        ((hX _ hφ).comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
        measurable_id).measurable)
    (fun φ D hφ hD j ↦
      integral_sub_eq_intervalIntegral_of_isMPSolution hlam hlam0 hL hX hsol hφ hD j) n
  simpa only [one_mul] using key

/-- **The Picard iteration, tested against a bounded factor of the past.**  This is
`abs_sub_sum_le_of_recursion` for the functional `φ ↦ ∫ K · φ (X (s + ·))`; the recursion it
consumes is `integral_mul_sub_eq_intervalIntegral_of_isMPSolution`. -/
theorem abs_integral_mul_sub_sum_le_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    {s : ℝ≥0} {K : Ω → ℝ} {B : ℝ} (hK : StronglyMeasurable[F s] K) (hKb : ∀ ω, |K ω| ≤ B)
    (n : ℕ) : ∀ (φ : E → ℝ) (D : ℝ), Measurable φ → (∀ x, |φ x| ≤ D) → ∀ t : ℝ≥0,
      |(∫ ω, K ω * φ (X (s + t) ω) ∂P) - ∑ k ∈ Finset.range n,
          ((t : ℝ) ^ k / k.factorial) * ∫ ω, K ω * ((jumpApply lam mu)^[k] φ) (X s ω) ∂P|
        ≤ (2 * L * (t : ℝ)) ^ n / n.factorial * (B * D) := by
  have hKm : Measurable K := (hK.mono (F.le s)).measurable
  have key := abs_sub_sum_le_of_recursion
    (I := fun j ψ ↦ ∫ ω, K ω * ψ (X (s + j) ω) ∂P) (M := B) hlam hlam0 hL
    (fun φ D hD j ↦ abs_integral_le_of_abs_le fun ω ↦ by
      rw [abs_mul]
      exact mul_le_mul (hKb ω) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hKb ω)))
    (fun φ hφ ↦ (stronglyMeasurable_integral_comp (α := Ω) (β := ℝ) (γ := ℝ) (𝕜 := ℝ) P
        (W := fun ω r ↦ K ω * φ (X (s + Real.toNNReal r) ω))
        ((hKm.comp measurable_fst).mul ((hX _ hφ).comp
          (((measurable_real_toNNReal.comp measurable_snd).const_add s).prodMk measurable_fst)))
        measurable_id).measurable)
    (fun φ D hφ hD j ↦ by
      simpa only [add_zero] using integral_mul_sub_eq_intervalIntegral_of_isMPSolution
        hlam hlam0 hL hX hsol hφ hD hK hKb j) n
  simpa only [add_zero] using key

/-- **The one dimensional distributions of any solution are the exponential series of the
generator applied to the initial law.**  This is the uniqueness half of
`exists_unique_of_bounded`: it fixes the law of `X t` for *every* solution of the martingale
problem, and it exhibits it as `nu.map (exp (t • A))` in the concrete shape `expJumpApply`. -/
theorem integral_eq_expJumpApply_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hX0 : Measurable (X 0))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    ∫ ω, f (X t ω) ∂P = ∫ x, expJumpApply lam mu (t : ℝ) f x ∂(P.map (X 0)) := by
  haveI : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map hX0.aemeasurable
  set A := jumpApply lam mu with hA
  set c : ℕ → ℝ := fun k ↦ ∫ ω, (A^[k] f) (X 0 ω) ∂P with hcdef
  have hmk : ∀ k, Measurable (A^[k] f) := fun k ↦
    measurable_iterate_jumpApply hlam hlam0 hL hf hC k
  have hbk : ∀ k x, |(A^[k] f) x| ≤ (2 * L) ^ k * C := fun k x ↦
    abs_iterate_jumpApply_le hlam0 hL hC k x
  have hck : ∀ k, |c k| ≤ (2 * L) ^ k * C := fun k ↦
    abs_integral_le_of_abs_le (fun ω ↦ hbk k (X 0 ω))
  have habs : (2 * L * |(t : ℝ)|) = 2 * L * (t : ℝ) := by rw [abs_of_nonneg t.coe_nonneg]
  -- the partial sums converge to the expectation
  have hsummable : Summable fun k : ℕ ↦ ((t : ℝ) ^ k / k.factorial) * c k :=
    Summable.of_norm_bounded ((Real.summable_pow_div_factorial (2 * L * |(t : ℝ)|)).mul_right C)
      fun k ↦ abs_series_term_le (hck k) (t : ℝ)
  have htends : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ((t : ℝ) ^ k / k.factorial) * c k)
      atTop (𝓝 (∫ ω, f (X t ω) ∂P)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (by simpa using (Real.summable_pow_div_factorial (2 * L * (t : ℝ))).tendsto_atTop_zero.mul_const C)
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_sub_sum_le_of_isMPSolution hlam hlam0 hL hX hsol n f C hf hC t
  have htsum : ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * c k = ∫ ω, f (X t ω) ∂P :=
    (hsummable.hasSum_iff_tendsto_nat.2 htends).tsum_eq
  -- the initial law
  have hmap : ∀ k, ∫ x, (A^[k] f) x ∂(P.map (X 0)) = c k := fun k ↦ by
    rw [hcdef, integral_map hX0.aemeasurable (hmk k).aestronglyMeasurable]
  -- the series may be integrated term by term
  have hint : ∀ k : ℕ, Integrable (fun x ↦ ((t : ℝ) ^ k / k.factorial) * (A^[k] f) x)
      (P.map (X 0)) := fun k ↦
    integrable_of_abs_le (measurable_const.mul (hmk k))
      (fun x ↦ abs_series_term_le (hbk k x) (t : ℝ))
  have hnormsum : Summable fun k : ℕ ↦
      ∫ x, ‖((t : ℝ) ^ k / k.factorial) * (A^[k] f) x‖ ∂(P.map (X 0)) := by
    refine Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun x ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial (2 * L * |(t : ℝ)|)).mul_right C)
    refine (abs_integral_le_of_abs_le (C := (2 * L * |(t : ℝ)|) ^ k / k.factorial * C)
      fun x ↦ ?_).trans' (le_abs_self _)
    rw [abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
    exact abs_series_term_le (hbk k x) (t : ℝ)
  have hswapint : ∑' k : ℕ, (∫ x, ((t : ℝ) ^ k / k.factorial) * (A^[k] f) x ∂(P.map (X 0)))
      = ∫ x, expJumpApply lam mu (t : ℝ) f x ∂(P.map (X 0)) :=
    integral_tsum_of_summable_integral_norm hint hnormsum
  rw [← htsum, ← hswapint]
  exact tsum_congr fun k ↦ by rw [integral_const_mul, hmap k]

/-- **Uniqueness in the one dimensional distributions.**  Two solutions of the martingale problem
for the same bounded jump generator, with the same initial law, have the same law at every time.
This is `exists_unique_of_bounded` read as a uniqueness statement; it does not mention the
constructed process, and the two solutions may live on different spaces. -/
theorem integral_eq_of_isMPSolution_of_map_eq [IsProbabilityMeasure P] [IsMarkovKernel mu]
    {Ω' : Type*} {m' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {F' : Filtration ℝ≥0 m'} {X' : ℝ≥0 → Ω' → E}
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hX0 : Measurable (X 0))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    (hX' : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω' ↦ h (X' p.1 p.2))
    (hX0' : Measurable (X' 0))
    (hsol' : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X')
      F' P')
    (hinit : P.map (X 0) = P'.map (X' 0))
    (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    ∫ ω, f (X t ω) ∂P = ∫ ω, f (X' t ω) ∂P' := by
  rw [integral_eq_expJumpApply_of_isMPSolution hlam hlam0 hL hX hX0 hsol hf hC t,
    integral_eq_expJumpApply_of_isMPSolution hlam hlam0 hL hX' hX0' hsol' hf hC t, hinit]

/-- **The conditional one dimensional distributions of any solution.**  Tested against an
arbitrary bounded `𝓕 s`-measurable factor `K`, the expectation of `f (X (s + t))` is the
expectation of the exponential series of the generator evaluated at the state at time `s`.  This
is the Markov property of *every* solution of the martingale problem, and it is the step that
carries the uniqueness from the one dimensional distributions to the finite dimensional ones:
`K` may be a product of test functions of finitely many earlier coordinates. -/
theorem integral_mul_eq_expJumpApply_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X) F P)
    {s : ℝ≥0} {K : Ω → ℝ} {B : ℝ} (hK : StronglyMeasurable[F s] K) (hKb : ∀ ω, |K ω| ≤ B)
    (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    ∫ ω, K ω * f (X (s + t) ω) ∂P = ∫ ω, K ω * expJumpApply lam mu (t : ℝ) f (X s ω) ∂P := by
  have hKm : Measurable K := (hK.mono (F.le s)).measurable
  set A := jumpApply lam mu with hA
  set c : ℕ → ℝ := fun k ↦ ∫ ω, K ω * (A^[k] f) (X s ω) ∂P with hcdef
  have hmk : ∀ k, Measurable (A^[k] f) := fun k ↦
    measurable_iterate_jumpApply hlam hlam0 hL hf hC k
  have hbk : ∀ k x, |(A^[k] f) x| ≤ (2 * L) ^ k * C := fun k x ↦
    abs_iterate_jumpApply_le hlam0 hL hC k x
  have hmXs : ∀ k, Measurable fun ω ↦ (A^[k] f) (X s ω) := fun k ↦
    (hX _ (hmk k)).comp (measurable_const.prodMk measurable_id)
  have hbKk : ∀ (k : ℕ) (ω : Ω), |K ω * (A^[k] f) (X s ω)| ≤ (2 * L) ^ k * (B * C) := by
    intro k ω
    rw [abs_mul]
    calc |K ω| * |(A^[k] f) (X s ω)| ≤ B * ((2 * L) ^ k * C) :=
          mul_le_mul (hKb ω) (hbk k _) (abs_nonneg _) ((abs_nonneg _).trans (hKb ω))
      _ = (2 * L) ^ k * (B * C) := by ring
  have hck : ∀ k, |c k| ≤ (2 * L) ^ k * (B * C) := fun k ↦
    abs_integral_le_of_abs_le (fun ω ↦ hbKk k ω)
  have hsummable : Summable fun k : ℕ ↦ ((t : ℝ) ^ k / k.factorial) * c k :=
    Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial (2 * L * |(t : ℝ)|)).mul_right (B * C))
      fun k ↦ abs_series_term_le (hck k) (t : ℝ)
  have htends : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ((t : ℝ) ^ k / k.factorial) * c k)
      atTop (𝓝 (∫ ω, K ω * f (X (s + t) ω) ∂P)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (by simpa using (Real.summable_pow_div_factorial
        (2 * L * (t : ℝ))).tendsto_atTop_zero.mul_const (B * C))
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_mul_sub_sum_le_of_isMPSolution hlam hlam0 hL hX hsol hK hKb n f C hf hC t
  have htsum : ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * c k = ∫ ω, K ω * f (X (s + t) ω) ∂P :=
    (hsummable.hasSum_iff_tendsto_nat.2 htends).tsum_eq
  -- the series may be integrated term by term
  have hint : ∀ k : ℕ,
      Integrable (fun ω ↦ ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω))) P := fun k ↦
    integrable_of_abs_le (measurable_const.mul (hKm.mul (hmXs k)))
      (fun ω ↦ abs_series_term_le (hbKk k ω) (t : ℝ))
  have hnormsum : Summable fun k : ℕ ↦
      ∫ ω, ‖((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω))‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun ω ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial (2 * L * |(t : ℝ)|)).mul_right (B * C))
    refine (abs_integral_le_of_abs_le (C := (2 * L * |(t : ℝ)|) ^ k / k.factorial * (B * C))
      fun ω ↦ ?_).trans' (le_abs_self _)
    rw [abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
    exact abs_series_term_le (hbKk k ω) (t : ℝ)
  have hswapint : ∑' k : ℕ, (∫ ω, ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω)) ∂P)
      = ∫ ω, ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω)) ∂P :=
    integral_tsum_of_summable_integral_norm hint hnormsum
  have hptw : ∀ ω, ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω))
      = K ω * expJumpApply lam mu (t : ℝ) f (X s ω) := by
    intro ω
    rw [expJumpApply, ← tsum_mul_left]
    exact tsum_congr fun k ↦ by ring
  rw [← htsum]
  calc ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * c k
      = ∑' k : ℕ, ∫ ω, ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω)) ∂P :=
        tsum_congr fun k ↦ by simp only [hcdef]; exact (integral_const_mul _ _).symm
    _ = ∫ ω, ∑' k : ℕ, ((t : ℝ) ^ k / k.factorial) * (K ω * (A^[k] f) (X s ω)) ∂P := hswapint
    _ = ∫ ω, K ω * expJumpApply lam mu (t : ℝ) f (X s ω) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hptw)

/-! ### From one coordinate to finitely many

A finite dimensional test variable is a product `∏ᵢ gᵢ (X sᵢ)` with `s₀ < s₁ < …`.  It is
recorded here as a **list of increments** `[(t₀, g₀), (t₁, g₁), …]`, read from a starting time:
that shape is what the induction of the Markov property consumes, because peeling the first
factor leaves a list of the same kind read from the later time.  A `Fin n`-indexed family would
have to reindex at every step. -/

/-- **The finite dimensional test variable along a list of time increments**, read from `s`. -/
def fddProd (Z : ℝ≥0 → Ω → E) : List (ℝ≥0 × (E → ℝ)) → ℝ≥0 → Ω → ℝ
  | [], _, _ => 1
  | (t, g) :: l, s, ω => g (Z (s + t) ω) * fddProd Z l (s + t) ω

/-- **The value the semigroup gives that test variable**: the exponential series of the generator,
nested along the list.  For a single pair this is `expJumpApply`; for a list it is the iterated
semigroup that the Markov property produces. -/
noncomputable def fddExp (lam : E → ℝ) (mu : Kernel E E) :
    List (ℝ≥0 × (E → ℝ)) → E → ℝ
  | [] => fun _ ↦ 1
  | (t, g) :: l => expJumpApply lam mu (t : ℝ) (fun y ↦ g y * fddExp lam mu l y)

/-- The nested semigroup value of a bounded measurable list is bounded and measurable.  Both
halves are proved at once because the induction step needs both of them for the tail. -/
theorem measurable_and_bdd_fddExp [IsMarkovKernel mu] (hlam : Measurable lam)
    (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L) :
    ∀ l : List (ℝ≥0 × (E → ℝ)), (∀ p ∈ l, Measurable p.2) →
      (∀ p ∈ l, ∃ D : ℝ, ∀ x, |p.2 x| ≤ D) →
      Measurable (fddExp lam mu l) ∧ ∃ D : ℝ, ∀ x, |fddExp lam mu l x| ≤ D := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨measurable_const, 1, fun x ↦ by simp [fddExp]⟩
  | cons p l ih =>
      intro hm hb
      obtain ⟨t, g⟩ := p
      have hgm : Measurable g := hm _ List.mem_cons_self
      obtain ⟨Dg, hgb⟩ := hb _ List.mem_cons_self
      obtain ⟨hEm, DE, hEb⟩ := ih (fun q hq ↦ hm q (List.mem_cons_of_mem _ hq))
        (fun q hq ↦ hb q (List.mem_cons_of_mem _ hq))
      have hhm : Measurable fun y ↦ g y * fddExp lam mu l y := hgm.mul hEm
      have hhb : ∀ y, |g y * fddExp lam mu l y| ≤ Dg * DE := fun y ↦ by
        rw [abs_mul]
        exact mul_le_mul (hgb y) (hEb y) (abs_nonneg _) ((abs_nonneg _).trans (hgb y))
      refine ⟨measurable_expJumpApply hlam hlam0 hL hhm hhb _,
        Real.exp (2 * L * |(t : ℝ)|) * (Dg * DE), fun x ↦ ?_⟩
      exact abs_expJumpApply_le hlam0 hL hhb (t : ℝ) x

/-- **The finite dimensional distributions of any solution, tested against a factor of the past.**
This is the induction over the number of coordinates: peeling the first factor turns the test
variable into one of the same kind read from the later time, with the peeled factor absorbed into
the past factor `K`, and `integral_mul_eq_expJumpApply_of_isMPSolution` then replaces the whole
tail by the nested semigroup value at the earlier time. -/
theorem integral_mul_fddProd_eq_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hXad : ∀ h : E → ℝ, Measurable h → ∀ u : ℝ≥0, StronglyMeasurable[F u] fun ω ↦ h (X u ω))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X)
      F P) :
    ∀ l : List (ℝ≥0 × (E → ℝ)), (∀ p ∈ l, Measurable p.2) →
      (∀ p ∈ l, ∃ D : ℝ, ∀ x, |p.2 x| ≤ D) →
      ∀ (s : ℝ≥0) (K : Ω → ℝ) (B : ℝ), StronglyMeasurable[F s] K → (∀ ω, |K ω| ≤ B) →
        ∫ ω, K ω * fddProd X l s ω ∂P = ∫ ω, K ω * fddExp lam mu l (X s ω) ∂P := by
  intro l
  induction l with
  | nil => intro _ _ s K B _ _; simp [fddProd, fddExp]
  | cons p l ih =>
      intro hm hb s K B hK hKb
      obtain ⟨t, g⟩ := p
      have hgm : Measurable g := hm _ List.mem_cons_self
      obtain ⟨Dg, hgb⟩ := hb _ List.mem_cons_self
      have hml : ∀ q ∈ l, Measurable q.2 := fun q hq ↦ hm q (List.mem_cons_of_mem _ hq)
      have hbl : ∀ q ∈ l, ∃ D : ℝ, ∀ x, |q.2 x| ≤ D := fun q hq ↦ hb q (List.mem_cons_of_mem _ hq)
      obtain ⟨hEm, DE, hEb⟩ := measurable_and_bdd_fddExp (mu := mu) hlam hlam0 hL l hml hbl
      -- the first factor joins the past factor
      have hKgm : StronglyMeasurable[F (s + t)] fun ω ↦ K ω * g (X (s + t) ω) :=
        (hK.mono (F.mono le_self_add)).mul (hXad g hgm (s + t))
      have hKgb : ∀ ω, |K ω * g (X (s + t) ω)| ≤ B * Dg := fun ω ↦ by
        rw [abs_mul]
        exact mul_le_mul (hKb ω) (hgb _) (abs_nonneg _) ((abs_nonneg _).trans (hKb ω))
      have hstep := ih hml hbl (s + t) (fun ω ↦ K ω * g (X (s + t) ω)) (B * Dg) hKgm hKgb
      -- the tail is replaced by the nested semigroup value at the earlier time
      have hhm : Measurable fun y ↦ g y * fddExp lam mu l y := hgm.mul hEm
      have hhb : ∀ y, |g y * fddExp lam mu l y| ≤ Dg * DE := fun y ↦ by
        rw [abs_mul]
        exact mul_le_mul (hgb y) (hEb y) (abs_nonneg _) ((abs_nonneg _).trans (hgb y))
      have hkey := integral_mul_eq_expJumpApply_of_isMPSolution (f := fun y ↦
        g y * fddExp lam mu l y) hlam hlam0 hL hX hsol hK hKb hhm hhb t
      calc ∫ ω, K ω * fddProd X ((t, g) :: l) s ω ∂P
          = ∫ ω, (K ω * g (X (s + t) ω)) * fddProd X l (s + t) ω ∂P := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            simp only [fddProd]; ring
        _ = ∫ ω, (K ω * g (X (s + t) ω)) * fddExp lam mu l (X (s + t) ω) ∂P := hstep
        _ = ∫ ω, K ω * (fun y ↦ g y * fddExp lam mu l y) (X (s + t) ω) ∂P := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            simp only []; ring
        _ = ∫ ω, K ω * expJumpApply lam mu (t : ℝ)
              (fun y ↦ g y * fddExp lam mu l y) (X s ω) ∂P := hkey
        _ = ∫ ω, K ω * fddExp lam mu ((t, g) :: l) (X s ω) ∂P := by simp only [fddExp]

/-- **The finite dimensional distributions of any solution are fixed by the initial law.**  This
is `exists_unique_of_bounded` in full: "exactly one solution" is a statement about the finite
dimensional distributions, and here they are computed from `nu` alone. -/
theorem integral_fddProd_eq_of_isMPSolution [IsProbabilityMeasure P] [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hXad : ∀ h : E → ℝ, Measurable h → ∀ u : ℝ≥0, StronglyMeasurable[F u] fun ω ↦ h (X u ω))
    (hX0 : Measurable (X 0))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X)
      F P)
    (l : List (ℝ≥0 × (E → ℝ))) (hm : ∀ p ∈ l, Measurable p.2)
    (hb : ∀ p ∈ l, ∃ D : ℝ, ∀ x, |p.2 x| ≤ D) :
    ∫ ω, fddProd X l 0 ω ∂P = ∫ x, fddExp lam mu l x ∂(P.map (X 0)) := by
  obtain ⟨hEm, DE, hEb⟩ := measurable_and_bdd_fddExp (mu := mu) hlam hlam0 hL l hm hb
  have key := integral_mul_fddProd_eq_of_isMPSolution hlam hlam0 hL hX hXad hsol l hm hb 0
    (fun _ ↦ (1 : ℝ)) 1 stronglyMeasurable_const (fun _ ↦ by norm_num)
  simp only [one_mul] at key
  rw [key, integral_map hX0.aemeasurable hEm.aestronglyMeasurable]

/-- **Uniqueness.**  Two solutions of the martingale problem for the same bounded jump generator,
with the same initial law, have the same finite dimensional distributions -- on two different
probability spaces.  This is the uniqueness half of `exists_unique_of_bounded`, and unlike
`integral_eq_of_isMPSolution_of_map_eq` it is not restricted to a single coordinate. -/
theorem integral_fddProd_eq_of_isMPSolution_of_map_eq [IsProbabilityMeasure P] [IsMarkovKernel mu]
    {Ω' : Type*} {m' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {F' : Filtration ℝ≥0 m'} {X' : ℝ≥0 → Ω' → E}
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 ≤ lam x) (hL : ∀ x, lam x ≤ L)
    (hX : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω ↦ h (X p.1 p.2))
    (hXad : ∀ h : E → ℝ, Measurable h → ∀ u : ℝ≥0, StronglyMeasurable[F u] fun ω ↦ h (X u ω))
    (hX0 : Measurable (X 0))
    (hsol : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X)
      F P)
    (hX' : ∀ h : E → ℝ, Measurable h → Measurable fun p : ℝ≥0 × Ω' ↦ h (X' p.1 p.2))
    (hXad' : ∀ h : E → ℝ, Measurable h → ∀ u : ℝ≥0, StronglyMeasurable[F' u] fun ω ↦ h (X' u ω))
    (hX0' : Measurable (X' 0))
    (hsol' : IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional X')
      F' P')
    (hinit : P.map (X 0) = P'.map (X' 0))
    (l : List (ℝ≥0 × (E → ℝ))) (hm : ∀ p ∈ l, Measurable p.2)
    (hb : ∀ p ∈ l, ∃ D : ℝ, ∀ x, |p.2 x| ≤ D) :
    ∫ ω, fddProd X l 0 ω ∂P = ∫ ω, fddProd X' l 0 ω ∂P' := by
  rw [integral_fddProd_eq_of_isMPSolution hlam hlam0 hL hX hXad hX0 hsol l hm hb,
    integral_fddProd_eq_of_isMPSolution hlam hlam0 hL hX' hXad' hX0' hsol' l hm hb, hinit]

/-- **The two hypotheses on the process are met by the constructed one, and are met globally.**
The joint measurability asked for by the uniqueness theorem is the one for the *full* σ-algebra,
not for the past, so it is `measurable_jumpProcess` composed with the coercion `ℝ≥0 → ℝ` and needs
none of `measurable_uncurry_jumpProcess`; the filtered version is what the compensator consumes
and is a different statement. -/
theorem measurable_uncurry_comp_jumpProcess (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) :
    Measurable fun p : ℝ≥0 × ((ℕ → E) × (ℕ → ℝ)) ↦ h (jumpProcess lam (p.1 : ℝ) p.2) :=
  hh.comp ((measurable_jumpProcess hlam).comp
    ((measurable_coe_nnreal_real.comp measurable_fst).prodMk measurable_snd))

/-- **The one dimensional distributions of the constructed jump process are the exponential
series applied to the initial law.**  This is the half of `exists_unique_of_bounded` that names
the process: `integral_eq_expJumpApply_of_isMPSolution` applies to *every* solution, and
`jumpProcess_isMPSolution` says the construction is one, so the two together compute the law of
`X t` from `nu` alone.  The initial law is `jumpMeasure_map_jumpProcess_zero`. -/
theorem jumpMeasure_integral_jumpProcess_eq_expJumpApply [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L)
    (nu : Measure E) [IsProbabilityMeasure nu] (hf : Measurable f) (hC : ∀ x, |f x| ≤ C)
    (t : ℝ≥0) :
    ∫ ω, f (jumpProcess lam (t : ℝ) ω) ∂(jumpMeasure mu nu)
      = ∫ x, expJumpApply lam mu (t : ℝ) f x ∂nu := by
  have hX0 : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpProcess lam (((0 : ℝ≥0) : ℝ)) ω :=
    (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)
  have hmap : (jumpMeasure mu nu).map (fun ω ↦ jumpProcess lam (((0 : ℝ≥0) : ℝ)) ω) = nu := by
    simpa only [NNReal.coe_zero] using jumpMeasure_map_jumpProcess_zero hlam0 mu nu
  have key := integral_eq_expJumpApply_of_isMPSolution (P := jumpMeasure mu nu)
    (X := fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (s : ℝ) ω) (F := jumpFiltration lam hlam)
    hlam (fun x ↦ (hlam0 x).le) hL
    (fun h hh ↦ measurable_uncurry_comp_jumpProcess hlam hh) hX0
    (jumpProcess_isMPSolution hlam hlam0 hL mu nu) hf hC t
  rw [key, hmap]

/-- **One coordinate of the nested semigroup is the exponential series**, so the finite
dimensional statements extend the one dimensional ones and do not merely sit beside them. -/
theorem fddExp_singleton (lam : E → ℝ) (mu : Kernel E E) (t : ℝ≥0) (g : E → ℝ) :
    fddExp lam mu [(t, g)] = expJumpApply lam mu (t : ℝ) g := by
  simp [fddExp]

omit [MeasurableSpace E] in
/-- One coordinate of the test variable is the test function at the single time. -/
theorem fddProd_singleton (Z : ℝ≥0 → Ω → E) (t : ℝ≥0) (g : E → ℝ) (s : ℝ≥0) (ω : Ω) :
    fddProd Z [(t, g)] s ω = g (Z (s + t) ω) := by
  simp [fddProd]

/-- **Every bounded functional of the current state of the jump process is adapted.**  This is the
hypothesis `hXad` of the finite dimensional uniqueness; for the constructed process it is
`measurable_naturalFiltration` read at `j = i`, the filtration being the natural one. -/
theorem stronglyMeasurable_jumpFiltration (hlam : Measurable lam) {h : E → ℝ}
    (hh : Measurable h) (u : ℝ≥0) :
    StronglyMeasurable[jumpFiltration lam hlam u] fun ω ↦ h (jumpProcess lam (u : ℝ) ω) :=
  (hh.comp (measurable_naturalFiltration
    (fun _ ↦ (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id))
    (le_refl u))).stronglyMeasurable

/-- **The finite dimensional distributions of the constructed jump process.**  Together with
`integral_fddProd_eq_of_isMPSolution_of_map_eq` this is `exists_unique_of_bounded` entire: the
constructed process is a solution, and every solution with the same initial law has these same
finite dimensional distributions. -/
theorem jumpMeasure_integral_fddProd_eq_fddExp [IsMarkovKernel mu]
    (hlam : Measurable lam) (hlam0 : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L)
    (nu : Measure E) [IsProbabilityMeasure nu]
    (l : List (ℝ≥0 × (E → ℝ))) (hm : ∀ p ∈ l, Measurable p.2)
    (hb : ∀ p ∈ l, ∃ D : ℝ, ∀ x, |p.2 x| ≤ D) :
    ∫ ω, fddProd (fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (s : ℝ) ω) l 0 ω ∂(jumpMeasure mu nu)
      = ∫ x, fddExp lam mu l x ∂nu := by
  have hX0 : Measurable fun ω : (ℕ → E) × (ℕ → ℝ) ↦ jumpProcess lam (((0 : ℝ≥0) : ℝ)) ω :=
    (measurable_jumpProcess hlam).comp (measurable_const.prodMk measurable_id)
  have hmap : (jumpMeasure mu nu).map (fun ω ↦ jumpProcess lam (((0 : ℝ≥0) : ℝ)) ω) = nu := by
    simpa only [NNReal.coe_zero] using jumpMeasure_map_jumpProcess_zero hlam0 mu nu
  have key := integral_fddProd_eq_of_isMPSolution (P := jumpMeasure mu nu)
    (X := fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (s : ℝ) ω) (F := jumpFiltration lam hlam)
    hlam (fun x ↦ (hlam0 x).le) hL
    (fun h hh ↦ measurable_uncurry_comp_jumpProcess hlam hh)
    (fun h hh u ↦ stronglyMeasurable_jumpFiltration hlam hh u) hX0
    (jumpProcess_isMPSolution hlam hlam0 hL mu nu) l hm hb
  rw [key, hmap]

end Uniqueness

/-! ## Acceptance example for Milestone 4: the Poisson process

`E = ℕ`, `lam ≡ 1`, `mu x = δ_{x+1}`.  This is the instance that checks Milestone 4, and it
checks two different things.  First, that the generator of `set:jumpdata` really *is* the forward
difference on this data: `jumpApply_poisson` is the computation the roadmap asks for before the
example is admitted, and if it came out as anything but `f (x + 1) - f x` the shape of
`set:jumpdata` would be the finding.  Second -- and this is what a milestone that only *names*
its example does not check -- that the six hypotheses of `jumpProcess_isMPSolution`
(`Measurable lam`, `0 < lam`, `lam ≤ L`, `IsMarkovKernel mu`, `IsProbabilityMeasure nu`,
`[MeasurableSpace E]`) are jointly satisfiable, so that the theorem is not vacuous.
`martingale_compensated_poisson` exhibits an actual martingale and not merely a solution
predicate.  Third, that the process the construction produces is the one it is named after:
`jumpMeasure_map_jumpProcess_poisson` identifies its one dimensional laws with Mathlib's
`ProbabilityTheory.poissonMeasure`, and that is the only statement here that could have come
out false. -/

section PoissonExample

/-- **The rate of the Poisson process**, constant `1`. -/
def poissonRate : ℕ → ℝ := fun _ ↦ 1

/-- **The jump kernel of the Poisson process**, the deterministic step `x ↦ x + 1`. -/
noncomputable def poissonKernel : Kernel ℕ ℕ :=
  Kernel.deterministic (fun x ↦ x + 1) (measurable_of_countable _)

instance : IsMarkovKernel poissonKernel :=
  Kernel.isMarkovKernel_deterministic (measurable_of_countable _)

theorem measurable_poissonRate : Measurable poissonRate := measurable_const

theorem poissonRate_pos (x : ℕ) : 0 < poissonRate x := zero_lt_one

theorem poissonRate_le_one (x : ℕ) : poissonRate x ≤ 1 := le_rfl

/-- **The generator of the Poisson jump data is the forward difference**,
`A f x = f (x + 1) - f x`.  The rate cancels because it is `1`, and the integral against the
kernel is an evaluation because the kernel is a Dirac measure. -/
theorem jumpApply_poisson (f : ℕ → ℝ) (x : ℕ) :
    jumpApply poissonRate poissonKernel f x = f (x + 1) - f x := by
  rw [jumpApply, poissonKernel, Kernel.deterministic_apply,
    integral_dirac (fun y ↦ f y - f x) (x + 1), poissonRate, one_mul]

/-- **The compensated increment of a bounded function along the Poisson process belongs to the
family of test processes.**  Written out, it is
`f (X t) - ∫_0^t (f (X u + 1) - f (X u)) du`, and no boundedness of `f` beyond the one the
operator itself carries is needed. -/
theorem mem_mpFamily_poisson {f : ℕ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    (fun (t : ℝ≥0) (ω : (ℕ → ℕ) × (ℕ → ℝ)) ↦ f (jumpProcess poissonRate (t : ℝ) ω)
        - ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
            (f (jumpProcess poissonRate (u : ℝ) ω + 1)
              - f (jumpProcess poissonRate (u : ℝ) ω)) ∂lebesgueClock.q)
      ∈ mpFamily (jumpOperator poissonRate poissonKernel) lebesgueClock Clock.Conv.optional
        (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess poissonRate (t : ℝ) ω) := by
  refine ⟨(f, jumpApply poissonRate poissonKernel f),
    mem_jumpOperator (measurable_of_countable f) hC, fun t ω ↦ ?_⟩
  simp only [jumpApply_poisson]

/-- **The Poisson process solves the martingale problem of the forward difference operator.**
This is `jumpProcess_isMPSolution` with `lam ≡ 1`, `mu x = δ_{x+1}` and `nu = δ_0`, and the
point of writing it out is that every hypothesis of that theorem is discharged here on data,
so that the theorem is shown to have an instance. -/
theorem poissonProcess_isMPSolution :
    IsMPSolution (mpFamily (jumpOperator poissonRate poissonKernel) lebesgueClock
        Clock.Conv.optional (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess poissonRate (t : ℝ) ω))
      (jumpFiltration poissonRate measurable_poissonRate)
      (jumpMeasure poissonKernel (Measure.dirac 0)) :=
  jumpProcess_isMPSolution measurable_poissonRate poissonRate_pos poissonRate_le_one
    poissonKernel (Measure.dirac 0)

/-- **A concrete martingale**, and not a solution predicate: for every bounded `f : ℕ → ℝ`, the
compensated increment `f (X t) - ∫_0^t (f (X u + 1) - f (X u)) du` of the Poisson process is a
martingale for its natural filtration. -/
theorem martingale_compensated_poisson {f : ℕ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Martingale (fun (t : ℝ≥0) (ω : (ℕ → ℕ) × (ℕ → ℝ)) ↦ f (jumpProcess poissonRate (t : ℝ) ω)
        - ∫ u in lebesgueClock.interval Clock.Conv.optional ⊥ t,
            (f (jumpProcess poissonRate (u : ℝ) ω + 1)
              - f (jumpProcess poissonRate (u : ℝ) ω)) ∂lebesgueClock.q)
      (jumpFiltration poissonRate measurable_poissonRate)
      (jumpMeasure poissonKernel (Measure.dirac 0)) :=
  poissonProcess_isMPSolution _ (mem_mpFamily_poisson hC)

/-! ### The independent control: the one dimensional laws are Mathlib's Poisson laws

Everything above instantiates the milestone on data.  What follows does not: it computes the law
of `X t` and compares it with `ProbabilityTheory.poissonMeasure`, into whose definition nothing
of `jumpTime`, `stepIndex` or `waitingMeasure` enters.  It is the only place where an error in
the construction would show.

The route is the one Milestone 4 names as the cheaper of the two, and it goes through
uniqueness rather than through the Erlang law of the `n`-th jump time -- Mathlib has the
densities of `expMeasure` and `gammaMeasure` but not their convolution.  So the law is read off
the exponential series, and the series is summed by the **Gregory--Newton formula**: the
generator here is Mathlib's forward difference operator `fwdDiff 1`, and
`shift_eq_sum_fwdDiff_iter` expands `f (x + k)` in its iterated differences.  What turns that
finite expansion into the Poisson sum is one Cauchy product with the exponential series. -/

/-- The iterated forward difference of a bounded function is bounded by `2 ^ n` times the bound.
Stated for `fwdDiff` and not for `jumpApply`, because it is `fwdDiff` that Mathlib's
Gregory--Newton formula is about; the induction is over the *pair* `(f, C)`, since the step
replaces `f` by `Δ f` and `C` by `2 * C`. -/
theorem abs_fwdDiff_iter_le {f : ℕ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℕ) :
    |(fwdDiff 1)^[n] f x| ≤ 2 ^ n * C := by
  induction n generalizing f C with
  | zero => simpa using hC x
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hstep : ∀ y, |fwdDiff 1 f y| ≤ 2 * C := by
        intro y
        rw [fwdDiff]
        calc |f (y + 1) - f y| ≤ |f (y + 1)| + |f y| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring
      calc |(fwdDiff 1)^[n] (fwdDiff 1 f) x| ≤ 2 ^ n * (2 * C) := ih hstep
        _ = 2 ^ (n + 1) * C := by ring

/-- **The exponential series of the forward difference is the Poisson sum.**  For bounded `f`
and every real `t`,
`∑' n, t^n/n! * (Δ^[n] f) x = ∑' k, exp (-t) * t^k/k! * f (x + k)`.

The proof is the Cauchy product of the series with `exp t = ∑' m, t^m/m!`: the `k`-th
antidiagonal sum is `t^k/k!` times `∑_{i ≤ k} C(k,i) * (Δ^[i] f) x`, which is `f (x + k)` by
`shift_eq_sum_fwdDiff_iter`.  No probability enters, and no restriction on the sign of `t`. -/
theorem tsum_fwdDiff_iter_eq {f : ℕ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : ℕ) :
    ∑' n : ℕ, (t ^ n / n.factorial) * (fwdDiff 1)^[n] f x
      = ∑' k : ℕ, (Real.exp (-t) * t ^ k / k.factorial) * f (x + k) := by
  set D : ℕ → ℝ := fun n ↦ (fwdDiff 1)^[n] f x with hDdef
  have hD : ∀ n, |D n| ≤ 2 ^ n * C := fun n ↦ abs_fwdDiff_iter_le hC n x
  -- the two series are absolutely summable
  have hsA : Summable fun n : ℕ ↦ ‖(t ^ n / n.factorial) * D n‖ := by
    refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (2 * |t|)).mul_right C)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    have hnn : (0:ℝ) ≤ |t| ^ n / n.factorial :=
      div_nonneg (pow_nonneg (abs_nonneg t) n) (Nat.cast_nonneg _)
    calc |t| ^ n / n.factorial * |D n| ≤ |t| ^ n / n.factorial * (2 ^ n * C) :=
          mul_le_mul_of_nonneg_left (hD n) hnn
      _ = (2 * |t|) ^ n / n.factorial * C := by rw [mul_pow]; ring
  have hsB : Summable fun m : ℕ ↦ ‖t ^ m / (m.factorial : ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
      (Real.summable_pow_div_factorial |t|)
    rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  -- the Cauchy product with the exponential series
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsB hsA
  have hexp : Real.exp t = ∑' m : ℕ, t ^ m / (m.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- each antidiagonal sum is the Gregory--Newton formula
  have hterm : ∀ k : ℕ, ∑ p ∈ Finset.antidiagonal k,
      (t ^ p.1 / (p.1.factorial : ℝ)) * ((t ^ p.2 / (p.2.factorial : ℝ)) * D p.2)
      = (t ^ k / (k.factorial : ℝ)) * f (x + k) := by
    intro k
    have hnewton : f (x + k) = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D i := by
      have h := shift_eq_sum_fwdDiff_iter (M := ℕ) (G := ℝ) 1 f k x
      simp only [smul_eq_mul, mul_one, nsmul_eq_mul] at h
      exact h
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hnewton, Finset.mul_sum,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hsub : k - (k - i) = i := Nat.sub_sub_self hik
    have hfac : (k.factorial : ℝ)
        = (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ))
        (Nat.choose_mul_factorial_mul_factorial hik).symm
    have hi0 : ((i.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have hk0 : (((k - i).factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - i))
    have hc0 : ((k.choose i : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hik).ne'
    have hpow : t ^ (k - i) * t ^ i = t ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hik]
    simp only [Nat.succ_sub_one, hsub]
    have hgroup : t ^ (k - i) / ((k - i).factorial : ℝ) * ((t ^ i / (i.factorial : ℝ)) * D i)
        = (t ^ (k - i) * t ^ i) * D i / (((k - i).factorial : ℝ) * (i.factorial : ℝ)) := by ring
    rw [hgroup, hpow, hfac]
    field_simp
  -- assemble
  rw [tsum_congr hterm, ← hexp] at hcauchy
  refine (?_ : ∑' k : ℕ, (Real.exp (-t) * t ^ k / k.factorial) * f (x + k) = _).symm
  calc ∑' k : ℕ, (Real.exp (-t) * t ^ k / k.factorial) * f (x + k)
      = Real.exp (-t) * ∑' k : ℕ, (t ^ k / (k.factorial : ℝ)) * f (x + k) := by
        rw [← tsum_mul_left]; exact tsum_congr fun k ↦ by ring
    _ = Real.exp (-t) * (Real.exp t * ∑' n : ℕ, (t ^ n / (n.factorial : ℝ)) * D n) := by
        rw [hcauchy]
    _ = ∑' n : ℕ, (t ^ n / (n.factorial : ℝ)) * D n := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **The generator of the Poisson jump data is Mathlib's forward difference operator.** -/
theorem jumpApply_poisson_eq_fwdDiff (f : ℕ → ℝ) :
    jumpApply poissonRate poissonKernel f = fwdDiff 1 f := by
  funext x
  rw [jumpApply_poisson]
  rfl

/-- The iterates agree, which is what carries the Gregory--Newton formula into `expJumpApply`. -/
theorem iterate_jumpApply_poisson (f : ℕ → ℝ) (n : ℕ) :
    (jumpApply poissonRate poissonKernel)^[n] f = (fwdDiff 1)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        jumpApply_poisson_eq_fwdDiff, ih]

/-- **The exponential series of the Poisson generator is the Poisson sum.** -/
theorem expJumpApply_poisson {f : ℕ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : ℕ) :
    expJumpApply poissonRate poissonKernel t f x
      = ∑' k : ℕ, (Real.exp (-t) * t ^ k / k.factorial) * f (x + k) := by
  rw [expJumpApply]
  simp only [iterate_jumpApply_poisson]
  exact tsum_fwdDiff_iter_eq hC t x

/-- **The one dimensional distributions of the constructed process are the Poisson laws.**
`(jumpMeasure poissonKernel δ_0).map (X t) = Po(t)`, with `Po` Mathlib's
`ProbabilityTheory.poissonMeasure`.  This is the independent control that the milestone asks
for: it compares the construction with a measure defined without any reference to it. -/
theorem jumpMeasure_map_jumpProcess_poisson (t : ℝ≥0) :
    (jumpMeasure poissonKernel (Measure.dirac 0)).map (jumpProcess poissonRate (t : ℝ))
      = poissonMeasure t := by
  have hXm : Measurable (jumpProcess poissonRate ((t : ℝ))) :=
    (measurable_jumpProcess measurable_poissonRate).comp (measurable_const.prodMk measurable_id)
  haveI : IsProbabilityMeasure ((jumpMeasure poissonKernel (Measure.dirac 0)).map
      (jumpProcess poissonRate (t : ℝ))) := Measure.isProbabilityMeasure_map hXm.aemeasurable
  refine ext_iff_measureReal_singleton.2 fun n ↦ ?_
  have hgm : Measurable (({n} : Set ℕ).indicator (1 : ℕ → ℝ)) := measurable_of_countable _
  have hgC : ∀ x : ℕ, |({n} : Set ℕ).indicator (1 : ℕ → ℝ) x| ≤ 1 := by
    intro x
    by_cases hx : x = n
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx]
  rw [← integral_indicator_one (measurableSet_singleton n),
    integral_map hXm.aemeasurable hgm.aestronglyMeasurable,
    jumpMeasure_integral_jumpProcess_eq_expJumpApply measurable_poissonRate poissonRate_pos
      poissonRate_le_one (Measure.dirac 0) hgm hgC t,
    integral_dirac _ 0, expJumpApply_poisson hgC (t : ℝ) 0, poissonMeasure_real_singleton,
    tsum_eq_single n (fun k hk ↦ by simp [Set.indicator_apply, hk])]
  simp

/-- **The finite dimensional machinery is not empty on this example, and it agrees with the one
dimensional answer already proved.**  Read on the one coordinate list,
`jumpMeasure_integral_fddProd_eq_fddExp` is `jumpMeasure_integral_jumpProcess_eq_expJumpApply`,
whose value at the Poisson data is `poissonMeasure t` by
`jumpMeasure_map_jumpProcess_poisson`. -/
example (t : ℝ≥0) (f : ℕ → ℝ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    ∫ ω, fddProd (fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess poissonRate (s : ℝ) ω) [(t, f)] 0 ω
        ∂(jumpMeasure poissonKernel (Measure.dirac 0))
      = ∫ x, expJumpApply poissonRate poissonKernel (t : ℝ) f x ∂(Measure.dirac (0 : ℕ)) := by
  rw [jumpMeasure_integral_fddProd_eq_fddExp (L := 1) measurable_poissonRate poissonRate_pos
      poissonRate_le_one (Measure.dirac 0) [(t, f)]
      (by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact measurable_of_countable _)
      (by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨C, hC⟩),
    fddExp_singleton]

end PoissonExample

/-! ## Second acceptance example for Milestone 4: the two state chain

`E = Bool`, `lam ≡ 1`, `mu x = δ_{!x}`, so that `A f x = f (!x) - f x` -- the matrix
`!![-1, 1; 1, -1]` on `Bool → ℝ`.  This is the smallest instance on which the exponential series
of Milestone 4 produces a **number**: started at `false`, the law at time `t` is
`((1 + exp (-2t))/2, (1 - exp (-2t))/2)`.

It checks something the Poisson example cannot.  There the generator is a *shift*, so every
iterate `A^[n] f` is again a difference of values of `f` and a sign error inside `A` would
propagate invisibly into a Poisson law of another mean; here the state space has two points,
the iterates cycle, and the answer `(1 - exp (-2t))/2` is one that no sign error in `jumpApply`
and no factor in `expJumpApply` leaves standing -- at `t = 0` it must be `0`, and as `t → ∞` it
must be `1/2` and not `1`. -/

section TwoStateExample

/-- **The rate of the two state chain**, constant `1`. -/
def flipRate : Bool → ℝ := fun _ ↦ 1

/-- **The jump kernel of the two state chain**, the deterministic flip. -/
noncomputable def flipKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun x ↦ !x) (measurable_of_countable _)

instance : IsMarkovKernel flipKernel :=
  Kernel.isMarkovKernel_deterministic (measurable_of_countable _)

theorem measurable_flipRate : Measurable flipRate := measurable_const

theorem flipRate_pos (x : Bool) : 0 < flipRate x := zero_lt_one

theorem flipRate_le_one (x : Bool) : flipRate x ≤ 1 := le_rfl

/-- **The generator of the two state chain is the flip difference**, `A f x = f (!x) - f x`. -/
theorem jumpApply_flip (f : Bool → ℝ) (x : Bool) :
    jumpApply flipRate flipKernel f x = f (!x) - f x := by
  rw [jumpApply, flipKernel, Kernel.deterministic_apply,
    integral_dirac (fun y ↦ f y - f x) (!x), flipRate, one_mul]

/-- **The iterates cycle with a factor `-2`.**  This is the eigenvalue of
`!![-1, 1; 1, -1]` on the antisymmetric part, and it is what makes the answer below `exp (-2t)`
and not `exp (-t)`. -/
theorem iterate_jumpApply_flip (f : Bool → ℝ) (n : ℕ) (x : Bool) :
    (jumpApply flipRate flipKernel)^[n + 1] f x = (-2) ^ n * (f (!x) - f x) := by
  induction n generalizing x with
  | zero => simpa using jumpApply_flip f x
  | succ n ih =>
      rw [Function.iterate_succ_apply', jumpApply_flip, ih (!x), ih x]
      simp only [Bool.not_not]
      ring

/-- **The exponential series of the two state generator, in closed form.** -/
theorem expJumpApply_flip {f : Bool → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (t : ℝ) (x : Bool) :
    expJumpApply flipRate flipKernel t f x
      = f x + (1 - Real.exp (-2 * t)) / 2 * (f (!x) - f x) := by
  have hsum : Summable fun n : ℕ ↦
      (t ^ n / n.factorial) * (jumpApply flipRate flipKernel)^[n] f x :=
    summable_expJumpApply (L := 1) (fun y ↦ (flipRate_pos y).le) flipRate_le_one hC t x
  have hsumA : Summable fun m : ℕ ↦ (-2 * t) ^ m / (m.factorial : ℝ) :=
    Real.summable_pow_div_factorial (-2 * t)
  have hexpa : Real.exp (-2 * t) = ∑' m : ℕ, (-2 * t) ^ m / (m.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have htail : ∑' n : ℕ, (-2 * t) ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ)
      = Real.exp (-2 * t) - 1 := by
    have h := hsumA.tsum_eq_zero_add
    rw [← hexpa] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    linarith
  have hiter : ∀ n : ℕ, (t ^ (n + 1) / ((n + 1).factorial : ℝ))
        * (jumpApply flipRate flipKernel)^[n + 1] f x
      = (-(1 : ℝ) / 2 * (f (!x) - f x)) * ((-2 * t) ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ)) := by
    intro n
    rw [iterate_jumpApply_flip f n x, mul_pow]
    ring
  rw [expJumpApply, hsum.tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    Function.iterate_zero_apply]
  rw [tsum_congr hiter, tsum_mul_left, htail]
  ring

/-- **The one dimensional law of the two state chain, as a number.**  Started at `false`, the
probability of being at `true` at time `t` is `(1 - exp (-2t))/2`.  It is `0` at `t = 0` and
tends to `1/2`, which is what the acceptance example of Milestone 4 asks a reader to check; the
complementary value `(1 + exp (-2t))/2` is the mass of `{false}`, the measure being a
probability measure. -/
theorem jumpMeasure_map_jumpProcess_flip (t : ℝ≥0) :
    ((jumpMeasure flipKernel (Measure.dirac false)).map
        (jumpProcess flipRate (t : ℝ))).real {true}
      = (1 - Real.exp (-2 * (t : ℝ))) / 2 := by
  have hXm : Measurable (jumpProcess flipRate ((t : ℝ))) :=
    (measurable_jumpProcess measurable_flipRate).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable (({true} : Set Bool).indicator (1 : Bool → ℝ)) :=
    measurable_of_countable _
  have hgC : ∀ x : Bool, |({true} : Set Bool).indicator (1 : Bool → ℝ) x| ≤ 1 := by
    intro x
    by_cases hx : x = true
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx]
  rw [← integral_indicator_one (measurableSet_singleton true),
    integral_map hXm.aemeasurable hgm.aestronglyMeasurable,
    jumpMeasure_integral_jumpProcess_eq_expJumpApply measurable_flipRate flipRate_pos
      flipRate_le_one (Measure.dirac false) hgm hgC t,
    integral_dirac _ false, expJumpApply_flip hgC (t : ℝ) false]
  simp

/-- The chain starts where it is started: at `t = 0` the closed form above is `0`.  This is the
cheapest probe there is on a formula with an exponential in it, and it is written down because a
formula that is only *stated* is not checked. -/
example : ((jumpMeasure flipKernel (Measure.dirac false)).map
    (jumpProcess flipRate ((0 : ℝ≥0) : ℝ))).real {true} = 0 := by
  rw [jumpMeasure_map_jumpProcess_flip 0]
  norm_num

/-- **The two coordinate law of the two state chain, as a number.**  Started at `false`, the
probability of being at `true` at time `t` *and* at time `t + u` is
`(1 - exp (-2t))/2 · (1 + exp (-2u))/2`: the one dimensional law at `t` times the probability of
staying put over the increment `u`.

This is the only probe in the file on the **order** in which `fddExp` nests the semigroup, and it
is the reason it is written down: `fddExp_singleton` cannot see that order, and a `fddExp` that
nested the other way round would give `(1 - exp (-2u))/2 · (1 + exp (-2t))/2` here, which is a
different number as soon as `t ≠ u`.  The two degenerations check the two ends: at `u = 0` the
value is `(1 - exp (-2t))/2`, the one dimensional law, and at `t = 0` it is `0`. -/
theorem jumpMeasure_integral_fddProd_flip (t u : ℝ≥0) :
    ∫ ω, fddProd (fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess flipRate (s : ℝ) ω)
        [(t, ({true} : Set Bool).indicator (1 : Bool → ℝ)),
          (u, ({true} : Set Bool).indicator (1 : Bool → ℝ))] 0 ω
        ∂(jumpMeasure flipKernel (Measure.dirac false))
      = (1 - Real.exp (-2 * (t : ℝ))) / 2 * ((1 + Real.exp (-2 * (u : ℝ))) / 2) := by
  set g : Bool → ℝ := ({true} : Set Bool).indicator (1 : Bool → ℝ) with hgdef
  have hgm : Measurable g := measurable_of_countable _
  have hgt : g true = 1 := by simp [hgdef]
  have hgf : g false = 0 := by simp [hgdef]
  have hgC : ∀ x : Bool, |g x| ≤ 1 := by
    intro x; cases x <;> simp [hgt, hgf]
  set a : ℝ := (1 - Real.exp (-2 * (u : ℝ))) / 2 with hadef
  set h : Bool → ℝ := fun y ↦ g y * (g y + a * (g (!y) - g y)) with hhdef
  have hht : h true = 1 - a := by simp only [hhdef, hgt, hgf, Bool.not_true]; ring
  have hhf : h false = 0 := by simp only [hhdef, hgf]; ring
  have hhC : ∀ y : Bool, |h y| ≤ |1 - a| := by
    intro y
    cases y
    · rw [hhf, abs_zero]; exact abs_nonneg _
    · rw [hht]
  have hexpu : expJumpApply flipRate flipKernel (u : ℝ) g
      = fun y ↦ g y + a * (g (!y) - g y) := by
    funext y; exact expJumpApply_flip hgC (u : ℝ) y
  have hfdd : fddExp flipRate flipKernel [(t, g), (u, g)]
      = expJumpApply flipRate flipKernel (t : ℝ) h := by
    show expJumpApply flipRate flipKernel (t : ℝ)
      (fun y ↦ g y * fddExp flipRate flipKernel [(u, g)] y) = _
    rw [fddExp_singleton, hexpu, hhdef]
  rw [jumpMeasure_integral_fddProd_eq_fddExp (L := 1) measurable_flipRate flipRate_pos
      flipRate_le_one (Measure.dirac false) [(t, g), (u, g)]
      (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> exact hgm)
      (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> exact ⟨1, hgC⟩),
    integral_dirac _ false, hfdd, expJumpApply_flip hhC (t : ℝ) false, hhf, Bool.not_false, hht,
    hadef]
  ring

/-- The two degenerations of the two coordinate law, written down because a formula that is only
*stated* is not checked: at `u = 0` it collapses to the one dimensional law, and at `t = 0` the
chain has not moved. -/
example (t : ℝ≥0) : ∫ ω, fddProd (fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess flipRate (s : ℝ) ω)
    [(t, ({true} : Set Bool).indicator (1 : Bool → ℝ)),
      (0, ({true} : Set Bool).indicator (1 : Bool → ℝ))] 0 ω
    ∂(jumpMeasure flipKernel (Measure.dirac false))
      = (1 - Real.exp (-2 * (t : ℝ))) / 2 := by
  rw [jumpMeasure_integral_fddProd_flip t 0]
  norm_num

example (u : ℝ≥0) : ∫ ω, fddProd (fun s : ℝ≥0 ↦ fun ω ↦ jumpProcess flipRate (s : ℝ) ω)
    [(0, ({true} : Set Bool).indicator (1 : Bool → ℝ)),
      (u, ({true} : Set Bool).indicator (1 : Bool → ℝ))] 0 ω
    ∂(jumpMeasure flipKernel (Measure.dirac false)) = 0 := by
  rw [jumpMeasure_integral_fddProd_flip 0 u]
  norm_num

end TwoStateExample
