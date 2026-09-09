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

/-!
# Suggested signatures for the martingale problems roadmap

Prototypes only. The abstract layer takes a family of test processes and never
mentions a state space; the Markovian layer specialises it.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-09.  Every declaration elaborates; 10 declarations carry `sorry`, and
every one of those `sorry`s is a **proof**.  The last two blocks of the file are
Milestone 4; the only `sorry` in them is the conditional expectation of
`jumpProcess_isMPSolution`, whose adaptedness half is proved.  The first, `IsStepPath`, was added on 2026-09-09:
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
forces.  The first
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

/-- **`thm:jumpMP`: the jump process solves the martingale problem of its generator.**  This is
the goal of Milestone 4 and the first solution of a martingale problem in this file that is a
solution and not a counterexample.

Everything except the conditional expectation is in place: `stronglyAdapted_mpFamily_jumpProcess`
is the adaptedness, `jumpMeasure_map_jumpProcess_zero` the initial law, and `expMeasure_Ioi_add`
the memorylessness on which the conditional expectation will rest. -/
theorem jumpProcess_isMPSolution {lam : E → ℝ} (hlam : Measurable lam) {L : ℝ}
    (hlam0 : ∀ x, 0 < lam x) (hL : ∀ x, lam x ≤ L) (mu : Kernel E E) [IsMarkovKernel mu]
    (nu : Measure E) [IsProbabilityMeasure nu] :
    IsMPSolution (mpFamily (jumpOperator lam mu) lebesgueClock Clock.Conv.optional
        (fun t : ℝ≥0 ↦ fun ω ↦ jumpProcess lam (t : ℝ) ω))
      (jumpFiltration lam hlam) (jumpMeasure mu nu) := sorry

end JumpFiltration

end JumpConstruction
