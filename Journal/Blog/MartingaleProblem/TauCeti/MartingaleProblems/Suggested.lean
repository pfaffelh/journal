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

/-!
# Suggested signatures for the martingale problems roadmap

Prototypes only. The abstract layer takes a family of test processes and never
mentions a state space; the Markovian layer specialises it.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-07.  Every declaration elaborates; 9 declarations carry `sorry`, and
every one of those `sorry`s is a **proof**.  The first proof of the
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
