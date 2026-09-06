/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Order.LeftRightLim

/-!
# Suggested signatures for the martingale problems roadmap

Prototypes only. The abstract layer takes a family of test processes and never
mentions a state space; the Markovian layer specialises it.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-06.  Every declaration elaborates; 37 declarations, 11 of them carrying
`sorry`, and every one of those `sorry`s is a **proof**.  The first proof of the
file is `IsQuasiLeftContinuous.ae_eq_leftLim`, and it needed the statement
corrected first: under `¬ IsMin t` alone it is false.  No statement in this
file is `True` or `sorry` any more: the drafts of Milestones 3, 5, 9 and 10 were
turned into propositions on 2026-09-06.  `Shift` now takes the coordinate maps
`π` as a parameter, so that its compatibility field can be stated at all;
`IsDetermining`, `IsRegularizingClass` and `IsQuasiLeftContinuous` say what the
roadmap says; and the hypothesis (a) of `mpSolution_of_tendsto` is convergence
in distribution one variable at a time, as the manuscript's remark on the
topology free form of the theorem prescribes.
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
      Disjoint (Q.interval c s t) (Q.interval c t u) := sorry

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

/-- The finite dimensional criterion, `isMPSolutionFor_iff_forall_fdd` of the
roadmap: solving the martingale problem is an identity among finitely many
coordinates.  It is what turns every later theorem into a statement about finite
dimensional distributions, and it is the reason the index needs no order
structure beyond a preorder.

The filtration must be the natural one of `X`: the right hand side tests only
against the coordinates, so for a larger filtration the equivalence fails in the
direction from right to left.  That hypothesis is `h𝓕`. -/
theorem isMPSolution_iff_forall_fdd [OrderBot ι] {A : Set ((E → 𝕂) × (E → 𝕂))}
    {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E} {𝓕 : Filtration ι m}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hA : ∀ p ∈ A, (Measurable p.1 ∧ ∃ b, ∀ x, ‖p.1 x‖ ≤ b) ∧
      Measurable p.2 ∧ ∃ b, ∀ x, ‖p.2 x‖ ≤ b)
    (hX : ∀ t, Measurable (X t))
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
    (hX : ∀ t, Measurable (X t))
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

/-- The sharpness, as a named example and not as a remark: an atom of the clock
at a point `u` approachable from the left is a fixed time of discontinuity, so
the existence of a càdlàg modification -- which holds for **every** clock -- and
quasi-left-continuity separate exactly at the atoms.  The witness is a fair coin
flipped at `u`, constant on either side of it, over `E = Bool`. -/
theorem not_isQuasiLeftContinuous_of_atom (u : ι)
    (hu : ∃ s : ℕ → ι, StrictMono s ∧ (∀ n, s n < u) ∧ Tendsto s atTop (𝓝 u)) :
    ∃ (Ω' : Type) (m' : MeasurableSpace Ω') (P : @Measure Ω' m')
      (𝓕 : @Filtration Ω' ι _ m') (Q : Clock ι) (c : Clock.Conv)
      (A : Set ((Bool → ℝ) × (Bool → ℝ))) (X : ι → Ω' → Bool),
      Q.q {u} ≠ 0 ∧ @IsMPSolution ι _ Ω' m' ℝ _ (mpFamily A Q c X) 𝓕 P ∧
        ¬ IsQuasiLeftContinuous X 𝓕 P := sorry

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
