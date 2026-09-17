/-
Scratch development for the middle step of
`isQuasiLeftContinuous_of_isRegularizingClass` (Milestone 9): the almost sure
limit of `f (X_{σ n})` is the conditional expectation of `f (X_{σ'})` for
`⨆ n, 𝓕_{σ n}`.

`ae_eq_condExp_iSup_of_tendsto` is proved in `Suggested.lean`, section
`LevyUpward`; it is stubbed here so that this file stands against Mathlib alone.
Everything below the stub is the work of this run.
-/
import Mathlib

open Filter Topology MeasureTheory Set

open scoped NNReal ENNReal

variable {ι : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
variable {Ω : Type*} {m : MeasurableSpace Ω} {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- STUB: proved in `Suggested.lean`, section `LevyUpward`. -/
theorem ae_eq_condExp_iSup_of_tendsto {ℱ : Filtration ℕ m} {μ : Measure Ω}
    [IsFiniteMeasure μ] {W A : Ω → 𝕂} {a Z : ℕ → Ω → 𝕂}
    (hZ : Tendsto (fun n ↦ ∫ ω, ‖Z n ω‖ ∂μ) atTop (𝓝 0))
    (hdec : ∀ n, a n =ᵐ[μ] fun ω ↦ (μ[W | ℱ n]) ω + (μ[Z n | ℱ n]) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ a n ω) atTop (𝓝 (A ω))) :
    A =ᵐ[μ] μ[W | ⨆ n, ℱ n] := sorry

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
/-- The filtration of a nondecreasing sequence of stopping times, and the only
place at which the stopping times of quasi-left-continuity are read as a
filtration indexed by `ℕ`. -/
def stoppingFiltration {𝓕 : Filtration ι m} {σ : ℕ → Ω → WithTop ι}
    (hσ : ∀ n, IsStoppingTime 𝓕 (σ n)) (hmono : Monotone σ) : Filtration ℕ m where
  seq n := (hσ n).measurableSpace
  mono' a b hab := (hσ a).measurableSpace_mono (hσ b) (hmono hab)
  le' n := (hσ n).measurableSpace_le

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] in
@[simp]
theorem stoppingFiltration_apply {𝓕 : Filtration ι m} {σ : ℕ → Ω → WithTop ι}
    (hσ : ∀ n, IsStoppingTime 𝓕 (σ n)) (hmono : Monotone σ) (n : ℕ) :
    stoppingFiltration hσ hmono n = (hσ n).measurableSpace := rfl

omit [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E] [MeasurableSpace E] in
/-- **The middle step of `isQuasiLeftContinuous_of_isRegularizingClass`.**  Where
`f ∘ X` splits as `Y + C` at all times at once, optional sampling turns the
stopped `Y` into a conditional expectation, conditional Jensen kills the stopped
increments of `C`, and Lévy's upward theorem identifies the almost sure limit of
`f (X_{σ n})` as the conditional expectation of `f (X_{σ'})`.

**No stopping time occurs**, and none has to: the filtration is an arbitrary
`ℱ : Filtration ℕ m`, the two places where the stopping times would be read are
the hypotheses `hOS` and `hCm`, and `σ`, `σ'` enter only through
`stoppedValue`, which is evaluation at `(σ ω).untopA`.  `stoppingFiltration`
above is what supplies `ℱ` at the point of use.

`hCm` is the hypothesis that `IsCompensatorFor` does **not** give: it says
`StronglyAdapted`, and adaptedness at a stopping time is progressive
measurability, exactly as `stoppedValue_ae_eq_condExp` asks of `Y`. -/
theorem ae_eq_condExp_iSup_stoppedValue {X : ι → Ω → E} {ℱ : Filtration ℕ m}
    {P : Measure Ω} [IsFiniteMeasure P] {f : E → 𝕂} {Y C : ι → Ω → 𝕂}
    {σ : ℕ → Ω → WithTop ι} {σ' : Ω → WithTop ι} {A : Ω → 𝕂}
    (hdec : ∀ᵐ ω ∂P, ∀ t : ι, f (X t ω) = Y t ω + C t ω)
    (hOS : ∀ n, stoppedValue Y (σ n) =ᵐ[P] P[stoppedValue Y σ' | ℱ n])
    (hCm : ∀ n, StronglyMeasurable[ℱ n] (stoppedValue C (σ n)))
    (hYi : Integrable (stoppedValue Y σ') P)
    (hCi : ∀ n, Integrable (stoppedValue C (σ n)) P)
    (hCi' : Integrable (stoppedValue C σ') P)
    (hZ : Tendsto (fun n ↦ ∫ ω, ‖stoppedValue C σ' ω - stoppedValue C (σ n) ω‖ ∂P)
      atTop (𝓝 0))
    (hA : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f (stoppedValue X (σ n) ω)) atTop (𝓝 (A ω))) :
    A =ᵐ[P] P[fun ω ↦ f (stoppedValue X σ' ω) | ⨆ n, ℱ n] := by
  set W : Ω → 𝕂 := fun ω ↦ f (stoppedValue X σ' ω) with hW
  set Z : ℕ → Ω → 𝕂 := fun n ω ↦ stoppedValue C (σ n) ω - stoppedValue C σ' ω with hZdef
  -- the decomposition, read at `σ n` and at `σ'`
  have hdn : ∀ n, ∀ᵐ ω ∂P,
      f (stoppedValue X (σ n) ω) = stoppedValue Y (σ n) ω + stoppedValue C (σ n) ω := by
    intro n
    filter_upwards [hdec] with ω hω
    exact hω _
  have hd' : ∀ᵐ ω ∂P, W ω = stoppedValue Y σ' ω + stoppedValue C σ' ω := by
    filter_upwards [hdec] with ω hω
    exact hω _
  -- the conditional expectation of `W`
  have hcW : ∀ n, P[W | ℱ n] =ᵐ[P]
      stoppedValue Y (σ n) + P[stoppedValue C σ' | ℱ n] := by
    intro n
    have e1 : P[W | ℱ n] =ᵐ[P] P[stoppedValue Y σ' + stoppedValue C σ' | ℱ n] :=
      condExp_congr_ae (by filter_upwards [hd'] with ω hω using hω)
    have e2 : P[stoppedValue Y σ' + stoppedValue C σ' | ℱ n]
        =ᵐ[P] P[stoppedValue Y σ' | ℱ n] + P[stoppedValue C σ' | ℱ n] :=
      condExp_add hYi hCi' _
    have e3 : P[stoppedValue Y σ' | ℱ n] + P[stoppedValue C σ' | ℱ n]
        =ᵐ[P] stoppedValue Y (σ n) + P[stoppedValue C σ' | ℱ n] := by
      filter_upwards [hOS n] with ω hω
      simp only [Pi.add_apply, hω]
    exact (e1.trans e2).trans e3
  -- the conditional expectation of the perturbation
  have hcZ : ∀ n, P[Z n | ℱ n] =ᵐ[P]
      stoppedValue C (σ n) - P[stoppedValue C σ' | ℱ n] := by
    intro n
    have e1 : P[Z n | ℱ n]
        =ᵐ[P] P[stoppedValue C (σ n) | ℱ n] - P[stoppedValue C σ' | ℱ n] :=
      condExp_sub (hCi n) hCi' _
    have e2 : P[stoppedValue C (σ n) | ℱ n] - P[stoppedValue C σ' | ℱ n]
        =ᵐ[P] stoppedValue C (σ n) - P[stoppedValue C σ' | ℱ n] := by
      rw [condExp_of_stronglyMeasurable (ℱ.le n) (hCm n) (hCi n)]
    exact e1.trans e2
  refine ae_eq_condExp_iSup_of_tendsto (ℱ := ℱ) (W := W) (A := A)
    (a := fun n ω ↦ f (stoppedValue X (σ n) ω)) (Z := Z) ?_ ?_ hA
  · refine hZ.congr fun n ↦ integral_congr_ae (.of_forall fun ω ↦ ?_)
    show ‖stoppedValue C σ' ω - stoppedValue C (σ n) ω‖
      = ‖stoppedValue C (σ n) ω - stoppedValue C σ' ω‖
    exact norm_sub_rev _ _
  · intro n
    filter_upwards [hdn n, hcW n, hcZ n] with ω h1 h2 h3
    rw [h1, h2, h3]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
