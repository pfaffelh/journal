/-
Scratch development for `IsCompensatorFor.ae_forall_decomposition` and
`IsCompensatorFor.decomposition_stoppedValue` (Milestone 9).  Stands against
Mathlib alone: `IsCompensatorFor` is not used here, only the fields that the
lifting reads, so that the statement can be iterated without the surrounding
file.
-/
import Mathlib

open Filter Topology MeasureTheory Set

open scoped NNReal ENNReal

variable {ι : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
variable {Ω : Type*} {m : MeasurableSpace Ω} {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

omit [OrderBot ι] [OrderTopology ι] [TopologicalSpace E] [MeasurableSpace E] in
/-- The lifting of an identity that holds, for each time separately, almost
surely, to one that holds almost surely for all times at once. -/
theorem ae_forall_eq_of_right_dense
    {P : Measure Ω} {D : Set ι} {X : ι → Ω → E} {f : E → 𝕂} {Y C : ι → Ω → 𝕂}
    (hDcount : D.Countable)
    (hD : ∀ t : ι, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot)
    (hdec : ∀ t ∈ D, ∀ᵐ ω ∂P, f (X t ω) = Y t ω + C t ω)
    (hXr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ f (X s ω)) (D ∩ Set.Ioi t) t)
    (hYr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ Y s ω) (D ∩ Set.Ioi t) t)
    (hCr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ C s ω) (D ∩ Set.Ioi t) t) :
    ∀ᵐ ω ∂P, ∀ t : ι, f (X t ω) = Y t ω + C t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ t ∈ D, f (X t ω) = Y t ω + C t ω := (ae_ball_iff hDcount).2 hdec
  filter_upwards [hall, hXr, hYr, hCr] with ω hω hXω hYω hCω t
  rcases hD t with ht | ht
  · exact hω t ht
  · have h1 : Tendsto (fun s ↦ f (X s ω)) (𝓝[D ∩ Set.Ioi t] t) (𝓝 (f (X t ω))) := hXω t
    have h2 : Tendsto (fun s ↦ Y s ω + C s ω) (𝓝[D ∩ Set.Ioi t] t) (𝓝 (Y t ω + C t ω)) :=
      (hYω t).add (hCω t)
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hω s hs.1

omit [OrderTopology ι] [TopologicalSpace E] [MeasurableSpace E] in
/-- The stopped form: no measurability and no stopping time property of `σ`. -/
theorem ae_eq_stoppedValue_of_right_dense
    {P : Measure Ω} {D : Set ι} {X : ι → Ω → E} {f : E → 𝕂} {Y C : ι → Ω → 𝕂}
    (hDcount : D.Countable)
    (hD : ∀ t : ι, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot)
    (hdec : ∀ t ∈ D, ∀ᵐ ω ∂P, f (X t ω) = Y t ω + C t ω)
    (hXr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ f (X s ω)) (D ∩ Set.Ioi t) t)
    (hYr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ Y s ω) (D ∩ Set.Ioi t) t)
    (hCr : ∀ᵐ ω ∂P, ∀ t : ι, ContinuousWithinAt (fun s ↦ C s ω) (D ∩ Set.Ioi t) t)
    (σ : Ω → WithTop ι) :
    ∀ᵐ ω ∂P, f (stoppedValue X σ ω) = stoppedValue Y σ ω + stoppedValue C σ ω := by
  filter_upwards [ae_forall_eq_of_right_dense hDcount hD hdec hXr hYr hCr] with ω hω
  exact hω _

/-! ### The witness that the right continuity of `Y` does not follow -/

/-- Local copy of `IsCompensatorFor` for the scratch file. -/
structure IsCompensatorFor' [OrderBot ι] (X : ι → Ω → E) (𝓕 : Filtration ι m) (P : Measure Ω)
    (D : Set ι) (f : E → 𝕂) (Y C : ι → Ω → 𝕂) : Prop where
  stronglyAdapted : StronglyAdapted 𝓕 C
  decomposition : ∀ t : ι, ∀ᵐ ω ∂P, f (X t ω) = Y t ω + C t ω
  exists_limits : ∀ᵐ ω ∂P, ∀ t : ι,
    (∃ l : 𝕂, Tendsto (fun s ↦ C s ω) (𝓝[D ∩ Set.Iio t] t) (𝓝 l)) ∧
      ∃ l : 𝕂, Tendsto (fun s ↦ C s ω) (𝓝[D ∩ Set.Ioi t] t) (𝓝 l)
  l1_rightContinuous : ∀ t : ι,
    Tendsto (fun s ↦ ∫⁻ ω, ‖C s ω - C t ω‖ₑ ∂P) (𝓝[>] t) (𝓝 0)

/-- A countable set that approximates every point of `ℝ≥0` from the right. -/
theorem exists_countable_right_dense :
    ∃ D : Set ℝ≥0, D.Countable ∧ ∀ t : ℝ≥0, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine ⟨D, hDc, fun t ↦ Or.inr ?_⟩
  rw [← mem_closure_iff_nhdsWithin_neBot, Set.inter_comm]
  refine closure_minimal (hDd.open_subset_closure_inter isOpen_Ioi) isClosed_closure ?_
  rw [closure_Ioi]
  exact Set.mem_Ici.2 le_rfl

/-- With `X` constant, `f = 0` and `C = 0` every hypothesis of
`ae_forall_eq_of_right_dense` except `hYr` holds, and the conclusion fails. -/
noncomputable def badY : ℝ≥0 → ℝ → ℝ := fun t ω ↦ if (t : ℝ) = ω then 1 else 0

theorem badY_ae_eq_zero (t : ℝ≥0) :
    ∀ᵐ ω ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), badY t ω = 0 := by
  have hz : (volume.restrict (Set.Icc (0 : ℝ) 1)) {(t : ℝ)} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null Set.inter_subset_left (by simp)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hz
  by_contra hne
  rw [Set.mem_singleton_iff] at hne
  exact hω (by simp [badY, Ne.symm hne])

theorem not_ae_forall_badY_eq_zero :
    ¬ ∀ᵐ ω ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ t : ℝ≥0, badY t ω = 0 := by
  rw [ae_iff]
  intro h
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ {ω : ℝ | ¬ ∀ t : ℝ≥0, badY t ω = 0} := by
    intro ω hω hcon
    have h2 := hcon ω.toNNReal
    simp [badY, Real.coe_toNNReal ω hω.1] at h2
  have h1 : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) = 1 := by
    rw [Measure.restrict_apply_self, Real.volume_Icc]
    norm_num
  have hle := measure_mono (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) hsub
  rw [h1, h] at hle
  simp at hle

theorem isCompensatorFor_badY (D : Set ℝ≥0) :
    IsCompensatorFor' (fun (_ : ℝ≥0) (_ : ℝ) ↦ ())
      (⊥ : Filtration ℝ≥0 (inferInstance : MeasurableSpace ℝ))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) D (fun _ ↦ (0 : ℝ)) badY 0 where
  stronglyAdapted := fun _ ↦ stronglyMeasurable_zero
  decomposition := fun t ↦ by
    filter_upwards [badY_ae_eq_zero t] with ω hω
    simp [hω]
  exists_limits := .of_forall fun _ _ ↦ ⟨⟨0, tendsto_const_nhds⟩, ⟨0, tendsto_const_nhds⟩⟩
  l1_rightContinuous := fun _ ↦ by simp
