import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace AtomConvWitness

open AtomWitness

/-- Integrals against the clock with a single atom are evaluations at the atom. -/
theorem setIntegral_atomClock (u : ℝ≥0) (S : Set ℝ≥0) (F : ℝ≥0 → ℝ) :
    ∫ s in S, F s ∂(atomClock u).q = S.indicator F u := by
  let _ : MeasurableSpace ℝ≥0 := ⊤
  have hdisc : DiscreteMeasurableSpace ℝ≥0 := ⟨fun _ ↦ trivial⟩
  change ∫ s in S, F s ∂(Measure.dirac u) = S.indicator F u
  classical
  rw [@restrict_dirac' ℝ≥0 ⊤ S u trivial (Classical.dec _)]
  split_ifs with h
  · rw [integral_dirac' F u (Measurable.of_discrete (f := F)).stronglyMeasurable,
      Set.indicator_of_mem h]
  · rw [integral_zero_measure, Set.indicator_of_notMem h]

/-- The deterministic path that jumps from `0` to `1` at time `1`. -/
noncomputable def stepPath {Ω : Type*} : ℝ≥0 → Ω → ℝ := fun t _ ↦ if 1 ≤ t then 1 else 0

/-- In the **optional** convention the test process of `(id, id)` along `stepPath` vanishes: the
compensator `∫_{(0,t]} X dδ₁ = 1_{t ≥ 1}` is the path itself. -/
theorem mpProcess_optional_stepPath {Ω : Type*} :
    mpProcess (atomClock (1 : ℝ≥0)) .optional (stepPath (Ω := Ω)) id id = 0 := by
  funext t ω
  simp only [mpProcess, setIntegral_atomClock, Pi.zero_apply, id, stepPath]
  by_cases h : (1 : ℝ≥0) ≤ t
  · rw [Set.indicator_of_mem (show (1 : ℝ≥0) ∈ (atomClock (1 : ℝ≥0)).interval .optional ⊥ t from
      ⟨h, by simp⟩)]
    simp [h]
  · rw [Set.indicator_of_notMem (fun hm : (1 : ℝ≥0) ∈ _ ↦ h hm.1)]
    simp [h]

/-- In the **predictable** convention it is the indicator of `{1}`: the compensator
`∫_{[0,t)} X dδ₁ = 1_{t > 1}` lags the path by the atom. -/
theorem mpProcess_predictable_stepPath {Ω : Type*} (t : ℝ≥0) (ω : Ω) :
    mpProcess (atomClock (1 : ℝ≥0)) .predictable (stepPath (Ω := Ω)) id id t ω
      = if t = 1 then 1 else 0 := by
  simp only [mpProcess, setIntegral_atomClock, id, stepPath]
  by_cases h : (1 : ℝ≥0) < t
  · rw [Set.indicator_of_mem (show (1 : ℝ≥0) ∈ (atomClock (1 : ℝ≥0)).interval .predictable ⊥ t
      from ⟨h, by simp⟩)]
    simp [h.le, h.ne']
  · rw [Set.indicator_of_notMem (fun hm : (1 : ℝ≥0) ∈ _ ↦ h hm.1)]
    by_cases h1 : t = 1
    · simp [h1]
    · have : ¬ (1 : ℝ≥0) ≤ t := fun h' ↦ h (lt_of_le_of_ne h' (Ne.symm h1))
      simp [this, h1]

/-- **A clock with an atom, where the two conventions give different solutions.**  For the clock
`δ₁` on `ℝ≥0`, the operator `{(id, id)}` and the deterministic path `1_{t ≥ 1}`, every probability
measure and every filtration solve the problem in the optional convention, and none in the
predictable one.  This is the manuscript's `ex:atomicdiscontinuity`, and it is why the convention
is a parameter of `mpFamily`. -/
theorem isMPSolutionFor_optional_and_not_predictable {Ω : Type*} {m : MeasurableSpace Ω}
    (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsMPSolutionFor {((id : ℝ → ℝ), (id : ℝ → ℝ))} (atomClock (1 : ℝ≥0)) .optional
        (stepPath (Ω := Ω)) 𝓖 P ∧
      ¬ IsMPSolutionFor {((id : ℝ → ℝ), (id : ℝ → ℝ))} (atomClock (1 : ℝ≥0)) .predictable
        (stepPath (Ω := Ω)) 𝓖 P := by
  constructor
  · rw [IsMPSolutionFor, mpFamily_eq_image_mpProcess]
    rintro _ ⟨p, hp, rfl⟩
    rw [Set.mem_singleton_iff] at hp
    subst hp
    dsimp only
    rw [mpProcess_optional_stepPath]
    exact martingale_zero _ _ _
  · intro h
    rw [IsMPSolutionFor, mpFamily_eq_image_mpProcess] at h
    have hm := h _ ⟨_, Set.mem_singleton _, rfl⟩
    have h1 := hm.setIntegral_eq (show (1 : ℝ≥0) ≤ 2 by norm_num) MeasurableSet.univ
    simp only [mpProcess_predictable_stepPath, Measure.restrict_univ] at h1
    norm_num at h1

end AtomConvWitness
