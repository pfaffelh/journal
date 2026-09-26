import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BumpWitness

/-- The bump sequence `min 1 (n · d(x, Uᶜ))` for `U = (-1, 1)`: `0` off `U`, increasing to `1` on
`U`. -/
noncomputable def bump (n : ℕ) (x : ℝ) : ℝ := min 1 (n * Metric.infDist x (Set.Ioo (-1) 1)ᶜ)

theorem norm_bump_le (n : ℕ) (x : ℝ) : ‖bump n x‖ ≤ 1 := by
  have h0 : 0 ≤ bump n x :=
    le_min zero_le_one (mul_nonneg n.cast_nonneg Metric.infDist_nonneg)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact min_le_left _ _

theorem tendsto_bump (x : ℝ) :
    Tendsto (fun n ↦ bump n x) atTop (𝓝 ((Set.Ioo (-1 : ℝ) 1).indicator 1 x)) := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    have hne : ((Set.Ioo (-1 : ℝ) 1)ᶜ).Nonempty := ⟨2, by norm_num⟩
    have hpos : 0 < Metric.infDist x (Set.Ioo (-1 : ℝ) 1)ᶜ :=
      (isOpen_Ioo.isClosed_compl.notMem_iff_infDist_pos hne).1 (not_not.2 hx)
    have htop : Tendsto (fun n : ℕ ↦ (n : ℝ) * Metric.infDist x (Set.Ioo (-1) 1)ᶜ) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hpos
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [htop.eventually_ge_atTop 1] with n hn
    exact (min_eq_left hn).symm
  · rw [Set.indicator_of_notMem hx]
    have h0 : Metric.infDist x (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 := Metric.infDist_zero_of_mem hx
    refine tendsto_const_nhds.congr fun n ↦ ?_
    simp [bump, h0]

variable {ι : Type*} [Preorder ι] [OrderBot ι] {Ω : Type*} {m : MeasurableSpace Ω}

/-- **`insert_of_forall_norm_le` against the indicator.**  A solution for an operator containing
the bumps `(bump n, 0)` solves for `insert (1_{(-1,1)}, 0)`, without any closure construction:
the one sequence suffices.  This is the single use Ethier–Kurtz make of the bounded pointwise
closure (Theorem 4.3.8). -/
theorem isMPSolutionFor_insert_indicator {A : Set ((ℝ → ℝ) × (ℝ → ℝ))} {Q : Clock ι}
    {c : Clock.Conv} {X : ι → Ω → ℝ} {𝓖 : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P]
    (hA : IsMPSolutionFor A Q c X 𝓖 P) (hbump : ∀ n, (bump n, (0 : ℝ → ℝ)) ∈ A) :
    IsMPSolutionFor (insert ((Set.Ioo (-1 : ℝ) 1).indicator 1, 0) A) Q c X 𝓖 P :=
  hA.insert_of_forall_norm_le (p := fun n ↦ (bump n, 0)) hbump tendsto_bump
    (fun _ ↦ tendsto_const_nhds) (C := 1) norm_bump_le (fun _ _ ↦ by simp)
    (fun _ _ ↦ stronglyMeasurable_const)

end BumpWitness
