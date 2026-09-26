import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {ι : Type*} [Preorder ι] {Ω : Type*} {m : MeasurableSpace Ω}
  {E : Type*} [MeasurableSpace E] {𝕂 : Type*} [RCLike 𝕂]

/-- **An `L¹` limit of martingales is a martingale**, once the limit is adapted.  Adaptedness is a
hypothesis and not a conclusion: an `L¹` limit of `𝓖 t`-measurable functions is only almost
everywhere equal to one, and the filtration is not assumed complete. -/
theorem MeasureTheory.martingale_of_tendsto_eLpNorm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {𝓖 : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P]
    {Z : ℕ → ι → Ω → F} {Y : ι → Ω → F} (hZ : ∀ n, Martingale (Z n) 𝓖 P)
    (hY : StronglyAdapted 𝓖 Y) (hYint : ∀ t, Integrable (Y t) P)
    (hlim : ∀ t, Tendsto (fun n ↦ eLpNorm (Z n t - Y t) 1 P) atTop (𝓝 0)) :
    Martingale Y 𝓖 P := by
  refine ⟨hY, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hYint t)
    (fun B _ _ ↦ (hYint s).integrableOn) (fun B hB _ ↦ ?_)
    (hY s).aestronglyMeasurable).symm
  have hs := tendsto_setIntegral_of_L1' (Y s) (Eventually.of_forall fun n ↦ (hZ n).integrable s)
    (hlim s) B
  have ht := tendsto_setIntegral_of_L1' (Y t) (Eventually.of_forall fun n ↦ (hZ n).integrable t)
    (hlim t) B
  refine tendsto_nhds_unique hs (ht.congr fun n ↦ ?_)
  exact ((hZ n).setIntegral_eq hst hB).symm

omit [MeasurableSpace E] in
/-- **`IsMPSolutionFor.insert_of_tendsto`: closure of the solution property along a solution.**  If
`p n ∈ A` and the test processes of `p n` converge in `L¹ P` at every time to that of `(f, g)`, then
a solution for `A` solves for `insert (f, g) A`.  The hypothesis is on the pairs composed with `X`,
so `f` and `g` may be unbounded.  Adaptedness of the new test process is carried as a hypothesis,
for the reason given at `martingale_of_tendsto_eLpNorm`.  For pairs in `Submodule.span 𝕂 A` apply
`IsMPSolutionFor.span` first. -/
theorem IsMPSolutionFor.insert_of_tendsto [OrderBot ι] {A : Set ((E → 𝕂) × (E → 𝕂))}
    {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E} {𝓖 : Filtration ι m} {P : Measure Ω}
    [IsFiniteMeasure P] (hA : IsMPSolutionFor A Q c X 𝓖 P) {p : ℕ → (E → 𝕂) × (E → 𝕂)}
    (hpA : ∀ n, p n ∈ A) {f g : E → 𝕂}
    (hadapt : StronglyAdapted 𝓖 (mpProcess Q c X f g))
    (hYint : ∀ t, Integrable (mpProcess Q c X f g t) P)
    (hlim : ∀ t, Tendsto (fun n ↦
      eLpNorm (mpProcess Q c X (p n).1 (p n).2 t - mpProcess Q c X f g t) 1 P) atTop (𝓝 0)) :
    IsMPSolutionFor (insert (f, g) A) Q c X 𝓖 P := by
  rw [IsMPSolutionFor, mpFamily_eq_image_mpProcess] at hA ⊢
  rintro _ ⟨q, hq, rfl⟩
  rcases hq with rfl | hq
  · exact martingale_of_tendsto_eLpNorm (fun n ↦ hA _ ⟨p n, hpA n, rfl⟩) hadapt hYint hlim
  · exact hA _ ⟨q, hq, rfl⟩
