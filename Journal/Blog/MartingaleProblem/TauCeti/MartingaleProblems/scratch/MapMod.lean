import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {ι : Type*} [Preorder ι] {Ω : Type*} {m : MeasurableSpace Ω}
  {E : Type*} [MeasurableSpace E] {𝕂 : Type*} [RCLike 𝕂]

/-- A process adapted and almost surely equal at every time to a martingale is a martingale. -/
theorem MeasureTheory.Martingale.of_forall_ae_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {𝓖 : Filtration ι m} {P : Measure Ω}
    {Y Y' : ι → Ω → F} (hY : Martingale Y 𝓖 P) (hY' : StronglyAdapted 𝓖 Y')
    (h : ∀ t, Y t =ᵐ[P] Y' t) : Martingale Y' 𝓖 P :=
  ⟨hY', fun s t hst ↦ (condExp_congr_ae (h t).symm).trans ((hY.condExp_ae_eq hst).trans (h s))⟩

omit [MeasurableSpace E] in
/-- **The test process of a modification is a modification of the test process**, once the
integrand is jointly measurable along both processes.  The joint measurability is what turns
"`X s = X' s` almost surely for every `s`" into "`X · ω = X' · ω` for `q`-almost every `s`, for
almost every `ω`" (`Measure.ae_ae_comm`); without it the compensators of the two processes need
not be comparable at all. -/
theorem mpProcess_ae_eq_of_forall_ae_eq [OrderBot ι] {Q : Clock ι} {c : Clock.Conv}
    {X X' : ι → Ω → E} {P : Measure Ω} [IsFiniteMeasure P] (hmod : ∀ t, X t =ᵐ[P] X' t)
    {f g : E → 𝕂}
    (hj : Measurable[Q.measurableSpace.prod m] fun x : ι × Ω ↦ g (X x.1 x.2))
    (hj' : Measurable[Q.measurableSpace.prod m] fun x : ι × Ω ↦ g (X' x.1 x.2)) (t : ι) :
    mpProcess Q c X f g t =ᵐ[P] mpProcess Q c X' f g t := by
  let _ : MeasurableSpace ι := Q.measurableSpace
  have : IsFiniteMeasure (Q.q.restrict (Q.interval c ⊥ t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (Q.measure_interval_ne_top c ⊥ t).lt_top⟩
  have hS : MeasurableSet {x : ι × Ω | g (X x.1 x.2) = g (X' x.1 x.2)} :=
    measurableSet_eq_fun hj hj'
  have h1 : ∀ᵐ s ∂(Q.q.restrict (Q.interval c ⊥ t)), ∀ᵐ ω ∂P, g (X s ω) = g (X' s ω) :=
    ae_of_all _ fun s ↦ by filter_upwards [hmod s] with ω hω using by rw [hω]
  have h2 := (Measure.ae_ae_comm (μ := Q.q.restrict (Q.interval c ⊥ t)) (ν := P) hS).1 h1
  filter_upwards [h2, hmod t] with ω hω hωt
  simp only [mpProcess, hωt]
  rw [integral_congr_ae hω]

omit [MeasurableSpace E] in
/-- **`IsMPSolutionFor.map`, along a modification.**  If `X` solves the problem for `A` and `X'`
is a modification of `X`, then `X'` solves it too, provided the integrands are jointly measurable
along both processes and the test processes of `X'` are adapted.  The adaptedness is a
hypothesis because a modification of an adapted process need not be adapted to a filtration that
is not complete. -/
theorem IsMPSolutionFor.of_forall_ae_eq [OrderBot ι] {A : Set ((E → 𝕂) × (E → 𝕂))}
    {Q : Clock ι} {c : Clock.Conv} {X X' : ι → Ω → E} {𝓖 : Filtration ι m} {P : Measure Ω}
    [IsFiniteMeasure P] (hA : IsMPSolutionFor A Q c X 𝓖 P) (hmod : ∀ t, X t =ᵐ[P] X' t)
    (hj : ∀ p ∈ A, Measurable[Q.measurableSpace.prod m] fun x : ι × Ω ↦ p.2 (X x.1 x.2))
    (hj' : ∀ p ∈ A, Measurable[Q.measurableSpace.prod m] fun x : ι × Ω ↦ p.2 (X' x.1 x.2))
    (hadapt : ∀ p ∈ A, StronglyAdapted 𝓖 (mpProcess Q c X' p.1 p.2)) :
    IsMPSolutionFor A Q c X' 𝓖 P := by
  rw [IsMPSolutionFor, mpFamily_eq_image_mpProcess] at hA ⊢
  rintro _ ⟨p, hp, rfl⟩
  exact (hA _ ⟨p, hp, rfl⟩).of_forall_ae_eq (hadapt p hp)
    (mpProcess_ae_eq_of_forall_ae_eq hmod (hj p hp) (hj' p hp))
