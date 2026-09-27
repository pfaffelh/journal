import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- **Fatou's lemma for real functions bounded below by a constant**, on a finite measure, in the
form that survives a sequence of integrals which need not be bounded above: both sides are read in
`ℝ≥0∞` after adding the constant. -/
theorem MeasureTheory.ofReal_integral_add_le_liminf {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {G : α → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hC : ∀ n, ∀ᵐ x ∂μ, -C ≤ F n x)
    (hG : Integrable G μ) (hGC : ∀ᵐ x ∂μ, -C ≤ G x)
    (hlim : ∀ᵐ x ∂μ,
      ENNReal.ofReal (G x + C) ≤ liminf (fun n ↦ ENNReal.ofReal (F n x + C)) atTop) :
    ENNReal.ofReal (∫ x, G x ∂μ + μ.real univ * C)
      ≤ liminf (fun n ↦ ENNReal.ofReal (∫ x, F n x ∂μ + μ.real univ * C)) atTop := by
  have hGi : ∫ x, G x ∂μ + μ.real univ * C = ∫ x, (G x + C) ∂μ := by
    rw [integral_add hG (integrable_const C), integral_const, smul_eq_mul]
  have hFi : ∀ n, ∫ x, F n x ∂μ + μ.real univ * C = ∫ x, (F n x + C) ∂μ := fun n ↦ by
    rw [integral_add (hF n) (integrable_const C), integral_const, smul_eq_mul]
  simp_rw [hGi, hFi]
  calc ENNReal.ofReal (∫ x, (G x + C) ∂μ) = ∫⁻ x, ENNReal.ofReal (G x + C) ∂μ := by
        refine ofReal_integral_eq_lintegral_ofReal (hG.add (integrable_const C)) ?_
        filter_upwards [hGC] with x hx
        simp only [Pi.zero_apply]
        linarith
    _ ≤ ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (F n x + C)) atTop ∂μ := lintegral_mono_ae hlim
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (F n x + C) ∂μ) atTop :=
        lintegral_liminf_le' fun n ↦
          ((hF n).add (integrable_const C)).aemeasurable.ennreal_ofReal
    _ = liminf (fun n ↦ ENNReal.ofReal (∫ x, (F n x + C) ∂μ)) atTop := by
        congr 1
        funext n
        refine (ofReal_integral_eq_lintegral_ofReal ((hF n).add (integrable_const C)) ?_).symm
        filter_upwards [hC n] with x hx
        show 0 ≤ F n x + C
        linarith

variable {ι : Type*} [Preorder ι] [OrderBot ι] {Ω : Type*} {m : MeasurableSpace Ω}
  {E : Type*} [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- **`IsMPSolutionFor.submartingale_mpProcess_of_tendsto`, the one sided companion of
`insert_of_forall_norm_le`**, for real valued test pairs.  If `p n ∈ A` converge pointwise to
`(f, g)`, the first components bounded by `C` and the second bounded **from below** by `-C` only,
then the test process of `(f, g)` is a submartingale.  The martingale identity of `p n` on a set
`B ∈ 𝓖 s` reads `∫_B (f_n(X_t) - f_n(X_s)) = ∫_B ∫_{(s,t]} g_n(X_u) q(du)`; the left side converges
by dominated convergence, and the right side is bounded below in the limit by Fatou's lemma, once
along the path and once in `ω` (`ofReal_integral_add_le_liminf`).

Three hypotheses are carried that the pointwise bounds do not give, and no measurability along the
paths is asked: the integrability over the windows carries it.  `hadapt`: with `g_n` bounded
only from below the compensators need not converge, so the adaptedness of the limit process is not
inherited from the `p n`.  `hint` and `hintn`: the compensating integrals are Bochner integrals,
and a window on which `g_n` or `g` is not integrable along a path would give the junk value `0`.
`hfX`: the measurability of `f_n ∘ X_t`, from which that of the path integrals over a window
follows. -/
theorem IsMPSolutionFor.submartingale_mpProcess_of_tendsto
    {A : Set ((E → ℝ) × (E → ℝ))} {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E}
    {𝓖 : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P]
    (hA : IsMPSolutionFor A Q c X 𝓖 P) {p : ℕ → (E → ℝ) × (E → ℝ)}
    (hpA : ∀ n, p n ∈ A) {f g : E → ℝ} (hf : ∀ x, Tendsto (fun n ↦ (p n).1 x) atTop (𝓝 (f x)))
    (hg : ∀ x, Tendsto (fun n ↦ (p n).2 x) atTop (𝓝 (g x)))
    {C : ℝ} (hC1 : ∀ n x, ‖(p n).1 x‖ ≤ C) (hC2 : ∀ n x, -C ≤ (p n).2 x)
    (hintn : ∀ n t ω, IntegrableOn (fun s ↦ (p n).2 (X s ω)) (Q.interval c ⊥ t) Q.q)
    (hint : ∀ t ω, IntegrableOn (fun s ↦ g (X s ω)) (Q.interval c ⊥ t) Q.q)
    (hfX : ∀ n t, AEStronglyMeasurable (fun ω ↦ (p n).1 (X t ω)) P)
    (hadapt : StronglyAdapted 𝓖 (mpProcess Q c X f g))
    (hYint : ∀ t, Integrable (mpProcess Q c X f g t) P) :
    Submartingale (mpProcess Q c X f g) 𝓖 P := by
  let _ : MeasurableSpace ι := Q.measurableSpace
  set Z : ℕ → ι → Ω → ℝ := fun n ↦ mpProcess Q c X (p n).1 (p n).2 with hZdef
  set Y := mpProcess Q c X f g with hYdef
  have hZ : ∀ n, Martingale (Z n) 𝓖 P := fun n ↦ by
    rw [IsMPSolutionFor, mpFamily_eq_image_mpProcess] at hA
    exact hA _ ⟨p n, hpA n, rfl⟩
  have hfC : ∀ x, ‖f x‖ ≤ C := fun x ↦ le_of_tendsto' (hf x).norm fun n ↦ hC1 n x
  have hgC : ∀ x, -C ≤ g x := fun x ↦ ge_of_tendsto' (hg x) fun n ↦ hC2 n x
  have hfXl : ∀ t, AEStronglyMeasurable (fun ω ↦ f (X t ω)) P := fun t ↦
    aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ hfX n t)
      (ae_of_all _ fun ω ↦ hf (X t ω))
  refine submartingale_of_setIntegral_le hadapt hYint fun s t hst B hB ↦ ?_
  -- the window and the path integrals over it
  set W := Q.interval c s t with hW
  have hWfin : Q.q W ≠ ⊤ := Q.measure_interval_ne_top c s t
  have : IsFiniteMeasure (Q.q.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hWfin.lt_top⟩
  have hsplit := Q.interval_union c (bot_le : (⊥ : ι) ≤ s) hst
  have hWm : MeasurableSet W := Q.measurableSet_interval c s t
  set H : ℕ → Ω → ℝ := fun n ω ↦ ∫ u in W, (p n).2 (X u ω) ∂Q.q with hHdef
  set H' : Ω → ℝ := fun ω ↦ ∫ u in W, g (X u ω) ∂Q.q with hH'def
  have hsplitI : ∀ (φ : ι → ℝ), IntegrableOn φ (Q.interval c ⊥ t) Q.q →
      ∫ u in Q.interval c ⊥ t, φ u ∂Q.q
        = ∫ u in Q.interval c ⊥ s, φ u ∂Q.q + ∫ u in W, φ u ∂Q.q := by
    intro φ hφ
    rw [hsplit.1] at hφ ⊢
    exact setIntegral_union hsplit.2 hWm (hφ.mono_set subset_union_left)
      (hφ.mono_set subset_union_right)
  -- the increments of the test processes
  have hZinc : ∀ n ω, Z n t ω - Z n s ω = (p n).1 (X t ω) - (p n).1 (X s ω) - H n ω := by
    intro n ω
    simp only [hZdef, mpProcess, hHdef]
    rw [hsplitI _ (hintn n t ω)]
    ring
  have hYinc : ∀ ω, Y t ω - Y s ω = f (X t ω) - f (X s ω) - H' ω := by
    intro ω
    simp only [hYdef, mpProcess, hH'def]
    rw [hsplitI _ (hint t ω)]
    ring
  -- integrability of the pieces
  have hfnI : ∀ n t, Integrable (fun ω ↦ (p n).1 (X t ω)) P := fun n t ↦
    Integrable.mono' (integrable_const C) (hfX n t) (ae_of_all _ fun ω ↦ hC1 n _)
  have hfI : ∀ t, Integrable (fun ω ↦ f (X t ω)) P := fun t ↦
    Integrable.mono' (integrable_const C) (hfXl t) (ae_of_all _ fun ω ↦ hfC _)
  have hHeq : ∀ n, H n = fun ω ↦ (p n).1 (X t ω) - (p n).1 (X s ω) - (Z n t ω - Z n s ω) := by
    intro n; funext ω; rw [hZinc]; ring
  have hHI : ∀ n, Integrable (H n) P := fun n ↦ by
    rw [hHeq n]
    exact ((hfnI n t).sub (hfnI n s)).sub (((hZ n).integrable t).sub ((hZ n).integrable s))
  have hH'eq : H' = fun ω ↦ f (X t ω) - f (X s ω) - (Y t ω - Y s ω) := by
    funext ω; rw [hYinc]; ring
  have hH'I : Integrable H' P := by
    rw [hH'eq]
    exact ((hfI t).sub (hfI s)).sub ((hYint t).sub (hYint s))
  -- lower bounds
  set K : ℝ := Q.q.real W * C with hK
  have hHlow : ∀ n ω, -K ≤ H n ω := by
    intro n ω
    have h1 : ∫ u in W, (-C) ∂Q.q ≤ H n ω :=
      setIntegral_mono_on (integrableOn_const hWfin) ((hintn n t ω).mono_set
        (by rw [hsplit.1]; exact subset_union_right)) hWm fun u _ ↦ hC2 n _
    rw [setIntegral_const, smul_eq_mul] at h1
    simp only [hK]
    linarith
  have hH'low : ∀ ω, -K ≤ H' ω := by
    intro ω
    have h1 : ∫ u in W, (-C) ∂Q.q ≤ H' ω :=
      setIntegral_mono_on (integrableOn_const hWfin) ((hint t ω).mono_set
        (by rw [hsplit.1]; exact subset_union_right)) hWm fun u _ ↦ hgC _
    rw [setIntegral_const, smul_eq_mul] at h1
    simp only [hK]
    linarith
  -- Fatou along the path
  have hinner : ∀ ω, ENNReal.ofReal (H' ω + K)
      ≤ liminf (fun n ↦ ENNReal.ofReal (H n ω + K)) atTop := by
    intro ω
    have hWreal : (Q.q.restrict W).real univ = Q.q.real W := by
      simp [Measure.real]
    have := ofReal_integral_add_le_liminf (μ := Q.q.restrict W)
      (F := fun n u ↦ (p n).2 (X u ω)) (G := fun u ↦ g (X u ω)) (C := C)
      (fun n ↦ (hintn n t ω).mono_set (by rw [hsplit.1]; exact subset_union_right))
      (fun n ↦ ae_of_all _ fun u ↦ hC2 n _)
      ((hint t ω).mono_set (by rw [hsplit.1]; exact subset_union_right))
      (ae_of_all _ fun u ↦ hgC _)
      (ae_of_all _ fun u ↦ by
        rw [(ENNReal.tendsto_ofReal ((hg (X u ω)).add_const C)).liminf_eq])
    rw [hWreal] at this
    simpa only [hK, hHdef, hH'def] using this
  -- Fatou in `ω`, on `B`
  have hBreal : (P.restrict B).real univ = P.real B := by
    simp [Measure.real]
  have houter := ofReal_integral_add_le_liminf (μ := P.restrict B) (F := H) (G := H') (C := K)
    (fun n ↦ (hHI n).restrict) (fun n ↦ ae_of_all _ fun ω ↦ hHlow n ω) hH'I.restrict
    (ae_of_all _ hH'low) (ae_of_all _ hinner)
  rw [hBreal] at houter
  -- the integrals of `H n` over `B` converge to that of the increment of `f ∘ X`
  have hmartB : ∀ n, ∫ ω in B, Z n t ω ∂P = ∫ ω in B, Z n s ω ∂P := fun n ↦
    ((hZ n).setIntegral_eq hst hB).symm
  have hHB : ∀ n, ∫ ω in B, H n ω ∂P
      = ∫ ω in B, (p n).1 (X t ω) ∂P - ∫ ω in B, (p n).1 (X s ω) ∂P := by
    intro n
    rw [hHeq n]
    rw [integral_sub (f := fun ω ↦ (p n).1 (X t ω) - (p n).1 (X s ω))
      (g := fun ω ↦ Z n t ω - Z n s ω) (((hfnI n t).sub (hfnI n s)).restrict)
      ((((hZ n).integrable t).sub ((hZ n).integrable s)).restrict),
      integral_sub (hfnI n t).restrict (hfnI n s).restrict,
      integral_sub ((hZ n).integrable t).restrict ((hZ n).integrable s).restrict, hmartB n]
    ring
  have hlimf : ∀ r, Tendsto (fun n ↦ ∫ ω in B, (p n).1 (X r ω) ∂P) atTop
      (𝓝 (∫ ω in B, f (X r ω) ∂P)) := fun r ↦
    tendsto_integral_of_dominated_convergence (fun _ ↦ C)
      (fun n ↦ (hfX n r).restrict) (integrable_const C)
      (fun n ↦ ae_of_all _ fun ω ↦ hC1 n _) (ae_of_all _ fun ω ↦ hf _)
  set a : ℝ := ∫ ω in B, f (X t ω) ∂P - ∫ ω in B, f (X s ω) ∂P with ha
  have hconv : Tendsto (fun n ↦ ENNReal.ofReal (∫ ω in B, H n ω ∂P + P.real B * K)) atTop
      (𝓝 (ENNReal.ofReal (a + P.real B * K))) := by
    simp_rw [hHB]
    exact ENNReal.tendsto_ofReal (((hlimf t).sub (hlimf s)).add_const _)
  rw [hconv.liminf_eq] at houter
  have hBK : ∀ n, 0 ≤ ∫ ω in B, H n ω ∂P + P.real B * K := by
    intro n
    have h1 : ∫ ω in B, (-K) ∂P ≤ ∫ ω in B, H n ω ∂P :=
      setIntegral_mono_on (integrableOn_const (measure_ne_top _ _)) (hHI n).integrableOn
        (𝓖.le s _ hB) fun ω _ ↦ hHlow n ω
    rw [setIntegral_const, smul_eq_mul] at h1
    linarith
  have hapos : 0 ≤ a + P.real B * K := by
    have htend : Tendsto (fun n ↦ ∫ ω in B, H n ω ∂P + P.real B * K) atTop
        (𝓝 (a + P.real B * K)) := by
      simp_rw [hHB]
      exact ((hlimf t).sub (hlimf s)).add_const _
    exact ge_of_tendsto' htend hBK
  have hle : ∫ ω in B, H' ω ∂P ≤ a := by
    have := (ENNReal.ofReal_le_ofReal_iff hapos).1 houter
    linarith
  -- conclude
  have hYB : ∫ ω in B, Y t ω ∂P - ∫ ω in B, Y s ω ∂P
      = (∫ ω in B, f (X t ω) ∂P - ∫ ω in B, f (X s ω) ∂P) - ∫ ω in B, H' ω ∂P := by
    rw [← integral_sub (hYint t).restrict (hYint s).restrict]
    simp_rw [hYinc]
    rw [integral_sub (f := fun ω ↦ f (X t ω) - f (X s ω)) ((hfI t).sub (hfI s)).restrict
      hH'I.restrict, integral_sub (hfI t).restrict (hfI s).restrict]
  linarith

omit [MeasurableSpace E] in
/-- The test process of `(0, -C)` is the deterministic `C q((⊥, t])`. -/
theorem mpProcess_zero_const (Q : Clock ι) (c : Clock.Conv) (X : ι → Ω → E) (C : ℝ) :
    mpProcess Q c X (fun _ ↦ (0 : ℝ)) (fun _ ↦ -C) = fun t _ ↦ C * Q.q.real (Q.interval c ⊥ t) := by
  funext t ω
  simp only [mpProcess, setIntegral_const, smul_eq_mul]
  ring

omit [MeasurableSpace E] in
/-- **The one sided companion is genuinely weaker.**  For `f_n = 0`, `g_n = -C` the hypotheses of
`submartingale_mpProcess_of_tendsto` hold with the bound `-C ≤ g_n`, and its conclusion is true, the
test process `C q((⊥, t])` being increasing and deterministic for `C ≥ 0`; but it is **no**
martingale as soon as `C ≠ 0` and the clock puts mass between two times.  So the conclusion cannot
be upgraded to `Martingale`, and the two closure statements are separate. -/
theorem not_martingale_mpProcess_zero_const {Q : Clock ι} {c : Clock.Conv} {X : ι → Ω → E}
    {𝓖 : Filtration ι m} {P : Measure Ω} [IsProbabilityMeasure P] {C : ℝ} (hC : C ≠ 0)
    {s t : ι} (hst : s ≤ t)
    (hne : Q.q.real (Q.interval c ⊥ s) ≠ Q.q.real (Q.interval c ⊥ t)) :
    ¬ Martingale (mpProcess Q c X (fun _ ↦ (0 : ℝ)) (fun _ ↦ -C)) 𝓖 P := by
  intro h
  have h1 := h.setIntegral_eq hst MeasurableSet.univ
  rw [mpProcess_zero_const] at h1
  simp only [Measure.restrict_univ, integral_const, probReal_univ, one_smul] at h1
  exact hne (mul_left_cancel₀ hC h1)
