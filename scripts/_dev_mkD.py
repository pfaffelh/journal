src = open('scripts/_dev_E3src.txt').read()
body = src[src.index('  have hX :'):]
R = [
    ("""  have hX : ∀ u : ℝ≥0, Measurable[pathFiltration (E := E) u]
      fun ω : RightContinuousPath E ↦ coordinate u (id ω) :=
    fun _ ↦ measurable_pathFiltration le_rfl""",
     """  have hX : ∀ u : ℝ≥0, Measurable[cadlagFiltration (E := E) u]
      fun ω : D(ℝ≥0, E) ↦ (id ω).toFun u :=
    fun _ ↦ measurable_cadlagFiltration le_rfl"""),
    ("""    fun _ hY ↦ stronglyAdapted_mpFamily_coordinate Clock.Conv.optional hfm hgm hY""",
     """    fun _ hY ↦ stronglyAdapted_mpFamily_cadlagFiltration hA' hY
  have hrcY : ∀ Y ∈ mpFamily A' lebesgueClock Clock.Conv.optional
      (fun r (z : D(ℝ≥0, E)) ↦ z.toFun r), ∀ ω s, ContinuousWithinAt (Y · ω) (Ici s) s := by
    intro Y hY ω s
    obtain ⟨p, -, hYp⟩ := exists_mpTest_eq_of_mem_mpFamily hA' hY
    have e : (fun r ↦ Y r ω) = fun r ↦ SkorokhodSpace.mpTest p.1 p.2 r ω :=
      funext fun r ↦ by rw [hYp r]
    rw [e]
    exact continuousWithinAt_Ioi_iff_Ici.1 (isRightContinuous_mpTest p.1 p.2 ω s)
  have hprogY : ∀ Y ∈ mpFamily A' lebesgueClock Clock.Conv.optional
      (fun r (z : D(ℝ≥0, E)) ↦ z.toFun r), IsStronglyProgressive (cadlagFiltration (E := E)) Y :=
    fun Y hY ↦ (hadaptY Y hY).isStronglyProgressive_of_rightContinuous (hrcY Y hY)"""),
    ("""    exact isMPSolution_map_withDensity_shiftByTime hadaptY hsol
      (fun _ hY ↦ isStronglyProgressive_mpFamily_coordinate Clock.Conv.optional hfm hgm hY)
      (fun _ hY ↦ ae_of_all _ fun ω ↦ tendsto_nhdsGE_mpFamily_coordinate hgm
        (fun p hp ↦ by
          obtain ⟨b, hb⟩ := hgb p hp
          exact ⟨b, fun x ↦ by rw [← Real.norm_eq_abs]; exact hb x⟩) hY ω)
      (hτn n)
      (fun _ hY t ↦ integrable_mpFamily_coordinate_randomTime hfm hfb hgm hgb (hτn n)
        (T := (n : ℝ≥0)) (fun ω ↦ min_le_right _ _) hY t)
      (hψn n) (measurable_shift_stoppingTime hX (hτn n))
      (exists_incr_mpFamily_of_shift (lebesgueClock_isShiftInvariant Clock.Conv.optional) hfb hgb
        (fun p hp g ↦ measurable_comp_coordinate (hgm p hp) g)
        (fun p hp ↦ measurable_comp_coordinate_randomTime (hfm p hp) (hτnm n) measurable_id))
      hZ0 hZb hZm""",
     """    have hintn : ∀ Y ∈ mpFamily A' lebesgueClock Clock.Conv.optional
        (fun r (z : D(ℝ≥0, E)) ↦ z.toFun r),
        ∀ s : ℝ≥0, Integrable (fun ω ↦ Y (τn n ω + s) ω) P := by
      intro Y hY s
      obtain ⟨p, -, hYp⟩ := exists_mpTest_eq_of_mem_mpFamily hA' hY
      have hm : Measurable[(hτn n s).measurableSpace] fun ω ↦ Y (τn n ω + s) ω :=
        measurable_stoppedValue (hprogY Y hY) (hτn n s)
      refine Integrable.mono'
        (integrable_const (‖p.1‖ + ‖p.2‖ * (((n : ℝ≥0) + s : ℝ≥0) : ℝ)))
        (hm.mono (hτn n s).measurableSpace_le le_rfl).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, hYp]
      exact abs_mpTest_le p.1 p.2 (add_le_add_left (min_le_right _ _) s) ω
    exact isMPSolution_map_withDensity_shiftByTime hadaptY hsol hprogY
      (fun Y hY ↦ ae_of_all _ fun ω s ↦ hrcY Y hY ω s)
      (hτn n) hintn
      (hψn n) (measurable_cadlagShift_stoppingTime hX (hτn n))
      (exists_incr_mpFamily_of_shift (lebesgueClock_isShiftInvariant Clock.Conv.optional)
        (exists_norm_fst_le_of_boundedContinuous hA')
        (exists_norm_snd_le_of_boundedContinuous hA')
        (measurable_snd_comp_of_boundedContinuous hA')
        (fun p hp ↦ (measurable_fst_of_boundedContinuous hA' p hp).comp
          (SkorokhodSpace.measurable_uncurry_eval_nnreal.comp
            ((hτnm n).prodMk measurable_id))))
      hZ0 hZb hZm"""),
    ("""        obtain ⟨c, -, hc⟩ := abs_mpFamily_coordinate_le hfb hgb hY i
        exact ⟨c, fun g ↦ by rw [Real.norm_eq_abs]; exact hc i le_rfl g⟩)""",
     """        obtain ⟨p, -, hYp⟩ := exists_mpTest_eq_of_mem_mpFamily hA' hY
        exact ⟨‖p.1‖ + ‖p.2‖ * (i : ℝ), fun g ↦ by
          rw [Real.norm_eq_abs, hYp]; exact abs_mpTest_le p.1 p.2 le_rfl g⟩)"""),
    ("""  have hπm : ∀ u : ℝ≥0, Measurable (coordinate u : RightContinuousPath E → E) :=
    fun u ↦ (measurable_pathFiltration le_rfl).mono ((pathFiltration (E := E)).le u) le_rfl""",
     """  have hπm : ∀ u : ℝ≥0, Measurable (fun z : D(ℝ≥0, E) ↦ z.toFun u) :=
    fun u ↦ (measurable_cadlagFiltration le_rfl).mono ((cadlagFiltration (E := E)).le u) le_rfl"""),
    ("""  have key := condExp_eq_condExp_state_of_restart (𝕂 := ℝ) (P := P) hπm""",
     """  have key := condExp_eq_condExp_state_of_restart (𝕂 := ℝ) (P := P)
    (π := fun r (z : D(ℝ≥0, E)) ↦ z.toFun r) hπm"""),
    ("""    (measurable_pathFiltration le_rfl).comp (measurable_shift_stoppingTime hX hτ 0)""",
     """    (measurable_cadlagFiltration le_rfl).comp (measurable_cadlagShift_stoppingTime hX hτ 0)"""),
    ("measurable_shift_randomTime", "measurable_cadlagShift_randomTime"),
    ("(coordinate : ℝ≥0 → RightContinuousPath E → E)", "(fun r (z : D(ℝ≥0, E)) ↦ z.toFun r)"),
    ("mpFamily A lebesgueClock", "mpFamily A' lebesgueClock"),
    ("RightContinuousPath E", "D(ℝ≥0, E)"),
    ("pathFiltration.shiftByTime", "(cadlagFiltration (E := E)).shiftByTime"),
    ("pathFiltration (E := E)", "cadlagFiltration (E := E)"),
    ("pathShift.θ", "(cadlagShift (E := E)).θ"),
    ("pathShift.eval_comp", "(cadlagShift (E := E)).eval_comp"),
    ("coordinate ⊥ (ψ ω)", "(ψ ω).toFun ⊥"),
    ("coordinate t (ψ ω)", "(ψ ω).toFun t"),
    ("coordinate (τ ω + t) ω", "ω.toFun (τ ω + t)"),
    ("coordinate (τ ω) ω", "ω.toFun (τ ω)"),
]
for a, b in R:
    if a not in body:
        print('MISS', a[:70])
    body = body.replace(a, b)
head = open('scripts/_dev_Dhead.lean').read()
open('scripts/_dev_E4c.lean', 'w').write(head + body + '\nend StrongMarkovCadlagFinite\n\nend MeasureTheory\n')
