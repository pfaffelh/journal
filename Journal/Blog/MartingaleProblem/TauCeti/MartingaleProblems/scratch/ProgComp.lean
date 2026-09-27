import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {ι : Type*} [Preorder ι] {Ω : Type*} {m : MeasurableSpace Ω}
  {E : Type*} [MeasurableSpace E]

/-- **Progressive measurability of the real functionals of the process**: below each `t` the path
has an extension `Z` such that `(u, ω) ↦ h (Z u ω)` is `Q.measurableSpace ⊗ 𝓕 t`-measurable for
every measurable `h : E → ℝ`.  This is what the compensator consumes, and unlike
`Clock.IsProgressive` it is reachable over a bare `[MeasurableSpace E]` by approximation in `ℝ`,
where limits of measurable maps are measurable. -/
def Clock.IsProgressiveComp (Q : Clock ι) (X : ι → Ω → E) (𝓕 : Filtration ι m) : Prop :=
  ∀ t : ι, ∃ Z : ι → Ω → E, (∀ u, u ≤ t → Z u = X u) ∧
    ∀ h : E → ℝ, Measurable h → Measurable[Q.measurableSpace.prod (𝓕 t)] fun x : ι × Ω ↦ h (Z x.1 x.2)

/-- The `E` valued form gives the real one, by composition. -/
theorem Clock.IsProgressive.isProgressiveComp {Q : Clock ι} {X : ι → Ω → E} {𝓕 : Filtration ι m}
    (hX : Q.IsProgressive X 𝓕) : Q.IsProgressiveComp X 𝓕 := by
  intro t
  obtain ⟨Z, hZ, hZm⟩ := hX t
  exact ⟨Z, hZ, fun h hh ↦ hh.comp hZm⟩
