/-
Der Zeuge zu einer Bemerkung im Doc-Kommentar von
`mpSolution_of_tendsto_augmented`: die augmentierte Konvergenzvoraussetzung
(C1') gibt die gewöhnliche (C1) zurück, und sie kostet dabei `BorelSpace F`.
Der Satz selbst steht in `../Suggested.lean`; hier steht nur der Beleg, damit
der Doc-Kommentar nicht auf etwas Ungeprüftes zeigt.

Übersetzt mit

    lake --dir=/home/pfaffelh/Code/lean/journal env sh -c \
      'LEAN_PATH="$LEAN_PATH:<worktree>/scratch/_lean" exec lean <diese Datei>'

nachdem `python3 scripts/check_suggested.py` die `.olean` gebaut hat.
-/
import TauCetiRoadmap.MartingaleProblems.Suggested

open Filter Topology MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {m : MeasurableSpace Ω} {F : Type*} [MeasurableSpace F]

example {G : Type*} [MeasurableSpace G] [TopologicalSpace G] [TopologicalSpace F]
    [OpensMeasurableSpace (F × G)] [BorelSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P] {Ω' : ℕ → Type*}
    {m' : ∀ n, MeasurableSpace (Ω' n)} {P' : ∀ n, @Measure (Ω' n) (m' n)}
    [∀ n, IsProbabilityMeasure (P' n)]
    {X : Ω → F} {X' : ∀ n, Ω' n → F} {γ : F → G}
    (hweak : TendstoInDistribution (fun n ω ↦ (X' n ω, γ (X' n ω))) atTop
      (fun ω ↦ (X ω, γ (X ω))) P' P) :
    TendstoInDistribution X' atTop X P' P :=
  hweak.continuous_comp continuous_fst
