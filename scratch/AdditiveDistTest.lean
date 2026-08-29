import Mathlib

open Metric Set

/-- The metric is additive along the order. -/
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u

namespace AdditiveDist

instance instReal : AdditiveDist ℝ where
  dist_add {s t u} hst htu := by
    simp only [Real.dist_eq]
    rw [abs_of_nonpos (by linarith : s - u ≤ 0), abs_of_nonpos (by linarith : s - t ≤ 0),
      abs_of_nonpos (by linarith : t - u ≤ 0)]
    ring

instance instInt : AdditiveDist ℤ where
  dist_add {s t u} hst htu := by
    have h : (s : ℝ) ≤ t := by exact_mod_cast hst
    have h' : (t : ℝ) ≤ u := by exact_mod_cast htu
    simp only [Int.dist_eq]
    rw [abs_of_nonpos (by linarith : (s : ℝ) - u ≤ 0), abs_of_nonpos (by linarith : (s : ℝ) - t ≤ 0),
      abs_of_nonpos (by linarith : (t : ℝ) - u ≤ 0)]
    ring

/-- Every subset of an `AdditiveDist` type inherits the property. -/
instance instSubtype {α : Type*} [LinearOrder α] [PseudoMetricSpace α] [AdditiveDist α]
    (s : Set α) : AdditiveDist s where
  dist_add {a b c} hab hbc := AdditiveDist.dist_add (α := α) hab hbc

end AdditiveDist

section Instanzen

-- die vier gewünschten Zeitmengen
example : AdditiveDist (Set.Ici (0 : ℝ)) := inferInstance
example : AdditiveDist (Set.Ici (-1 : ℝ)) := inferInstance
example : AdditiveDist (Set.Icc (0 : ℝ) 1) := inferInstance
example : AdditiveDist ℝ := inferInstance
example : AdditiveDist ℤ := inferInstance
example (h : ℝ) : AdditiveDist (Set.range (fun n : ℤ => h * n)) := inferInstance

-- ProperSpace: fuer abgeschlossene Teilmengen ueber ProperSpace.of_isClosed
example : ProperSpace ℝ := inferInstance
example : ProperSpace ℤ := inferInstance
example : ProperSpace (Set.Ici (0 : ℝ)) := .of_isClosed isClosed_Ici
example : ProperSpace (Set.Ici (-1 : ℝ)) := .of_isClosed isClosed_Ici
example : ProperSpace (Set.Icc (0 : ℝ) 1) := inferInstance
-- das Gitter h*ℤ, in Mathlib-Schreibweise
-- LUECKE 1: die Subtyp-Instanz greift nicht durch die SetLike-Huelle.
-- Ueber die Set-Koerzion geht es:
example (h : ℝ) : AdditiveDist ((AddSubgroup.zmultiples h : Set ℝ)) := inferInstance
example (h : ℝ) : ProperSpace (AddSubgroup.zmultiples h) :=
  .of_isClosed (AddSubgroup.isClosed_of_discrete)

-- OrderTopology
example : OrderTopology ℝ := inferInstance
example : OrderTopology ℤ := inferInstance
example : OrderTopology (Set.Ici (0 : ℝ)) := inferInstance
example : OrderTopology (Set.Ici (-1 : ℝ)) := inferInstance
example : OrderTopology (Set.Icc (0 : ℝ) 1) := inferInstance
-- LUECKE 2: Das Gitter ist nicht ordnungszusammenhaengend, also greift
-- orderTopology_of_ordConnected nicht; und OrderTopology.of_discreteTopology
-- braucht PredOrder/SuccOrder, die fuer den Untertyp fehlen.  Als eigener Typ
-- dagegen ist alles vorhanden:
example : OrderTopology ℤ := inferInstance
example : AdditiveDist ℤ := inferInstance
example : ProperSpace ℤ := inferInstance

end Instanzen

section Konsequenz

variable {α : Type*} [LinearOrder α] [MetricSpace α] [AdditiveDist α]

/-- Die Längenfunktion zu einem Basispunkt ist monoton oberhalb davon, und die Metrik ist
ihre Differenz.  Das ist der Schritt, aus dem (N4) folgt. -/
theorem dist_eq_sub_of_le {t₀ s t : α} (h₀s : t₀ ≤ s) (hst : s ≤ t) :
    dist s t = dist t₀ t - dist t₀ s := by
  have := AdditiveDist.dist_add (α := α) h₀s hst
  linarith

theorem monotone_dist_basepoint {t₀ : α} :
    MonotoneOn (fun t => dist t₀ t) (Set.Ici t₀) := by
  intro s hs t ht hst
  have := AdditiveDist.dist_add (α := α) hs hst
  have : dist t₀ t = dist t₀ s + dist s t := this
  have hd : 0 ≤ dist s t := dist_nonneg
  simp only
  linarith

end Konsequenz
