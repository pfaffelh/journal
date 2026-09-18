# `lake env lean` gegen Mathlib `upstream/master`

* Mathlib: `94ef6b89544e58e90f119da869f3fb48d1da0f4c 2026-09-18`
* Lean (version 4.35.0-rc2, x86_64-unknown-linux-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release)

| Datei | rc | Fehler | `sorry` | Warnungen | Sekunden |
| --- | ---: | ---: | ---: | ---: | ---: |
| `WeakConvergence` | 1 | 16 | 0 | 52 | 7 |
| `SkorokhodSpace` | 1 | 1 | 0 | 0 | 1 |
| `MartingaleProblems` | 1 | 1 | 0 | 0 | 1 |

## Fehler in `WeakConvergence`

* `779:17: error: Application type mismatch: The argument`
* `1952:57: error: Application type mismatch: The argument`
* `1953:53: error: Application type mismatch: The argument`
* `3998:48: error: unsolved goals`
* `4019:48: error: unsolved goals`
* `4052:47: error: Type mismatch`
* `4206:61: error: Type mismatch`
* `4361:84: error: unsolved goals`
* `4661:2: error: unsolved goals`
* `4676:35: error(lean.unknownIdentifier): Unknown identifier `_root_.not_imp``
* `4677:13: error: Tactic `rcases` failed: `hz : (ε n < dist (z.2 (n, Φ n z.1)) z.1.1 → z.1.1 ∈ A n 0 ∨ 1 - t n < z.1.2) →`
* `5276:22: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.isProbabilityMeasure_map``
* `5278:15: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.isProbabilityMeasure_map``
* `5842:10: error: Function expected at`
* `5856:6: error: Function expected at`
* `5856:37: error: Type mismatch`

## Keine `.olean` für `WeakConvergence`

* die folgenden Dateien der Kette sind damit **nicht geprüft**

## Fehler in `SkorokhodSpace`

* `6:0: error: object file '/home/pfaffelh/Code/lean/mathlib-master/_lean_master/TauCetiRoadmap/WeakConvergence/Suggested.olean' of module TauCetiRoadmap.WeakConvergence.Suggested does not exist`

## Keine `.olean` für `SkorokhodSpace`

* die folgenden Dateien der Kette sind damit **nicht geprüft**

## Fehler in `MartingaleProblems`

* `6:0: error: object file '/home/pfaffelh/Code/lean/mathlib-master/_lean_master/TauCetiRoadmap/WeakConvergence/Suggested.olean' of module TauCetiRoadmap.WeakConvergence.Suggested does not exist`

## Keine `.olean` für `MartingaleProblems`

* die folgenden Dateien der Kette sind damit **nicht geprüft**
