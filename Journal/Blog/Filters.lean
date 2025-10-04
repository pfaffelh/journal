import Mathlib
import VersoBlog

open Verso Genre Blog
-- open Set Filter

#doc (Page) "Filters in probability" =>

Convergence in Mathlib is usually formulated with filters. I wonder how they can be useful in probability. Let us recall what a filter is:

Let us see how a filter is defined:
```
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

Our goal is to formulate tightness in terms of filters. Recall that tigthness means:

```leanInit tightness
-- This block initializes a Lean context
```
```lean tightness
def MeasureTheory.Measure.IsTight {α : Type u_1} [TopologicalSpace α] [MeasurableSpace α] (ℙ : Measure α) : Prop := InnerRegularWRT ℙ IsCompact (fun x ↦ x = Set.univ)
```

```lean tightness
def atTopCompact [TopologicalSpace α] : Filter (Set α) :=
  ⨅ (K : Set α) (_ : IsCompact K), Filter.principal {B | K ⊆ B}
```

We will show one part of the Prohorov Theorem: If `[PolishSpace α]`, and `S : Set (Measure α)` and `∀ s ∈ S, IsProbabilityMeasure s`, then `[IsTightMeasureSet S]` implies relative compactness of `S` in the topology of weak convergence.

* A set `s` in a topological space is compact iff every ultrafilter in `s` converges.
* `α` is equivalent to a measurable subset of a compact space `β`. (This is not yet implemented in Mathlib.)
* If `IsCompact α`, any `S : Set (Measure α)` is relatively compact.
