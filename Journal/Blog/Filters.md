# Filters in probability

The general question is:

Convergence in Mathlib is usually formulated with filters. I wonder how they can be useful in probability.

Let us start by recalling what a filter (and ultrafilter) is:

{docstring Filter}

{docstring Ultrafilter}

Our goal is to formulate tightness in terms of filters. Recall that tigthness means:

{docstring MeasureTheory.IsTightMeasureSet}

```
def MeasureTheory.Measure.IsTight {α : Type u_1} [TopologicalSpace α] [MeasurableSpace α] (ℙ : Measure α) : Prop := InnerRegularWRT ℙ IsCompact (fun x ↦ x = Set.univ)
```

```
def atTopCompact [TopologicalSpace α] : Filter (Set α) :=
  ⨅ (K : Set α) (_ : IsCompact K), Filter.principal {B | K ⊆ B}
```

We will show one part of the Prohorov Theorem: If `[PolishSpace α]`, and `S : Set (Measure α)` and `∀ s ∈ S, IsProbabilityMeasure s`, then `[IsTightMeasureSet S]` implies relative compactness of `S` in the topology of weak convergence.

* A set `s` in a topological space is compact iff every ultrafilter in `s` converges.
* `α` is equivalent to a measurable subset of a compact space `β`. (This is not yet implemented in Mathlib.)
* If `IsCompact α`, any `S : Set (Measure α)` is relatively compact.
