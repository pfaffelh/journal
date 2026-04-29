Here are some more general questions how stochastic processes are used in Mathlib: 

* Very general: Various times, I think the dependence on `ω` is not needed, since definitions/assertions are valid for any `f : \iota \to \R`. (Examples: `upcrossing`, `hittingBtwn`)
* `hittingBtwn f s n m ω` is the first time `f` hits `s` after `n` but before `m`. I would not have `m` in this definition, and take the `hittingBtwn f s n \wedge m` if needed. Or is this to avoid writing `withTop`?
* Why does hittingBtwn need [InfSet ι]?
* The definition of the lower and upper times coud be made through `mutual inductive`. Why wasn't this done?
* Why does `UpcrossingData` have the `n`?
