/-!
# Axiom record for `SkorokhodSpace/Suggested.lean`

**This file is a record, not a build target.**  There is no lake project in this
worktree, so it has no `import` and nothing to compile; it is a comment.  The
check it records is reproduced like this, and it takes a few minutes because
Mathlib is loaded:

    cp Suggested.lean ~/Code/lean/journal-facts/axcheck.lean
    # append one `#print axioms <name>` line per declaration
    cd ~/Code/lean/journal && lake env lean ~/Code/lean/journal-facts/axcheck.lean

`/axcheck.lean` and `/axcheck_tmp.lean` are git-ignored at the worktree root.

## 2026-09-08, twenty-third run

Thirteen declarations, the four of that run and the nine of the interrupted run
before it.  Every one printed `[propext, Classical.choice, Quot.sound]`, except
`min_max_pair_cases`, which printed `[propext]` alone.

* `SkorokhodSpace.tendsto_distWith_of_tendstoUniformlyOn`
* `SkorokhodSpace.tendsto_intWith_of_ae_tendsto_distWith`
* `SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp`
* `SkorokhodSpace.instCompleteSpace`
* `exhaustionMax_lt_exhaustionMax_of_no_gap`
* `exhaustionMin_lt_exhaustionMin_of_no_gap`
* `countable_radius_exhaustionMax`
* `countable_radius_exhaustionMin`
* `SkorokhodSpace.distWith_le_of_oscillation`
* `min_max_pair_cases`
* `dist_le_dist_of_mem_uIcc`
* `TimeChange.eq_of_gap_of_norm_lt`
* `TimeChange.eq_of_gap_below_of_norm_lt`

On the same day `Suggested.lean` itself goes through `lake env lean` against
Mathlib `v4.33.1` with `rc = 0` and six `sorry` warnings:
`exists_orderIso_isometry_real`, `SkorokhodSpace.instSeparableSpace`,
`SkorokhodSpace.measurableEmbedding_piDense`,
`SkorokhodSpace.borel_eq_iSup_comap_eval`, `SkorokhodSpace.tendsto_modulus` and
`SkorokhodSpace.isCompact_closure_iff`.
-/
