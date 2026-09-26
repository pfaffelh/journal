p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
dev = open('scripts/_dev_C5ck.lean').read()
i1 = dev.index('theorem chapmanKolmogorov_of_unique_onedim')
i2 = dev.index('\nend CK')
thm = dev[i1:i2].rstrip() + '\n'
doc = '''
/-- **The Chapman--Kolmogorov relation**, the last sentence of `thm:absstrongmarkov` (manuscript,
Z. 4421), in the **time homogeneous** case `𝓧₀ r = 𝓧₀ 0`: if every `K x` solves the problem from
`δ x` and the one dimensional laws are unique, then

```
(K x) {π (s + t) ∈ C} = ∫ f, (K (π s f)) {π t ∈ C} ∂(K x),
```

i.e. `T_{s+t} = T_s T_t` for `T_u g x = ∫ g (π u) ∂K x`.

The proof is "the first assertion applied twice" of the manuscript, and the first application is
free: `setIntegral_indicator_eq_kernel` on the canonical space, with `X = id`, `P = K x`, the
filtration `𝓕₀`, and `A = univ`.

**Why homogeneous.** In the inhomogeneous case the relation reads
`T_{r,s} T_{s,t} = T_{r,t}` with `K_r x` solving the problem posed at `r`, and the same proof needs
`K_r x` as a solution **started at `0`** of a problem with a shift system -- the family
`u ↦ 𝓧₀ (r + u)`.  `IsShiftSystem` expresses every shifted family through `𝓧₀ 0` only, and a
shift system for the reindexed family does not follow from it: the increment clause for
`𝓧₀ (r + s)` would have to go through `𝓧₀ r`, and the structure says nothing about that.  The
inhomogeneous relation is therefore not a consequence of the hypotheses of this section as
stated. -/
'''
s = open(p).read()
k = s.index('\nend StrongMarkovKernel')
s = s[:k] + '\n' + doc + thm + s[k:]
open(p, 'w').write(s)
print(s[:s.index('theorem chapmanKolmogorov_of_unique_onedim')].count('\n') + 1)
