dev = open('scripts/_dev_B3markov.lean').read()
body = dev.split('theorem map_withDensity_comp_eq', 1)[1]
body = 'theorem map_withDensity_comp_eq' + body
doc1 = """/-- **A density read through a map pushes forward with it**: `(g ∘ Φ) • P`, carried along
`θ ∘ Φ`, is `g • (P.map Φ)` carried along `θ`.  `setLIntegral_map` on each measurable set. -/
"""
doc2 = """/-- **`thm:localuniq`, Markov half, on arbitrary spaces.**  Let `Φ : Ω → F` be the path map of an
adapted process on `(Ω, 𝓖, P)` whose law `P.map Φ` solves the local problem, and suppose that at
the time `r` the filtration `𝓖` knows no more than the path up to `r`:
`𝓖 r ≤ MeasurableSpace.comap Φ (𝓕₀ r)`.  Under `eq:localonedim` at `r`, the process is Markov at
`r` for `𝓖`.

The proof is `isMarkov_of_restart` with `X := Φ`, and the restart it asks for is `localRestart` on
the path space: an `𝓖 r`-measurable density `Z` factors as `Z' ∘ Φ` with `Z'` measurable for
`𝓕₀ r` (`StronglyMeasurable.exists_eq_measurable_comp`), clipped to the same bounds, and
`map_withDensity_comp_eq` moves the density to `P.map Φ`.

**The hypothesis on `𝓖 r` is where the ambient space differs from the canonical one.**  On the
path space it is `𝓕₀ r` itself.  On `Ω` it cannot be dropped: `hP` speaks of the law only, and
for the filtration that is `m` at every time the left hand side is `g (π (r + t) (Φ ·))` itself,
which is not `σ(X r)`-measurable in general.  An enlargement by a σ-algebra independent of the
path, which keeps the Markov property, is not covered by this statement; it needs the
independence and is `Martingale.supConst` in spirit, not this proof. -/
"""
body = body.replace('theorem map_withDensity_comp_eq', doc1 + 'theorem map_withDensity_comp_eq', 1)
body = body.replace('theorem isMarkov_of_unique_onedim_local_of_le_comap',
                    doc2 + 'theorem isMarkov_of_unique_onedim_local_of_le_comap', 1)
body = body.rstrip('\n')
p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = open(p).read()
anchor = "\nend LocalOnAmbient\n"
assert s.count(anchor) == 1
s = s.replace(anchor, "\n" + body + "\n" + anchor)
open(p, 'w').write(s)
print('ok')
