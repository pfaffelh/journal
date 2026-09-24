#!/usr/bin/env python3
"""Prüft die **Negativaussagen** der Roadmaps gegen frisches `upstream/master`.

Jede Zeile der beiden Listen unten ist eine Behauptung „Mathlib hat X nicht",
der Ort, an dem sie steht, und das Suchmuster, das sie widerlegen würde.  Das
Skript sucht mit `git grep` in `upstream/master` und meldet die Trefferzahl; ein
Treffer ist kein Gegenbeweis, sondern eine Stelle zum Nachlesen.

`CLAIMS` sind die Behauptungen der vier `README.md` und der drei
`Suggested.lean`, `CLAIMS_TODO8` die Lücken von `TODO.md` Punkt 8.

Jede Zeile trägt als letztes Feld die Dateien, in denen ein Treffer **bekannt
und harmlos** ist — Namensvettern, Literaturverweise, der jeweils benachbarte
Satz, den die Behauptung selbst zitiert.  Das Skript meldet `UNERWARTET`, sobald
ein Treffer in einer anderen Datei steht; genau das ist die Stelle, an der eine
Negativaussage falsch geworden sein könnte.  Eine leere Liste heißt: kein
Treffer erwartet.

**Was das Skript nicht leistet.**  Es prüft Zeichenketten, nicht Aussagen.  Eine
Lücke kann unter einem Namen gefüllt worden sein, den kein Muster hier trifft;
umgekehrt ist `UNERWARTET` kein Befund, sondern eine Leseaufgabe.  Deklarationen
innerhalb eines `namespace` stehen im Quelltext ohne ihr Präfix — ein Muster
`Foo.bar` findet `lemma bar` in `namespace Foo` **nicht**.

    python3 scripts/check_negatives.py   -> scripts/_citations/negatives.md
"""
import subprocess, os

# Alle Pfade relativ zur Wurzel des Worktrees, damit das Skript aus jedem
# Verzeichnis heraus lauffähig ist.
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

MATHLIB4 = '/home/pfaffelh/Code/lean/mathlib4'
OUT = 'scripts/_citations'

# (Kurzname, Fundstelle der Behauptung, Behauptung, Suchmuster, Pfadfilter)
CLAIMS = [
    # Die beiden Behauptungen über `cadlag` und `IsCadlag` sind mit #43352
    # hinfällig geworden: `Mathlib/Topology/Order/Cadlag.lean` trägt
    # `IsRightContinuous`, `IsLeftContinuous`, `IsCadlag` und `IsCaglad`.  Die
    # Roadmap sagt das seit dem 2026-09-07 selbst; hier stehen sie nicht mehr,
    # weil eine Behauptung, die von ihrem eigenen Fundort widerrufen ist, in
    # dieser Liste nur Lärm erzeugt.  Was von ihr bleibt, ist die Aussage über
    # den *Raum*, und die steht als `skorokhod-space` da.
    ('skorokhod-space', 'SkorokhodSpace/README.md:3',
     'Der Skorokhodraum selbst — die càdlàg-Pfade mit der J₁-Topologie — kommt '
     'in Mathlib nicht vor; nur das Prädikat.',
     'SkorokhodSpace|skorokhodSpace|J1Topology|Skorokhod', 'Mathlib/'),
    ('memoryless', 'MartingaleProblems/README.md:743',
     'Eine Suche nach `memoryless` über `Mathlib/` liefert nichts.',
     'memoryless', 'Mathlib/'),
    ('dissipative', 'MartingaleProblems/README.md:3617',
     'Das Wort `dissipative` kommt in Mathlib nirgends vor.',
     'dissipative', 'Mathlib/'),
    ('semigroup-of-operators', 'MartingaleProblems/README.md:3617',
     'Mathlib hat keine Operatorhalbgruppe.',
     'OneParameterSemigroup|StronglyContinuousSemigroup|C0Semigroup|HilleYosida'
     '|Hille_Yosida|SemigroupGenerator', 'Mathlib/'),
    ('quasi-left', 'MartingaleProblems/README.md:3171',
     'Die Strings `quasi-left` und `QuasiLeftContinuous` kommen nirgends vor.',
     'QuasiLeftContinuous|quasi-left|quasiLeftContinuous', 'Mathlib/'),
    ('doob-Lp', 'MartingaleProblems/README.md:38',
     "Doobs `Lᵖ`-Ungleichung fehlt für jeden Index.",
     'eLpNorm_iSup|maximal_ineq|doob_Lp|Lp_maximal', 'Mathlib/Probability/'),
    ('submartingale-regularization', 'MartingaleProblems/README.md:3035',
     'Submartingal-Regularisierung hat Mathlib nicht.',
     'regulariz|leftLim', 'Mathlib/Probability/Martingale/'),
    ('iIndepFun-to-iIndepSet', 'MartingaleProblems/README.md:724',
     'Kein Lemma von `iIndepFun` der Koordinaten zu `iIndepSet` der Ereignisse.',
     'iIndepSet_of_iIndepFun|iIndepFun.iIndepSet|IndepSet.*of.*IndepFun',
     'Mathlib/Probability/'),
    ('volume-Ioc01-prob', 'WeakConvergence/Suggested.lean:4047',
     'Mathlib hat keine `IsProbabilityMeasure`-Instanz für `volume` auf `(0,1]`.',
     'IsProbabilityMeasure.*Ioc|isProbabilityMeasure.*volume.*Ioc'
     '|Ioc.*volume.*IsProbabilityMeasure', 'Mathlib/'),
    ('skorokhod-representation', 'WeakConvergence/README.md:838',
     'Mathlib hat die Skorohod-Darstellung nicht.',
     'Skorokhod|Skorohod', 'Mathlib/'),
    ('conditional-expectation-functional', 'WeakConvergence/Suggested.lean:5213',
     'Die funktionale Form ist abwesend.',
     'condExp_ae_eq_condExp_of', 'Mathlib/'),
    ('integrating-factor', 'MartingaleProblems/Suggested.lean, section YuleProcess',
     'Mathlib hat keine lineare Differentialgleichung erster Ordnung und keinen '
     'integrierenden Faktor; `Mathlib/Analysis/ODE/` hat sechs Dateien, keine '
     'davon über den linearen Fall.',
     'integrating factor|integratingFactor|linear_ODE|linearODE'
     '|variation of constants', 'Mathlib/'),
    ('first-order-pde', 'MartingaleProblems/README.md, Meilenstein 4',
     'Mathlib hat keine partielle Differentialgleichung erster Ordnung und keine '
     'Charakteristikenmethode, also kein Werkzeug für die erzeugende Funktion '
     'eines Geburt-Tod-Prozesses.',
     'method of characteristics|partial differential equation|characteristicCurve'
     '|characteristic curve', 'Mathlib/'),
    ('generalised-inverse', 'MartingaleProblems/README.md, Meilenstein 4',
     'Mathlib hat keine verallgemeinerte Inverse einer monotonen Funktion und '
     'keine Quantilfunktion; `StrictMono.orderIsoOfSurjective` verlangt '
     'Bijektivität auf dem ganzen Typ und trägt eine auf einer Halbgeraden '
     'streng monotone Funktion nicht.',
     'quantile|generalized inverse|generalised inverse|rightContinuousInverse'
     '|monotoneInverse', 'Mathlib/'),
    ('point-process', 'MartingaleProblems/README.md, Meilenstein 4',
     'Mathlib hat keinen Punktprozeß, keinen Zählprozeß, keinen Kompensator '
     'und keinen Hawkes-Prozeß; die pfadabhängige Variante hat daher auch für '
     'ihr Beispiel nichts zu übernehmen.',
     'hawkes|selfExciting|self-exciting|PointProcess|pointProcess'
     '|countingProcess|compensator', 'Mathlib/'),
    ('measure-smul-cancel', 'Facts/INVENTAR.md, Lauf 2026-09-14 (zweiter)',
     'Mathlib hat keine Kürzungsregel für das Skalieren von Maßen: '
     '`c • μ = c • ν ↔ μ = ν` für `c ≠ 0`, `c ≠ ⊤` steht nirgends, weder als '
     'Äquivalenz noch als Injektivität, weshalb `lem:propagation` die '
     'Normierung punktweise über `Measure.ext` zurücknimmt.',
     'smul_right_injective|smul_left_cancel|smul_right_inj|smul_eq_smul_iff',
     'Mathlib/MeasureTheory/Measure/'),
    ('progressive-rightcontinuous',
     'MartingaleProblems/README.md, Meilenstein 6, Naht zu Meilenstein 4',
     'Mathlib leitet fortschreitende Meßbarkeit aus **Stetigkeit** der Pfade ab '
     '(`StronglyAdapted.isStronglyProgressive_of_continuous`), aus einem '
     'diskreten Index (`..._of_discrete`) und aus einem Grenzwert '
     '(`isStronglyProgressive_of_tendsto`), aber aus **Rechtsstetigkeit** der '
     'Pfade nicht — obwohl das der Standardfall der Sprungprozesse ist und der '
     'Beweis die dyadische Näherung von oben plus `..._of_tendsto` ist.',
     'isStronglyProgressive.*[Rr]ight|progMeasurable.*[Rr]ight'
     '|[Rr]ightContinuous.*[Pp]rogressive',
     'Mathlib/'),
    ('volterra-resolvent', 'MartingaleProblems/README.md, Meilenstein 14',
     'Die Volterra-Resolvente eines Kerns in `L¹_loc` und die '
     'Erneuerungsgleichung `m = m₀ + φ ⋆ m` kommen in Mathlib nicht vor. '
     'Vorhanden sind die Faltung (`MeasureTheory.convolution`, '
     '`MeasureTheory.lconvolution`) und die Neumann-Reihe in einer normierten '
     'Algebra (`NormedRing.inverse_one_sub`), die `‖φ‖ < 1` **global** '
     'verlangt; der kausale Trick — auf einem kurzen Fenster arbeiten und '
     'fortschreiten — braucht das gerade nicht.',
     'volterra|Volterra|[Rr]enewal|resolventKernel|resolvent_kernel',
     'Mathlib/'),
    ('lconvolution-support', 'MartingaleProblems/README.md, Meilenstein 14',
     'Die Trägerinklusion `support (f ⋆ₗ[μ] g) ⊆ support f + support g` steht '
     'für die Bochner-Faltung (`support_convolution_subset`, '
     '`Mathlib/Analysis/Convolution.lean`) und **nicht** für `lconvolution`. '
     'Sie ist es, die eine Faltung auf der Halbachse kausal macht.',
     'support_lconvolution|support_mlconvolution|lconvolution.*support'
     '|mlconvolution.*support',
     'Mathlib/'),
    ('progressive-continuous-comp', 'MartingaleProblems/Suggested.lean, '
     '„The assembly at an image path"',
     'Die Nachkomposition eines progressiv meßbaren Prozesses mit einer '
     'stetigen Abbildung steht in Mathlib nicht.  '
     '`Mathlib/Probability/Process/Adapted.lean` beweist '
     '`IsStronglyProgressive.mul`, `.inv` und `.div\'` einzeln und hat kein '
     '`continuous_comp`, aus dem sie folgten; `IsStronglyProgressive.comp` ist '
     'die Komposition im **Zeitargument**.  `Mathlib/Topology/Order/Cadlag.lean` '
     'hat die Abstraktion als `IsCadlag.continuous_comp` sehr wohl.',
     'IsStronglyProgressive.continuous_comp|StronglyAdapted.continuous_comp'
     '|IsProgressive.continuous_comp',
     'Mathlib/'),
    ('rightcontinuous-measurable', 'MartingaleProblems/README.md, Meilenstein 11, '
     'und `MartingaleProblems/Suggested.lean`, `measurable_of_tendsto_nhdsGE`',
     'Daß eine **rechtsstetige** reelle Funktion einer reellen Veränderlichen '
     'Borel-meßbar ist, steht in Mathlib nicht. '
     '`Mathlib/Topology/Order/Cadlag.lean`, wo `IsRightContinuous` und '
     '`IsCadlag` wohnen, ist eine Topologiedatei und trägt überhaupt keine '
     'Meßbarkeit; die Vorkommen von `IsRightContinuous` außerhalb davon sind '
     'die in `Probability/Process/` und handeln von **Filtrationen**, nicht von '
     'Pfaden.  Vorhanden ist `Monotone.measurable` — so wird eine '
     '`StieltjesFunction` meßbar, über die Monotonie und nicht über die '
     'Rechtsstetigkeit —, und ein càdlàg-Pfad ist weder monoton noch stetig.',
     'measurable[a-z_]*_of_[a-z_]*rightcontinuous'
     '|isrightcontinuous[a-z_.]*measurable|iscadlag[a-z_.]*measurable',
     'Mathlib/'),
    ('tight-uniform-limit', 'WeakConvergence/Suggested.lean, '
     '`isTightMeasureSet_map_of_forall_exists_dist_le`',
     'Mathlib transportiert Straffheit längs **einer** Abbildung '
     '(`IsTightMeasureSet.map`, für stetige), aber nicht längs eines '
     'gleichmäßigen Grenzwertes von Abbildungen.  `isTightMeasureSet_of_tendsto` '
     'ist etwas anderes: dort konvergieren die **Maße**, nicht die Abbildung.',
     'istightmeasureset[a-z_.\']*of_forall_exists_dist'
     '|istightmeasureset[a-z_.\']*tendstouniformly'
     '|tendstouniformly[a-z_.\']*istight',
     'Mathlib/'),
    ('continuousat-finset-prod', 'SkorokhodSpace/Suggested.lean, '
     '`SkorokhodSpace.continuousAt_of_mem_evalFuns`',
     'Mathlib hat die Stetigkeit eines endlichen Produkts **an einer Stelle** '
     'unter keinem Namen: `continuous_finsetProd` und `continuousOn_finsetProd` '
     'stehen in `Mathlib/Topology/Algebra/Monoid.lean`, eine `ContinuousAt`-'
     'Fassung nicht.  Zu nehmen ist `tendsto_finsetProd`, weil `ContinuousAt` '
     'ein `Tendsto` längs `𝓝 y` ist.',
     'continuousat_finsetprod|continuousat_finset_prod'
     '|continuousat[a-z_.\']*\\.finsetprod',
     'Mathlib/'),
    ('martingale-smaller-filtration', 'MartingaleProblems/Suggested.lean, '
     '`MeasureTheory.tendsto_integral_mpTest_sub_mul_of_approx` und '
     '`MeasureTheory.comap_pathOfProcess_le_of_stronglyAdapted`',
     'Mathlib hat keinen Satz, der ein Martingal von einer Filtration auf eine '
     '**kleinere** trägt, für die es adaptiert bleibt (der Turmschluß).  '
     'Gesucht wurde am 2026-09-21 nicht nach der Vokabel, sondern nach der '
     'Gestalt: in ganz `Mathlib/Probability/` steht **keine** Aussage mit zwei '
     'Filtrationen im Satz; `Mathlib/Probability/Martingale/Basic.lean` hält '
     'die Filtration über die ganze Datei fest.',
     'mono_filtration|martingale_of_le_filtration|martingale\\.mono\\b'
     '|submartingale\\.mono_filtration',
     'Mathlib/'),
]


# Die zweiundzwanzig Lücken von `TODO.md` Punkt 8.  Sechstes Feld: die Dateien,
# in denen ein Treffer bekannt und harmlos ist.
CLAIMS_TODO8 = [
    ('traj-homogeneity', 'TODO.md Punkt 8, erste Lücke',
     'Die Zeithomogenität von `Kernel.traj` — die Verschiebung einer homogenen '
     'Markovkette ist wieder dieselbe Kette — steht in Mathlib nicht.',
     'shift', ['Mathlib/Probability/Kernel/IonescuTulcea/'], []),
    ('exp-tail', 'TODO.md Punkt 8, zweite Lücke',
     'Gedächtnislosigkeit und Schwanz der Exponentialverteilung fehlen; '
     'vorhanden ist allein die Verteilungsfunktion `cdf_expMeasure_eq`.',
     'memoryless|expMeasure_Ioi|Ioi.*expMeasure|expMeasure.*Ioi',
     ['Mathlib/Probability/Distributions/'], []),
    ('unif-near-compact', 'TODO.md Punkt 8, siebenundzwanzigste Lücke',
     'Die einseitige gleichmäßige Stetigkeit in der Nähe eines Kompaktums — '
     'erster Punkt in `K`, zweiter frei — fehlt; Mathlib hat allein '
     '`IsCompact.uniformContinuousOn_of_continuous`, die beide Punkte '
     'einsperrt.',
     'exists_pos_forall_dist|forall_dist_image_lt|uniformContinuousOn_of_mem_nhdsSet',
     ['Mathlib/Topology/'], []),
    ('exp-mean', 'TODO.md Punkt 8, vierundzwanzigste Lücke',
     'Der Erwartungswert der Exponential- und der Gammaverteilung fehlt; die '
     'einzigen Integrale beider Dateien sind die Normierung und die '
     'Verteilungsfunktion.',
     'mean_|variance_|integral_id|expectation',
     ['Mathlib/Probability/Distributions/Exponential.lean',
      'Mathlib/Probability/Distributions/Gamma.lean'], []),
    # Hier stand vom 2026-09-18 an eine zweite Behauptung: ein skaliertes
    # `GammaIntegral_convergent` gebe es nicht.  Sie ist **widerlegt**, und zwar
    # von diesem Skript selbst, im vierten Lauf des 2026-09-18, beim ersten
    # Durchlauf nach ihrer Aufnahme.  Mathlib hat sie als
    # `integrableOn_rpow_mul_exp_neg_mul_rpow`
    # (`Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:74`, in
    # v4.33.1 wie auf `upstream/master` `a218e50f981`), für `exp (−b·x^p)` und
    # dort nur bei `p = 2` benutzt; bei `p = 1` ist es genau die Aussage.
    #
    # Sie steht hier nicht mehr, weil eine widerlegte Behauptung keine zu
    # prüfende ist.  Was von ihr bleibt, ist die Lehre, die der Pfadfilter
    # verursacht hat: die Behauptung war auf `Analysis/SpecialFunctions/Gamma/`
    # eingeschränkt und in *diesem* Verzeichnis wahr.  Ein Pfadfilter, der eng
    # genug ist, macht jede Negativaussage wahr.  Deshalb steht in diesem
    # Skript ab jetzt `Mathlib/` als Filter, wo die Behauptung von der
    # Bibliothek und nicht von einer Datei handelt.
    ('convergence-in-measure-complete', 'TODO.md Punkt 8, dritte Lücke',
     '`ConvergenceInMeasure.lean` enthält das Wort `cauchy` nicht ein '
     'einziges Mal; die Vollständigkeit der Konvergenz im Maß fehlt.',
     'cauchy', ['Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean'], []),
    ('infinitePi-head-tail', 'TODO.md Punkt 8, vierte Lücke',
     'Die Abspaltung der ersten Koordinate vom Schwanz im unendlichen Produkt — '
     '`(infinitePi μ).map (fun x ↦ (x 0, x ∘ Nat.succ)) = μ.prod (infinitePi μ)` '
     '— fehlt.',
     'infinitePi.*Nat\\.succ|infinitePi.*\\.prod|Measure\\.prod.*infinitePi',
     ['Mathlib/'],
     # `infinitePi_map_eval_prod` ist das Paar **zweier Koordinaten**, das die
     # Behauptung selbst nennt; der zweite Treffer ist ein `Finset.prod`.
     ['Mathlib/Probability/Independence/InfinitePi.lean',
      'Mathlib/Probability/ProductMeasure.lean']),
    ('martingale-stability-stopping', 'TODO.md Punkt 8, fünfte Lücke',
     'Der gestoppte Martingalsatz in stetiger Zeit fehlt; ein '
     '`IsStable 𝓕 (fun Y ↦ Martingale Y 𝓕 P)` gibt es nicht, und '
     '`OptionalStopping.lean` steht in ganzer Länge über `Filtration ℕ`.',
     # `IsStable` selbst **gibt es** (`Process/LocalProperty.lean:142`), und die
     # `Locally`-Maschinerie daneben; was fehlt, ist der Zeuge für `Martingale`
     # — in `LocalProperty.lean` kommt das Wort `Martingale` nicht vor.
     'IsStable', ['Mathlib/Probability/'],
     ['Mathlib/Probability/Kernel/Category/Stoch.lean',
      'Mathlib/Probability/Process/LocalProperty.lean']),
    ('optional-stopping-index', 'TODO.md Punkt 8, fünfte Lücke',
     '`OptionalStopping.lean` trägt den Index `ℕ` in seinem Variablenblock; ein '
     'Treffer auf `Filtration ι` wäre die Verallgemeinerung.',
     'Filtration ι', ['Mathlib/Probability/Martingale/OptionalStopping.lean'], []),
    ('volterra', 'TODO.md Punkt 8, achte Lücke',
     'Die Volterra-Resolvente und die Faltungsalgebra der kausalen Kerne fehlen.',
     'volterra|renewal|resolvent kernel|Neumann series', ['Mathlib/'], []),
    ('augmentation', 'TODO.md Punkt 8, neunte Lücke',
     'Die augmentierte Filtration und die üblichen Bedingungen fehlen, und mit '
     'ihnen die Aussage, daß die bedingte Erwartung sich unter Vergrößerung um '
     'f.s. schon vorhandene Mengen nicht ändert.',
     'augmentedFiltration|Filtration\\.augment|usualConditions'
     '|IsRightContinuousFiltration|condExp_eq_condExp_of', ['Mathlib/'], []),
    ('freezing', 'TODO.md Punkt 8, elfte Lücke',
     'Das Einfrieren fehlt; Mathlib hat allein den entarteten Fall '
     '`condExp_indep_eq` und dessen eine Verwendung in `BorelCantelli.lean`.',
     'freezing|IndepFun\\.condExp|condExp_indep', ['Mathlib/'],
     ['Mathlib/Probability/BorelCantelli.lean',
      'Mathlib/Probability/ConditionalExpectation.lean']),
    ('measurable-primitive', 'TODO.md Punkt 8, zwölfte Lücke',
     'Die gemeinsame Meßbarkeit der Stammfunktion in Parameter und oberer '
     'Grenze fehlt; vorhanden sind allein Stetigkeitsaussagen.',
     'measurable.*primitive|primitive.*easurable',
     ['Mathlib/MeasureTheory/Integral/'], []),
    ('compProd-first-factor', 'TODO.md Punkt 8, dreizehnte Lücke',
     'Das Vorschieben des **ersten** Faktors eines `compProd` hat keinen Namen; '
     '`Measure.compProd_map` ist der zweite, und der erste steht nur als '
     'Zwischenschritt einer `calc`-Kette in `HasCondDistrib.comp_right`.',
     'compProd_comap|comap_compProd', ['Mathlib/'], []),
    ('hasconddistrib-condExp', 'TODO.md Punkt 8, vierzehnte Lücke',
     'Aus `HasCondDistrib` folgt in Mathlib keine bedingte Erwartung; die Datei '
     'enthält keinen einzigen Treffer für `condExp`.',
     'condExp', ['Mathlib/Probability/HasCondDistrib.lean'], []),
    ('condExp-sup-indep', 'TODO.md Punkt 8, fünfzehnte Lücke',
     'Die bedingte Erwartung unter Vergrößerung der bedingenden σ-Algebra um '
     'einen unabhängigen Block — `μ[f | m₁ ⊔ m₂] =ᵐ μ[f | m₁]` — fehlt.',
     'condExp.*⊔|⊔.*condExp|condExp_sup', ['Mathlib/'], []),
    ('condExp-fubini', 'TODO.md Punkt 8, sechzehnte Lücke',
     'Fubini für die bedingte Erwartung fehlt; die Vertauschung eines '
     'Parameterintegrals mit `condExp` steht nirgends.',
     'condExp_integral|integral_condExp_comm|condExp_intervalIntegral',
     ['Mathlib/'], []),
    ('abscont-comp', 'TODO.md Punkt 8, siebzehnte Lücke',
     'Die Komposition einer absolut stetigen mit einer lipschitzstetigen '
     'Funktion fehlt; die absolute Stetigkeit ist unter Summe, Produkt und '
     'Skalar abgeschlossen, unter Komposition nicht.',
     'AbsolutelyContinuousOnInterval.*comp|comp.*AbsolutelyContinuousOnInterval',
     ['Mathlib/'], ['Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean']),
    ('substitution-rule', 'TODO.md Punkt 8, siebzehnte Lücke, zweite Hälfte',
     'Die Substitutionsregel `∫_a^b f_u · g'"'"' (∫_c^u f) du = g (∫_c^b f) − '
     'g (∫_c^a f)` für bloß intervallintegrierbares `f` fehlt; Mathlib hat die '
     'partielle Integration und die Substitution mit Ableitung an **jedem** '
     'Punkt. Die Kompositionsaussage darunter steht auf `master` seit '
     '#42996 und ist keine Lücke mehr.',
     'integral_mul_deriv_comp|deriv_comp_intervalIntegral', ['Mathlib/'], []),
    ('filtration-comp', 'TODO.md Punkt 8, neunzehnte Lücke',
     'Die Umindizierung einer Filtration längs einer monotonen Abbildung fehlt.',
     'Filtration\\.comp|Filtration\\.reindex|Filtration\\.precomp',
     ['Mathlib/'], []),
    ('submartingale-min', 'TODO.md Punkt 8, zwanzigste Lücke',
     'Die Minimalungleichung für Submartingale fehlt; die Zeichenkette `inf` '
     'mit Apostroph kommt in `Mathlib/Probability/Martingale/` nicht vor.',
     "inf'", ['Mathlib/Probability/Martingale/'], []),
    ('martingale-clm', 'TODO.md Punkt 8, einundzwanzigste Lücke',
     'Ein Martingal hinter einer stetigen linearen Abbildung fehlt; '
     '`ContinuousLinearMap` und `RCLike` kommen in '
     '`Mathlib/Probability/Martingale/` und `Mathlib/Probability/Process/` '
     'gar nicht vor.',
     'ContinuousLinearMap|RCLike',
     ['Mathlib/Probability/Martingale/', 'Mathlib/Probability/Process/'], []),
    ('stopping-isup', 'TODO.md Punkt 8, zweiundzwanzigste Lücke',
     'Das Supremum einer Folge von Stoppzeiten fehlt; Mathlib hat nur das '
     'Infimum (`IsStoppingTime.iInf`, `IsStoppingTime.biInf`), und ein '
     '`protected lemma iSup` oder `biSup` kommt in `Mathlib/Probability/` '
     'nicht vor.',
     'protected (lemma|theorem) (iSup|biSup)',
     ['Mathlib/Probability/'], []),
    ('unifintegrable-distribution',
     'TODO.md Punkt 8, dreiundzwanzigste Lücke',
     'Die gleichgradige Integrierbarkeit über einer Folge verschiedener Räume '
     'zusammen mit der Verteilungskonvergenz gibt es nicht: `UnifIntegrable` '
     'kommt in `ConvergenceInDistribution.lean` nicht vor, und die '
     'Erwartungswertkonvergenz aus Verteilungskonvergenz plus gleichgradiger '
     'Integrierbarkeit steht in keiner Fassung da.',
     'UnifIntegrable|unifIntegrable',
     ['Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean'], []),
    ('condexp-sup-indep', 'TODO.md Punkt 8, fünfundzwanzigste Lücke',
     'Die unerhebliche Vergrößerung der bedingten Erwartung fehlt: '
     '`μ[f | m₁ ⊔ m₂] = μ[f | m₁]` für `m₂` unabhängig von `m₁ ⊔ σ(f)`. '
     'Mathlib hat nur den Fall `m₁ = ⊥`, `condExp_indep_eq`; die Zeichenketten '
     '`condExp_sup` und `condexp_sup` kommen nirgends vor.  Der Filter ist '
     '`Mathlib/` und kein engerer -- die Behauptung handelt von der '
     'Bibliothek und nicht von einer Datei.',
     'condExp_sup|condexp_sup', ['Mathlib/'], []),
    ('counting-layercake', 'TODO.md Punkt 8, sechsundzwanzigste Lücke',
     'Die **zählende** Schichtkuchenformel fehlt: '
     '`∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑'"'"' n, μ {x | n < f x}` für `f : α → ℕ`. '
     'Mathlib hat die stetige Fassung (`lintegral_eq_lintegral_meas_lt`, '
     '`Layercake.lean`), die eine Ordnung auf dem Index und σ-Endlichkeit '
     'braucht; die zählende braucht beides nicht.',
     'lintegral_natCast|integrable_natCast|tsum_measure_lt|lintegral_eq_tsum_meas',
     ['Mathlib/'], []),
    ('martingale-setIntegral-weight',
     'MartingaleProblems/README.md, Meilenstein 5',
     'Ein Martingal gegen eine **beschränkte** Gewichtsfunktion getestet hat in '
     'Mathlib keinen Satz; der Indikatorfall steht als '
     '`Martingale.setIntegral_eq` und ist die einzige Fassung.',
     'setIntegral.*[Mm]artingale|[Mm]artingale.*setIntegral',
     ['Mathlib/Probability/Martingale/'],
     ['Mathlib/Probability/Martingale/Basic.lean',
      'Mathlib/Probability/Martingale/OptionalStopping.lean']),
    ('stoppingtime-add-const-nnreal',
     'MartingaleProblems/README.md, Meilenstein 11; TODO.md Punkt 8',
     'Eine Stoppzeit um eine Konstante zu verschieben, hat in Mathlib genau '
     'zwei Fassungen — `IsStoppingTime.add_const` über einer additiven Gruppe '
     'und `IsStoppingTime.add_const\'` über abzählbarem Index —, und beide '
     'sperren `ℝ≥0` aus; `OrderedSub` kommt unter `Mathlib/Probability/` nicht '
     'vor.',
     'OrderedSub',
     ['Mathlib/Probability/'],
     []),
    ('optional-sampling-two-times-nnreal',
     'MartingaleProblems/README.md, Meilenstein 11; TODO.md Punkt 8',
     'Optionales Sampling zwischen **zwei** Stoppzeiten steht in Mathlib nur in '
     '`Probability/Martingale/OptionalSampling.lean`, und dort in drei '
     'Fassungen, die alle `ℝ≥0` aussperren (`[Countable ι]`, abzählbarer '
     'Wertebereich beider Zeiten, `[DiscreteTopology ι]`). In keiner anderen '
     'Datei kommen `condExp` und `stoppedValue` in derselben Zeile vor.',
     'condExp.*stoppedValue|stoppedValue.*condExp',
     ['Mathlib/'],
     ['Mathlib/Probability/Martingale/OptionalSampling.lean']),
    ('elpnorm-measurable-in-parameter',
     'MartingaleProblems/Suggested.lean, `IsApproximatingPair`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Die Meßbarkeit einer `eLpNorm` **im Parameter** — also von '
     '`ω ↦ eLpNorm (fun s ↦ Z s ω) q ν` für gemeinsam meßbares `Z` — steht in '
     'Mathlib in keiner Fassung; weder `MeasureTheory/Integral/Prod.lean` noch '
     'das Verzeichnis `LpSeminorm/` trägt sie. Deshalb ist die f.s. '
     '`MemLp`-Eigenschaft ein eigenes Feld von `IsApproximatingPair` und keine '
     'Folge der Schranke an den Mittelwert.',
     'measurable_eLpNorm|eLpNorm_prod|stronglyMeasurable_eLpNorm'
     '|eLpNorm.*prod_right',
     ['Mathlib/'],
     []),
    ('le-lintegral-finset-sum',
     'MartingaleProblems/Suggested.lean, `le_lintegral_finsetSum`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Die **Superadditivität** des unteren Integrals — `∑ ∫⁻ f i ≤ ∫⁻ ∑ f i`, '
     'die Richtung, die ohne Meßbarkeit gilt — steht in Mathlib nur für **zwei** '
     'Summanden, als `MeasureTheory.le_lintegral_add` '
     '(`MeasureTheory/Integral/Lebesgue/Add.lean:273`); eine `Finset`-Fassung '
     'gibt es nicht, und `lintegral_finsetSum` (`:356`) ist die Gleichheit unter '
     '`Measurable`. Es ist keine weitere Deklaration `le_lintegral…` in der '
     'ganzen Bibliothek.',
     'theorem le_lintegral|lemma le_lintegral',
     ['Mathlib/'],
     ['Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean']),
    ('abs-of-martingale-is-submartingale',
     'MartingaleProblems/Suggested.lean, `Martingale.submartingale_abs`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Daß der **Betrag** eines Martingals ein Untermartingal ist, steht in '
     'Mathlib in keiner Fassung: `Mathlib/Probability/Martingale/Basic.lean` '
     'trägt `Submartingale.pos` für den Positivteil und `Submartingale.sup` für '
     'das Supremum zweier, und im ganzen Verzeichnis '
     '`Mathlib/Probability/Martingale/` kommt `abs` in genau einem Namen vor, '
     '`Submartingale.exists_tendsto_of_abs_bddAbove_aux`. Am 2026-09-21 mit '
     '`example … := by exact?` gegen den master-Worktree geprüft: `exact?` '
     'schließt das Ziel nicht.',
     'abs_submartingale|submartingale_abs|Martingale.abs',
     ['Mathlib/'],
     []),
    ('maximal-ineq-event-form',
     'MartingaleProblems/Suggested.lean, `Martingale.measure_exists_abs_ge_le`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Die Maximalungleichung in **Ereignisgestalt** — '
     '`ε · P {∃ k ≤ N, ε ≤ |f k|} ≤ ∫ |f N|` — steht in Mathlib nicht. '
     'Vorhanden ist `MeasureTheory.maximal_ineq` '
     '(`Mathlib/Probability/Martingale/OptionalStopping.lean:144`) über '
     '`Finset.sup'"'"'` und mit dem Integral über dem Ereignis selbst; die '
     'beiden Umformungen (`Finset.le_sup'"'"'_iff` und '
     '`MeasureTheory.setIntegral_le_integral`) bleiben dem Verbraucher. Am '
     '2026-09-21 mit `example … := by exact?` gegen den master-Worktree '
     'geprüft: `exact?` schließt das Ziel nicht.',
     'measure_exists_abs|maximal_ineq_event|measure_le_of_maximal',
     ['Mathlib/'],
     []),
    ('partial-sum-martingale',
     'MartingaleProblems/Suggested.lean, `martingale_partialSum_of_iIndepFun`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Daß die **Partialsummen** unabhängiger, zentrierter, integrierbarer '
     'Größen ein Martingal bilden, steht in Mathlib in keiner Fassung: '
     '`partialSum` kommt unter `Mathlib/Probability/` in keinem '
     'Deklarationsnamen vor. Vorhanden sind die Bausteine — '
     '`ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt` '
     '(`Mathlib/Probability/BorelCantelli.lean:43`) und '
     '`MeasureTheory.condExp_indep_eq` '
     '(`Mathlib/Probability/ConditionalExpectation.lean:42`) —, nicht aber der '
     'Satz. Am 2026-09-21 mit `example … := by exact?` gegen den '
     'master-Worktree geprüft: `exact?` schließt das Ziel nicht.',
     'partialSum|partial_sum_martingale|martingale_sum_range',
     ['Mathlib/Probability/'],
     []),
    ('integral-abs-le-sqrt-integral-sq',
     'MartingaleProblems/Suggested.lean, `integral_abs_le_sqrt_integral_sq`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Die reelle Gestalt `∫ |f| ≤ √(∫ f ^ 2)` über einem '
     'Wahrscheinlichkeitsmaß steht in Mathlib nicht. Vorhanden ist der '
     'Vergleich über `eLpNorm` '
     '(`MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`, '
     '`Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:115`) und '
     'Hölder über `(∫ f ^ p) ^ (1 / p)` '
     '(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`, '
     '`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1225`); die '
     'Umrechnung in beide Richtungen bleibt dem Verbraucher. Am 2026-09-21 mit '
     '`example … := by exact?` gegen den master-Worktree geprüft, in der '
     'Jensen- wie in der Wurzelgestalt: `exact?` schließt beide Ziele nicht.',
     'integral_abs_le_sqrt|sq_integral_le_integral_sq|integral_abs_le_rpow',
     ['Mathlib/'],
     []),
    ('filtration-reindex',
     'MartingaleProblems/Suggested.lean, `floorFiltration`; '
     'MartingaleProblems/README.md, Meilenstein 11',
     'Mathlib hat keine Umindizierung einer Filtration laengs einer monotonen '
     'Abbildung. Die Konstruktionen in '
     '`Mathlib/Probability/Process/Filtration.lean` sind `const`, '
     '`filtrationOfSet`, `natural`, `piLE`, `piFinset` und '
     '`cylinderEventsCompl`, und keine davon aendert den Index; am 2026-09-21 '
     'am Quelltext nachgesehen.',
     'Filtration.comap|Filtration.reindex|Filtration.comp\\b|reindexFiltration'
     '|floorFiltration',
     ['Mathlib/'],
     []),
    ('tight-finite',
     'TODO.md Punkt 8; MartingaleProblems/Suggested.lean, '
     '`isTightMeasureSet_of_finite`; MartingaleProblems/README.md, '
     'Meilenstein 11',
     'Mathlib hat die Straffheit einer **endlichen** Menge endlicher Masse '
     'nicht. `Mathlib/MeasureTheory/Measure/Tight.lean` traegt '
     '`isTightMeasureSet_singleton` (:99) und im Namensraum '
     '`IsTightMeasureSet` die Aussagen `of_compactSpace` (:109), `subset` '
     '(:114), `union` (:119), `inter` (:125), `map` (:129), `prodMk` (:143); '
     'das Wort `Finite` steht dort nur in den Doc-Kommentaren der '
     'Einzelmass-Aussagen. Am 2026-09-21 am Quelltext nachgesehen, nach dem '
     'letzten Namensbestandteil **innerhalb der Datei** und nicht nach dem '
     'qualifizierten Namen.',
     'isTightMeasureSet_of_finite|IsTightMeasureSet.finite'
     '|isTightMeasureSet_finite|IsTightMeasureSet.biUnion',
     ['Mathlib/'],
     []),
    ('iterated-deriv-compact-support',
     'TODO.md Punkt 8; MartingaleProblems/Suggested.lean, '
     '`HasCompactSupport.iteratedDeriv`',
     'Mathlib hat den kompakten Traeger der **iterierten** Ableitung nicht. '
     '`HasCompactSupport.deriv` steht in '
     '`Mathlib/Analysis/Calculus/Deriv/Support.lean:60` und ist der erste '
     'Schritt; die Iterierte darueber steht nirgends. Am 2026-09-24 am '
     'Quelltext nachgesehen.',
     'HasCompactSupport\\.iteratedDeriv|iteratedDeriv.*HasCompactSupport'
     '|support_iteratedDeriv|tsupport_iteratedDeriv',
     ['Mathlib/'],
     []),
    ('bcf-of-compact-support',
     'TODO.md Punkt 8; MartingaleProblems/Suggested.lean, '
     '`BoundedContinuousFunction.ofHasCompactSupport`',
     'Mathlib hat die stetige Funktion mit kompaktem Traeger als beschraenkte '
     'stetige Funktion nicht als Deklaration. Sie fuehrt die Konstruktion an '
     'drei Stellen **inline** aus — '
     '`Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:142` und '
     '`:287`, `Mathlib/Analysis/Distribution/TestFunction.lean:111` —, '
     'jedesmal `bounded_above_of_compact_support` gefolgt von '
     '`ofNormedAddCommGroup`. Am 2026-09-24 am Quelltext nachgesehen.',
     'ofHasCompactSupport|hasCompactSupport.*toBoundedContinuous',
     ['Mathlib/'],
     []),
]


def count(pattern, pathfilters):
    r = subprocess.run(
        ['git', '-C', MATHLIB4, 'grep', '-I', '-n', '-E', '-i', pattern,
         'upstream/master', '--', *pathfilters],
        capture_output=True, text=True)
    return [l for l in r.stdout.splitlines() if l.strip()]


def section(key, where, claim, pat, pfs, expected):
    hits = count(pat, pfs)
    files = sorted({l.split(':')[1] for l in hits})
    surprises = [f for f in files
                 if not any(f == e or f.startswith(e) for e in expected)]
    verdict = ('**UNERWARTET** — nachzulesen' if surprises
               else 'wie erwartet')
    out = [f'## `{key}` — {where}', '', f'> {claim}', '',
           f'Suche `{pat}` unter `{", ".join(pfs)}`: **{len(hits)} Treffer** in '
           f'{len(files)} Dateien — {verdict}.', '']
    for f in files[:12]:
        mark = '  ← unerwartet' if f in surprises else ''
        out.append(f'* `{f}`{mark}')
    if len(files) > 12:
        out.append(f'* … und {len(files) - 12} weitere')
    out.append('')
    return out, bool(surprises)


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    rev = subprocess.run(['git', '-C', MATHLIB4, 'rev-parse', 'upstream/master'],
                         capture_output=True, text=True).stdout.strip()
    out = [f'# Negativaussagen gegen `upstream/master` `{rev}`', '']
    surprised = []
    # Bekannte und harmlose Treffer der ersten Liste.  `maximal_ineq` ist Doobs
    # Maximalungleichung in `L¹`; ihr eigener Doc-Kommentar sagt, daß die
    # `Lᵖ`-Fassung noch fehlt.  Die beiden PDE-Treffer sind Literaturverweise.
    expected_claims = {
        'doob-Lp': ['Mathlib/Probability/Martingale/OptionalStopping.lean'],
        'first-order-pde': ['Mathlib/Analysis/Distribution/Sobolev.lean',
                            'Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean'],
        # Beide Treffer sind Aussagen über **Filtrationen**: die Meßbarkeit
        # einer Menge für eine rechtsstetige Filtration und das Stoppzeit-
        # kriterium darüber.  Von der Meßbarkeit eines rechtsstetigen *Pfades*
        # handelt keiner.
        'rightcontinuous-measurable': [
            'Mathlib/Probability/Process/Filtration.lean',
            'Mathlib/Probability/Process/Stopping.lean'],
        # Ein Namensvetter und nichts weiter: `strictMono_filtration` ist die
        # strenge Monotonie einer Körperturmfiltration und enthält das Muster
        # `mono_filtration` als Teilzeichenkette.  Von Martingalen handelt die
        # Datei nicht.
        'martingale-smaller-filtration': ['Mathlib/FieldTheory/CardinalEmb.lean'],
    }
    out += ['## Die Behauptungen der Roadmaps', '']
    for key, where, claim, pat, pf in CLAIMS:
        lines, s = section(key, where, claim, pat, [pf],
                           expected_claims.get(key, []))
        out += lines
        if s:
            surprised.append(key)
    out += ['## Die zweiundzwanzig Lücken von `TODO.md` Punkt 8', '']
    for key, where, claim, pat, pfs, expected in CLAIMS_TODO8:
        lines, s = section(key, where, claim, pat, pfs, expected)
        out += lines
        if s:
            surprised.append(key)
    out += ['## Zusammenfassung', '',
            f'{len(CLAIMS) + len(CLAIMS_TODO8)} Behauptungen geprüft, '
            f'{len(surprised)} mit unerwarteten Treffern: '
            + (', '.join(f'`{k}`' for k in surprised) or 'keine') + '.', '']
    open(f'{OUT}/negatives.md', 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))
