#!/usr/bin/env python3
"""Prüft die **Negativaussagen** der Roadmaps gegen frisches `upstream/master`.

Jede Zeile der Liste unten ist eine Behauptung „Mathlib hat X nicht", der Ort,
an dem sie steht, und das Suchmuster, das sie widerlegen würde.  Das Skript
sucht mit `git grep` in `upstream/master` und meldet die Trefferzahl; ein
Treffer ist kein Gegenbeweis, sondern eine Stelle zum Nachlesen.

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
    ('cadlag', 'SkorokhodSpace/README.md:3',
     'Der String `cadlag` kommt in Mathlib nicht vor.',
     'cadlag', 'Mathlib/'),
    ('IsCadlag', 'SkorokhodSpace/Suggested.lean:341',
     '`Function.RightContinuous` und `IsCadlag` sind nicht in Mathlib.',
     'IsCadlag|IsRightContinuous', 'Mathlib/'),
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
]


def count(pattern, pathfilter):
    r = subprocess.run(
        ['git', '-C', MATHLIB4, 'grep', '-I', '-n', '-E', '-i', pattern,
         'upstream/master', '--', pathfilter],
        capture_output=True, text=True)
    lines = [l for l in r.stdout.splitlines() if l.strip()]
    return lines


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    rev = subprocess.run(['git', '-C', MATHLIB4, 'rev-parse', 'upstream/master'],
                         capture_output=True, text=True).stdout.strip()
    out = [f'# Negativaussagen gegen `upstream/master` `{rev}`', '']
    for key, where, claim, pat, pf in CLAIMS:
        hits = count(pat, pf)
        files = sorted({l.split(':')[1] for l in hits})
        out += [f'## `{key}` — {where}', '', f'> {claim}', '',
                f'Suche `{pat}` unter `{pf}`: **{len(hits)} Treffer** in '
                f'{len(files)} Dateien.', '']
        for f in files[:12]:
            out.append(f'* `{f}`')
        if len(files) > 12:
            out.append(f'* … und {len(files) - 12} weitere')
        out.append('')
    open(f'{OUT}/negatives.md', 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))
