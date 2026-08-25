#!/usr/bin/env python3
"""Compile check for MartingaleProblem.tex.  Fails loudly on anything LaTeX
complains about, not only on undefined references."""
import io, os, re, subprocess, sys, collections

os.chdir(os.path.dirname(os.path.abspath(__file__)))

TEX = 'MartingaleProblem.tex'
ENVS = ['definition','lemma','theorem','proposition','remark','corollary','proof',
        'example','setting','fact','enumerate','itemize','equation','align',
        'align*','gather*','tabular','multline','multline*']

s = io.open(TEX, encoding='utf-8').read()
bad = False

# 1. environment balance -- catches a dropped \end{...} before LaTeX does
for env in ENVS:
    b = len(re.findall(r'\\begin\{%s\}' % re.escape(env), s))
    e = len(re.findall(r'\\end\{%s\}'   % re.escape(env), s))
    if b != e:
        print('UNBALANCED %s: %d begin, %d end' % (env, b, e)); bad = True

# 2. duplicate labels
dup = [k for k, v in collections.Counter(re.findall(r'\\label\{([^}]+)\}', s)).items() if v > 1]
if dup:
    print('DUPLICATE LABELS:', dup); bad = True

# 3. non-ASCII outside comments (LaTeX silently drops unknown Unicode)
for n, line in enumerate(s.split('\n'), 1):
    code = line.split('%')[0]
    for ch in code:
        if ord(ch) > 127 and ch not in '\u2019\u00e0\u00e8\u00e9\u00ea\u00fc\u00f6\u00e4\u00df':
            print('NON-ASCII U+%04X at line %d: %s' % (ord(ch), n, line.strip()[:70]))
            bad = True
            break

# run until the .aux stabilizes (a structural insertion can need more than 3)
prev = None
for _ in range(6):
    subprocess.run(['pdflatex', '-interaction=nonstopmode', TEX],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        aux = io.open(TEX.replace('.tex', '.aux'), encoding='utf-8', errors='replace').read()
    except FileNotFoundError:
        aux = None
    if aux == prev:
        break
    prev = aux
else:
    print('WARNING: .aux did not stabilize in 6 passes')

log = io.open(TEX.replace('.tex', '.log'), encoding='utf-8', errors='replace').read()

# 4. hard LaTeX/TeX errors
errs = re.findall(r'(?m)^! .*', log)
if errs:
    print('LATEX ERRORS (%d):' % len(errs))
    for e in errs[:10]: print('   ', e)
    bad = True

# 5. references and citations
for pat in ['Reference', 'Citation', 'Label']:
    for m in set(re.findall(r'%s `([^\']+)\' .{0,30}undefined' % pat, log)):
        print('UNDEFINED %s: %s' % (pat, m)); bad = True
if 'multiply defined' in log:
    print('MULTIPLY DEFINED labels present'); bad = True

# 6. layout
over = [float(x) for x in re.findall(r'Overfull .hbox \(([0-9.]+)pt', log)]
big = [x for x in over if x > 8]
if big: print('Overfull hboxes > 8pt: %s' % sorted(big, reverse=True)[:5])

m = re.search(r'Output written on \S+ \((\d+) pages, (\d+) bytes\)', log)
print('%s  --  %s pages, %d overfull (max %.1fpt)'
      % ('FAIL' if bad else 'clean', m.group(1) if m else '?', len(over), max(over) if over else 0))
sys.exit(1 if bad else 0)
