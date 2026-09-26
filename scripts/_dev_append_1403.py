import sys
p = 'Journal/Blog/MartingaleProblem/Facts/INVENTAR.md'
src = sys.argv[1]
s = open(p).read().rstrip('\n') + '\n'
s += open(src).read()
open(p, 'w').write(s)
