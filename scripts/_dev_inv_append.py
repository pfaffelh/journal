import sys
p = 'Journal/Blog/MartingaleProblem/Facts/INVENTAR.md'
text = open(sys.argv[1]).read()
s = open(p).read()
if not s.endswith('\n'):
    s += '\n'
s += '\n' + text.strip('\n') + '\n'
open(p, 'w').write(s)
print('appended', len(text))
