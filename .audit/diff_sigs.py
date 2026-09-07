import re, sys

# Compare instance binders per declaration between two #check dumps.
# Usage: diff_sigs.py <orig.output> <exp.output>
def parse(path):
    text = open(path).read()
    # #check output blocks start with '@name : ' and may span lines until the
    # next '@' line or a diagnostic line
    sigs = {}
    cur = None
    buf = []
    for line in text.splitlines():
        m = re.match(r"^@([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*) : (.*)", line)
        if m:
            if cur:
                sigs[cur] = ' '.join(buf)
            cur = m.group(1)
            buf = [m.group(2)]
            continue
        if re.match(r'^\S+\.lean:\d+', line) or line.startswith('warning') or line.startswith('error'):
            if cur:
                sigs[cur] = ' '.join(buf)
                cur = None
                buf = []
            continue
        if cur is not None:
            buf.append(line.strip())
    if cur:
        sigs[cur] = ' '.join(buf)
    return sigs

def insts(sig):
    return re.findall(r'\[(?:inst[^ :]* : )?([A-Za-z][A-Za-z0-9_.]*[^\]]*)\]', sig)

a = parse(sys.argv[1])
b = parse(sys.argv[2])
for name in a:
    if name not in b:
        print('NUR ORIGINAL:', name)
        continue
    ia, ib = insts(a[name]), insts(b[name])
    if ia != ib:
        gone = [x for x in ia if x not in ib]
        new = [x for x in ib if x not in ia]
        if gone or new:
            print(name)
            if gone: print('   weg:', gone)
            if new:  print('   neu:', new)
