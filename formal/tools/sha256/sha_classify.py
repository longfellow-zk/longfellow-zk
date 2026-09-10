import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
import re, glob, os, sys
_sys.path.insert(0, _HERE)
from sha_parse import parse_nodes, parse_constNat, parse_layout, GEN, P256, NAME

nodes = parse_nodes(); consts = parse_constNat(); layout = parse_layout()

def parse_asserts():
    out = {}
    for f in glob.glob(os.path.join(GEN, f"{NAME}Asserts*.lean")):
        s = open(f).read()
        m = re.search(r'def asserts_(\d+) : List RawAssert :=\s*\n\s*\[(.*)\]', s, re.S)
        idx = int(m.group(1))
        out[idx] = [(int(a), int(b), int(c)) for a, b, c in
                    re.findall(r'⟨(\d+),\s*(\d+),\s*(\d+)⟩', m.group(2))]
    res = []
    for i in sorted(out): res.extend(out[i])
    return res

asserts = parse_asserts()
print("asserts:", len(asserts))

def kind(root):
    """Classify an assertion root: booleanity (3-node) or a wrap product chain."""
    k, v = nodes[root]
    if k != 'sum': return ('other', None)
    if len(v) == 2:  # x - x*x style booleanity
        return ('bool', None)
    if len(v) != 1: return ('other', None)
    # product node: (c, a, b) -- walk the product tree collecting factors
    factors = []
    def walk(n, depth=0):
        kk, vv = nodes[n]
        if kk == 'sum' and len(vv) == 1 and depth < 6:
            c, a, b = vv[0]
            if consts.get(c, 0) == 1 and a != 0 and b != 0:
                walk(a, depth+1); walk(b, depth+1); return
        factors.append(n)
    walk(root)
    return ('wrap', factors)

from collections import Counter
cnt = Counter()
wraps = []
for (root, _, _) in asserts:
    t, f = kind(root)
    if t == 'wrap':
        cnt[len(f)] += 1
        wraps.append((root, f))
    else:
        cnt[t] += 1
print("classes:", dict(cnt))
print("first wrap roots:", [w[0] for w in wraps[:10]])
