import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
"""Analyse the 128 round_step cones."""
import re, sys, pickle
_sys.path.insert(0, _HERE)
from sha_parse import P256
from sha_classify import asserts, kind, nodes, consts, layout
from collections import Counter
ONE = {0, 238}
K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
     0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
     0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
     0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
     0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
     0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
     0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
     0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
def sg(c):
    v = consts[c]; return v - P256 if v > P256//2 else v
def lname(n):
    k, v = nodes[n]
    return layout.get(v) if k == 'input' else None
def bitpos(n): return int(re.match(r'.*_(\d+)$', lname(n)).group(1))
def wname(n):  return re.sub(r'_\d+$', '', lname(n))
def unwrap(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 1:
        c, a, b = v[0]
        return b if a in ONE else a
    return n
def xlegs(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 3: return (v[0][2], v[1][2])
    return None
def statename(t, i):
    if i < 4:
        k = t - 1 - i
        return f"outa{k}" if k >= 0 else f"h0_{i - t}"
    k = t - 1 - (i - 4)
    return f"oute{k}" if k >= 0 else f"h0_{(i - 4) - t + 4}"

def analyse(root, facs):
    z = [n for n in facs if nodes[n][0]=='sum' and len(nodes[n][1])>10][0]
    seen, stack = set(), [z]
    while stack:
        n = stack.pop()
        if n in seen: continue
        seen.add(n)
        if nodes[n][0]=='sum':
            for c,a,b in nodes[n][1]: stack.extend([a,b])
    leaves = sorted(n for n in seen if nodes[n][0]=='input')
    leaves.remove(0); leaves = [0] + leaves
    mids = sorted(n for n in seen if nodes[n][0]=='sum' and n != z)
    L, M = len(leaves), len(mids)
    ti = {n: i for i, n in enumerate(leaves)}
    ti.update({n: L + j for j, n in enumerate(mids)})
    ti[z] = L + M
    merged = max(mids, key=lambda n: len(nodes[n][1]))
    kc = [sg(c) for c,a,b in nodes[merged][1] if a in ONE and b in ONE]
    assert len(kc) == 1
    t = K.index(kc[0])
    n = 6 if len(facs) == 16 else 7
    words = {}
    for x in leaves[1:]: words.setdefault(wname(x), {})[bitpos(x)] = x
    # xor mids grouped by the source word of their legs
    xors = {}
    for m in mids:
        lg = xlegs(m)
        if lg: xors.setdefault(wname(lg[0]), []).append((m, bitpos(lg[0]), bitpos(lg[1])))
    return dict(root=root, z=z, t=t, n=n, L=L, M=M, ti=ti, leaves=leaves, mids=mids,
                merged=merged, K=kc[0], words=words, xors=xors, cone=len(seen),
                copies=[m for m in mids if len(nodes[m][1]) == 1],
                xormids=[m for m in mids if len(nodes[m][1]) == 3])

rounds = [(r,f) for (r,_,_) in asserts for (tt,f) in [kind(r)] if tt=='wrap' and len(f) in (13,16)]
insts = sorted((analyse(r,f) for r,f in rounds), key=lambda d: (d['n'], d['t']))
print("analysed", len(insts))
print("cone sizes:", Counter((d['n'], d['cone'], d['L'], len(d['copies']), len(d['xormids']),
                              len(nodes[d['merged']][1]), len(nodes[d['z']][1])) for d in insts))
d = insts[0]
print("\nn=6 t=0: xor-mid source words:", {k: len(v) for k, v in d['xors'].items()})
d7 = [x for x in insts if x['n'] == 7][0]
print("n=7 t=0: xor-mid source words:", {k: len(v) for k, v in d7['xors'].items()})
pickle.dump(insts, open(_os.path.join(_HERE, "rinsts.pkl"),"wb"))
