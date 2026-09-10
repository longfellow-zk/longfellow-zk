import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
"""Emit the schedule bridge for all 48 `sha256/schedule/N` assertions."""
import re, sys, os
_sys.path.insert(0, _HERE)
from sha_parse import P256
from sha_classify import asserts, kind, nodes, consts, layout

OUTDIR = "/Users/abhi/Projects/longfellow-zk/formal/circuits/quadcert/Bridge/Sha256"
ONE = {0, 238}
def sg(c):
    v = consts[c]; return v - P256 if v > P256//2 else v
def lname(n):
    k, v = nodes[n]
    return layout.get(v) if k == 'input' else None
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
def widx(w):
    m = re.match(r'input_block(\d+)$', w)
    if m: return int(m.group(1))
    m = re.match(r'outw(\d+)$', w)
    if m: return 16 + int(m.group(1))
    raise SystemExit("unknown word " + w)

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
    words = {}
    for n in leaves:
        m = re.match(r'(.*)_(\d+)$', lname(n) or "")
        if m: words.setdefault(m.group(1), {})[int(m.group(2))] = n
    idxs = {widx(w): w for w in words}
    t = max(idxs)
    assert set(idxs) == {t, t-2, t-7, t-15, t-16}, (root, sorted(idxs))
    s0w, s1w, p7, p16, outw = idxs[t-15], idxs[t-2], idxs[t-7], idxs[t-16], idxs[t]
    pair = {}
    for c,a,b in nodes[z][1]:
        if a in ONE or b in ONE: continue
        W = -sg(c) // 2
        u, other = (a, b) if xlegs(a) else (b, a)
        d = unwrap(other)
        j = W.bit_length() - 1
        w = re.match(r'(.*)_\d+$', lname(xlegs(u)[0])).group(1)
        pair[(w, j)] = (u, d)
    assert sum(1 for (w,_) in pair if w == s0w) == 29, (root, "sigma0 count")
    assert sum(1 for (w,_) in pair if w == s1w) == 22, (root, "sigma1 count")
    copies = [n for n in mids if len(nodes[n][1]) == 1]
    xors   = [n for n in mids if len(nodes[n][1]) == 3]
    merged = [n for n in mids if len(nodes[n][1]) not in (1, 3)]
    assert len(merged) == 1, (root, len(merged))
    ROT = {s0w: (7, 18, 3), s1w: (17, 19, 10)}
    def entry(w, j):
        r1, r2, sh = ROT[w]
        bits = words[w]
        spec = {(j+r1) % 32, (j+r2) % 32} | ({j+sh} if j+sh < 32 else set())
        if (w, j) in pair:
            u, d = pair[(w, j)]
            got = {int(re.match(r'.*_(\d+)$', lname(l)).group(1)) for l in xlegs(u)}
            got.add(int(re.match(r'.*_(\d+)$', lname(d)).group(1)))
            assert got == spec, (root, w, j, sorted(got), sorted(spec))
            return f"Quadcert.xorVal (midLeafVal (cnstw F) lv {L} mvS{t} {ti[u]}) (lv {ti[d]})"
        a, b = bits[(j+r1) % 32], bits[(j+r2) % 32]
        assert spec == {(j+r1) % 32, (j+r2) % 32}, (root, w, j)
        return f"Quadcert.xorVal (lv {ti[a]}) (lv {ti[b]})"
    groups = []
    for w in (s0w, p7, s1w, p16):
        if w in ROT: groups.append((w, [(2**j, entry(w, j)) for j in range(32)]))
        else:        groups.append((w, [(2**j, f"lv {ti[words[w][j]]}") for j in range(32)]))
    dsg = [(2**j, f"lv {ti[words[outw][j]]}") for j in range(32)]
    return dict(t=t, root=root, z=z, L=L, M=M, ti=ti, leaves=leaves, mids=mids,
                copies=copies, xors=xors, merged=merged[0], groups=groups, ds=dsg,
                outw=outw, s0w=s0w, s1w=s1w, p7=p7, p16=p16)

sched = [(r,f) for (r,_,_) in asserts for (t,f) in [kind(r)] if t=='wrap' and len(f)==6]
insts = sorted((analyse(r, f) for r, f in sched), key=lambda d: d['t'])
print("analysed", len(insts), "instances; t =", insts[0]['t'], "..", insts[-1]['t'])
print("all spec index checks passed")
import pickle
pickle.dump(insts, open(_os.path.join(_HERE, "insts.pkl"),"wb"))
