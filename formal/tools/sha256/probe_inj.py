"""Measure one injection-cone shape before committing to an emitter for all eight."""
import sys, os
from collections import Counter, OrderedDict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_gf2_wrap as G
nodes = G.nodes; consts = G.consts
INJ = {2 + i: i for i in range(32)}

def operands():
    ops = set()
    for (root, _, _) in G.read_asserts():
        a = G.analyse(root)
        if a is None: continue
        _, got, want, _, _ = a
        ops.update([got[0], got[1], want[0], want[1]])
    return sorted(o for o in ops if G.depends(o))

def analyse_inj(root):
    """Descend every 1-term product (any coefficient); collect folded coeffs + factor leaves."""
    order, idx, coeffs = [], {}, []
    def visit(n):
        if n in idx: return idx[n]
        k, v = nodes[n]
        if k == 'sum' and len(v) == 1 and G.depends(n):
            c, a, b = v[0]
            if consts.get(c, 0) != 1: coeffs.append(c)
            ia, ib = visit(a), visit(b)
            idx[n] = len(order); order.append(('P', n, ia, ib, c)); return idx[n]
        idx[n] = len(order); order.append(('L', n)); return idx[n]
    visit(root)
    return order, coeffs

def build(root):
    """Template + instance map. Leaf 0 is the `one` wire, as the injFactor lemmas expect."""
    order, coeffs = analyse_inj(root)
    leaves = [o[1] for o in order if o[0] == 'L']
    one = 0
    if any(nodes[L][0] != 'sum' and L != one for L in leaves):
        return None
    # every leaf's operands must be leaf-level: `one` plus the bits it mentions
    bits = []
    for L in leaves:
        k, v = nodes[L]
        if k != 'sum': continue
        for (_, a, b) in v:
            for x in (a, b):
                if x != one and x not in bits: bits.append(x)
    tmplleaves = [one] + bits
    pos = {x: i for i, x in enumerate(tmplleaves)}
    tn = [('leaf', i) for i in range(len(tmplleaves))]
    mp = list(tmplleaves)
    for L in leaves:
        k, v = nodes[L]
        if k != 'sum':
            if L not in pos: return None
            continue
        terms = [(c, pos[a], pos[b]) for (c, a, b) in v]
        pos[L] = len(mp); tn.append(('sum', terms)); mp.append(L)
    for o in order:
        if o[0] == 'L':
            if o[1] not in pos: return None
        else:
            a = pos[order[o[2]][1]]; b = pos[order[o[3]][1]]
            pos[o[1]] = len(mp); tn.append(('sum', [(o[4], a, b)])); mp.append(o[1])
    return tn, mp, coeffs

if __name__ == "__main__":
    ops = operands()
    shapes = OrderedDict()
    bad = 0
    for o in ops:
        r = build(o)
        if r is None: bad += 1; continue
        tn, mp, coeffs = r
        if not G.cone_is(tn, mp):
            print("coneIs FAILED for", o); continue
        key = tuple((x[0], tuple(x[1]) if x[0] == 'sum' else x[1]) for x in tn)
        shapes.setdefault(key, []).append((o, mp, coeffs))
    print(f"operands {len(ops)}   unbuildable {bad}   shapes {len(shapes)}   coneIs OK for all built")
    for key, insts in sorted(shapes.items(), key=lambda kv: len(kv[0])):
        L = sum(1 for x in key if x[0] == 'leaf')
        print(f"  {len(insts):4} instances : {len(key):4} template nodes, {L} leaves, "
              f"folded coeffs {sorted(set(len(c) for _,_,c in insts))}")
