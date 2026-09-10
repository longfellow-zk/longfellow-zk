"""Emit the GF(2^128) wrapping-sum cone templates and instance maps.

The binary-field circuit asserts `Π_j (got - α^(j·2^32)·want) = 0` where `got` and `want` are
each a product of two earlier nodes (`analog_adder/src/circuit.rs:117`).  Measured on the
artifact, all 184 wrap cones have exactly that shape, with only five distinct product trees:

    64 x  n=7 rounds (a)     8 tree leaves: 7 factors + one constant
    63 x  n=6 rounds (e)     7 tree leaves: 6 factors + one constant, one leaf used twice
    48 x  n=4 schedule       4 tree leaves
     8 x  n=2 finals         2 tree leaves
     1 x  n=6, odd tree      the single instance the compiler associated differently

The "constant" factor is a 9-deep squaring chain rooted at the `one` wire, i.e. the value 1.

Emitted template layout, per class:

    0 .. 3        leaves: got1, got2, want1, want2
    4 .. 4+n-1    the n wrap factors, `[(0,0,1), (windowIdx j, 2,3)]`
    4+n ..        the product tree, one `[(0, a, b)]` node each

`coneIs` is simulated here before anything is written, so a template that the kernel would
reject is never emitted.
"""
import sys, os, re, glob
from collections import Counter, OrderedDict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sha_parse import parse_nodes, parse_constNat, GEN, NAME

nodes = parse_nodes(); consts = parse_constNat()

POLY = (1 << 128) | 0x87
def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if (a >> 128) & 1: a ^= POLY
    return r
def gpow(a, e):
    r = 1
    while e:
        if e & 1: r = gmul(r, a)
        a = gmul(a, a); e >>= 1
    return r

_T = gpow(2, 1 << 32)
_v2i = {}
for i, c in consts.items(): _v2i.setdefault(c, i)
WIDX = {j: _v2i[gpow(_T, j)] for j in range(7)}     # j -> constant index of alpha^(j*2^32)
_IW = {v: k for k, v in WIDX.items()}

_dep = {}
def depends(n):
    if n in _dep: return _dep[n]
    _dep[n] = False
    k, v = nodes[n]
    r = (v != 0) if k == 'input' else (
        any(depends(a) or depends(b) for _, a, b in v) if k == 'sum' else True)
    _dep[n] = r
    return r

def read_asserts():
    out = {}
    for f in glob.glob(os.path.join(GEN, f"{NAME}Asserts*.lean")):
        s = open(f).read()
        m = re.search(r'def asserts_(\d+) : List RawAssert :=\s*\n\s*\[(.*)\]', s, re.S)
        out[int(m.group(1))] = [(int(a), int(b), int(c)) for a, b, c in
                                re.findall(r'⟨(\d+),\s*(\d+),\s*(\d+)⟩', m.group(2))]
    return [a for i in sorted(out) for a in out[i]]

def analyse(root):
    """(n, got, want, factor node per j, tree order) or None if the cone is not a wrap."""
    k, v = nodes[root]
    if k != 'sum' or len(v) != 1: return None
    order, idx = [], {}
    def visit(n):
        if n in idx: return idx[n]
        kk, vv = nodes[n]
        isprod = depends(n) and kk == 'sum' and len(vv) == 1 and consts.get(vv[0][0], 0) == 1
        if not isprod:
            idx[n] = len(order); order.append(('L', n)); return idx[n]
        _, a, b = vv[0]
        ia, ib = visit(a), visit(b)
        idx[n] = len(order); order.append(('P', n, ia, ib)); return idx[n]
    visit(root)
    leaves = [o[1] for o in order if o[0] == 'L']
    varl = [x for x in leaves if depends(x)]
    if not varl or any(nodes[x][0] != 'sum' or len(nodes[x][1]) != 2 for x in varl): return None
    # `want` is identified by the one factor carrying a non-unit window coefficient
    want = None
    for x in varl:
        for (c, a, b) in nodes[x][1]:
            if consts.get(c, 0) != 1 and c in _IW: want = (a, b)
    if want is None: return None
    got, byj = set(), {}
    for x in varl:
        ts = nodes[x][1]
        wt = [t for t in ts if t[1:] == want]
        gt = [t for t in ts if t[1:] != want]
        if len(wt) != 1 or len(gt) != 1 or consts.get(gt[0][0], 0) != 1: return None
        j = _IW.get(wt[0][0])
        if j is None: return None
        byj[j] = (x, ts.index(gt[0]) == 0)     # node, and whether `got` is the first term
        got.add(gt[0][1:])
    n = len(varl)
    if len(got) != 1 or sorted(byj) != list(range(n)): return None
    return n, got.pop(), want, byj, order

def const_chain(n, stop):
    """The squaring chain under a constant factor, stopping at any node already placed.

    Walking past a node that is already a template leaf emits rows nothing references -- that is
    what first made these templates 26 nodes where `cone_probe` measures 19."""
    chain = [n]
    cur = n
    while cur not in stop:
        k, v = nodes[cur]
        if k != 'sum' or len(v) != 1: break
        c, a, b = v[0]
        if a != b or consts.get(c, 0) != 1: break
        chain.append(a); cur = a
        if cur in stop: break
    chain.reverse()
    return chain[0], chain[1:]

def template(n, got, want, byj, order):
    """Template nodes + the instance map.

    Leaves are `got1, got2, want1, want2` and, when the class has a constant factor, the base of
    its squaring chain -- which measurement shows is the `one` wire, so the chain's value is 1.
    The chain rows come next, then the `n` wrap factors, then the compiler's product tree."""
    tn, mp = [], []
    leaves = [got[0], got[1], want[0], want[1]]
    constleaves = [o[1] for o in order if o[0] == 'L' and o[1] not in
                   {byj[j][0] for j in range(n)}]
    bases, chains = [], []
    for cl in constleaves:
        base, ch = const_chain(cl, set(leaves))
        bases.append(base); chains.append(ch)
    # dedupe shared bases
    seen = []
    for b in bases:
        if b not in seen: seen.append(b)
    leaves += seen
    for x in leaves:
        tn.append(('leaf', len(mp))); mp.append(x)
    pos = {x: i for i, x in enumerate(leaves)}
    # squaring chains
    for ch in chains:
        prev = pos[ch[0]] if ch[0] in pos else None
        for node in ch:
            if node in pos: continue
            k, v = nodes[node]
            _, a, _ = v[0]
            tn.append(('sum', [(0, pos[a], pos[a])])); pos[node] = len(mp); mp.append(node)
    factor_pos = {}
    for j in range(n):
        node, got_first = byj[j]
        terms = [(0, 0, 1), (WIDX[j], 2, 3)] if got_first else [(WIDX[j], 2, 3), (0, 0, 1)]
        factor_pos[node] = len(mp); pos[node] = len(mp)
        tn.append(('sum', terms)); mp.append(node)
    for o in order:
        if o[0] == 'L':
            if o[1] not in pos: return None
        else:
            a = pos[order[o[2]][1]]; b = pos[order[o[3]][1]]
            pos[o[1]] = len(mp)
            tn.append(('sum', [(0, a, b)])); mp.append(o[1])
    return tn, mp

def cone_is(tn, mp):
    """Simulate `Core/ConeTmpl.coneIs`, so nothing that would fail is emitted."""
    for p, item in enumerate(tn):
        if item[0] == 'leaf':
            if item[1] != p: return False
        else:
            ts = item[1]
            want = ('sum', [(c, mp[a], mp[b]) for (c, a, b) in ts])
            if nodes[mp[p]] != want: return False
            for (_, a, b) in ts:
                if not (a < p and b < p and mp[a] < mp[p] and mp[b] < mp[p]): return False
    return True

# ---------------------------------------------------------------------------
def lean_tmpl(name, tn):
    L = sum(1 for x in tn if x[0] == 'leaf')
    rows = [x for x in tn if x[0] == 'sum']
    out = [f"/-- Chain rows of the `n`-factor wrap template: {len(rows)} nodes over {L} leaves. -/",
           f"def mv{name} : Nat → List (Nat × Nat × Nat)"]
    for k, x in enumerate(rows):
        lst = ", ".join(f"({c}, {a}, {b})" for (c, a, b) in x[1])
        out.append(f"  | {k} => [{lst}]" if k < len(rows) - 1 else f"  | _ => [{lst}]")
    out += ["",
            f"def tn{name} : List TmplNode :=",
            f"  (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))",
            f"    ++ (List.range {len(rows)}).map (fun k => TmplNode.sum (mv{name} k))",
            ""]
    return "\n".join(out), L, len(rows)

def lean_map(name, insts):
    out = [f"/-- Instance maps: template position → artifact node, one row per instance. -/",
           f"def map{name} : Nat → Nat → Nat"]
    for e, (root, mp, _) in enumerate(insts):
        lst = ", ".join(str(x) for x in mp)
        arm = f"  | {e} => fun i => ([{lst}] : List Nat).getD i 0"
        out.append(arm if e < len(insts) - 1 else f"  | _ => fun i => ([{lst}] : List Nat).getD i 0")
    out.append("")
    return "\n".join(out)

def emit(path, classes):
    body = ['/-',
            '# GF(2^128) wrapping-sum cone templates',
            '',
            'Generated by `tools/sha256/gen_gf2_wrap.py`.  Each class is one template plus one',
            'instance map per assertion; `coneIs` decides the structural match against the artifact\'s',
            'own node table, so nothing here is trusted.  The generator simulates `coneIs` before',
            'writing, so a template the kernel would reject is never emitted.',
            '',
            'Template layout: positions 0..3 are the leaves `got1, got2, want1, want2`; then the `n`',
            'wrap factors `[(0,0,1), (windowIdx j, 2,3)]`; then the product tree the compiler emitted.',
            '-/',
            '',
            'import quadcert.Bridge.Sha256Gf2.Gf2Sound',
            'import quadcert.Gen.Sha256Gf2.Sha256Gf2NodeChk',
            '',
            'set_option maxRecDepth 8000000',
            'set_option maxHeartbeats 4000000',
            '',
            'namespace Sha256Gf2',
            '',
            'open Quadcert Quadcert.Gen.Sha256Gf2',
            '']
    used = {}
    ordered = sorted(classes.items(), key=lambda kv: (kv[0][0], -len(kv[1])))
    for (n, _), insts in ordered:
        k = used.get(n, 0); used[n] = k + 1
        name = f"W{n}" + ("" if k == 0 else chr(ord('b') + k - 1))
        tn = insts[0][1]
        tnodes = TN[(n, _)]
        t, L, M = lean_tmpl(name, tnodes)
        body += [f"/-! ## `n = {n}`: {len(insts)} instances -/", "", t,
                 lean_map(name, insts), ""]
        body += [f"/-- Kernel-checked: every instance's cone matches the template. -/",
                 f"theorem cone{name} :",
                 f"    (List.range {len(insts)}).all (fun e => coneIs nodeFn tn{name} (map{name} e)) = true := by",
                 f"  decide +kernel", "",
                 f"/-- …and every mapped node is inside the DAG. -/",
                 f"theorem map{name}_lt :",
                 f"    (List.range {len(insts)}).all (fun e =>",
                 f"      (List.range {L + M}).all (fun i => decide (map{name} e i < 58258))) = true := by",
                 f"  decide +kernel", "",
                 f"/-- Root position of the template. -/",
                 f"abbrev root{name} : Nat := {L + M - 1}", ""]
    body.append('end Sha256Gf2')
    open(path, 'w').write("\n".join(body) + "\n")
    print("wrote", path)

if __name__ == "__main__":
    asserts = read_asserts()
    classes = OrderedDict()
    TN = {}
    skipped = Counter()
    for (root, _, _) in asserts:
        a = analyse(root)
        if a is None: skipped['not a wrap'] += 1; continue
        n, got, want, byj, order = a
        t = template(n, got, want, byj, order)
        if t is None: skipped[f'n={n} has a constant factor'] += 1; continue
        tn, mp = t
        ok = cone_is(tn, mp)
        key = (n, tuple((x[0], tuple(x[1]) if x[0] == 'sum' else x[1]) for x in tn))
        classes.setdefault(key, []).append((root, mp, ok))
        TN[key] = tn
    print(f"asserts {len(asserts)}   skipped {dict(skipped)}")
    for (n, tnkey), insts in classes.items():
        good = sum(1 for _, _, ok in insts if ok)
        print(f"  n={n}: {len(insts):3} instances, {len(tnkey)} template nodes, coneIs {good}/{len(insts)}")
        assert good == len(insts), "coneIs simulation failed; refusing to emit"
    globals()['TN'] = TN
    out = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__)))), "circuits", "quadcert", "Bridge", "Sha256Gf2",
        "Gf2WrapTmpl.lean")
    emit(out, classes)

