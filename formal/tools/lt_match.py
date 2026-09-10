#!/usr/bin/env python3
"""Locate the comparator tree of `rx_lt_order` / `nms_lt_order` in the DAG.

Usage: lt_match.py lt_cone.json bits_cone.json    (bits_cone supplies the bit -> node map)

`lt` is `fold2(a, b, lt_reduce, lt_base, ...)`, and `fold2` is `util::array::tree_fold2`, which
splits at the *midpoint*. So the tree shape is not a compiler choice to be discovered -- it is
the balanced tree over `0..255`, with the lower (less significant) half as `lt_reduce`'s first
argument, matching `BitLt.step lo hi`. Only the wire ids and the polarities have to be found.

Polarity is the whole difficulty. `notb` is free in this compiler: `Bitw` carries an `Inner::N`
tag rather than emitting a `1 - x` node, so a state component may be stored *complemented* and
the complement fused into whichever product consumes it. `lt_tree.py` records the motif census
that made a syntactic matcher hopeless.

So match semantically instead, bottom-up. At each tree node the children's wire ids are already
known, so the predicted `step` polynomial is a polynomial in at most four atoms; scan the cone
for a node whose own single-level expansion equals it, or equals its complement. Each match is a
local identity over that node's own operands -- cheap, and exactly the obligation the emitted
Lean lemma will re-check in the kernel.

**Status: 489 of the 502 demanded components are located; 13 are not.** Three refinements were
needed to get there and each is worth keeping: resolving `copy.rs` aliases before comparing
operand sets (+24), a demand analysis (the root's `eq` is discarded, and since the low half is
always `lo`, whose `eq` a parent uses only for its own `eq`, the entire left spine's `eq` is dead
and was never emitted), and treating a component that coincides with a child's wire up to
complement as costing no node.

What defeats the remaining 13 is **single-use intermediates being fused away**, and `(24, 32)` is
the clean example. Reading `boolean/src/circuit.rs`: `Inner::N(x)` means the *value* is `1 - x`
while the *node* holds `x`; `andb(P x, N y) = P(x - x*y)`; `or_assuming_at_most_one_true(N x, P y)
= N(x - y)`; `tree_andb = positive(andb ..)`, and `positive` on an `N` emits `1 - x`. Tracing the
subtree with those rules gives, for bits 24..31 (order bits `0,0,1,1,1,1,1,1`):

    eq(24,26) = P 13405        lt(24,26) = False
    eq(26,28) = P 13412        lt(26,28) = N 13412
    eq(24,28) = P 13413        lt(24,28) = N 13412
    eq(28,32) = P 13428        lt(28,32) = N 13428
    eq(24,32) = P 13429        lt(24,32) = N (13428 * 13412)   <- no such node exists

and the node that *does* exist is `13437 = 13428 * 13412 - 13429`. That is exactly
`or(N (13428*13412), P (andb (P 13429) lt(16,24)))` -- i.e. **`lt(16,32)`**, with `lt(24,32)`'s
node inlined into it because it had a single use. So the failure is not a missing rule; it is
that a tree node's state is sometimes not a wire at all.

The fix is therefore in the state representation, not in the search: allow a component to be a
*polynomial over descendant wires* when no node matches, and carry it up one level. Fusion only
ever crosses one level (degree two is the quad limit), so this terminates, and the emitted Lean
lemma states the value either way -- a wire is just the case where the polynomial is a variable.
The 13 failures are all of this shape.

Separately, the dumped root `14406` mixes in node `10703`, which also appears in
`nms_lt_order`'s cone, so the assertion as dumped is not the bare comparator output; the top of
the tree still has to be identified.
"""
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, signed  # noqa: E402

ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
N = 256


class Cone:
    def __init__(self, path):
        self.d = json.load(open(path))
        self.nodes = {n["id"]: n for n in self.d["nodes"]}
        self.one = next(i for i, n in self.nodes.items() if n.get("name") == "one")

    def is_one(self, i):
        if i == self.one:
            return True
        s = self.nodes[i].get("sum")
        return (bool(s) and len(s) == 1 and s[0][0] == "1"
                and self.is_one(s[0][1]) and self.is_one(s[0][2]))

    def alias(self, i):
        """`copy.rs` inserts `1 * one * x` identity nodes for depth alignment; follow them, or
        an operand-set test compares a copy against the value it aliases and fails."""
        seen = set()
        while i not in seen:
            seen.add(i)
            s = self.nodes[i].get("sum")
            if not (s and len(s) == 1 and s[0][0] == "1"):
                return i
            a, b = s[0][1], s[0][2]
            nxt = b if self.is_one(a) else a if self.is_one(b) else None
            if nxt is None:
                return i
            i = nxt
        return i

    def operands(self, i):
        return {self.alias(w) for _, w0, w1, _ in self.nodes[i].get("sum", [])
                for w in (w0, w1) if not self.is_one(w)}

    def expand(self, i, atoms, nv):
        """One level: the node as a polynomial over `atoms` (node id -> var index)."""
        acc = Poly(nv)
        for c, w0, w1, _ in self.nodes[i]["sum"]:
            t = Poly.const(nv, signed(int(c, 16)))
            for w in (w0, w1):
                if not self.is_one(w):
                    a = self.alias(w)
                    if a not in atoms:
                        return None
                    t = t * Poly.var(nv, atoms[a])
            acc = acc + t
        return acc


def bit_map(path):
    """bit index -> node id, read off the fused weighted-sum root (see gen_bitsum_meaning)."""
    c = Cone(path)
    terms = c.nodes[c.d["root"]]["sum"]
    out = {}
    for co, w0, w1, _ in terms:
        ops = [w for w in (w0, w1) if not c.is_one(w)]
        if len(ops) != 1:
            continue
        v = (-int(co, 16)) % P
        k = v.bit_length() - 1
        if v == 1 << k and k < N:
            out[k] = ops[0]
    return out


def main():
    lt = Cone(sys.argv[1])
    bits = bit_map(sys.argv[2])
    assert len(bits) == N, f"found {len(bits)} bits"
    missing = [k for k, n in bits.items() if n not in lt.nodes]
    assert not missing, f"bit nodes not in the lt cone: {missing[:5]}"

    # Candidate comparator nodes: everything reachable from the root without entering a bit.
    bitset = set(bits.values())
    comp, st = set(), [lt.d["root"]]
    while st:
        i = st.pop()
        if i in comp or i in bitset or "sum" not in lt.nodes[i]:
            continue
        comp.add(i)
        st += [w for _, w0, w1, _ in lt.nodes[i]["sum"] for w in (w0, w1)]

    def lift(q, nv2):
        """Same polynomial in a larger variable space."""
        return Poly(nv2, {m + (0,) * (nv2 - len(m)): c for m, c in q.terms.items()})

    def zero_mod_p(q):
        return all(c % P == 0 for c in q.terms.values())

    # A state component: ("const", c) or ("ref", node, pol) meaning `node` if pol else `1 - node`.
    def poly_of(comp_, atoms, nv):
        if comp_[0] == "const":
            return Poly.const(nv, comp_[1])
        v = Poly.var(nv, atoms[comp_[1]])
        return v if comp_[2] else Poly.const(nv, 1) - v

    def find(target, atoms, nv, want_operands):
        """A cone node equal to `target` or to `1 - target`, over the given atoms."""
        for i in comp:
            if not lt.operands(i) <= want_operands:
                continue
            e = lt.expand(i, atoms, nv)
            if e is None:
                continue
            if all(c % P == 0 for c in (e - target).terms.values()):
                return (i, True)
            if all(c % P == 0 for c in (e - (Poly.const(nv, 1) - target)).terms.values()):
                return (i, False)
        return None

    # Demand analysis. `lt` returns only `res.1`, so the root's `eq` is dead -- and since the
    # low half is always the `lo` argument, whose `eq` a parent uses only for its own `eq`, the
    # whole left spine's `eq` is dead too and the compiler dropped those nodes. Asking for them
    # is what made 14 subtrees look unmatchable.
    need = set()

    def demand(lo, hi, comp_):
        if (lo, hi, comp_) in need or hi - lo == 1:
            return
        need.add((lo, hi, comp_))
        mid = lo + (hi - lo) // 2
        if comp_ == "lt":
            demand(mid, hi, "lt")
            demand(mid, hi, "eq")
            demand(lo, mid, "lt")
        else:
            demand(lo, mid, "eq")
            demand(mid, hi, "eq")

    demand(0, N, "lt")

    log = {"leaf": 0, "found": 0, "implicit": 0, "dead": 0, "split": 0, "failed": []}

    def build(lo, hi):
        if hi - lo == 1:
            log["leaf"] += 1
            b = bits[lo]
            if (ORDER >> lo) & 1:
                return (("ref", b, True), ("ref", b, False))       # base a 1 = (a, 1 - a)
            return (("ref", b, False), ("const", 0))               # base a 0 = (1 - a, 0)
        mid = lo + (hi - lo) // 2
        s_lo, s_hi = build(lo, mid), build(mid, hi)
        parts = [p for p in (s_lo[0], s_lo[1], s_hi[0], s_hi[1]) if p is not None]
        refs = [p[1] for p in parts if p[0] == "ref"]
        atoms = {n: j for j, n in enumerate(dict.fromkeys(refs))}
        nv = max(len(atoms), 1)
        want = set(atoms)

        def pol(c):
            return poly_of(c, atoms, nv) if c is not None else None

        e_lo, l_lo, e_hi, l_hi = pol(s_lo[0]), pol(s_lo[1]), pol(s_hi[0]), pol(s_hi[1])

        def resolve(target, label):
            if (lo, hi, label) not in need:
                log["dead"] += 1
                return None
            # A component that is a literal, or that coincides with a child's wire (up to
            # complement), costs no node at all -- `Inner` carries it.
            for p in parts:
                if p[0] != "ref":
                    continue
                v = poly_of(p, atoms, nv)
                if all(c % P == 0 for c in (v - target).terms.values()):
                    log["implicit"] += 1
                    return p
                if all(c % P == 0 for c in (v - (Poly.const(nv, 1) - target)).terms.values()):
                    log["implicit"] += 1
                    return ("ref", p[1], not p[2])
            if not target.terms:
                log["implicit"] += 1
                return ("const", 0)
            r = find(target, atoms, nv, want)
            if r is not None:
                log["found"] += 1
                return ("ref", r[0], r[1])
            # `lt_reduce` is `or_assuming_at_most_one_true(lt_hi, andb(eq_hi, lt_lo))`, which
            # fits one quad node -- but only when the compiler chooses to fuse it. Where it did
            # not, the `andb` is its own node and the sum's operands are not the children's
            # wires at all. Find the `andb` first, then look again with it as an atom.
            if label == "lt" and e_hi is not None and l_lo is not None:
                sub = find(e_hi * l_lo, atoms, nv, want)
                if sub is not None:
                    nv2 = nv + 1
                    atoms2 = dict(atoms)
                    atoms2[sub[0]] = nv
                    sv = Poly.var(nv2, nv)
                    if not sub[1]:
                        sv = Poly.const(nv2, 1) - sv
                    tgt2 = lift(l_hi, nv2) + sv
                    r2 = find(tgt2, atoms2, nv2, set(atoms2))
                    if r2 is not None:
                        log["split"] += 1
                        return ("ref", r2[0], r2[1])
            log["failed"].append((lo, hi, label))
            return ("const", 0)

        eq = resolve(e_hi * e_lo, "eq") if (e_hi is not None and e_lo is not None) else None
        lt_ = (resolve(l_hi + e_hi * l_lo, "lt")
               if (l_hi is not None and e_hi is not None and l_lo is not None) else None)
        return (eq, lt_)

    root_state = build(0, N)
    print(f"{sys.argv[1].rsplit('/', 1)[-1]}: comparator region {len(comp)} nodes")
    print(f"  demanded {len(need)}, leaves {log['leaf']}, matched {log['found']}, "
          f"implicit {log['implicit']}, split {log['split']}, dead {log['dead']}, "
          f"failed {len(log['failed'])}")
    if log["failed"]:
        print("  first failures:", log["failed"][:6])
    print("  root state:", root_state)
    print("  cone root:", lt.d["root"], lt.nodes[lt.d["root"]]["sum"])


main()
