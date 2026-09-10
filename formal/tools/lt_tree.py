#!/usr/bin/env python3
"""Recover the comparator tree of `rx_lt_order` / `nms_lt_order` from the DAG.

Usage: lt_tree.py cone.json

These two cones cannot be expanded: the comparator is a 256-step fold, so as a polynomial in the
bits its degree is 256. `BitLt.step_assoc` says the *shape* does not matter, and
`BitLt.eval_eq_foldSt` turns any shape into the list fold -- so the certificate does not have to
justify the compiler's tree, only to report it correctly and check each node locally.

This module reports it. Every match is a local polynomial identity over a node's own operands, so
nothing here is trusted: `check` re-derives each state from the DAG and the emitted Lean lemmas
re-check them in the kernel.

State convention (`BitLt`): `(eq, lt)`, `step lo hi = (hi.1 * lo.1, hi.2 + hi.1 * lo.2)`, and
`base a b = (1 - a - b + 2ab, (1 - a) * b)`, which for a *constant* order bit collapses to
`(a, 1 - a)` when the bit is 1 and `(1 - a, 0)` when it is 0.

**Measured motif census of the 325-node comparator region** (`rx_lt_order`; `nms_lt_order` is
identical). `x` is a non-`one` operand, `1` the constant:

    189  +1xx            plain product -- `step`'s `eq`
     47  +11x -1xx       `c - b*c`, i.e. a product with one side complemented
     30  +11x +1xx -11x  `step`'s `lt` with a complement folded in
     23  +11x            a `copy.rs` identity node
     17  +11x +11x -1xx
     10  +111            the depth-alignment `one` chain
      6  +11x +1xx       `step`'s `lt`, both sides positive
      3  +1xx -1xx

The lesson is the second column: only **6** nodes match `l_hi + e_hi * l_lo` literally. `notb` is
free in this compiler -- `Bitw` carries an `Inner::N` tag rather than emitting a `1 - x` node --
so complements are fused into whichever product consumes them, and a purely syntactic matcher on
the DAG has to enumerate every folded form. Worse, the tree is not the 255-node binary tree one
would expect: where the order bit is 0 the state is `(1 - a, 0)` and the `step` degenerates, so
the compiler drops nodes entirely.

**Therefore the tree should be extracted on the Rust side**, where `bv.lt` is built and the
`Inner` polarity of every `Bitw` is visible, and emitted as an `STree` plus per-node polarities.
Lean still re-checks each node as a local `ring` identity, so nothing about that extraction is
trusted -- it only has to be *reported*, which is exactly the division of labour the rest of
these generators use. This module stays as the record of why the DAG-side route was abandoned.
"""
import json
import sys

P = 115792089210356248762697446949407573530086143415290314195533631308867097853951
ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551


def load(path):
    d = json.load(open(path))
    nodes = {n["id"]: n for n in d["nodes"]}
    one = next(i for i, n in nodes.items() if n.get("name") == "one")
    return d, nodes, one


def analyse(path):
    d, nodes, one = load(path)

    def is_one(i):
        if i == one:
            return True
        s = nodes[i].get("sum")
        return bool(s) and len(s) == 1 and s[0][0] == "1" and is_one(s[0][1]) and is_one(s[0][2])

    def terms(i):
        """(coefficient, operands-other-than-one) per term, copies not resolved."""
        out = []
        for c, w0, w1, _ in nodes[i].get("sum", []):
            ops = [w for w in (w0, w1) if not is_one(w)]
            out.append((int(c, 16), tuple(ops)))
        return out

    # A node is `1 - x` iff it is `1*one*one + (p-1)*one*x` in some order.
    def is_compl(i):
        t = terms(i)
        if len(t) != 2:
            return None
        c0, o0 = t[0]
        c1, o1 = t[1]
        for (ca, oa), (cb, ob) in ((t[0], t[1]), (t[1], t[0])):
            if not oa and ca % P == 1 and len(ob) == 1 and cb % P == P - 1:
                return ob[0]
        return None

    # Products `e_hi * e_lo`.
    prod = {i: terms(i)[0][1] for i in nodes
            if len(terms(i)) == 1 and len(terms(i)[0][1]) == 2 and terms(i)[0][0] % P == 1}
    # Sums `l_hi + e_hi * l_lo`.
    sums = {}
    for i in nodes:
        t = terms(i)
        if len(t) == 2 and all(c % P == 1 for c, _ in t):
            a, b = t[0][1], t[1][1]
            if len(a) == 1 and len(b) == 2:
                sums[i] = (a[0], b)
            elif len(b) == 1 and len(a) == 2:
                sums[i] = (b[0], a)

    print(f"{path.rsplit('/', 1)[-1]}: root {d['root']}, "
          f"{len(prod)} products, {len(sums)} step-sums, "
          f"{sum(1 for i in nodes if is_compl(i) is not None)} complements")

    # Walk down from the root's `lt` component, pairing each `lt` node with the `eq` node that
    # appears as the multiplier of its low part.
    def descend(lt, depth=0, out=None):
        if out is None:
            out = {"leaf": 0, "node": 0, "unmatched": []}
        if lt in sums:
            out["node"] += 1
            hi_lt, (a, b) = sums[lt]
            # one of a, b is `e_hi`, the other `l_lo`; `e_hi` also multiplies into the eq node
            descend(hi_lt, depth + 1, out)
            for cand in (a, b):
                if cand in sums or is_compl(cand) is not None:
                    descend(cand, depth + 1, out)
                    break
            else:
                out["unmatched"].append(lt)
        elif is_compl(lt) is not None:
            out["leaf"] += 1
        else:
            out["unmatched"].append(lt)
        return out

    root_t = terms(d["root"])
    print("   root terms:", [(hex(c % P)[:8], o) for c, o in root_t])
    r = descend(d["root"])
    print("   descend from root:", r["node"], "step nodes,", r["leaf"], "leaves,",
          len(r["unmatched"]), "unmatched", r["unmatched"][:6])


for p in sys.argv[1:]:
    analyse(p)
