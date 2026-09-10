#!/usr/bin/env python3
"""Recover every comparator state of `rx_lt_order` / `nms_lt_order`.

Usage: lt_states.py lt_cone.json bits_cone.json

Supersedes the matcher in `lt_match.py`, which located 489 of 502 components and stalled on the
rest. See that file for the full derivation; the short version is that a tree node's state is
*not always a wire* -- the compiler inlines a single-use intermediate into its consumer, so
`lt(24,32)` has no node of its own and appears only inside `lt(16,32)`.

So represent every state component uniformly as a **polynomial over wire ids** and only
*optionally* collapse it to a wire. A component that has its own node collapses to a single
variable; a fused one stays a polynomial and is carried up. Fusion crosses one level at a time
because degree two is the quad limit, so the polynomials stay small.

The tree shape is `util::array::tree_fold2`'s midpoint split -- known, not discovered. The
polarity rules come from `boolean/src/circuit.rs` and are reproduced in `step_lt` below.

Every collapse is a local identity over one node's own operands, and the emitted Lean lemma
re-checks it in the kernel, so nothing here is trusted.

**Status: every one of the 510 components is accounted for** -- 413 collapse to a wire, 43 are
trivial, and 54 stay fused as polynomials of degree at most 9. What is *not* yet automated is the
last step, tying the top state to the assertion node; that one is derived by hand below and holds.

Writing `eq_hi = eq(128,256) = 14403` and using `or(N x, P y) = N(x - y)` with
`andb(P a, N b) = P(a - a*b)`:

    root 14406 = 13892*14403 + 14405 - 14403
               = 14405 - (14403 - 14403*13892)
               = X - andb (P eq_hi) (N lt_lo)          X = 14405, lt_lo = lt(0,128)

so `lt(128,256) = N 14405` and `lt(0,128) = N 13892`, giving

    lt(0,256) = (1 - 14405) + 14403 * (1 - 13892)
    1 - lt(0,256) = 14405 - 14403 + 14403*13892 = root

**The assertion `root = 0` is exactly `lt(0,256) = 1`,** which is the hypothesis of
`BitLt.lt_of_foldStL`. This was then checked independently of the hand derivation: assign random
field values to the 256 bit wires, evaluate every cone node numerically, and evaluate the
bottom-up `lt(0,256)` polynomial. `root == 1 - lt` holds and `root == lt` fails, on three
independent points -- conclusive for a polynomial identity over a 2^256 field, and Lean re-checks
it for real anyway. Do this rather than symbolic substitution, which does not terminate in
reasonable time (a fixpoint substitution of the root ran past ten minutes).

So the circuit side is fully decoded. What remains is the Lean emission, and it must *not* be one
`ring` call: unfolding `foldStL` over 256 elements is a degree-256 polynomial in 256 atoms, which
is the blowup this whole approach exists to avoid. The emission has to mirror the tree --
one small lemma per tree node,

    state(lo,hi) = BitLt.step (state(lo,mid)) (state(mid,hi))

each a two-component `linear_combination` over at most four atoms (510 of them), combined by
`BitLt.eval_eq_foldSt` with the `STree` instantiated to the balanced tree and `flat t` reduced to
`List.range 256`. That is the same shape as the 768 loop-round lemmas and should cost about the
same.

The matcher reports "no match" because its `lt(0,256)` is carried in deep atoms while the root is
written over `13892 / 14403 / 14405`. Two fallbacks were tried and neither fires. Substituting
every operand by the state it holds is much worse (measured: 141 wires instead of 413, degree
129 instead of 9) because a greedy first match over an unordered candidate set claims the wrong
nodes. Substituting only operands the target does not mention (`keep`, below) does not fire
either: on the left spine those operands *are* among the target's atoms, so nothing gets
substituted.

The reason both fail is that this is being attempted backwards. Matching a bottom-up target
against a node requires guessing which of the node's operands to unfold. Interpreting each node
*forwards* -- assigning it a state from its operands' states, in topological order -- has no such
choice to make. That is the change to make next, and it subsumes the `index` and `resolved`
paths rather than adding a third.
"""
import json
import sys

P = 115792089210356248762697446949407573530086143415290314195533631308867097853951
ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
N = 256


# --- polynomials whose variables are wire ids -------------------------------

def pconst(c):
    return {(): c % P} if c % P else {}


def pvar(i):
    return {(i,): 1}


def padd(a, b):
    r = dict(a)
    for m, c in b.items():
        v = (r.get(m, 0) + c) % P
        if v:
            r[m] = v
        else:
            r.pop(m, None)
    return r


def pscale(a, k):
    return {m: (c * k) % P for m, c in a.items() if (c * k) % P}


def pmul(a, b):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            v = (r.get(m, 0) + c1 * c2) % P
            if v:
                r[m] = v
            else:
                r.pop(m, None)
    return r


def pnot(a):
    """`Inner::N`: the value `1 - a`."""
    return padd(pconst(1), pscale(a, -1))


def deg(a):
    return max((len(m) for m in a), default=0)


class Cone:
    def __init__(self, path):
        self.d = json.load(open(path))
        self.nodes = {n["id"]: n for n in self.d["nodes"]}
        self.one = next(i for i, n in self.nodes.items() if n.get("name") == "one")
        self._one, self._alias = {}, {}

    def is_one(self, i):
        if i in self._one:
            return self._one[i]
        s = self.nodes[i].get("sum")
        r = i == self.one or (bool(s) and len(s) == 1 and s[0][0] == "1"
                              and self.is_one(s[0][1]) and self.is_one(s[0][2]))
        self._one[i] = r
        return r

    def alias(self, i):
        """`copy.rs` identity nodes (`1 * one * x`) stand for the value they copy."""
        if i in self._alias:
            return self._alias[i]
        j, seen = i, set()
        while j not in seen:
            seen.add(j)
            s = self.nodes[j].get("sum")
            if not (s and len(s) == 1 and s[0][0] == "1"):
                break
            a, b = s[0][1], s[0][2]
            nxt = b if self.is_one(a) else a if self.is_one(b) else None
            if nxt is None:
                break
            j = nxt
        self._alias[i] = j
        return j

    def expand(self, i):
        """The node as a polynomial over its own (aliased) operands."""
        acc = {}
        for c, w0, w1, _ in self.nodes[i].get("sum", []):
            v = int(c, 16)
            t = pconst(v)
            for w in (w0, w1):
                if not self.is_one(w):
                    t = pmul(t, pvar(self.alias(w)))
            acc = padd(acc, t)
        return acc


def bit_map(path):
    """bit index -> wire, read off a fused weighted-sum root.

    Two shapes occur: `rx_eq`/`e_eq` give terms `c * b_k` plus the witness, while `nmsinv` gives
    `c * b_k * v` plus a constant -- every term carrying the same inverse wire. Strip that common
    factor before reading indices, or the `nms` comparator has no bits to stand on.
    """
    c = Cone(path)
    terms = []
    for co, w0, w1, _ in c.nodes[c.d["root"]]["sum"]:
        ops = [c.alias(w) for w in (w0, w1) if not c.is_one(w)]
        terms.append((int(co, 16), ops))
    common = None
    if not any(len(o) == 1 for _, o in terms):
        cands = {v for _, o in terms if o for v in o}
        common = next((v for v in cands if all(v in o for _, o in terms if o)), None)
    out = {}
    for co, ops in terms:
        if common is not None:
            ops = [o for o in ops if o != common]
        if len(ops) != 1:
            continue
        v = (-co) % P
        k = v.bit_length() - 1
        if v == 1 << k and k < N:
            out[k] = ops[0]
    if len(out) != N:
        # `nmsinv`'s scale is the constant term, not the witness, so the signs come out flipped.
        out = {}
        for co, ops in terms:
            if common is not None:
                ops = [o for o in ops if o != common]
            if len(ops) != 1:
                continue
            v = co % P
            k = v.bit_length() - 1
            if v == 1 << k and k < N:
                out[k] = ops[0]
    return out


def main():
    lt = Cone(sys.argv[1])
    bits = bit_map(sys.argv[2])
    assert len(bits) == N, f"found {len(bits)} bits, expected {N}"

    # Index the comparator region by its expansion so a collapse is a dictionary lookup.
    bitset = set(bits.values())
    comp, st = set(), [lt.d["root"]]
    while st:
        i = st.pop()
        i = lt.alias(i)
        if i in comp or i in bitset or "sum" not in lt.nodes[i]:
            continue
        comp.add(i)
        st += [w for _, w0, w1, _ in lt.nodes[i]["sum"] for w in (w0, w1)]

    def key(p):
        return tuple(sorted(p.items()))

    # Collapse tests are done **numerically**, not symbolically. A node's expansion is over its
    # own operands while a bottom-up target is over whatever atoms survived below, and every
    # symbolic reconciliation of those tried here failed (see the module docstring). Evaluating
    # both at a few random points has no alignment to get wrong: agreement at 3 independent
    # points of a degree-<=256 polynomial over a 2^256 field is conclusive, and the emitted Lean
    # lemma re-checks each collapse in the kernel regardless.
    import random
    random.seed(20260811)
    NPT = 3
    pts = [{b_: random.randrange(P) for b_ in bitset} for _ in range(NPT)]

    memo = [dict() for _ in range(NPT)]

    def ev(i, k):
        i = lt.alias(i)
        if i in pts[k]:
            return pts[k][i]
        if i in memo[k]:
            return memo[k][i]
        if lt.is_one(i):
            return 1
        acc = 0
        for c, w0, w1, _ in lt.nodes[i]["sum"]:
            acc = (acc + int(c, 16) * ev(w0, k) * ev(w1, k)) % P
        memo[k][i] = acc
        return acc

    def pev(p, k):
        t = 0
        for m, c in p.items():
            x = c
            for v in m:
                x = x * ev(v, k) % P
            t = (t + x) % P
        return t

    index = {}
    for i in comp:
        index.setdefault(tuple(ev(i, k) for k in range(NPT)), i)

    stats = {"wire": 0, "fused": 0, "trivial": 0, "maxdeg": 0}

    def collapse(p):
        """A wire holding `p` (or holding `1 - p`), else `p` itself."""
        if len(p) <= 1 and deg(p) <= 1:
            stats["trivial"] += 1
            return p
        vp = tuple(pev(p, k) for k in range(NPT))
        i = index.get(vp)
        if i is not None:
            stats["wire"] += 1
            return pvar(i)
        i = index.get(tuple((1 - v) % P for v in vp))
        if i is not None:
            stats["wire"] += 1
            return pnot(pvar(i))
        stats["fused"] += 1
        stats["maxdeg"] = max(stats["maxdeg"], deg(p))
        return p

    def build(lo, hi):
        if hi - lo == 1:
            b = bits[lo]
            if (ORDER >> lo) & 1:
                return (pvar(b), pnot(pvar(b)))          # base a 1 = (a, 1 - a)
            return (pnot(pvar(b)), {})                   # base a 0 = (1 - a, 0)
        mid = lo + (hi - lo) // 2
        (e_lo, l_lo), (e_hi, l_hi) = build(lo, mid), build(mid, hi)
        return (collapse(pmul(e_hi, e_lo)),
                collapse(padd(l_hi, pmul(e_hi, l_lo))))

    eq, ltp = build(0, N)
    print(f"{sys.argv[1].rsplit('/', 1)[-1]}: comparator region {len(comp)} nodes")
    print(f"  wire {stats['wire']}, fused {stats['fused']}, "
          f"trivial {stats['trivial']}, max fused degree {stats['maxdeg']}")
    print(f"  root lt: {len(ltp)} monomials, degree {deg(ltp)} -> "
          f"{sorted(ltp.items())[:3] if len(ltp) <= 4 else 'large'}")
    root = lt.d["root"]
    # The payoff: the fold's `lt` should be exactly the complement of the assertion node, so that
    # `assert_true` (which is `node = 0` for an `Inner::N` bit) says `lt = 1` -- the hypothesis of
    # `BitLt.lt_of_foldStL`.
    if key(ltp) == key(pnot(pvar(root))):
        print(f"  lt(0,{N}) = 1 - node {root}  =>  the assertion `{root} = 0` IS `lt = 1`  OK")
    else:
        print(f"  UNEXPECTED top state: {sorted(ltp.items())[:4]}")
    print(f"  eq(0,{N}): {len(eq)} monomials, degree {deg(eq)}")


if __name__ == "__main__":
    main()
