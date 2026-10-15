#!/usr/bin/env python3
"""Emit the Lean meaning lemma for `rx_lt_order` / `nms_lt_order`.

Usage: gen_lt_meaning.py lt_cone.json bits_cone.json THEOREM_NAME [LEAVES] > out.lean

`LEAVES` (default 256) truncates to the subtree over bits `0..LEAVES`, a genuine subtree of
`tree_fold2`'s balanced split, so a small value emits a real -- just smaller -- lemma. Validate
at 8 before paying for all 255 internal nodes.

The proof mirrors the circuit's tree. It cannot be one `ring` call: unfolding `foldStL` over 256
states is a degree-256 polynomial in 256 atoms, the blowup the cone-cutting method exists to
avoid. `BitLt.foldStL_append` splits each segment exactly where `tree_fold2` split it, and each
internal node contributes one two-component identity over at most four wires.

Why one `linear_combination` closes each node: the numeric collapse (see `lt_states.py`) assigns
each tree node the wire the compiler actually emitted, and *that wire's operands are its
children's wires*. So `eq = eq_hi * eq_lo` and `lt = lt_hi + eq_hi * lt_lo` relate wires whose
value equations are immediately to hand. Alignment was only ever a problem for the search.

Coefficients are integers, never residues: the value equation carries signed residues while the
goal multiplies rendered children, and `ring` cannot bridge the difference. `W` supplies it
integrally, as in every other generator here, and is untrusted -- a wrong one fails `ring`.

**Status (2026-10-15): compiles at 256 leaves**, both `lt_rx_order` and `lt_nms_order`, as part
of the full ECDSA2 bridge (all 146 modules of `Gen/E2`, `Bridge/Ecdsa2` and `Ecdsa2Meaning`).

What fixed it was not term size but the *fold*. Parts used to be stated over
`raw.toDag (Ecdsa2.consts F)`, so citing one inside the combiner -- after its `set dag` -- needed
`rw [<- hdag]` across every leaf of every cited part, and that rewrite was where `isDefEq` timed
out. Parts are now stated over an abstract `{dag}` with `hdag : dag = raw.toDag ...` as a
hypothesis (`DAG_ARG`, on by default), so the citation is already in the combiner's variable and
nothing is rewritten; `subst hdag` puts each part's own proof back in its old context. The
table-ification proposed below was not needed.

History, for whoever reads the rest of this docstring: it compiled at 8 and 32 leaves, and at 256
the parts were fine but the combiner timed out in `isDefEq`.

The reason is term size in the statement, not the proof. A part's statement mentions 16 wires,
but the combiner's mentions all 256, each written out as
`interpDag (raw.toDag (Ecdsa2.consts F)) inputs N`. Matching the 16 part theorems against that
forces defeq checks over enormous terms. Splitting more finely does not help -- the combiner
still names every leaf.

The fix is to stop writing the segment as a 256-element literal. State it as
`(List.range' lo len).map (fun k => base (bitOf inputs k) (orderBit k))`, with `bitOf` and
`orderBit` emitted as functions, and split with `List.range'_append` instead of `from rfl`. Term
size then stays constant in the number of leaves. `bitOf` is a 256-case match, so check early
that `bitOf inputs 5` reduces cheaply -- a large match is what blew `maxRecDepth` in
`gen_addE_meaning.py`, and the same trap applies here.

**The gap is already closed at 256 -- and only at 256.** Measured 2026-10-14, by running the
numeric collapse at each size and printing the top node's `l` component:

    leaves    top `l0`                        == 1 - interpDag <root>?
       8      1 - w13329                      no
      32      1 - w13439                      no
     256      1 - w14406                      YES   (`rx_lt_order`, root 14406)
     256      1 - w10706                      YES   (`nms_lt_order`, root 10706)

So `(foldStL ...).2 = 1 - interpDag <root>` falls out of the collapse with no new proof idea,
and `interpDag <root> = 0` finishes it. The reason this looked like an open problem is that
**truncation moves the top node**: at 8 or 32 leaves the tree's root is a different wire, so no
run below full size can exercise the endpoint, and every validation run was at 8 or 32.

The three routes recorded here as dead -- a cone lemma over the certificate's 38 atoms (reaches
a stray leaf, node 331), the same plus the 256 bit wires (does not finish in ten minutes), and
deep substitution in `collapse` (65,568 terms) -- were all attempts to *build* a connection that
the collapse already produces. They stay listed because they are genuinely dead, not because
they are still needed.

**A claim that was in this docstring and is false.** It said the `1 - w_node` candidate "is found
by the numeric collapse at every internal node". It is not. Measured per component at 256
leaves: of 255 `l` collapses, 183 land on a wire, 6 need deep substitution, and **66 fuse**; of
255 `e` collapses, 247 land on a wire and 8 fuse. Even at 8 leaves one `l` fuses. This does not
matter -- a fused node is handled by the fused branch below, and only the *top* has to be
wire-shaped for the assertion to attach -- but a strategy built on the stronger claim would fail
at a quarter of the tree.

One regularity worth keeping: `e` fuses exactly `log2(leaves)` times (3, 4, 5, 6, 7, 8 at 8 ...
256), once per level, while `l` fusion grows with the tree at a steady ~26%.

**Never set `maxHeartbeats 0` here.** A `linear_combination` with a wrong coefficient does not
fail fast -- `ring1` grinds -- and with heartbeats unbounded it simply never returns. Every
"scaling wall" measured below was really a diverging tactic with no way to report itself: RSS sat
at the Mathlib baseline (4.1 GB) and never grew. A finite bound turns those into errors.

**Measured scaling wall -- STALE, kept for the numbers only.** This predates the pre-split
change in `segx` (`foldStL_append` applying syntactically, no `show ... from rfl`), and it
contradicts the Status line above: it says 16 leaves does not finish, while 32 now compiles.
Re-measure before trusting any of it. 8 leaves compiles in 4 s. 16 leaves
does not finish in 9 minutes, and 256 leaves as one theorem aborts the interpreter at the
`-M 12000` cap (`memory_exception`, 602 value equations plus 511 node lemmas in one context).
Splitting into per-subtree theorems does *not* help: 16 leaves as three theorems is equally slow,
so the cost is per-node, not per-context.

The likely cause, not yet confirmed: coefficient growth in the *fused* components. Where the
compiler inlined a node the state stays a polynomial, and a polynomial of degree up to 9 whose
coefficients are products of 77-digit residues gives `W` coefficients of several hundred digits.
`ring` normalising many monomials at that size is plausibly the whole bill -- and it would be
invisible at 8 leaves, where nothing is fused deeply enough to compound. Confirm by instrumenting
`render` with the maximum coefficient width per node before trying to fix it.

If that is the cause, the fix is to give each fused component its own named abbreviation and
prove it separately, so no single `ring` call ever sees a compounded coefficient -- rather than
splitting the theorem, which was tried and measured not to help.
"""
import json
import os
import random
import re
import sys

P = 115792089210356248762697446949407573530086143415290314195533631308867097853951
ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
N = 256
NPT = 3


# --- integer polynomials over wire ids (unreduced: this is what `ring` sees) ---

def ic(c):
    return {(): c} if c else {}


def iv(i):
    return {(i,): 1}


def iadd(a, b):
    r = dict(a)
    for m, c in b.items():
        v = r.get(m, 0) + c
        if v:
            r[m] = v
        else:
            r.pop(m, None)
    return r


def isub(a, b):
    return iadd(a, {m: -c for m, c in b.items()})


def imul(a, b):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            v = r.get(m, 0) + c1 * c2
            if v:
                r[m] = v
            else:
                r.pop(m, None)
    return r


def inot(a):
    return isub(ic(1), a)


def ired(a):
    """Signed representatives -- what `render` writes, hence what Lean carries."""
    out = {}
    for m, c in a.items():
        v = c % P
        v = v if v <= P // 2 else v - P
        if v:
            out[m] = v
    return out


def over_p(a):
    assert all(c % P == 0 for c in a.values()), \
        f"residual not divisible by p: {sorted(a.items())[:2]}"
    return {m: c // P for m, c in a.items() if c // P}


def deg(a):
    return max((len(m) for m in a), default=0)


# Bounds for the extra value equations `collapse` may substitute. Both are there to fail fast:
# the node the compiler emitted sits one or two levels above the certificate's atoms, so a
# search that runs long is not the case this handles.
DEEP_STEPS = 12
DEEP_TERMS = 2000


def isubst(a, j, e):
    """Replace the variable `j` by the polynomial `e` throughout `a`."""
    out = {}
    for m, c in a.items():
        k = m.count(j)
        t = {tuple(x for x in m if x != j): c}
        for _ in range(k):
            t = imul(t, e)
        out = iadd(out, t)
    return out


# Whether the statement currently being emitted is a *part* (stated over an abstract `dag`,
# with `hdag` as a hypothesis) or the top theorem (stated over `raw.toDag` directly).
#
# A part used to be stated over `raw.toDag (Ecdsa2.consts F)` and folded back to the combiner's
# `set` variable with `rw [<- hdag]` at the citation.  That rewrite walks every leaf of every
# cited part -- 8 parts x 32 leaves, plus the combiner's own 256 -- and the folding is the
# measured hot path here (4 s when it lands, 7.4 GB and 87 minutes when it does not).  Stating
# the part over an abstract `dag` instead means the citation is already in the combiner's
# variable and nothing is rewritten.  Set `DAG_ARG=0` to go back.
DAG_ARG = os.environ.get("DAG_ARG", "1") != "0"
PART_STMT = [False]


def wire(v, full=False):
    """`set` introduces `w{i}` inside the proof, but the *statement* is elaborated before it, so
    the theorem has to spell the wire out."""
    if not full:
        return f"w{v}"
    dag = "dag" if (DAG_ARG and PART_STMT[0]) else "(raw.toDag (Ecdsa2.consts F))"
    return f"interpDag {dag} inputs {v}"


def render(p, full=False):
    if not p:
        return "(0 : F)"
    parts = []
    for m, c in sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0])):
        lit = f"({c} : F)" if c >= 0 else f"(-{-c} : F)"
        parts.append(lit if not m
                     else lit + " * " + " * ".join(wire(v, full) for v in m))
    return " + ".join(parts)


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
        """One level, signed -- exactly the polynomial the value equation states."""
        acc = {}
        for c, w0, w1, _ in self.nodes[i].get("sum", []):
            v = int(c, 16)
            t = ic(v if v <= P // 2 else v - P)
            for w in (w0, w1):
                if not self.is_one(w):
                    t = imul(t, iv(self.alias(w)))
            acc = iadd(acc, t)
        return acc


def bit_map(c):
    """bit index -> wire, off the fused weighted-sum root of `rx_eq` / `e_eq` / `nmsinv`.

    `nmsinv`'s terms all carry the inverse wire; strip that common factor first, and try both
    signs, since its scale is the constant term rather than a witness."""
    terms = []
    for co, w0, w1, _ in c.nodes[c.d["root"]]["sum"]:
        ops = [c.alias(w) for w in (w0, w1) if not c.is_one(w)]
        terms.append((int(co, 16), ops))
    common = None
    if not any(len(o) == 1 for _, o in terms):
        cands = {v for _, o in terms if o for v in o}
        common = next((v for v in cands if all(v in o for _, o in terms if o)), None)
    for sign in (-1, 1):
        out = {}
        for co, ops in terms:
            o = [x for x in ops if x != common] if common is not None else ops
            if len(o) != 1:
                continue
            v = (sign * co) % P
            k = v.bit_length() - 1
            if v == 1 << k and k < N:
                out[k] = o[0]
        if len(out) == N:
            return out
    raise SystemExit("could not read the bit map off the weighted-sum root")


def main():
    lt = Cone(sys.argv[1])
    bits = bit_map(Cone(sys.argv[2]))
    name = sys.argv[3]
    leaves = int(sys.argv[4]) if len(sys.argv) > 4 else N

    bitset = set(bits.values())
    comp, stk = set(), [lt.d["root"]]
    while stk:
        i = lt.alias(stk.pop())
        if i in comp or i in bitset or "sum" not in lt.nodes[i]:
            continue
        comp.add(i)
        stk += [w for _, w0, w1, _ in lt.nodes[i]["sum"] for w in (w0, w1)]

    random.seed(20260811)
    pts = [{b: random.randrange(P) for b in bitset} for _ in range(NPT)]
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
            x = c % P
            for v in m:
                x = x * ev(v, k) % P
            t = (t + x) % P
        return t

    # Value-vector -> *every* node with that value. Distinct comparator nodes do coincide
    # (`copy.rs` aliases are folded out, but the compiler still emits equal values at different
    # points of the tree), and picking one arbitrarily out of a set is both wrong and
    # nondeterministic -- at 8 leaves it happened not to collide, at 256 it does.
    index = {}
    for i in comp:
        index.setdefault(tuple(ev(i, k) for k in range(NPT)), []).append(i)
    for v in index.values():
        v.sort()

    used = set()

    def collapse(target):
        """`(value, tactic)` for a component whose defining product is `target`."""
        vp = tuple(pev(target, k) for k in range(NPT))
        for vec, sgn in ((vp, 1), (tuple((1 - v) % P for v in vp), -1)):
          for i in index.get(vec, ()):
            got = iv(i) if sgn > 0 else inot(iv(i))
            # The `have` reads `foldStL seg = (E, L)`, so after rewriting the children the
            # goal is `target = got`, not `got = target`. `linear_combination c * v_i + W * hpB`
            # then checks `(target - got) - c*(w_i - expand i) - W*p = 0` over the integers.
            # `c` is how much of the value equation the goal actually needs. **Zero is the
            # common case and was the bug**: where the compiler emitted the wire the collapse
            # is looking for, `target` is already literally `got`, and forcing `c = -sgn`
            # manufactured a residual out of nothing and rejected a perfect match. Measured on
            # `rx_lt_order` segment [24, 28): `target = got = 1 - w13412`, yet the check
            # reported `-w13412 + w13408 * w13411` and fell through to the fused branch -- and
            # since a fused node is no longer a single wire, every ancestor then failed too, all
            # the way to the assertion node.
            veq = isub(iv(i), lt.expand(i))
            for c in (0, -sgn):
                resid = isub(isub(target, got), {m: c * v for m, v in veq.items()})
                if any(x % P for x in resid.values()):
                    continue
                used.add(i)
                W = over_p(resid)
                if c:
                    tac = (f"linear_combination ({c} : F) * v{i}"
                           + (f" + ({render(W)}) * hpB (F := F)" if W else ""))
                else:
                    tac = (f"linear_combination ({render(W)}) * hpB (F := F)" if W
                           else "ring")
                return got, tac
            # One or two further value equations. The node the compiler emitted is often a
            # level or two above the certificate's own atoms -- measured on segment [16, 32):
            # `target - got` reduces to `w13429 + w13437 - w13412 * w13428`, which is exactly
            # `v13437`. Substituting (rather than solving for coefficients) keeps the Lean side
            # to `simp only [v…]`. Only the bit wires are off limits: substituting those is the
            # degree-256 blowup, and `DEEP_TERMS` catches any other run that starts to walk down
            # the tree (an earlier unbounded version reached 65,568 terms).
            keep = bitset
            D, S = isub(target, got), []
            for _ in range(DEEP_STEPS):
                if not any(x % P for x in D.values()):
                    break
                cand = [j for m in D for j in m
                        if j not in keep and j in lt.nodes and "sum" in lt.nodes[j]]
                if not cand or len(D) > DEEP_TERMS:
                    break
                j = max(cand)
                S.append(j)
                D = isubst(D, j, lt.expand(j))
            if S and not any(x % P for x in D.values()):
                used.add(i)
                used.update(S)
                W = over_p(D)
                tail = ("ring" if not W
                        else f"linear_combination ({render(W)}) * hpB (F := F)")
                return got, ("simp only [" + ", ".join(f"v{j}" for j in S) + "]\n      "
                             + tail)
        # Fused: the compiler inlined this one, so it is not a wire. Reduce the coefficients
        # (they are products of residues and grow fast) and pay for that with `W`.
        val = ired(target)
        W = over_p(isub(target, val))
        return val, ("ring" if not W else
                     f"linear_combination ({render(W)}) * hpB (F := F)")

    st = {}

    def build(lo, hi):
        if hi - lo == 1:
            b = bits[lo]
            used.add(b)
            s = ((iv(b), inot(iv(b))) if (ORDER >> lo) & 1 else (inot(iv(b)), {}))
            st[(lo, hi)] = (s[0], s[1], None, None)
            return s
        mid = lo + (hi - lo) // 2
        (e_lo, l_lo), (e_hi, l_hi) = build(lo, mid), build(mid, hi)
        e, te = collapse(imul(e_hi, e_lo))
        l, tl = collapse(iadd(l_hi, imul(e_hi, l_lo)))
        st[(lo, hi)] = (e, l, te, tl)
        return e, l

    build(0, leaves)
    e0, l0 = st[(0, leaves)][0], st[(0, leaves)][1]

    bound = set()

    def segx(lo, hi, full=False):
        """The segment already in `tree_fold2`'s split form.

        Stating each `have` over a flat literal forced a `show ... = ... ++ ... from rfl` at every
        node, and the kernel/defeq cost of those on a 256-element list is what killed the
        combiner. Written pre-split, `foldStL_append` applies syntactically and no defeq check
        happens at all."""
        if hi - lo == 1:
            b = bits[lo]
            # Goes through `wire` so a part's segment is stated over the abstract `dag` too;
            # spelling `raw.toDag` here was what left 32 of them in each part statement.
            nm = f"w{b}" if (not full and b in bound) else wire(b, True)
            return f"[ECDSA2.BitLt.base ({nm}) ({(ORDER >> lo) & 1} : F)]"
        mid = lo + (hi - lo) // 2
        return f"({segx(lo, mid, full)} ++ {segx(mid, hi, full)})"

    def seg(lo, hi, full=False):
        return "[" + ", ".join(
            f"ECDSA2.BitLt.base ({wire(bits[k], full)}) ({(ORDER >> k) & 1} : F)"
            for k in range(lo, hi)
        ) + "]"

    PART = int(os.environ.get("PART_LEAVES", "32"))
    parts = ([(j, min(j + PART, leaves)) for j in range(0, leaves, PART)]
             if leaves > PART else [])
    partname = {r: f"{name}_p{j}" for j, r in enumerate(parts)}

    def walk(lo, hi, steps, used, stop):
        e, l, te, tl = st[(lo, hi)]
        if (lo, hi) in stop:
            # Proved by its own theorem; just cite it.
            # The part theorem is stated over `raw.toDag (Ecdsa2.consts F)`, but `set dag`
            # has already run, so the citation must be folded back to `dag` explicitly --
            # otherwise nothing downstream matches it and elaboration thrashes (measured: 7.4 GB
            # and 87 minutes on a module that takes 4 s when the folding is right).
            steps.append(
                f"@CITE@  have s{lo}_{hi} := {partname[(lo, hi)]} (F := F) inputs hone hdag"
                if DAG_ARG else
                f"@CITE@  have s{lo}_{hi} := {partname[(lo, hi)]} (F := F) inputs hone\n"
                f"  rw [\u2190 hdag] at s{lo}_{hi}")
            for m in list(e) + list(l):
                used.update(m)
            return
        if hi - lo == 1:
            used.add(bits[lo])
            for m in list(e) + list(l):
                used.update(m)
            steps.append(
                f"  have s{lo}_{hi} : ECDSA2.BitLt.foldStL {seg(lo, hi)}\n"
                f"      = ({render(e)}, {render(l)}) := by\n"
                f"    simp only [ECDSA2.BitLt.foldStL_singleton, ECDSA2.BitLt.base,\n"
                f"      Prod.mk.injEq]\n    exact ⟨by ring, by ring⟩")
            return
        mid = lo + (hi - lo) // 2
        walk(lo, mid, steps, used, stop)
        walk(mid, hi, steps, used, stop)
        for m in list(e) + list(l):
            used.update(m)
        # Harvest from *any* tactic, not just `linear_combination`: the deeper collapse emits
        # `simp only [v…]`, and a cited value equation that never gets emitted is an unknown
        # identifier at the other end.
        for t in (te, tl):
            if t:
                used.update(int(x) for x in re.findall(r"\bv(\d+)", t))
                used.update(int(x) for x in re.findall(r"\bw(\d+)", t))
        steps.append(
            f"  have s{lo}_{hi} : ECDSA2.BitLt.foldStL {segx(lo, hi)}\n"
            f"      = ({render(e)}, {render(l)}) := by\n"
            f"    rw [ECDSA2.BitLt.foldStL_append, s{lo}_{mid}, s{mid}_{hi}]\n"
            f"    simp only [ECDSA2.BitLt.step, Prod.mk.injEq]\n"
            f"    refine ⟨?_, ?_⟩\n    · {te}\n    · {tl}")


    # `copy.rs` aligns depth by squaring `one`, so the value equations mention nodes like `3`
    # that are the constant 1. They are invisible to `is_one`-based reasoning on the Python side
    # but very much visible to `ring`, which sees an unconstrained atom. Give each one a value.
    wires = [i for i in sorted(used) if i not in bitset and "sum" in lt.nodes[i]]
    chain, kmap = [], {}
    for i in wires:
        lits, rhs = [], "0"
        for c, w0, w1, ki in lt.nodes[i]["sum"]:
            kmap[ki] = int(c, 16)
            lits.append(f"⟨Ecdsa2.consts F {ki}, {w0}, {w1}⟩")
            rhs = (f"({rhs} + Ecdsa2.consts F {ki} * interpDag dag inputs {w0}"
                   f" * interpDag dag inputs {w1})")
        chain.append(
            f"  have h{i} : dag.getD {i} (.input 0) = .sum [{', '.join(lits)}] := by\n"
            f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
            f"(by rw [nodes_len]; omega)]\n    rfl\n"
            f"  have v{i} : interpDag dag inputs {i} = {rhs} := by\n"
            f"    rw [interpDag_sum inputs dag {i} _ h{i} (vs.sum_operands_lt {i} _ h{i})]\n"
            f"    simp only [List.foldl_cons, List.foldl_nil]")

    def mk(lo, hi, tname, stop):
        """One self-contained theorem for the subtree `[lo, hi)`, citing `stop` subtrees.

        A part is stated over an abstract `dag` so the combiner can cite it without rewriting;
        the top theorem keeps `raw.toDag` because nothing cites it. `PART_STMT` has to be set
        before any `wire(.., full=True)` runs, which is why it is set here rather than at the
        emission site.

        Citations of part theorems are emitted *before* the `set` block. `set` only abstracts
        occurrences present at the time it runs, so a `have` introduced afterwards keeps the raw
        `interpDag` terms -- and `ring` then sees those and the `w` binders as unrelated atoms."""
        PART_STMT[0] = DAG_ARG and tname != name
        steps, used = [], set()
        walk(lo, hi, [], used, stop)          # pass 1: which wires this theorem binds
        bound.clear()
        bound.update(v for v in used if v in lt.nodes)
        walk(lo, hi, steps, used, stop)       # pass 2: emit with the right names
        wires = [i for i in sorted(used)
                 if i in lt.nodes and i not in bitset and "sum" in lt.nodes[i]]
        chain, kmap, ones = [], {}, set()
        for i in wires:
            lits, rhs = [], "0"
            for c, w0, w1, ki in lt.nodes[i]["sum"]:
                kmap[ki] = int(c, 16)
                lits.append(f"\u27e8Ecdsa2.consts F {ki}, {w0}, {w1}\u27e9")
                rhs = (f"({rhs} + Ecdsa2.consts F {ki} * interpDag dag inputs {w0}"
                       f" * interpDag dag inputs {w1})")
                for w in (w0, w1):
                    if lt.is_one(w):
                        j = w
                        while True:
                            ones.add(j)
                            sm = lt.nodes[j].get("sum")
                            if not sm:
                                break
                            j = sm[0][1]
            chain.append(
                f"  have h{i} : dag.getD {i} (.input 0) = .sum [{', '.join(lits)}] := by\n"
                f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]\n    rfl\n"
                f"  have v{i} : interpDag dag inputs {i} = {rhs} := by\n"
                f"    rw [interpDag_sum inputs dag {i} _ h{i} (vs.sum_operands_lt {i} _ h{i})]\n"
                f"    simp only [List.foldl_cons, List.foldl_nil]")
        # `alias()` folds `copy.rs` identity nodes on the Python side, but the emitted value
        # equations still name the raw operand, so `ring` sees `interpDag ... 13364` and
        # `w13347` as unrelated atoms. Give each copy link its own equation. Invisible at 8
        # leaves, where no copies occur.
        alines, seen_a = [], set()
        for i in wires:
            for _, w0, w1, _ in lt.nodes[i]["sum"]:
                for w in (w0, w1):
                    j = w
                    while not lt.is_one(j) and lt.alias(j) != j and j not in seen_a:
                        seen_a.add(j)
                        n = lt.nodes[j]
                        c, a0, a1, ki = n["sum"][0]
                        kmap[ki] = int(c, 16)
                        nxt = a1 if lt.is_one(a0) else a0
                        for z in (a0, a1):
                            if lt.is_one(z):
                                y = z
                                while True:
                                    ones.add(y)
                                    sm = lt.nodes[y].get("sum")
                                    if not sm:
                                        break
                                    y = sm[0][1]
                        alines.append(
                            f"  have r{j} : dag.getD {j} (.input 0) = .sum "
                            f"[\u27e8Ecdsa2.consts F {ki}, {a0}, {a1}\u27e9] := by\n"
                            f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                            f"(by rw [nodes_len]; omega)]\n    rfl\n"
                            f"  have a{j} : interpDag dag inputs {j} "
                            f"= interpDag dag inputs {nxt} := by\n"
                            f"    rw [interpDag_sum inputs dag {j} _ r{j} "
                            f"(vs.sum_operands_lt {j} _ r{j})]\n"
                            f"    simp only [List.foldl_cons, List.foldl_nil, ck{ki}, "
                            f"o{a0 if lt.is_one(a0) else a1}]\n"
                            f"    push_cast; ring")
                        j = nxt
        onelines = []
        for i in sorted(ones):
            n = lt.nodes[i]
            if "sum" not in n:
                onelines.append(
                    f"  have o{i} : interpDag dag inputs {i} = 1 := by\n"
                    f"    rw [interpDag_input dag inputs {i} {n['input']} "
                    f"(by rw [dag_len]; omega)\n"
                    f"      (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                    f"(by rw [nodes_len]; omega)]; rfl)]\n    exact hone")
                continue
            c, w0, w1, ki = n["sum"][0]
            kmap[ki] = int(c, 16)
            onelines.append(
                f"  have p{i} : dag.getD {i} (.input 0) = .sum "
                f"[\u27e8Ecdsa2.consts F {ki}, {w0}, {w1}\u27e9] := by\n"
                f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]\n    rfl\n"
                f"  have o{i} : interpDag dag inputs {i} = 1 := by\n"
                f"    rw [interpDag_sum inputs dag {i} _ p{i} (vs.sum_operands_lt {i} _ p{i})]\n"
                f"    simp only [List.foldl_cons, List.foldl_nil, o{w0}, o{w1}, ck{ki}]\n"
                f"    push_cast; ring")
        cdefs = []
        for k in sorted(kmap):
            v = kmap[k]
            if v <= P // 2:
                cdefs.append(f"  have ck{k} : Ecdsa2.consts F {k} = (({v} : Nat) : F) :="
                             f" consts_pos {k} {v} (by rfl)")
            else:
                cdefs.append(f"  have ck{k} : Ecdsa2.consts F {k} = -(({P - v} : Nat) : F) :="
                             f" consts_neg {k} {P - v} (by rfl) (by norm_num)")
        vs_at = " ".join(f"v{i}" for i in wires)
        wnames = [v for v in sorted(used) if v in lt.nodes]
        sets = "\n".join(f"  set w{v} := interpDag dag inputs {v} with hw{v}" for v in wnames)
        # `clear_value` stops the kernel zeta-expanding let-bound wires back into full
        # `interpDag (raw.toDag ...)` terms. It is cheap now that only the wires a theorem
        # actually manipulates are `set` -- 16-ish per part, a handful in the combiner.
        if wnames:
            sets += ("\n  clear_value " + " ".join(f"w{v}" for v in wnames))
        e, l = st[(lo, hi)][0], st[(lo, hi)][1]
        alias_rw = (f"  try simp only [{', '.join('a' + str(j) for j in sorted(seen_a))}] "
                    f"at {vs_at}\n" if seen_a else "")
        rw1 = (f"  try simp only [{', '.join('ck' + str(k) for k in sorted(kmap))}] at {vs_at}\n"
               f"  try simp only [{', '.join('o' + str(i) for i in sorted(ones))}] at {vs_at}\n"
               + alias_rw
               + f"  push_cast at {vs_at}\n") if wires else ""
        _part = PART_STMT[0]
        _binders = ("\n    {dag : _} (hdag : dag = raw.toDag (Ecdsa2.consts F))"
                    if _part else "")
        # `subst` puts the part back in terms of `raw.toDag`, so everything below is unchanged;
        # only the *statement* is abstract, which is all the citation needs.
        _subst = "  subst hdag\n" if _part else ""
        return f'''theorem {tname} (inputs : Nat \u2192 F) (hone : inputs 0 = 1){_binders} :
    ECDSA2.BitLt.foldStL {segx(lo, hi, True)}
      = ({render(e, True)}, {render(l, True)}) := by
{_subst}  set dag := raw.toDag (Ecdsa2.consts F) with hdag
  have vs := Ecdsa2.valid (F := F) inputs
  have dag_len : dag.length = 26939 := by
    rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len
{chr(10).join(chain)}
{chr(10).join(cdefs)}
{chr(10).join(onelines)}
{chr(10).join(alines)}
{rw1}{chr(10).join(c.replace("@CITE@", "") for c in steps if c.startswith("@CITE@"))}
{sets}
{chr(10).join(c for c in steps if not c.startswith("@CITE@"))}
  exact s{lo}_{hi}'''

    blocks = [mk(lo, hi, partname[(lo, hi)], set()) for (lo, hi) in parts]
    blocks.append(mk(0, leaves, name, set(parts)))

    print(f'''-- Generated by `formal/tools/gen_lt_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.BitLt

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-!
# `{name}`: the circuit's comparator is `BitLt`'s fold

Mirrors `tree_fold2`'s balanced split rather than expanding `foldStL`, which over 256 states
would be a degree-256 polynomial in 256 atoms. Each internal node contributes one two-component
identity over at most four wires; `BitLt.step_assoc` is what makes the tree shape irrelevant.

Split into {len(parts)} subtree theorems plus a combiner: all 511 node lemmas and 602 value
equations in one proof aborted the interpreter under `-M 12000`, and each subtree needs only the
wires beneath it.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

private theorem hpB : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

{(chr(10) * 2).join(blocks)}

end Ecdsa2.Meaning''')


main()
