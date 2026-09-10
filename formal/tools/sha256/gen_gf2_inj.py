"""Emit the GF(2^128) *injection* cones as α-power chains.

The wrapping-sum cone (`gen_gf2_wrap.py`) stops at `got` and `want`, each a product of two
earlier nodes.  Those four nodes per cone -- 428 across the artifact -- are the injection cones,
and templating them is the wrong move: measured, they have 7 leaf-kind mixes but **204** distinct
templates, ~2 instances each, because the compiler puts the fused 2-, 3- and 4-term factors at
different positions in every one.

So each cone is emitted on its own, in the only form that makes the tree shape irrelevant: every
row is a power of α.  A row is either

    [(0,0,0)] ++ [(2+i, a, b) ...]   an injection factor, α^(2^i · x) for the bit x it spells
    [(k, a, b)]                      a product, α^(K + eₐ + e_b), with K = 0 or a round constant

and `Core/ConeChain.chainVals_row` reads one row against the whole chain, so a proof pays O(1)
per row rather than unfolding the cone.  `coneIs` is simulated here before anything is written.

Usage:  SHA_ARTIFACT=Sha256Gf2 python3 gen_gf2_inj.py [--only NODE] [--out DIR]
"""
import sys, os, argparse
from collections import Counter, OrderedDict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_gf2_wrap as G
import probe_inj as P

nodes = G.nodes; consts = G.consts
ONE = 0
NNODES = len(nodes)

# constant index -> exponent K with constNat k = alpha^K, for the coefficients a product row
# may carry: the shared 1 (K = 0) and the 64 folded round constants.
SHAK = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
PRODK = {0: 0}
for t, k in enumerate(SHAK):
    PRODK[40 + t] = k
INJK = {2 + i: i for i in range(32)}       # coefficient index -> bit position


def walk(root):
    """Topological order of the cone: ('fac', node, pos, ops) / ('prod', node, k, a, b) / leaves.

    A node is a *row* when it is a `sum` that depends on the witness; anything else (the `one`
    wire, the constant squaring chains) is a leaf, and leaves contribute exponent 0.
    """
    order, idx = [], {}
    leaves = []

    def leaf(n):
        if n not in idx:
            idx[n] = ('L', len(leaves))
            leaves.append(n)
        return idx[n]

    leaf(ONE)

    def visit(n):
        if n in idx:
            return idx[n]
        kind, v = nodes[n]
        if kind != 'sum':
            return leaf(n)
        if len(v) == 1 and v[0][0] in PRODK:
            c, a, b = v[0]
            ia, ib = visit(a), visit(b)
            idx[n] = ('R', len(order)); order.append(('prod', n, c, ia, ib)); return idx[n]
        # an injection factor: `1` on `one*one`, then one shared coefficient on the rest
        if v[0][0] != 0 or v[0][1] != ONE or v[0][2] != ONE:
            return None
        ks = set(t[0] for t in v[1:])
        if len(ks) != 1 or ks.pop() not in INJK:
            return None
        k = v[1][0]
        ops = [(t[1], t[2]) for t in v[1:]]
        for (a, b) in ops:
            leaf(a); leaf(b)
        idx[n] = ('R', len(order)); order.append(('fac', n, INJK[k], ops)); return idx[n]

    if visit(root) is None:
        return None
    return order, leaves, idx


def build(root):
    """Template nodes + instance map + per-row data, or None."""
    w = walk(root)
    if w is None:
        return None
    order, leaves, idx = w
    L = len(leaves)
    if leaves[0] != ONE:
        return None
    pos = {n: i for i, n in enumerate(leaves)}

    def ref(t):
        return t[1] if t[0] == 'L' else L + t[1]

    mv, ts, bit, kk = [], [], [], []
    for row in order:
        if row[0] == 'fac':
            _, n, i, ops = row
            mv.append([(0, 0, 0)] + [(2 + i, pos[a], pos[b]) for (a, b) in ops])
            ts.append([(pos[a], pos[b]) for (a, b) in ops]); bit.append(i); kk.append(None)
        else:
            _, n, c, ia, ib = row
            mv.append([(c, ref(ia), ref(ib))])
            ts.append([]); bit.append(0); kk.append(c)
    tn = [('leaf', i) for i in range(L)] + [('sum', m) for m in mv]
    mp = leaves + [r[1] for r in order]
    return dict(L=L, M=len(order), tn=tn, mp=mp, mv=mv, ts=ts, bit=bit, kk=kk, order=order,
                leaves=leaves)


def exponent(b, j):
    """Row j's exponent, as a Lean `Nat` expression. Parenthesised to match the row lemmas."""
    if b['kk'][j] is None:
        return f"(2 ^ {b['bit'][j]} * n {j})"
    K = PRODK[b['kk'][j]]
    L = b['L']

    def sub(x):
        return "0" if x < L else exponent(b, x - L)
    a, c = b['mv'][j][0][1], b['mv'][j][0][2]
    return f"({K} + {sub(a)} + {sub(c)})"


def flat(b):
    """The root exponent as a flat sum: the folded round constants first, then the injected bits
    ascending in bit position.  That is the shape the word layer wants -- and note what it says:
    over GF(2^128) SHA-256's `Kₜ` shows up as a *summand of the exponent*, exactly as the spec's
    `T1 = h + Σ₁(e) + Ch + Kₜ + Wₜ` has it, because `algsimp` folded `α^(Kₜ)` into a product."""
    ks = [PRODK[b['kk'][j]] for j in range(b['M'])
          if b['kk'][j] is not None and PRODK[b['kk'][j]] != 0]
    ts = sorted((b['bit'][j], j) for j in range(b['M']) if b['kk'][j] is None)
    parts = [str(k) for k in ks] + [f"2 ^ {i} * n {j}" for (i, j) in ts]
    return " + ".join(parts) if parts else "0"


def flat_bound(b):
    """`1 + Σ` of the flat sum's term-wise maxima."""
    ks = [PRODK[b['kk'][j]] for j in range(b['M'])
          if b['kk'][j] is not None and PRODK[b['kk'][j]] != 0]
    ts = [b['bit'][j] for j in range(b['M']) if b['kk'][j] is None]
    return ks, sorted(ts), sum(ks) + sum(2 ** i for i in ts) + 1


def lean(tag, root, b):
    L, M = b['L'], b['M']
    out = []
    A = out.append
    A(f"import quadcert.Bridge.Sha256Gf2.Gf2Wrap\n")
    A("/-!")
    A(f"# Injection cone `{root}` as a power of α\n")
    A(f"{M} rows over {L} leaves: {sum(1 for k in b['kk'] if k is None)} injection factors and")
    A(f"{sum(1 for k in b['kk'] if k is not None)} products. Generated by `gen_gf2_inj.py`;")
    A("`coneIs` matches the template against the artifact, so a mistranscribed index is rejected")
    A("by the kernel rather than believed. What is *not* structural, and is left to the caller,")
    A("is `hval`: what bit each injection factor injects.")
    A("-/\n")
    A("set_option maxRecDepth 8000000")
    A("set_option maxHeartbeats 4000000\n")
    A("namespace Sha256Gf2\n")
    A("open Quadcert Quadcert.Gen.Sha256Gf2 GF128\n")
    A("variable {F : Type} [Field F] [CharP F 2]\n")

    A(f"def mv{tag} : Nat → List (Nat × Nat × Nat)")
    for j, m in enumerate(b['mv']):
        head = f"  | {j} =>" if j + 1 < M else "  | _ =>"
        A(head + " [" + ", ".join(f"({c}, {x}, {y})" for (c, x, y) in m) + "]")
    A("")
    A(f"def ts{tag} : Nat → List (Nat × Nat)")
    for j, t in enumerate(b['ts']):
        head = f"  | {j} =>" if j + 1 < M else "  | _ =>"
        A(head + " [" + ", ".join(f"({x}, {y})" for (x, y) in t) + "]")
    A("")
    A(f"def tn{tag} : List TmplNode :=")
    A(f"  (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))")
    A(f"    ++ (List.range {M}).map (fun k => TmplNode.sum (mv{tag} k))\n")
    A(f"def map{tag} : Nat → Nat :=")
    A(f"  fun i => ([" + ", ".join(str(x) for x in b['mp']) + f"] : List Nat).getD i 0\n")
    A(f"theorem cone{tag} : coneIs nodeFn tn{tag} map{tag} = true := by decide +kernel\n")
    A(f"theorem map{tag}_lt : (List.range {L + M}).all "
      f"(fun i => decide (map{tag} i < {NNODES})) = true := by decide +kernel\n")

    A(f"theorem inj{tag} (α : F) (hgen : IsGen α) (inputs : Nat → F) (lv : Nat → F)")
    A(f"    (hlv : lv = fun h => interpDag (raw.toDag (consts α)) inputs (map{tag} h))")
    A(f"    (hin0 : inputs 0 = 1) (n : Nat → Nat)")
    A(f"    (hval : ∀ j, j < {M} →")
    A(f"      ((ts{tag} j).map (fun t => lv t.1 * lv t.2)).sum = (n j : F))")
    A(f"    (hn : ∀ j, j < {M} → n j = 0 ∨ n j = 1) :")
    A(f"    interpDag (raw.toDag (consts α)) inputs {root} = α ^ ({flat(b)}) := by")
    A(f"  have hone : lv 0 = 1 := by subst hlv; exact node0 α inputs hin0")
    A(f"  have hmap : ∀ i, i < tn{tag}.length → map{tag} i < raw.nodes.length := by")
    A(f"    intro i hi")
    A(f"    rw [nodes_len]")
    A(f"    have h := map{tag}_lt")
    A(f"    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h")
    A(f"    exact h i (by simpa [tn{tag}] using hi)")
    A(f"  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tn{tag} map{tag}")
    A(f"    cone{tag} hmap ({L} + {M - 1}) (by simp [tn{tag}])")
    A(f"  have hbd : ∀ j, j < {M} → ∀ t ∈ mv{tag} j, t.2.1 < {L} + j ∧ t.2.2 < {L} + j := by")
    A(f"    decide +kernel")
    A(f"  have hchain := interpDag_leafChain (consts α) lv {L} {M} mv{tag} hbd")
    A(f"    (show {M - 1} < {M} by norm_num)")
    A(f"  simp only [tn{tag}] at htr")
    A(f"  rw [← hlv] at htr")
    A(f"  have hc0 : consts α 0 = 1 := consts_one α")
    A(f"  have hc0' : consts α 0 = α ^ 0 := consts_one_pow α")
    A(f"  have hci : ∀ i, i < 32 → consts α (2 + i) = α ^ 2 ^ i - 1 :=")
    A(f"    fun i hi => consts_inj α hgen i hi")
    if any(k is not None and k != 0 for k in b['kk']):
        A(f"  have hcp : ∀ t, t < 64 → consts α (40 + t) = α ^ (shaK.getD t 0) :=")
        A(f"    fun t ht => consts_round α hgen t ht")
    # A row feeds at most one later row (the cone is a tree), so its `have` can be discharged
    # as soon as its consumer is emitted.  Without this the local context grows to M hypotheses
    # and every `exact` pays for traversing it: measured, 0.40 s/row at M=255 against 0.10 s/row
    # at M=63, i.e. quadratic in the cone.
    uses = Counter()
    for j in range(M):
        if b['kk'][j] is not None:
            _, x, y = b['mv'][j][0]
            for z in (x, y):
                if z >= L:
                    uses[z - L] += 1
    for j in range(M):
        e = exponent(b, j)
        A(f"  have r{j} : (chainVals (consts α) lv {L} mv{tag} {M}).getD {j} 0 = α ^ {e} := by")
        A(f"    rw [chainVals_row (consts α) lv {L} mv{tag} (by norm_num) (hbd {j} (by norm_num))]")
        if b['kk'][j] is None:
            i = b['bit'][j]
            tsj = "[" + ", ".join(f"({x}, {y})" for (x, y) in b['ts'][j]) + "]"
            A(f"    exact chainNode_fac_pow (consts α) lv {L} _ α {i} (n {j}) {tsj} hone")
            A(f"      (by norm_num) (by decide) hc0 (hci {i} (by norm_num))")
            A(f"      (hval {j} (by norm_num)) (hn {j} (by norm_num))")
        else:
            k = b['kk'][j]
            c, x, y = b['mv'][j][0]
            hck = "hc0'" if k == 0 else f"(hcp {k - 40} (by norm_num))"

            def rd(z):
                if z < L:
                    assert z == 0, f"prod row reads non-`one` leaf {z}"
                    return f"(chainRead_one_pow lv {L} _ α hone (by norm_num))"
                return f"(by rw [chainRead, if_neg (by norm_num)]; exact r{z - L})"
            A(f"    exact chainNode_prod_pow (consts α) lv {L} _ α {c} {x} {y} _ _ _ {hck}")
            A(f"      {rd(x)} {rd(y)}")
            done = []
            for z in (x, y):
                if z >= L:
                    uses[z - L] -= 1
                    if uses[z - L] == 0 and f"r{z - L}" not in done:
                        done.append(f"r{z - L}")
            if done:
                A("  clear " + " ".join(done))
    A(f"  have hE : {exponent(b, M - 1)} = {flat(b)} := by ring")
    A(f"  rw [show ({root} : Nat) = map{tag} {L + M - 1} from rfl, htr, hchain, r{M - 1}, hE]")
    facs = sorted((b['bit'][j], j) for j in range(M) if b['kk'][j] is None)
    ks, _, bound = flat_bound(b)
    A(f"\n/-- The exponent's range, which `wrap_nat_gf` needs before it can read the assertion as")
    A(f"    32-bit arithmetic. `{bound}` is `1 + Σ 2^i` over this cone's {len(facs)} factors.")
    A(f"")
    A(f"    Bounded term by term rather than by `omega`: at {len(facs)} atoms with coefficients up")
    A(f"    to 2^31 a single `omega` does not return, while a chain of `Nat.add_le_add` is linear.")
    A(f"    -/")
    A(f"theorem inj{tag}_lt (n : Nat → Nat) (hn : ∀ j, j < {M} → n j = 0 ∨ n j = 1) :")
    A(f"    {flat(b)} < {bound} := by")
    if not facs:
        A(f"  norm_num")
        return "\n".join(out) + "\n"
    A(f"  have hb : ∀ j, j < {M} → n j ≤ 1 := fun j hj => by")
    A(f"    rcases hn j hj with h | h <;> omega")
    for (i, j) in facs:
        A(f"  have t{j} : 2 ^ {i} * n {j} ≤ {2 ** i} := by")
        A(f"    have h := hb {j} (by norm_num); omega")
    terms = [(str(k), f"(le_refl {k})") for k in ks] \
        + [(str(2 ** i), f"t{j}") for (i, j) in facs]
    chain = terms[0][1]
    for (_, pf) in terms[1:]:
        chain = f"(Nat.add_le_add {chain} {pf})"
    tot = " + ".join(t for (t, _) in terms)
    A(f"  exact lt_of_le_of_lt (show {flat(b)} ≤ {tot} from {chain}) (by norm_num)")
    A("\nend Sha256Gf2")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", type=int)
    ap.add_argument("--out", default="/tmp")
    args = ap.parse_args()
    # every operand of every wrapping-sum cone, including the ones that carry no witness (the
    # constant squaring chains the compiler leaves in `want`): `probe_inj.operands` filters those
    # out, but the seam still needs them, as `α^0`.
    ops = set(P.operands())
    for (root, _, _) in G.read_asserts():
        a = G.analyse(root)
        if a is None:
            continue
        _, got, want, _, _ = a
        ops.update([got[0], got[1], want[0], want[1]])
    ops = sorted(ops)
    sel = [args.only] if args.only else ops
    stats = Counter()
    for o in sel:
        b = build(o)
        if b is None:
            stats['unbuildable'] += 1; continue
        if not G.cone_is(b['tn'], b['mp']):
            print("coneIs FAILED", o); stats['coneIs'] += 1; continue
        stats['ok'] += 1
        stats['rows'] += b['M']
        path = os.path.join(args.out, f"Gf2Inj{o}.lean")
        open(path, "w").write(lean(str(o), o, b))
        if args.only:
            print("wrote", path, b['L'], "leaves", b['M'], "rows")
    print(dict(stats))
