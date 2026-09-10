"""Emit each injection cone's row forms, discharging `hval` with no per-row proof.

`Gf2Row.rows_isBit` needs two decidable facts per cone -- that every row's operand pairs are a
permutation of its form's canonical pairs, and that every form's wires are non-`one` leaves -- and
then `rows_val` turns that into the `hval`/`hn` pair `inj<o>` asks for, with `n` *defined* as
`bitOf` of the row rather than assumed.

Each row's form is identified by its **truth table** over every boolean assignment of its wires,
and the identification is re-checked here against the canonical form's own truth table before
anything is written; the `isPerm` decide in Lean then re-checks it again.

Usage: SHA_ARTIFACT=Sha256Gf2 python3 gen_gf2_row.py [--out DIR] [--group 16] [--only NODE]
"""
import sys, os, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_gf2_inj as I
import gen_gf2_wrap as G
import probe_inj as P
import gen_gf2_bool as GB
import gf2_word_probe as WP

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BRIDGE = os.path.join(ROOT, "circuits", "quadcert", "Bridge", "Sha256Gf2")


def truth(ts, ws):
    """The row's value at every boolean assignment of `ws` (wire 0 pinned to 1)."""
    out = []
    for m in range(1 << len(ws)):
        val = {0: 1}
        for t, w in enumerate(ws):
            val[w] = (m >> t) & 1
        s = 0
        for (x, y) in ts:
            s ^= val[x] & val[y]
        out.append(s)
    return out


def canon_pairs(f):
    k, a = f[0], f[1:]
    return {'prod': [], 'one': [(0, a[0])] if a else [],
            'xor2': [(0, a[0]), (0, a[1])] if len(a) > 1 else [],
            'xor3': [(0, a[0]), (0, a[1]), (0, a[2])] if len(a) > 2 else [],
            'ch': [(a[0], a[1]), (0, a[2]), (a[0], a[2])] if len(a) > 2 else [],
            'maj': [(a[0], a[1]), (a[1], a[2]), (a[0], a[2])] if len(a) > 2 else []}[k]


def canon_order(kind, ws, bitpos, mp):
    """Put a symmetric form's wires in an order that is the same at all 32 bit positions.

    `xor2`/`xor3`/`maj` are symmetric, and their canonical `Form.pairs` are order-independent as
    multisets, so reordering is free -- the `isPerm` decide still passes. Ordering by (word,
    rotation offset) is what makes a σ/Σ addend's 32 rows present the same leg order, which is
    what `SHA/Sigma.lean`'s `Sigma0_bits`/`Sigma1_bits` consume. `ch` is NOT symmetric (its first
    wire is the selector), so it is left alone.

    NOTE for σ₀/σ₁: their third leg is a *shift*, and `sigma0_bits`/`sigma1_bits` put it last
    rather than in offset order. A generator targeting those addends has to detect the shift --
    it is the offset missing from the top rows -- and move it to the end.
    """
    if kind not in ('xor2', 'xor3', 'maj'):
        return ws
    def key(w):
        cand = WP.NODE2WORD.get(mp[w] if mp else w, [])
        if not cand:
            return (1, "", 0, 0, w)
        return (0,) + min((n, t, (i - bitpos) % 32) for (n, t, i) in cand) + (w,)
    # xor legs ascend in rotation offset, matching `Sigma0_bits`/`Sigma1_bits`; `maj`'s three
    # wires share offset 0 and differ in round, and descending puts them in the specification's
    # (a, b, c) order, matching `Maj_bits`.
    return sorted(ws, key=key, reverse=(kind == 'maj'))


def classify(ts, bitpos=0, mp=None):
    """`('prod',) | ('one',a) | ('xor2',a,b) | ('xor3',a,b,c) | ('ch',a,b,c) | ('maj',a,b,c)`."""
    if not ts:
        return ('prod',)
    ws = []
    for (x, y) in ts:
        for z in (x, y):
            if z != 0 and z not in ws:
                ws.append(z)
    withzero = [p for p in ts if 0 in p]
    nz = [p for p in ts if 0 not in p]
    if len(ts) == 1:
        f = ('one', ws[0])
    elif len(ts) == 2 and not nz:
        f = ('xor2',) + tuple(canon_order('xor2', ws[:2], bitpos, mp))
    elif len(ts) == 3 and not nz:
        f = ('xor3',) + tuple(canon_order('xor3', ws[:3], bitpos, mp))
    elif len(ts) == 3 and len(nz) == 3:
        f = ('maj',) + tuple(canon_order('maj', ws[:3], bitpos, mp))
    elif len(ts) == 3 and len(withzero) == 1 and len(nz) == 2:
        c = [z for z in withzero[0] if z != 0][0]
        shared = set(nz[0]) & set(nz[1])
        if len(shared) != 1:
            return None
        a = shared.pop()
        # of the two non-zero pairs, the one that mentions `c` is (a, c); the other gives b
        other = [p for p in nz if c not in p]
        if len(other) != 1:
            return None
        b = [z for z in other[0] if z != a]
        if len(b) != 1:
            return None
        f = ('ch', a, b[0], c)
    else:
        return None
    # re-check: the canonical pairs must have the same truth table on the same wires
    if truth(ts, ws) != truth(canon_pairs(f), ws):
        return None
    return f


def wordsig(nd, bitpos):
    """`(word name, round, rotation offset)` for a DAG node, or `None` if it names no word."""
    cand = WP.NODE2WORD.get(nd, [])
    if not cand:
        return None
    return min((n, t, (i - bitpos) % 32) for (n, t, i) in cand)


def cone_forms(b):
    """Every row's form for one cone, with symmetric wires ordered *group*-consistently.

    A σ/Σ addend's 32 rows must present their legs in the same order, and for `σ₀`/`σ₁` the
    **shift** leg has to come last -- that is where `sigma0_bits`/`sigma1_bits` put it -- rather
    than in offset order. Shift and rotation cannot be told apart from a single row, so the order
    is decided per addend: a `≫d` leg exists only where `p + d < 32`, so the shift is the offset
    that is *absent* from the top `d` rows, while a rotation appears in all 32.

    Returns the list of forms, and a dict giving each xor addend's `(rotations, shift)`.
    """
    mp = b['mp']
    raw, sigs = {}, {}
    for j in range(b['M']):
        if b['kk'][j] is not None:
            raw[j] = ('prod',)
            continue
        p = b['bit'][j]
        f = classify(b['ts'][j])          # first-appearance wire order, no canonicalisation
        raw[j] = f
        sigs[j] = [wordsig(mp[w], p) for w in f[1:]]
    # group the xor rows of one base word: that is one addend
    addend = {}
    for j, f in raw.items():
        if f[0] not in ('xor2', 'xor3'):
            continue
        bases = {(n, t) for s in sigs[j] if s for (n, t, _) in [s]}
        if len(bases) != 1:
            continue
        addend.setdefault(bases.pop(), []).append(j)
    shape = {}
    for base, js in addend.items():
        cnt = {}
        for j in js:
            for s in sigs[j]:
                if s:
                    cnt[s[2]] = cnt.get(s[2], 0) + 1
        full = sorted(o for o, c in cnt.items() if c == len(js))
        part = sorted(o for o, c in cnt.items() if c != len(js))
        if len(part) > 1:
            raise SystemExit(f"addend {base}: {len(part)} partial offsets {part}, expected ≤ 1")
        shape[base] = (tuple(full), part[0] if part else None)
        order = list(full) + part
        for j in js:
            byoff = {s[2]: w for s, w in zip(sigs[j], raw[j][1:]) if s}
            ws = [byoff[o] for o in order if o in byoff]
            raw[j] = (raw[j][0],) + tuple(ws)
    # `maj`'s three wires share offset 0 and differ in round; descending puts them in the
    # specification's (a, b, c) order, which is what `Maj_bits` consumes.
    for j, f in raw.items():
        if f[0] != 'maj':
            continue
        ws = sorted(f[1:], key=lambda w: (wordsig(mp[w], b['bit'][j]) or (chr(0xff), 0, 0)),
                    reverse=True)
        raw[j] = ('maj',) + tuple(ws)
    return [raw[j] for j in range(b['M'])], shape


def lean_form(f):
    k = f[0]
    return ".prod" if k == 'prod' else "." + k + " " + " ".join(str(x) for x in f[1:])


BIT2EDGE = {b: e for e, (a, b) in enumerate(GB.pairs())}
NEDGES = len(BIT2EDGE)


def cone_block(o, b, forms):
    L, M = b['L'], b['M']
    edges = [0] + [BIT2EDGE[nd] for nd in b['leaves'][1:]]
    out = []
    A = out.append
    A(f"/-! ### Cone `{o}`: {M} rows over {L} leaves -/")
    A("")
    A(f"def formOf{o} : Nat → Form")
    for j, f in enumerate(forms):
        head = f"  | {j} =>" if j + 1 < M else "  | _ =>"
        A(head + " " + lean_form(f))
    A("")
    A(f"theorem perm{o} : (List.range {M}).all (fun j =>")
    A(f"    ((ts{o} j).map normPair).isPerm (((formOf{o} j).pairs).map normPair)) = true := by")
    A("  decide +kernel")
    A("")
    A(f"theorem wire{o} : (List.range {M}).all (fun j =>")
    A(f"    ((formOf{o} j).wires).all (fun i => decide (0 < i) && decide (i < {L})))")
    A("    = true := by decide +kernel")
    A("")
    A(f"/-- Which booleanity edge names each leaf. Leaf 0 is the `one` wire and has none. -/")
    A(f"def edgeOf{o} : Nat → Nat :=")
    A(f"  fun i => ([" + ", ".join(str(e) for e in edges) + f"] : List Nat).getD i 0")
    A("")
    A(f"theorem edge{o} : (List.range {L}).all (fun i =>")
    A(f"    (i == 0) || (decide (bitOfB (edgeOf{o} i) = map{o} i)")
    A(f"      && decide (edgeOf{o} i < {NEDGES}))) = true := by decide +kernel")
    A("")
    A(f"/-- **Cone `{o}`'s leaves are bits**, from the artifact's own `is_boolean` assertions. -/")
    A(f"theorem bl{o} (α : F) (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hz : ∀ e, e < {NEDGES} → interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0) :")
    A(f"    ∀ i, i < {L} → i ≠ 0 →")
    A(f"      lvAt α inputs map{o} i = 0 ∨ lvAt α inputs map{o} i = 1 := by")
    A("  intro i hi hne")
    A(f"  have h := edge{o}")
    A("  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,")
    A("    Bool.and_eq_true, decide_eq_true_eq] at h")
    A("  rcases h i hi with h0 | ⟨heq, hlt⟩")
    A("  · exact absurd h0 hne")
    A(f"  · have hb := allBoolBits α inputs hin0 hz (edgeOf{o} i) hlt")
    A("    rw [heq] at hb")
    A("    exact hb")
    A("")
    A(f"/-- The bit each of cone `{o}`'s rows injects, *defined* rather than assumed. -/")
    A(f"noncomputable def nOf{o} (α : F) (inputs : Nat → F) : Nat → Nat := fun j =>")
    A(f"  bitOf (((ts{o} j).map (fun t =>")
    A(f"    lvAt α inputs map{o} t.1 * lvAt α inputs map{o} t.2)).sum)")
    A("")
    A(f"/-- **Cone `{o}` as a power of α, with only leaf booleanity left.** -/")
    A(f"theorem injB{o} (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hbl : ∀ i, i < {L} → i ≠ 0 →")
    A(f"      lvAt α inputs map{o} i = 0 ∨ lvAt α inputs map{o} i = 1) :")
    A(f"    interpDag (raw.toDag (consts α)) inputs {o}")
    A(f"      = α ^ ({I.flat(b).replace('n ', f'nOf{o} α inputs ')}) := by")
    A(f"  have hone : lvAt α inputs map{o} 0 = 1 := node0 α inputs hin0")
    A(f"  have hp : ∀ j, j < {M} → ((ts{o} j).map normPair).Perm")
    A(f"      (((formOf{o} j).pairs).map normPair) := by")
    A(f"    have h := perm{o}")
    A("    simp only [List.all_eq_true, List.mem_range] at h")
    A("    exact fun j hj => List.isPerm_iff.mp (h j hj)")
    A(f"  have hw : ∀ j, j < {M} → ∀ i ∈ (formOf{o} j).wires, i < {L} ∧ i ≠ 0 := by")
    A(f"    have h := wire{o}")
    A("    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h")
    A("    intro j hj i hi")
    A("    have hx := h j hj i hi")
    A("    exact ⟨hx.2, by omega⟩")
    A(f"  have hbit := rows_isBit (lvAt α inputs map{o}) {L} {M} hone hbl ts{o} formOf{o} hp hw")
    A(f"  have hv := rows_val (lvAt α inputs map{o}) {M} ts{o} hbit")
    A(f"  exact inj{o} α hgen inputs (lvAt α inputs map{o}) rfl hin0 (nOf{o} α inputs) hv.1 hv.2")
    A("")
    A(f"/-- **Each row's bit, in the specification's vocabulary.** `Form.spec` is `xb`, `chb` and")
    A(f"    `majb` -- exactly what `SHA/Sigma.lean`'s rotation lemmas consume. -/")
    A(f"theorem spec{o} (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hz : ∀ e, e < {NEDGES} → interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0) :")
    A(f"    ∀ j, j < {M} → nOf{o} α inputs j")
    A(f"      = Form.spec (fun i => bitOf (lvAt α inputs map{o} i)) (formOf{o} j) := by")
    A(f"  have hp : ∀ j, j < {M} → ((ts{o} j).map normPair).Perm")
    A(f"      (((formOf{o} j).pairs).map normPair) := by")
    A(f"    have h := perm{o}")
    A("    simp only [List.all_eq_true, List.mem_range] at h")
    A("    exact fun j hj => List.isPerm_iff.mp (h j hj)")
    A(f"  have hw : ∀ j, j < {M} → ∀ i ∈ (formOf{o} j).wires, i < {L} ∧ i ≠ 0 := by")
    A(f"    have h := wire{o}")
    A("    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h")
    A("    intro j hj i hi")
    A("    have hx := h j hj i hi")
    A("    exact ⟨hx.2, by omega⟩")
    A(f"  exact rows_spec (lvAt α inputs map{o}) {L} {M} (node0 α inputs hin0)")
    A(f"    (bl{o} α inputs hin0 hz) ts{o} formOf{o} hp hw")
    A("")
    A(f"/-- **…and with nothing left but the artifact's own assertions.** -/")
    A(f"theorem injZ{o} (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hz : ∀ e, e < {NEDGES} → interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0) :")
    A(f"    interpDag (raw.toDag (consts α)) inputs {o}")
    A(f"      = α ^ ({I.flat(b).replace('n ', f'nOf{o} α inputs ')}) :=")
    A(f"  injB{o} α hgen inputs hin0 (bl{o} α inputs hin0 hz)")
    A("")
    return out


def group_module(tag, cones, B, F):
    out = []
    A = out.append
    A("import quadcert.Bridge.Sha256Gf2.Gf2Spec")
    A("import quadcert.Bridge.Sha256Gf2.Gf2BoolEdges")
    for o in cones:
        A(f"import quadcert.Bridge.Sha256Gf2.Gf2Inj{o}")
    A("")
    A("/-!")
    A(f"# Row forms for injection cones {', '.join(str(o) for o in cones)}")
    A("")
    A("Per cone: the form of every row as data, two `decide`s that the data matches the artifact,")
    A("and `injB<o>` -- the cone as a power of α with only leaf booleanity left standing.")
    A("Generated by `tools/sha256/gen_gf2_row.py`.")
    A("-/")
    A("")
    A("set_option maxRecDepth 8000000")
    A("set_option maxHeartbeats 4000000")
    A("")
    A("namespace Sha256Gf2")
    A("")
    A("open Quadcert Quadcert.Gen.Sha256Gf2 GF128")
    A("")
    A("variable {F : Type} [Field F] [CharP F 2]")
    A("")
    for o in cones:
        out.extend(cone_block(o, B[o], F[o]))
    A("end Sha256Gf2")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=BRIDGE)
    ap.add_argument("--group", type=int, default=16)
    ap.add_argument("--only", type=int, nargs="*")
    ap.add_argument("--name", default="Gf2Rows")
    args = ap.parse_args()
    ops = set(P.operands())
    for (root, _, _) in G.read_asserts():
        a = G.analyse(root)
        if a:
            ops.update([a[1][0], a[1][1], a[2][0], a[2][1]])
    ops = sorted(ops)
    if args.only:
        ops = args.only
    B, F, bad = {}, {}, []
    for o in ops:
        b = I.build(o)
        fs, _ = cone_forms(b)
        for j, f in enumerate(fs):
            if f is None:
                bad.append((o, j, b['ts'][j]))
                fs[j] = ('prod',)
        B[o], F[o] = b, fs
    if bad:
        print(f"UNCLASSIFIED ROWS: {len(bad)}", bad[:5])
        sys.exit(1)
    groups = [ops[i:i + args.group] for i in range(0, len(ops), args.group)]
    for k, g in enumerate(groups):
        open(os.path.join(args.out, f"{args.name}{k}.lean"), "w").write(
            group_module(k, g, B, F))
    print(f"wrote {len(groups)} modules over {len(ops)} cones, "
          f"{sum(B[o]['M'] for o in ops)} rows, 0 unclassified")
