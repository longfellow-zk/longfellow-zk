"""Emit a wrapping-sum instance's *word* layer: the cone read as a SHA-256 round equation.

The seam (`gen_gf2_seam.py`) leaves a 32-bit modular equation over 224 individual bits. This
turns those bits into words. Per addend group of 32 rows:

* `one`  -- the 32 bits are a word's bits in order, so `ofBits` of them *is* the word;
* `xor3` -- the three legs are one word at three rotations, which is `Σ₀`/`Σ₁`, and
            `SHA/Sigma.lean`'s `Sigma0_bits`/`Sigma1_bits` say so per output bit;
* `ch`   -- `Ch_bits`;
* `maj`  -- `Maj_bits`.

Every word list is expressed as `map<o>` of leaf indices rather than as literal node indices, so
the two sides' atoms are syntactically identical and the regrouping is a plain `ring`. That, plus
the canonical wire ordering `gen_gf2_row.py` now imposes, is what removes any per-bit reasoning.

Usage: SHA_ARTIFACT=Sha256Gf2 python3 gen_gf2_word.py TAG:E [--rowmod NAME] [--out DIR]
"""
import sys, os, argparse
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_gf2_inj as I
import gen_gf2_row as R
import gen_gf2_seam as S
import gf2_word_probe as WP

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BRIDGE = os.path.join(ROOT, "circuits", "quadcert", "Bridge", "Sha256Gf2")
NEDGES = 6656
SHAK = I.SHAK
# (rotation offsets, shift amount) -> the specification's function. A `None` shift is a pure
# rotate-xor (`Σ₀`/`Σ₁`); a shift is `σ₀`/`σ₁`, whose leg vanishes at the top `d` bit positions.
ROT = {((2, 13, 22), None): "Sigma0", ((6, 11, 25), None): "Sigma1",
       ((7, 18), 3): "sigma0", ((17, 19), 10): "sigma1"}


def analyse(o):
    """(build, node->leaf, groups, forms) with one group per addend.

    `xor2` and `xor3` rows of the same base word are **one** addend -- that is `σ₀`/`σ₁`, whose
    shift leg is absent at the top bit positions -- so they are keyed together.
    """
    b = I.build(o)
    mp = b['mp']
    n2l = {}
    for i, nd in enumerate(b['leaves']):
        n2l.setdefault(nd, i)
    fs, shape = R.cone_forms(b)
    gs = defaultdict(list)
    for j in range(b['M']):
        if b['kk'][j] is not None:
            continue
        p = b['bit'][j]
        f = fs[j]
        if f[0] in ('xor2', 'xor3'):
            bases = {(n, t) for w in f[1:]
                     for s in [R.wordsig(mp[w], p)] if s for (n, t, _) in [s]}
            base = bases.pop()
            gs[('xor', (base, shape[base]))].append((p, j))
        else:
            sig = tuple(R.wordsig(mp[w], p) for w in f[1:])
            gs[(f[0], sig)].append((p, j))
    return b, n2l, gs, fs


def wlist(o, n2l, name, t):
    """`wordBits t` etc. as `map<o>` of leaf indices, so both sides share atoms."""
    return "[" + ", ".join(f"map{o} {n2l[nd]}" for nd in WP.WORD[(name, t)]) + "]"


def blist(o, n2l, name, t):
    """The same list with `nb` already distributed: what the `*_bits` lemmas take as `bs`."""
    return "[" + ", ".join(f"nb α inputs (map{o} {n2l[nd]})" for nd in WP.WORD[(name, t)]) + "]"


def wname(name, t):
    return f"{name} {t}"


def sumexpr(o, ps):
    return " + ".join(f"2 ^ {p} * nOf{o} α inputs {j}" for (p, j) in sorted(ps))


def group_lemma(tag, o, n2l, kind, sig, ps, lines, b):
    A = lines.append
    # `simp only [formOf<o>]` does not scale: at 255 equations its equation-lemma machinery blows
    # the recursion limit, while `rfl` on the same match is instant (the kernel handles Nat
    # literal `casesOn` directly). So each row's form is rewritten by `rfl` instead.
    fs, _ = R.cone_forms(b)
    rws = ", ".join(
        f"hs{o} {j} (by norm_num), show formOf{o} {j} = {R.lean_form(fs[j])} from rfl"
        for (p, j) in sorted(ps))
    tail = [f"  have hs{o} := spec{o} α hgen inputs hin0 hzb",
            f"  rw [{rws}]",
            "  simp only [Form.spec, nb_lvAt]",
            "  all_goals ring"]
    hdr = (f"theorem {tag} (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)\n"
           f"    (hzb : ∀ e, e < {NEDGES} →\n"
           f"      interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0) :")
    if kind == 'one':
        (n, t, _), = sig
        A(hdr)
        A(f"    wv α inputs ({wname(n, t)}) = {sumexpr(o, ps)} := by")
        A(f"  rw [show {wname(n, t)} = {wlist(o, n2l, n, t)} from by decide]")
        A(f"  simp only [wv, List.map_cons, List.map_nil, ofBits]")
        lines.extend(tail)
        return f"wv α inputs ({wname(n, t)})"
    if kind == 'xor':
        (n, t), rs = sig
        fn = ROT[rs]
        A(hdr)
        A(f"    {fn} (wv α inputs ({wname(n, t)})) = {sumexpr(o, ps)} := by")
        A(f"  rw [show {wname(n, t)} = {wlist(o, n2l, n, t)} from by decide]")
        A(f"  simp only [wv, List.map_cons, List.map_nil]")
        A(f"  rw [{fn}_bits {blist(o, n2l, n, t)} (by rfl)")
        A(f"    (wv_isBits α inputs {wlist(o, n2l, n, t)}), ofBits_range32]")
        A(f"  simp only [Nat.reduceAdd, Nat.reduceMod, List.getD_cons_zero,")
        A(f"    List.getD_cons_succ, List.getD_nil, xb_zero]")
        lines.extend(tail)
        return f"{fn} (wv α inputs ({wname(n, t)}))"
    if kind in ('ch', 'maj'):
        fn = "Ch" if kind == 'ch' else "Maj"
        ws = [(n, t) for (n, t, _) in sig]
        args = " ".join(f"(wv α inputs ({wname(n, t)}))" for (n, t) in ws)
        A(hdr)
        A(f"    {fn} {args} = {sumexpr(o, ps)} := by")
        for (n, t) in ws:
            A(f"  rw [show {wname(n, t)} = {wlist(o, n2l, n, t)} from by decide]")
        A(f"  simp only [wv, List.map_cons, List.map_nil]")
        extra = "(by rfl) " if kind == 'ch' else ""
        A(f"  rw [{fn}_bits " + " ".join(blist(o, n2l, n2, t2) for (n2, t2) in ws)
          + f" {extra}"
          + " ".join(f"(wv_isBits α inputs {wlist(o, n2l, n2, t2)})" for (n2, t2) in ws)
          + ", ofBits_range32]")
        A(f"  simp only [List.getD_cons_zero, List.getD_cons_succ]")
        lines.extend(tail)
        return f"{fn} {args}"
    raise SystemExit(f"unhandled group kind {kind}")


def emit(tag, e, n, hin0, mp, rowmod):
    ops = mp[:4]
    B, N2L, G, FS = {}, {}, {}, {}
    for o in dict.fromkeys(ops):
        B[o], N2L[o], G[o], FS[o] = analyse(o)
    L = []
    A = L.append
    if rowmod:
        A(f"import quadcert.Bridge.Sha256Gf2.{rowmod}")
    else:
        for g in sorted({S.ROWGROUP[o] for o in ops}):
            A(f"import quadcert.Bridge.Sha256Gf2.Gf2Rows{g}")
    A("import quadcert.Bridge.Sha256Gf2.Gf2Word")
    A("import quadcert.Bridge.Sha256Gf2.Gf2Words")
    A(f"import quadcert.Bridge.Sha256Gf2.Gf2Seam{tag}_{e}")
    A("")
    A("/-!")
    A(f"# `{tag}` instance {e} as a SHA-256 round equation")
    A("")
    A("The seam reads assertion node "
      f"{mp[-1]} as a 32-bit modular equation over individual bits;")
    A("this reads those bits as words. Generated by `tools/sha256/gen_gf2_word.py`, whose group")
    A("identification is the one reported in `tools/sha256/GF2_WORD_AUDIT.md`.")
    A("-/")
    A("")
    A("set_option maxRecDepth 8000000")
    A("set_option maxHeartbeats 4000000")
    A("")
    A("namespace Sha256Gf2")
    A("")
    A("open Quadcert Quadcert.Gen.Sha256Gf2 GF128 SHA256")
    A("")
    A("variable {F : Type} [Field F] [CharP F 2]")
    A("")
    # want side (position 2 or 3, whichever is not the constant chain)
    wi = [i for i in (2, 3) if I.flat(B[ops[i]]) != "0"]
    gi = [0, 1]
    body, terms = [], {}
    names = {}
    kk = 0
    for slot in gi + wi:
        o = ops[slot]
        rank = {'one': 0, 'xor': 1, 'ch': 2, 'maj': 3}
        for (kind, sig), ps in sorted(G[o].items(),
                                      key=lambda kv: (rank[kv[0][0]], str(kv[0][1]))):
            nm = f"wg{tag}_{e}_{kk}"
            kk += 1
            expr = group_lemma(nm, o, N2L[o], kind, sig, ps, body, B[o])
            body[-1] = body[-1]  # no-op, keeps the list shape explicit
            names[nm] = (slot, o, expr, sorted(ps))
    for ln in body:
        A(ln)
    A("")
    A(f"theorem word{tag}_{e} (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hzb : ∀ e, e < {NEDGES} →")
    A("      interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0)")
    A(f"    (hz : interpDag (raw.toDag (consts α)) inputs (map{tag} {e} root{tag}) = 0) :")
    wantnm = [nm for nm, v in names.items() if v[0] in wi]
    gotnm = [nm for nm, v in names.items() if v[0] in gi]
    assert len(wantnm) == 1
    kconst = sum(I.PRODK[B[o]['kk'][j]] for o in dict.fromkeys(ops)
                 for j in range(B[o]['M'])
                 if B[o]['kk'][j] is not None and I.PRODK[B[o]['kk'][j]])
    kidx = [i for i, v in enumerate(SHAK) if v == kconst]
    kterm = "" if kconst == 0 else (f" + K.getD {kidx[0]} 0" if kidx else f" + {kconst}")
    klit = "" if kconst == 0 else f" + {kconst}"
    rhs = " + ".join(names[nm][2] for nm in gotnm) + kterm
    rhslit = " + ".join(names[nm][2] for nm in gotnm) + klit
    A(f"    {names[wantnm[0]][2]} = ({rhs}) % 2 ^ 32 := by")
    for nm in names:
        A(f"  have h{nm} := {nm} α hgen inputs hin0 hzb")
    A(f"  have hw := seam{tag}_{e} α hgen inputs hin0 hzb hz")
    wflat = " + ".join(f"({I.flat(B[ops[i]]).replace('n ', f'nOf{ops[i]} α inputs ')})"
                       for i in (2, 3))
    gflat = " + ".join(f"({I.flat(B[ops[i]]).replace('n ', f'nOf{ops[i]} α inputs ')})"
                       for i in (0, 1))
    A(f"  have e1 : {wflat} = {names[wantnm[0]][2]} := by")
    A(f"    rw [h{wantnm[0]}]")
    A("    all_goals ring")
    A(f"  have e2 : {gflat} = {rhslit} := by")
    A("    rw [" + ", ".join(f"h{nm}" for nm in gotnm) + "]")
    A("    all_goals ring")
    if kidx:
        A(f"  rw [show K.getD {kidx[0]} 0 = ({kconst} : Nat) from by decide]")
    A("  rw [← e1, hw, e2]")
    A("")
    A("end Sha256Gf2")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("inst")
    ap.add_argument("--rowmod")
    ap.add_argument("--out", default=BRIDGE)
    args = ap.parse_args()
    import probe_inj as PI
    _maps = S.read_maps()
    _all = set(PI.operands())
    for _t, _n, _h in S.CLASSES:
        for _e, _mp in _maps[_t].items():
            _all.update(_mp[:4])
    for _i, _o in enumerate(sorted(_all)):
        S.ROWGROUP[_o] = _i // 16
    tag, e = args.inst.split(":")
    e = int(e)
    n, hin0 = {t: (n, h) for (t, n, h) in S.CLASSES}[tag]
    mp = S.read_maps()[tag][e]
    path = os.path.join(args.out, f"Gf2Word{tag}_{e}.lean")
    open(path, "w").write(emit(tag, e, n, hin0, mp, args.rowmod))
    print("wrote", path)
