#!/usr/bin/env python3
"""Prove that `rx_eq` / `e_eq` / `nmsinv` say what `bitsLE` says.

Usage: gen_bitsum_meaning.py cone.json THEOREM_NAME KIND > out.lean
       KIND is `eq` (a witness equals the bit sum) or `inv` (the bit sum is invertible).

These three cones are 2,313 nodes -- large enough that expanding them to input wires is
hopeless, since each of the 256 bits is a degree-7 table interpolant in its digit and the
interpolants would multiply through a 256-term sum.

But they do not need expanding. `as_eltw_unsafe` weights bit `i` by `2^i` and the compiler fuses
the whole thing into a *single* 257-term root node, whose operands are exactly the 256 table
evaluations plus the witness. Cutting there leaves a polynomial that is linear (`eq`) or
quadratic (`inv`) in 257 opaque atoms -- a few hundred monomials, which `ring` does in seconds.

What the bits *are* is then a separate, per-digit question, answered by the range and bit
extractor certificates; keeping the two apart is what makes either tractable.

The bit index of each atom is read off its coefficient (`c = s * 2^k`) rather than assumed from
term order, and the result is checked against `bitsLE` modulo `p` -- so a misread order fails.
"""
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, signed  # noqa: E402

N = 256


def main():
    d = json.load(open(sys.argv[1]))
    name, kind = sys.argv[2], sys.argv[3]
    nodes = {n["id"]: n for n in d["nodes"]}
    ins = {n["id"]: n for n in d["nodes"] if "input" in n}
    one = next(i for i, n in nodes.items() if n.get("name") == "one")

    def is_one(i):
        """`copy.rs` aligns depth by squaring `one`, so `1` appears under many ids."""
        if i == one:
            return True
        s = nodes[i].get("sum")
        return bool(s) and len(s) == 1 and s[0][0] == "1" and is_one(s[0][1]) and is_one(s[0][2])

    def resolve(i):
        """Follow `1 * one * x` copy nodes to the value they alias."""
        while True:
            s = nodes[i].get("sum")
            if not (s and len(s) == 1 and s[0][0] == "1"):
                return i
            a, b = s[0][1], s[0][2]
            nxt = b if is_one(a) else a if is_one(b) else None
            if nxt is None or nxt == i:
                return i
            i = nxt

    terms = nodes[d["root"]]["sum"]
    assert len(terms) == N + 1, f"expected {N + 1} root terms, got {len(terms)}"

    # Classify each term: (coefficient, the non-`one` operands, after copy resolution).
    parsed = []
    for c, w0, w1, ki in terms:
        ops = [resolve(w) for w in (w0, w1) if not is_one(w)]
        parsed.append((int(c, 16), ops, ki))

    if kind == "eq":
        # 256 terms `c * b_k` plus one `±1 * w`. Bit 0 also carries a unit coefficient, so
        # the witness is picked out by resolving to an *input* wire -- bits never do.
        wt = [t for t in parsed
              if abs(signed(t[0])) == 1 and len(t[1]) == 1 and t[1][0] in ins]
        assert len(wt) == 1, f"expected one unit-coefficient input term, got {len(wt)}"
        wnode = wt[0][1][0]
        bits = [t for t in parsed if t is not wt[0]]
        scale = signed(wt[0][0])
        extra = []
    else:
        # 256 terms `c * b_k * v` plus one constant `c * 1 * 1`.
        const = [t for t in parsed if not t[1]]
        assert len(const) == 1, f"expected one constant term, got {len(const)}"
        vs = {o for t in parsed if t[1] for o in t[1]}
        common = [v for v in vs if all(v in t[1] for t in parsed if t[1])]
        assert len(common) == 1, f"no single common factor among {sorted(vs)[:8]}"
        wnode = common[0]
        bits = [t for t in parsed if t[1] and t[1] != [wnode]]
        scale = -signed(const[0][0])
        extra = [const[0]]

    assert len(bits) == N, f"expected {N} bit terms, got {len(bits)}"

    # Bit index from the coefficient, not from term order.
    inv_scale = pow(scale % P, -1, P)
    bit_of = {}
    for c, ops, _ in bits:
        b = [o for o in ops if o != wnode]
        assert len(b) == 1, f"term has operands {ops}"
        v = (c * inv_scale) % P if kind == "inv" else (-c * inv_scale) % P
        k = v.bit_length() - 1
        assert v == 1 << k and k < N, f"coefficient {hex(c)} is not a power of two"
        assert k not in bit_of, f"bit {k} appears twice"
        bit_of[k] = b[0]
    bs = [bit_of[k] for k in range(N)]

    # Expand the root over the atoms and check against `bitsLE` modulo `p`.
    atoms = {n: j for j, n in enumerate(bs + [wnode])}
    nv = len(atoms)
    V = [Poly.var(nv, j) for j in range(nv)]
    chain = Poly(nv)
    for c, ops, _ in parsed:
        t = Poly.const(nv, signed(c))
        for o in ops:
            t = t * V[atoms[o]]
        chain = chain + t
    total = Poly(nv)
    for k in range(N):
        total = total + V[k].scale(1 << k)
    goal = (V[nv - 1] - total) if kind == "eq" else (total * V[nv - 1] - Poly.const(nv, 1))
    diff = chain - goal.scale(scale)
    assert all(c % P == 0 for c in diff.terms.values()), "root is not the weighted bit sum"
    emit(d, name, kind, nodes, ins, bs, wnode, scale, diff.divide_by(P), atoms, is_one)


def emit(d, name, kind, nodes, ins, bs, wnode, scale, W, atoms, is_one):
    lean_names = [
        (f"inputs {ins[n]['input']}" if n in ins else f"interpDag dag inputs {n}")
        for n in sorted(atoms, key=atoms.get)
    ]

    kmap, lines, done, vnames = {}, [], set(atoms), []

    def walk(i):
        if i in done:
            return
        done.add(i)
        n = nodes[i]
        if "input" in n:
            lines.append(
                f"  have v{i} : interpDag dag inputs {i} = inputs {n['input']} :=\n"
                f"    interpDag_input dag inputs {i} {n['input']} (by rw [dag_len]; omega)\n"
                f"      (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]; rfl)"
            )
            vnames.append(f"v{i}")
            return
        for _, w0, w1, _ in n["sum"]:
            walk(w0)
            walk(w1)
        lit, rhs = [], "0"
        for c, w0, w1, ki in n["sum"]:
            kmap[ki] = int(c, 16)
            lit.append(f"⟨Ecdsa2.consts F {ki}, {w0}, {w1}⟩")
            rhs = (f"({rhs} + Ecdsa2.consts F {ki} * interpDag dag inputs {w0}"
                   f" * interpDag dag inputs {w1})")
        lines.append(
            f"  have h{i} : dag.getD {i} (.input 0) = .sum [{', '.join(lit)}] := by\n"
            f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
            f"(by rw [nodes_len]; omega)]\n    rfl\n"
            f"  have v{i} : interpDag dag inputs {i} = {rhs} := by\n"
            f"    rw [interpDag_sum inputs dag {i} _ h{i} (vs.sum_operands_lt {i} _ h{i})]\n"
            f"    simp only [List.foldl_cons, List.foldl_nil]"
        )
        vnames.append(f"v{i}")

    for a in sorted(atoms, key=atoms.get):
        if a in ins:
            n = nodes[a]
            lines.append(
                f"  have v{a} : interpDag dag inputs {a} = inputs {n['input']} :=\n"
                f"    interpDag_input dag inputs {a} {n['input']} (by rw [dag_len]; omega)\n"
                f"      (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]; rfl)"
            )
            vnames.append(f"v{a}")
    walk(d["root"])

    cdefs, cnames = [], []
    for k in sorted(kmap):
        v = kmap[k]
        cnames.append(f"ck{k}")
        if v <= P // 2:
            cdefs.append(f"  have ck{k} : Ecdsa2.consts F {k} = (({v} : Nat) : F) :="
                         f" consts_pos {k} {v} (by rfl)")
        else:
            cdefs.append(f"  have ck{k} : Ecdsa2.consts F {k} = -(({P - v} : Nat) : F) :="
                         f" consts_neg {k} {P - v} (by rfl) (by norm_num)")

    def atom(n):
        return (f"inputs {ins[n]['input']}" if n in ins
                else f"interpDag (raw.toDag (Ecdsa2.consts F)) inputs {n}")

    lst = "[" + ", ".join(atom(b) for b in bs) + "]"
    w = atom(wnode)
    stmt = (f"    {w} = ECDSA2.bitsLE {lst}" if kind == "eq"
            else f"    ECDSA2.bitsLE {lst} * {w} = 1")

    what = ("the witness equals the weighted sum of the 256 extracted bits"
            if kind == "eq" else "the weighted sum of the 256 extracted bits is invertible")

    print(f'''-- Generated by `formal/tools/gen_bitsum_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.EcdsaV2

set_option maxRecDepth 4000000
-- Unbounded, not merely large: `bitsLE` on a 256-element literal list is a 256-deep nesting and
-- the `linear_combination` carries 257 atoms, which overruns even 4,000,000 heartbeats. Memory
-- is still capped by `-M` in lakefile.toml, which is the limit that actually protects the box.
set_option maxHeartbeats 0

/-!
# `{name}`: {what}

The cone is 2,313 nodes, but only because each bit is a degree-7 table interpolant. The compiler
fuses the weighted sum into one 257-term root, so cutting at the 256 table outputs leaves
something {"linear" if kind == "eq" else "quadratic"} in 257 opaque atoms. What the bits *are* is
a separate, per-digit question; see the range and bit-extractor certificates.

`W` ({len(W.terms)} monomials) is the modulo-`p` correction: the chain carries `p - 2^k` where
`bitsLE` carries `-2^k`.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

private theorem hpB : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (h : interpDag (raw.toDag (Ecdsa2.consts F)) inputs {d["root"]} = 0) :
{stmt} := by
  set dag := raw.toDag (Ecdsa2.consts F) with hdag
  have vs := Ecdsa2.valid (F := F) inputs
  have dag_len : dag.length = 26939 := by
    rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len
{chr(10).join(lines)}
{chr(10).join(cdefs)}
  simp only [{", ".join(reversed(vnames))}] at h
  simp only [{", ".join(cnames)}] at h
  rw [show inputs 0 = 1 from hone] at h
  push_cast at h
  simp only [ECDSA2.bitsLE]
  linear_combination ({scale} : F) * h + ({W.scale(-scale).lean(lean_names)}) * hpB (F := F)

end Ecdsa2.Meaning''')


main()
