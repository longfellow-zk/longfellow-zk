#!/usr/bin/env python3
"""Prove that a round's three table-output wires *are* `optPoint` of that round's digit.

Usage: gen_mux_meaning.py cones.jsonl THEOREM_NAME > out.lean

`cones.jsonl` is what `DUMP_NODE=x,y,z meaning_gen` prints: the X, Y and Z cones of one round's
mux, one JSON object per line, in that order.

This is the lemma class every remaining bridge waits on. The loop-round lemmas
(`gen_loop_meaning.py`) deliberately stop at the mux boundary and leave the three table outputs
as opaque `interpDag` atoms -- that cut is what keeps `ring` inside 12 GB. Nothing said what
those atoms *are*, so `LoopFull`, whose second summand is `optPoint u pk rx ry pre params`,
could not be reached.

Unlike the loop cones, these expand outright: 50 monomials for X and Y, 5 for Z. The table is a
degree-7 interpolant over the eight encoded digit nodes `-8, -6, …, 6`, so once `IsDigit u` picks
a node the polynomial collapses to a single atom (or to a constant -- G is not an input, it is
compiled in). Measured, on round 0:

    u = -8  ->  (0, 1, 0)          u = 0  ->  (gx, gy, 1)
    u = -6  ->  (rx, ry, 1)        u = 2  ->  (pre2, pre3, 1)
    u = -4  ->  (pkx, pky, 1)      u = 4  ->  (pre0, pre1, 1)
    u = -2  ->  (pre4, pre5, 1)    u = 6  ->  (pre6, pre7, 1)

which is `optPoint` on the nose.

**The digit association is read off the cone, not carried in.** Each mux cone reads exactly one
`ers*` input, and the layout names it, so the wire -> digit link is recovered here rather than
threaded through from whatever found the wire. That is deliberate: the same association went
missing once before, when a sidecar was built from the pre-segmentation circuit and every
`k_index` silently referred to a different constant table.

The statement is at the *point* level rather than per coordinate, because that is the shape
`LoopFull` consumes -- the loop lemma's second summand is literally the triple of these three
`interpDag` terms, so assembly is one rewrite rather than three.
"""
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, signed  # noqa: E402

# P-256, as `Curves.lean` records it. Supplied to the lemma as hypotheses `hgx`/`hgy` rather
# than baked in, so the statement stays over an abstract `params`.
GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

NODES = [-8, -6, -4, -2, 0, 2, 4, 6]


def main():
    cones = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    name = sys.argv[2]
    assert len(cones) == 3, f"expected the X, Y and Z cones, got {len(cones)}"

    nodes, ins = {}, {}
    for d in cones:
        for n in d["nodes"]:
            nodes[n["id"]] = n
            if "input" in n:
                ins[n["id"]] = n["name"]
    pos = {n["id"]: n["input"] for d in cones for n in d["nodes"] if "input" in n}

    one = next(i for i, nm in ins.items() if nm == "one")
    digs = {i for i, nm in ins.items() if nm.startswith("ers")}
    assert len(digs) == 1, f"expected exactly one digit input in the cones, got {sorted(digs)}"
    dig = digs.pop()
    vals = sorted(i for i in ins if i not in (one, dig))

    atomlist = [dig] + vals
    atoms = {n: k for k, n in enumerate(atomlist)}
    nv = len(atomlist)

    val = {}

    def ev(i):
        if i in val:
            return val[i]
        if i in atoms:
            r = Poly.var(nv, atoms[i])
        elif i == one:
            r = Poly.const(nv, 1)
        else:
            assert "sum" in nodes[i], f"input node {i} is neither an atom nor `one`"
            r = Poly(nv)
            for c, w0, w1, _ in nodes[i]["sum"]:
                r = r + Poly.const(nv, signed(int(c, 16))) * ev(w0) * ev(w1)
        val[i] = r
        return r

    chains = [ev(d["root"]) for d in cones]

    # Value atoms keep their variable index; the digit's slot is dead after substitution, so the
    # names list just needs a placeholder there.
    names = ["<digit>"] + [f"inputs {pos[a]}" for a in vals]

    # `pre`'s index in `optPoint` is the layout offset from `pre0` at position 266.
    p0 = min((pos[a] for a in vals if ins[a].startswith("pre")), default=266)

    def target(coord, k):
        """`(optPoint node_k …).coord` as (rewrite lemmas, integer polynomial)."""
        u = NODES[k]
        if coord == 2:
            return ([], Poly.const(nv, 0 if u == -8 else 1))
        pt = f"ECDSA2.optPoint_n{k}"
        if u == -8:
            return ([pt], Poly.const(nv, 0 if coord == 0 else 1))
        if u == 0:
            return ([pt, "hgx" if coord == 0 else "hgy"],
                    Poly.const(nv, GX if coord == 0 else GY))
        nm = {-6: ("rx", "ry"), -4: ("pkx", "pky"), -2: ("pre4", "pre5"),
              2: ("pre2", "pre3"), 4: ("pre0", "pre1"), 6: ("pre6", "pre7")}[u][coord]
        a = next(i for i in vals if ins[i] == nm)
        hyp = ({"rx": "hrx", "ry": "hry", "pkx": "hpkx", "pky": "hpky"}.get(nm)
               or f"hq{pos[a] - p0}")
        return ([pt, hyp], Poly.var(nv, atoms[a]))

    # `W` per node, per coordinate: the chain's integer expansion minus the goal's, over `p`.
    branches = []
    for k, u in enumerate(NODES):
        parts = []
        for coord in range(3):
            sub = {}
            for m, c in chains[coord].terms.items():
                cc = c * (u ** m[0])
                key = (0,) + m[1:]
                sub[key] = sub.get(key, 0) + cc
            chain_u = Poly(nv, {m: c for m, c in sub.items() if c})
            rw, tgt = target(coord, k)
            diff = chain_u - tgt
            bad = [c for c in diff.terms.values() if c % P != 0]
            if bad:
                raise SystemExit(
                    f"{name}: node {u}, coordinate {coord} does not match `optPoint` "
                    f"(residual {bad[0] % P})")
            parts.append((rw, diff.divide_by(P)))
        branches.append(parts)

    emit(cones, name, nodes, ins, pos, atomlist, one, dig, vals, p0, branches, names)


def emit(cones, name, nodes, ins, pos, atomlist, one, dig, vals, p0, branches, names):
    kmap = {}
    lines, done, vnames = [], set(), []

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

    for d in cones:
        walk(d["root"])

    rws = ", ".join(reversed(vnames))
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

    # Only the hypotheses this round's branches actually rewrite with, so the linter stays quiet.
    used = {h for parts in branches for rw, _ in parts for h in rw if not h.startswith("ECDSA2.")}
    hyps = []
    if "hgx" in used:
        hyps.append(f"(hgx : params.gx = (({GX} : Nat) : F))")
    if "hgy" in used:
        hyps.append(f"(hgy : params.gy = (({GY} : Nat) : F))")
    for h, e in (("hpkx", "pk.X"), ("hpky", "pk.Y"), ("hrx", "rx"), ("hry", "ry")):
        if h in used:
            src = {"hpkx": 1, "hpky": 2, "hrx": 4, "hry": 5}[h]
            hyps.append(f"({h} : {e} = inputs {src})")
    for j in range(8):
        if f"hq{j}" in used:
            hyps.append(f"(hq{j} : pre.getD {j} 0 = inputs {p0 + j})")

    pt = ",\n      ".join(
        f"interpDag (raw.toDag (Ecdsa2.consts F)) inputs {d['root']}" for d in cones)

    body = []
    for k, parts in enumerate(branches):
        rw = sorted({h for r, _ in parts for h in r})
        body.append(f"  · rw [hd{(', ' + ', '.join(rw)) if rw else ''}]\n"
                    f"    simp only [ProjectivePoint.mk.injEq]\n"
                    f"    refine ⟨?_, ?_, ?_⟩")
        for _, W in parts:
            body.append(f"    · linear_combination ({W.lean(names)}) * hpM (F := F)")

    print(f'''-- Generated by `formal/tools/gen_mux_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.EcdsaV2

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-!
# One round's table lookup: the mux wires are `optPoint` of the digit

The loop-round lemmas stop at these three wires. This says what they hold: the degree-7
interpolant, evaluated at whichever of the eight encoded nodes `IsDigit` allows, is the
corresponding entry of the Rust `opts` table. `hpM` supplies the modulo-`p` correction, which
`ring` cannot find on its own because the chain expands the circuit's residues over `ℤ`.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

private theorem hpM : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (pk : AffinePoint F) (rx ry : F) (pre : List F) (params : CurveParameters F)
    {" ".join(hyps)}
    (hd : ECDSA2.IsDigit (inputs {pos[dig]})) :
    (⟨{pt}⟩ : ProjectivePoint F)
      = ECDSA2.optPoint (inputs {pos[dig]}) pk rx ry pre params := by
  set dag := raw.toDag (Ecdsa2.consts F) with hdag
  have vs := Ecdsa2.valid (F := F) inputs
  have dag_len : dag.length = 26939 := by
    rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len
{chr(10).join(lines)}
{chr(10).join(cdefs)}
  rw [{rws}]
  rw [{", ".join(cnames)}]
  simp only [show inputs 0 = 1 from hone]
  push_cast
  rcases hd with hd|hd|hd|hd|hd|hd|hd|hd
{chr(10).join(body)}

end Ecdsa2.Meaning''')


main()
