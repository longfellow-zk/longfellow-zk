#!/usr/bin/env python3
"""Prove that a `slicing2` assertion says what Lean's `addE` says.

Usage: gen_addE_meaning.py cone.json THEOREM_NAME COORD > out.lean
       COORD is `X` (slice_x) or `Y` (slice_y).

This is the first meaning lemma whose statement is about the *specification's* elliptic-curve
operation rather than about wires. `slicing2(w, pt)` asserts `pt.X = pt.Z * w.x`, and here `pt`
is `addE` of two affine points, so the clause is exactly one half of
`ValidPreComputationExact`'s `IsPointEquality`.

The proof is the usual chain plus one correction: the meaning chain's expansion and `addE`'s
agree only modulo `p`, so `linear_combination h + W * hp` supplies the difference. `W` is
untrusted advice -- a wrong one fails `ring` -- and is computed by expanding both sides.
"""
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, addE, expand_cone, signed  # noqa: E402

B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B


GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5


def main():
    d = json.load(open(sys.argv[1]))
    name = sys.argv[2]
    coord = sys.argv[3]

    ins = [(n["id"], n["name"], n["input"]) for n in d["nodes"] if "input" in n]
    one = next(i for i, nm, _ in ins if nm == "one")
    order = [x for x in ins if x[1] != "one"]
    atoms = {i: k for k, (i, _, _) in enumerate(order)}
    names = [nm for _, nm, _ in order]
    pos = {nm: p for _, nm, p in order}
    nv = len(names)

    chain = expand_cone(d["nodes"], d["root"], atoms, one)

    V = {nm: Poly.var(nv, k) for k, nm in enumerate(names)}
    one_p = Poly.const(nv, 1)
    a = Poly.const(nv, -3)
    k3b = Poly.const(nv, 3 * B)

    # Candidate summands. `G` is `konst` in the circuit, so it appears as constants rather than
    # as input wires; the `pre` points are the earlier slicing outputs feeding later ones.
    cands = {"G": (Poly.const(nv, GX), Poly.const(nv, GY), one_p)}
    if "pkx" in V and "pky" in V:
        cands["PK"] = (V["pkx"], V["pky"], one_p)
    if "rx" in V and "ry" in V:
        cands["R"] = (V["rx"], V["ry"], one_p)
    for j in range(4):
        xa, ya = f"pre{2 * j}", f"pre{2 * j + 1}"
        if xa in V and ya in V:
            cands[f"PRE{j}"] = (V[xa], V[ya], one_p)

    # The witness is whichever `pre` wire the assertion pins; try each.
    witnesses = [nm for nm in names if nm.startswith("pre")]
    for witness in witnesses:
        for n1, p1 in cands.items():
            for n2, p2 in cands.items():
                if n1 == n2:
                    continue
                # A point cannot be both a summand and the witness.
                if any(witness in (f"pre{2 * j}", f"pre{2 * j + 1}")
                       and f"PRE{j}" in (n1, n2) for j in range(4)):
                    continue
                X, Y, Z = addE(p1, p2, a, k3b)
                target = X if coord == "X" else Y
                for sgn in (1, -1):
                    goal = (target - Z * V[witness]).scale(sgn)
                    diff = chain - goal
                    if all(c % P == 0 for c in diff.terms.values()):
                        emit(d, name, coord, n1, n2, names, pos, witness,
                             diff.scale(-sgn).divide_by(P), sgn, cands)
                        return
    raise SystemExit(
        f"no addE orientation matches the cone mod p (vars {names}, coord {coord})"
    )


def emit(d, name, coord, n1, n2, names, pos, witness, W, sgn, cands):
    lean_names = [f"inputs {pos[nm]}" for nm in names]

    def pt(label):
        if label == "G":
            return f"(⟨({GX} : F), ({GY} : F), 1⟩ : ProjectivePoint F)"
        if label == "PK":
            return f"(⟨inputs {pos['pkx']}, inputs {pos['pky']}, 1⟩ : ProjectivePoint F)"
        if label == "R":
            return f"(⟨inputs {pos['rx']}, inputs {pos['ry']}, 1⟩ : ProjectivePoint F)"
        j = int(label[3:])
        return (f"(⟨inputs {pos[f'pre{2 * j}']}, inputs {pos[f'pre{2 * j + 1}']}, 1⟩"
                f" : ProjectivePoint F)")

    pt1, pt2 = pt(n1), pt(n2)

    chain_lines = []
    for n in d["nodes"]:
        i = n["id"]
        if "input" in n:
            chain_lines.append(
                f"  have v{i} : interpDag dag inputs {i} = inputs {n['input']} :=\n"
                f"    interpDag_input dag inputs {i} {n['input']} (by rw [dag_len]; omega)\n"
                f"      (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]; rfl)"
            )
        else:
            lit = ", ".join(f"⟨Ecdsa2.consts F {ki}, {w0}, {w1}⟩" for _, w0, w1, ki in n["sum"])
            rhs = "0"
            for _, w0, w1, ki in n["sum"]:
                rhs = (
                    f"({rhs} + Ecdsa2.consts F {ki} * interpDag dag inputs {w0}"
                    f" * interpDag dag inputs {w1})"
                )
            chain_lines.append(
                f"  have h{i} : dag.getD {i} (.input 0) = .sum [{lit}] := by\n"
                f"    rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]\n    rfl\n"
                f"  have v{i} : interpDag dag inputs {i} = {rhs} := by\n"
                f"    rw [interpDag_sum inputs dag {i} _ h{i} (vs.sum_operands_lt {i} _ h{i})]\n"
                f"    simp only [List.foldl_cons, List.foldl_nil]"
            )

    # Per-constant lemmas, not `simp only [constNat]`: unfolding a 609-case match inside the
    # hypothesis blows `maxRecDepth`.
    kmap = {}
    for n in d["nodes"]:
        for c, _, _, ki in n.get("sum", []):
            kmap[ki] = int(c, 16)
    cdefs, cnames = [], []
    for k in sorted(kmap):
        v = kmap[k]
        cnames.append(f"ck{k}")
        if v <= P // 2:
            cdefs.append(
                f"  have ck{k} : Ecdsa2.consts F {k} = (({v} : Nat) : F) :="
                f" consts_pos {k} {v} (by rfl)"
            )
        else:
            cdefs.append(
                f"  have ck{k} : Ecdsa2.consts F {k} = -(({P - v} : Nat) : F) :="
                f" consts_neg {k} {P - v} (by rfl) (by norm_num)"
            )
    rws = ", ".join(f"v{n['id']}" for n in reversed(d["nodes"]))

    print(f'''-- Generated by `formal/tools/gen_addE_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.EcdsaV2

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-!
# `slice_{coord.lower()}`: the circuit's precomputation is Lean's `addE`

The deployed assertion is `slicing2`'s `pt.{coord} = pt.Z * w`, with `pt = addE {n1} {n2}`. The
statement below is written with `ECDSA.addE` — the specification's operation, not the circuit's —
so this is the step that says the compiled circuit computes what the model says.

The expansions agree only modulo `p`, and `W` ({len(W.terms)} monomials) supplies the difference.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

theorem hp : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (params : CurveParameters F) (ha : params.a = -3) (hb : params.b = ({B} : F))
    (h : interpDag (raw.toDag (Ecdsa2.consts F)) inputs {d["root"]} = 0) :
    (addE {pt1} {pt2} params).{coord}
      = (addE {pt1} {pt2} params).Z * inputs {pos[witness]} := by
  set dag := raw.toDag (Ecdsa2.consts F) with hdag
  have vs := Ecdsa2.valid (F := F) inputs
  have dag_len : dag.length = 26939 := by
    rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len
{chr(10).join(chain_lines)}
{chr(10).join(cdefs)}
  rw [{rws}] at h
  rw [{", ".join(cnames)}] at h
  rw [show inputs 0 = 1 from hone] at h
  push_cast at h
  simp only [addE, ha, hb]
  linear_combination {"" if sgn > 0 else "-"}h + ({W.lean(lean_names)}) * hp (F := F)

end Ecdsa2.Meaning''')


main()
