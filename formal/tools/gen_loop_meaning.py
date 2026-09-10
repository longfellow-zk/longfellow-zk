#!/usr/bin/env python3
"""Prove that a loop-round assertion says what `addE (doubleE acc) mux` says.

Usage: gen_loop_meaning.py cone.json THEOREM_NAME COORD > out.lean

The 768 `slice_wx` / `slice_wy` / `slice_wz` assertions are `EcdsaLoopConstraintsF`. Each says
`round[i] = addE (double round[i+1]) (table[ers[i]])` in one coordinate.

Expanding such a cone down to input wires does not work -- 118 nodes over 18 variables, and the
degree-7 table interpolant multiplies through; measured, `ring` needed more than 12 GB. The cut
that does work is the **mux boundary**: keep the three table outputs as opaque atoms, so the
polynomial is over the accumulator, the witness and those three. That is 88 monomials of degree
10, which `ring` handles.

Finding the boundary is the fiddly part and is done by search, because two things obscure it:

* `copy.rs` inserts identity nodes for depth alignment, so a value appears under several ids and
  treating them as independent variables makes the match impossible;
* the circuit precomputes RCB's `(X+Y)`, `(Y+Z)`, `(X+Z)` sums, so the *sums* sit on the
  boundary while the coordinates themselves do not.

So: try each ordered triple of boundary candidates as the mux, expand everything else, and
reject the triple if expansion reaches a stray input. The surviving triple is checked against
`addE (doubleE acc) mux` modulo `p`, which is the real test -- a wrong guess simply fails.
"""
import itertools
import json
import os
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, addE, doubleE, signed  # noqa: E402

B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B


class Stray(Exception):
    pass


def main():
    d = json.load(open(sys.argv[1]))
    name, coord = sys.argv[2], sys.argv[3]
    nodes = {n["id"]: n for n in d["nodes"]}
    ins = {n["id"]: n["name"] for n in d["nodes"] if "input" in n}
    pos = {n["name"]: n["input"] for n in d["nodes"] if "input" in n}
    byname = {nm: i for i, nm in ins.items()}
    one = byname["one"]

    # The accumulator is round i+1, the witness round i; the layout names carry the index.
    accnames = sorted(nm for nm in byname if nm.startswith(("intx", "inty", "intz")))
    rounds = sorted({int(nm[4:]) for nm in accnames})
    # Round 255 is processed first, with `p = ec.zero() = (0, 1, 0)` — a constant, not wires.
    # Its cone therefore mentions only its own round.
    if len(rounds) == 1:
        lo = hi = rounds[0]
        acc = None
    else:
        assert len(rounds) == 2, f"expected one or two rounds in the cone, got {rounds}"
        lo, hi = rounds
        acc = [byname[f"int{c}{hi}"] for c in "xyz"]
    wit = byname[f"int{coord[-1].lower()}{lo}"]

    memo = {}

    def sub(n):
        if n in memo:
            return memo[n]
        r = {n}
        if "sum" in nodes[n]:
            for _, w0, w1, _ in nodes[n]["sum"]:
                r |= sub(w0)
                r |= sub(w1)
        memo[n] = r
        return r

    accset = set(acc or [])
    touches = lambda n: bool(sub(n) & accset)  # noqa: E731
    if acc is None:
        # With a constant accumulator there is nothing to separate the table from, so the
        # boundary criterion does not apply. `addE (doubleE (0,1,0)) mux` is only degree two in
        # the mux, so its operands sit within two levels of the root; search there.
        near = set()
        frontier = [d["root"]]
        for _ in range(3):
            nxt = []
            for i in frontier:
                for _, w0, w1, _ in nodes[i].get("sum", []):
                    near.add(w0)
                    near.add(w1)
                    nxt += [w0, w1]
            frontier = nxt
        boundary = sorted(near - {one} - {wit})
    else:
        boundary = sorted(
            {
                w
                for n in d["nodes"]
                if "sum" in n and touches(n["id"])
                for _, w0, w1, _ in n["sum"]
                for w in (w0, w1)
                if not touches(w)
            }
            - {one}
        )

    def expand(mux):
        atomlist = (acc or []) + [wit] + list(mux)
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
            elif "sum" not in nodes[i]:
                raise Stray(i)
            else:
                r = Poly(nv)
                for c, w0, w1, _ in nodes[i]["sum"]:
                    r = r + Poly.const(nv, signed(int(c, 16))) * ev(w0) * ev(w1)
            val[i] = r
            return r

        return ev(d["root"]), nv

    # With a constant accumulator the coordinates are `(mx*my, my^2, mz*my)`; `mx*my` is
    # symmetric, so X on its own cannot order the pair and the three coordinates can land on
    # different orderings of the same point. `MUX=` forces one triple for all three.
    forced = os.environ.get("MUX")
    cands = ([tuple(int(x) for x in forced.split(","))] if forced
             else itertools.permutations(boundary, 3))
    for mux in cands:
        try:
            chain, nv = expand(mux)
        except Stray:
            continue
        V = [Poly.var(nv, k) for k in range(nv)]
        a = Poly.const(nv, -3)
        k3b = Poly.const(nv, 3 * B)
        if acc is None:
            base = (Poly.const(nv, 0), Poly.const(nv, 1), Poly.const(nv, 0))
            wI, mI = 0, 1
        else:
            base = (V[0], V[1], V[2])
            wI, mI = 3, 4
        dbl = doubleE(base, a, k3b)
        X, Y, Z = addE(dbl, (V[mI], V[mI + 1], V[mI + 2]), a, k3b)
        target = {"X": X, "Y": Y, "Z": Z}[coord[-1].upper()]
        for sgn in (1, -1):
            diff = chain - (target - V[wI]).scale(sgn)
            if all(c % P == 0 for c in diff.terms.values()):
                emit(d, name, coord, acc, wit, mux, pos, ins,
                     diff.scale(-sgn).divide_by(P), sgn, nv)
                return
    raise SystemExit(f"no mux triple among {boundary} matches (coord {coord})")


def emit(d, name, coord, acc, wit, mux, pos, ins, W, sgn, nv):
    nodes = {n["id"]: n for n in d["nodes"]}
    atomlist = (acc or []) + [wit] + list(mux)
    lean_names = [
        f"inputs {ins_pos(ins, pos, n)}" if n in ins else f"interpDag dag inputs {n}"
        for n in atomlist
    ]
    kmap = {}
    lines, done, vnames = [], set(), []

    def walk(i):
        if i in done or i in atomlist:
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

    for i in atomlist:
        if i in ins:
            n = nodes[i]
            lines.append(
                f"  have v{i} : interpDag dag inputs {i} = inputs {n['input']} :=\n"
                f"    interpDag_input dag inputs {i} {n['input']} (by rw [dag_len]; omega)\n"
                f"      (by rw [toDag_getD_fn raw (Ecdsa2.consts F) nodeFn nodefn_ok "
                f"(by rw [nodes_len]; omega)]; rfl)"
            )
            vnames.append(f"v{i}")
            done.add(i)
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

    accL = ("(0 : F), (1 : F), (0 : F)" if acc is None
            else ", ".join(f"inputs {nodes[i]['input']}" for i in acc))
    muxL = ", ".join(
        f"interpDag (raw.toDag (Ecdsa2.consts F)) inputs {m}" for m in mux)
    C = coord[-1].upper()
    print(f'''-- Generated by `formal/tools/gen_loop_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.EcdsaV2

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-!
# One loop round: the circuit's accumulator step is `addE (doubleE ·) ·`

The table outputs stay opaque — expanding them multiplies a degree-7 interpolant through an
already large polynomial, which does not fit. `W` ({len(W.terms)} monomials) is the modulo-`p`
correction between the chain's integer expansion and `addE`'s.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

theorem hpL : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (params : CurveParameters F) (ha : params.a = -3) (hb : params.b = ({B} : F))
    (h : interpDag (raw.toDag (Ecdsa2.consts F)) inputs {d["root"]} = 0) :
    (addE (doubleE (⟨{accL}⟩ : ProjectivePoint F) params)
        (⟨{muxL}⟩ : ProjectivePoint F) params).{C}
      = inputs {nodes[wit]["input"]} := by
  set dag := raw.toDag (Ecdsa2.consts F) with hdag
  have vs := Ecdsa2.valid (F := F) inputs
  have dag_len : dag.length = 26939 := by
    rw [hdag]; simp only [RawCircuit.toDag, List.length_map]; exact nodes_len
{chr(10).join(lines)}
{chr(10).join(cdefs)}
  rw [{rws}] at h
  rw [{", ".join(cnames)}] at h
  rw [show inputs 0 = 1 from hone] at h
  push_cast at h
  simp only [addE, doubleE, ha, hb]
  linear_combination {"" if sgn > 0 else "-"}h + ({W.lean(lean_names)}) * hpL (F := F)

end Ecdsa2.Meaning''')


def ins_pos(ins, pos, n):
    return pos[ins[n]]


main()
