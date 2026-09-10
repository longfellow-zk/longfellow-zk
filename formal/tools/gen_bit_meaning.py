#!/usr/bin/env python3
"""Prove that a round's three bit-table wires are the digit's `e`, `r` and `s` bits.

Usage: gen_bit_meaning.py cones.jsonl THEOREM_NAME > out.lean

`cones.jsonl` is `DUMP_NODE=e,r,s meaning_gen` output: the three bit wires of one round, in
`e, r, s` order, one JSON object per line.

The companion of `gen_mux_meaning.py`, and the other half of what the CSE cut deferred. The
bit-sum lemmas (`E2BitSumE`, `E2BitSumRx`, `E2BitSumNms`) prove `e = bitsLE [b₀ … b₂₅₅]` with
the `bₖ` opaque; this says what each `bₖ` is.

Each cone is 12 nodes and reads exactly one `ers` input, so the digit association is recovered
here rather than threaded in. Measured, at the eight encoded nodes `-8 … 6`:

    e-bits  ->  0 0 0 0 1 1 1 1     the high bit of `d`
    r-bits  ->  0 0 1 1 0 0 1 1     the middle bit
    s-bits  ->  0 1 0 1 0 1 0 1     the low bit

which is `circuit.rs`'s `d = 4e + 2r + s`, and `ECDSA2.digitBit` is the specification's name for
the same three bits (via `muxE`/`muxR`/`muxS` of `val3 (bitrev3 u)`).
"""
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from conepoly import Poly, P, signed  # noqa: E402

NODES = [-8, -6, -4, -2, 0, 2, 4, 6]
SEL = [("E", 1), ("R", 2), ("S", 4)]
REV = [0, 4, 2, 6, 1, 5, 3, 7]


def main():
    cones = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    name = sys.argv[2]
    assert len(cones) == 3, f"expected the e, r and s cones, got {len(cones)}"

    nodes, ins = {}, {}
    for d in cones:
        for n in d["nodes"]:
            nodes[n["id"]] = n
            if "input" in n:
                ins[n["id"]] = n["name"]
    pos = {n["id"]: n["input"] for d in cones for n in d["nodes"] if "input" in n}

    one = next(i for i, nm in ins.items() if nm == "one")
    digs = {i for i, nm in ins.items() if nm.startswith("ers")}
    assert len(digs) == 1, f"expected one digit input across the three cones, got {sorted(digs)}"
    dig = digs.pop()
    stray = [i for i in ins if i not in (one, dig)]
    assert not stray, f"bit cone reads unexpected inputs {[ins[i] for i in stray]}"

    val = {}

    def ev(i):
        if i in val:
            return val[i]
        if i == dig:
            r = Poly.var(1, 0)
        elif i == one:
            r = Poly.const(1, 1)
        else:
            r = Poly(1)
            for c, w0, w1, _ in nodes[i]["sum"]:
                r = r + Poly.const(1, signed(int(c, 16))) * ev(w0) * ev(w1)
        val[i] = r
        return r

    chains = [ev(d["root"]) for d in cones]

    branches = []
    for k, u in enumerate(NODES):
        parts = []
        for c, (_tag, sel) in enumerate(SEL):
            at_u = sum(co * (u ** m[0]) for m, co in chains[c].terms.items())
            want = (REV[k] // sel) % 2
            diff = at_u - want
            if diff % P != 0:
                raise SystemExit(
                    f"{name}: node {u}, table {_tag} gives {at_u % P}, expected {want}")
            parts.append(diff // P)
        branches.append(parts)

    emit(cones, name, nodes, ins, pos, one, dig, branches)


def emit(cones, name, nodes, ins, pos, one, dig, branches):
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

    u = f"inputs {pos[dig]}"
    concl = " ∧\n      ".join(
        f"interpDag (raw.toDag (Ecdsa2.consts F)) inputs {d['root']}"
        f" = ECDSA2.digitBit {sel} ({u})"
        for d, (_t, sel) in zip(cones, SEL))

    body = []
    for k, parts in enumerate(branches):
        rw = ", ".join(f"ECDSA2.digitBit_{t}_n{k}" for t, _ in SEL)
        body.append(f"  · rw [hd, {rw}]\n    refine ⟨?_, ?_, ?_⟩")
        for W in parts:
            lit = f"({W} : F)" if W >= 0 else f"(-{-W} : F)"
            body.append(f"    · linear_combination {lit} * hpB (F := F)")

    print(f'''-- Generated by `formal/tools/gen_bit_meaning.py`. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Meaning
import ECDSA.BitTable

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-!
# One round's bit tables

The three wires the `e_eq`, `rx_eq` and `nmsinv` bit-sums leave opaque, identified with the
digit's `e`, `r` and `s` bits.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

variable {{F : Type}} [Field F] [CharP F p256]

private theorem hpB : ({P} : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F {P}

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (hd : ECDSA2.IsDigit ({u})) :
    {concl} := by
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
