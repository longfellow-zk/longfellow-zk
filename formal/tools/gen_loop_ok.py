#!/usr/bin/env python3
"""Assemble the round and mux lemmas into `LoopFull` -- the `hloop` bridge.

Usage: gen_loop_ok.py SCRATCH THEOREM_NAME [NROUNDS] > out.lean

`NROUNDS` builds only the last `NROUNDS` steps of the chain (a valid `LoopFull` in its own
right, starting from that point's stored accumulator). It exists to test the composition on
three rounds before paying for 256.

Three facts are read out of the generated artifacts rather than assumed:

* the **chain order** is derived by following each round's output triple to the next round's
  accumulator, starting from the one round whose accumulator is the constant `(0, 1, 0)`. It
  comes out as 255, 254, …, 0 -- but it is derived, so a mis-numbered lemma would break the
  chain rather than silently produce a wrong ordering;
* the **assertion index** of each round lemma is checked against the sidecar's asserted node;
* each mux lemma's **hypothesis list** is read from its own generated signature, since
  `gen_mux_meaning.py` emits only the ones that round's branches use.

The chain is one nested term, not 256 `have`s. Naming the intermediates would force Lean to
elaborate 256 `LoopFull` types whose list arguments grow, which is quadratic; leaving them
implicit lets unification peel one `cons` at a time.
"""
import json
import re
import sys

B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

# `raw.asserts = asserts_0 ++ … ++ asserts_4`; a lemma about assertion `i` is discharged by
# the `j`-th name of chunk `c`, so the bridge destructures each chunk once.
CHUNKS = [198, 196, 196, 240, 218]


def chunk_of(i):
    off = 0
    for c, n in enumerate(CHUNKS):
        if i < off + n:
            return c, i - off
        off += n
    raise AssertionError(f"assertion {i} past the end")


def main():
    S, name = sys.argv[1], sys.argv[2]
    nrounds = int(sys.argv[3]) if len(sys.argv) > 3 else 256

    tab = json.load(open(S + "/looptab.json"))
    chain = json.load(open(S + "/chain.json"))
    assert len(chain) == 256

    rounds = {}
    for k, v in tab.items():
        c, i = k.split("_")
        rounds.setdefault(int(i), {})[c] = v

    # Each mux lemma's own signature, in order, minus the leading fixed arguments.
    muxargs, muxdig = {}, {}
    for i in range(256):
        src = open(f"{S}/muxes/mux_{i}.lean").read()
        sig = src[src.index(f"theorem mux_{i} "):src.index(":= by", src.index(f"theorem mux_{i} "))]
        muxargs[i] = re.findall(r"\((h(?:gx|gy|pkx|pky|rx|ry|q\d)) :", sig)
        muxdig[i] = int(re.search(r"IsDigit \(inputs (\d+)\)", sig).group(1))

    seg = chain[len(chain) - nrounds:]
    first_is_infinity = seg[0] == chain[0]

    def out(i, c):
        return rounds[i][c]["out"]

    # The accumulator the segment starts from.
    if first_is_infinity:
        start = "infinityPoint"
    else:
        prev = chain[chain.index(seg[0]) - 1]
        start = (f"(⟨inputs {out(prev, 'x')}, inputs {out(prev, 'y')}, "
                 f"inputs {out(prev, 'z')}⟩ : ProjectivePoint F)")

    us = ", ".join(f"inputs {muxdig[i]}" for i in seg)
    ws = {c: ", ".join(f"inputs {out(i, c)}" for i in seg) for c in "xyz"}

    # Assertion names, per chunk, that this segment consumes.
    need = set()
    for i in seg:
        for c in "xyz":
            need.add(rounds[i][c]["aidx"])
    used_chunks = sorted({chunk_of(i)[0] for i in need})

    lines = []
    lines.append(f"  obtain ⟨{', '.join(f'hd{k}' for k in range(256))}⟩ :="
                 f" digits_tuple inputs hone hacc")
    lines.append("  have H := Ecdsa2.assertions_zero inputs hacc")
    lines.append("  simp only [RawCircuit.toRecs, List.forall_mem_map,\n"
                 "    show (raw.asserts) = asserts_0 ++ asserts_1 ++ asserts_2 ++ asserts_3"
                 " ++ asserts_4 from rfl,\n    List.forall_mem_append] at H")
    lines.append("  obtain ⟨⟨⟨⟨H0, H1⟩, H2⟩, H3⟩, H4⟩ := H")
    for c in used_chunks:
        lines.append(f"  simp only [asserts_{c}, List.forall_mem_cons,"
                     f" List.forall_mem_nil] at H{c}")
        names = ", ".join(f"c{c}_{j}" for j in range(CHUNKS[c]))
        lines.append(f"  obtain ⟨{names}, -⟩ := H{c}")

    for i in seg:
        margs = " ".join(muxargs[i])
        d = muxdig[i] - 6
        lines.append(f"  have m{i} := mux_{i} inputs hone pk rx ry pre params"
                     f"{' ' + margs if margs else ''} hd{d}")
        for c in "xyz":
            ci, cj = chunk_of(rounds[i][c]["aidx"])
            lines.append(f"  have {c}{i} := loop_w{c}_{i} inputs hone params ha hb c{ci}_{cj}")
        lines.append(f"  rw [m{i}] at x{i} y{i} z{i}")

    term = "(ECDSA2.LoopFull.nil _ _ pk rx ry pre params)"
    for n, i in enumerate(reversed(seg)):
        rule = ("ECDSA2.LoopFull.cons_first" if (first_is_infinity and n == len(seg) - 1)
                else "ECDSA2.LoopFull.cons_step")
        holes = "_ " * (8 if rule.endswith("first") else 9)
        term = (f"({rule} {holes}pk rx ry pre params\n"
                f"      x{i} y{i} z{i} {term})")
    lines.append(f"  exact {term}")

    imports = "\n".join(
        [f"import quadcert.Gen.E2.E2LoopB{k:02d}" for k in range(96)]
        + [f"import quadcert.Gen.E2.E2MuxM{k:02d}" for k in range(16)]
        + ["import quadcert.Bridge.Ecdsa2.E2Digits", "import ECDSA.LoopAssembly"])

    print(f'''-- Generated by `formal/tools/gen_loop_ok.py`. Do not edit.
{imports}

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-!
# `hloop`: the circuit's {len(seg)} stored accumulators are the specification's ladder

`soundness_of_v2`'s third bridge. The round lemmas say each stored triple is
`addE (doubleE acc) mux`; the mux lemmas say that `mux` is `optPoint` of the round's digit;
`LoopFull` is the two composed, threaded through the accumulator.

The order is not assumed: it is recovered by following each round's output triple to the round
that consumes it, from the one round whose accumulator is the constant point at infinity.
-/

namespace Ecdsa2.Assembly

open Quadcert Quadcert.Gen.Ecdsa2 Ecdsa2.Meaning ECDSA2

variable {{F : Type}} [Field F] [CharP F p256]

theorem {name} (inputs : Nat → F) (hone : inputs 0 = 1)
    (pk : AffinePoint F) (rx ry : F) (pre : List F) (params : CurveParameters F)
    (ha : params.a = -3) (hb : params.b = ({B} : F))
    (hgx : params.gx = (({GX} : Nat) : F))
    (hgy : params.gy = (({GY} : Nat) : F))
    (hpkx : pk.X = inputs 1) (hpky : pk.Y = inputs 2)
    (hrx : rx = inputs 4) (hry : ry = inputs 5)
    (hq0 : pre.getD 0 0 = inputs 266) (hq1 : pre.getD 1 0 = inputs 267)
    (hq2 : pre.getD 2 0 = inputs 268) (hq3 : pre.getD 3 0 = inputs 269)
    (hq4 : pre.getD 4 0 = inputs 270) (hq5 : pre.getD 5 0 = inputs 271)
    (hq6 : pre.getD 6 0 = inputs 272) (hq7 : pre.getD 7 0 = inputs 273)
    (hacc : Accepts (Ecdsa2.circuit F) inputs) :
    ECDSA2.LoopFull {start} {"true" if first_is_infinity else "false"}
      [{us}]
      [{ws["x"]}]
      [{ws["y"]}]
      [{ws["z"]}]
      pk rx ry pre params := by
{chr(10).join(lines)}

end Ecdsa2.Assembly''')


main()
