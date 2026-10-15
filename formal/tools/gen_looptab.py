#!/usr/bin/env python3
"""Emit `looptab.json` and `chain.json`, the two tables `gen_loop_ok.py` assembles from.

Usage: gen_looptab.py SCRATCH [--artifact Ecdsa2]

Both were read by `gen_loop_ok.py` and written by nothing in the repo, so the loop bridge could
not be rebuilt from a fresh circuit -- the same defect as `wordtbl.pkl` (a dead load) and
`asserttbl.pkl` (committed and stale until `gen_asserttbl.py`).

`looptab.json`  `{"<coord>_<round>": {"out": <input position>, "aidx": <assertion index>}}`
`chain.json`    the 256 rounds in accumulation order, infinity first

Nothing here is assumed that can be read instead:

* **`out`** is parsed from the round lemma's own conclusion (`… = inputs N`), which is the
  statement `gen_loop_ok` has to chain, so a disagreement with the layout is a real conflict
  rather than a convention mismatch.  It is then cross-checked against `intx/inty/intz` at the
  round's index, and the check is reported, not silently enforced.

* **`aidx`** is the position of the cone's root in `asserts_0 ++ … ++ asserts_4`, read from
  `Gen/<artifact>/<artifact>Asserts*.lean` in shard order.  `gen_loop_ok.CHUNKS` records the
  shard sizes it expects; this asserts the real ones match, since an off-by-one there would
  silently discharge a lemma against the wrong assertion name.

* **`chain`** is derived by data dependency, following `gen_loop_ok`'s own description: each
  round's cone reads the accumulator of its predecessor, so the round whose cone reads no other
  round's accumulator is the one starting from infinity, and the rest form a single path.  It
  comes out as 255, 254, … 0, matching the `255 - j` convention in `gen_final.py` -- but it is
  derived, so a renumbering breaks the chain instead of quietly reordering it.
"""
import argparse, glob, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
COORDS = ("x", "y", "z")
ACC = {"x": "intx", "y": "inty", "z": "intz"}


def asserts_in_order(artifact):
    """Assertion roots, concatenated in shard order -- the indexing `aidx` means."""
    gen = os.path.join(ROOT, "circuits", "quadcert", "Gen", artifact)
    shards = {}
    for f in glob.glob(os.path.join(gen, f"{artifact}Asserts*.lean")):
        s = open(f).read()
        m = re.search(r'def asserts_(\d+) : List RawAssert :=\s*\n\s*\[(.*)\]', s, re.S)
        if not m:
            continue
        shards[int(m.group(1))] = [int(a) for a, _, _ in
                                   re.findall(r'⟨(\d+),\s*(\d+),\s*(\d+)⟩', m.group(2))]
    if not shards:
        raise SystemExit(f"no asserts shards under {gen}; run tools/regen_artifact.sh first")
    sizes = [len(shards[i]) for i in sorted(shards)]
    out = [r for i in sorted(shards) for r in shards[i]]
    return out, sizes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("scratch")
    ap.add_argument("--artifact", default="Ecdsa2")
    a = ap.parse_args()
    S = a.scratch

    roots, sizes = asserts_in_order(a.artifact)
    aidx_of = {r: i for i, r in enumerate(roots)}
    # Read `CHUNKS` out of the source rather than importing it: `gen_loop_ok.py` calls `main()`
    # at module level, so an import would run the assembler with this script's argv.
    gl = open(os.path.join(HERE, "gen_loop_ok.py")).read()
    CHUNKS = [int(x) for x in
              re.search(r'^CHUNKS = \[([0-9, ]+)\]', gl, re.M).group(1).split(",")]
    if sizes != CHUNKS:
        raise SystemExit(f"assert shard sizes {sizes} != gen_loop_ok.CHUNKS {CHUNKS}; "
                         f"update CHUNKS, or the lemma names it destructures will be wrong")

    if not glob.glob(f"{S}/cones/slice_w*.json") or not glob.glob(f"{S}/loops/w*.lean"):
        raise SystemExit(
            f"{S} has no cones/ and loops/ to read.\n"
            f"\nPopulate it first -- one cone dump, then a lemma per round:\n"
            f"\n    tools/gen_all_loops.sh {S} <path to ecdsa2.sidecar>\n")

    tab, reads, mismatch = {}, {}, []
    for c in COORDS:
        for i in range(256):
            cone = json.load(open(f"{S}/cones/slice_w{c}_{i}.json"))
            lemma = open(f"{S}/loops/w{c}_{i}.lean").read()

            m = re.search(r'=\s*inputs\s+(\d+)\s*:=\s*by', lemma)
            if not m:
                raise SystemExit(f"w{c}_{i}.lean: no `= inputs N := by` conclusion to read")
            out = int(m.group(1))

            root = cone["root"]
            if root not in aidx_of:
                raise SystemExit(f"slice_w{c}_{i}: root {root} is not an assertion of {a.artifact}")
            tab[f"{c}_{i}"] = {"out": out, "aidx": aidx_of[root]}

            # Every `int{x,y,z}` index this cone touches: its own output and its predecessor's.
            seen = {int(g.group(1)) for n in cone["nodes"] if "input" in n
                    for g in [re.fullmatch(ACC[c] + r'(\d+)', n["name"])] if g}
            if out not in {274 + 3 * i, 275 + 3 * i, 276 + 3 * i}:
                mismatch.append((c, i, out))
            reads.setdefault(i, set()).update(seen - {i})

    # Derive the chain: the round reading no other round's accumulator starts from infinity.
    pred = {i: (sorted(p)[0] if len(p) == 1 else None) for i, p in reads.items()}
    heads = [i for i, p in pred.items() if p is None and not reads[i]]
    if len(heads) != 1:
        raise SystemExit(f"expected exactly one round with no predecessor, got {heads}")
    nxt = {}
    for i, p in pred.items():
        if p is not None:
            nxt.setdefault(p, []).append(i)
    chain, cur = [heads[0]], heads[0]
    while cur in nxt:
        succ = nxt[cur]
        if len(succ) != 1:
            raise SystemExit(f"round {cur} feeds {succ}; the chain is not a path")
        cur = succ[0]
        chain.append(cur)
    if sorted(chain) != list(range(256)):
        raise SystemExit(f"chain covers {len(set(chain))} of 256 rounds")

    json.dump(tab, open(f"{S}/looptab.json", "w"))
    json.dump(chain, open(f"{S}/chain.json", "w"))
    print(f"looptab.json: {len(tab)} entries over {len(roots)} assertions {sizes}")
    print(f"chain.json:   {chain[:3]} … {chain[-3:]}  "
          f"({'matches the 255-j convention' if chain == list(range(255, -1, -1)) else 'NOT 255..0'})")
    if mismatch:
        print(f"note: {len(mismatch)} rounds whose `out` is not their own accumulator slot, "
              f"first {mismatch[:3]}")


if __name__ == "__main__":
    main()
