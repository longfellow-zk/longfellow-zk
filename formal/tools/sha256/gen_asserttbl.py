"""Build `asserttbl.pkl`, the flat assertion table the `S2Flat`/`S2Assert`/`S2Bytes` emitters read.

This producer was missing from the repo: `emit_flat.py`, `emit_assert.py` and `emit_bytes.py`
all load `asserttbl.pkl`, but nothing wrote it, so the committed copy was the only one and it
went stale when the circuit was recompiled.  `emit_assert.py` then died with `KeyError: 1104` --
a booleanity assertion that exists in the current artifact but not in the old table.

Everything in the table is derived from the artifact:

* `flat`  the 6,840 assertion roots, in `sha_classify.asserts` order (shard order of
          `Gen/{NAME}/{NAME}Asserts*.lean`), which is the order every downstream index means.
          Component 0 of each triple is the root: 184 come out as arity-1 product chains and
          6,656 as arity-2 booleanity, which is the split the classifier reports independently.
* `idx`   its inverse, node -> flat index.
* `sizes` how the flat range is cut into `decide` chunks, and `off` the prefix sums.

`sizes` is a *policy*, not data: 205, then 22 at a time, then whatever remains.  `S2Flat.subOfK`
and `posOfK` hardcode the same 205 and 22, so changing it here without changing `emit_flat.py`
would silently misalign them.
"""
import os, sys, pickle
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from sha_classify import asserts, nodes

HEAD, STEP = 205, 22

flat = [t[0] for t in asserts]
assert len(flat) == len(set(flat)), "assertion roots are not distinct"
for n in flat:
    k, v = nodes[n]
    assert k == "sum" and len(v) in (1, 2), f"node {n} is not an assertion root: {k}"

sizes = [HEAD]
while sum(sizes) < len(flat):
    sizes.append(min(STEP, len(flat) - sum(sizes)))
off, acc = [], 0
for s in sizes:
    off.append(acc); acc += s
assert acc == len(flat)

T = {"flat": flat, "idx": {n: i for i, n in enumerate(flat)}, "sizes": sizes, "off": off}
pickle.dump(T, open(os.path.join(_HERE, "asserttbl.pkl"), "wb"))
print(f"asserttbl.pkl: {len(flat)} assertions, {len(sizes)} chunks "
      f"({sizes[0]} + {sizes.count(STEP)}x{STEP} + {sizes[-1] if sizes[-1] != STEP else 0})")
