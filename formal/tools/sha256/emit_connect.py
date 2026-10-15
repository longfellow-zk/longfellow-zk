import os
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
NL = chr(10)
OUT = os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
LAST = 302
def chain(i):
    inner = "ha" if i == 0 else "List.mem_append_right _ ha"
    return "List.mem_append_left _ (" * (LAST - i) + inner + ")" * (LAST - i)
o = []; A = o.append
A('''/-
# From `Accepts` to the bridges' assertion hypotheses

`S2Sound.assertions_zero_of_bytes` proves every *asserted node* of the artifact evaluates to
zero, quantified over membership in `raw.toRecs`. The 176 meaning bridges instead name ~41,400
specific nodes, in generated tables. This file is the join.

## Why it is not one `decide`

`raw.asserts` is `asserts_0 ++ … ++ asserts_302`, left-associated. Measured on this artifact,
`raw.asserts.getD k` is affordable only for `k` below roughly 1,500 — and the cost tracks the
*depth reached*, not the number of lookups, so 100 lookups at index 5,000 exhaust 14 GB while
400 at index 1,000 fit in 11 GB. Index-chunking therefore does not help: the deep chunks are
individually infeasible.

What is cheap is staying inside a sublist. Each holds 22 entries (the first 205, the last 13),
so `(assertsAt i).getD j` is a walk of at most 22. Lifting `a ∈ assertsAt i` to
`a ∈ raw.asserts` is then `List.mem_append_left`/`_right` — proof terms, not computation.
-/

import quadcert.Bridge.Sha256.S2Sound
import quadcert.Bridge.Sha256.S2TmplWrap
import quadcert.Core.BackedIdx

set_option maxRecDepth 8000000
set_option maxHeartbeats 2000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk
''')
for i in range(LAST + 1):
    A(f"theorem memSub{i} : ∀ a ∈ asserts_{i}, a ∈ raw.asserts := fun a ha => {chain(i)}")
A("")
A("/-- The assertion sublists, by index. -/")
A("def assertsAt : Nat → List RawAssert")
for i in range(LAST + 1): A(f"  | {i} => asserts_{i}")
A("  | _ => []" + NL)
A("theorem memAt : ∀ i, i < 303 → ∀ a ∈ assertsAt i, a ∈ raw.asserts := by")
A("  intro i hi a ha")
A("  match i, hi with")
for i in range(LAST + 1): A(f"  | {i}, _ => exact memSub{i} a ha")
A("  | (n + 303), hx => exact absurd hx (by omega)")
A("")
A('''variable {F : Type} [Field F]

/-- `hacc` restated over `raw.asserts` rather than `raw.toRecs`.

    The record is passed to `hacc` **explicitly**. Leaving it to unification costs 94 s and a
    heartbeat timeout: the conclusion only constrains `?r.assertedNode`, so Lean falls back to
    whnf on `raw.toRecs` and materialises the 303-way append. Supplying it takes 5 s. -/
theorem accAsserts (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ a ∈ raw.asserts, interpDag (raw.toDag (cnstw F)) inputs a.assertedNode = 0 := by
  intro a ha
  have hmem : (⟨a.assertedNode, a.wireLayer, a.wireIndex⟩ : AssertionRec) ∈ raw.toRecs := by
    show _ ∈ List.map _ raw.asserts
    exact List.mem_map_of_mem ha
  exact hacc ⟨a.assertedNode, a.wireLayer, a.wireIndex⟩ hmem

/-- **Every assertion, by sublist and position.** The form the bridges' tables are cut from. -/
theorem zeroAt (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ i, i < 303 → ∀ j, j < (assertsAt i).length →
      interpDag (raw.toDag (cnstw F)) inputs
        ((assertsAt i).getD j ⟨0, 0, 0⟩).assertedNode = 0 := fun i hi j hj =>
  accAsserts inputs hacc ((assertsAt i).getD j ⟨0, 0, 0⟩) (memAt i hi _ (getD_mem _ _ hj))

end Sha256Blk''')
open(os.path.join(OUT, "S2Connect.lean"), "w").write(NL.join(o) + NL)
print("emitted S2Connect.lean", len(o), "lines")
