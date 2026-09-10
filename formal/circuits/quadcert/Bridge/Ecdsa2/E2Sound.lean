/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import quadcert.Core.Check
import quadcert.Gen.Ecdsa2.Ecdsa2OkCheck
import quadcert.Gen.Ecdsa2.Ecdsa2InvCheck
import quadcert.Gen.Ecdsa2.Ecdsa2SumLocal
import quadcert.Gen.Ecdsa2.Ecdsa2Backed

/-!
# ECDSA2: committed bytes to named assertions

The assembly point. Nothing here is data and nothing here is generated — it is the generic
theory of `quadcert/Check.lean` and `quadcert/Semantics.lean` applied to the checks the
generated modules discharged. This is also the only module on the path that pays for Mathlib.

**The name matters.** Every generated module is `Ecdsa2*`, and regenerating starts with
`rm -f Ecdsa2*.lean`. A hand-written module must not answer to that glob; this one is `E2Sound`
for exactly that reason, after an earlier `Ecdsa2Sound.lean` was deleted by its own build script.

The chain, with the module that closes each step:

```
  packed LFC2 pages                      Ecdsa2Packed{k}
    → page-hash leaves, Merkle root      Ecdsa2Commitment{k}, Ecdsa2Commitment
    → staged parse : CompressedCircuit   Ecdsa2Header, Ecdsa2CompressedLayer{l}, Ecdsa2Compressed
    → term expansion : DecodedCircuit    Ecdsa2Expansion{l}_{j}, Ecdsa2ExpandedLayer{l}, Ecdsa2Decoded
    → decode                             Ecdsa2Decode
    → RawCircuit                         Ecdsa2Data (`raw_from_bytes`)
    → ValidScheduling, all eight fields   this module (`valid`)
    → Accepts → named assertions zero     this module (`assertions_zero`)
```
-/

namespace Ecdsa2

open Quadcert Quadcert.Gen.Ecdsa2

variable {F : Type} [Field F]

/-- The generated constant table, cast into the field. The table is the **artifact's**:
    `ecdsa2_artifacts.rs` builds the sidecar from the segmented circuit, so the numbering
    `constNat` uses is the one the committed bytes commit to. -/
def consts (F : Type) [Field F] : Nat → F := fun i => (constNat i : F)

/-- The one constants fact `Backed` needs. -/
theorem consts_zeroConst : consts F zeroConst = 0 := by
  have h : constNat zeroConst = 0 := by rfl
  show ((constNat zeroConst : Nat) : F) = 0
  rw [h, Nat.cast_zero]

/-- The compiled circuit, over `F`. -/
@[reducible] noncomputable def circuit (F : Type) [Field F] : QuadCircuitData F :=
  raw.toQuad (consts F)

/-- **All eight `ValidScheduling` fields**, from the generated checks alone. `sum_local` is the
    one that needed the grouping certificates — `perm_all`, `hom_all`, `corr_check`; the other
    seven come from `ok_check` and `inv_check`. -/
theorem valid (inputs : Nat → F) :
    ValidScheduling (circuit F) (raw.toDag (consts F)) raw.toWireMap inputs :=
  validScheduling_of_raw raw (consts F) inputs wireInv groupOf gbound
    ok_check inv_check wireFn_lt perm_all hom_all corr_check

/-- **Soundness bridge.** An accepting input assignment zeroes every named assertion. Only
    `Backed` is required; `CoversConstraints` is what the converse would need. -/
theorem assertions_zero (inputs : Nat → F) (hacc : Accepts (circuit F) inputs) :
    ∀ r ∈ raw.toRecs, interpDag (raw.toDag (consts F)) inputs r.assertedNode = 0 :=
  assertions_zero_of_accepts (circuit F) (raw.toDag (consts F)) raw.toWireMap inputs
    (valid inputs) raw.toRecs
    (all_backed_of_rawWith raw (consts F) zeroConst consts_zeroConst azt azt_sub backed_check)
    (by rw [toQuad_layers_length]; show 0 < 11; norm_num) hacc

/-- **The same, from the committed bytes.** Whatever the pinned LFC2 pages decode to, extended by
    the sidecar's four advice fields, *is* `raw` — so this is a statement about the artifact and
    not about a generated literal. -/
theorem assertions_zero_of_bytes (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) (hacc : Accepts ((c.toRaw advice).toQuad (consts F)) inputs) :
    ∀ r ∈ (c.toRaw advice).toRecs,
      interpDag ((c.toRaw advice).toDag (consts F)) inputs r.assertedNode = 0 := by
  rw [raw_from_bytes c hdec] at hacc ⊢
  exact assertions_zero inputs hacc

/-- **Per-assertion accessor.** `assertions_zero` quantifies over `raw.toRecs`, so using it for a
    particular node needs a membership witness. Going through the index makes that cheap:
    `List.getElem_mem` supplies membership, and the record's `assertedNode` is a numeral, so the
    side condition is `rfl`. Every meaning lemma's hypothesis is obtained this way.

    Applying it needs `i < raw.toRecs.length`, and there is no length lemma for `toRecs` yet --
    `by decide` times out in `whnf` on a list that size. `toRecs` is `asserts.map _`, and
    `Ecdsa2Data` builds `asserts` as `asserts_0 ++ ... ++ asserts_4`, so the missing lemma is

        theorem recs_len : raw.toRecs.length = N := by
          simp only [RawCircuit.toRecs, List.length_map]
          show (asserts_0 ++ asserts_1 ++ asserts_2 ++ asserts_3 ++ asserts_4).length = N
          simp only [List.length_append, ...]

    exactly mirroring `nodes_len` in `Ecdsa2Data`, which needs the generator to emit per-chunk
    `alen_j` lemmas alongside the existing `len_j`. Then every side condition is
    `by rw [recs_len]; omega`, the pattern used throughout the meaning lemmas. -/
theorem assert_at (inputs : Nat → F) (hacc : Accepts (circuit F) inputs)
    (i : Nat) (hi : i < raw.toRecs.length) (N : Nat)
    (hN : (raw.toRecs[i]'hi).assertedNode = N) :
    interpDag (raw.toDag (consts F)) inputs N = 0 := by
  subst hN
  exact assertions_zero inputs hacc _ (List.getElem_mem hi)

/-- **The accessor the assembly should use.** `assert_at` needs `i < raw.toRecs.length`, which
    has no cheap proof (`decide` times out in `whnf` on a list that size, and a `recs_len` lemma
    would need the generator to emit per-chunk `alen_j`). `getElem?` removes the obligation
    entirely: the caller supplies `raw.toRecs[i]? = some r` by `rfl`, which forces the list only
    as far as `i`.

    Verified to fire at index 0, with `r` recovered from the list by unification. **But the
    `rfl` cost is linear in `i`**: at 0 it is instant, and at a digit's record index (in the
    thousands) it times out in `whnf`. Measured, not assumed -- a four-digit `hdig` bridge was
    generated and failed exactly there.

    **Do not use either accessor for the assembly.** Both pay per assertion. Destructure the
    quantifier once instead -- verified to work, and it needs no generator change:

        have H := assertions_zero inputs hacc
        simp only [RawCircuit.toRecs, List.forall_mem_map,
          show raw.asserts = asserts_0 ++ asserts_1 ++ asserts_2 ++ asserts_3 ++ asserts_4
            from rfl,
          List.forall_mem_append] at H
        obtain ⟨⟨⟨⟨H0, H1⟩, H2⟩, H3⟩, H4⟩ := H
        simp only [asserts_0, List.forall_mem_cons] at H0
        obtain ⟨e0, e1, ...⟩ := H0

    `e0` and `e1` then *are* `interpDag ... 10706 = 0` and `interpDag ... 14406 = 0` -- the two
    comparator assertions -- with no membership proof anywhere. `asserts_j` must be named in the
    `simp` set: it is a `def`, so simp will not unfold it otherwise. The cost is one pass per
    chunk, not one walk per assertion. -/
theorem assert_at' (inputs : Nat → F) (hacc : Accepts (circuit F) inputs)
    (i : Nat) (r : AssertionRec) (h : raw.toRecs[i]? = some r) :
    interpDag (raw.toDag (consts F)) inputs r.assertedNode = 0 :=
  assertions_zero inputs hacc r (List.mem_of_getElem? h)

end Ecdsa2
