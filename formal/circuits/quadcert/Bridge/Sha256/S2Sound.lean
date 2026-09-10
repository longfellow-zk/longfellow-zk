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
import quadcert.Gen.Sha256Blk.Sha256BlkOkCheck
import quadcert.Gen.Sha256Blk.Sha256BlkInvCheck
import quadcert.Gen.Sha256Blk.Sha256BlkSumLocal
import quadcert.Gen.Sha256Blk.Sha256BlkBacked

/-!
# SHA-256: committed bytes to named assertions

The assembly point for the one-block SHA-256 circuit, mirroring `E2Sound` for ECDSA2. Nothing
here is data and nothing here is generated — it is the generic theory of `quadcert/Check.lean`
and `quadcert/Semantics.lean` applied to the checks the generated modules discharged.

**The name matters.** Every generated module for this circuit is `Sha256Blk*`, and regenerating
starts by removing them. A hand-written module must not answer to that glob — nor to `Sha*`,
which is what actually destroyed `quadcert/Sha256.lean` once. Hence `S2Sound`, matching neither,
by the same reasoning that named ECDSA2's `E2Sound`.

The chain, with the module that closes each step:

```
  packed LFC3 pages                      Sha256BlkPacked{k}
    → page-hash leaves, Merkle root      Sha256BlkCommitment{k}, Sha256BlkCommitment
    → staged parse : CompressedCircuit   Sha256BlkHeader, Sha256BlkCompressedLayer{l}, …
    → term expansion : DecodedCircuit    Sha256BlkExpansion{l}_{j}, Sha256BlkExpandedLayer{l}, …
    → decode                             Sha256BlkDecode
    → RawCircuit                         Sha256BlkData (`raw_from_bytes`)
    → ValidScheduling, all eight fields   this module (`valid`)
    → Accepts → named assertions zero     this module (`assertions_zero`)
```
-/

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {F : Type} [Field F]

/-- The generated constant table, cast into the field. The table is the **artifact's**:
    `sha256_artifacts.rs` builds the sidecar from the segmented circuit, so the numbering
    `constNat` uses is the one the committed bytes commit to. -/
def consts (F : Type) [Field F] : Nat → F := fun i => (constNat i : F)

/-- The one constants fact `Backed` needs. Note `zeroConst` is 3 here, not ECDSA2's 70 — the
    segmentation pass sorts the constant table by frequency, so the index is per-circuit. -/
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
    (by rw [toQuad_layers_length]; show 0 < 6; norm_num) hacc

/-- **The same, from the committed bytes.** Whatever the pinned LFC3 pages decode to, extended by
    the sidecar's four advice fields, *is* `raw` — so this is a statement about the artifact and
    not about a generated literal. -/
theorem assertions_zero_of_bytes (c : Lfc3.DecodedCircuit)
    (hdec : Lfc3.decode Lfc3.p256 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) (hacc : Accepts ((c.toRaw advice).toQuad (consts F)) inputs) :
    ∀ r ∈ (c.toRaw advice).toRecs,
      interpDag ((c.toRaw advice).toDag (consts F)) inputs r.assertedNode = 0 := by
  rw [raw_from_bytes c hdec] at hacc ⊢
  exact assertions_zero inputs hacc

end Sha256Blk
