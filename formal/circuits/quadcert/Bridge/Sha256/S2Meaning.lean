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

import quadcert.Bridge.Sha256.S2Sound
import quadcert.Gen.Sha256Blk.Sha256BlkNodeChk
import SHA.Field
import SHA.Wrap

/-!
# Meaning lemmas for SHA-256: support module

`Sha256Blk.assertions_zero` says every named assertion's DAG node evaluates to zero. A meaning
lemma says *what that means*, in `SHA/Spec.lean`'s vocabulary. This module supplies what the
generated lemmas cite; `meaning_gen` is pointed at it with `SUPPORT=S2Meaning`.

The pattern, per assertion:

1. one `getD` per cone node, through `Check.toDag_getD_fn` so it costs O(log n) rather than
   walking a 19-chunk append;
2. one `interpDag_sum` value lemma per node, and `interpDag_input` at the leaves;
3. the constants correspondence for the coefficients the cone mentions;
4. `ring`, or `linear_combination` against the hypothesis.

The 6,656 `is_boolean` assertions land on `SHA256F.isBit_of_zero_raw`. The 184
`assert_wrapping_sum_prime` assertions are cut at the circuit's own `z` node and land on
`SHA256F.wrap_sum_of_zero`: expanding one outright is not merely slow but impossible, since the
product raises a degree-4 polynomial to the 4th or 6th power — measured at 10^16 and 10^26 leaves
in the inlined expression, against 2,019 for the cone below `z`.

Two circuit-level facts enter here rather than being checked, and both belong in
`CIRCUIT_PROOF_PLAN.md`'s residual-trust list: input position 0 carries the constant `1`, and the
input layout means what its names say.
-/

namespace Sha256Blk.Meaning

open Quadcert Quadcert.Gen.Sha256Blk

/-- P-256's field characteristic, as the constant table encodes it. The SHA-256 circuit is
    compiled over the same prime field as ECDSA2 — `sha256_artifacts.rs` passes `FieldID::P256` —
    so the negated-constant encoding below is the same one. -/
abbrev p256 : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

variable {F : Type} [Field F] [CharP F p256]

/-! ### The constants this file uses

The generated table holds canonical integers from the artifact's own encoding, so a negated
constant appears as `p - n`. Relating it to `-n` is where the P-256 choice enters, and it enters
as the `CharP` hypothesis rather than as prose.

Unlike ECDSA2 there is no `consts_1 : consts F 1 = -1`: the tables are sorted by frequency per
circuit, and this circuit's constant 1 is `p - 2`, not `p - 1`. Only the two general lemmas are
cited by generated code, so nothing depends on the accident of which index holds what. -/

theorem consts_0 : Sha256Blk.consts F 0 = 1 := by
  show ((constNat 0 : Nat) : F) = 1
  have h : constNat 0 = 1 := by rfl
  rw [h, Nat.cast_one]

/-- A negated constant: the artifact encodes `-n` as `p - n`. -/
theorem consts_neg (k n : Nat) (h : constNat k = p256 - n) (hn : n ≤ p256) :
    Sha256Blk.consts F k = -(n : F) := by
  show ((constNat k : Nat) : F) = -(n : F)
  rw [h, Quadcert.cast_sub_eq_neg p256 n hn]

/-- A small constant, as itself. -/
theorem consts_pos (k n : Nat) (h : constNat k = n) : Sha256Blk.consts F k = (n : F) := by
  show ((constNat k : Nat) : F) = (n : F)
  rw [h]

end Sha256Blk.Meaning
