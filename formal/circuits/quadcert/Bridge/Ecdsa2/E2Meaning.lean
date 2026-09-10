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

import quadcert.Bridge.Ecdsa2.E2Sound
import quadcert.Gen.Ecdsa2.Ecdsa2NodeChk

/-!
# Meaning lemmas: from an assertion's DAG node to a `ValidEcdsaWitness` clause

`Ecdsa2Sound.assertions_zero` says every named assertion's DAG node evaluates to zero. A meaning
lemma says *what that means*, in `ECDSA/EcdsaCircuit.lean`'s vocabulary. This file does it for
the clauses whose cones are small enough to expand outright; the rest need the incremental
composition described at the bottom.

The pattern, per assertion:

1. one `getD` per cone node, through `Check.toDag_getD_fn` so it costs O(log n) rather than
   walking a 27-chunk append (measured: walking timed out at the 65th node of a 118-node cone);
2. one `interpDag_sum` value lemma per node, and `interpDag_input` at the leaves;
3. the constants correspondence for the coefficients the cone mentions;
4. `linear_combination` against the hypothesis.

Two circuit-level facts enter here rather than being checked, and both are recorded in
`CIRCUIT_PROOF_PLAN.md`'s residual-trust list: input position 0 carries the constant `1`, and
the input layout means what its names say.
-/

namespace Ecdsa2.Meaning

open Quadcert Quadcert.Gen.Ecdsa2

/-- P-256's field characteristic, as the constant table encodes it. -/
abbrev p256 : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

variable {F : Type} [Field F] [CharP F p256]

/-! ### Small numerals are non-zero

`EcdsaV2` decides `optPoint`'s and `muxPointF`'s eight-way `if` chains by knowing the lookup
nodes `-8, -6, …, 6` are distinct, which reduces to `2 … 7` being non-zero. That is not
automatic from `Field F`; it follows from `CharP F p256` because `p256` is a prime larger than
`7`. `EcdsaV2` takes it as section variables, so every generated mux lemma — and the final
assembly — would otherwise have to supply it. Declared once, here. -/

instance : NeZero (2 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])
instance : NeZero (3 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])
instance : NeZero (4 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])
instance : NeZero (5 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])
instance : NeZero (6 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])
instance : NeZero (7 : F) := NeZero.of_not_dvd (R := F) (p := p256) (by norm_num [p256])

/-! ### The constants this file uses

The generated table holds canonical integers from the artifact's own encoding, so a negated
constant appears as `p - n`. Relating it to `-n` is where the P-256 choice enters, and it enters
as the `CharP` hypothesis rather than as prose. -/

theorem consts_0 : Ecdsa2.consts F 0 = 1 := by
  show ((constNat 0 : Nat) : F) = 1
  have h : constNat 0 = 1 := by rfl
  rw [h, Nat.cast_one]

theorem consts_1 : Ecdsa2.consts F 1 = -1 := by
  show ((constNat 1 : Nat) : F) = -1
  have h : constNat 1 = p256 - 1 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256 1 (by norm_num)]
  norm_num

/-- A negated constant: the artifact encodes `-n` as `p - n`, so relating the two is where the
    P-256 choice enters, and it enters as the `CharP` hypothesis rather than as prose. -/
theorem consts_neg (k n : Nat) (h : constNat k = p256 - n) (hn : n ≤ p256) :
    Ecdsa2.consts F k = -(n : F) := by
  show ((constNat k : Nat) : F) = -(n : F)
  rw [h, Quadcert.cast_sub_eq_neg p256 n hn]

/-- A small constant, as itself. -/
theorem consts_pos (k n : Nat) (h : constNat k = n) : Ecdsa2.consts F k = (n : F) := by
  show ((constNat k : Nat) : F) = (n : F)
  rw [h]

end Ecdsa2.Meaning
