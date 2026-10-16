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

import ECDSA.EcdsaSound

/-!
# The Rust v2 ECDSA interface, against `ValidEcdsaWitness`

`ECDSA/EcdsaCircuit.lean` models the C++ circuit (`verify_circuit.h`). The deployed Rust circuit
(`rust/circuits/ecdsa2/src/circuit.rs`) computes the same thing but does not present it the same
way, and the differences are real rather than cosmetic:

* **The three-bit digit is packed in the opposite order.** `circuit.rs`'s lookup table is
  `opts = [0, R, PK, PK+R, G, G+R, G+PK, G+PK+R]`, i.e. index `4·[G] + 2·[PK] + 1·[R]`, and its
  bit extractors are `(idx & 4)`, `(idx & 2)`, `(idx & 1)` for `e`, `r`, `nms`. `muxPoint`'s
  index is `[G] + 2·[PK] + 4·[R]`. The *point selected* is the same function of the three bits;
  only the packing differs, so a witness digit must be bit-reversed before it is a `bi` digit.
* **The Rust loop runs 256 rounds and stores all 256 accumulators**, while
  `EcdsaLoopConstraintsF` consumes 256 digits against 255 intermediates and computes the last
  accumulator with `ecdsaLoopResultF`. Rust's final `round[0]` is that computed value, pinned by
  the round-0 assertions.
* **Rust iterates `i = 255 … 0`**, so `bi k` is `ers (255 - k)`; `reconstructE` folds
  most-significant-first while `as_eltw_unsafe` weights index `i` by `2^i`, and those agree
  under the same reversal.
* **`yinv` has no counterpart.** It is an extra constraint, which only strengthens the circuit;
  soundness does not need it.

This file closes the first of those. `optPoint` is the Rust selection, stated directly, and
`LoopConstraintsOpt` is `EcdsaLoopConstraintsF` phrased over it.
-/

namespace ECDSA2

open Classical

variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)]
  [NeZero (6 : F)] [NeZero (7 : F)]

/-- A witness digit is one of the eight lookup **nodes**, not a raw index.

    `lookup_point(9, i) = 2i - 8` (`compile/algebra/src/fp.rs:251`), and `concrete.rs` fills
    `ers[i]` with `f.lookup_point(9, 4e + 2r + s)`. So the value on the wire is the encoded node
    `2d - 8`, and the eight admissible values are `-8, -6, -4, -2, 0, 2, 4, 6`. This is what
    `range_check`'s `valid_index` buys: the 9-point interpolant through `(node_i, δ_{i,8})` has
    its roots exactly at nodes `0 … 7`, so asserting it vanishes says the wire carries one of
    them. -/
def IsDigit (u : F) : Prop :=
  u = -8 ∨ u = -6 ∨ u = -4 ∨ u = -2 ∨ u = 0 ∨ u = 2 ∨ u = 4 ∨ u = 6

/-- Encoded node `2d - 8` to `muxPoint`'s index, reversing the digit's three bits on the way:
    `circuit.rs` packs `4e + 2r + s`, `muxPoint` packs `e + 2r + 4s`. -/
noncomputable def bitrev3 (u : F) : F :=
  if u = -8 then 0
  else if u = -6 then 4
  else if u = -4 then 2
  else if u = -2 then 6
  else if u = 0 then 1
  else if u = 2 then 5
  else if u = 4 then 3
  else 7

/-- The point `circuit.rs`'s `opts` table holds for the node `2d - 8`:
    `opts = [zero, R, PK, PK+R, G, G+R, G+PK, G+PK+R]` indexed by `d = 4·[G] + 2·[PK] + 1·[R]`.
    `pre` is in `ValidPreComputationExact` order — `[GPK.x, GPK.y, GR.x, GR.y, RPK.x, RPK.y,
    GRPK.x, GRPK.y]` — which is also the order `allocate_derived_wires` lays down
    `g_pk, g_r, pk_r, g_pk_r`. -/
noncomputable def optPoint (u : F) (pk : AffinePoint F) (rx ry : F) (pre : List F)
    (params : CurveParameters F) : ProjectivePoint F :=
  if u = -8 then { X := 0, Y := 1, Z := 0 }                                    -- d = 0, infinity
  else if u = -6 then ({ X := rx, Y := ry : AffinePoint F }).toProjective       -- d = 1, R
  else if u = -4 then pk.toProjective                                           -- d = 2, PK
  else if u = -2 then ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective
  else if u = 0 then ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective  -- d = 4, G
  else if u = 2 then ({ X := pre.getD 2 0, Y := pre.getD 3 0 : AffinePoint F }).toProjective
  else if u = 4 then ({ X := pre.getD 0 0, Y := pre.getD 1 0 : AffinePoint F }).toProjective
  else { X := pre.getD 6 0, Y := pre.getD 7 0, Z := 1 }                         -- d = 7, G+PK+R

section Digits

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
private lemma num_ne' {a b c : F} (hc : c ≠ 0) (h : a - b = c) : a ≠ b := by
  intro he; exact hc (by rw [← h, he, sub_self])

omit [NeZero (3 : F)] in
/-- Differences between distinct lookup nodes are `2, 4, …, 14`. The even ones above `7` are not
    hypotheses: `2m ≠ 0` follows from `2 ≠ 0` and `m ≠ 0` in a field. -/
private lemma node_diff_ne_zero :
    ((2 : F) ≠ 0) ∧ ((4 : F) ≠ 0) ∧ ((6 : F) ≠ 0) ∧ ((8 : F) ≠ 0) ∧ ((10 : F) ≠ 0) ∧
      ((12 : F) ≠ 0) ∧ ((14 : F) ≠ 0) := by
  have n2 : (2 : F) ≠ 0 := NeZero.ne _
  have n4 : (4 : F) ≠ 0 := NeZero.ne _
  have n5 : (5 : F) ≠ 0 := NeZero.ne _
  have n6 : (6 : F) ≠ 0 := NeZero.ne _
  have n7 : (7 : F) ≠ 0 := NeZero.ne _
  refine ⟨n2, n4, n6, ?_, ?_, ?_, ?_⟩
  · rw [show (8 : F) = 2 * 4 by norm_num]; exact mul_ne_zero n2 n4
  · rw [show (10 : F) = 2 * 5 by norm_num]; exact mul_ne_zero n2 n5
  · rw [show (12 : F) = 2 * 6 by norm_num]; exact mul_ne_zero n2 n6
  · rw [show (14 : F) = 2 * 7 by norm_num]; exact mul_ne_zero n2 n7

omit [NeZero (3 : F)] in
/-- Every `if` condition either if-chain has to decide, as one bundle. -/
private lemma node_ne :
    ((-6 : F) ≠ -8) ∧ ((-4 : F) ≠ -8) ∧ ((-4 : F) ≠ -6) ∧ ((-2 : F) ≠ -8) ∧ ((-2 : F) ≠ -6) ∧
    ((-2 : F) ≠ -4) ∧ ((0 : F) ≠ -8) ∧ ((0 : F) ≠ -6) ∧ ((0 : F) ≠ -4) ∧ ((0 : F) ≠ -2) ∧
    ((2 : F) ≠ -8) ∧ ((2 : F) ≠ -6) ∧ ((2 : F) ≠ -4) ∧ ((2 : F) ≠ -2) ∧ ((2 : F) ≠ 0) ∧
    ((4 : F) ≠ -8) ∧ ((4 : F) ≠ -6) ∧ ((4 : F) ≠ -4) ∧ ((4 : F) ≠ -2) ∧ ((4 : F) ≠ 0) ∧
    ((4 : F) ≠ 2) ∧ ((6 : F) ≠ -8) ∧ ((6 : F) ≠ -6) ∧ ((6 : F) ≠ -4) ∧ ((6 : F) ≠ -2) ∧
    ((6 : F) ≠ 0) ∧ ((6 : F) ≠ 2) ∧ ((6 : F) ≠ 4) := by
  obtain ⟨n2, n4, n6, n8, n10, n12, n14⟩ := node_diff_ne_zero (F := F)
  exact ⟨num_ne' n2 (by norm_num), num_ne' n4 (by norm_num), num_ne' n2 (by norm_num),
    num_ne' n6 (by norm_num), num_ne' n4 (by norm_num), num_ne' n2 (by norm_num),
    num_ne' n8 (by norm_num), num_ne' n6 (by norm_num), num_ne' n4 (by norm_num),
    num_ne' n2 (by norm_num), num_ne' n10 (by norm_num), num_ne' n8 (by norm_num),
    num_ne' n6 (by norm_num), num_ne' n4 (by norm_num), num_ne' n2 (by norm_num),
    num_ne' n12 (by norm_num), num_ne' n10 (by norm_num), num_ne' n8 (by norm_num),
    num_ne' n6 (by norm_num), num_ne' n4 (by norm_num), num_ne' n2 (by norm_num),
    num_ne' n14 (by norm_num), num_ne' n12 (by norm_num), num_ne' n10 (by norm_num),
    num_ne' n8 (by norm_num), num_ne' n6 (by norm_num), num_ne' n4 (by norm_num),
    num_ne' n2 (by norm_num)⟩

/-- **The packing bridge.** On the eight lookup nodes, `muxPoint`'s index of the bit-reversed
    digit selects exactly what the circuit's table holds. -/
theorem muxPointF_bitrev3 (u : F) (hu : IsDigit u) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F) :
    muxPointF (bitrev3 u) pk rx ry pre params = optPoint u pk rx ry pre params := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩ := node_ne (F := F)
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h2 : (2 : F) ≠ 0 := NeZero.ne _
  have h3 : (3 : F) ≠ 0 := NeZero.ne _
  have h4 : (4 : F) ≠ 0 := NeZero.ne _
  have h5 : (5 : F) ≠ 0 := NeZero.ne _
  have h6 : (6 : F) ≠ 0 := NeZero.ne _
  have h7 : (7 : F) ≠ 0 := NeZero.ne _
  have e10 : (1 : F) ≠ 0 := num_ne' h1 (by norm_num)
  have e20 : (2 : F) ≠ 0 := num_ne' h2 (by norm_num)
  have e21 : (2 : F) ≠ 1 := num_ne' h1 (by norm_num)
  have e30 : (3 : F) ≠ 0 := num_ne' h3 (by norm_num)
  have e31 : (3 : F) ≠ 1 := num_ne' h2 (by norm_num)
  have e32 : (3 : F) ≠ 2 := num_ne' h1 (by norm_num)
  have e40 : (4 : F) ≠ 0 := num_ne' h4 (by norm_num)
  have e41 : (4 : F) ≠ 1 := num_ne' h3 (by norm_num)
  have e42 : (4 : F) ≠ 2 := num_ne' h2 (by norm_num)
  have e43 : (4 : F) ≠ 3 := num_ne' h1 (by norm_num)
  have e50 : (5 : F) ≠ 0 := num_ne' h5 (by norm_num)
  have e51 : (5 : F) ≠ 1 := num_ne' h4 (by norm_num)
  have e52 : (5 : F) ≠ 2 := num_ne' h3 (by norm_num)
  have e53 : (5 : F) ≠ 3 := num_ne' h2 (by norm_num)
  have e54 : (5 : F) ≠ 4 := num_ne' h1 (by norm_num)
  have e60 : (6 : F) ≠ 0 := num_ne' h6 (by norm_num)
  have e61 : (6 : F) ≠ 1 := num_ne' h5 (by norm_num)
  have e62 : (6 : F) ≠ 2 := num_ne' h4 (by norm_num)
  have e63 : (6 : F) ≠ 3 := num_ne' h3 (by norm_num)
  have e64 : (6 : F) ≠ 4 := num_ne' h2 (by norm_num)
  have e65 : (6 : F) ≠ 5 := num_ne' h1 (by norm_num)
  have e70 : (7 : F) ≠ 0 := num_ne' h7 (by norm_num)
  have e71 : (7 : F) ≠ 1 := num_ne' h6 (by norm_num)
  have e72 : (7 : F) ≠ 2 := num_ne' h5 (by norm_num)
  have e73 : (7 : F) ≠ 3 := num_ne' h4 (by norm_num)
  have e74 : (7 : F) ≠ 4 := num_ne' h3 (by norm_num)
  have e75 : (7 : F) ≠ 5 := num_ne' h2 (by norm_num)
  have e76 : (7 : F) ≠ 6 := num_ne' h1 (by norm_num)
  rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [bitrev3, optPoint, muxPointF, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28,
      e10, e21, e30, e31, e32, e41, e43,
      e50, e51, e52, e53, e54, e61, e63, e65, e70, e71, e72, e73, e74, e75, e76,
      if_true, if_false]

/-! ### `optPoint` at the eight nodes

The generated *mux* lemmas — `interpDag <wire> = (optPoint u …).X` and its `Y`/`Z` siblings —
case on `IsDigit u` and then have to decide `optPoint`'s eight-way `if` chain. Deciding it once
here, rather than inside each of the ~1,536 generated proofs, keeps those proofs to a cone chain
plus one `linear_combination`. -/

section OptPointNodes
variable (pk : AffinePoint F) (rx ry : F) (pre : List F) (params : CurveParameters F)

omit [NeZero (3 : F)] in
private lemma optPoint_all :
    optPoint (-8 : F) pk rx ry pre params = { X := 0, Y := 1, Z := 0 } ∧
    optPoint (-6 : F) pk rx ry pre params = { X := rx, Y := ry, Z := 1 } ∧
    optPoint (-4 : F) pk rx ry pre params = { X := pk.X, Y := pk.Y, Z := 1 } ∧
    optPoint (-2 : F) pk rx ry pre params
      = { X := pre.getD 4 0, Y := pre.getD 5 0, Z := 1 } ∧
    optPoint (0 : F) pk rx ry pre params = { X := params.gx, Y := params.gy, Z := 1 } ∧
    optPoint (2 : F) pk rx ry pre params
      = { X := pre.getD 2 0, Y := pre.getD 3 0, Z := 1 } ∧
    optPoint (4 : F) pk rx ry pre params
      = { X := pre.getD 0 0, Y := pre.getD 1 0, Z := 1 } ∧
    optPoint (6 : F) pk rx ry pre params
      = { X := pre.getD 6 0, Y := pre.getD 7 0, Z := 1 } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩ := node_ne (F := F)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [optPoint, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, AffinePoint.toProjective,
      if_true, if_false]

omit [NeZero (3 : F)] in
theorem optPoint_n0 : optPoint (-8 : F) pk rx ry pre params = { X := 0, Y := 1, Z := 0 } :=
  (optPoint_all pk rx ry pre params).1
omit [NeZero (3 : F)] in
theorem optPoint_n1 : optPoint (-6 : F) pk rx ry pre params = { X := rx, Y := ry, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.1
omit [NeZero (3 : F)] in
theorem optPoint_n2 : optPoint (-4 : F) pk rx ry pre params = { X := pk.X, Y := pk.Y, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.1
omit [NeZero (3 : F)] in
theorem optPoint_n3 :
    optPoint (-2 : F) pk rx ry pre params = { X := pre.getD 4 0, Y := pre.getD 5 0, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.2.1
omit [NeZero (3 : F)] in
theorem optPoint_n4 :
    optPoint (0 : F) pk rx ry pre params = { X := params.gx, Y := params.gy, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.2.2.1
omit [NeZero (3 : F)] in
theorem optPoint_n5 :
    optPoint (2 : F) pk rx ry pre params = { X := pre.getD 2 0, Y := pre.getD 3 0, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.2.2.2.1
omit [NeZero (3 : F)] in
theorem optPoint_n6 :
    optPoint (4 : F) pk rx ry pre params = { X := pre.getD 0 0, Y := pre.getD 1 0, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.2.2.2.2.1
omit [NeZero (3 : F)] in
theorem optPoint_n7 :
    optPoint (6 : F) pk rx ry pre params = { X := pre.getD 6 0, Y := pre.getD 7 0, Z := 1 } :=
  (optPoint_all pk rx ry pre params).2.2.2.2.2.2.2

/-! The same, already projected. A generated proof ends in `linear_combination`, whose `ring`
treats `(⟨a, b, c⟩ : ProjectivePoint F).X` as an opaque atom rather than reducing it, so the
projection has to be gone before then. Rewriting with these does that in one step. -/

omit [NeZero (3 : F)] in
theorem optPoint_n0_X : (optPoint (-8 : F) pk rx ry pre params).X = 0 := by rw [optPoint_n0]
omit [NeZero (3 : F)] in
theorem optPoint_n0_Y : (optPoint (-8 : F) pk rx ry pre params).Y = 1 := by rw [optPoint_n0]
omit [NeZero (3 : F)] in
theorem optPoint_n0_Z : (optPoint (-8 : F) pk rx ry pre params).Z = 0 := by rw [optPoint_n0]
omit [NeZero (3 : F)] in
theorem optPoint_n1_X : (optPoint (-6 : F) pk rx ry pre params).X = rx := by rw [optPoint_n1]
omit [NeZero (3 : F)] in
theorem optPoint_n1_Y : (optPoint (-6 : F) pk rx ry pre params).Y = ry := by rw [optPoint_n1]
omit [NeZero (3 : F)] in
theorem optPoint_n1_Z : (optPoint (-6 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n1]
omit [NeZero (3 : F)] in
theorem optPoint_n2_X : (optPoint (-4 : F) pk rx ry pre params).X = pk.X := by rw [optPoint_n2]
omit [NeZero (3 : F)] in
theorem optPoint_n2_Y : (optPoint (-4 : F) pk rx ry pre params).Y = pk.Y := by rw [optPoint_n2]
omit [NeZero (3 : F)] in
theorem optPoint_n2_Z : (optPoint (-4 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n2]
omit [NeZero (3 : F)] in
theorem optPoint_n3_X : (optPoint (-2 : F) pk rx ry pre params).X = pre.getD 4 0 := by
  rw [optPoint_n3]
omit [NeZero (3 : F)] in
theorem optPoint_n3_Y : (optPoint (-2 : F) pk rx ry pre params).Y = pre.getD 5 0 := by
  rw [optPoint_n3]
omit [NeZero (3 : F)] in
theorem optPoint_n3_Z : (optPoint (-2 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n3]
omit [NeZero (3 : F)] in
theorem optPoint_n4_X : (optPoint (0 : F) pk rx ry pre params).X = params.gx := by rw [optPoint_n4]
omit [NeZero (3 : F)] in
theorem optPoint_n4_Y : (optPoint (0 : F) pk rx ry pre params).Y = params.gy := by rw [optPoint_n4]
omit [NeZero (3 : F)] in
theorem optPoint_n4_Z : (optPoint (0 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n4]
omit [NeZero (3 : F)] in
theorem optPoint_n5_X : (optPoint (2 : F) pk rx ry pre params).X = pre.getD 2 0 := by
  rw [optPoint_n5]
omit [NeZero (3 : F)] in
theorem optPoint_n5_Y : (optPoint (2 : F) pk rx ry pre params).Y = pre.getD 3 0 := by
  rw [optPoint_n5]
omit [NeZero (3 : F)] in
theorem optPoint_n5_Z : (optPoint (2 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n5]
omit [NeZero (3 : F)] in
theorem optPoint_n6_X : (optPoint (4 : F) pk rx ry pre params).X = pre.getD 0 0 := by
  rw [optPoint_n6]
omit [NeZero (3 : F)] in
theorem optPoint_n6_Y : (optPoint (4 : F) pk rx ry pre params).Y = pre.getD 1 0 := by
  rw [optPoint_n6]
omit [NeZero (3 : F)] in
theorem optPoint_n6_Z : (optPoint (4 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n6]
omit [NeZero (3 : F)] in
theorem optPoint_n7_X : (optPoint (6 : F) pk rx ry pre params).X = pre.getD 6 0 := by
  rw [optPoint_n7]
omit [NeZero (3 : F)] in
theorem optPoint_n7_Y : (optPoint (6 : F) pk rx ry pre params).Y = pre.getD 7 0 := by
  rw [optPoint_n7]
omit [NeZero (3 : F)] in
theorem optPoint_n7_Z : (optPoint (6 : F) pk rx ry pre params).Z = 1 := by rw [optPoint_n7]

end OptPointNodes

end Digits

/-! ## The loop, in the circuit's own packing

`LoopConstraintsOpt` is `EcdsaLoopConstraintsF` with `optPoint` in place of `muxPointF`: exactly
what the 256 `slice_wx` / `slice_wy` / `slice_wz` assertions say, given that `slicing3` asserts
`round[i] = add (double p) (opts[ers[i]])` componentwise. -/

noncomputable def LoopConstraintsOpt :
    ProjectivePoint F → Bool → List F → List F → List F → List F → AffinePoint F → F → F →
      List F → CurveParameters F → Prop
  | _, _, [], _, _, _, _, _, _, _, _ => True
  | _, _, [_], [], [], [], _, _, _, _, _ => True
  | acc, is_first, u :: us@(_ :: _), wx :: wxs, wy :: wys, wz :: wzs, pk, rx, ry, pre, params =>
    let tx := optPoint u pk rx ry pre params
    let doubled := if is_first then acc else doubleE acc params
    let nextAcc := addE doubled tx params
    nextAcc.X = wx ∧ nextAcc.Y = wy ∧ nextAcc.Z = wz ∧
    LoopConstraintsOpt { X := wx, Y := wy, Z := wz } false us wxs wys wzs pk rx ry pre params
  | _, _, _, _, _, _, _, _, _, _, _ => False

noncomputable def loopResultOpt :
    ProjectivePoint F → Bool → List F → List F → List F → List F → AffinePoint F → F → F →
      List F → CurveParameters F → ProjectivePoint F
  | acc, _, [], _, _, _, _, _, _, _, _ => acc
  | acc, is_first, [u], [], [], [], pk, rx, ry, pre, params =>
    let tx := optPoint u pk rx ry pre params
    let doubled := if is_first then acc else doubleE acc params
    addE doubled tx params
  | _, _, _ :: us@(_ :: _), wx :: wxs, wy :: wys, wz :: wzs, pk, rx, ry, pre, params =>
    loopResultOpt { X := wx, Y := wy, Z := wz } false us wxs wys wzs pk rx ry pre params
  | _, _, _, _, _, _, _, _, _, _, _ => infinityPoint

/-- **The loop bridge.** The circuit's round constraints, in its own digit packing, *are*
    `EcdsaLoopConstraintsF` on the bit-reversed digits. Structural in the digit list, so it does
    not unroll 256 times. -/
theorem loopConstraints_bitrev (us : List F) (h : ∀ u ∈ us, IsDigit u) (acc : ProjectivePoint F)
    (is_first : Bool) (wx wy wz : List F) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F) :
    EcdsaLoopConstraintsF acc is_first (us.map bitrev3) wx wy wz pk rx ry pre params ↔
      LoopConstraintsOpt acc is_first us wx wy wz pk rx ry pre params := by
  induction us generalizing acc is_first wx wy wz with
  | nil => simp [EcdsaLoopConstraintsF, LoopConstraintsOpt]
  | cons u us ih =>
    cases us with
    | nil =>
      cases wx <;> cases wy <;> cases wz <;>
        simp [EcdsaLoopConstraintsF, LoopConstraintsOpt]
    | cons u' us' =>
      cases wx <;> cases wy <;> cases wz <;>
        simp only [List.map_cons, EcdsaLoopConstraintsF, LoopConstraintsOpt,
          muxPointF_bitrev3 u (h u (by simp))]
      try (refine and_congr_right fun _ => and_congr_right fun _ =>
             and_congr_right fun _ => ?_
           exact ih (fun x hx => h x (by simp [hx])) _ _ _ _ _)

/-- The computed final accumulator likewise. -/
theorem loopResult_bitrev (us : List F) (h : ∀ u ∈ us, IsDigit u) (acc : ProjectivePoint F)
    (is_first : Bool) (wx wy wz : List F) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F) :
    ecdsaLoopResultF acc is_first (us.map bitrev3) wx wy wz pk rx ry pre params =
      loopResultOpt acc is_first us wx wy wz pk rx ry pre params := by
  induction us generalizing acc is_first wx wy wz with
  | nil => simp [ecdsaLoopResultF, loopResultOpt]
  | cons u us ih =>
    cases us with
    | nil =>
      cases wx <;> cases wy <;> cases wz <;>
        simp [ecdsaLoopResultF, loopResultOpt, muxPointF_bitrev3 u (h u (by simp))]
    | cons u' us' =>
      cases wx <;> cases wy <;> cases wz <;>
        simp only [List.map_cons, ecdsaLoopResultF, loopResultOpt]
      try exact ih (fun x hx => h x (by simp [hx])) _ _ _ _ _


/-! ## The round count

The Rust loop stores **all 256** accumulators — `round[i]` for every `i` — and asserts each one.
`EcdsaLoopConstraintsF` consumes 256 digits against 255 intermediates and *computes* the last
accumulator with `ecdsaLoopResultF`. `LoopFull` is the Rust shape (equal-length lists), and
`loopFull_split` is the exchange rate: the last stored triple is exactly the computed result. -/

/-- Every round asserted, as `circuit.rs` does. -/
noncomputable def LoopFull :
    ProjectivePoint F → Bool → List F → List F → List F → List F → AffinePoint F → F → F →
      List F → CurveParameters F → Prop
  | _, _, [], [], [], [], _, _, _, _, _ => True
  | acc, is_first, u :: us, wx :: wxs, wy :: wys, wz :: wzs, pk, rx, ry, pre, params =>
    let tx := optPoint u pk rx ry pre params
    let doubled := if is_first then acc else doubleE acc params
    let nextAcc := addE doubled tx params
    nextAcc.X = wx ∧ nextAcc.Y = wy ∧ nextAcc.Z = wz ∧
    LoopFull { X := wx, Y := wy, Z := wz } false us wxs wys wzs pk rx ry pre params
  | _, _, _, _, _, _, _, _, _, _, _ => False

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
/-- **The round-count bridge.** Splitting off the last stored accumulator turns the circuit's
    256 round assertions into Lean's 255 intermediates plus the computed final value. This is
    where `ax_zero` / `az_zero` become `finalAcc.X = 0 ∧ finalAcc.Z = 0`. -/
theorem loopFull_split (us : List F) (wx wy wz : List F) (lx ly lz : F)
    (acc : ProjectivePoint F) (is_first : Bool) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F)
    (h : LoopFull acc is_first us (wx ++ [lx]) (wy ++ [ly]) (wz ++ [lz]) pk rx ry pre params) :
    LoopConstraintsOpt acc is_first us wx wy wz pk rx ry pre params ∧
      loopResultOpt acc is_first us wx wy wz pk rx ry pre params = { X := lx, Y := ly, Z := lz } := by
  induction us generalizing acc is_first wx wy wz with
  | nil =>
      -- `wx ++ [lx]` is never `[]`, so `LoopFull` lands in its `False` arm
      cases wx <;> cases wy <;> cases wz <;> simp [LoopFull] at h
  | cons u us ih =>
      cases wx with
      | nil =>
          -- the only stored accumulator left is the last one, so this must be the final digit
          cases wy with
          | cons _ _ => cases wz <;> simp [LoopFull] at h
          | nil =>
            cases wz with
            | cons _ _ => simp [LoopFull] at h
            | nil =>
              cases us with
              | cons _ _ => simp [LoopFull] at h
              | nil =>
                simp only [List.nil_append, LoopFull] at h
                obtain ⟨hx, hy, hz, -⟩ := h
                refine ⟨trivial, ?_⟩
                show addE (if is_first = true then acc else doubleE acc params)
                  (optPoint u pk rx ry pre params) params = _
                rw [← hx, ← hy, ← hz]
      | cons x xs =>
          cases wy with
          | nil => cases wz <;> simp [LoopFull] at h
          | cons y ys =>
            cases wz with
            | nil => simp [LoopFull] at h
            | cons z zs =>
              simp only [List.cons_append, LoopFull] at h
              obtain ⟨hx, hy, hz, hrest⟩ := h
              -- a stored intermediate means at least one more digit follows
              cases us with
              | nil => simp [LoopFull] at hrest
              | cons u' us' =>
                obtain ⟨hc, hr⟩ := ih (wx := xs) (wy := ys) (wz := zs) _ _ hrest
                exact ⟨⟨hx, hy, hz, hc⟩, hr⟩

omit [NeZero (3 : F)] in
/-- The image of `bitrev3` is `muxPoint`'s index range `0 … 7`, which is what
    `ValidEcdsaWitness`'s digit condition asks for. Note this is a *different* set from
    `IsDigit`, which is the lookup-node range: the circuit's wire carries `2d - 8` and Lean's
    `bi` carries the bit-reversed `d`. -/
theorem bitrev3_isIndex (u : F) (hu : IsDigit u) :
    bitrev3 u = 0 ∨ bitrev3 u = 1 ∨ bitrev3 u = 2 ∨ bitrev3 u = 3 ∨ bitrev3 u = 4 ∨
      bitrev3 u = 5 ∨ bitrev3 u = 6 ∨ bitrev3 u = 7 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩ := node_ne (F := F)
  rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [bitrev3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, if_true, if_false] <;> norm_num

/-! ## Bit order in the reconstructions

`reconstructE` / `reconstructR` / `reconstructS` fold **most-significant digit first**
(`fun acc v => acc * 2 + mux v`), while `as_eltw_unsafe` weights bit `i` by `2^i` and
`circuit.rs` fills `e_bits[i]` from `ers[i]`. Since the loop -- and hence `bi` -- runs
`i = 255 ... 0`, the same reversal that reorders the digits also reconciles the two weightings.
`bitsLE` is the least-significant-first form the circuit produces. -/

/-- Least-significant-first bit value: `b0 + 2*b1 + 4*b2 + ...`. -/
def bitsLE : List F -> F
  | [] => 0
  | b :: bs => b + 2 * bitsLE bs

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
/-- **The weighting bridge.** Horner folding over the reversed list is the circuit's
    least-significant-first sum. -/
theorem foldl_horner_reverse (bs : List F) :
    bs.reverse.foldl (fun acc b => acc * 2 + b) 0 = bitsLE bs := by
  have key : ∀ (l : List F) (a : F),
      l.reverse.foldl (fun acc b => acc * 2 + b) a = a * 2 ^ l.length + bitsLE l := by
    intro l
    induction l with
    | nil => intro a; simp [bitsLE]
    | cons b bs ih =>
        intro a
        simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.length_cons, bitsLE, ih]
        ring
  simpa using key bs 0

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
/-- The same, for the digit-indexed reconstruction `reconstructExponent` uses. -/
theorem reconstructExponent_reverse (bi : List Nat) (mux : Nat → F) :
    reconstructExponent bi.reverse mux = bitsLE (bi.map mux) := by
  have := foldl_horner_reverse (F := F) (bi.map mux)
  simpa [reconstructExponent, List.map_reverse, List.foldr_map] using this

/-! ## The assembled bridge

`soundness_of_v2` takes the deployed circuit's constraints, in the deployed circuit's own shape,
and produces the ECDSA specification. Every interface difference is discharged inside:

* the digits are bit-reversed on the way in (`muxPointF_bitrev3`);
* the 256th stored accumulator becomes Lean's computed final value (`loopFull_split`), which is
  what turns `ax_zero` / `az_zero` into `finalAcc.X = 0 ∧ finalAcc.Z = 0`;
* `yinv` is absent, because an extra constraint only strengthens the circuit.

The digit list `us` is in **loop order** — `us k` is `ers (255 - k)`, since `circuit.rs` runs
`i = 255 … 0` — and likewise for the stored accumulators. Reversing the emitted lists is the
caller's job and is a pure re-indexing.

The reconstruction hypotheses (`he`, `hr`, `hsi`, `hrlt`, `hslt`) are stated in Lean's own
vocabulary. Deriving them from the circuit's bit-sum and comparison gadgets is a separate
bridge; see the module docstring. -/
theorem soundness_of_v2
    (params : CurveParameters F) [(params.toMathlib).IsElliptic]
    [CurveHasNoPointsOfOrder2 params] (order : Nat) [Fact (Nat.Prime order)]
    (pk : AffinePoint F) (e rx ry rxinv nmsinv pkxinv : F)
    (us wxs wys wzs pre : List F) (lx ly lz : F)
    -- shapes, from the allocator
    (hus : us.length = params.kBits)
    (hwx : wxs.length = params.kBits - 1) (hwy : wys.length = params.kBits - 1)
    (hwz : wzs.length = params.kBits - 1) (hpre8 : pre.length = 8)
    -- `range_check.i/valid_index`
    (hdig : ∀ u ∈ us, IsDigit u)
    -- the 256 `slice_wx` / `slice_wy` / `slice_wz` rounds
    (hloop : LoopFull infinityPoint true us (wxs ++ [lx]) (wys ++ [ly]) (wzs ++ [lz])
      pk rx ry pre params)
    -- `ax_zero`, `az_zero`
    (hax : lx = 0) (haz : lz = 0)
    -- `slice_x` / `slice_y` on the four precomputed points, with their `is_on_curve`
    (hpre : ValidPreComputationExact pk rx ry pre params)
    -- `e_eq`, `rx_eq`
    (he : reconstructE ((us.map bitrev3).map val3) = e)
    (hr : reconstructR ((us.map bitrev3).map val3) = rx)
    -- `is_on_curve` on the public key and on R
    (hpkc : pk.IsOnCurve params) (hrc : AffinePoint.IsOnCurve ⟨rx, ry⟩ params)
    -- `rxinv`, `nmsinv`, `pkxinv`
    (hrxi : rx * rxinv = 1)
    (hsi : reconstructS ((us.map bitrev3).map val3) * nmsinv = 1)
    (hpki : pk.X * pkxinv = 1)
    -- `rx_lt_order`, `nms_lt_order`
    (hrlt : natR ((us.map bitrev3).map val3) < order)
    (hslt : natS ((us.map bitrev3).map val3) < order)
    -- curve facts, as `ecdsa_circuit_soundness` states them
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params)
    (h_pk_order : bsmul (padBits (natToBits order) params.kBits) pk.toProjective params
      = infinityPoint)
    (h_G_order : ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
      ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) infinityPoint)
    (h_R_order : ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
      ({ X := rx, Y := ry : AffinePoint F }).toProjective params) infinityPoint) :
    ∃ (r s e_nat : Nat),
      r = natR ((us.map bitrev3).map val3) ∧
      s = order - natS ((us.map bitrev3).map val3) ∧
      e_nat = natE ((us.map bitrev3).map val3) ∧
      StandardEcdsaVerify pk e_nat r s order params := by
  obtain ⟨hconstr, hres⟩ :=
    loopFull_split us wxs wys wzs lx ly lz infinityPoint true pk rx ry pre params hloop
  refine ecdsa_circuit_soundness
    { rx := rx, ry := ry, pre := pre, rx_inv := rxinv, s_inv := nmsinv, pk_inv := pkxinv,
      bi := us.map bitrev3, int_x := wxs, int_y := wys, int_z := wzs }
    pk e order params ?_ h_G_on h_pk_order h_G_order h_R_order
  refine ⟨by simpa using hus, hwx, hwy, hwz, hpre8, ?_, hpre, ?_, ?_, ?_,
    he, hr, hpkc, hrc, hrxi, hsi, hpki, hrlt, hslt⟩
  · -- digits stay digits under bit reversal
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact bitrev3_isIndex u (hdig u hu)
  · -- the round constraints, in Lean's packing
    exact (loopConstraints_bitrev us hdig infinityPoint true wxs wys wzs pk rx ry pre params).mpr
      hconstr
  · -- `ax_zero`: the computed final accumulator is the last stored one
    rw [show ecdsaLoopResultF infinityPoint true (us.map bitrev3) wxs wys wzs pk rx ry pre params
      = { X := lx, Y := ly, Z := lz } from
        (loopResult_bitrev us hdig infinityPoint true wxs wys wzs pk rx ry pre params).trans hres]
    exact hax
  · -- `az_zero`
    rw [show ecdsaLoopResultF infinityPoint true (us.map bitrev3) wxs wys wzs pk rx ry pre params
      = { X := lx, Y := ly, Z := lz } from
        (loopResult_bitrev us hdig infinityPoint true wxs wys wzs pk rx ry pre params).trans hres]
    exact haz

end ECDSA2
