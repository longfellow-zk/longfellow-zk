/-
# `z`'s linear form, as a template

The last per-instance piece of the wrapping-sum meaning. `z` (node 19753 for the `n = 2` class) is
a flat linear form over input bits; `S2TmplNat.wrap_nat_of_bits` needs it split into addend-bit
and output-bit halves.

Measured: 96 terms, 64 positive and 32 negative, coefficients powers of two summing to
`2 * (2^32 - 1)` and `2^32 - 1` -- exactly the bounds `wrap_nat_of_bits` wants, with one to spare.

`tnZ2` is stated in the `leaves ++ [sum]` shape so `ConeFlat.interpDag_leafSum` applies. That
matters: reducing the evaluation with `simp` instead is quadratic (96 operand lookups through a
97-element accumulator, ~9,300 rewrites) and leaves the goal too tangled for `ring` to close.
-/

import quadcert.Core.ConeFlat
import quadcert.Bridge.Sha256.S2TmplWrap
import quadcert.Bridge.Sha256.S2TmplNat
import quadcert.Bridge.Sha256.S2TmplBool

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {F : Type} [Field F]

theorem cnstw_pos (k m : Nat) (h : constNat k = m) : cnstw F k = (m : F) := by
  show ((constNat k : Nat) : F) = (m : F)
  rw [h]

theorem cnstw_neg [CharP F p256w] (k m : Nat) (h : constNat k = p256w - m) (hm : m ≤ p256w) :
    cnstw F k = -((m : Nat) : F) := by
  show ((constNat k : Nat) : F) = -((m : Nat) : F)
  rw [h, Quadcert.cast_sub_eq_neg p256w m hm]

/-- `z`'s 96 terms, operands in template indices. -/
def tsZ2 : List (Nat × Nat × Nat) :=
  [(32, 0, 1), (33, 0, 2), (34, 0, 3), (27, 0, 4), (28, 0, 5), (29, 0, 6), (30, 0, 7), (31, 0, 8), (21, 0, 9), (22, 0, 10), (4, 0, 11), (5, 0, 12), (6, 0, 13), (7, 0, 14), (8, 0, 15), (9, 0, 16), (10, 0, 17), (11, 0, 18), (12, 0, 19), (13, 0, 20), (14, 0, 21), (23, 0, 22), (24, 0, 23), (25, 0, 24), (15, 0, 25), (16, 0, 26), (17, 0, 27), (18, 0, 28), (19, 0, 29), (20, 0, 30), (26, 0, 31), (0, 0, 32), (0, 0, 33), (35, 0, 34), (36, 0, 35), (37, 0, 36), (38, 0, 37), (39, 0, 38), (40, 0, 39), (41, 0, 40), (42, 0, 41), (43, 0, 42), (44, 0, 43), (45, 0, 44), (46, 0, 45), (47, 0, 46), (48, 0, 47), (49, 0, 48), (50, 0, 49), (51, 0, 50), (52, 0, 51), (53, 0, 52), (54, 0, 53), (55, 0, 54), (56, 0, 55), (57, 0, 56), (58, 0, 57), (59, 0, 58), (60, 0, 59), (61, 60, 0), (62, 0, 61), (63, 0, 62), (64, 0, 63), (1, 0, 64), (2, 0, 65), (32, 0, 66), (33, 0, 67), (34, 0, 68), (27, 0, 69), (28, 0, 70), (29, 0, 71), (30, 0, 72), (31, 0, 73), (21, 0, 74), (22, 0, 75), (4, 0, 76), (5, 0, 77), (6, 0, 78), (7, 0, 79), (8, 0, 80), (9, 0, 81), (10, 0, 82), (11, 0, 83), (12, 0, 84), (13, 0, 85), (14, 0, 86), (23, 0, 87), (24, 0, 88), (25, 0, 89), (15, 0, 90), (16, 0, 91), (17, 0, 92), (18, 0, 93), (19, 0, 94), (20, 0, 95), (26, 0, 96)]

/-- The `z` cone as a flat template: 97 leaves, then the sum at index 97. -/
def tnZ2 : List TmplNode :=
  [.leaf 0, .leaf 1, .leaf 2, .leaf 3, .leaf 4, .leaf 5, .leaf 6, .leaf 7, .leaf 8, .leaf 9, .leaf 10, .leaf 11, .leaf 12, .leaf 13, .leaf 14, .leaf 15, .leaf 16, .leaf 17, .leaf 18, .leaf 19, .leaf 20, .leaf 21, .leaf 22, .leaf 23, .leaf 24, .leaf 25, .leaf 26, .leaf 27, .leaf 28, .leaf 29, .leaf 30, .leaf 31, .leaf 32, .leaf 33, .leaf 34, .leaf 35, .leaf 36, .leaf 37, .leaf 38, .leaf 39, .leaf 40, .leaf 41, .leaf 42, .leaf 43, .leaf 44, .leaf 45, .leaf 46, .leaf 47, .leaf 48, .leaf 49, .leaf 50, .leaf 51, .leaf 52, .leaf 53, .leaf 54, .leaf 55, .leaf 56, .leaf 57, .leaf 58, .leaf 59, .leaf 60, .leaf 61, .leaf 62, .leaf 63, .leaf 64, .leaf 65, .leaf 66, .leaf 67, .leaf 68, .leaf 69, .leaf 70, .leaf 71, .leaf 72, .leaf 73, .leaf 74, .leaf 75, .leaf 76, .leaf 77, .leaf 78, .leaf 79, .leaf 80, .leaf 81, .leaf 82, .leaf 83, .leaf 84, .leaf 85, .leaf 86, .leaf 87, .leaf 88, .leaf 89, .leaf 90, .leaf 91, .leaf 92, .leaf 93, .leaf 94, .leaf 95, .leaf 96, .sum tsZ2]

def csZ2 (lv : Nat → F) : List (Nat × F) :=
  [(2147483648, lv 1), (1073741824, lv 2), (536870912, lv 3), (268435456, lv 4), (134217728, lv 5), (67108864, lv 6), (33554432, lv 7), (16777216, lv 8), (8388608, lv 9), (4194304, lv 10), (2097152, lv 11), (1048576, lv 12), (524288, lv 13), (262144, lv 14), (131072, lv 15), (65536, lv 16), (32768, lv 17), (16384, lv 18), (8192, lv 19), (4096, lv 20), (2048, lv 21), (1024, lv 22), (512, lv 23), (256, lv 24), (128, lv 25), (64, lv 26), (32, lv 27), (16, lv 28), (8, lv 29), (4, lv 30), (2, lv 31), (1, lv 32), (1, lv 33), (2147483648, lv 66), (1073741824, lv 67), (536870912, lv 68), (268435456, lv 69), (134217728, lv 70), (67108864, lv 71), (33554432, lv 72), (16777216, lv 73), (8388608, lv 74), (4194304, lv 75), (2097152, lv 76), (1048576, lv 77), (524288, lv 78), (262144, lv 79), (131072, lv 80), (65536, lv 81), (32768, lv 82), (16384, lv 83), (8192, lv 84), (4096, lv 85), (2048, lv 86), (1024, lv 87), (512, lv 88), (256, lv 89), (128, lv 90), (64, lv 91), (32, lv 92), (16, lv 93), (8, lv 94), (4, lv 95), (2, lv 96)]

def dsZ2 (lv : Nat → F) : List (Nat × F) :=
  [(2147483648, lv 34), (1073741824, lv 35), (536870912, lv 36), (268435456, lv 37), (134217728, lv 38), (67108864, lv 39), (33554432, lv 40), (16777216, lv 41), (8388608, lv 42), (4194304, lv 43), (2097152, lv 44), (1048576, lv 45), (524288, lv 46), (262144, lv 47), (131072, lv 48), (65536, lv 49), (32768, lv 50), (16384, lv 51), (8192, lv 52), (4096, lv 53), (2048, lv 54), (1024, lv 55), (512, lv 56), (256, lv 57), (128, lv 58), (64, lv 59), (32, lv 60), (16, lv 61), (8, lv 62), (4, lv 63), (2, lv 64), (1, lv 65)]

/-- The instance map as a **bisection**, not a list. A list makes `coneIs` O(n^2):
    measured on a synthetic map, lookups cost 0.99 s at n=256, 18.7 s at n=1024, and
    **abort** at n=4096, while the bisection does the same in 0.14 / 1.20 / 14.2 s.
    mdoc_hash's largest assertion cone is 94,135 nodes. -/
def mapFnZ2 : Nat → Nat := fun i =>
  (if i < 49 then if i < 24 then if i < 12 then if i < 6 then if i < 3 then if i < 1 then 0 else if i < 2 then 16166 else 16169 else if i < 4 then 4297 else if i < 5 then 16176 else 5738 else if i < 9 then if i < 7 then 16181 else if i < 8 then 16184 else 16188 else if i < 10 then 184 else if i < 11 then 16195 else 16198 else if i < 18 then if i < 15 then if i < 13 then 16202 else if i < 14 then 16206 else 16210 else if i < 16 then 16214 else if i < 17 then 16218 else 16221 else if i < 21 then if i < 19 then 16225 else if i < 20 then 11554 else 16230 else if i < 22 then 16233 else if i < 23 then 14930 else 16240 else if i < 36 then if i < 30 then if i < 27 then if i < 25 then 13312 else if i < 26 then 13552 else 3144 else if i < 28 then 16251 else if i < 29 then 16255 else 3181 else if i < 33 then if i < 31 then 11815 else if i < 32 then 16263 else 16269 else if i < 34 then 12304 else if i < 35 then 19707 else 11767 else if i < 42 then if i < 39 then if i < 37 then 12639 else if i < 38 then 7400 else 12658 else if i < 40 then 19708 else if i < 41 then 19709 else 19710 else if i < 45 then if i < 43 then 19711 else if i < 44 then 19712 else 19713 else if i < 47 then if i < 46 then 19714 else 19715 else if i < 48 then 19716 else 19717 else if i < 73 then if i < 61 then if i < 55 then if i < 52 then if i < 50 then 19718 else if i < 51 then 15652 else 19719 else if i < 53 then 19720 else if i < 54 then 19721 else 19722 else if i < 58 then if i < 56 then 5747 else if i < 57 then 19248 else 19723 else if i < 59 then 19724 else if i < 60 then 19725 else 19726 else if i < 67 then if i < 64 then if i < 62 then 19727 else if i < 63 then 19728 else 19729 else if i < 65 then 19730 else if i < 66 then 8808 else 16693 else if i < 70 then if i < 68 then 19731 else if i < 69 then 19732 else 19733 else if i < 71 then 5704 else if i < 72 then 14383 else 9984 else if i < 85 then if i < 79 then if i < 76 then if i < 74 then 19734 else if i < 75 then 14862 else 19735 else if i < 77 then 19736 else if i < 78 then 19737 else 19738 else if i < 82 then if i < 80 then 19739 else if i < 81 then 19740 else 19741 else if i < 83 then 19742 else if i < 84 then 15267 else 19743 else if i < 91 then if i < 88 then if i < 86 then 19441 else if i < 87 then 19744 else 3806 else if i < 89 then 19745 else if i < 90 then 19746 else 19747 else if i < 94 then if i < 92 then 19748 else if i < 93 then 19749 else 15682 else if i < 96 then if i < 95 then 19750 else 19751 else if i < 97 then 19752 else 19753)

/-- The instance map as a list, for the composed proof. -/
def mpZ2 : List Nat :=
  [0, 16166, 16169, 4297, 16176, 5738, 16181, 16184, 16188, 184, 16195, 16198, 16202, 16206, 16210, 16214, 16218, 16221, 16225, 11554, 16230, 16233, 14930, 16240, 13312, 13552, 3144, 16251, 16255, 3181, 11815, 16263, 16269, 12304, 19707, 11767, 12639, 7400, 12658, 19708, 19709, 19710, 19711, 19712, 19713, 19714, 19715, 19716, 19717, 19718, 15652, 19719, 19720, 19721, 19722, 5747, 19248, 19723, 19724, 19725, 19726, 19727, 19728, 19729, 19730, 8808, 16693, 19731, 19732, 19733, 5704, 14383, 9984, 19734, 14862, 19735, 19736, 19737, 19738, 19739, 19740, 19741, 19742, 15267, 19743, 19441, 19744, 3806, 19745, 19746, 19747, 19748, 19749, 15682, 19750, 19751, 19752, 19753]

/-- **`z` as a difference of two bit-linear forms.** -/
theorem tmpl_z2 [CharP F p256w] (lv : Nat → F) (hone : lv 0 = 1) :
    interpDag (tmplDag (cnstw F) tnZ2) lv 97
      = ((csZ2 lv).map (fun q => (q.1 : F) * q.2)).sum
        - ((dsZ2 lv).map (fun q => (q.1 : F) * q.2)).sum := by
  rw [show tnZ2 = (List.range 97).map (fun i => (TmplNode.leaf i : TmplNode))
        ++ [TmplNode.sum tsZ2] from rfl,
    interpDag_leafSum (cnstw F) lv 97 tsZ2 (by decide)]
  have c0 : cnstw F 0 = ((1 : Nat) : F) := cnstw_pos 0 1 (by rfl)
  have c1 : cnstw F 1 = -((2 : Nat) : F) := cnstw_neg 1 2 (by rfl) (by norm_num)
  have c2 : cnstw F 2 = -((1 : Nat) : F) := cnstw_neg 2 1 (by rfl) (by norm_num)
  have c4 : cnstw F 4 = ((2097152 : Nat) : F) := cnstw_pos 4 2097152 (by rfl)
  have c5 : cnstw F 5 = ((1048576 : Nat) : F) := cnstw_pos 5 1048576 (by rfl)
  have c6 : cnstw F 6 = ((524288 : Nat) : F) := cnstw_pos 6 524288 (by rfl)
  have c7 : cnstw F 7 = ((262144 : Nat) : F) := cnstw_pos 7 262144 (by rfl)
  have c8 : cnstw F 8 = ((131072 : Nat) : F) := cnstw_pos 8 131072 (by rfl)
  have c9 : cnstw F 9 = ((65536 : Nat) : F) := cnstw_pos 9 65536 (by rfl)
  have c10 : cnstw F 10 = ((32768 : Nat) : F) := cnstw_pos 10 32768 (by rfl)
  have c11 : cnstw F 11 = ((16384 : Nat) : F) := cnstw_pos 11 16384 (by rfl)
  have c12 : cnstw F 12 = ((8192 : Nat) : F) := cnstw_pos 12 8192 (by rfl)
  have c13 : cnstw F 13 = ((4096 : Nat) : F) := cnstw_pos 13 4096 (by rfl)
  have c14 : cnstw F 14 = ((2048 : Nat) : F) := cnstw_pos 14 2048 (by rfl)
  have c15 : cnstw F 15 = ((128 : Nat) : F) := cnstw_pos 15 128 (by rfl)
  have c16 : cnstw F 16 = ((64 : Nat) : F) := cnstw_pos 16 64 (by rfl)
  have c17 : cnstw F 17 = ((32 : Nat) : F) := cnstw_pos 17 32 (by rfl)
  have c18 : cnstw F 18 = ((16 : Nat) : F) := cnstw_pos 18 16 (by rfl)
  have c19 : cnstw F 19 = ((8 : Nat) : F) := cnstw_pos 19 8 (by rfl)
  have c20 : cnstw F 20 = ((4 : Nat) : F) := cnstw_pos 20 4 (by rfl)
  have c21 : cnstw F 21 = ((8388608 : Nat) : F) := cnstw_pos 21 8388608 (by rfl)
  have c22 : cnstw F 22 = ((4194304 : Nat) : F) := cnstw_pos 22 4194304 (by rfl)
  have c23 : cnstw F 23 = ((1024 : Nat) : F) := cnstw_pos 23 1024 (by rfl)
  have c24 : cnstw F 24 = ((512 : Nat) : F) := cnstw_pos 24 512 (by rfl)
  have c25 : cnstw F 25 = ((256 : Nat) : F) := cnstw_pos 25 256 (by rfl)
  have c26 : cnstw F 26 = ((2 : Nat) : F) := cnstw_pos 26 2 (by rfl)
  have c27 : cnstw F 27 = ((268435456 : Nat) : F) := cnstw_pos 27 268435456 (by rfl)
  have c28 : cnstw F 28 = ((134217728 : Nat) : F) := cnstw_pos 28 134217728 (by rfl)
  have c29 : cnstw F 29 = ((67108864 : Nat) : F) := cnstw_pos 29 67108864 (by rfl)
  have c30 : cnstw F 30 = ((33554432 : Nat) : F) := cnstw_pos 30 33554432 (by rfl)
  have c31 : cnstw F 31 = ((16777216 : Nat) : F) := cnstw_pos 31 16777216 (by rfl)
  have c32 : cnstw F 32 = ((2147483648 : Nat) : F) := cnstw_pos 32 2147483648 (by rfl)
  have c33 : cnstw F 33 = ((1073741824 : Nat) : F) := cnstw_pos 33 1073741824 (by rfl)
  have c34 : cnstw F 34 = ((536870912 : Nat) : F) := cnstw_pos 34 536870912 (by rfl)
  have c35 : cnstw F 35 = -((2147483648 : Nat) : F) := cnstw_neg 35 2147483648 (by rfl) (by norm_num)
  have c36 : cnstw F 36 = -((1073741824 : Nat) : F) := cnstw_neg 36 1073741824 (by rfl) (by norm_num)
  have c37 : cnstw F 37 = -((536870912 : Nat) : F) := cnstw_neg 37 536870912 (by rfl) (by norm_num)
  have c38 : cnstw F 38 = -((268435456 : Nat) : F) := cnstw_neg 38 268435456 (by rfl) (by norm_num)
  have c39 : cnstw F 39 = -((134217728 : Nat) : F) := cnstw_neg 39 134217728 (by rfl) (by norm_num)
  have c40 : cnstw F 40 = -((67108864 : Nat) : F) := cnstw_neg 40 67108864 (by rfl) (by norm_num)
  have c41 : cnstw F 41 = -((33554432 : Nat) : F) := cnstw_neg 41 33554432 (by rfl) (by norm_num)
  have c42 : cnstw F 42 = -((16777216 : Nat) : F) := cnstw_neg 42 16777216 (by rfl) (by norm_num)
  have c43 : cnstw F 43 = -((8388608 : Nat) : F) := cnstw_neg 43 8388608 (by rfl) (by norm_num)
  have c44 : cnstw F 44 = -((4194304 : Nat) : F) := cnstw_neg 44 4194304 (by rfl) (by norm_num)
  have c45 : cnstw F 45 = -((2097152 : Nat) : F) := cnstw_neg 45 2097152 (by rfl) (by norm_num)
  have c46 : cnstw F 46 = -((1048576 : Nat) : F) := cnstw_neg 46 1048576 (by rfl) (by norm_num)
  have c47 : cnstw F 47 = -((524288 : Nat) : F) := cnstw_neg 47 524288 (by rfl) (by norm_num)
  have c48 : cnstw F 48 = -((262144 : Nat) : F) := cnstw_neg 48 262144 (by rfl) (by norm_num)
  have c49 : cnstw F 49 = -((131072 : Nat) : F) := cnstw_neg 49 131072 (by rfl) (by norm_num)
  have c50 : cnstw F 50 = -((65536 : Nat) : F) := cnstw_neg 50 65536 (by rfl) (by norm_num)
  have c51 : cnstw F 51 = -((32768 : Nat) : F) := cnstw_neg 51 32768 (by rfl) (by norm_num)
  have c52 : cnstw F 52 = -((16384 : Nat) : F) := cnstw_neg 52 16384 (by rfl) (by norm_num)
  have c53 : cnstw F 53 = -((8192 : Nat) : F) := cnstw_neg 53 8192 (by rfl) (by norm_num)
  have c54 : cnstw F 54 = -((4096 : Nat) : F) := cnstw_neg 54 4096 (by rfl) (by norm_num)
  have c55 : cnstw F 55 = -((2048 : Nat) : F) := cnstw_neg 55 2048 (by rfl) (by norm_num)
  have c56 : cnstw F 56 = -((1024 : Nat) : F) := cnstw_neg 56 1024 (by rfl) (by norm_num)
  have c57 : cnstw F 57 = -((512 : Nat) : F) := cnstw_neg 57 512 (by rfl) (by norm_num)
  have c58 : cnstw F 58 = -((256 : Nat) : F) := cnstw_neg 58 256 (by rfl) (by norm_num)
  have c59 : cnstw F 59 = -((128 : Nat) : F) := cnstw_neg 59 128 (by rfl) (by norm_num)
  have c60 : cnstw F 60 = -((64 : Nat) : F) := cnstw_neg 60 64 (by rfl) (by norm_num)
  have c61 : cnstw F 61 = -((32 : Nat) : F) := cnstw_neg 61 32 (by rfl) (by norm_num)
  have c62 : cnstw F 62 = -((16 : Nat) : F) := cnstw_neg 62 16 (by rfl) (by norm_num)
  have c63 : cnstw F 63 = -((8 : Nat) : F) := cnstw_neg 63 8 (by rfl) (by norm_num)
  have c64 : cnstw F 64 = -((4 : Nat) : F) := cnstw_neg 64 4 (by rfl) (by norm_num)
  simp only [tsZ2, csZ2, dsZ2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.foldl_cons, List.foldl_nil, hone, c0, c1, c2, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64]
  push_cast
  ring

/-- `(booleanity assertion, bit)` for each of `z`'s 96 addend and output bits, in
    `csZ2 ++ dsZ2` order. -/
def boolPairsZ2 : List (Nat × Nat) :=
  [(35396, 16166), (32797, 16169), (4298, 4297), (31424, 16176), (5739, 5738), (25633, 16181), (36480, 16184), (31622, 16188), (185, 184), (24288, 16195), (31241, 16198), (19326, 16202), (32466, 16206), (28618, 16210), (34660, 16214), (32358, 16218), (36114, 16221), (34662, 16225), (11555, 11554), (25986, 16230), (28821, 16233), (14931, 14930), (34684, 16240), (13313, 13312), (13553, 13552), (3145, 3144), (18522, 16251), (28843, 16255), (3182, 3181), (11816, 11815), (33927, 16263), (19564, 16269), (12305, 12304), (16694, 16693), (28121, 19731), (26004, 19732), (26553, 19733), (5705, 5704), (14384, 14383), (9985, 9984), (28857, 19734), (14863, 14862), (34720, 19735), (24046, 19736), (25092, 19737), (21290, 19738), (20226, 19739), (20612, 19740), (29741, 19741), (32691, 19742), (15268, 15267), (33024, 19743), (19442, 19441), (25742, 19744), (3807, 3806), (29912, 19745), (25547, 19746), (24306, 19747), (25042, 19748), (25776, 19749), (15683, 15682), (22525, 19750), (24981, 19751), (24366, 19752), (31656, 19707), (11768, 11767), (12640, 12639), (7401, 7400), (12659, 12658), (21004, 19708), (27662, 19709), (30551, 19710), (25992, 19711), (29786, 19712), (36160, 19713), (23623, 19714), (27265, 19715), (20166, 19716), (27077, 19717), (22329, 19718), (15653, 15652), (26282, 19719), (31620, 19720), (26268, 19721), (24054, 19722), (5748, 5747), (19249, 19248), (30573, 19723), (24799, 19724), (36750, 19725), (37067, 19726), (35518, 19727), (27249, 19728), (33370, 19729), (33038, 19730), (8809, 8808)]

/-- **Booleanity for all 96 bits, discharged from their assertions.** One `decide` covers every
    node shape; the per-bit step is a numeric index, not a list membership. -/
theorem bitsZ2 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < boolPairsZ2.length →
      interpDag (raw.toDag (cnstw F)) inputs (boolPairsZ2.getD j (0, 0)).1 = 0) :
    ∀ q ∈ csZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0))
              ++ dsZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0)),
      q.2 = 0 ∨ q.2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have h : constNat 2 = p256w - 1 := by rfl
    rw [h, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : boolPairsZ2.all
      (fun p => nodeEq (nodeFn p.1) (.sum [(0, 0, p.2), (2, p.2, p.2)])) = true := by
    decide +kernel
  have hltc : boolPairsZ2.all
      (fun p => decide (p.2 < p.1) && decide (p.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hbits := bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2
    hone boolPairsZ2 hshape hltc hbz
  have hlen : boolPairsZ2.length = 96 := by rfl
  have hb : ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs (boolPairsZ2.getD j (0, 0)).2 = 0
        ∨ interpDag (raw.toDag (cnstw F)) inputs (boolPairsZ2.getD j (0, 0)).2 = 1 := by
    intro j hj; exact hbits j (by rw [hlen]; exact hj)
  intro q hq
  simp only [csZ2, dsZ2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  · simpa [boolPairsZ2, mpZ2] using hb 0 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 1 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 2 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 3 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 4 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 5 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 6 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 7 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 8 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 9 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 10 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 11 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 12 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 13 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 14 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 15 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 16 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 17 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 18 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 19 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 20 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 21 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 22 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 23 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 24 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 25 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 26 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 27 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 28 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 29 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 30 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 31 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 32 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 33 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 34 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 35 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 36 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 37 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 38 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 39 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 40 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 41 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 42 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 43 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 44 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 45 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 46 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 47 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 48 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 49 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 50 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 51 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 52 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 53 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 54 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 55 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 56 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 57 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 58 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 59 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 60 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 61 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 62 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 63 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 64 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 65 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 66 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 67 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 68 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 69 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 70 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 71 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 72 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 73 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 74 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 75 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 76 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 77 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 78 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 79 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 80 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 81 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 82 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 83 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 84 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 85 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 86 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 87 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 88 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 89 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 90 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 91 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 92 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 93 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 94 (by norm_num)
  · simpa [boolPairsZ2, mpZ2] using hb 95 (by norm_num)

/-- The bisection form works for `coneIs` itself -- kept as evidence, since it is what a
    generator should emit at scale. Measured on synthetic maps: list lookups cost 0.99 s at
    n=256, 18.7 s at n=1024 and **abort** at n=4096, against 0.14 / 1.20 / 14.2 s for the
    bisection. At this instance's n=98 the list is fine, and the composed proof below prefers it:
    an if-tree gets duplicated into subterms where a list literal is shared. -/
theorem coneOK_bisect : coneIs nodeFn tnZ2 mapFnZ2 = true := by decide +kernel

/-- **The whole thing, end to end.** The `n = 2` wrapping-sum assertion at node 19756, from
    "the asserted node is zero" to 32-bit arithmetic. Booleanity of the 96 addend and output bits
    is supplied separately -- each is an `is_boolean` assertion discharged by
    `S2TmplBool.tmpl_isBool`. -/
theorem wrap_arith_19756 [CharP F p256w] (inputs : Nat → F)
    (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < boolPairsZ2.length →
      interpDag (raw.toDag (cnstw F)) inputs (boolPairsZ2.getD j (0, 0)).1 = 0)
    (hroot : interpDag (raw.toDag (cnstw F)) inputs 19756 = 0) :
    ∃ C P : Nat,
      ((csZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0))).map
        (fun q => (q.1 : F) * q.2)).sum = (C : F) ∧
      ((dsZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0))).map
        (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      P = C % 2 ^ 32 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  -- the z cone, matched and transported
  have hconeZ : coneIs nodeFn tnZ2 (fun i => mpZ2.getD i 0) = true := by decide +kernel
  have hmapZ : ∀ i, i < tnZ2.length → mpZ2.getD i 0 < raw.nodes.length := by
    intro i hi
    have h97 : tnZ2.length = 98 := by rfl
    rw [h97] at hi
    rw [nodes_len]
    have hb : (List.range 98).all (fun j => decide (mpZ2.getD j 0 < 37139)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
    exact hb i hi
  have htrZ := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnZ2 (fun i => mpZ2.getD i 0) hconeZ hmapZ 97
    (by decide)
  have honeZ : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0)) 0 = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hzval : interpDag (raw.toDag (cnstw F)) inputs 19753
      = ((csZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0))).map
          (fun q => (q.1 : F) * q.2)).sum
        - ((dsZ2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0))).map
          (fun q => (q.1 : F) * q.2)).sum := by
    have := htrZ
    show interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD 97 0) = _
    rw [this, tmpl_z2 (fun h => interpDag (raw.toDag (cnstw F)) inputs (mpZ2.getD h 0)) honeZ]
  refine SHA256F.wrap_nat_of_bits 2 _ _ _ ?_ ?_ ?_ ?_ (SHA256F.wrap_hnp 2 (by norm_num)) hzval
    (wrap_19756 inputs hin0 hroot)
  · intro q hq; exact bitsZ2 inputs hin0 hbz q (List.mem_append_left _ hq)
  · intro q hq; exact bitsZ2 inputs hin0 hbz q (List.mem_append_right _ hq)
  · simp [csZ2]
  · simp [dsZ2]

end Sha256Blk
