/-
# The wrapping-sum template lemma (n = 2)

`assert_wrapping_sum_prime` is the only assertion family in the SHA-256 circuit with arithmetic
content -- the other 6,656 are booleanity. It builds `z = c - p` and asserts
`∏_{i<n} (z - i · 2^32) = 0`, with `n = 2` for the eight `final` assertions, 4 for the 48
`schedule` ones and 6 for the 128 `round_step` ones.

**The cut at `z` is what makes this tractable.** The full cone of a `final` assertion is 102
nodes, but `z` (node 19753 in the instance below) is a 97-term flat sum, and expanding the
product through it is what `S2Meaning` measured at 10^16 leaves. Treating `z` as a *hole* leaves
a six-node template:

```
  238    sum [(0,0,0)]                      -- consts 0 * 1 * 1        = 1
  19754  sum [(0,238,19753)]                -- 1 * 1 * z               = z - 0*2^32
  19755  sum [(65,238,238),(0,238,19753)]   -- consts 65 + z           = z - 1*2^32
  19756  sum [(0,19754,19755)]              -- the product
```

`constNat 65 = p - 2^32`, so `consts 65 = -(2^32)`. The circuit associates the product as
`z * (z - 2^32)` while `wrapPoly` recurses the other way; the docstring in `SHA/Wrap.lean` warns
that nothing may assume a particular association, so the two are reconciled by `ring` rather than
by matching shapes.

This lemma is the *field* half. `SHA256F.wrap_sum_of_zero` supplies the `Nat` half, and needs
three facts this template cannot provide -- `C < n·2^32`, `P < 2^32`, `n·2^32 ≤ p` -- which are
per-instance data about the addends, not properties of the cone shape.
-/

import quadcert.Core.ConeTmpl
import quadcert.Gen.Sha256Blk.Sha256BlkNodeChk
import SHA.Wrap

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

abbrev p256w : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

variable {F : Type} [Field F]

def cnstw (F : Type) [Field F] : Nat → F := fun i => (constNat i : F)

theorem cnstw_0 : cnstw F 0 = 1 := by
  show ((constNat 0 : Nat) : F) = 1
  have h : constNat 0 = 1 := by rfl
  rw [h, Nat.cast_one]

theorem cnstw_65 [CharP F p256w] : cnstw F 65 = -((2 ^ 32 : Nat) : F) := by
  show ((constNat 65 : Nat) : F) = -((2 ^ 32 : Nat) : F)
  have h : constNat 65 = p256w - 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (2 ^ 32) (by norm_num)]

/-- The `n = 2` wrapping-sum template, cut at `z`. Index 0 is the constant-1 input, index 1 is
    the hole for `z`, index 5 is the asserted node. -/
def tnWrap2 : List TmplNode :=
  [.leaf 0, .leaf 1,
   .sum [(0, 0, 0)],
   .sum [(0, 2, 1)],
   .sum [(65, 2, 2), (0, 2, 1)],
   .sum [(0, 3, 4)]]

/-- **The template lemma.** Proven once; each of the eight `final` assertions instantiates it. -/
theorem tmpl_wrap2 (consts lv : Nat → F)
    (h0 : consts 0 = 1) (h65 : consts 65 = -((2 ^ 32 : Nat) : F)) (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnWrap2) lv 5 = 0) :
    SHA256F.wrapPoly 2 ((2 ^ 32 : Nat) : F) (lv 1) = 0 := by
  have hval : interpDag (tmplDag consts tnWrap2) lv 5
      = consts 0 * (consts 0 * (consts 0 * lv 0 * lv 0) * lv 1)
          * (consts 65 * (consts 0 * lv 0 * lv 0) * (consts 0 * lv 0 * lv 0)
             + consts 0 * (consts 0 * lv 0 * lv 0) * lv 1) := by
    simp [interpDag, interpDagAux, nodeValue, tmplDag, tnWrap2, List.getD]
  rw [hval, h0, h65, hone] at hroot
  simp only [SHA256F.wrapPoly, Nat.cast_one, Nat.cast_zero]
  linear_combination hroot


theorem cnstw_66 [CharP F p256w] : cnstw F 66 = -((3 * 2 ^ 32 : Nat) : F) := by
  show ((constNat 66 : Nat) : F) = -((3 * 2 ^ 32 : Nat) : F)
  have h : constNat 66 = p256w - 3 * 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (3 * 2 ^ 32) (by norm_num)]

theorem cnstw_67 [CharP F p256w] : cnstw F 67 = -((2 * 2 ^ 32 : Nat) : F) := by
  show ((constNat 67 : Nat) : F) = -((2 * 2 ^ 32 : Nat) : F)
  have h : constNat 67 = p256w - 2 * 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (2 * 2 ^ 32) (by norm_num)]

theorem cnstw_68 [CharP F p256w] : cnstw F 68 = -((5 * 2 ^ 32 : Nat) : F) := by
  show ((constNat 68 : Nat) : F) = -((5 * 2 ^ 32 : Nat) : F)
  have h : constNat 68 = p256w - 5 * 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (5 * 2 ^ 32) (by norm_num)]

theorem cnstw_69 [CharP F p256w] : cnstw F 69 = -((4 * 2 ^ 32 : Nat) : F) := by
  show ((constNat 69 : Nat) : F) = -((4 * 2 ^ 32 : Nat) : F)
  have h : constNat 69 = p256w - 4 * 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (4 * 2 ^ 32) (by norm_num)]

theorem cnstw_70 [CharP F p256w] : cnstw F 70 = -((6 * 2 ^ 32 : Nat) : F) := by
  show ((constNat 70 : Nat) : F) = -((6 * 2 ^ 32 : Nat) : F)
  have h : constNat 70 = p256w - 6 * 2 ^ 32 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256w (6 * 2 ^ 32) (by norm_num)]

def tnWrap4 : List TmplNode :=
  [.leaf 0, .sum [(0, 0, 0)], .sum [(0, 1, 1)], .leaf 3, .sum [(66, 2, 2), (0, 2, 3)], .sum [(67, 2, 2), (0, 2, 3)], .sum [(0, 4, 5)], .sum [(0, 2, 3)], .sum [(65, 2, 2), (0, 2, 3)], .sum [(0, 7, 8)], .sum [(0, 6, 9)]]

/-- **n = 4** (schedule, 48 assertions). Product tree above `z`; `z` stays a hole. -/
theorem tmpl_wrap4 (consts lv : Nat → F)
    (h0 : consts 0 = 1)
    (h65 : consts 65 = -((1 * 2 ^ 32 : Nat) : F))
    (h66 : consts 66 = -((3 * 2 ^ 32 : Nat) : F))
    (h67 : consts 67 = -((2 * 2 ^ 32 : Nat) : F))
    (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnWrap4) lv 10 = 0) :
    SHA256F.wrapPoly 4 ((2 ^ 32 : Nat) : F) (lv 3) = 0 := by
  simp [interpDag, interpDagAux, nodeValue, tmplDag, tnWrap4, List.getD,
    h0, h65, h66, h67, hone, -mul_eq_zero] at hroot
  simp only [SHA256F.wrapPoly]
  push_cast at hroot ⊢
  linear_combination hroot

def tnWrap6 : List TmplNode :=
  [.leaf 0, .sum [(0, 0, 0)], .sum [(0, 1, 1)], .leaf 3, .sum [(68, 2, 2), (0, 2, 3)], .sum [(69, 2, 2), (0, 2, 3)], .sum [(0, 4, 5)], .sum [(0, 2, 2)], .sum [(66, 2, 2), (0, 2, 3)], .sum [(0, 7, 8)], .sum [(0, 6, 9)], .sum [(67, 2, 2), (0, 2, 3)], .sum [(65, 2, 2), (0, 2, 3)], .sum [(0, 11, 12)], .sum [(0, 2, 3)], .sum [(0, 7, 14)], .sum [(0, 13, 15)], .sum [(0, 10, 16)]]

/-- **n = 6** (round_step, 64 assertions). Product tree above `z`; `z` stays a hole. -/
theorem tmpl_wrap6 (consts lv : Nat → F)
    (h0 : consts 0 = 1)
    (h65 : consts 65 = -((1 * 2 ^ 32 : Nat) : F))
    (h66 : consts 66 = -((3 * 2 ^ 32 : Nat) : F))
    (h67 : consts 67 = -((2 * 2 ^ 32 : Nat) : F))
    (h68 : consts 68 = -((5 * 2 ^ 32 : Nat) : F))
    (h69 : consts 69 = -((4 * 2 ^ 32 : Nat) : F))
    (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnWrap6) lv 17 = 0) :
    SHA256F.wrapPoly 6 ((2 ^ 32 : Nat) : F) (lv 3) = 0 := by
  simp [interpDag, interpDagAux, nodeValue, tmplDag, tnWrap6, List.getD,
    h0, h65, h66, h67, h68, h69, hone, -mul_eq_zero] at hroot
  simp only [SHA256F.wrapPoly]
  push_cast at hroot ⊢
  linear_combination hroot

def tnWrap7 : List TmplNode :=
  [.leaf 0, .sum [(0, 0, 0)], .sum [(0, 1, 1)], .leaf 3, .sum [(70, 2, 2), (0, 2, 3)], .sum [(68, 2, 2), (0, 2, 3)], .sum [(0, 4, 5)], .sum [(69, 2, 2), (0, 2, 3)], .sum [(66, 2, 2), (0, 2, 3)], .sum [(0, 7, 8)], .sum [(0, 6, 9)], .sum [(67, 2, 2), (0, 2, 3)], .sum [(65, 2, 2), (0, 2, 3)], .sum [(0, 11, 12)], .sum [(0, 2, 2)], .sum [(0, 2, 3)], .sum [(0, 14, 15)], .sum [(0, 13, 16)], .sum [(0, 10, 17)]]

/-- **n = 7** (round_step, 64 assertions). Product tree above `z`; `z` stays a hole. -/
theorem tmpl_wrap7 (consts lv : Nat → F)
    (h0 : consts 0 = 1)
    (h65 : consts 65 = -((1 * 2 ^ 32 : Nat) : F))
    (h66 : consts 66 = -((3 * 2 ^ 32 : Nat) : F))
    (h67 : consts 67 = -((2 * 2 ^ 32 : Nat) : F))
    (h68 : consts 68 = -((5 * 2 ^ 32 : Nat) : F))
    (h69 : consts 69 = -((4 * 2 ^ 32 : Nat) : F))
    (h70 : consts 70 = -((6 * 2 ^ 32 : Nat) : F))
    (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnWrap7) lv 18 = 0) :
    SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F) (lv 3) = 0 := by
  simp [interpDag, interpDagAux, nodeValue, tmplDag, tnWrap7, List.getD,
    h0, h65, h66, h67, h68, h69, h70, hone, -mul_eq_zero] at hroot
  simp only [SHA256F.wrapPoly]
  push_cast at hroot ⊢
  linear_combination hroot

/-- **One instance, end to end.** Assertion node 19756 -- one of the eight `final` wrapping
    sums -- matched by `decide` and transported through `coneIs_transfer`. The 97-term `z` node
    is never expanded: it stays a hole, and its value appears in the conclusion as
    `interpDag ... 19753`. -/
theorem wrap_19756 [CharP F p256w] (inputs : Nat → F)
    (hin0 : inputs 0 = 1)
    (hroot : interpDag (raw.toDag (cnstw F)) inputs 19756 = 0) :
    SHA256F.wrapPoly 2 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs 19753) = 0 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hcone : coneIs nodeFn tnWrap2 (fun i => ([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD i 0) = true := by
    decide +kernel
  have hmap : ∀ i, i < tnWrap2.length →
      ([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD i 0 < raw.nodes.length := by
    intro i hi
    have h6 : tnWrap2.length = 6 := rfl
    rw [h6] at hi
    rw [nodes_len]
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
  have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap2
      (fun i => ([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD i 0) hcone hmap 5 (by decide)
  have hlv0 : interpDag (raw.toDag (cnstw F)) inputs
      (([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD 0 0) = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hz : interpDag (tmplDag (cnstw F) tnWrap2)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs
        (([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD h 0)) 5 = 0 := by
    rw [← htr]; exact hroot
  exact tmpl_wrap2 (cnstw F)
    (fun h => interpDag (raw.toDag (cnstw F)) inputs
      (([0, 19753, 238, 19754, 19755, 19756] : List Nat).getD h 0))
    cnstw_0 cnstw_65 hlv0 hz

/-- The mirrored `n = 7` tree. Round 5's `a` assertion is the one instance of the 128 whose
    product tree the compiler emitted with the operands the other way round -- `(0,z,1)` before
    `(k,1,1)` rather than after. Same polynomial, different operand list, and `coneIs` compares
    operand lists exactly, so it needs its own template. -/
def tnWrap7b : List TmplNode :=
  [.leaf 0, .sum [(0, 0, 0)], .sum [(0, 1, 1)], .leaf 3, .sum [(0, 3, 2), (70, 2, 2)], .sum [(0, 3, 2), (68, 2, 2)], .sum [(0, 4, 5)], .sum [(0, 3, 2), (69, 2, 2)], .sum [(0, 3, 2), (66, 2, 2)], .sum [(0, 7, 8)], .sum [(0, 6, 9)], .sum [(0, 3, 2), (67, 2, 2)], .sum [(0, 3, 2), (65, 2, 2)], .sum [(0, 11, 12)], .sum [(0, 2, 2)], .sum [(0, 3, 2)], .sum [(0, 15, 14)], .sum [(0, 13, 16)], .sum [(0, 10, 17)]]

theorem tmpl_wrap7b (consts lv : Nat → F)
    (h0 : consts 0 = 1)
    (h65 : consts 65 = -((1 * 2 ^ 32 : Nat) : F))
    (h66 : consts 66 = -((3 * 2 ^ 32 : Nat) : F))
    (h67 : consts 67 = -((2 * 2 ^ 32 : Nat) : F))
    (h68 : consts 68 = -((5 * 2 ^ 32 : Nat) : F))
    (h69 : consts 69 = -((4 * 2 ^ 32 : Nat) : F))
    (h70 : consts 70 = -((6 * 2 ^ 32 : Nat) : F))
    (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnWrap7b) lv 18 = 0) :
    SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F) (lv 3) = 0 := by
  simp [interpDag, interpDagAux, nodeValue, tmplDag, tnWrap7b, List.getD,
    h0, h65, h66, h67, h68, h69, h70, hone, -mul_eq_zero] at hroot
  simp only [SHA256F.wrapPoly]
  push_cast at hroot ⊢
  linear_combination hroot

end Sha256Blk
