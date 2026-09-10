/-
# The `is_boolean` template lemma

One lemma for **6,656 of SHA-256's 6,840 assertions**, and **284,707 of mdoc_hash's 303,413**
(94%). Every one of them has the same 3-node cone:

```
  node 0      input 0                                  -- the constant-1 input
  node x      input k                                  -- the bit
  node r      sum [(0, 0, x), (2, x, x)]               -- consts 0 * 1 * x + consts 2 * x * x
```

`constNat 0 = 1` and `constNat 2 = p - 1`, so the node computes `x - x*x` and the assertion is
exactly the hypothesis of `SHA256F.isBit_of_zero_raw`.

The point is that this is proven **once**. An individual assertion is discharged by matching its
cone against `tnBool` with `decide +kernel` and transporting through `coneIs_transfer` -- no
per-node value chain, and no algebra repeated per instance.
-/

import quadcert.Core.ConeTmpl
import quadcert.Gen.Sha256Blk.Sha256BlkNodeChk
import SHA.Field

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- P-256's characteristic, as the constant table encodes it. -/
abbrev p256 : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

variable {F : Type} [Field F]

/-- The generated constant table, cast into the field. -/
def cnst (F : Type) [Field F] : Nat → F := fun i => (constNat i : F)

theorem cnst_0 : cnst F 0 = 1 := by
  show ((constNat 0 : Nat) : F) = 1
  have h : constNat 0 = 1 := by rfl
  rw [h, Nat.cast_one]

theorem cnst_2 [CharP F p256] : cnst F 2 = -1 := by
  show ((constNat 2 : Nat) : F) = -1
  have h : constNat 2 = p256 - 1 := by rfl
  rw [h, Quadcert.cast_sub_eq_neg p256 1 (by norm_num), Nat.cast_one]

/-- **The `is_boolean` cone template.** Index 0 is the constant-1 input, index 1 the bit,
    index 2 the asserted node. -/
def tnBool : List TmplNode :=
  [.leaf 0, .leaf 1, .sum [(0, 0, 1), (2, 1, 1)]]

/-- **The template lemma.** Proven once; every `is_boolean` assertion instantiates it. -/
theorem tmpl_isBool (consts lv : Nat → F)
    (h0 : consts 0 = 1) (h2 : consts 2 = -1) (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag consts tnBool) lv 2 = 0) :
    lv 1 = 0 ∨ lv 1 = 1 := by
  refine SHA256F.isBit_of_zero_raw (lv 1) ?_
  have hval : interpDag (tmplDag consts tnBool) lv 2
      = consts 0 * lv 0 * lv 1 + consts 2 * lv 1 * lv 1 := by
    simp [interpDag, interpDagAux, nodeValue, tmplDag, tnBool, List.getD]
  rw [hval, h0, h2, hone] at hroot
  linear_combination hroot

/-- **One instance, end to end.** The assertion at node 14940 -- one of the 6,656 -- discharged by
    a `decide` cone match plus the template lemma above. No per-node value chain, and the algebra
    is not repeated: `tmpl_isBool` was proven once. -/
theorem bool_14940 [CharP F p256] (inputs : Nat → F)
    (hin0 : inputs 0 = 1)
    (hroot : interpDag (raw.toDag (cnst F)) inputs 14940 = 0) :
    inputs 1 = 0 ∨ inputs 1 = 1 := by
  have hdaglen : (raw.toDag (cnst F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hcone : coneIs nodeFn tnBool (fun i => ([0, 14939, 14940] : List Nat).getD i 0) = true := by decide +kernel
  have hmap : ∀ i, i < tnBool.length →
      ([0, 14939, 14940] : List Nat).getD i 0 < raw.nodes.length := by
    intro i hi
    have h3 : tnBool.length = 3 := rfl
    rw [h3] at hi
    rw [nodes_len]
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
  have htr := coneIs_transfer raw (cnst F) inputs nodeFn nodefn_ok tnBool
      (fun i => ([0, 14939, 14940] : List Nat).getD i 0) hcone hmap 2 (by decide)
  have hlv0 : interpDag (raw.toDag (cnst F)) inputs
      (([0, 14939, 14940] : List Nat).getD 0 0) = 1 := by
    show interpDag (raw.toDag (cnst F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnst F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnst F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hlv1 : interpDag (raw.toDag (cnst F)) inputs
      (([0, 14939, 14940] : List Nat).getD 1 0) = inputs 1 := by
    show interpDag (raw.toDag (cnst F)) inputs 14939 = inputs 1
    rw [interpDag_input (raw.toDag (cnst F)) inputs 14939 1
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnst F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
  have hz : interpDag (tmplDag (cnst F) tnBool)
      (fun h => interpDag (raw.toDag (cnst F)) inputs
        (([0, 14939, 14940] : List Nat).getD h 0)) 2 = 0 := by
    rw [← htr]; exact hroot
  have hb := tmpl_isBool (cnst F)
    (fun h => interpDag (raw.toDag (cnst F)) inputs (([0, 14939, 14940] : List Nat).getD h 0))
    cnst_0 cnst_2 hlv0 hz
  rwa [hlv1] at hb

/-! ### Discharging booleanity in bulk

A wrapping-sum instance needs the booleanity of all 96 of its addend and output bits. Going
through `coneIs_transfer` for each would be wasteful -- the cone is three nodes -- so this states
the step directly, and then lifts it over a list so one `decide` covers every pair. -/

/-- One booleanity assertion, straight from the node shape. -/
theorem isBit_of_boolNode (r : RawCircuit) (consts inputs : Nat → F) (nodeFn : Nat → RawNode)
    (hfn : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    (h0 : consts 0 = 1) (h2 : consts 2 = -1)
    (hone : interpDag (r.toDag consts) inputs 0 = 1)
    (a x : Nat) (ha : a < r.nodes.length) (hxa : x < a)
    (hshape : nodeEq (nodeFn a) (.sum [(0, 0, x), (2, x, x)]) = true)
    (hz : interpDag (r.toDag consts) inputs a = 0) :
    interpDag (r.toDag consts) inputs x = 0 ∨ interpDag (r.toDag consts) inputs x = 1 := by
  have hnode : nodeFn a = .sum [(0, 0, x), (2, x, x)] := eq_of_nodeEq hshape
  have hget : (r.toDag consts).getD a (.input 0)
      = .sum [⟨consts 0, 0, x⟩, ⟨consts 2, x, x⟩] := by
    rw [toDag_getD_fn r consts nodeFn hfn ha, hnode]; rfl
  rw [interpDag_sum inputs _ _ _ hget (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨lt_of_le_of_lt (Nat.zero_le x) hxa, hxa⟩
    · exact ⟨hxa, hxa⟩)] at hz
  simp only [List.foldl_cons, List.foldl_nil, h0, h2, hone] at hz
  refine SHA256F.isBit_of_zero_raw _ ?_
  linear_combination hz

/-- The same, over a list of `(assertion node, bit node)` pairs: one `decide` for every shape. -/
theorem bits_of_boolNodes (r : RawCircuit) (consts inputs : Nat → F) (nodeFn : Nat → RawNode)
    (hfn : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    (h0 : consts 0 = 1) (h2 : consts 2 = -1)
    (hone : interpDag (r.toDag consts) inputs 0 = 1)
    (pairs : List (Nat × Nat))
    (hshape : pairs.all (fun p => nodeEq (nodeFn p.1) (.sum [(0, 0, p.2), (2, p.2, p.2)]))
      = true)
    (hlt : pairs.all (fun p => decide (p.2 < p.1) && decide (p.1 < r.nodes.length)) = true)
    (hz : ∀ p ∈ pairs, interpDag (r.toDag consts) inputs p.1 = 0) :
    ∀ p ∈ pairs, interpDag (r.toDag consts) inputs p.2 = 0
      ∨ interpDag (r.toDag consts) inputs p.2 = 1 := by
  intro p hp
  simp only [List.all_eq_true] at hshape hlt
  have hb := hlt p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact isBit_of_boolNode r consts inputs nodeFn hfn h0 h2 hone p.1 p.2 hb.2 hb.1
    (hshape p hp) (hz p hp)

/-- **Indexed form.** The membership version forces the caller to supply `p ∈ pairs`, and
    `decide (_ ∈ _)` reduces through `List.instDecidableMemList`, building a `Decidable` value per
    element -- the trap `RawGroup.backedRawWith` already documents. Indexing by position replaces
    that with a numeric `j < n`, which `norm_num` settles instantly. -/
theorem bits_of_boolNodes_idx (r : RawCircuit) (consts inputs : Nat → F) (nodeFn : Nat → RawNode)
    (hfn : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    (h0 : consts 0 = 1) (h2 : consts 2 = -1)
    (hone : interpDag (r.toDag consts) inputs 0 = 1)
    (pairs : List (Nat × Nat))
    (hshape : pairs.all (fun p => nodeEq (nodeFn p.1) (.sum [(0, 0, p.2), (2, p.2, p.2)]))
      = true)
    (hlt : pairs.all (fun p => decide (p.2 < p.1) && decide (p.1 < r.nodes.length)) = true)
    (hz : ∀ j, j < pairs.length →
      interpDag (r.toDag consts) inputs (pairs.getD j (0, 0)).1 = 0) :
    ∀ j, j < pairs.length →
      interpDag (r.toDag consts) inputs (pairs.getD j (0, 0)).2 = 0
        ∨ interpDag (r.toDag consts) inputs (pairs.getD j (0, 0)).2 = 1 := by
  intro j hj
  have hmem : pairs.getD j (0, 0) ∈ pairs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  simp only [List.all_eq_true] at hshape hlt
  have hb := hlt _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact isBit_of_boolNode r consts inputs nodeFn hfn h0 h2 hone _ _ hb.2 hb.1
    (hshape _ hmem) (hz j hj)

end Sha256Blk
