import quadcert.Bridge.Sha256Gf2.Gf2WrapTmpl

/-!
# The wrapping-sum classes, from the artifact's cones

One lemma per class. The template and the instance maps are generated
(`Gf2WrapTmpl.lean`, kernel-checked by `coneIs`); this is the algebra, written once per class
and reused across its instances.

The chain is: `coneIs_transfer` moves `interpDag` from the artifact's DAG onto the template,
`interpDag_leafChain` evaluates the template to `chainVals`, the `chainNode_*` lemmas of
`Gf2Cone.lean` identify each row, and `GF128.wrapPolyM_zero_of_prod` turns the vanishing
product into `wrapPolyM`. `wrap_nat_gf` then reads it as 32-bit arithmetic.
-/

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2 GF128

variable {F : Type} [Field F] [CharP F 2]

/-- Abbreviation for the artifact's DAG interpretation at an instance's template position. -/
noncomputable def lvAt (α : F) (inputs : Nat → F) (mp : Nat → Nat) : Nat → F :=
  fun i => interpDag (raw.toDag (consts α)) inputs (mp i)

/-! ## The constant factor the round cones carry

Node 1721 is `(inputs 0)^(2^8)` — an eight-deep squaring chain rooted at the `one` wire, a
redundant multiplication by 1 the compiler left in every round cone. Its value being 1 is what
collapses that factor. The node numbers were traced by `gen_gf2_wrap.py`; `coneIs` checks them,
so a mistranscription is rejected by the kernel rather than believed. -/

def mvC : Nat → List (Nat × Nat × Nat)
  | 0 => [(0, 0, 0)]
  | 1 => [(0, 1, 1)]
  | 2 => [(0, 2, 2)]
  | 3 => [(0, 3, 3)]
  | 4 => [(0, 4, 4)]
  | 5 => [(0, 5, 5)]
  | 6 => [(0, 6, 6)]
  | _ => [(0, 7, 7)]

def tnC : List TmplNode :=
  (List.range 1).map (fun i => (TmplNode.leaf i : TmplNode))
    ++ (List.range 8).map (fun k => TmplNode.sum (mvC k))

def mapC : Nat → Nat :=
  fun i => ([0, 404, 405, 406, 407, 408, 409, 410, 1721] : List Nat).getD i 0

theorem coneC : coneIs nodeFn tnC mapC = true := by decide +kernel

theorem mapC_lt : (List.range 9).all (fun i => decide (mapC i < 58258)) = true := by
  decide +kernel

/-- **The chain's value is 1.** Used by both round classes, once. -/
theorem node1721 (α : F) (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (consts α)) inputs 1721 = 1 := by
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapC h) with hlv
  have hmap : ∀ i, i < tnC.length → mapC i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapC_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h i (by simpa [tnC] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnC mapC coneC hmap
    (1 + 7) (by simp [tnC])
  have hb : ∀ j, j < 8 → ∀ t ∈ mvC j, t.2.1 < 1 + j ∧ t.2.2 < 1 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 1 8 mvC hb (show 7 < 8 by norm_num)
  simp only [tnC] at htr
  rw [← hlv] at htr
  have h0 : lv 0 = 1 := by
    rw [hlv]
    show interpDag (raw.toDag (consts α)) inputs (mapC 0) = 1
    rw [show mapC 0 = 0 from rfl,
      interpDag_input (raw.toDag (consts α)) inputs 0 0
        (by simp only [RawCircuit.toDag, List.length_map]; rw [nodes_len]; omega)
        (by rw [toDag_getD_fn raw (consts α) nodeFn nodefn_ok (by rw [nodes_len]; omega)]; rfl),
      hin0]
  have hc0 : consts α 0 = 1 := consts_one α
  show interpDag (raw.toDag (consts α)) inputs (mapC (1 + 7)) = 1
  rw [htr, hchain]
  simp only [chainVals, chainRead, mvC, List.foldl_cons, List.foldl_nil, hc0, h0]
  norm_num

/-- **The `one` wire.** Node 0 is `input 0`, and every injection template puts it at leaf 0,
    so this is the one artifact fact each injection cone needs beyond its own `coneIs`. -/
theorem node0 (α : F) (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (consts α)) inputs 0 = 1 := by
  rw [interpDag_input (raw.toDag (consts α)) inputs 0 0
      (by simp only [RawCircuit.toDag, List.length_map]; rw [nodes_len]; omega)
      (by rw [toDag_getD_fn raw (consts α) nodeFn nodefn_ok (by rw [nodes_len]; omega)]; rfl),
    hin0]

/-! ## `n = 2` — the eight `final` assertions -/

theorem wrapW2_zero (α : F) (hgen : IsGen α) (inputs : Nat → F) (e : Nat) (he : e < 8)
    (hz : interpDag (raw.toDag (consts α)) inputs (mapW2 e rootW2) = 0) :
    wrapPolyM 2 (α ^ 2 ^ 32)
        (lvAt α inputs (mapW2 e) 2 * lvAt α inputs (mapW2 e) 3)
        (lvAt α inputs (mapW2 e) 0 * lvAt α inputs (mapW2 e) 1) = 0 := by
  simp only [lvAt] at *
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapW2 e h) with hlv
  have hcone : coneIs nodeFn tnW2 (mapW2 e) = true := by
    have h := coneW2
    simp only [List.all_eq_true, List.mem_range] at h
    exact h e he
  have hmap : ∀ i, i < tnW2.length → mapW2 e i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapW2_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h e he i (by simpa [tnW2] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnW2 (mapW2 e) hcone hmap
    (4 + 2) (by simp [tnW2])
  have hb : ∀ j, j < 3 → ∀ t ∈ mvW2 j, t.2.1 < 4 + j ∧ t.2.2 < 4 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 4 3 mvW2 hb (show 2 < 3 by norm_num)
  simp only [tnW2] at htr
  rw [← hlv] at htr
  have hz' : (chainVals (consts α) lv 4 mvW2 3).getD 2 0 = 0 := by
    rw [← hchain, ← htr]
    exact hz
  have hc0 : consts α 0 = 1 := consts_one α
  have hc34 : consts α 34 = (α ^ 2 ^ 32) ^ 1 := by
    have := consts_window α hgen 1 (by norm_num)
    simpa [windowIdx] using this
  refine wrapPolyM_zero_of_prod α 2 _ _ _
    (fun j => lv 0 * lv 1 - (α ^ 2 ^ 32) ^ j * (lv 2 * lv 3))
    (fun j _ => rfl) ?_ hz'
  simp only [chainVals, chainRead, mvW2, List.foldl_cons, List.foldl_nil, hc0, hc34,
    Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring

/-! ## `n = 4` — the 48 `schedule` assertions

The same argument. Only the numbers move: seven chain rows instead of three, root at template
position 10, and three more window coefficients to identify. -/

theorem wrapW4_zero (α : F) (hgen : IsGen α) (inputs : Nat → F) (e : Nat) (he : e < 48)
    (hz : interpDag (raw.toDag (consts α)) inputs (mapW4 e rootW4) = 0) :
    wrapPolyM 4 (α ^ 2 ^ 32)
        (lvAt α inputs (mapW4 e) 2 * lvAt α inputs (mapW4 e) 3)
        (lvAt α inputs (mapW4 e) 0 * lvAt α inputs (mapW4 e) 1) = 0 := by
  simp only [lvAt] at *
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapW4 e h) with hlv
  have hcone : coneIs nodeFn tnW4 (mapW4 e) = true := by
    have h := coneW4
    simp only [List.all_eq_true, List.mem_range] at h
    exact h e he
  have hmap : ∀ i, i < tnW4.length → mapW4 e i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapW4_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h e he i (by simpa [tnW4] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnW4 (mapW4 e) hcone hmap
    (4 + 6) (by simp [tnW4])
  have hb : ∀ j, j < 7 → ∀ t ∈ mvW4 j, t.2.1 < 4 + j ∧ t.2.2 < 4 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 4 7 mvW4 hb (show 6 < 7 by norm_num)
  simp only [tnW4] at htr
  rw [← hlv] at htr
  have hz' : (chainVals (consts α) lv 4 mvW4 7).getD 6 0 = 0 := by
    rw [← hchain, ← htr]
    exact hz
  have hc0 : consts α 0 = 1 := consts_one α
  have hcj : ∀ j, 1 ≤ j → j ≤ 3 → consts α (33 + j) = (α ^ 2 ^ 32) ^ j := by
    intro j h1 h3
    have := consts_window α hgen j (by omega)
    simpa [windowIdx, show j ≠ 0 from by omega] using this
  have hc34 : consts α 34 = (α ^ 2 ^ 32) ^ 1 := by simpa using hcj 1 (by norm_num) (by norm_num)
  have hc35 : consts α 35 = (α ^ 2 ^ 32) ^ 2 := by simpa using hcj 2 (by norm_num) (by norm_num)
  have hc36 : consts α 36 = (α ^ 2 ^ 32) ^ 3 := by simpa using hcj 3 (by norm_num) (by norm_num)
  refine wrapPolyM_zero_of_prod α 4 _ _ _
    (fun j => lv 0 * lv 1 - (α ^ 2 ^ 32) ^ j * (lv 2 * lv 3))
    (fun j _ => rfl) ?_ hz'
  simp only [chainVals, chainRead, mvW4, List.foldl_cons, List.foldl_nil, hc0, hc34, hc35, hc36,
    Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring


/-- Every round instance's constant leaf is node 1721. -/
theorem mapW6_const : (List.range 63).all (fun e => mapW6 e 4 == 1721) = true := by decide +kernel

theorem mapW7_const : (List.range 64).all (fun e => mapW7 e 4 == 1721) = true := by decide +kernel

theorem mapW6b_const : (List.range 1).all (fun e => mapW6b e 4 == 1721) = true := by decide +kernel

/-! ## `n = 6` and `n = 7` — the 128 `round_step` assertions

Same argument again, with one addition: the compiler leaves a redundant factor `(v[1721])^2` in
each round cone, and `node1721` collapses it. The `n = 6` class has two such occurrences and
`n = 7` has one; `ring` absorbs either once the value is known to be 1. -/

theorem wrapW6_zero (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (e : Nat) (he : e < 63)
    (hz : interpDag (raw.toDag (consts α)) inputs (mapW6 e rootW6) = 0) :
    wrapPolyM 6 (α ^ 2 ^ 32)
        (lvAt α inputs (mapW6 e) 2 * lvAt α inputs (mapW6 e) 3)
        (lvAt α inputs (mapW6 e) 0 * lvAt α inputs (mapW6 e) 1) = 0 := by
  simp only [lvAt] at *
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapW6 e h) with hlv
  have hcone : coneIs nodeFn tnW6 (mapW6 e) = true := by
    have h := coneW6
    simp only [List.all_eq_true, List.mem_range] at h
    exact h e he
  have hmap : ∀ i, i < tnW6.length → mapW6 e i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapW6_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h e he i (by simpa [tnW6] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnW6 (mapW6 e)
    hcone hmap (5 + 13) (by simp [tnW6])
  have hb : ∀ j, j < 14 → ∀ t ∈ mvW6 j, t.2.1 < 5 + j ∧ t.2.2 < 5 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 5 14 mvW6 hb
    (show 13 < 14 by norm_num)
  simp only [tnW6] at htr
  rw [← hlv] at htr
  have hz' : (chainVals (consts α) lv 5 mvW6 14).getD 13 0 = 0 := by
    rw [← hchain, ← htr]
    exact hz
  have h4 : lv 4 = 1 := by
    rw [hlv]
    show interpDag (raw.toDag (consts α)) inputs (mapW6 e 4) = 1
    have hn : mapW6 e 4 = 1721 := by
      have h := mapW6_const
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
      exact h e he
    rw [hn]
    exact node1721 α inputs hin0
  have hc0 : consts α 0 = 1 := consts_one α
  have hcj : ∀ j, 1 ≤ j → j ≤ 5 → consts α (33 + j) = (α ^ 2 ^ 32) ^ j := by
    intro j h1 h2
    have := consts_window α hgen j (by omega)
    simpa [windowIdx, show j ≠ 0 from by omega] using this
  have hc34 : consts α 34 = (α ^ 2 ^ 32) ^ 1 := by
    simpa using hcj 1 (by norm_num) (by norm_num)
  have hc35 : consts α 35 = (α ^ 2 ^ 32) ^ 2 := by
    simpa using hcj 2 (by norm_num) (by norm_num)
  have hc36 : consts α 36 = (α ^ 2 ^ 32) ^ 3 := by
    simpa using hcj 3 (by norm_num) (by norm_num)
  have hc37 : consts α 37 = (α ^ 2 ^ 32) ^ 4 := by
    simpa using hcj 4 (by norm_num) (by norm_num)
  have hc38 : consts α 38 = (α ^ 2 ^ 32) ^ 5 := by
    simpa using hcj 5 (by norm_num) (by norm_num)
  refine wrapPolyM_zero_of_prod α 6 _ _ _
    (fun j => lv 0 * lv 1 - (α ^ 2 ^ 32) ^ j * (lv 2 * lv 3))
    (fun j _ => rfl) ?_ hz'
  simp only [chainVals, chainRead, mvW6, List.foldl_cons, List.foldl_nil, hc0, hc34, hc35, hc36, hc37, hc38, h4,
    Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  simp only [CharTwo.sub_eq_add]
  ring

theorem wrapW7_zero (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (e : Nat) (he : e < 64)
    (hz : interpDag (raw.toDag (consts α)) inputs (mapW7 e rootW7) = 0) :
    wrapPolyM 7 (α ^ 2 ^ 32)
        (lvAt α inputs (mapW7 e) 2 * lvAt α inputs (mapW7 e) 3)
        (lvAt α inputs (mapW7 e) 0 * lvAt α inputs (mapW7 e) 1) = 0 := by
  simp only [lvAt] at *
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapW7 e h) with hlv
  have hcone : coneIs nodeFn tnW7 (mapW7 e) = true := by
    have h := coneW7
    simp only [List.all_eq_true, List.mem_range] at h
    exact h e he
  have hmap : ∀ i, i < tnW7.length → mapW7 e i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapW7_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h e he i (by simpa [tnW7] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnW7 (mapW7 e)
    hcone hmap (5 + 14) (by simp [tnW7])
  have hb : ∀ j, j < 15 → ∀ t ∈ mvW7 j, t.2.1 < 5 + j ∧ t.2.2 < 5 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 5 15 mvW7 hb
    (show 14 < 15 by norm_num)
  simp only [tnW7] at htr
  rw [← hlv] at htr
  have hz' : (chainVals (consts α) lv 5 mvW7 15).getD 14 0 = 0 := by
    rw [← hchain, ← htr]
    exact hz
  have h4 : lv 4 = 1 := by
    rw [hlv]
    show interpDag (raw.toDag (consts α)) inputs (mapW7 e 4) = 1
    have hn : mapW7 e 4 = 1721 := by
      have h := mapW7_const
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
      exact h e he
    rw [hn]
    exact node1721 α inputs hin0
  have hc0 : consts α 0 = 1 := consts_one α
  have hcj : ∀ j, 1 ≤ j → j ≤ 6 → consts α (33 + j) = (α ^ 2 ^ 32) ^ j := by
    intro j h1 h2
    have := consts_window α hgen j (by omega)
    simpa [windowIdx, show j ≠ 0 from by omega] using this
  have hc34 : consts α 34 = (α ^ 2 ^ 32) ^ 1 := by
    simpa using hcj 1 (by norm_num) (by norm_num)
  have hc35 : consts α 35 = (α ^ 2 ^ 32) ^ 2 := by
    simpa using hcj 2 (by norm_num) (by norm_num)
  have hc36 : consts α 36 = (α ^ 2 ^ 32) ^ 3 := by
    simpa using hcj 3 (by norm_num) (by norm_num)
  have hc37 : consts α 37 = (α ^ 2 ^ 32) ^ 4 := by
    simpa using hcj 4 (by norm_num) (by norm_num)
  have hc38 : consts α 38 = (α ^ 2 ^ 32) ^ 5 := by
    simpa using hcj 5 (by norm_num) (by norm_num)
  have hc39 : consts α 39 = (α ^ 2 ^ 32) ^ 6 := by
    simpa using hcj 6 (by norm_num) (by norm_num)
  refine wrapPolyM_zero_of_prod α 7 _ _ _
    (fun j => lv 0 * lv 1 - (α ^ 2 ^ 32) ^ j * (lv 2 * lv 3))
    (fun j _ => rfl) ?_ hz'
  simp only [chainVals, chainRead, mvW7, List.foldl_cons, List.foldl_nil, hc0, hc34, hc35, hc36, hc37, hc38, hc39, h4,
    Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  simp only [CharTwo.sub_eq_add]
  ring

theorem wrapW6b_zero (α : F) (hgen : IsGen α) (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (e : Nat) (he : e < 1)
    (hz : interpDag (raw.toDag (consts α)) inputs (mapW6b e rootW6b) = 0) :
    wrapPolyM 6 (α ^ 2 ^ 32)
        (lvAt α inputs (mapW6b e) 2 * lvAt α inputs (mapW6b e) 3)
        (lvAt α inputs (mapW6b e) 0 * lvAt α inputs (mapW6b e) 1) = 0 := by
  simp only [lvAt] at *
  set lv : Nat → F := fun h => interpDag (raw.toDag (consts α)) inputs (mapW6b e h) with hlv
  have hcone : coneIs nodeFn tnW6b (mapW6b e) = true := by
    have h := coneW6b
    simp only [List.all_eq_true, List.mem_range] at h
    exact h e he
  have hmap : ∀ i, i < tnW6b.length → mapW6b e i < raw.nodes.length := by
    intro i hi
    rw [nodes_len]
    have h := mapW6b_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h e he i (by simpa [tnW6b] using hi)
  have htr := coneIs_transfer raw (consts α) inputs nodeFn nodefn_ok tnW6b (mapW6b e)
    hcone hmap (5 + 13) (by simp [tnW6b])
  have hb : ∀ j, j < 14 → ∀ t ∈ mvW6b j, t.2.1 < 5 + j ∧ t.2.2 < 5 + j := by decide
  have hchain := interpDag_leafChain (consts α) lv 5 14 mvW6b hb
    (show 13 < 14 by norm_num)
  simp only [tnW6b] at htr
  rw [← hlv] at htr
  have hz' : (chainVals (consts α) lv 5 mvW6b 14).getD 13 0 = 0 := by
    rw [← hchain, ← htr]
    exact hz
  have h4 : lv 4 = 1 := by
    rw [hlv]
    show interpDag (raw.toDag (consts α)) inputs (mapW6b e 4) = 1
    have hn : mapW6b e 4 = 1721 := by
      have h := mapW6b_const
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
      exact h e he
    rw [hn]
    exact node1721 α inputs hin0
  have hc0 : consts α 0 = 1 := consts_one α
  have hcj : ∀ j, 1 ≤ j → j ≤ 5 → consts α (33 + j) = (α ^ 2 ^ 32) ^ j := by
    intro j h1 h2
    have := consts_window α hgen j (by omega)
    simpa [windowIdx, show j ≠ 0 from by omega] using this
  have hc34 : consts α 34 = (α ^ 2 ^ 32) ^ 1 := by
    simpa using hcj 1 (by norm_num) (by norm_num)
  have hc35 : consts α 35 = (α ^ 2 ^ 32) ^ 2 := by
    simpa using hcj 2 (by norm_num) (by norm_num)
  have hc36 : consts α 36 = (α ^ 2 ^ 32) ^ 3 := by
    simpa using hcj 3 (by norm_num) (by norm_num)
  have hc37 : consts α 37 = (α ^ 2 ^ 32) ^ 4 := by
    simpa using hcj 4 (by norm_num) (by norm_num)
  have hc38 : consts α 38 = (α ^ 2 ^ 32) ^ 5 := by
    simpa using hcj 5 (by norm_num) (by norm_num)
  refine wrapPolyM_zero_of_prod α 6 _ _ _
    (fun j => lv 0 * lv 1 - (α ^ 2 ^ 32) ^ j * (lv 2 * lv 3))
    (fun j _ => rfl) ?_ hz'
  simp only [chainVals, chainRead, mvW6b, List.foldl_cons, List.foldl_nil, hc0, hc34, hc35, hc36, hc37, hc38, h4,
    Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  simp only [CharTwo.sub_eq_add]
  ring

end Sha256Gf2
