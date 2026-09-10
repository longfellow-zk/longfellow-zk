/-
# The 128 `round_step` wrapping sums, as edge lists

The `n = 6` (`e` update) and `n = 7` (`a` update) analogues of `S2EdgesSched`.

The product tree above `z` is contiguous, with one node pulled out by CSE: `532`, the constant
`1`, which every tree needs and only one instance owns. That owner is round 18's `n = 6`
assertion, where `532` sits inside the tree at `z+4`; its map is contiguous where the other 63
have a gap.

Round 5's `n = 7` assertion is the one instance of 128 whose tree the compiler emitted with the
operands the other way round, so it goes through `tnWrap7b` on its own. The other 63 share an
edge list, indexed through `skip5`.
-/

import quadcert.Core.ConeEdges
import quadcert.Bridge.Sha256.S2TmplWrap

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

def zOf6 : Nat → Nat
  | 0 => 27313
  | 1 => 21363
  | 2 => 32894
  | 3 => 29235
  | 4 => 24127
  | 5 => 31345
  | 6 => 35176
  | 7 => 27104
  | 8 => 26374
  | 9 => 14738
  | 10 => 34077
  | 11 => 23801
  | 12 => 12852
  | 13 => 15840
  | 14 => 35589
  | 15 => 27179
  | 16 => 36011
  | 17 => 25185
  | 18 => 528
  | 19 => 15944
  | 20 => 8210
  | 21 => 23040
  | 22 => 4085
  | 23 => 34669
  | 24 => 19660
  | 25 => 35852
  | 26 => 30612
  | 27 => 13341
  | 28 => 25556
  | 29 => 34703
  | 30 => 4265
  | 31 => 32405
  | 32 => 27128
  | 33 => 6395
  | 34 => 30426
  | 35 => 18399
  | 36 => 26630
  | 37 => 7324
  | 38 => 35280
  | 39 => 16807
  | 40 => 1023
  | 41 => 35435
  | 42 => 36344
  | 43 => 15625
  | 44 => 25953
  | 45 => 13492
  | 46 => 19842
  | 47 => 28824
  | 48 => 34745
  | 49 => 11530
  | 50 => 26928
  | 51 => 34723
  | 52 => 30179
  | 53 => 36087
  | 54 => 19940
  | 55 => 12962
  | 56 => 19924
  | 57 => 27880
  | 58 => 8771
  | 59 => 14324
  | 60 => 30532
  | 61 => 35212
  | 62 => 29590
  | 63 => 24248
  | _ => 0

def zOf7 : Nat → Nat
  | 0 => 16425
  | 1 => 27628
  | 2 => 29122
  | 3 => 20915
  | 4 => 27491
  | 5 => 36827
  | 6 => 20588
  | 7 => 21274
  | 8 => 33843
  | 9 => 16637
  | 10 => 29483
  | 11 => 28371
  | 12 => 10812
  | 13 => 7205
  | 14 => 11476
  | 15 => 13190
  | 16 => 18682
  | 17 => 28500
  | 18 => 12792
  | 19 => 30337
  | 20 => 12605
  | 21 => 14214
  | 22 => 34286
  | 23 => 10458
  | 24 => 33531
  | 25 => 14537
  | 26 => 5584
  | 27 => 4715
  | 28 => 11227
  | 29 => 31889
  | 30 => 8087
  | 31 => 1939
  | 32 => 22224
  | 33 => 31209
  | 34 => 34201
  | 35 => 32603
  | 36 => 3784
  | 37 => 36446
  | 38 => 2699
  | 39 => 23017
  | 40 => 33994
  | 41 => 7732
  | 42 => 22825
  | 43 => 17490
  | 44 => 24640
  | 45 => 31090
  | 46 => 15515
  | 47 => 9441
  | 48 => 33742
  | 49 => 5238
  | 50 => 33262
  | 51 => 27861
  | 52 => 21722
  | 53 => 9908
  | 54 => 13945
  | 55 => 35008
  | 56 => 15194
  | 57 => 9124
  | 58 => 36327
  | 59 => 31602
  | 60 => 34618
  | 61 => 17348
  | 62 => 36629
  | 63 => 26490
  | _ => 0

def rootOf6 : Nat → Nat := fun e => zOf6 e + (if e = 18 then 14 else 13)
def rootOf7 : Nat → Nat := fun e => zOf7 e + 14

def mapOf6 : Nat → Nat → Nat := fun e i =>
  if i < 3 then (if i < 1 then 0 else if i < 2 then 238 else 239)
  else if i < 7 then zOf6 e + (i - 3)
  else if i = 7 then (if e = 18 then zOf6 e + 4 else 532)
  else zOf6 e + (if e = 18 then i - 3 else i - 4)

def mapOf7 : Nat → Nat → Nat := fun e i =>
  if i < 3 then (if i < 1 then 0 else if i < 2 then 238 else 239)
  else if i < 14 then zOf7 e + (i - 3)
  else if i = 14 then 532
  else zOf7 e + (i - 4)

/-- The 63 rounds whose `n = 7` tree has the standard operand order. -/
def skip5 : Nat → Nat := fun k => if k < 5 then k else k + 1

theorem rndEdges6 : edgesMatch nodeFn tnWrap6 mapOf6 64 = true := by decide +kernel
theorem rndEdges7 : edgesMatch nodeFn tnWrap7 (fun k i => mapOf7 (skip5 k) i) 63 = true := by
  decide +kernel
theorem cone7at5 : coneIs nodeFn tnWrap7b (mapOf7 5) = true := by decide +kernel

theorem mapOf6_lt : ∀ e, e < 64 → ∀ i, i < tnWrap6.length → mapOf6 e i < raw.nodes.length := by
  have hb : (List.range 64).all
      (fun e => (List.range 18).all (fun i => decide (mapOf6 e i < 37139))) = true := by
    decide +kernel
  intro e he i hi
  rw [nodes_len]
  have h18 : tnWrap6.length = 18 := rfl
  rw [h18] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb e he i hi

theorem mapOf7s_lt : ∀ k, k < 63 → ∀ i, i < tnWrap7.length →
    mapOf7 (skip5 k) i < raw.nodes.length := by
  have hb : (List.range 63).all
      (fun k => (List.range 19).all (fun i => decide (mapOf7 (skip5 k) i < 37139))) = true := by
    decide +kernel
  intro k hk i hi
  rw [nodes_len]
  have h19 : tnWrap7.length = 19 := rfl
  rw [h19] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb k hk i hi

theorem map7at5_lt : ∀ i, i < tnWrap7b.length → mapOf7 5 i < raw.nodes.length := by
  have hb : (List.range 19).all (fun i => decide (mapOf7 5 i < 37139)) = true := by decide +kernel
  intro i hi
  rw [nodes_len]
  have h19 : tnWrap7b.length = 19 := rfl
  rw [h19] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb i hi

variable {F : Type} [Field F]

private theorem one_val (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
  have hdl : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
    (by rw [hdl, nodes_len]; norm_num)
    (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
  exact hin0

/-- **All 64 `n = 6` wrapping sums.** -/
theorem allWrap6 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0) :
    ∀ e, e < 64 → SHA256F.wrapPoly 6 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf6 e)) = 0 := by
  intro e he
  have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap6 mapOf6 64
    rndEdges6 mapOf6_lt e he
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h)) 0 = 1 :=
    one_val inputs hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap6)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h)) 17 = 0 := by
    rw [← htr 17 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0
    exact hz e he
  exact tmpl_wrap6 (cnstw F) (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h))
    cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 hone hroot

/-- Round 5, through the mirrored template. -/
theorem wrap7at5 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : interpDag (raw.toDag (cnstw F)) inputs (rootOf7 5) = 0) :
    SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 5)) = 0 := by
  have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap7b (mapOf7 5)
    cone7at5 map7at5_lt
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h)) 0 = 1 :=
    one_val inputs hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap7b)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h)) 18 = 0 := by
    rw [← htr 18 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOf7 5) = 0
    exact hz
  exact tmpl_wrap7b (cnstw F) (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h))
    cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 cnstw_70 hone hroot

/-- **All 64 `n = 7` wrapping sums.** -/
theorem allWrap7 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0) :
    ∀ e, e < 64 → SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 e)) = 0 := by
  intro e he
  by_cases h5 : e = 5
  · subst h5; exact wrap7at5 inputs hin0 (hz 5 (by norm_num))
  · have hk : skip5 (if e < 5 then e else e - 1) = e := by
      rcases Nat.lt_or_ge e 5 with h | h
      · simp [skip5, h]
      · have hne : ¬ (e - 1 < 5) := by omega
        simp [skip5, Nat.not_lt.mpr h, hne]
        omega
    have hlt : (if e < 5 then e else e - 1) < 63 := by
      by_cases h : e < 5 <;> simp only [h, if_true, if_false, ite_true, ite_false] <;> omega
    set k := if e < 5 then e else e - 1 with hkdef
    have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap7
      (fun k i => mapOf7 (skip5 k) i) 63 rndEdges7 mapOf7s_lt k hlt
    have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h)) 0 = 1 :=
      one_val inputs hin0
    have hroot : interpDag (tmplDag (cnstw F) tnWrap7)
        (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h)) 18 = 0 := by
      rw [← htr 18 (by decide)]
      show interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) 18) = 0
      rw [hk]
      exact hz e he
    have hw := tmpl_wrap7 (cnstw F)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h))
      cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 cnstw_70 hone hroot
    show SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 e)) = 0
    rw [← hk]
    exact hw

end Sha256Blk
