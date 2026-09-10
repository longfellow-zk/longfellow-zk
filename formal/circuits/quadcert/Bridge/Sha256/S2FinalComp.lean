/-
# The eight `final` assertions, composed

`S2Final` proves each of the eight outgoing chaining words is the wrapped sum of the incoming one
and a round-64 state word, as three linear forms over the circuit's bits. This file names those
three `Nat`s: `hWord`, `stateWord … 64`, `outWord`, the same vocabulary the schedule and round
bridges speak. What comes out is `SHA256.sha256_soundness`'s `hout`.
-/

import quadcert.Bridge.Sha256.S2Final
import quadcert.Bridge.Sha256.S2State

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {F : Type} [Field F]

/-! #### Output word 0 -/

noncomputable def lvF0 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF0.getD k 0)

theorem leafBitsF0 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF0.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF0.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF0.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF0.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF0.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF0.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF0
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF0 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF0.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF0 inputs k = 0 ∨ lvF0 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF0 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF0.getD j (0, 0)).2 = mpF0.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF0a (lv : Nat → F) : Nat → F
  | 0 => lv 32
  | 1 => lv 31
  | 2 => lv 30
  | 3 => lv 29
  | 4 => lv 28
  | 5 => lv 27
  | 6 => lv 26
  | 7 => lv 25
  | 8 => lv 24
  | 9 => lv 23
  | 10 => lv 22
  | 11 => lv 21
  | 12 => lv 20
  | 13 => lv 19
  | 14 => lv 18
  | 15 => lv 17
  | 16 => lv 16
  | 17 => lv 15
  | 18 => lv 14
  | 19 => lv 13
  | 20 => lv 12
  | 21 => lv 11
  | 22 => lv 10
  | 23 => lv 9
  | 24 => lv 8
  | 25 => lv 7
  | 26 => lv 6
  | 27 => lv 5
  | 28 => lv 4
  | 29 => lv 3
  | 30 => lv 2
  | 31 => lv 1
  | _ => 0

theorem csA0_eq (lv : Nat → F) :
    csA0 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF0a lv j)) := rfl

theorem vbF0a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF0a lv j = 0 ∨ vF0a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 32 (by norm_num)
  | 1, _ => exact hlv 31 (by norm_num)
  | 2, _ => exact hlv 30 (by norm_num)
  | 3, _ => exact hlv 29 (by norm_num)
  | 4, _ => exact hlv 28 (by norm_num)
  | 5, _ => exact hlv 27 (by norm_num)
  | 6, _ => exact hlv 26 (by norm_num)
  | 7, _ => exact hlv 25 (by norm_num)
  | 8, _ => exact hlv 24 (by norm_num)
  | 9, _ => exact hlv 23 (by norm_num)
  | 10, _ => exact hlv 22 (by norm_num)
  | 11, _ => exact hlv 21 (by norm_num)
  | 12, _ => exact hlv 20 (by norm_num)
  | 13, _ => exact hlv 19 (by norm_num)
  | 14, _ => exact hlv 18 (by norm_num)
  | 15, _ => exact hlv 17 (by norm_num)
  | 16, _ => exact hlv 16 (by norm_num)
  | 17, _ => exact hlv 15 (by norm_num)
  | 18, _ => exact hlv 14 (by norm_num)
  | 19, _ => exact hlv 13 (by norm_num)
  | 20, _ => exact hlv 12 (by norm_num)
  | 21, _ => exact hlv 11 (by norm_num)
  | 22, _ => exact hlv 10 (by norm_num)
  | 23, _ => exact hlv 9 (by norm_num)
  | 24, _ => exact hlv 8 (by norm_num)
  | 25, _ => exact hlv 7 (by norm_num)
  | 26, _ => exact hlv 6 (by norm_num)
  | 27, _ => exact hlv 5 (by norm_num)
  | 28, _ => exact hlv 4 (by norm_num)
  | 29, _ => exact hlv 3 (by norm_num)
  | 30, _ => exact hlv 2 (by norm_num)
  | 31, _ => exact hlv 1 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF0a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF0 inputs 32), SHA256F.natBit (lvF0 inputs 31), SHA256F.natBit (lvF0 inputs 30), SHA256F.natBit (lvF0 inputs 29), SHA256F.natBit (lvF0 inputs 28), SHA256F.natBit (lvF0 inputs 27), SHA256F.natBit (lvF0 inputs 26), SHA256F.natBit (lvF0 inputs 25), SHA256F.natBit (lvF0 inputs 24), SHA256F.natBit (lvF0 inputs 23), SHA256F.natBit (lvF0 inputs 22), SHA256F.natBit (lvF0 inputs 21), SHA256F.natBit (lvF0 inputs 20), SHA256F.natBit (lvF0 inputs 19), SHA256F.natBit (lvF0 inputs 18), SHA256F.natBit (lvF0 inputs 17), SHA256F.natBit (lvF0 inputs 16), SHA256F.natBit (lvF0 inputs 15), SHA256F.natBit (lvF0 inputs 14), SHA256F.natBit (lvF0 inputs 13), SHA256F.natBit (lvF0 inputs 12), SHA256F.natBit (lvF0 inputs 11), SHA256F.natBit (lvF0 inputs 10), SHA256F.natBit (lvF0 inputs 9), SHA256F.natBit (lvF0 inputs 8), SHA256F.natBit (lvF0 inputs 7), SHA256F.natBit (lvF0 inputs 6), SHA256F.natBit (lvF0 inputs 5), SHA256F.natBit (lvF0 inputs 4), SHA256F.natBit (lvF0 inputs 3), SHA256F.natBit (lvF0 inputs 2), SHA256F.natBit (lvF0 inputs 1)]

theorem bwF0a_eq (inputs : Nat → F) : bwF0a inputs = bitsOf inputs (hinBits 0) := rfl

noncomputable def vF0b (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB0_eq (lv : Nat → F) :
    csB0 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF0b lv j)) := rfl

theorem vbF0b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF0b lv j = 0 ∨ vF0b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF0b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF0 inputs 33), SHA256F.natBit (lvF0 inputs 96), SHA256F.natBit (lvF0 inputs 95), SHA256F.natBit (lvF0 inputs 94), SHA256F.natBit (lvF0 inputs 93), SHA256F.natBit (lvF0 inputs 92), SHA256F.natBit (lvF0 inputs 91), SHA256F.natBit (lvF0 inputs 90), SHA256F.natBit (lvF0 inputs 89), SHA256F.natBit (lvF0 inputs 88), SHA256F.natBit (lvF0 inputs 87), SHA256F.natBit (lvF0 inputs 86), SHA256F.natBit (lvF0 inputs 85), SHA256F.natBit (lvF0 inputs 84), SHA256F.natBit (lvF0 inputs 83), SHA256F.natBit (lvF0 inputs 82), SHA256F.natBit (lvF0 inputs 81), SHA256F.natBit (lvF0 inputs 80), SHA256F.natBit (lvF0 inputs 79), SHA256F.natBit (lvF0 inputs 78), SHA256F.natBit (lvF0 inputs 77), SHA256F.natBit (lvF0 inputs 76), SHA256F.natBit (lvF0 inputs 75), SHA256F.natBit (lvF0 inputs 74), SHA256F.natBit (lvF0 inputs 73), SHA256F.natBit (lvF0 inputs 72), SHA256F.natBit (lvF0 inputs 71), SHA256F.natBit (lvF0 inputs 70), SHA256F.natBit (lvF0 inputs 69), SHA256F.natBit (lvF0 inputs 68), SHA256F.natBit (lvF0 inputs 67), SHA256F.natBit (lvF0 inputs 66)]

theorem bwF0b_eq (inputs : Nat → F) : bwF0b inputs = bitsOf inputs (stateBits 64 0) := rfl

noncomputable def vF0p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF0_eq (lv : Nat → F) :
    dsF0 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF0p lv j)) := rfl

theorem vbF0p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF0p lv j = 0 ∨ vF0p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF0p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF0 inputs 65), SHA256F.natBit (lvF0 inputs 64), SHA256F.natBit (lvF0 inputs 63), SHA256F.natBit (lvF0 inputs 62), SHA256F.natBit (lvF0 inputs 61), SHA256F.natBit (lvF0 inputs 60), SHA256F.natBit (lvF0 inputs 59), SHA256F.natBit (lvF0 inputs 58), SHA256F.natBit (lvF0 inputs 57), SHA256F.natBit (lvF0 inputs 56), SHA256F.natBit (lvF0 inputs 55), SHA256F.natBit (lvF0 inputs 54), SHA256F.natBit (lvF0 inputs 53), SHA256F.natBit (lvF0 inputs 52), SHA256F.natBit (lvF0 inputs 51), SHA256F.natBit (lvF0 inputs 50), SHA256F.natBit (lvF0 inputs 49), SHA256F.natBit (lvF0 inputs 48), SHA256F.natBit (lvF0 inputs 47), SHA256F.natBit (lvF0 inputs 46), SHA256F.natBit (lvF0 inputs 45), SHA256F.natBit (lvF0 inputs 44), SHA256F.natBit (lvF0 inputs 43), SHA256F.natBit (lvF0 inputs 42), SHA256F.natBit (lvF0 inputs 41), SHA256F.natBit (lvF0 inputs 40), SHA256F.natBit (lvF0 inputs 39), SHA256F.natBit (lvF0 inputs 38), SHA256F.natBit (lvF0 inputs 37), SHA256F.natBit (lvF0 inputs 36), SHA256F.natBit (lvF0 inputs 35), SHA256F.natBit (lvF0 inputs 34)]

theorem bwF0p_eq (inputs : Nat → F) : bwF0p inputs = bitsOf inputs (h1Bits 0) := rfl

/-- **Output word 0.** -/
theorem finalW0 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF0.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF0.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 0 = SHA256.w32 (hWord inputs 0 + stateWord inputs 64 0) := by
  have hlv : ∀ k, k < 97 → lvF0 inputs k = 0 ∨ lvF0 inputs k = 1 := lvBitsF0 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final0 inputs hin0 hbz (allWrap2 inputs hin0 hroot 0 (by norm_num))
  rw [csA0_eq] at hA
  rw [csB0_eq] at hB
  rw [dsF0_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF0a (lvF0 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF0a (lvF0 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF0b (lvF0 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF0b (lvF0 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF0p (lvF0 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF0p (lvF0 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 0 := by rw [hvA, hWord, ← bwF0a_eq]; rfl
  have heB : B = stateWord inputs 64 0 := by rw [hvB, stateWord, ← bwF0b_eq]; rfl
  have heP : P = outWord inputs 0 := by rw [hvP, outWord, ← bwF0p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 1 -/

noncomputable def lvF1 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF1.getD k 0)

theorem leafBitsF1 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF1.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF1.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF1.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF1.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF1.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF1.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF1
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF1 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF1.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF1 inputs k = 0 ∨ lvF1 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF1 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF1.getD j (0, 0)).2 = mpF1.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF1a (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA1_eq (lv : Nat → F) :
    csA1 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF1a lv j)) := rfl

theorem vbF1a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF1a lv j = 0 ∨ vF1a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF1a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF1 inputs 33), SHA256F.natBit (lvF1 inputs 32), SHA256F.natBit (lvF1 inputs 31), SHA256F.natBit (lvF1 inputs 30), SHA256F.natBit (lvF1 inputs 29), SHA256F.natBit (lvF1 inputs 28), SHA256F.natBit (lvF1 inputs 27), SHA256F.natBit (lvF1 inputs 26), SHA256F.natBit (lvF1 inputs 25), SHA256F.natBit (lvF1 inputs 24), SHA256F.natBit (lvF1 inputs 23), SHA256F.natBit (lvF1 inputs 22), SHA256F.natBit (lvF1 inputs 21), SHA256F.natBit (lvF1 inputs 20), SHA256F.natBit (lvF1 inputs 19), SHA256F.natBit (lvF1 inputs 18), SHA256F.natBit (lvF1 inputs 17), SHA256F.natBit (lvF1 inputs 16), SHA256F.natBit (lvF1 inputs 15), SHA256F.natBit (lvF1 inputs 14), SHA256F.natBit (lvF1 inputs 13), SHA256F.natBit (lvF1 inputs 12), SHA256F.natBit (lvF1 inputs 11), SHA256F.natBit (lvF1 inputs 10), SHA256F.natBit (lvF1 inputs 9), SHA256F.natBit (lvF1 inputs 8), SHA256F.natBit (lvF1 inputs 7), SHA256F.natBit (lvF1 inputs 6), SHA256F.natBit (lvF1 inputs 5), SHA256F.natBit (lvF1 inputs 4), SHA256F.natBit (lvF1 inputs 3), SHA256F.natBit (lvF1 inputs 2)]

theorem bwF1a_eq (inputs : Nat → F) : bwF1a inputs = bitsOf inputs (hinBits 1) := rfl

noncomputable def vF1b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB1_eq (lv : Nat → F) :
    csB1 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF1b lv j)) := rfl

theorem vbF1b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF1b lv j = 0 ∨ vF1b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF1b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF1 inputs 1), SHA256F.natBit (lvF1 inputs 96), SHA256F.natBit (lvF1 inputs 95), SHA256F.natBit (lvF1 inputs 94), SHA256F.natBit (lvF1 inputs 93), SHA256F.natBit (lvF1 inputs 92), SHA256F.natBit (lvF1 inputs 91), SHA256F.natBit (lvF1 inputs 90), SHA256F.natBit (lvF1 inputs 89), SHA256F.natBit (lvF1 inputs 88), SHA256F.natBit (lvF1 inputs 87), SHA256F.natBit (lvF1 inputs 86), SHA256F.natBit (lvF1 inputs 85), SHA256F.natBit (lvF1 inputs 84), SHA256F.natBit (lvF1 inputs 83), SHA256F.natBit (lvF1 inputs 82), SHA256F.natBit (lvF1 inputs 81), SHA256F.natBit (lvF1 inputs 80), SHA256F.natBit (lvF1 inputs 79), SHA256F.natBit (lvF1 inputs 78), SHA256F.natBit (lvF1 inputs 77), SHA256F.natBit (lvF1 inputs 76), SHA256F.natBit (lvF1 inputs 75), SHA256F.natBit (lvF1 inputs 74), SHA256F.natBit (lvF1 inputs 73), SHA256F.natBit (lvF1 inputs 72), SHA256F.natBit (lvF1 inputs 71), SHA256F.natBit (lvF1 inputs 70), SHA256F.natBit (lvF1 inputs 69), SHA256F.natBit (lvF1 inputs 68), SHA256F.natBit (lvF1 inputs 67), SHA256F.natBit (lvF1 inputs 66)]

theorem bwF1b_eq (inputs : Nat → F) : bwF1b inputs = bitsOf inputs (stateBits 64 1) := rfl

noncomputable def vF1p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF1_eq (lv : Nat → F) :
    dsF1 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF1p lv j)) := rfl

theorem vbF1p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF1p lv j = 0 ∨ vF1p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF1p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF1 inputs 65), SHA256F.natBit (lvF1 inputs 64), SHA256F.natBit (lvF1 inputs 63), SHA256F.natBit (lvF1 inputs 62), SHA256F.natBit (lvF1 inputs 61), SHA256F.natBit (lvF1 inputs 60), SHA256F.natBit (lvF1 inputs 59), SHA256F.natBit (lvF1 inputs 58), SHA256F.natBit (lvF1 inputs 57), SHA256F.natBit (lvF1 inputs 56), SHA256F.natBit (lvF1 inputs 55), SHA256F.natBit (lvF1 inputs 54), SHA256F.natBit (lvF1 inputs 53), SHA256F.natBit (lvF1 inputs 52), SHA256F.natBit (lvF1 inputs 51), SHA256F.natBit (lvF1 inputs 50), SHA256F.natBit (lvF1 inputs 49), SHA256F.natBit (lvF1 inputs 48), SHA256F.natBit (lvF1 inputs 47), SHA256F.natBit (lvF1 inputs 46), SHA256F.natBit (lvF1 inputs 45), SHA256F.natBit (lvF1 inputs 44), SHA256F.natBit (lvF1 inputs 43), SHA256F.natBit (lvF1 inputs 42), SHA256F.natBit (lvF1 inputs 41), SHA256F.natBit (lvF1 inputs 40), SHA256F.natBit (lvF1 inputs 39), SHA256F.natBit (lvF1 inputs 38), SHA256F.natBit (lvF1 inputs 37), SHA256F.natBit (lvF1 inputs 36), SHA256F.natBit (lvF1 inputs 35), SHA256F.natBit (lvF1 inputs 34)]

theorem bwF1p_eq (inputs : Nat → F) : bwF1p inputs = bitsOf inputs (h1Bits 1) := rfl

/-- **Output word 1.** -/
theorem finalW1 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF1.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF1.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 1 = SHA256.w32 (hWord inputs 1 + stateWord inputs 64 1) := by
  have hlv : ∀ k, k < 97 → lvF1 inputs k = 0 ∨ lvF1 inputs k = 1 := lvBitsF1 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final1 inputs hin0 hbz (allWrap2 inputs hin0 hroot 1 (by norm_num))
  rw [csA1_eq] at hA
  rw [csB1_eq] at hB
  rw [dsF1_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF1a (lvF1 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF1a (lvF1 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF1b (lvF1 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF1b (lvF1 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF1p (lvF1 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF1p (lvF1 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 1 := by rw [hvA, hWord, ← bwF1a_eq]; rfl
  have heB : B = stateWord inputs 64 1 := by rw [hvB, stateWord, ← bwF1b_eq]; rfl
  have heP : P = outWord inputs 1 := by rw [hvP, outWord, ← bwF1p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 2 -/

noncomputable def lvF2 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF2.getD k 0)

theorem leafBitsF2 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF2.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF2.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF2.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF2.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF2.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF2.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF2
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF2 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF2.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF2 inputs k = 0 ∨ lvF2 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF2 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF2.getD j (0, 0)).2 = mpF2.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF2a (lv : Nat → F) : Nat → F
  | 0 => lv 96
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA2_eq (lv : Nat → F) :
    csA2 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF2a lv j)) := rfl

theorem vbF2a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF2a lv j = 0 ∨ vF2a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 96 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF2a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF2 inputs 96), SHA256F.natBit (lvF2 inputs 32), SHA256F.natBit (lvF2 inputs 31), SHA256F.natBit (lvF2 inputs 30), SHA256F.natBit (lvF2 inputs 29), SHA256F.natBit (lvF2 inputs 28), SHA256F.natBit (lvF2 inputs 27), SHA256F.natBit (lvF2 inputs 26), SHA256F.natBit (lvF2 inputs 25), SHA256F.natBit (lvF2 inputs 24), SHA256F.natBit (lvF2 inputs 23), SHA256F.natBit (lvF2 inputs 22), SHA256F.natBit (lvF2 inputs 21), SHA256F.natBit (lvF2 inputs 20), SHA256F.natBit (lvF2 inputs 19), SHA256F.natBit (lvF2 inputs 18), SHA256F.natBit (lvF2 inputs 17), SHA256F.natBit (lvF2 inputs 16), SHA256F.natBit (lvF2 inputs 15), SHA256F.natBit (lvF2 inputs 14), SHA256F.natBit (lvF2 inputs 13), SHA256F.natBit (lvF2 inputs 12), SHA256F.natBit (lvF2 inputs 11), SHA256F.natBit (lvF2 inputs 10), SHA256F.natBit (lvF2 inputs 9), SHA256F.natBit (lvF2 inputs 8), SHA256F.natBit (lvF2 inputs 7), SHA256F.natBit (lvF2 inputs 6), SHA256F.natBit (lvF2 inputs 5), SHA256F.natBit (lvF2 inputs 4), SHA256F.natBit (lvF2 inputs 3), SHA256F.natBit (lvF2 inputs 2)]

theorem bwF2a_eq (inputs : Nat → F) : bwF2a inputs = bitsOf inputs (hinBits 2) := rfl

noncomputable def vF2b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 95
  | 2 => lv 94
  | 3 => lv 93
  | 4 => lv 92
  | 5 => lv 91
  | 6 => lv 90
  | 7 => lv 89
  | 8 => lv 88
  | 9 => lv 87
  | 10 => lv 86
  | 11 => lv 85
  | 12 => lv 84
  | 13 => lv 83
  | 14 => lv 82
  | 15 => lv 81
  | 16 => lv 80
  | 17 => lv 79
  | 18 => lv 78
  | 19 => lv 77
  | 20 => lv 76
  | 21 => lv 75
  | 22 => lv 74
  | 23 => lv 73
  | 24 => lv 72
  | 25 => lv 71
  | 26 => lv 70
  | 27 => lv 69
  | 28 => lv 68
  | 29 => lv 67
  | 30 => lv 66
  | 31 => lv 65
  | _ => 0

theorem csB2_eq (lv : Nat → F) :
    csB2 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF2b lv j)) := rfl

theorem vbF2b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF2b lv j = 0 ∨ vF2b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 95 (by norm_num)
  | 2, _ => exact hlv 94 (by norm_num)
  | 3, _ => exact hlv 93 (by norm_num)
  | 4, _ => exact hlv 92 (by norm_num)
  | 5, _ => exact hlv 91 (by norm_num)
  | 6, _ => exact hlv 90 (by norm_num)
  | 7, _ => exact hlv 89 (by norm_num)
  | 8, _ => exact hlv 88 (by norm_num)
  | 9, _ => exact hlv 87 (by norm_num)
  | 10, _ => exact hlv 86 (by norm_num)
  | 11, _ => exact hlv 85 (by norm_num)
  | 12, _ => exact hlv 84 (by norm_num)
  | 13, _ => exact hlv 83 (by norm_num)
  | 14, _ => exact hlv 82 (by norm_num)
  | 15, _ => exact hlv 81 (by norm_num)
  | 16, _ => exact hlv 80 (by norm_num)
  | 17, _ => exact hlv 79 (by norm_num)
  | 18, _ => exact hlv 78 (by norm_num)
  | 19, _ => exact hlv 77 (by norm_num)
  | 20, _ => exact hlv 76 (by norm_num)
  | 21, _ => exact hlv 75 (by norm_num)
  | 22, _ => exact hlv 74 (by norm_num)
  | 23, _ => exact hlv 73 (by norm_num)
  | 24, _ => exact hlv 72 (by norm_num)
  | 25, _ => exact hlv 71 (by norm_num)
  | 26, _ => exact hlv 70 (by norm_num)
  | 27, _ => exact hlv 69 (by norm_num)
  | 28, _ => exact hlv 68 (by norm_num)
  | 29, _ => exact hlv 67 (by norm_num)
  | 30, _ => exact hlv 66 (by norm_num)
  | 31, _ => exact hlv 65 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF2b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF2 inputs 1), SHA256F.natBit (lvF2 inputs 95), SHA256F.natBit (lvF2 inputs 94), SHA256F.natBit (lvF2 inputs 93), SHA256F.natBit (lvF2 inputs 92), SHA256F.natBit (lvF2 inputs 91), SHA256F.natBit (lvF2 inputs 90), SHA256F.natBit (lvF2 inputs 89), SHA256F.natBit (lvF2 inputs 88), SHA256F.natBit (lvF2 inputs 87), SHA256F.natBit (lvF2 inputs 86), SHA256F.natBit (lvF2 inputs 85), SHA256F.natBit (lvF2 inputs 84), SHA256F.natBit (lvF2 inputs 83), SHA256F.natBit (lvF2 inputs 82), SHA256F.natBit (lvF2 inputs 81), SHA256F.natBit (lvF2 inputs 80), SHA256F.natBit (lvF2 inputs 79), SHA256F.natBit (lvF2 inputs 78), SHA256F.natBit (lvF2 inputs 77), SHA256F.natBit (lvF2 inputs 76), SHA256F.natBit (lvF2 inputs 75), SHA256F.natBit (lvF2 inputs 74), SHA256F.natBit (lvF2 inputs 73), SHA256F.natBit (lvF2 inputs 72), SHA256F.natBit (lvF2 inputs 71), SHA256F.natBit (lvF2 inputs 70), SHA256F.natBit (lvF2 inputs 69), SHA256F.natBit (lvF2 inputs 68), SHA256F.natBit (lvF2 inputs 67), SHA256F.natBit (lvF2 inputs 66), SHA256F.natBit (lvF2 inputs 65)]

theorem bwF2b_eq (inputs : Nat → F) : bwF2b inputs = bitsOf inputs (stateBits 64 2) := rfl

noncomputable def vF2p (lv : Nat → F) : Nat → F
  | 0 => lv 64
  | 1 => lv 63
  | 2 => lv 62
  | 3 => lv 61
  | 4 => lv 60
  | 5 => lv 59
  | 6 => lv 58
  | 7 => lv 57
  | 8 => lv 56
  | 9 => lv 55
  | 10 => lv 54
  | 11 => lv 53
  | 12 => lv 52
  | 13 => lv 51
  | 14 => lv 50
  | 15 => lv 49
  | 16 => lv 48
  | 17 => lv 47
  | 18 => lv 46
  | 19 => lv 45
  | 20 => lv 44
  | 21 => lv 43
  | 22 => lv 42
  | 23 => lv 41
  | 24 => lv 40
  | 25 => lv 39
  | 26 => lv 38
  | 27 => lv 37
  | 28 => lv 36
  | 29 => lv 35
  | 30 => lv 34
  | 31 => lv 33
  | _ => 0

theorem dsF2_eq (lv : Nat → F) :
    dsF2 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF2p lv j)) := rfl

theorem vbF2p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF2p lv j = 0 ∨ vF2p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 64 (by norm_num)
  | 1, _ => exact hlv 63 (by norm_num)
  | 2, _ => exact hlv 62 (by norm_num)
  | 3, _ => exact hlv 61 (by norm_num)
  | 4, _ => exact hlv 60 (by norm_num)
  | 5, _ => exact hlv 59 (by norm_num)
  | 6, _ => exact hlv 58 (by norm_num)
  | 7, _ => exact hlv 57 (by norm_num)
  | 8, _ => exact hlv 56 (by norm_num)
  | 9, _ => exact hlv 55 (by norm_num)
  | 10, _ => exact hlv 54 (by norm_num)
  | 11, _ => exact hlv 53 (by norm_num)
  | 12, _ => exact hlv 52 (by norm_num)
  | 13, _ => exact hlv 51 (by norm_num)
  | 14, _ => exact hlv 50 (by norm_num)
  | 15, _ => exact hlv 49 (by norm_num)
  | 16, _ => exact hlv 48 (by norm_num)
  | 17, _ => exact hlv 47 (by norm_num)
  | 18, _ => exact hlv 46 (by norm_num)
  | 19, _ => exact hlv 45 (by norm_num)
  | 20, _ => exact hlv 44 (by norm_num)
  | 21, _ => exact hlv 43 (by norm_num)
  | 22, _ => exact hlv 42 (by norm_num)
  | 23, _ => exact hlv 41 (by norm_num)
  | 24, _ => exact hlv 40 (by norm_num)
  | 25, _ => exact hlv 39 (by norm_num)
  | 26, _ => exact hlv 38 (by norm_num)
  | 27, _ => exact hlv 37 (by norm_num)
  | 28, _ => exact hlv 36 (by norm_num)
  | 29, _ => exact hlv 35 (by norm_num)
  | 30, _ => exact hlv 34 (by norm_num)
  | 31, _ => exact hlv 33 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF2p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF2 inputs 64), SHA256F.natBit (lvF2 inputs 63), SHA256F.natBit (lvF2 inputs 62), SHA256F.natBit (lvF2 inputs 61), SHA256F.natBit (lvF2 inputs 60), SHA256F.natBit (lvF2 inputs 59), SHA256F.natBit (lvF2 inputs 58), SHA256F.natBit (lvF2 inputs 57), SHA256F.natBit (lvF2 inputs 56), SHA256F.natBit (lvF2 inputs 55), SHA256F.natBit (lvF2 inputs 54), SHA256F.natBit (lvF2 inputs 53), SHA256F.natBit (lvF2 inputs 52), SHA256F.natBit (lvF2 inputs 51), SHA256F.natBit (lvF2 inputs 50), SHA256F.natBit (lvF2 inputs 49), SHA256F.natBit (lvF2 inputs 48), SHA256F.natBit (lvF2 inputs 47), SHA256F.natBit (lvF2 inputs 46), SHA256F.natBit (lvF2 inputs 45), SHA256F.natBit (lvF2 inputs 44), SHA256F.natBit (lvF2 inputs 43), SHA256F.natBit (lvF2 inputs 42), SHA256F.natBit (lvF2 inputs 41), SHA256F.natBit (lvF2 inputs 40), SHA256F.natBit (lvF2 inputs 39), SHA256F.natBit (lvF2 inputs 38), SHA256F.natBit (lvF2 inputs 37), SHA256F.natBit (lvF2 inputs 36), SHA256F.natBit (lvF2 inputs 35), SHA256F.natBit (lvF2 inputs 34), SHA256F.natBit (lvF2 inputs 33)]

theorem bwF2p_eq (inputs : Nat → F) : bwF2p inputs = bitsOf inputs (h1Bits 2) := rfl

/-- **Output word 2.** -/
theorem finalW2 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF2.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF2.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 2 = SHA256.w32 (hWord inputs 2 + stateWord inputs 64 2) := by
  have hlv : ∀ k, k < 97 → lvF2 inputs k = 0 ∨ lvF2 inputs k = 1 := lvBitsF2 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final2 inputs hin0 hbz (allWrap2 inputs hin0 hroot 2 (by norm_num))
  rw [csA2_eq] at hA
  rw [csB2_eq] at hB
  rw [dsF2_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF2a (lvF2 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF2a (lvF2 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF2b (lvF2 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF2b (lvF2 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF2p (lvF2 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF2p (lvF2 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 2 := by rw [hvA, hWord, ← bwF2a_eq]; rfl
  have heB : B = stateWord inputs 64 2 := by rw [hvB, stateWord, ← bwF2b_eq]; rfl
  have heP : P = outWord inputs 2 := by rw [hvP, outWord, ← bwF2p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 3 -/

noncomputable def lvF3 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF3.getD k 0)

theorem leafBitsF3 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF3.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF3.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF3.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF3.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF3.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF3.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF3
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF3 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF3.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF3 inputs k = 0 ∨ lvF3 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF3 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF3.getD j (0, 0)).2 = mpF3.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF3a (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA3_eq (lv : Nat → F) :
    csA3 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF3a lv j)) := rfl

theorem vbF3a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF3a lv j = 0 ∨ vF3a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF3a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF3 inputs 33), SHA256F.natBit (lvF3 inputs 32), SHA256F.natBit (lvF3 inputs 31), SHA256F.natBit (lvF3 inputs 30), SHA256F.natBit (lvF3 inputs 29), SHA256F.natBit (lvF3 inputs 28), SHA256F.natBit (lvF3 inputs 27), SHA256F.natBit (lvF3 inputs 26), SHA256F.natBit (lvF3 inputs 25), SHA256F.natBit (lvF3 inputs 24), SHA256F.natBit (lvF3 inputs 23), SHA256F.natBit (lvF3 inputs 22), SHA256F.natBit (lvF3 inputs 21), SHA256F.natBit (lvF3 inputs 20), SHA256F.natBit (lvF3 inputs 19), SHA256F.natBit (lvF3 inputs 18), SHA256F.natBit (lvF3 inputs 17), SHA256F.natBit (lvF3 inputs 16), SHA256F.natBit (lvF3 inputs 15), SHA256F.natBit (lvF3 inputs 14), SHA256F.natBit (lvF3 inputs 13), SHA256F.natBit (lvF3 inputs 12), SHA256F.natBit (lvF3 inputs 11), SHA256F.natBit (lvF3 inputs 10), SHA256F.natBit (lvF3 inputs 9), SHA256F.natBit (lvF3 inputs 8), SHA256F.natBit (lvF3 inputs 7), SHA256F.natBit (lvF3 inputs 6), SHA256F.natBit (lvF3 inputs 5), SHA256F.natBit (lvF3 inputs 4), SHA256F.natBit (lvF3 inputs 3), SHA256F.natBit (lvF3 inputs 2)]

theorem bwF3a_eq (inputs : Nat → F) : bwF3a inputs = bitsOf inputs (hinBits 3) := rfl

noncomputable def vF3b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB3_eq (lv : Nat → F) :
    csB3 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF3b lv j)) := rfl

theorem vbF3b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF3b lv j = 0 ∨ vF3b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF3b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF3 inputs 1), SHA256F.natBit (lvF3 inputs 96), SHA256F.natBit (lvF3 inputs 95), SHA256F.natBit (lvF3 inputs 94), SHA256F.natBit (lvF3 inputs 93), SHA256F.natBit (lvF3 inputs 92), SHA256F.natBit (lvF3 inputs 91), SHA256F.natBit (lvF3 inputs 90), SHA256F.natBit (lvF3 inputs 89), SHA256F.natBit (lvF3 inputs 88), SHA256F.natBit (lvF3 inputs 87), SHA256F.natBit (lvF3 inputs 86), SHA256F.natBit (lvF3 inputs 85), SHA256F.natBit (lvF3 inputs 84), SHA256F.natBit (lvF3 inputs 83), SHA256F.natBit (lvF3 inputs 82), SHA256F.natBit (lvF3 inputs 81), SHA256F.natBit (lvF3 inputs 80), SHA256F.natBit (lvF3 inputs 79), SHA256F.natBit (lvF3 inputs 78), SHA256F.natBit (lvF3 inputs 77), SHA256F.natBit (lvF3 inputs 76), SHA256F.natBit (lvF3 inputs 75), SHA256F.natBit (lvF3 inputs 74), SHA256F.natBit (lvF3 inputs 73), SHA256F.natBit (lvF3 inputs 72), SHA256F.natBit (lvF3 inputs 71), SHA256F.natBit (lvF3 inputs 70), SHA256F.natBit (lvF3 inputs 69), SHA256F.natBit (lvF3 inputs 68), SHA256F.natBit (lvF3 inputs 67), SHA256F.natBit (lvF3 inputs 66)]

theorem bwF3b_eq (inputs : Nat → F) : bwF3b inputs = bitsOf inputs (stateBits 64 3) := rfl

noncomputable def vF3p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF3_eq (lv : Nat → F) :
    dsF3 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF3p lv j)) := rfl

theorem vbF3p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF3p lv j = 0 ∨ vF3p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF3p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF3 inputs 65), SHA256F.natBit (lvF3 inputs 64), SHA256F.natBit (lvF3 inputs 63), SHA256F.natBit (lvF3 inputs 62), SHA256F.natBit (lvF3 inputs 61), SHA256F.natBit (lvF3 inputs 60), SHA256F.natBit (lvF3 inputs 59), SHA256F.natBit (lvF3 inputs 58), SHA256F.natBit (lvF3 inputs 57), SHA256F.natBit (lvF3 inputs 56), SHA256F.natBit (lvF3 inputs 55), SHA256F.natBit (lvF3 inputs 54), SHA256F.natBit (lvF3 inputs 53), SHA256F.natBit (lvF3 inputs 52), SHA256F.natBit (lvF3 inputs 51), SHA256F.natBit (lvF3 inputs 50), SHA256F.natBit (lvF3 inputs 49), SHA256F.natBit (lvF3 inputs 48), SHA256F.natBit (lvF3 inputs 47), SHA256F.natBit (lvF3 inputs 46), SHA256F.natBit (lvF3 inputs 45), SHA256F.natBit (lvF3 inputs 44), SHA256F.natBit (lvF3 inputs 43), SHA256F.natBit (lvF3 inputs 42), SHA256F.natBit (lvF3 inputs 41), SHA256F.natBit (lvF3 inputs 40), SHA256F.natBit (lvF3 inputs 39), SHA256F.natBit (lvF3 inputs 38), SHA256F.natBit (lvF3 inputs 37), SHA256F.natBit (lvF3 inputs 36), SHA256F.natBit (lvF3 inputs 35), SHA256F.natBit (lvF3 inputs 34)]

theorem bwF3p_eq (inputs : Nat → F) : bwF3p inputs = bitsOf inputs (h1Bits 3) := rfl

/-- **Output word 3.** -/
theorem finalW3 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF3.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF3.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 3 = SHA256.w32 (hWord inputs 3 + stateWord inputs 64 3) := by
  have hlv : ∀ k, k < 97 → lvF3 inputs k = 0 ∨ lvF3 inputs k = 1 := lvBitsF3 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final3 inputs hin0 hbz (allWrap2 inputs hin0 hroot 3 (by norm_num))
  rw [csA3_eq] at hA
  rw [csB3_eq] at hB
  rw [dsF3_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF3a (lvF3 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF3a (lvF3 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF3b (lvF3 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF3b (lvF3 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF3p (lvF3 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF3p (lvF3 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 3 := by rw [hvA, hWord, ← bwF3a_eq]; rfl
  have heB : B = stateWord inputs 64 3 := by rw [hvB, stateWord, ← bwF3b_eq]; rfl
  have heP : P = outWord inputs 3 := by rw [hvP, outWord, ← bwF3p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 4 -/

noncomputable def lvF4 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF4.getD k 0)

theorem leafBitsF4 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF4.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF4.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF4.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF4.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF4.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF4.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF4
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF4 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF4.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF4 inputs k = 0 ∨ lvF4 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF4 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF4.getD j (0, 0)).2 = mpF4.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF4a (lv : Nat → F) : Nat → F
  | 0 => lv 2
  | 1 => lv 33
  | 2 => lv 32
  | 3 => lv 31
  | 4 => lv 30
  | 5 => lv 29
  | 6 => lv 28
  | 7 => lv 27
  | 8 => lv 26
  | 9 => lv 25
  | 10 => lv 24
  | 11 => lv 23
  | 12 => lv 22
  | 13 => lv 21
  | 14 => lv 20
  | 15 => lv 19
  | 16 => lv 18
  | 17 => lv 17
  | 18 => lv 16
  | 19 => lv 15
  | 20 => lv 14
  | 21 => lv 13
  | 22 => lv 12
  | 23 => lv 11
  | 24 => lv 10
  | 25 => lv 9
  | 26 => lv 8
  | 27 => lv 7
  | 28 => lv 6
  | 29 => lv 5
  | 30 => lv 4
  | 31 => lv 3
  | _ => 0

theorem csA4_eq (lv : Nat → F) :
    csA4 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF4a lv j)) := rfl

theorem vbF4a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF4a lv j = 0 ∨ vF4a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 2 (by norm_num)
  | 1, _ => exact hlv 33 (by norm_num)
  | 2, _ => exact hlv 32 (by norm_num)
  | 3, _ => exact hlv 31 (by norm_num)
  | 4, _ => exact hlv 30 (by norm_num)
  | 5, _ => exact hlv 29 (by norm_num)
  | 6, _ => exact hlv 28 (by norm_num)
  | 7, _ => exact hlv 27 (by norm_num)
  | 8, _ => exact hlv 26 (by norm_num)
  | 9, _ => exact hlv 25 (by norm_num)
  | 10, _ => exact hlv 24 (by norm_num)
  | 11, _ => exact hlv 23 (by norm_num)
  | 12, _ => exact hlv 22 (by norm_num)
  | 13, _ => exact hlv 21 (by norm_num)
  | 14, _ => exact hlv 20 (by norm_num)
  | 15, _ => exact hlv 19 (by norm_num)
  | 16, _ => exact hlv 18 (by norm_num)
  | 17, _ => exact hlv 17 (by norm_num)
  | 18, _ => exact hlv 16 (by norm_num)
  | 19, _ => exact hlv 15 (by norm_num)
  | 20, _ => exact hlv 14 (by norm_num)
  | 21, _ => exact hlv 13 (by norm_num)
  | 22, _ => exact hlv 12 (by norm_num)
  | 23, _ => exact hlv 11 (by norm_num)
  | 24, _ => exact hlv 10 (by norm_num)
  | 25, _ => exact hlv 9 (by norm_num)
  | 26, _ => exact hlv 8 (by norm_num)
  | 27, _ => exact hlv 7 (by norm_num)
  | 28, _ => exact hlv 6 (by norm_num)
  | 29, _ => exact hlv 5 (by norm_num)
  | 30, _ => exact hlv 4 (by norm_num)
  | 31, _ => exact hlv 3 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF4a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF4 inputs 2), SHA256F.natBit (lvF4 inputs 33), SHA256F.natBit (lvF4 inputs 32), SHA256F.natBit (lvF4 inputs 31), SHA256F.natBit (lvF4 inputs 30), SHA256F.natBit (lvF4 inputs 29), SHA256F.natBit (lvF4 inputs 28), SHA256F.natBit (lvF4 inputs 27), SHA256F.natBit (lvF4 inputs 26), SHA256F.natBit (lvF4 inputs 25), SHA256F.natBit (lvF4 inputs 24), SHA256F.natBit (lvF4 inputs 23), SHA256F.natBit (lvF4 inputs 22), SHA256F.natBit (lvF4 inputs 21), SHA256F.natBit (lvF4 inputs 20), SHA256F.natBit (lvF4 inputs 19), SHA256F.natBit (lvF4 inputs 18), SHA256F.natBit (lvF4 inputs 17), SHA256F.natBit (lvF4 inputs 16), SHA256F.natBit (lvF4 inputs 15), SHA256F.natBit (lvF4 inputs 14), SHA256F.natBit (lvF4 inputs 13), SHA256F.natBit (lvF4 inputs 12), SHA256F.natBit (lvF4 inputs 11), SHA256F.natBit (lvF4 inputs 10), SHA256F.natBit (lvF4 inputs 9), SHA256F.natBit (lvF4 inputs 8), SHA256F.natBit (lvF4 inputs 7), SHA256F.natBit (lvF4 inputs 6), SHA256F.natBit (lvF4 inputs 5), SHA256F.natBit (lvF4 inputs 4), SHA256F.natBit (lvF4 inputs 3)]

theorem bwF4a_eq (inputs : Nat → F) : bwF4a inputs = bitsOf inputs (hinBits 4) := rfl

noncomputable def vF4b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB4_eq (lv : Nat → F) :
    csB4 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF4b lv j)) := rfl

theorem vbF4b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF4b lv j = 0 ∨ vF4b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF4b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF4 inputs 1), SHA256F.natBit (lvF4 inputs 96), SHA256F.natBit (lvF4 inputs 95), SHA256F.natBit (lvF4 inputs 94), SHA256F.natBit (lvF4 inputs 93), SHA256F.natBit (lvF4 inputs 92), SHA256F.natBit (lvF4 inputs 91), SHA256F.natBit (lvF4 inputs 90), SHA256F.natBit (lvF4 inputs 89), SHA256F.natBit (lvF4 inputs 88), SHA256F.natBit (lvF4 inputs 87), SHA256F.natBit (lvF4 inputs 86), SHA256F.natBit (lvF4 inputs 85), SHA256F.natBit (lvF4 inputs 84), SHA256F.natBit (lvF4 inputs 83), SHA256F.natBit (lvF4 inputs 82), SHA256F.natBit (lvF4 inputs 81), SHA256F.natBit (lvF4 inputs 80), SHA256F.natBit (lvF4 inputs 79), SHA256F.natBit (lvF4 inputs 78), SHA256F.natBit (lvF4 inputs 77), SHA256F.natBit (lvF4 inputs 76), SHA256F.natBit (lvF4 inputs 75), SHA256F.natBit (lvF4 inputs 74), SHA256F.natBit (lvF4 inputs 73), SHA256F.natBit (lvF4 inputs 72), SHA256F.natBit (lvF4 inputs 71), SHA256F.natBit (lvF4 inputs 70), SHA256F.natBit (lvF4 inputs 69), SHA256F.natBit (lvF4 inputs 68), SHA256F.natBit (lvF4 inputs 67), SHA256F.natBit (lvF4 inputs 66)]

theorem bwF4b_eq (inputs : Nat → F) : bwF4b inputs = bitsOf inputs (stateBits 64 4) := rfl

noncomputable def vF4p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF4_eq (lv : Nat → F) :
    dsF4 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF4p lv j)) := rfl

theorem vbF4p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF4p lv j = 0 ∨ vF4p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF4p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF4 inputs 65), SHA256F.natBit (lvF4 inputs 64), SHA256F.natBit (lvF4 inputs 63), SHA256F.natBit (lvF4 inputs 62), SHA256F.natBit (lvF4 inputs 61), SHA256F.natBit (lvF4 inputs 60), SHA256F.natBit (lvF4 inputs 59), SHA256F.natBit (lvF4 inputs 58), SHA256F.natBit (lvF4 inputs 57), SHA256F.natBit (lvF4 inputs 56), SHA256F.natBit (lvF4 inputs 55), SHA256F.natBit (lvF4 inputs 54), SHA256F.natBit (lvF4 inputs 53), SHA256F.natBit (lvF4 inputs 52), SHA256F.natBit (lvF4 inputs 51), SHA256F.natBit (lvF4 inputs 50), SHA256F.natBit (lvF4 inputs 49), SHA256F.natBit (lvF4 inputs 48), SHA256F.natBit (lvF4 inputs 47), SHA256F.natBit (lvF4 inputs 46), SHA256F.natBit (lvF4 inputs 45), SHA256F.natBit (lvF4 inputs 44), SHA256F.natBit (lvF4 inputs 43), SHA256F.natBit (lvF4 inputs 42), SHA256F.natBit (lvF4 inputs 41), SHA256F.natBit (lvF4 inputs 40), SHA256F.natBit (lvF4 inputs 39), SHA256F.natBit (lvF4 inputs 38), SHA256F.natBit (lvF4 inputs 37), SHA256F.natBit (lvF4 inputs 36), SHA256F.natBit (lvF4 inputs 35), SHA256F.natBit (lvF4 inputs 34)]

theorem bwF4p_eq (inputs : Nat → F) : bwF4p inputs = bitsOf inputs (h1Bits 4) := rfl

/-- **Output word 4.** -/
theorem finalW4 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF4.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF4.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 4 = SHA256.w32 (hWord inputs 4 + stateWord inputs 64 4) := by
  have hlv : ∀ k, k < 97 → lvF4 inputs k = 0 ∨ lvF4 inputs k = 1 := lvBitsF4 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final4 inputs hin0 hbz (allWrap2 inputs hin0 hroot 4 (by norm_num))
  rw [csA4_eq] at hA
  rw [csB4_eq] at hB
  rw [dsF4_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF4a (lvF4 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF4a (lvF4 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF4b (lvF4 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF4b (lvF4 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF4p (lvF4 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF4p (lvF4 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 4 := by rw [hvA, hWord, ← bwF4a_eq]; rfl
  have heB : B = stateWord inputs 64 4 := by rw [hvB, stateWord, ← bwF4b_eq]; rfl
  have heP : P = outWord inputs 4 := by rw [hvP, outWord, ← bwF4p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 5 -/

noncomputable def lvF5 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF5.getD k 0)

theorem leafBitsF5 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF5.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF5.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF5.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF5.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF5.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF5.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF5
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF5 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF5.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF5 inputs k = 0 ∨ lvF5 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF5 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF5.getD j (0, 0)).2 = mpF5.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF5a (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA5_eq (lv : Nat → F) :
    csA5 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF5a lv j)) := rfl

theorem vbF5a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF5a lv j = 0 ∨ vF5a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF5a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF5 inputs 1), SHA256F.natBit (lvF5 inputs 32), SHA256F.natBit (lvF5 inputs 31), SHA256F.natBit (lvF5 inputs 30), SHA256F.natBit (lvF5 inputs 29), SHA256F.natBit (lvF5 inputs 28), SHA256F.natBit (lvF5 inputs 27), SHA256F.natBit (lvF5 inputs 26), SHA256F.natBit (lvF5 inputs 25), SHA256F.natBit (lvF5 inputs 24), SHA256F.natBit (lvF5 inputs 23), SHA256F.natBit (lvF5 inputs 22), SHA256F.natBit (lvF5 inputs 21), SHA256F.natBit (lvF5 inputs 20), SHA256F.natBit (lvF5 inputs 19), SHA256F.natBit (lvF5 inputs 18), SHA256F.natBit (lvF5 inputs 17), SHA256F.natBit (lvF5 inputs 16), SHA256F.natBit (lvF5 inputs 15), SHA256F.natBit (lvF5 inputs 14), SHA256F.natBit (lvF5 inputs 13), SHA256F.natBit (lvF5 inputs 12), SHA256F.natBit (lvF5 inputs 11), SHA256F.natBit (lvF5 inputs 10), SHA256F.natBit (lvF5 inputs 9), SHA256F.natBit (lvF5 inputs 8), SHA256F.natBit (lvF5 inputs 7), SHA256F.natBit (lvF5 inputs 6), SHA256F.natBit (lvF5 inputs 5), SHA256F.natBit (lvF5 inputs 4), SHA256F.natBit (lvF5 inputs 3), SHA256F.natBit (lvF5 inputs 2)]

theorem bwF5a_eq (inputs : Nat → F) : bwF5a inputs = bitsOf inputs (hinBits 5) := rfl

noncomputable def vF5b (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB5_eq (lv : Nat → F) :
    csB5 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF5b lv j)) := rfl

theorem vbF5b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF5b lv j = 0 ∨ vF5b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF5b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF5 inputs 33), SHA256F.natBit (lvF5 inputs 96), SHA256F.natBit (lvF5 inputs 95), SHA256F.natBit (lvF5 inputs 94), SHA256F.natBit (lvF5 inputs 93), SHA256F.natBit (lvF5 inputs 92), SHA256F.natBit (lvF5 inputs 91), SHA256F.natBit (lvF5 inputs 90), SHA256F.natBit (lvF5 inputs 89), SHA256F.natBit (lvF5 inputs 88), SHA256F.natBit (lvF5 inputs 87), SHA256F.natBit (lvF5 inputs 86), SHA256F.natBit (lvF5 inputs 85), SHA256F.natBit (lvF5 inputs 84), SHA256F.natBit (lvF5 inputs 83), SHA256F.natBit (lvF5 inputs 82), SHA256F.natBit (lvF5 inputs 81), SHA256F.natBit (lvF5 inputs 80), SHA256F.natBit (lvF5 inputs 79), SHA256F.natBit (lvF5 inputs 78), SHA256F.natBit (lvF5 inputs 77), SHA256F.natBit (lvF5 inputs 76), SHA256F.natBit (lvF5 inputs 75), SHA256F.natBit (lvF5 inputs 74), SHA256F.natBit (lvF5 inputs 73), SHA256F.natBit (lvF5 inputs 72), SHA256F.natBit (lvF5 inputs 71), SHA256F.natBit (lvF5 inputs 70), SHA256F.natBit (lvF5 inputs 69), SHA256F.natBit (lvF5 inputs 68), SHA256F.natBit (lvF5 inputs 67), SHA256F.natBit (lvF5 inputs 66)]

theorem bwF5b_eq (inputs : Nat → F) : bwF5b inputs = bitsOf inputs (stateBits 64 5) := rfl

noncomputable def vF5p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF5_eq (lv : Nat → F) :
    dsF5 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF5p lv j)) := rfl

theorem vbF5p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF5p lv j = 0 ∨ vF5p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF5p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF5 inputs 65), SHA256F.natBit (lvF5 inputs 64), SHA256F.natBit (lvF5 inputs 63), SHA256F.natBit (lvF5 inputs 62), SHA256F.natBit (lvF5 inputs 61), SHA256F.natBit (lvF5 inputs 60), SHA256F.natBit (lvF5 inputs 59), SHA256F.natBit (lvF5 inputs 58), SHA256F.natBit (lvF5 inputs 57), SHA256F.natBit (lvF5 inputs 56), SHA256F.natBit (lvF5 inputs 55), SHA256F.natBit (lvF5 inputs 54), SHA256F.natBit (lvF5 inputs 53), SHA256F.natBit (lvF5 inputs 52), SHA256F.natBit (lvF5 inputs 51), SHA256F.natBit (lvF5 inputs 50), SHA256F.natBit (lvF5 inputs 49), SHA256F.natBit (lvF5 inputs 48), SHA256F.natBit (lvF5 inputs 47), SHA256F.natBit (lvF5 inputs 46), SHA256F.natBit (lvF5 inputs 45), SHA256F.natBit (lvF5 inputs 44), SHA256F.natBit (lvF5 inputs 43), SHA256F.natBit (lvF5 inputs 42), SHA256F.natBit (lvF5 inputs 41), SHA256F.natBit (lvF5 inputs 40), SHA256F.natBit (lvF5 inputs 39), SHA256F.natBit (lvF5 inputs 38), SHA256F.natBit (lvF5 inputs 37), SHA256F.natBit (lvF5 inputs 36), SHA256F.natBit (lvF5 inputs 35), SHA256F.natBit (lvF5 inputs 34)]

theorem bwF5p_eq (inputs : Nat → F) : bwF5p inputs = bitsOf inputs (h1Bits 5) := rfl

/-- **Output word 5.** -/
theorem finalW5 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF5.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF5.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 5 = SHA256.w32 (hWord inputs 5 + stateWord inputs 64 5) := by
  have hlv : ∀ k, k < 97 → lvF5 inputs k = 0 ∨ lvF5 inputs k = 1 := lvBitsF5 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final5 inputs hin0 hbz (allWrap2 inputs hin0 hroot 5 (by norm_num))
  rw [csA5_eq] at hA
  rw [csB5_eq] at hB
  rw [dsF5_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF5a (lvF5 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF5a (lvF5 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF5b (lvF5 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF5b (lvF5 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF5p (lvF5 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF5p (lvF5 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 5 := by rw [hvA, hWord, ← bwF5a_eq]; rfl
  have heB : B = stateWord inputs 64 5 := by rw [hvB, stateWord, ← bwF5b_eq]; rfl
  have heP : P = outWord inputs 5 := by rw [hvP, outWord, ← bwF5p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 6 -/

noncomputable def lvF6 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF6.getD k 0)

theorem leafBitsF6 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF6.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF6.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF6.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF6.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF6.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF6.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF6
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF6 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF6.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF6 inputs k = 0 ∨ lvF6 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF6 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF6.getD j (0, 0)).2 = mpF6.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF6a (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA6_eq (lv : Nat → F) :
    csA6 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF6a lv j)) := rfl

theorem vbF6a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF6a lv j = 0 ∨ vF6a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF6a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF6 inputs 33), SHA256F.natBit (lvF6 inputs 32), SHA256F.natBit (lvF6 inputs 31), SHA256F.natBit (lvF6 inputs 30), SHA256F.natBit (lvF6 inputs 29), SHA256F.natBit (lvF6 inputs 28), SHA256F.natBit (lvF6 inputs 27), SHA256F.natBit (lvF6 inputs 26), SHA256F.natBit (lvF6 inputs 25), SHA256F.natBit (lvF6 inputs 24), SHA256F.natBit (lvF6 inputs 23), SHA256F.natBit (lvF6 inputs 22), SHA256F.natBit (lvF6 inputs 21), SHA256F.natBit (lvF6 inputs 20), SHA256F.natBit (lvF6 inputs 19), SHA256F.natBit (lvF6 inputs 18), SHA256F.natBit (lvF6 inputs 17), SHA256F.natBit (lvF6 inputs 16), SHA256F.natBit (lvF6 inputs 15), SHA256F.natBit (lvF6 inputs 14), SHA256F.natBit (lvF6 inputs 13), SHA256F.natBit (lvF6 inputs 12), SHA256F.natBit (lvF6 inputs 11), SHA256F.natBit (lvF6 inputs 10), SHA256F.natBit (lvF6 inputs 9), SHA256F.natBit (lvF6 inputs 8), SHA256F.natBit (lvF6 inputs 7), SHA256F.natBit (lvF6 inputs 6), SHA256F.natBit (lvF6 inputs 5), SHA256F.natBit (lvF6 inputs 4), SHA256F.natBit (lvF6 inputs 3), SHA256F.natBit (lvF6 inputs 2)]

theorem bwF6a_eq (inputs : Nat → F) : bwF6a inputs = bitsOf inputs (hinBits 6) := rfl

noncomputable def vF6b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 96
  | 2 => lv 95
  | 3 => lv 94
  | 4 => lv 93
  | 5 => lv 92
  | 6 => lv 91
  | 7 => lv 90
  | 8 => lv 89
  | 9 => lv 88
  | 10 => lv 87
  | 11 => lv 86
  | 12 => lv 85
  | 13 => lv 84
  | 14 => lv 83
  | 15 => lv 82
  | 16 => lv 81
  | 17 => lv 80
  | 18 => lv 79
  | 19 => lv 78
  | 20 => lv 77
  | 21 => lv 76
  | 22 => lv 75
  | 23 => lv 74
  | 24 => lv 73
  | 25 => lv 72
  | 26 => lv 71
  | 27 => lv 70
  | 28 => lv 69
  | 29 => lv 68
  | 30 => lv 67
  | 31 => lv 66
  | _ => 0

theorem csB6_eq (lv : Nat → F) :
    csB6 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF6b lv j)) := rfl

theorem vbF6b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF6b lv j = 0 ∨ vF6b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 96 (by norm_num)
  | 2, _ => exact hlv 95 (by norm_num)
  | 3, _ => exact hlv 94 (by norm_num)
  | 4, _ => exact hlv 93 (by norm_num)
  | 5, _ => exact hlv 92 (by norm_num)
  | 6, _ => exact hlv 91 (by norm_num)
  | 7, _ => exact hlv 90 (by norm_num)
  | 8, _ => exact hlv 89 (by norm_num)
  | 9, _ => exact hlv 88 (by norm_num)
  | 10, _ => exact hlv 87 (by norm_num)
  | 11, _ => exact hlv 86 (by norm_num)
  | 12, _ => exact hlv 85 (by norm_num)
  | 13, _ => exact hlv 84 (by norm_num)
  | 14, _ => exact hlv 83 (by norm_num)
  | 15, _ => exact hlv 82 (by norm_num)
  | 16, _ => exact hlv 81 (by norm_num)
  | 17, _ => exact hlv 80 (by norm_num)
  | 18, _ => exact hlv 79 (by norm_num)
  | 19, _ => exact hlv 78 (by norm_num)
  | 20, _ => exact hlv 77 (by norm_num)
  | 21, _ => exact hlv 76 (by norm_num)
  | 22, _ => exact hlv 75 (by norm_num)
  | 23, _ => exact hlv 74 (by norm_num)
  | 24, _ => exact hlv 73 (by norm_num)
  | 25, _ => exact hlv 72 (by norm_num)
  | 26, _ => exact hlv 71 (by norm_num)
  | 27, _ => exact hlv 70 (by norm_num)
  | 28, _ => exact hlv 69 (by norm_num)
  | 29, _ => exact hlv 68 (by norm_num)
  | 30, _ => exact hlv 67 (by norm_num)
  | 31, _ => exact hlv 66 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF6b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF6 inputs 1), SHA256F.natBit (lvF6 inputs 96), SHA256F.natBit (lvF6 inputs 95), SHA256F.natBit (lvF6 inputs 94), SHA256F.natBit (lvF6 inputs 93), SHA256F.natBit (lvF6 inputs 92), SHA256F.natBit (lvF6 inputs 91), SHA256F.natBit (lvF6 inputs 90), SHA256F.natBit (lvF6 inputs 89), SHA256F.natBit (lvF6 inputs 88), SHA256F.natBit (lvF6 inputs 87), SHA256F.natBit (lvF6 inputs 86), SHA256F.natBit (lvF6 inputs 85), SHA256F.natBit (lvF6 inputs 84), SHA256F.natBit (lvF6 inputs 83), SHA256F.natBit (lvF6 inputs 82), SHA256F.natBit (lvF6 inputs 81), SHA256F.natBit (lvF6 inputs 80), SHA256F.natBit (lvF6 inputs 79), SHA256F.natBit (lvF6 inputs 78), SHA256F.natBit (lvF6 inputs 77), SHA256F.natBit (lvF6 inputs 76), SHA256F.natBit (lvF6 inputs 75), SHA256F.natBit (lvF6 inputs 74), SHA256F.natBit (lvF6 inputs 73), SHA256F.natBit (lvF6 inputs 72), SHA256F.natBit (lvF6 inputs 71), SHA256F.natBit (lvF6 inputs 70), SHA256F.natBit (lvF6 inputs 69), SHA256F.natBit (lvF6 inputs 68), SHA256F.natBit (lvF6 inputs 67), SHA256F.natBit (lvF6 inputs 66)]

theorem bwF6b_eq (inputs : Nat → F) : bwF6b inputs = bitsOf inputs (stateBits 64 6) := rfl

noncomputable def vF6p (lv : Nat → F) : Nat → F
  | 0 => lv 65
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem dsF6_eq (lv : Nat → F) :
    dsF6 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF6p lv j)) := rfl

theorem vbF6p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF6p lv j = 0 ∨ vF6p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 65 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF6p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF6 inputs 65), SHA256F.natBit (lvF6 inputs 64), SHA256F.natBit (lvF6 inputs 63), SHA256F.natBit (lvF6 inputs 62), SHA256F.natBit (lvF6 inputs 61), SHA256F.natBit (lvF6 inputs 60), SHA256F.natBit (lvF6 inputs 59), SHA256F.natBit (lvF6 inputs 58), SHA256F.natBit (lvF6 inputs 57), SHA256F.natBit (lvF6 inputs 56), SHA256F.natBit (lvF6 inputs 55), SHA256F.natBit (lvF6 inputs 54), SHA256F.natBit (lvF6 inputs 53), SHA256F.natBit (lvF6 inputs 52), SHA256F.natBit (lvF6 inputs 51), SHA256F.natBit (lvF6 inputs 50), SHA256F.natBit (lvF6 inputs 49), SHA256F.natBit (lvF6 inputs 48), SHA256F.natBit (lvF6 inputs 47), SHA256F.natBit (lvF6 inputs 46), SHA256F.natBit (lvF6 inputs 45), SHA256F.natBit (lvF6 inputs 44), SHA256F.natBit (lvF6 inputs 43), SHA256F.natBit (lvF6 inputs 42), SHA256F.natBit (lvF6 inputs 41), SHA256F.natBit (lvF6 inputs 40), SHA256F.natBit (lvF6 inputs 39), SHA256F.natBit (lvF6 inputs 38), SHA256F.natBit (lvF6 inputs 37), SHA256F.natBit (lvF6 inputs 36), SHA256F.natBit (lvF6 inputs 35), SHA256F.natBit (lvF6 inputs 34)]

theorem bwF6p_eq (inputs : Nat → F) : bwF6p inputs = bitsOf inputs (h1Bits 6) := rfl

/-- **Output word 6.** -/
theorem finalW6 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF6.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF6.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 6 = SHA256.w32 (hWord inputs 6 + stateWord inputs 64 6) := by
  have hlv : ∀ k, k < 97 → lvF6 inputs k = 0 ∨ lvF6 inputs k = 1 := lvBitsF6 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final6 inputs hin0 hbz (allWrap2 inputs hin0 hroot 6 (by norm_num))
  rw [csA6_eq] at hA
  rw [csB6_eq] at hB
  rw [dsF6_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF6a (lvF6 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF6a (lvF6 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF6b (lvF6 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF6b (lvF6 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF6p (lvF6 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF6p (lvF6 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 6 := by rw [hvA, hWord, ← bwF6a_eq]; rfl
  have heB : B = stateWord inputs 64 6 := by rw [hvB, stateWord, ← bwF6b_eq]; rfl
  have heP : P = outWord inputs 6 := by rw [hvP, outWord, ← bwF6p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-! #### Output word 7 -/

noncomputable def lvF7 (inputs : Nat → F) : Nat → F :=
  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF7.getD k 0)

theorem leafBitsF7 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF7.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF7.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF7.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF7.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF7.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF7.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF7
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF7 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF7.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF7 inputs k = 0 ∨ lvF7 inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF7 inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF7.getD j (0, 0)).2 = mpF7.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb

noncomputable def vF7a (lv : Nat → F) : Nat → F
  | 0 => lv 33
  | 1 => lv 32
  | 2 => lv 31
  | 3 => lv 30
  | 4 => lv 29
  | 5 => lv 28
  | 6 => lv 27
  | 7 => lv 26
  | 8 => lv 25
  | 9 => lv 24
  | 10 => lv 23
  | 11 => lv 22
  | 12 => lv 21
  | 13 => lv 20
  | 14 => lv 19
  | 15 => lv 18
  | 16 => lv 17
  | 17 => lv 16
  | 18 => lv 15
  | 19 => lv 14
  | 20 => lv 13
  | 21 => lv 12
  | 22 => lv 11
  | 23 => lv 10
  | 24 => lv 9
  | 25 => lv 8
  | 26 => lv 7
  | 27 => lv 6
  | 28 => lv 5
  | 29 => lv 4
  | 30 => lv 3
  | 31 => lv 2
  | _ => 0

theorem csA7_eq (lv : Nat → F) :
    csA7 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF7a lv j)) := rfl

theorem vbF7a (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF7a lv j = 0 ∨ vF7a lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 33 (by norm_num)
  | 1, _ => exact hlv 32 (by norm_num)
  | 2, _ => exact hlv 31 (by norm_num)
  | 3, _ => exact hlv 30 (by norm_num)
  | 4, _ => exact hlv 29 (by norm_num)
  | 5, _ => exact hlv 28 (by norm_num)
  | 6, _ => exact hlv 27 (by norm_num)
  | 7, _ => exact hlv 26 (by norm_num)
  | 8, _ => exact hlv 25 (by norm_num)
  | 9, _ => exact hlv 24 (by norm_num)
  | 10, _ => exact hlv 23 (by norm_num)
  | 11, _ => exact hlv 22 (by norm_num)
  | 12, _ => exact hlv 21 (by norm_num)
  | 13, _ => exact hlv 20 (by norm_num)
  | 14, _ => exact hlv 19 (by norm_num)
  | 15, _ => exact hlv 18 (by norm_num)
  | 16, _ => exact hlv 17 (by norm_num)
  | 17, _ => exact hlv 16 (by norm_num)
  | 18, _ => exact hlv 15 (by norm_num)
  | 19, _ => exact hlv 14 (by norm_num)
  | 20, _ => exact hlv 13 (by norm_num)
  | 21, _ => exact hlv 12 (by norm_num)
  | 22, _ => exact hlv 11 (by norm_num)
  | 23, _ => exact hlv 10 (by norm_num)
  | 24, _ => exact hlv 9 (by norm_num)
  | 25, _ => exact hlv 8 (by norm_num)
  | 26, _ => exact hlv 7 (by norm_num)
  | 27, _ => exact hlv 6 (by norm_num)
  | 28, _ => exact hlv 5 (by norm_num)
  | 29, _ => exact hlv 4 (by norm_num)
  | 30, _ => exact hlv 3 (by norm_num)
  | 31, _ => exact hlv 2 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF7a (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF7 inputs 33), SHA256F.natBit (lvF7 inputs 32), SHA256F.natBit (lvF7 inputs 31), SHA256F.natBit (lvF7 inputs 30), SHA256F.natBit (lvF7 inputs 29), SHA256F.natBit (lvF7 inputs 28), SHA256F.natBit (lvF7 inputs 27), SHA256F.natBit (lvF7 inputs 26), SHA256F.natBit (lvF7 inputs 25), SHA256F.natBit (lvF7 inputs 24), SHA256F.natBit (lvF7 inputs 23), SHA256F.natBit (lvF7 inputs 22), SHA256F.natBit (lvF7 inputs 21), SHA256F.natBit (lvF7 inputs 20), SHA256F.natBit (lvF7 inputs 19), SHA256F.natBit (lvF7 inputs 18), SHA256F.natBit (lvF7 inputs 17), SHA256F.natBit (lvF7 inputs 16), SHA256F.natBit (lvF7 inputs 15), SHA256F.natBit (lvF7 inputs 14), SHA256F.natBit (lvF7 inputs 13), SHA256F.natBit (lvF7 inputs 12), SHA256F.natBit (lvF7 inputs 11), SHA256F.natBit (lvF7 inputs 10), SHA256F.natBit (lvF7 inputs 9), SHA256F.natBit (lvF7 inputs 8), SHA256F.natBit (lvF7 inputs 7), SHA256F.natBit (lvF7 inputs 6), SHA256F.natBit (lvF7 inputs 5), SHA256F.natBit (lvF7 inputs 4), SHA256F.natBit (lvF7 inputs 3), SHA256F.natBit (lvF7 inputs 2)]

theorem bwF7a_eq (inputs : Nat → F) : bwF7a inputs = bitsOf inputs (hinBits 7) := rfl

noncomputable def vF7b (lv : Nat → F) : Nat → F
  | 0 => lv 1
  | 1 => lv 64
  | 2 => lv 63
  | 3 => lv 62
  | 4 => lv 61
  | 5 => lv 60
  | 6 => lv 59
  | 7 => lv 58
  | 8 => lv 57
  | 9 => lv 56
  | 10 => lv 55
  | 11 => lv 54
  | 12 => lv 53
  | 13 => lv 52
  | 14 => lv 51
  | 15 => lv 50
  | 16 => lv 49
  | 17 => lv 48
  | 18 => lv 47
  | 19 => lv 46
  | 20 => lv 45
  | 21 => lv 44
  | 22 => lv 43
  | 23 => lv 42
  | 24 => lv 41
  | 25 => lv 40
  | 26 => lv 39
  | 27 => lv 38
  | 28 => lv 37
  | 29 => lv 36
  | 30 => lv 35
  | 31 => lv 34
  | _ => 0

theorem csB7_eq (lv : Nat → F) :
    csB7 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF7b lv j)) := rfl

theorem vbF7b (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF7b lv j = 0 ∨ vF7b lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 1 (by norm_num)
  | 1, _ => exact hlv 64 (by norm_num)
  | 2, _ => exact hlv 63 (by norm_num)
  | 3, _ => exact hlv 62 (by norm_num)
  | 4, _ => exact hlv 61 (by norm_num)
  | 5, _ => exact hlv 60 (by norm_num)
  | 6, _ => exact hlv 59 (by norm_num)
  | 7, _ => exact hlv 58 (by norm_num)
  | 8, _ => exact hlv 57 (by norm_num)
  | 9, _ => exact hlv 56 (by norm_num)
  | 10, _ => exact hlv 55 (by norm_num)
  | 11, _ => exact hlv 54 (by norm_num)
  | 12, _ => exact hlv 53 (by norm_num)
  | 13, _ => exact hlv 52 (by norm_num)
  | 14, _ => exact hlv 51 (by norm_num)
  | 15, _ => exact hlv 50 (by norm_num)
  | 16, _ => exact hlv 49 (by norm_num)
  | 17, _ => exact hlv 48 (by norm_num)
  | 18, _ => exact hlv 47 (by norm_num)
  | 19, _ => exact hlv 46 (by norm_num)
  | 20, _ => exact hlv 45 (by norm_num)
  | 21, _ => exact hlv 44 (by norm_num)
  | 22, _ => exact hlv 43 (by norm_num)
  | 23, _ => exact hlv 42 (by norm_num)
  | 24, _ => exact hlv 41 (by norm_num)
  | 25, _ => exact hlv 40 (by norm_num)
  | 26, _ => exact hlv 39 (by norm_num)
  | 27, _ => exact hlv 38 (by norm_num)
  | 28, _ => exact hlv 37 (by norm_num)
  | 29, _ => exact hlv 36 (by norm_num)
  | 30, _ => exact hlv 35 (by norm_num)
  | 31, _ => exact hlv 34 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF7b (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF7 inputs 1), SHA256F.natBit (lvF7 inputs 64), SHA256F.natBit (lvF7 inputs 63), SHA256F.natBit (lvF7 inputs 62), SHA256F.natBit (lvF7 inputs 61), SHA256F.natBit (lvF7 inputs 60), SHA256F.natBit (lvF7 inputs 59), SHA256F.natBit (lvF7 inputs 58), SHA256F.natBit (lvF7 inputs 57), SHA256F.natBit (lvF7 inputs 56), SHA256F.natBit (lvF7 inputs 55), SHA256F.natBit (lvF7 inputs 54), SHA256F.natBit (lvF7 inputs 53), SHA256F.natBit (lvF7 inputs 52), SHA256F.natBit (lvF7 inputs 51), SHA256F.natBit (lvF7 inputs 50), SHA256F.natBit (lvF7 inputs 49), SHA256F.natBit (lvF7 inputs 48), SHA256F.natBit (lvF7 inputs 47), SHA256F.natBit (lvF7 inputs 46), SHA256F.natBit (lvF7 inputs 45), SHA256F.natBit (lvF7 inputs 44), SHA256F.natBit (lvF7 inputs 43), SHA256F.natBit (lvF7 inputs 42), SHA256F.natBit (lvF7 inputs 41), SHA256F.natBit (lvF7 inputs 40), SHA256F.natBit (lvF7 inputs 39), SHA256F.natBit (lvF7 inputs 38), SHA256F.natBit (lvF7 inputs 37), SHA256F.natBit (lvF7 inputs 36), SHA256F.natBit (lvF7 inputs 35), SHA256F.natBit (lvF7 inputs 34)]

theorem bwF7b_eq (inputs : Nat → F) : bwF7b inputs = bitsOf inputs (stateBits 64 7) := rfl

noncomputable def vF7p (lv : Nat → F) : Nat → F
  | 0 => lv 96
  | 1 => lv 95
  | 2 => lv 94
  | 3 => lv 93
  | 4 => lv 92
  | 5 => lv 91
  | 6 => lv 90
  | 7 => lv 89
  | 8 => lv 88
  | 9 => lv 87
  | 10 => lv 86
  | 11 => lv 85
  | 12 => lv 84
  | 13 => lv 83
  | 14 => lv 82
  | 15 => lv 81
  | 16 => lv 80
  | 17 => lv 79
  | 18 => lv 78
  | 19 => lv 77
  | 20 => lv 76
  | 21 => lv 75
  | 22 => lv 74
  | 23 => lv 73
  | 24 => lv 72
  | 25 => lv 71
  | 26 => lv 70
  | 27 => lv 69
  | 28 => lv 68
  | 29 => lv 67
  | 30 => lv 66
  | 31 => lv 65
  | _ => 0

theorem dsF7_eq (lv : Nat → F) :
    dsF7 lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF7p lv j)) := rfl

theorem vbF7p (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :
    ∀ j, j < 32 → vF7p lv j = 0 ∨ vF7p lv j = 1 := by
  intro j hj
  match j, hj with
  | 0, _ => exact hlv 96 (by norm_num)
  | 1, _ => exact hlv 95 (by norm_num)
  | 2, _ => exact hlv 94 (by norm_num)
  | 3, _ => exact hlv 93 (by norm_num)
  | 4, _ => exact hlv 92 (by norm_num)
  | 5, _ => exact hlv 91 (by norm_num)
  | 6, _ => exact hlv 90 (by norm_num)
  | 7, _ => exact hlv 89 (by norm_num)
  | 8, _ => exact hlv 88 (by norm_num)
  | 9, _ => exact hlv 87 (by norm_num)
  | 10, _ => exact hlv 86 (by norm_num)
  | 11, _ => exact hlv 85 (by norm_num)
  | 12, _ => exact hlv 84 (by norm_num)
  | 13, _ => exact hlv 83 (by norm_num)
  | 14, _ => exact hlv 82 (by norm_num)
  | 15, _ => exact hlv 81 (by norm_num)
  | 16, _ => exact hlv 80 (by norm_num)
  | 17, _ => exact hlv 79 (by norm_num)
  | 18, _ => exact hlv 78 (by norm_num)
  | 19, _ => exact hlv 77 (by norm_num)
  | 20, _ => exact hlv 76 (by norm_num)
  | 21, _ => exact hlv 75 (by norm_num)
  | 22, _ => exact hlv 74 (by norm_num)
  | 23, _ => exact hlv 73 (by norm_num)
  | 24, _ => exact hlv 72 (by norm_num)
  | 25, _ => exact hlv 71 (by norm_num)
  | 26, _ => exact hlv 70 (by norm_num)
  | 27, _ => exact hlv 69 (by norm_num)
  | 28, _ => exact hlv 68 (by norm_num)
  | 29, _ => exact hlv 67 (by norm_num)
  | 30, _ => exact hlv 66 (by norm_num)
  | 31, _ => exact hlv 65 (by norm_num)
  | (n + 32), hx => exact absurd hx (by omega)

noncomputable def bwF7p (inputs : Nat → F) : List Nat :=
  [SHA256F.natBit (lvF7 inputs 96), SHA256F.natBit (lvF7 inputs 95), SHA256F.natBit (lvF7 inputs 94), SHA256F.natBit (lvF7 inputs 93), SHA256F.natBit (lvF7 inputs 92), SHA256F.natBit (lvF7 inputs 91), SHA256F.natBit (lvF7 inputs 90), SHA256F.natBit (lvF7 inputs 89), SHA256F.natBit (lvF7 inputs 88), SHA256F.natBit (lvF7 inputs 87), SHA256F.natBit (lvF7 inputs 86), SHA256F.natBit (lvF7 inputs 85), SHA256F.natBit (lvF7 inputs 84), SHA256F.natBit (lvF7 inputs 83), SHA256F.natBit (lvF7 inputs 82), SHA256F.natBit (lvF7 inputs 81), SHA256F.natBit (lvF7 inputs 80), SHA256F.natBit (lvF7 inputs 79), SHA256F.natBit (lvF7 inputs 78), SHA256F.natBit (lvF7 inputs 77), SHA256F.natBit (lvF7 inputs 76), SHA256F.natBit (lvF7 inputs 75), SHA256F.natBit (lvF7 inputs 74), SHA256F.natBit (lvF7 inputs 73), SHA256F.natBit (lvF7 inputs 72), SHA256F.natBit (lvF7 inputs 71), SHA256F.natBit (lvF7 inputs 70), SHA256F.natBit (lvF7 inputs 69), SHA256F.natBit (lvF7 inputs 68), SHA256F.natBit (lvF7 inputs 67), SHA256F.natBit (lvF7 inputs 66), SHA256F.natBit (lvF7 inputs 65)]

theorem bwF7p_eq (inputs : Nat → F) : bwF7p inputs = bitsOf inputs (h1Bits 7) := rfl

/-- **Output word 7.** -/
theorem finalW7 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF7.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF7.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs 7 = SHA256.w32 (hWord inputs 7 + stateWord inputs 64 7) := by
  have hlv : ∀ k, k < 97 → lvF7 inputs k = 0 ∨ lvF7 inputs k = 1 := lvBitsF7 inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final7 inputs hin0 hbz (allWrap2 inputs hin0 hroot 7 (by norm_num))
  rw [csA7_eq] at hA
  rw [csB7_eq] at hB
  rw [dsF7_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF7a (lvF7 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF7a (lvF7 inputs) hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF7b (lvF7 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF7b (lvF7 inputs) hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF7p (lvF7 inputs) j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF7p (lvF7 inputs) hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs 7 := by rw [hvA, hWord, ← bwF7a_eq]; rfl
  have heB : B = stateWord inputs 64 7 := by rw [hvB, stateWord, ← bwF7b_eq]; rfl
  have heP : P = outWord inputs 7 := by rw [hvP, outWord, ← bwF7p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres

/-- **`hout`.** -/
theorem hout [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpAt i).getD j (0, 0)).1 = 0)
    (hbzl : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpLAt i).getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    ∀ i, i < 8 → outWord inputs i = SHA256.w32 (hWord inputs i + stateWord inputs 64 i) := by
  intro i hi
  match i, hi with
  | 0, _ => exact finalW0 inputs hin0 (hbz 0 (by norm_num)) (hbzl 0 (by norm_num)) hroot
  | 1, _ => exact finalW1 inputs hin0 (hbz 1 (by norm_num)) (hbzl 1 (by norm_num)) hroot
  | 2, _ => exact finalW2 inputs hin0 (hbz 2 (by norm_num)) (hbzl 2 (by norm_num)) hroot
  | 3, _ => exact finalW3 inputs hin0 (hbz 3 (by norm_num)) (hbzl 3 (by norm_num)) hroot
  | 4, _ => exact finalW4 inputs hin0 (hbz 4 (by norm_num)) (hbzl 4 (by norm_num)) hroot
  | 5, _ => exact finalW5 inputs hin0 (hbz 5 (by norm_num)) (hbzl 5 (by norm_num)) hroot
  | 6, _ => exact finalW6 inputs hin0 (hbz 6 (by norm_num)) (hbzl 6 (by norm_num)) hroot
  | 7, _ => exact finalW7 inputs hin0 (hbz 7 (by norm_num)) (hbzl 7 (by norm_num)) hroot
  | (n + 8), hx => exact absurd hx (by omega)

end Sha256Blk
