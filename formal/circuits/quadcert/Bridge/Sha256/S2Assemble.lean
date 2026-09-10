/-
# The deployed SHA-256 circuit computes the SHA-256 block transform

The assembly. `SHA256.sha256_soundness` states the block transform in terms of abstract
`h`, `w`, `s` and `out`; this file instantiates them with the circuit's own words — `hWord`,
`wWord`, `stateWord`, `outWord` — and discharges each of its seven hypotheses from the bridges:

| hypothesis | source |
|---|---|
| `hcopy`, `hinit`, `hshift` | `S2State`, generic in `t` |
| `hsched` | 48 x `sched t` |
| `hrnd_a` | 64 x `rndR7_t` |
| `hrnd_e` | 64 x `rndR6_t` |
| `hout` | `S2FinalComp.hout` |

`hcopy` and `hinit` are structural: `wordBits t` *is* `input_block t` below 16, and
`stateBits 0 i` *is* `hinBits i`. `hshift` needed no per-round work either -- one lemma about
`stateBits` covers all 64 rounds.

## What this theorem assumes

That the circuit's assertion nodes evaluate to zero. Those hypotheses are stated here per
family, over the generated `(assertion, bit)` tables, rather than derived from `Accepts`:
`S2Sound.assertions_zero_of_bytes` proves every asserted node is zero from the committed bytes,
but connecting it to these tables needs a membership check for each of the ~41,000 nodes the
bridges name, which is not done. That is the one remaining link between this theorem and
`bytes -> spec`.
-/


import quadcert.Bridge.Sha256.S2CompA
import quadcert.Bridge.Sha256.S2CompB
import quadcert.Bridge.Sha256.S2CompC
import quadcert.Bridge.Sha256.S2CompD
import quadcert.Bridge.Sha256.S2CompE
import quadcert.Bridge.Sha256.S2CompF
import quadcert.Bridge.Sha256.S2CompG
import quadcert.Bridge.Sha256.S2CompH
import quadcert.Bridge.Sha256.S2CRndA
import quadcert.Bridge.Sha256.S2CRndB
import quadcert.Bridge.Sha256.S2CRndC
import quadcert.Bridge.Sha256.S2CRndD
import quadcert.Bridge.Sha256.S2CRndE
import quadcert.Bridge.Sha256.S2CRndF
import quadcert.Bridge.Sha256.S2CRndG
import quadcert.Bridge.Sha256.S2CRndH
import quadcert.Bridge.Sha256.S2CRndI
import quadcert.Bridge.Sha256.S2CRndJ
import quadcert.Bridge.Sha256.S2CRndK
import quadcert.Bridge.Sha256.S2CRndL
import quadcert.Bridge.Sha256.S2CRndM
import quadcert.Bridge.Sha256.S2CRndN
import quadcert.Bridge.Sha256.S2CRndO
import quadcert.Bridge.Sha256.S2CRndP
import quadcert.Bridge.Sha256.S2FinalComp
import SHA.Sound

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- The 48 schedule cones' booleanity tables. -/
def bpSchedAt : Nat → List (Nat × Nat)
  | 16 => bpS16
  | 17 => bpS17
  | 18 => bpS18
  | 19 => bpS19
  | 20 => bpS20
  | 21 => bpS21
  | 22 => bpS22
  | 23 => bpS23
  | 24 => bpS24
  | 25 => bpS25
  | 26 => bpS26
  | 27 => bpS27
  | 28 => bpS28
  | 29 => bpS29
  | 30 => bpS30
  | 31 => bpS31
  | 32 => bpS32
  | 33 => bpS33
  | 34 => bpS34
  | 35 => bpS35
  | 36 => bpS36
  | 37 => bpS37
  | 38 => bpS38
  | 39 => bpS39
  | 40 => bpS40
  | 41 => bpS41
  | 42 => bpS42
  | 43 => bpS43
  | 44 => bpS44
  | 45 => bpS45
  | 46 => bpS46
  | 47 => bpS47
  | 48 => bpS48
  | 49 => bpS49
  | 50 => bpS50
  | 51 => bpS51
  | 52 => bpS52
  | 53 => bpS53
  | 54 => bpS54
  | 55 => bpS55
  | 56 => bpS56
  | 57 => bpS57
  | 58 => bpS58
  | 59 => bpS59
  | 60 => bpS60
  | 61 => bpS61
  | 62 => bpS62
  | 63 => bpS63
  | _ => []

/-- The 64 `n = 6` round cones' booleanity tables. -/
def bpR6At : Nat → List (Nat × Nat)
  | 0 => bpR6_0
  | 1 => bpR6_1
  | 2 => bpR6_2
  | 3 => bpR6_3
  | 4 => bpR6_4
  | 5 => bpR6_5
  | 6 => bpR6_6
  | 7 => bpR6_7
  | 8 => bpR6_8
  | 9 => bpR6_9
  | 10 => bpR6_10
  | 11 => bpR6_11
  | 12 => bpR6_12
  | 13 => bpR6_13
  | 14 => bpR6_14
  | 15 => bpR6_15
  | 16 => bpR6_16
  | 17 => bpR6_17
  | 18 => bpR6_18
  | 19 => bpR6_19
  | 20 => bpR6_20
  | 21 => bpR6_21
  | 22 => bpR6_22
  | 23 => bpR6_23
  | 24 => bpR6_24
  | 25 => bpR6_25
  | 26 => bpR6_26
  | 27 => bpR6_27
  | 28 => bpR6_28
  | 29 => bpR6_29
  | 30 => bpR6_30
  | 31 => bpR6_31
  | 32 => bpR6_32
  | 33 => bpR6_33
  | 34 => bpR6_34
  | 35 => bpR6_35
  | 36 => bpR6_36
  | 37 => bpR6_37
  | 38 => bpR6_38
  | 39 => bpR6_39
  | 40 => bpR6_40
  | 41 => bpR6_41
  | 42 => bpR6_42
  | 43 => bpR6_43
  | 44 => bpR6_44
  | 45 => bpR6_45
  | 46 => bpR6_46
  | 47 => bpR6_47
  | 48 => bpR6_48
  | 49 => bpR6_49
  | 50 => bpR6_50
  | 51 => bpR6_51
  | 52 => bpR6_52
  | 53 => bpR6_53
  | 54 => bpR6_54
  | 55 => bpR6_55
  | 56 => bpR6_56
  | 57 => bpR6_57
  | 58 => bpR6_58
  | 59 => bpR6_59
  | 60 => bpR6_60
  | 61 => bpR6_61
  | 62 => bpR6_62
  | 63 => bpR6_63
  | _ => []

/-- The 64 `n = 7` round cones' booleanity tables. -/
def bpR7At : Nat → List (Nat × Nat)
  | 0 => bpR7_0
  | 1 => bpR7_1
  | 2 => bpR7_2
  | 3 => bpR7_3
  | 4 => bpR7_4
  | 5 => bpR7_5
  | 6 => bpR7_6
  | 7 => bpR7_7
  | 8 => bpR7_8
  | 9 => bpR7_9
  | 10 => bpR7_10
  | 11 => bpR7_11
  | 12 => bpR7_12
  | 13 => bpR7_13
  | 14 => bpR7_14
  | 15 => bpR7_15
  | 16 => bpR7_16
  | 17 => bpR7_17
  | 18 => bpR7_18
  | 19 => bpR7_19
  | 20 => bpR7_20
  | 21 => bpR7_21
  | 22 => bpR7_22
  | 23 => bpR7_23
  | 24 => bpR7_24
  | 25 => bpR7_25
  | 26 => bpR7_26
  | 27 => bpR7_27
  | 28 => bpR7_28
  | 29 => bpR7_29
  | 30 => bpR7_30
  | 31 => bpR7_31
  | 32 => bpR7_32
  | 33 => bpR7_33
  | 34 => bpR7_34
  | 35 => bpR7_35
  | 36 => bpR7_36
  | 37 => bpR7_37
  | 38 => bpR7_38
  | 39 => bpR7_39
  | 40 => bpR7_40
  | 41 => bpR7_41
  | 42 => bpR7_42
  | 43 => bpR7_43
  | 44 => bpR7_44
  | 45 => bpR7_45
  | 46 => bpR7_46
  | 47 => bpR7_47
  | 48 => bpR7_48
  | 49 => bpR7_49
  | 50 => bpR7_50
  | 51 => bpR7_51
  | 52 => bpR7_52
  | 53 => bpR7_53
  | 54 => bpR7_54
  | 55 => bpR7_55
  | 56 => bpR7_56
  | 57 => bpR7_57
  | 58 => bpR7_58
  | 59 => bpR7_59
  | 60 => bpR7_60
  | 61 => bpR7_61
  | 62 => bpR7_62
  | 63 => bpR7_63
  | _ => []

variable {F : Type} [Field F]

/-- **`hsched` for every `t`.** -/
theorem schedAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbSched : ∀ t, 16 ≤ t → t < 64 → ∀ j, j < 160 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpSchedAt t).getD j (0, 0)).1 = 0)
    (hrSched : ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0) :
    ∀ t, 16 ≤ t → t < 64 → wWord inputs t
      = SHA256.w32 (SHA256.sigma1 (wWord inputs (t - 2)) + wWord inputs (t - 7)
          + SHA256.sigma0 (wWord inputs (t - 15)) + wWord inputs (t - 16)) := by
  intro t h16 h64
  match t, h16, h64 with
  | 0, hx, _ => exact absurd hx (by omega)
  | 1, hx, _ => exact absurd hx (by omega)
  | 2, hx, _ => exact absurd hx (by omega)
  | 3, hx, _ => exact absurd hx (by omega)
  | 4, hx, _ => exact absurd hx (by omega)
  | 5, hx, _ => exact absurd hx (by omega)
  | 6, hx, _ => exact absurd hx (by omega)
  | 7, hx, _ => exact absurd hx (by omega)
  | 8, hx, _ => exact absurd hx (by omega)
  | 9, hx, _ => exact absurd hx (by omega)
  | 10, hx, _ => exact absurd hx (by omega)
  | 11, hx, _ => exact absurd hx (by omega)
  | 12, hx, _ => exact absurd hx (by omega)
  | 13, hx, _ => exact absurd hx (by omega)
  | 14, hx, _ => exact absurd hx (by omega)
  | 15, hx, _ => exact absurd hx (by omega)
  | 16, _, _ =>
    simp only [wWord, show (16 : Nat) - 2 = 14 from rfl, show (16 : Nat) - 7 = 9 from rfl,
      show (16 : Nat) - 15 = 1 from rfl, show (16 : Nat) - 16 = 0 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 16)) = _ from
      sched16 inputs hin0 (hbSched 16 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 17, _, _ =>
    simp only [wWord, show (17 : Nat) - 2 = 15 from rfl, show (17 : Nat) - 7 = 10 from rfl,
      show (17 : Nat) - 15 = 2 from rfl, show (17 : Nat) - 16 = 1 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 17)) = _ from
      sched17 inputs hin0 (hbSched 17 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 18, _, _ =>
    simp only [wWord, show (18 : Nat) - 2 = 16 from rfl, show (18 : Nat) - 7 = 11 from rfl,
      show (18 : Nat) - 15 = 3 from rfl, show (18 : Nat) - 16 = 2 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 18)) = _ from
      sched18 inputs hin0 (hbSched 18 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 19, _, _ =>
    simp only [wWord, show (19 : Nat) - 2 = 17 from rfl, show (19 : Nat) - 7 = 12 from rfl,
      show (19 : Nat) - 15 = 4 from rfl, show (19 : Nat) - 16 = 3 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 19)) = _ from
      sched19 inputs hin0 (hbSched 19 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 20, _, _ =>
    simp only [wWord, show (20 : Nat) - 2 = 18 from rfl, show (20 : Nat) - 7 = 13 from rfl,
      show (20 : Nat) - 15 = 5 from rfl, show (20 : Nat) - 16 = 4 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 20)) = _ from
      sched20 inputs hin0 (hbSched 20 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 21, _, _ =>
    simp only [wWord, show (21 : Nat) - 2 = 19 from rfl, show (21 : Nat) - 7 = 14 from rfl,
      show (21 : Nat) - 15 = 6 from rfl, show (21 : Nat) - 16 = 5 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 21)) = _ from
      sched21 inputs hin0 (hbSched 21 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 22, _, _ =>
    simp only [wWord, show (22 : Nat) - 2 = 20 from rfl, show (22 : Nat) - 7 = 15 from rfl,
      show (22 : Nat) - 15 = 7 from rfl, show (22 : Nat) - 16 = 6 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 22)) = _ from
      sched22 inputs hin0 (hbSched 22 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 23, _, _ =>
    simp only [wWord, show (23 : Nat) - 2 = 21 from rfl, show (23 : Nat) - 7 = 16 from rfl,
      show (23 : Nat) - 15 = 8 from rfl, show (23 : Nat) - 16 = 7 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 23)) = _ from
      sched23 inputs hin0 (hbSched 23 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 24, _, _ =>
    simp only [wWord, show (24 : Nat) - 2 = 22 from rfl, show (24 : Nat) - 7 = 17 from rfl,
      show (24 : Nat) - 15 = 9 from rfl, show (24 : Nat) - 16 = 8 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 24)) = _ from
      sched24 inputs hin0 (hbSched 24 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 25, _, _ =>
    simp only [wWord, show (25 : Nat) - 2 = 23 from rfl, show (25 : Nat) - 7 = 18 from rfl,
      show (25 : Nat) - 15 = 10 from rfl, show (25 : Nat) - 16 = 9 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 25)) = _ from
      sched25 inputs hin0 (hbSched 25 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 26, _, _ =>
    simp only [wWord, show (26 : Nat) - 2 = 24 from rfl, show (26 : Nat) - 7 = 19 from rfl,
      show (26 : Nat) - 15 = 11 from rfl, show (26 : Nat) - 16 = 10 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 26)) = _ from
      sched26 inputs hin0 (hbSched 26 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 27, _, _ =>
    simp only [wWord, show (27 : Nat) - 2 = 25 from rfl, show (27 : Nat) - 7 = 20 from rfl,
      show (27 : Nat) - 15 = 12 from rfl, show (27 : Nat) - 16 = 11 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 27)) = _ from
      sched27 inputs hin0 (hbSched 27 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 28, _, _ =>
    simp only [wWord, show (28 : Nat) - 2 = 26 from rfl, show (28 : Nat) - 7 = 21 from rfl,
      show (28 : Nat) - 15 = 13 from rfl, show (28 : Nat) - 16 = 12 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 28)) = _ from
      sched28 inputs hin0 (hbSched 28 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 29, _, _ =>
    simp only [wWord, show (29 : Nat) - 2 = 27 from rfl, show (29 : Nat) - 7 = 22 from rfl,
      show (29 : Nat) - 15 = 14 from rfl, show (29 : Nat) - 16 = 13 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 29)) = _ from
      sched29 inputs hin0 (hbSched 29 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 30, _, _ =>
    simp only [wWord, show (30 : Nat) - 2 = 28 from rfl, show (30 : Nat) - 7 = 23 from rfl,
      show (30 : Nat) - 15 = 15 from rfl, show (30 : Nat) - 16 = 14 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 30)) = _ from
      sched30 inputs hin0 (hbSched 30 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 31, _, _ =>
    simp only [wWord, show (31 : Nat) - 2 = 29 from rfl, show (31 : Nat) - 7 = 24 from rfl,
      show (31 : Nat) - 15 = 16 from rfl, show (31 : Nat) - 16 = 15 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 31)) = _ from
      sched31 inputs hin0 (hbSched 31 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 32, _, _ =>
    simp only [wWord, show (32 : Nat) - 2 = 30 from rfl, show (32 : Nat) - 7 = 25 from rfl,
      show (32 : Nat) - 15 = 17 from rfl, show (32 : Nat) - 16 = 16 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 32)) = _ from
      sched32 inputs hin0 (hbSched 32 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 33, _, _ =>
    simp only [wWord, show (33 : Nat) - 2 = 31 from rfl, show (33 : Nat) - 7 = 26 from rfl,
      show (33 : Nat) - 15 = 18 from rfl, show (33 : Nat) - 16 = 17 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 33)) = _ from
      sched33 inputs hin0 (hbSched 33 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 34, _, _ =>
    simp only [wWord, show (34 : Nat) - 2 = 32 from rfl, show (34 : Nat) - 7 = 27 from rfl,
      show (34 : Nat) - 15 = 19 from rfl, show (34 : Nat) - 16 = 18 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 34)) = _ from
      sched34 inputs hin0 (hbSched 34 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 35, _, _ =>
    simp only [wWord, show (35 : Nat) - 2 = 33 from rfl, show (35 : Nat) - 7 = 28 from rfl,
      show (35 : Nat) - 15 = 20 from rfl, show (35 : Nat) - 16 = 19 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 35)) = _ from
      sched35 inputs hin0 (hbSched 35 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 36, _, _ =>
    simp only [wWord, show (36 : Nat) - 2 = 34 from rfl, show (36 : Nat) - 7 = 29 from rfl,
      show (36 : Nat) - 15 = 21 from rfl, show (36 : Nat) - 16 = 20 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 36)) = _ from
      sched36 inputs hin0 (hbSched 36 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 37, _, _ =>
    simp only [wWord, show (37 : Nat) - 2 = 35 from rfl, show (37 : Nat) - 7 = 30 from rfl,
      show (37 : Nat) - 15 = 22 from rfl, show (37 : Nat) - 16 = 21 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 37)) = _ from
      sched37 inputs hin0 (hbSched 37 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 38, _, _ =>
    simp only [wWord, show (38 : Nat) - 2 = 36 from rfl, show (38 : Nat) - 7 = 31 from rfl,
      show (38 : Nat) - 15 = 23 from rfl, show (38 : Nat) - 16 = 22 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 38)) = _ from
      sched38 inputs hin0 (hbSched 38 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 39, _, _ =>
    simp only [wWord, show (39 : Nat) - 2 = 37 from rfl, show (39 : Nat) - 7 = 32 from rfl,
      show (39 : Nat) - 15 = 24 from rfl, show (39 : Nat) - 16 = 23 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 39)) = _ from
      sched39 inputs hin0 (hbSched 39 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 40, _, _ =>
    simp only [wWord, show (40 : Nat) - 2 = 38 from rfl, show (40 : Nat) - 7 = 33 from rfl,
      show (40 : Nat) - 15 = 25 from rfl, show (40 : Nat) - 16 = 24 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 40)) = _ from
      sched40 inputs hin0 (hbSched 40 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 41, _, _ =>
    simp only [wWord, show (41 : Nat) - 2 = 39 from rfl, show (41 : Nat) - 7 = 34 from rfl,
      show (41 : Nat) - 15 = 26 from rfl, show (41 : Nat) - 16 = 25 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 41)) = _ from
      sched41 inputs hin0 (hbSched 41 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 42, _, _ =>
    simp only [wWord, show (42 : Nat) - 2 = 40 from rfl, show (42 : Nat) - 7 = 35 from rfl,
      show (42 : Nat) - 15 = 27 from rfl, show (42 : Nat) - 16 = 26 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 42)) = _ from
      sched42 inputs hin0 (hbSched 42 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 43, _, _ =>
    simp only [wWord, show (43 : Nat) - 2 = 41 from rfl, show (43 : Nat) - 7 = 36 from rfl,
      show (43 : Nat) - 15 = 28 from rfl, show (43 : Nat) - 16 = 27 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 43)) = _ from
      sched43 inputs hin0 (hbSched 43 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 44, _, _ =>
    simp only [wWord, show (44 : Nat) - 2 = 42 from rfl, show (44 : Nat) - 7 = 37 from rfl,
      show (44 : Nat) - 15 = 29 from rfl, show (44 : Nat) - 16 = 28 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 44)) = _ from
      sched44 inputs hin0 (hbSched 44 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 45, _, _ =>
    simp only [wWord, show (45 : Nat) - 2 = 43 from rfl, show (45 : Nat) - 7 = 38 from rfl,
      show (45 : Nat) - 15 = 30 from rfl, show (45 : Nat) - 16 = 29 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 45)) = _ from
      sched45 inputs hin0 (hbSched 45 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 46, _, _ =>
    simp only [wWord, show (46 : Nat) - 2 = 44 from rfl, show (46 : Nat) - 7 = 39 from rfl,
      show (46 : Nat) - 15 = 31 from rfl, show (46 : Nat) - 16 = 30 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 46)) = _ from
      sched46 inputs hin0 (hbSched 46 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 47, _, _ =>
    simp only [wWord, show (47 : Nat) - 2 = 45 from rfl, show (47 : Nat) - 7 = 40 from rfl,
      show (47 : Nat) - 15 = 32 from rfl, show (47 : Nat) - 16 = 31 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 47)) = _ from
      sched47 inputs hin0 (hbSched 47 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 48, _, _ =>
    simp only [wWord, show (48 : Nat) - 2 = 46 from rfl, show (48 : Nat) - 7 = 41 from rfl,
      show (48 : Nat) - 15 = 33 from rfl, show (48 : Nat) - 16 = 32 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 48)) = _ from
      sched48 inputs hin0 (hbSched 48 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 49, _, _ =>
    simp only [wWord, show (49 : Nat) - 2 = 47 from rfl, show (49 : Nat) - 7 = 42 from rfl,
      show (49 : Nat) - 15 = 34 from rfl, show (49 : Nat) - 16 = 33 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 49)) = _ from
      sched49 inputs hin0 (hbSched 49 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 50, _, _ =>
    simp only [wWord, show (50 : Nat) - 2 = 48 from rfl, show (50 : Nat) - 7 = 43 from rfl,
      show (50 : Nat) - 15 = 35 from rfl, show (50 : Nat) - 16 = 34 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 50)) = _ from
      sched50 inputs hin0 (hbSched 50 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 51, _, _ =>
    simp only [wWord, show (51 : Nat) - 2 = 49 from rfl, show (51 : Nat) - 7 = 44 from rfl,
      show (51 : Nat) - 15 = 36 from rfl, show (51 : Nat) - 16 = 35 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 51)) = _ from
      sched51 inputs hin0 (hbSched 51 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 52, _, _ =>
    simp only [wWord, show (52 : Nat) - 2 = 50 from rfl, show (52 : Nat) - 7 = 45 from rfl,
      show (52 : Nat) - 15 = 37 from rfl, show (52 : Nat) - 16 = 36 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 52)) = _ from
      sched52 inputs hin0 (hbSched 52 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 53, _, _ =>
    simp only [wWord, show (53 : Nat) - 2 = 51 from rfl, show (53 : Nat) - 7 = 46 from rfl,
      show (53 : Nat) - 15 = 38 from rfl, show (53 : Nat) - 16 = 37 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 53)) = _ from
      sched53 inputs hin0 (hbSched 53 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 54, _, _ =>
    simp only [wWord, show (54 : Nat) - 2 = 52 from rfl, show (54 : Nat) - 7 = 47 from rfl,
      show (54 : Nat) - 15 = 39 from rfl, show (54 : Nat) - 16 = 38 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 54)) = _ from
      sched54 inputs hin0 (hbSched 54 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 55, _, _ =>
    simp only [wWord, show (55 : Nat) - 2 = 53 from rfl, show (55 : Nat) - 7 = 48 from rfl,
      show (55 : Nat) - 15 = 40 from rfl, show (55 : Nat) - 16 = 39 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 55)) = _ from
      sched55 inputs hin0 (hbSched 55 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 56, _, _ =>
    simp only [wWord, show (56 : Nat) - 2 = 54 from rfl, show (56 : Nat) - 7 = 49 from rfl,
      show (56 : Nat) - 15 = 41 from rfl, show (56 : Nat) - 16 = 40 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 56)) = _ from
      sched56 inputs hin0 (hbSched 56 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 57, _, _ =>
    simp only [wWord, show (57 : Nat) - 2 = 55 from rfl, show (57 : Nat) - 7 = 50 from rfl,
      show (57 : Nat) - 15 = 42 from rfl, show (57 : Nat) - 16 = 41 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 57)) = _ from
      sched57 inputs hin0 (hbSched 57 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 58, _, _ =>
    simp only [wWord, show (58 : Nat) - 2 = 56 from rfl, show (58 : Nat) - 7 = 51 from rfl,
      show (58 : Nat) - 15 = 43 from rfl, show (58 : Nat) - 16 = 42 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 58)) = _ from
      sched58 inputs hin0 (hbSched 58 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 59, _, _ =>
    simp only [wWord, show (59 : Nat) - 2 = 57 from rfl, show (59 : Nat) - 7 = 52 from rfl,
      show (59 : Nat) - 15 = 44 from rfl, show (59 : Nat) - 16 = 43 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 59)) = _ from
      sched59 inputs hin0 (hbSched 59 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 60, _, _ =>
    simp only [wWord, show (60 : Nat) - 2 = 58 from rfl, show (60 : Nat) - 7 = 53 from rfl,
      show (60 : Nat) - 15 = 45 from rfl, show (60 : Nat) - 16 = 44 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 60)) = _ from
      sched60 inputs hin0 (hbSched 60 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 61, _, _ =>
    simp only [wWord, show (61 : Nat) - 2 = 59 from rfl, show (61 : Nat) - 7 = 54 from rfl,
      show (61 : Nat) - 15 = 46 from rfl, show (61 : Nat) - 16 = 45 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 61)) = _ from
      sched61 inputs hin0 (hbSched 61 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 62, _, _ =>
    simp only [wWord, show (62 : Nat) - 2 = 60 from rfl, show (62 : Nat) - 7 = 55 from rfl,
      show (62 : Nat) - 15 = 47 from rfl, show (62 : Nat) - 16 = 46 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 62)) = _ from
      sched62 inputs hin0 (hbSched 62 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | 63, _, _ =>
    simp only [wWord, show (63 : Nat) - 2 = 61 from rfl, show (63 : Nat) - 7 = 56 from rfl,
      show (63 : Nat) - 15 = 48 from rfl, show (63 : Nat) - 16 = 47 from rfl]
    rw [show SHA256.ofBits (bitsOf inputs (wordBits 63)) = _ from
      sched63 inputs hin0 (hbSched 63 (by norm_num) (by norm_num)) hrSched]
    exact congrArg SHA256.w32 (by omega)
  | (n + 64), _, hx => exact absurd hx (by omega)

/-- **`hrnd_a` for every `t`.** -/
theorem rndAAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbR7 : ∀ t, t < 64 → ∀ j, j < 288 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR7At t).getD j (0, 0)).1 = 0)
    (hrR7 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0) :
    ∀ t, t < 64 → stateWord inputs (t + 1) 0 = SHA256.w32 (stateWord inputs t 7
      + SHA256.Sigma1 (stateWord inputs t 4)
      + SHA256.Ch (stateWord inputs t 4) (stateWord inputs t 5) (stateWord inputs t 6)
      + SHA256.K.getD t 0 + wWord inputs t
      + (SHA256.Sigma0 (stateWord inputs t 0)
        + SHA256.Maj (stateWord inputs t 0) (stateWord inputs t 1) (stateWord inputs t 2))) := by
  intro t ht
  match t, ht with
  | 0, _ => exact rndR7_0 inputs hin0 (hbR7 0 (by norm_num)) hrR7
  | 1, _ => exact rndR7_1 inputs hin0 (hbR7 1 (by norm_num)) hrR7
  | 2, _ => exact rndR7_2 inputs hin0 (hbR7 2 (by norm_num)) hrR7
  | 3, _ => exact rndR7_3 inputs hin0 (hbR7 3 (by norm_num)) hrR7
  | 4, _ => exact rndR7_4 inputs hin0 (hbR7 4 (by norm_num)) hrR7
  | 5, _ => exact rndR7_5 inputs hin0 (hbR7 5 (by norm_num)) hrR7
  | 6, _ => exact rndR7_6 inputs hin0 (hbR7 6 (by norm_num)) hrR7
  | 7, _ => exact rndR7_7 inputs hin0 (hbR7 7 (by norm_num)) hrR7
  | 8, _ => exact rndR7_8 inputs hin0 (hbR7 8 (by norm_num)) hrR7
  | 9, _ => exact rndR7_9 inputs hin0 (hbR7 9 (by norm_num)) hrR7
  | 10, _ => exact rndR7_10 inputs hin0 (hbR7 10 (by norm_num)) hrR7
  | 11, _ => exact rndR7_11 inputs hin0 (hbR7 11 (by norm_num)) hrR7
  | 12, _ => exact rndR7_12 inputs hin0 (hbR7 12 (by norm_num)) hrR7
  | 13, _ => exact rndR7_13 inputs hin0 (hbR7 13 (by norm_num)) hrR7
  | 14, _ => exact rndR7_14 inputs hin0 (hbR7 14 (by norm_num)) hrR7
  | 15, _ => exact rndR7_15 inputs hin0 (hbR7 15 (by norm_num)) hrR7
  | 16, _ => exact rndR7_16 inputs hin0 (hbR7 16 (by norm_num)) hrR7
  | 17, _ => exact rndR7_17 inputs hin0 (hbR7 17 (by norm_num)) hrR7
  | 18, _ => exact rndR7_18 inputs hin0 (hbR7 18 (by norm_num)) hrR7
  | 19, _ => exact rndR7_19 inputs hin0 (hbR7 19 (by norm_num)) hrR7
  | 20, _ => exact rndR7_20 inputs hin0 (hbR7 20 (by norm_num)) hrR7
  | 21, _ => exact rndR7_21 inputs hin0 (hbR7 21 (by norm_num)) hrR7
  | 22, _ => exact rndR7_22 inputs hin0 (hbR7 22 (by norm_num)) hrR7
  | 23, _ => exact rndR7_23 inputs hin0 (hbR7 23 (by norm_num)) hrR7
  | 24, _ => exact rndR7_24 inputs hin0 (hbR7 24 (by norm_num)) hrR7
  | 25, _ => exact rndR7_25 inputs hin0 (hbR7 25 (by norm_num)) hrR7
  | 26, _ => exact rndR7_26 inputs hin0 (hbR7 26 (by norm_num)) hrR7
  | 27, _ => exact rndR7_27 inputs hin0 (hbR7 27 (by norm_num)) hrR7
  | 28, _ => exact rndR7_28 inputs hin0 (hbR7 28 (by norm_num)) hrR7
  | 29, _ => exact rndR7_29 inputs hin0 (hbR7 29 (by norm_num)) hrR7
  | 30, _ => exact rndR7_30 inputs hin0 (hbR7 30 (by norm_num)) hrR7
  | 31, _ => exact rndR7_31 inputs hin0 (hbR7 31 (by norm_num)) hrR7
  | 32, _ => exact rndR7_32 inputs hin0 (hbR7 32 (by norm_num)) hrR7
  | 33, _ => exact rndR7_33 inputs hin0 (hbR7 33 (by norm_num)) hrR7
  | 34, _ => exact rndR7_34 inputs hin0 (hbR7 34 (by norm_num)) hrR7
  | 35, _ => exact rndR7_35 inputs hin0 (hbR7 35 (by norm_num)) hrR7
  | 36, _ => exact rndR7_36 inputs hin0 (hbR7 36 (by norm_num)) hrR7
  | 37, _ => exact rndR7_37 inputs hin0 (hbR7 37 (by norm_num)) hrR7
  | 38, _ => exact rndR7_38 inputs hin0 (hbR7 38 (by norm_num)) hrR7
  | 39, _ => exact rndR7_39 inputs hin0 (hbR7 39 (by norm_num)) hrR7
  | 40, _ => exact rndR7_40 inputs hin0 (hbR7 40 (by norm_num)) hrR7
  | 41, _ => exact rndR7_41 inputs hin0 (hbR7 41 (by norm_num)) hrR7
  | 42, _ => exact rndR7_42 inputs hin0 (hbR7 42 (by norm_num)) hrR7
  | 43, _ => exact rndR7_43 inputs hin0 (hbR7 43 (by norm_num)) hrR7
  | 44, _ => exact rndR7_44 inputs hin0 (hbR7 44 (by norm_num)) hrR7
  | 45, _ => exact rndR7_45 inputs hin0 (hbR7 45 (by norm_num)) hrR7
  | 46, _ => exact rndR7_46 inputs hin0 (hbR7 46 (by norm_num)) hrR7
  | 47, _ => exact rndR7_47 inputs hin0 (hbR7 47 (by norm_num)) hrR7
  | 48, _ => exact rndR7_48 inputs hin0 (hbR7 48 (by norm_num)) hrR7
  | 49, _ => exact rndR7_49 inputs hin0 (hbR7 49 (by norm_num)) hrR7
  | 50, _ => exact rndR7_50 inputs hin0 (hbR7 50 (by norm_num)) hrR7
  | 51, _ => exact rndR7_51 inputs hin0 (hbR7 51 (by norm_num)) hrR7
  | 52, _ => exact rndR7_52 inputs hin0 (hbR7 52 (by norm_num)) hrR7
  | 53, _ => exact rndR7_53 inputs hin0 (hbR7 53 (by norm_num)) hrR7
  | 54, _ => exact rndR7_54 inputs hin0 (hbR7 54 (by norm_num)) hrR7
  | 55, _ => exact rndR7_55 inputs hin0 (hbR7 55 (by norm_num)) hrR7
  | 56, _ => exact rndR7_56 inputs hin0 (hbR7 56 (by norm_num)) hrR7
  | 57, _ => exact rndR7_57 inputs hin0 (hbR7 57 (by norm_num)) hrR7
  | 58, _ => exact rndR7_58 inputs hin0 (hbR7 58 (by norm_num)) hrR7
  | 59, _ => exact rndR7_59 inputs hin0 (hbR7 59 (by norm_num)) hrR7
  | 60, _ => exact rndR7_60 inputs hin0 (hbR7 60 (by norm_num)) hrR7
  | 61, _ => exact rndR7_61 inputs hin0 (hbR7 61 (by norm_num)) hrR7
  | 62, _ => exact rndR7_62 inputs hin0 (hbR7 62 (by norm_num)) hrR7
  | 63, _ => exact rndR7_63 inputs hin0 (hbR7 63 (by norm_num)) hrR7
  | (n + 64), hx => exact absurd hx (by omega)

/-- **`hrnd_e` for every `t`.** -/
theorem rndEAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbR6 : ∀ t, t < 64 → ∀ j, j < 224 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR6At t).getD j (0, 0)).1 = 0)
    (hrR6 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0) :
    ∀ t, t < 64 → stateWord inputs (t + 1) 4 = SHA256.w32 (stateWord inputs t 3
      + (stateWord inputs t 7 + SHA256.Sigma1 (stateWord inputs t 4)
        + SHA256.Ch (stateWord inputs t 4) (stateWord inputs t 5) (stateWord inputs t 6)
        + SHA256.K.getD t 0 + wWord inputs t)) := by
  intro t ht
  match t, ht with
  | 0, _ => exact rndR6_0 inputs hin0 (hbR6 0 (by norm_num)) hrR6
  | 1, _ => exact rndR6_1 inputs hin0 (hbR6 1 (by norm_num)) hrR6
  | 2, _ => exact rndR6_2 inputs hin0 (hbR6 2 (by norm_num)) hrR6
  | 3, _ => exact rndR6_3 inputs hin0 (hbR6 3 (by norm_num)) hrR6
  | 4, _ => exact rndR6_4 inputs hin0 (hbR6 4 (by norm_num)) hrR6
  | 5, _ => exact rndR6_5 inputs hin0 (hbR6 5 (by norm_num)) hrR6
  | 6, _ => exact rndR6_6 inputs hin0 (hbR6 6 (by norm_num)) hrR6
  | 7, _ => exact rndR6_7 inputs hin0 (hbR6 7 (by norm_num)) hrR6
  | 8, _ => exact rndR6_8 inputs hin0 (hbR6 8 (by norm_num)) hrR6
  | 9, _ => exact rndR6_9 inputs hin0 (hbR6 9 (by norm_num)) hrR6
  | 10, _ => exact rndR6_10 inputs hin0 (hbR6 10 (by norm_num)) hrR6
  | 11, _ => exact rndR6_11 inputs hin0 (hbR6 11 (by norm_num)) hrR6
  | 12, _ => exact rndR6_12 inputs hin0 (hbR6 12 (by norm_num)) hrR6
  | 13, _ => exact rndR6_13 inputs hin0 (hbR6 13 (by norm_num)) hrR6
  | 14, _ => exact rndR6_14 inputs hin0 (hbR6 14 (by norm_num)) hrR6
  | 15, _ => exact rndR6_15 inputs hin0 (hbR6 15 (by norm_num)) hrR6
  | 16, _ => exact rndR6_16 inputs hin0 (hbR6 16 (by norm_num)) hrR6
  | 17, _ => exact rndR6_17 inputs hin0 (hbR6 17 (by norm_num)) hrR6
  | 18, _ => exact rndR6_18 inputs hin0 (hbR6 18 (by norm_num)) hrR6
  | 19, _ => exact rndR6_19 inputs hin0 (hbR6 19 (by norm_num)) hrR6
  | 20, _ => exact rndR6_20 inputs hin0 (hbR6 20 (by norm_num)) hrR6
  | 21, _ => exact rndR6_21 inputs hin0 (hbR6 21 (by norm_num)) hrR6
  | 22, _ => exact rndR6_22 inputs hin0 (hbR6 22 (by norm_num)) hrR6
  | 23, _ => exact rndR6_23 inputs hin0 (hbR6 23 (by norm_num)) hrR6
  | 24, _ => exact rndR6_24 inputs hin0 (hbR6 24 (by norm_num)) hrR6
  | 25, _ => exact rndR6_25 inputs hin0 (hbR6 25 (by norm_num)) hrR6
  | 26, _ => exact rndR6_26 inputs hin0 (hbR6 26 (by norm_num)) hrR6
  | 27, _ => exact rndR6_27 inputs hin0 (hbR6 27 (by norm_num)) hrR6
  | 28, _ => exact rndR6_28 inputs hin0 (hbR6 28 (by norm_num)) hrR6
  | 29, _ => exact rndR6_29 inputs hin0 (hbR6 29 (by norm_num)) hrR6
  | 30, _ => exact rndR6_30 inputs hin0 (hbR6 30 (by norm_num)) hrR6
  | 31, _ => exact rndR6_31 inputs hin0 (hbR6 31 (by norm_num)) hrR6
  | 32, _ => exact rndR6_32 inputs hin0 (hbR6 32 (by norm_num)) hrR6
  | 33, _ => exact rndR6_33 inputs hin0 (hbR6 33 (by norm_num)) hrR6
  | 34, _ => exact rndR6_34 inputs hin0 (hbR6 34 (by norm_num)) hrR6
  | 35, _ => exact rndR6_35 inputs hin0 (hbR6 35 (by norm_num)) hrR6
  | 36, _ => exact rndR6_36 inputs hin0 (hbR6 36 (by norm_num)) hrR6
  | 37, _ => exact rndR6_37 inputs hin0 (hbR6 37 (by norm_num)) hrR6
  | 38, _ => exact rndR6_38 inputs hin0 (hbR6 38 (by norm_num)) hrR6
  | 39, _ => exact rndR6_39 inputs hin0 (hbR6 39 (by norm_num)) hrR6
  | 40, _ => exact rndR6_40 inputs hin0 (hbR6 40 (by norm_num)) hrR6
  | 41, _ => exact rndR6_41 inputs hin0 (hbR6 41 (by norm_num)) hrR6
  | 42, _ => exact rndR6_42 inputs hin0 (hbR6 42 (by norm_num)) hrR6
  | 43, _ => exact rndR6_43 inputs hin0 (hbR6 43 (by norm_num)) hrR6
  | 44, _ => exact rndR6_44 inputs hin0 (hbR6 44 (by norm_num)) hrR6
  | 45, _ => exact rndR6_45 inputs hin0 (hbR6 45 (by norm_num)) hrR6
  | 46, _ => exact rndR6_46 inputs hin0 (hbR6 46 (by norm_num)) hrR6
  | 47, _ => exact rndR6_47 inputs hin0 (hbR6 47 (by norm_num)) hrR6
  | 48, _ => exact rndR6_48 inputs hin0 (hbR6 48 (by norm_num)) hrR6
  | 49, _ => exact rndR6_49 inputs hin0 (hbR6 49 (by norm_num)) hrR6
  | 50, _ => exact rndR6_50 inputs hin0 (hbR6 50 (by norm_num)) hrR6
  | 51, _ => exact rndR6_51 inputs hin0 (hbR6 51 (by norm_num)) hrR6
  | 52, _ => exact rndR6_52 inputs hin0 (hbR6 52 (by norm_num)) hrR6
  | 53, _ => exact rndR6_53 inputs hin0 (hbR6 53 (by norm_num)) hrR6
  | 54, _ => exact rndR6_54 inputs hin0 (hbR6 54 (by norm_num)) hrR6
  | 55, _ => exact rndR6_55 inputs hin0 (hbR6 55 (by norm_num)) hrR6
  | 56, _ => exact rndR6_56 inputs hin0 (hbR6 56 (by norm_num)) hrR6
  | 57, _ => exact rndR6_57 inputs hin0 (hbR6 57 (by norm_num)) hrR6
  | 58, _ => exact rndR6_58 inputs hin0 (hbR6 58 (by norm_num)) hrR6
  | 59, _ => exact rndR6_59 inputs hin0 (hbR6 59 (by norm_num)) hrR6
  | 60, _ => exact rndR6_60 inputs hin0 (hbR6 60 (by norm_num)) hrR6
  | 61, _ => exact rndR6_61 inputs hin0 (hbR6 61 (by norm_num)) hrR6
  | 62, _ => exact rndR6_62 inputs hin0 (hbR6 62 (by norm_num)) hrR6
  | 63, _ => exact rndR6_63 inputs hin0 (hbR6 63 (by norm_num)) hrR6
  | (n + 64), hx => exact absurd hx (by omega)



/-- **The deployed circuit computes `SHA256.blockFrom`.** -/
theorem sha256_block_of_circuit [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbSched : ∀ t, 16 ≤ t → t < 64 → ∀ j, j < 160 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpSchedAt t).getD j (0, 0)).1 = 0)
    (hrSched : ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0)
    (hbR6 : ∀ t, t < 64 → ∀ j, j < 224 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR6At t).getD j (0, 0)).1 = 0)
    (hrR6 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0)
    (hbR7 : ∀ t, t < 64 → ∀ j, j < 288 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR7At t).getD j (0, 0)).1 = 0)
    (hrR7 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0)
    (hbFin : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpAt i).getD j (0, 0)).1 = 0)
    (hblFin : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpLAt i).getD j (0, 0)).1 = 0)
    (hrFin : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    (List.range 8).map (outWord inputs)
      = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs) :=
  SHA256.sha256_soundness (msgBlock inputs) (msgBlock_length inputs)
    (hWord inputs) (wWord inputs) (stateWord inputs) (outWord inputs)
    (fun t ht => hcopy inputs t ht)
    (schedAll inputs hin0 hbSched hrSched)
    (fun i _ => hinit inputs i)
    (rndAAll inputs hin0 hbR7 hrR7)
    (rndEAll inputs hin0 hbR6 hrR6)
    (fun t _ => hshift inputs t)
    (hout inputs hin0 hbFin hblFin hrFin)

end Sha256Blk
