/-
# `bytes → SHA-256`

The four wrap-root families (184 references) and the composition: `S2Sound.assertions_zero_of_bytes`
gives every asserted node from the committed LFC3 bytes, `S2Assert` and this file cash that in for
the nine hypotheses of `sha256_block_of_circuit`.
-/

import quadcert.Bridge.Sha256.S2Assert

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- Flat assert index of the `rootOfS` roots. -/
def kRootS (e : Nat) : Nat :=
  if e < 24 then if e < 12 then if e < 6 then if e < 3 then if e < 1 then 0 else if e < 2 then 1 else 2 else if e < 4 then 3 else if e < 5 then 4 else 5 else if e < 9 then if e < 7 then 6 else if e < 8 then 7 else 8 else if e < 10 then 9 else if e < 11 then 10 else 11 else if e < 18 then if e < 15 then if e < 13 then 12 else if e < 14 then 13 else 14 else if e < 16 then 15 else if e < 17 then 16 else 17 else if e < 21 then if e < 19 then 18 else if e < 20 then 19 else 20 else if e < 22 then 21 else if e < 23 then 22 else 23 else if e < 36 then if e < 30 then if e < 27 then if e < 25 then 24 else if e < 26 then 25 else 26 else if e < 28 then 27 else if e < 29 then 28 else 29 else if e < 33 then if e < 31 then 30 else if e < 32 then 31 else 32 else if e < 34 then 33 else if e < 35 then 34 else 35 else if e < 42 then if e < 39 then if e < 37 then 36 else if e < 38 then 37 else 38 else if e < 40 then 39 else if e < 41 then 40 else 41 else if e < 45 then if e < 43 then 42 else if e < 44 then 43 else 44 else if e < 46 then 45 else if e < 47 then 46 else 47

theorem okRootS : (List.range 48).all
    (fun e => decide (kRootS e < 6840 ∧ assertNode (kRootS e) = rootOfS e)) = true := by
  decide +kernel

/-- Flat assert index of the `rootOf6` roots. -/
def kRootR6 (e : Nat) : Nat :=
  if e < 32 then if e < 16 then if e < 8 then if e < 4 then if e < 2 then if e < 1 then 48 else 49 else if e < 3 then 50 else 51 else if e < 6 then if e < 5 then 52 else 54 else if e < 7 then 56 else 58 else if e < 12 then if e < 10 then if e < 9 then 60 else 62 else if e < 11 then 64 else 66 else if e < 14 then if e < 13 then 68 else 70 else if e < 15 then 72 else 74 else if e < 24 then if e < 20 then if e < 18 then if e < 17 then 76 else 78 else if e < 19 then 80 else 82 else if e < 22 then if e < 21 then 84 else 86 else if e < 23 then 88 else 90 else if e < 28 then if e < 26 then if e < 25 then 92 else 94 else if e < 27 then 96 else 98 else if e < 30 then if e < 29 then 100 else 102 else if e < 31 then 104 else 106 else if e < 48 then if e < 40 then if e < 36 then if e < 34 then if e < 33 then 108 else 110 else if e < 35 then 112 else 114 else if e < 38 then if e < 37 then 116 else 118 else if e < 39 then 120 else 122 else if e < 44 then if e < 42 then if e < 41 then 124 else 126 else if e < 43 then 128 else 130 else if e < 46 then if e < 45 then 132 else 134 else if e < 47 then 136 else 138 else if e < 56 then if e < 52 then if e < 50 then if e < 49 then 140 else 142 else if e < 51 then 144 else 146 else if e < 54 then if e < 53 then 148 else 150 else if e < 55 then 152 else 154 else if e < 60 then if e < 58 then if e < 57 then 156 else 158 else if e < 59 then 160 else 162 else if e < 62 then if e < 61 then 164 else 166 else if e < 63 then 168 else 170

theorem okRootR6 : (List.range 64).all
    (fun e => decide (kRootR6 e < 6840 ∧ assertNode (kRootR6 e) = rootOf6 e)) = true := by
  decide +kernel

/-- Flat assert index of the `rootOf7` roots. -/
def kRootR7 (e : Nat) : Nat :=
  if e < 32 then if e < 16 then if e < 8 then if e < 4 then if e < 2 then if e < 1 then 53 else 55 else if e < 3 then 57 else 59 else if e < 6 then if e < 5 then 61 else 63 else if e < 7 then 65 else 67 else if e < 12 then if e < 10 then if e < 9 then 69 else 71 else if e < 11 then 73 else 75 else if e < 14 then if e < 13 then 77 else 79 else if e < 15 then 81 else 83 else if e < 24 then if e < 20 then if e < 18 then if e < 17 then 85 else 87 else if e < 19 then 89 else 91 else if e < 22 then if e < 21 then 93 else 95 else if e < 23 then 97 else 99 else if e < 28 then if e < 26 then if e < 25 then 101 else 103 else if e < 27 then 105 else 107 else if e < 30 then if e < 29 then 109 else 111 else if e < 31 then 113 else 115 else if e < 48 then if e < 40 then if e < 36 then if e < 34 then if e < 33 then 117 else 119 else if e < 35 then 121 else 123 else if e < 38 then if e < 37 then 125 else 127 else if e < 39 then 129 else 131 else if e < 44 then if e < 42 then if e < 41 then 133 else 135 else if e < 43 then 137 else 139 else if e < 46 then if e < 45 then 141 else 143 else if e < 47 then 145 else 147 else if e < 56 then if e < 52 then if e < 50 then if e < 49 then 149 else 151 else if e < 51 then 153 else 155 else if e < 54 then if e < 53 then 157 else 159 else if e < 55 then 161 else 163 else if e < 60 then if e < 58 then if e < 57 then 165 else 167 else if e < 59 then 169 else 171 else if e < 62 then if e < 61 then 172 else 173 else if e < 63 then 174 else 175

theorem okRootR7 : (List.range 64).all
    (fun e => decide (kRootR7 e < 6840 ∧ assertNode (kRootR7 e) = rootOf7 e)) = true := by
  decide +kernel

/-- Flat assert index of the `rootOfW` roots. -/
def kRootW (e : Nat) : Nat :=
  if e < 4 then if e < 2 then if e < 1 then 176 else 177 else if e < 3 then 178 else 179 else if e < 6 then if e < 5 then 180 else 181 else if e < 7 then 182 else 183

theorem okRootW : (List.range 8).all
    (fun e => decide (kRootW e < 6840 ∧ assertNode (kRootW e) = rootOfW e)) = true := by
  decide +kernel

variable {F : Type} [Field F]

theorem hrS (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0 := by
  intro e he
  have hb := okRootS
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hk, heq⟩ := hb e he
  rw [← heq]
  exact zeroFlat inputs hacc (kRootS e) hk

theorem hrR6 (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0 := by
  intro e he
  have hb := okRootR6
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hk, heq⟩ := hb e he
  rw [← heq]
  exact zeroFlat inputs hacc (kRootR6 e) hk

theorem hrR7 (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0 := by
  intro e he
  have hb := okRootR7
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hk, heq⟩ := hb e he
  rw [← heq]
  exact zeroFlat inputs hacc (kRootR7 e) hk

theorem hrW (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0 := by
  intro e he
  have hb := okRootW
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hk, heq⟩ := hb e he
  rw [← heq]
  exact zeroFlat inputs hacc (kRootW e) hk

/-- **The deployed SHA-256 circuit, from the committed bytes.**

    Hypotheses: the artifact's LFC3 pages decode to `c`, and `inputs` satisfies the quad system.
    Conclusion: the eight outgoing chaining words are `SHA256.blockFrom` of the incoming ones and
    the message block, in `SHA/Spec.lean`'s vocabulary. -/
theorem sha256_block_of_bytes (c : Lfc3.DecodedCircuit)
    (hdec : Lfc3.decode Lfc3.p256 packedInput deltaTrees = .ok c)
    [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hacc : Accepts ((c.toRaw advice).toQuad (consts F)) inputs) :
    (List.range 8).map (outWord inputs)
      = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs) := by
  have hz := assertions_zero_of_bytes c hdec inputs hacc
  rw [raw_from_bytes c hdec] at hz
  have hz' : ∀ r ∈ raw.toRecs,
      interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0 := hz
  exact sha256_block_of_circuit inputs hin0
    (fun t h16 h64 j hj => hbSched inputs hz' t h16 h64 j hj)
    (hrS inputs hz')
    (fun t ht j hj => hbR6 inputs hz' t (by omega) ht j hj)
    (hrR6 inputs hz')
    (fun t ht j hj => hbR7 inputs hz' t (by omega) ht j hj)
    (hrR7 inputs hz')
    (fun i hi j hj => hbFin inputs hz' i (by omega) hi j hj)
    (fun i hi j hj => hbFinL inputs hz' i (by omega) hi j hj)
    (hrW inputs hz')

end Sha256Blk
