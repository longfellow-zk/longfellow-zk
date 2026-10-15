import Lfzk.Mac

/-!
# The two-field MAC with a separate private MAC witness per circuit

`Lfzk.Mac` proves the fixed-pair facts; this file is the algebra and counting that the end-to-end
composition with **separate** private MAC witnesses needs (`Lfzk.NizkZkDeployedHashSepMac`), and
the reparametrisation that the v7 zero-knowledge statement needs (`Lfzk.CompiledLongfellowZkV7Mac`).

## The two formulas

`rust/applications/mdoc_zk/runtime/src/mac.rs` gates on `version >= 8`:

```text
v8 (push_modern_macs):  tag j = av · msg j + ap j          -- `macTag av ap msg`
v7 (push_legacy_macs):  tag j = (av + ap j) · msg j        -- `shiftTag av ap msg`
```

over `GF(2^128)`, for the six 128-bit blocks `msg` of `(issuer_sig_e, device_pk.x, device_pk.y)`
(low half first, `bytes[..16]`, `bytes[16..]` of the little-endian 32-byte encoding).  The v7
formula is the C++ circuit's (`lib/circuits/mac/mac_circuit.h`, `assert_mac`: `key = av ⊕ ap`,
`mac == key · x`).  Each circuit reads the public tags and `av`, and has **its own** private `ap`
in its witness: equal for an honest prover, unrelated for a cheating one.

## Soundness: an affine MAC per side

Both formulas are, at a fixed side witness `a`, a map `x ↦ mac a x` from the multiplier to the
tags such that two witnesses with **different** messages collide at **at most one** multiplier
(`shiftTag_collision_card_le_one`, `Mac.macTag_collision_card_le_one`).  The composition uses
only that, so it is stated for any `mac₁`, `mac₂` with that property (`hcoll`).

The MAC slot's bad event at a key point is `SepMacBad`: some pair of fixed candidates with
different messages collides at the multiplier.  `sepMacBad_card_le`: over the raw key coin `c`,
decoded by a `kmac`-balanced decoder and shifted by a fixed public share, it has at most
`|L₁| · |L₂| · kmac` coins — `|L₁| · |L₂| / |Fmac|` of them.

## Zero knowledge: the v7 tag leaks the zero pattern

At a zero block, `(av + ap j) · 0 = 0` whatever `ap j` is (`shiftTag_zero_block`), so the v7
tags reveal which blocks are zero; at a nonzero block `ap j ↦ (av + ap j) · msg j` is a
bijection.  `shareEquiv msg` reparametrises the v7 shares as v8 blinds on the nonzero blocks and
leaves the zero blocks alone, and `maskTag_macTag_shareEquiv` is the identity

```text
maskTag (zeroPat msg) (macTag av (shareEquiv msg s) msg) = shiftTag av s msg
```

so the v7 tags are the v8 tags at uniform blinds with the zero blocks overwritten by `0`.  This
leakage is a property of the v7 formula, not of the proof system.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Classical

namespace Lfzk.MacSep

open Lfzk.Mac

variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/-! ## The v7 formula -/

/-- **The v7 MAC** (`push_legacy_macs`, `mac_circuit.h` `assert_mac`): the multiplier is shifted
by the prover's private share block by block, and there is no additive blind. -/
def shiftTag (a : Fmac) (s msg : Fin nblk → Fmac) : Fin nblk → Fmac :=
  fun j => (a + s j) * msg j

@[simp] lemma shiftTag_apply (a : Fmac) (s msg : Fin nblk → Fmac) (j : Fin nblk) :
    shiftTag a s msg j = (a + s j) * msg j := rfl

/-- `Mac.shiftedMultiplier_collision_card_le_one` at `shiftTag`: with separate fixed shares and
unequal fixed messages, at most one multiplier collides. -/
theorem shiftTag_collision_card_le_one [Fintype Fmac] [DecidableEq Fmac]
    (s s' msg msg' : Fin nblk → Fmac) (hne : msg ≠ msg') :
    (univ.filter fun a : Fmac => shiftTag a s msg = shiftTag a s' msg').card ≤ 1 :=
  shiftedMultiplier_collision_card_le_one s s' msg msg' hne

/-- **The v7 tag is zero at a zero block**, whatever the share and the multiplier. -/
theorem shiftTag_zero_block (a : Fmac) (s msg : Fin nblk → Fmac) {j : Fin nblk}
    (hj : msg j = 0) : shiftTag a s msg j = 0 := by
  simp [hj]

/-- So a nonzero tag block certifies a nonzero message block: the tags reveal (part of) the zero
pattern. -/
theorem msg_ne_zero_of_shiftTag_ne_zero {a : Fmac} {s msg : Fin nblk → Fmac} {j : Fin nblk}
    (h : shiftTag a s msg j ≠ 0) : msg j ≠ 0 :=
  fun hj => h (shiftTag_zero_block a s msg hj)

/-! ## The MAC slot's bad event, counted -/

section Count

variable {W₁ W₂ : Type}

/--
**The MAC slot's bad event** at multiplier `x`: two candidates, one from each fixed list, with
different messages and colliding tags.
-/
def SepMacBad (L₁ : Finset W₁) (L₂ : Finset W₂) (common₁ : W₁ → Fin nblk → Fmac)
    (common₂ : W₂ → Fin nblk → Fmac) (mac₁ : W₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : W₂ → Fmac → Fin nblk → Fmac) (x : Fmac) : Prop :=
  ∃ a₁ ∈ L₁, ∃ a₂ ∈ L₂, common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ x = mac₂ a₂ x

variable [Fintype Fmac] [DecidableEq Fmac]

omit [Field Fmac] in
/-- One pair of fixed candidates: at most one bad multiplier. -/
theorem disagree_card_le_one (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (mac₁ : W₁ → Fmac → Fin nblk → Fmac) (mac₂ : W₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1) (a₁ : W₁) (a₂ : W₂) :
    (univ.filter fun x => common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ x = mac₂ a₂ x).card ≤ 1 := by
  by_cases h : common₁ a₁ = common₂ a₂
  · refine le_trans (card_le_card (t := (∅ : Finset Fmac)) ?_) (by simp)
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact absurd h hx.1
  · refine le_trans (card_le_card ?_) (hcoll a₁ a₂ h)
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.2

/-- A fixed set of at most one multiplier, shifted by a fixed public share and read through a
`kmac`-balanced decoder: at most `kmac` coins. -/
theorem shift_decode_card_le {C : Type} [Fintype C] (Bad : Fmac → Prop)
    (hone : (univ.filter fun x => Bad x).card ≤ 1) (shift : Fmac) (decode : C → Fmac) {kmac : ℕ}
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac) :
    (univ.filter fun c : C => Bad (shift + decode c)).card ≤ kmac := by
  set T := univ.filter fun x => Bad x
  have hsub : (univ.filter fun c : C => Bad (shift + decode c))
      ⊆ T.biUnion (fun x => univ.filter fun c : C => decode c = x - shift) := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, T] at hc ⊢
    exact ⟨shift + decode c, hc, by ring⟩
  calc (univ.filter fun c : C => Bad (shift + decode c)).card
      ≤ (T.biUnion (fun x => univ.filter fun c : C => decode c = x - shift)).card :=
        card_le_card hsub
    _ ≤ ∑ x ∈ T, (univ.filter fun c : C => decode c = x - shift).card := card_biUnion_le
    _ ≤ ∑ _x ∈ T, kmac := sum_le_sum fun x _ => hbal _
    _ = T.card * kmac := by rw [sum_const, smul_eq_mul]
    _ ≤ 1 * kmac := Nat.mul_le_mul_right _ hone
    _ = kmac := one_mul _

/--
**The MAC slot's count.**  With the two candidate lists and both sides' private MAC witnesses
fixed before the key coin `c`, the coins at which some pair with different messages collides are
at most `|L₁| · |L₂| · kmac` — a union bound over the pairs of `Mac`'s fixed-pair bound.
-/
theorem sepMacBad_card_le {C : Type} [Fintype C] (L₁ : Finset W₁) (L₂ : Finset W₂)
    (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (mac₁ : W₁ → Fmac → Fin nblk → Fmac) (mac₂ : W₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (shift : Fmac) (decode : C → Fmac) {kmac : ℕ}
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac) :
    (univ.filter fun c : C =>
        SepMacBad L₁ L₂ common₁ common₂ mac₁ mac₂ (shift + decode c)).card
      ≤ L₁.card * L₂.card * kmac := by
  have hone : ∀ a₁ a₂, (univ.filter fun c : C =>
      common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ (shift + decode c) = mac₂ a₂ (shift + decode c)).card
        ≤ kmac := by
    intro a₁ a₂
    have h := shift_decode_card_le (fun x => common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ x = mac₂ a₂ x)
      (by convert disagree_card_le_one common₁ common₂ mac₁ mac₂ hcoll a₁ a₂)
      shift decode hbal
    convert h
  have hsub : (univ.filter fun c : C =>
        SepMacBad L₁ L₂ common₁ common₂ mac₁ mac₂ (shift + decode c))
      ⊆ L₁.biUnion fun a₁ => L₂.biUnion fun a₂ => univ.filter fun c : C =>
          common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ (shift + decode c) = mac₂ a₂ (shift + decode c) := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, SepMacBad] at hc ⊢
    obtain ⟨a₁, h₁, a₂, h₂, h⟩ := hc
    exact ⟨a₁, h₁, a₂, h₂, h⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a₁ ∈ L₁, (L₂.biUnion fun a₂ => univ.filter fun c : C =>
          common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ (shift + decode c) = mac₂ a₂ (shift + decode c)).card :=
        card_biUnion_le
    _ ≤ ∑ a₁ ∈ L₁, ∑ a₂ ∈ L₂, (univ.filter fun c : C =>
          common₁ a₁ ≠ common₂ a₂ ∧ mac₁ a₁ (shift + decode c) = mac₂ a₂ (shift + decode c)).card :=
        sum_le_sum fun _ _ => card_biUnion_le
    _ ≤ ∑ _a₁ ∈ L₁, ∑ _a₂ ∈ L₂, kmac := sum_le_sum fun a₁ _ => sum_le_sum fun a₂ _ => hone a₁ a₂
    _ = L₁.card * L₂.card * kmac := by
        simp only [sum_const, smul_eq_mul]
        ring

/-- **The v7 formula satisfies `hcoll`**, at any share readers `share₁`, `share₂`. -/
theorem shiftTag_hcoll (common₁ : W₁ → Fin nblk → Fmac)
    (common₂ : W₂ → Fin nblk → Fmac) (share₁ : W₁ → Fin nblk → Fmac)
    (share₂ : W₂ → Fin nblk → Fmac) :
    ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => shiftTag x (share₁ a₁) (common₁ a₁)
        = shiftTag x (share₂ a₂) (common₂ a₂)).card ≤ 1 := fun a₁ a₂ hne => by
  refine le_trans (card_le_card ?_)
    (shiftTag_collision_card_le_one (share₁ a₁) (share₂ a₂) (common₁ a₁) (common₂ a₂) hne)
  intro x hx
  simpa using hx

/-- **The v8 formula satisfies `hcoll`**, at any blind readers `blind₁`, `blind₂`. -/
theorem macTag_hcoll (common₁ : W₁ → Fin nblk → Fmac)
    (common₂ : W₂ → Fin nblk → Fmac) (blind₁ : W₁ → Fin nblk → Fmac)
    (blind₂ : W₂ → Fin nblk → Fmac) :
    ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => macTag x (blind₁ a₁) (common₁ a₁)
        = macTag x (blind₂ a₂) (common₂ a₂)).card ≤ 1 := fun a₁ a₂ hne => by
  refine le_trans (card_le_card ?_)
    (macTag_collision_card_le_one (blind₁ a₁) (blind₂ a₂) (common₁ a₁) (common₂ a₂) hne)
  intro x hx
  simpa using hx

end Count

/-! ## The v7 shares as v8 blinds -/

section Reparam

variable [DecidableEq Fmac]

/-- **The zero pattern** of the message blocks: the leakage of the v7 tags. -/
def zeroPat (msg : Fin nblk → Fmac) : Fin nblk → Bool := fun j => decide (msg j = 0)

/-- Overwrite the blocks a pattern marks with `0`. -/
def maskTag (z : Fin nblk → Bool) (t : Fin nblk → Fmac) : Fin nblk → Fmac :=
  fun j => if z j then 0 else t j

/-- **The v7 shares as v8 blinds**: `s j ↦ s j · msg j` on the nonzero blocks (a bijection there),
the identity on the zero blocks. -/
def shareEquiv (msg : Fin nblk → Fmac) : (Fin nblk → Fmac) ≃ (Fin nblk → Fmac) where
  toFun s j := if msg j = 0 then s j else s j * msg j
  invFun b j := if msg j = 0 then b j else b j / msg j
  left_inv s := by
    funext j
    by_cases h : msg j = 0
    · simp [h]
    · simp [h]
  right_inv b := by
    funext j
    by_cases h : msg j = 0
    · simp [h]
    · simp [h]

/--
**The v7 tags are the masked v8 tags at the reparametrised shares.**  At a nonzero block,
`av · msg j + s j · msg j = (av + s j) · msg j`; at a zero block both sides are `0`.
-/
theorem maskTag_macTag_shareEquiv (av : Fmac) (s msg : Fin nblk → Fmac) :
    maskTag (zeroPat msg) (macTag av (shareEquiv msg s) msg) = shiftTag av s msg := by
  funext j
  by_cases h : msg j = 0
  · simp [maskTag, zeroPat, h]
  · simp only [maskTag, zeroPat, h, decide_false, Bool.false_eq_true, if_false, macTag_apply,
      shareEquiv, Equiv.coe_fn_mk, shiftTag_apply]
    ring

/-- With no zero block, the mask is the identity. -/
theorem maskTag_zeroPat_of_ne_zero {msg : Fin nblk → Fmac} (h : ∀ j, msg j ≠ 0) :
    maskTag (Fmac := Fmac) (zeroPat msg) = id := by
  funext t j
  simp [maskTag, zeroPat, h j]

end Reparam

end Lfzk.MacSep
