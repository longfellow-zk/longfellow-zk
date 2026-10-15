import Lfzk.CompiledLongfellowZkStat
import Lfzk.MacSep

/-!
# Zero knowledge of the two-field mdoc proof with the v7 MAC

`Lfzk.CompiledLongfellowZkTwoField.twofield_zk` (and its numerals `CompiledLongfellowZkV7`, and the
full-view statistical form `CompiledLongfellowZkStat.twofield_zk_stat`) models the tags as the
**v8** MAC, `macTag av ap msg = av · msg + ap`, with uniform blinds `ap`: the tags are a translate
of the blinds (`tagEquiv`), so they are uniform and the simulator samples them.  The registered
**v7** circuits and the deployed `version < 8` prover (`push_legacy_macs` in
`rust/applications/mdoc_zk/runtime/src/mac.rs`, `assert_mac` in `lib/circuits/mac/mac_circuit.h`)
use instead

```text
tag j = (av + ap j) · msg j            (MacSep.shiftTag av ap msg)
```

with uniform shares `ap j`.  At a block with `msg j ≠ 0` the tag is uniform; at a block with
`msg j = 0` it is **always `0`** (`MacSep.shiftTag_zero_block`).  So the v7 tags reveal the **zero
pattern** of the message blocks, `MacSep.zeroPat msg`, and nothing else.  This leakage is a
property of the v7 MAC formula, not of the proof system: the v8 formula has none
(`twofield_zk`), and `mac_circuit.h` says as much ("hiding whenever x is non-zero … a small error
to the zero-knowledge analysis").

## The statements

* `twofield_zk_v7` — **with leakage**: the real two-field experiment with the v7 tags
  (`realExp2V7`) is `(ε₁ + ε₂)`-close to `simExp2Leak … (zeroPat msg)`, a simulation that reads
  **no witness and no message**, only the zero pattern `z : Fin nblk → Bool`.  It samples a
  uniform tag `t` and publishes `maskTag z t` (the blocks `z` marks overwritten by `0`); the
  rest is `twofield_zk`'s simulator.  Same `ε`.
* `twofield_zk_v7_nonzero` — **without leakage, under a hypothesis**: if every message block is
  nonzero, the v7 tags are perfectly hiding and the real experiment is `(ε₁ + ε₂)`-close to
  `twofield_zk`'s own witness-free `simExp2`.  Same `ε`, same simulator.
* `v7mac_twofield_zk_q115`, `v7mac_twofield_zk_q115_nonzero` — the numerals: `≤ 2^-127` against
  `2^115` Merkle queries at the v7 geometries (`CompiledLongfellowZkV7.v7_twofield_zk_q115`);
* `twofield_wi_v7` — witness indistinguishability between two common values **with the same zero
  pattern** (in particular between any two with no zero block);
* `twofield_zk_stat_v7`, `twofield_zk_stat_v7_nonzero`, `v7mac_twofield_zk_stat542` — the same
  for the full-view statistical experiments of `CompiledLongfellowZkStat`.

## How: the v7 shares are v8 blinds on the nonzero blocks

`MacSep.shareEquiv msg` maps the v7 shares bijectively to v8 blinds (`s j ↦ s j · msg j` on the
nonzero blocks, the identity on the zero blocks), and `MacSep.maskTag_macTag_shareEquiv`:

```text
maskTag (zeroPat msg) (macTag av (shareEquiv msg s) msg) = shiftTag av s msg
```

So the v7 experiment **is** the v8 experiment of `twofield_zk` at uniform blinds, with the
witnesses read through `(shareEquiv msg).symm`, and with the circuits' public inputs
(`maskCtx₁`, `maskCtx₂`) and the distinguisher (`maskDist`) seeing the tags through
`maskTag (zeroPat msg)` (`realExp2V7_eq`).  `twofield_zk` at those parameters, reindexed along
`shareEquiv`, is `twofield_zk_v7`; its simulator `simExp2` at those parameters is `simExp2Leak`.
No step of `twofield_zk` is redone, and the bound is exactly its bound.

## What the messages are, and whether a zero block is possible

`push_legacy_macs` MACs, for each of `issuer_sig_e`, `device_pk.x`, `device_pk.y` (`nblk = 6`),
the two 128-bit halves of its 32-byte little-endian encoding (`bytes[..16]`, `bytes[16..]`):

* `issuer_sig_e` is `issuer_sig_digest`, the SHA-256 digest of the COSE `Sig_structure` of the
  MSO (`circuits/src/cbor/mdoc.rs`), read big-endian as an integer;
* `device_pk.x`, `device_pk.y` are the device key's P-256 affine coordinates (`deviceKeyInfo`).

A zero block **is possible for honest inputs**: there are P-256 points with `x < 2^128` (high half
zero) or `x ≡ 0 mod 2^128` (low half zero), and likewise for `y`; and a digest whose low or high
128 bits vanish is a valid `issuer_sig_e`.  For an honestly generated device key and an honest
digest each block is zero with probability about `2^-128`, so the leakage has probability about
`6 · 2^-128` over honest credentials, and finding a digest with a zero half is a 128-bit partial
preimage of SHA-256.  `twofield_zk_v7_nonzero` is the statement for the credentials where it does
not occur; `twofield_zk_v7` holds for all.  Neither is an assumption about the proof: the
leaked bit is computed by the v7 formula itself.

## What is still a hypothesis

`twofield_zk`'s (`CompiledLongfellowZkV7`'s, `CompiledLongfellowZkStat`'s), with validity
(`hvalid₁`, `hvalid₂`) stated at the v7 tags, and `wit₁`, `wit₂` the witnesses as functions of the
v7 shares `ap` (which both circuits' witnesses carry).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.CompiledLongfellowZkV7Mac

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open Lfzk.ZkAdaptiveV1 Lfzk.CompiledLongfellowZk Lfzk.ZkTwoTape Lfzk.Mac Lfzk.MacSep
open Lfzk.CompiledLongfellowZkTwoField

/-! ## 1. The v7 experiment, and the masked public data -/

section Defs

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] [DecidableEq Fmac] {nblk : ℕ}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- Side 1's context as a function of its root, at the v7 tags of the shares `s`. -/
def ctxOf₁V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac) (root₂ : D) : D → Ctx₁ :=
  fun root₁ => ctx₁ root₁ root₂ (Gav (root₁, root₂)) (shiftTag (Gav (root₁, root₂)) s msg)

/-- Side 2's context as a function of its root, after side 1's proof `pf₁`, at the v7 tags. -/
def ctxOf₂V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac)
    (pf₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁) : D → Ctx₂ :=
  fun root₂ => ctx₂ pf₁.root root₂ (Gav (pf₁.root, root₂))
    (shiftTag (Gav (pf₁.root, root₂)) s msg) pf₁

variable {T₁ T₂ f : ℕ}
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f)

/-- **The real two-field run with the v7 MAC, at fixed coins.**  `realCore2` with the v7 tags
`shiftTag av s msg` at the prover's shares `s` (`push_legacy_macs`): both commitments, `av` at the
two roots, side 1 at context `(root₁, root₂, av, tags)`, side 2 after it, the distinguisher on the
tags, both proofs and every challenge oracle. -/
noncomputable def realCore2V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (colsOf (v1Oracle (P₁.FE.msgs (wit₁ s) b₁) ρ₁)) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ s) b₂) ρ₂)) hs₂.2
  let pf₁ := realProof P₁.dec₁ P₁.dec₂ P₁.FE (ctxOf₁V7 ctx₁ msg s Gav (O₂.1 1) (O₁.1 1)) P₁.pts
    (wit₁ s) ρ₁ b₁ hs₁.1 Gr₁ Gl₁ O₁.1
  let pf₂ := realProof P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂V7 ctx₂ msg s Gav pf₁ (O₂.1 1)) P₂.pts
    (wit₂ s) ρ₂ b₂ hs₂.1 Gr₂ Gl₂ O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (shiftTag (Gav (pf₁.root, O₂.1 1)) s msg, pf₁, pf₂) (Gav, Gr₁, Gl₁, Gr₂, Gl₂)) O₁.2 O₂.2

/-- **The real two-field experiment with the v7 MAC.**  Coins: the shares `mac_ap`, `av`'s oracle
and each side's real coins — `realExp2`'s coin space. -/
noncomputable def realExp2V7 :
    Tag Fmac nblk × (D × D → Fmac) × RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- Side 1's public input, reading the tags through `maskTag z`. -/
def maskCtx₁ (z : Fin nblk → Bool) : D → D → Fmac → Tag Fmac nblk → Ctx₁ :=
  fun r₁ r₂ av t => ctx₁ r₁ r₂ av (maskTag z t)

/-- Side 2's public input, reading the tags through `maskTag z`. -/
def maskCtx₂ (z : Fin nblk → Bool) :
    D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ → Ctx₂ :=
  fun r₁ r₂ av t pf₁ => ctx₂ r₁ r₂ av (maskTag z t) pf₁

/-- The distinguisher, reading the tags through `maskTag z`. -/
def maskDist (z : Fin nblk → Bool) :
    TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f :=
  fun p G => dist (maskTag z p.1, p.2.1, p.2.2) G

/--
**The simulator with the zero pattern as leakage.**  `twofield_zk`'s witness-free `simExp2` with the
uniform tag coin `t` published as `maskTag z t`.  It reads the zero pattern `z` and nothing else
that depends on the witness or the message.
-/
noncomputable def simExp2Leak (z : Fin nblk → Bool) :
    Tag Fmac nblk × (D × D → Fmac) × SimCoins P₁.C nw₁ nq₁ reps₁ Tr₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      SimCoins P₂.C nw₂ nq₂ reps₂ Tr₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  simExp2 P₁ P₂ (maskCtx₁ ctx₁ z) (maskCtx₂ ctx₂ z) (maskDist dist z)

/--
**The v7 experiment is a v8 experiment.**  At the v8 blinds `shareEquiv msg s`, with the
witnesses read through `(shareEquiv msg).symm` and the public data and the distinguisher reading the
tags through `maskTag (zeroPat msg)`, `realExp2` is the v7 experiment at the shares `s`.
-/
theorem realExp2V7_eq (ω : Tag Fmac nblk × (D × D → Fmac) ×
      RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂) :
    realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω
      = realExp2 P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
          (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
          (maskDist dist (zeroPat msg)) (shareEquiv msg ω.1, ω.2) := by
  simp only [realExp2V7, realCore2V7, realExp2, realCore2, ctxOf₁V7, ctxOf₂V7, ctxOf₁, ctxOf₂,
    maskCtx₁, maskCtx₂, maskDist, Equiv.symm_apply_apply, maskTag_macTag_shareEquiv]

end Defs

/-! ## 2. Zero knowledge with the v7 MAC -/

section Theorem

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂] [DecidableEq V]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- Validity at the v7 tags is validity of the reparametrised witnesses at the masked v8 tags. -/
theorem hvalid₁_masked
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg))) :
    ∀ ap root₁ root₂ av, P₁.FE.Valid ((fun b => wit₁ ((shareEquiv msg).symm b)) ap)
      (maskCtx₁ ctx₁ (zeroPat msg) root₁ root₂ av (macTag av ap msg)) := by
  intro ap root₁ root₂ av
  have h := hvalid₁ ((shareEquiv msg).symm ap) root₁ root₂ av
  rw [← maskTag_macTag_shareEquiv, Equiv.apply_symm_apply] at h
  exact h

theorem hvalid₂_masked
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁)) :
    ∀ ap root₁ root₂ av pf₁, P₂.FE.Valid ((fun b => wit₂ ((shareEquiv msg).symm b)) ap)
      (maskCtx₂ ctx₂ (zeroPat msg) root₁ root₂ av (macTag av ap msg) pf₁) := by
  intro ap root₁ root₂ av pf₁
  have h := hvalid₂ ((shareEquiv msg).symm ap) root₁ root₂ av pf₁
  rw [← maskTag_macTag_shareEquiv, Equiv.apply_symm_apply] at h
  exact h

/-- **The transfer**: any closeness of the masked v8 experiment to its simulator is the same
closeness of the v7 experiment to the leakage simulator — the reindexing along `shareEquiv`. -/
theorem statClose_v7_of_masked {T₁ T₂ f : ℕ} {ε : ℚ}
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f)
    (h : StatClose ε
      (realExp2 P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
        (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
        (T₁ := T₁) (T₂ := T₂) (maskDist dist (zeroPat msg)))
      (simExp2Leak P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist (zeroPat msg))) :
    StatClose ε (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2Leak P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist (zeroPat msg)) :=
  statClose_reindex ((shareEquiv msg).prodCongr (Equiv.refl _)) (Equiv.refl _)
    (fun ω => realExp2V7_eq P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω) (fun _ => rfl) h

/--
**Zero knowledge of the two-field mdoc proof with the v7 MAC, with the zero pattern as leakage.**

For every pair of witness maps `wit₁ wit₂` (the witnesses as functions of the v7 shares `mac_ap`)
valid at every public input carrying the honest **v7** tags `shiftTag av ap msg`, and every
distinguisher that receives the tags, both compiled proofs and every challenge oracle and makes at
most `f` queries to the two Merkle oracles, the real v7 experiment is `(ε₁ + ε₂)`-close to
`simExp2Leak … (zeroPat msg)`, which reads no witness and no message — only which message blocks
are zero.  `ε₁ + ε₂` is `twofield_zk`'s bound.  The leakage is the v7 formula's
(`MacSep.shiftTag_zero_block`), not the proof's.
-/
theorem twofield_zk_v7 (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
          (Fintype.card (HidingSample n₁ T₁ Salt D)) +
        ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
          (Fintype.card (HidingSample n₂ T₂ Salt D)))
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2Leak P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist (zeroPat msg)) :=
  statClose_v7_of_masked P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist
    (twofield_zk P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
      (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
      hinj₁ hinj₂ (hvalid₁_masked P₁ ctx₁ wit₁ msg hvalid₁)
      (hvalid₂_masked P₂ ctx₂ wit₂ msg hvalid₂)
      hn₁ hn₂ hT₁ hT₂ (maskDist dist (zeroPat msg)))

/-- With no zero block the leakage simulator **is** `twofield_zk`'s simulator. -/
theorem simExp2Leak_of_ne_zero {T₁ T₂ f : ℕ} (hmsg : ∀ j, msg j ≠ 0)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    simExp2Leak P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist (zeroPat msg)
      = simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist := by
  have hm := maskTag_zeroPat_of_ne_zero hmsg
  have e₁ : maskCtx₁ ctx₁ (zeroPat msg) = ctx₁ := by
    funext r₁ r₂ av t; simp only [maskCtx₁, hm, id]
  have e₂ : maskCtx₂ ctx₂ (zeroPat msg) = ctx₂ := by
    funext r₁ r₂ av t pf₁; simp only [maskCtx₂, hm, id]
  have e₃ : maskDist dist (zeroPat msg) = dist := by
    funext p G; simp only [maskDist, hm, id]
  simp only [simExp2Leak, e₁, e₂, e₃]

/--
**Zero knowledge of the two-field mdoc proof with the v7 MAC, when no message block is zero.**

If every 128-bit block of `(issuer_sig_e, device_pk.x, device_pk.y)` is nonzero, the v7 tags are
perfectly hiding and the real v7 experiment is `(ε₁ + ε₂)`-close to `twofield_zk`'s own
witness-free simulation `simExp2`: the same simulator and the same `ε` as for the v8 MAC.
-/
theorem twofield_zk_v7_nonzero (hmsg : ∀ j, msg j ≠ 0) (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
          (Fintype.card (HidingSample n₁ T₁ Salt D)) +
        ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
          (Fintype.card (HidingSample n₂ T₂ Salt D)))
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
  rw [← simExp2Leak_of_ne_zero P₁ P₂ ctx₁ ctx₂ msg hmsg dist]
  exact twofield_zk_v7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₂ hT₁ hT₂
    dist

/--
**Witness indistinguishability with the v7 MAC.**  Two choices of witnesses and common value, both
valid at their v7 tags, **with the same zero pattern**, give `2 · (ε₁ + ε₂)`-close real proofs: both
are close to the same leakage simulation.  With no zero block on either side the patterns agree, so
any two such common values are indistinguishable.
-/
theorem twofield_wi_v7 (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    {wit₁' : Tag Fmac nblk → Wit₁} {wit₂' : Tag Fmac nblk → Wit₂} {msg' : Fin nblk → Fmac}
    (hz : zeroPat msg = zeroPat msg')
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hvalid₁' : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁' s) (ctx₁ root₁ root₂ av (shiftTag av s msg')))
    (hvalid₂' : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂' s) (ctx₂ root₁ root₂ av (shiftTag av s msg') pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose
      (2 * (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
          (Fintype.card (HidingSample n₁ T₁ Salt D)) +
        ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
          (Fintype.card (HidingSample n₂ T₂ Salt D))))
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁' wit₂' msg' (T₁ := T₁) (T₂ := T₂) dist) := by
  have h := twofield_zk_v7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₂ hT₁
    hT₂ dist
  have h' := twofield_zk_v7 P₁ P₂ ctx₁ ctx₂ wit₁' wit₂' msg' hinj₁ hinj₂ hvalid₁' hvalid₂' hn₁ hn₂
    hT₁ hT₂ dist
  rw [← hz] at h'
  rw [two_mul]
  exact h.trans h'.symm

end Theorem

/-! ## 3. The v7 numerals: `≤ 2^-127` at `2^115` Merkle queries -/

section Numerals

open Lfzk.CompiledLongfellowZkV7
open Lfzk.CompiledLigeroZk (Bits256 card_Bits256)

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂] [DecidableEq V]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}

/--
**The two-field proof with the v7 MAC, at `2^115` Merkle-oracle queries: `≤ 2^-127`, with the zero
pattern as leakage**, at every pair of geometries with at most `2^12` columns per side and at least
one opened column — in particular the v7 signature row with any v7 hash row
(`CompiledLongfellowZkV7.v7_rows_small`).  `CompiledLongfellowZkV7.v7_twofield_zk_q115` at the
masked parameters, reindexed.
-/
theorem v7mac_twofield_zk_q115
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Bits256 Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Bits256 Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Bits256 Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hn₁ : 0 < n₁) (hn₁' : n₁ ≤ 2 ^ 12) (hr₁ : 0 < r₁) (hn₂ : 0 < n₂) (hn₂' : n₂ ≤ 2 ^ 12)
    (hr₂ : 0 < r₂) {T₁ T₂ : ℕ} (hT₁ : 2 * n₁ - 1 + 2 ^ 115 ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + 2 ^ 115 ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Bits256 Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V (2 ^ 115)) :
    StatClose (1 / 2 ^ 127)
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2Leak P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist (zeroPat msg)) :=
  statClose_v7_of_masked P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist
    (v7_twofield_zk_q115 P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
      (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
      hinj₁ hinj₂ (hvalid₁_masked P₁ ctx₁ wit₁ msg hvalid₁)
      (hvalid₂_masked P₂ ctx₂ wit₂ msg hvalid₂)
      hn₁ hn₁' hr₁ hn₂ hn₂' hr₂ hT₁ hT₂ (maskDist dist (zeroPat msg)))

/-- **The same, with no zero block**: `≤ 2^-127`-close to `twofield_zk`'s witness-free `simExp2`. -/
theorem v7mac_twofield_zk_q115_nonzero
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Bits256 Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Bits256 Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Bits256 Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hmsg : ∀ j, msg j ≠ 0) (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hn₁ : 0 < n₁) (hn₁' : n₁ ≤ 2 ^ 12) (hr₁ : 0 < r₁) (hn₂ : 0 < n₂) (hn₂' : n₂ ≤ 2 ^ 12)
    (hr₂ : 0 < r₂) {T₁ T₂ : ℕ} (hT₁ : 2 * n₁ - 1 + 2 ^ 115 ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + 2 ^ 115 ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Bits256 Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V (2 ^ 115)) :
    StatClose (1 / 2 ^ 127)
      (realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
  rw [← simExp2Leak_of_ne_zero P₁ P₂ ctx₁ ctx₂ msg hmsg dist]
  exact v7mac_twofield_zk_q115 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₁'
    hr₁ hn₂ hn₂' hr₂ hT₁ hT₂ dist

end Numerals

/-! ## 4. The full-view statistical form -/

section Stat

open Lfzk.CompiledLongfellowZkStat
open Lfzk.CompiledLigeroZk (Bits256 card_Bits256)

section StatDefs

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] [DecidableEq Fmac] {nblk : ℕ}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V)

/-- **The real full-view two-field run with the v7 MAC, at fixed coins**: `realCore2S` at the v7
tags `shiftTag av s msg`. -/
noncomputable def realCore2SV7 (s : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : MerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let root₂ := realRootS P₂.Cod P₂.FE (wit₂ s) ρ₂ b₂ hs₂
  let pf₁ := realProofS P₁.Cod hs₁.2 P₁.dec₁ P₁.dec₂ P₁.FE
    (ctxOf₁V7 ctx₁ msg s Gav root₂ (realRootS P₁.Cod P₁.FE (wit₁ s) ρ₁ b₁ hs₁)) P₁.pts (wit₁ s)
    ρ₁ b₁ hs₁.1 Gr₁ Gl₁
  let pf₂ := realProofS P₂.Cod hs₂.2 P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂V7 ctx₂ msg s Gav pf₁ root₂)
    P₂.pts (wit₂ s) ρ₂ b₂ hs₂.1 Gr₂ Gl₂
  dist (shiftTag (Gav (pf₁.root, root₂)) s msg, pf₁, pf₂) (Gav, Gr₁, Gl₁, Gr₂, Gl₂) hs₁.2 hs₂.2

/-- **The real full-view two-field experiment with the v7 MAC**, on `realExp2S`'s coin space. -/
noncomputable def realExp2SV7 :
    Tag Fmac nblk × (D × D → Fmac) × RealCoinsS P₁.C nw₁ nq₁ reps₁ B₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      RealCoinsS P₂.C nw₂ nq₂ reps₂ B₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- The full-view distinguisher, reading the tags through `maskTag z`. -/
def maskDistS (z : Fin nblk → Bool) :
    TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V :=
  fun p G H₁ H₂ => dist (maskTag z p.1, p.2.1, p.2.2) G H₁ H₂

/-- **The full-view simulator with the zero pattern as leakage**: `simExp2S` with the uniform tag
coin `t` published as `maskTag z t`. -/
noncomputable def simExp2SLeak (z : Fin nblk → Bool) :
    Tag Fmac nblk × (D × D → Fmac) × SimCoinsS P₁.C nw₁ nq₁ reps₁ Tr₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      SimCoinsS P₂.C nw₂ nq₂ reps₂ Tr₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  simExp2S P₁ P₂ (maskCtx₁ ctx₁ z) (maskCtx₂ ctx₂ z) (maskDistS dist z)

/-- **The full-view v7 experiment is a full-view v8 experiment** (`realExp2V7_eq`'s twin). -/
theorem realExp2SV7_eq (ω : Tag Fmac nblk × (D × D → Fmac) ×
      RealCoinsS P₁.C nw₁ nq₁ reps₁ B₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      RealCoinsS P₂.C nw₂ nq₂ reps₂ B₂ Salt D Enc₂ RO₂ LQ₂ Coin₂) :
    realExp2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω
      = realExp2S P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
          (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
          (maskDistS dist (zeroPat msg)) (shareEquiv msg ω.1, ω.2) := by
  simp only [realExp2SV7, realCore2SV7, realExp2S, realCore2S, ctxOf₁V7, ctxOf₂V7, ctxOf₁, ctxOf₂,
    maskCtx₁, maskCtx₂, maskDistS, Equiv.symm_apply_apply, maskTag_macTag_shareEquiv]

/-- With no zero block the full-view leakage simulator **is** `simExp2S`. -/
theorem simExp2SLeak_of_ne_zero (hmsg : ∀ j, msg j ≠ 0) :
    simExp2SLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg) = simExp2S P₁ P₂ ctx₁ ctx₂ dist := by
  have hm := maskTag_zeroPat_of_ne_zero hmsg
  have e₁ : maskCtx₁ ctx₁ (zeroPat msg) = ctx₁ := by
    funext r₁ r₂ av t; simp only [maskCtx₁, hm, id]
  have e₂ : maskCtx₂ ctx₂ (zeroPat msg) = ctx₂ := by
    funext r₁ r₂ av t pf₁; simp only [maskCtx₂, hm, id]
  have e₃ : maskDistS dist (zeroPat msg) = dist := by
    funext p G H₁ H₂; simp only [maskDistS, hm, id]
  simp only [simExp2SLeak, e₁, e₂, e₃]

end StatDefs

section StatThm

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Fintype Enc₁] [DecidableEq Enc₁] [Fintype Enc₂] [DecidableEq Enc₂] [Inhabited D]
variable [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Salt] [DecidableEq Salt] [Nonempty Salt] [Fintype D] [DecidableEq D]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- **The full-view transfer**: closeness of the masked full-view v8 experiment to its simulator is
the same closeness of the full-view v7 experiment to the leakage simulator. -/
theorem statClose_v7S_of_masked {ε : ℚ}
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V)
    (h : StatClose ε
      (realExp2S P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
        (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
        (maskDistS dist (zeroPat msg)))
      (simExp2SLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg))) :
    StatClose ε (realExp2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2SLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg)) :=
  statClose_reindex ((shareEquiv msg).prodCongr (Equiv.refl _)) (Equiv.refl _)
    (fun ω => realExp2SV7_eq P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω) (fun _ => rfl) h

/--
**Statistical zero knowledge of the two-field mdoc proof with the v7 MAC, against a full view, with
the zero pattern as leakage.**  `CompiledLongfellowZkStat.twofield_zk_stat` at the v7 tags: the real
full-view v7 experiment is `((n₁ − r₁) + (n₂ − r₂)) · ε`-close to `simExp2SLeak … (zeroPat msg)`
whenever `|D| ≤ 4 · ε² · |Salt|`.
-/
theorem twofield_zk_stat_v7 (hleaf₁ : Function.Injective P₁.Cod.leafEnc)
    (hleaf₂ : Function.Injective P₂.Cod.leafEnc)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    {ε : ℚ} (hε : 0 ≤ ε) (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V) :
    StatClose (((n₁ - r₁ : ℕ) : ℚ) * ε + ((n₂ - r₂ : ℕ) : ℚ) * ε)
      (realExp2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2SLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg)) :=
  statClose_v7S_of_masked P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist
    (twofield_zk_stat P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
      (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
      hleaf₁ hleaf₂ (hvalid₁_masked P₁ ctx₁ wit₁ msg hvalid₁)
      (hvalid₂_masked P₂ ctx₂ wit₂ msg hvalid₂) hε hD (maskDistS dist (zeroPat msg)))

/-- **The same with no zero block**: close to `twofield_zk_stat`'s own simulator `simExp2S`. -/
theorem twofield_zk_stat_v7_nonzero (hmsg : ∀ j, msg j ≠ 0)
    (hleaf₁ : Function.Injective P₁.Cod.leafEnc) (hleaf₂ : Function.Injective P₂.Cod.leafEnc)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    {ε : ℚ} (hε : 0 ≤ ε) (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V) :
    StatClose (((n₁ - r₁ : ℕ) : ℚ) * ε + ((n₂ - r₂ : ℕ) : ℚ) * ε)
      (realExp2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2S P₁ P₂ ctx₁ ctx₂ dist) := by
  rw [← simExp2SLeak_of_ne_zero P₁ P₂ ctx₁ ctx₂ msg dist hmsg]
  exact twofield_zk_stat_v7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hleaf₁ hleaf₂ hvalid₁ hvalid₂ hε hD dist

end StatThm

section Stat542

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Fintype Enc₁] [DecidableEq Enc₁] [Fintype Enc₂] [DecidableEq Enc₂]
variable [DecidableEq LQ₁] [DecidableEq LQ₂] [Fintype Salt] [DecidableEq Salt] [Nonempty Salt]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}

/--
**The two-field proof with the v7 MAC and 542-bit nonces is statistically zero knowledge,
`≤ 2^-131`, with the zero pattern as leakage**, against a full view, at every pair of geometries
with at most `2^12` columns per side (`CompiledLongfellowZkStat.v7_twofield_zk_stat542` at the
masked parameters, reindexed).
-/
theorem v7mac_twofield_zk_stat542
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hSalt : Fintype.card Salt = 2 ^ 542)
    (hleaf₁ : Function.Injective P₁.Cod.leafEnc) (hleaf₂ : Function.Injective P₂.Cod.leafEnc)
    (hvalid₁ : ∀ s root₁ root₂ av,
      P₁.FE.Valid (wit₁ s) (ctx₁ root₁ root₂ av (shiftTag av s msg)))
    (hvalid₂ : ∀ s root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ s) (ctx₂ root₁ root₂ av (shiftTag av s msg) pf₁))
    (hn₁ : n₁ ≤ 2 ^ 12) (hn₂ : n₂ ≤ 2 ^ 12)
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V) :
    StatClose (1 / 2 ^ 131)
      (realExp2SV7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2SLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg)) :=
  statClose_v7S_of_masked P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist
    (v7_twofield_zk_stat542 P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
      (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
      hSalt hleaf₁ hleaf₂ (hvalid₁_masked P₁ ctx₁ wit₁ msg hvalid₁)
      (hvalid₂_masked P₂ ctx₂ wit₂ msg hvalid₂) hn₁ hn₂ (maskDistS dist (zeroPat msg)))

end Stat542

end Stat

end Lfzk.CompiledLongfellowZkV7Mac
