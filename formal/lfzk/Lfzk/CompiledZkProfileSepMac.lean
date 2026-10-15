import Lfzk.CompiledZkProfileRows
import Lfzk.NizkZkDeployedHashSepMac
import Lfzk.TwoFieldSepMacRows

/-!
# The end-to-end two-field headlines with a separate private MAC witness per circuit

`Lfzk.CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec` take MAC rows `hrow₁`, `hrow₂` with
the **same** multiplier share `aP` and the **same private blind** `keyB` on both sides.  The
deployed prover and verifier share only the public tags `proof.macs` and the challenge `av`
(`rust/applications/mdoc_zk/runtime/src/verifier.rs`); each circuit has its own private MAC
witness, and for v7 — the registered circuits, `mac.rs`'s `version < 8` branch — the MAC is

```text
tag j = (av + ap j) · msg j            (push_legacy_macs; mac_circuit.h assert_mac)
```

with no additive blind.  This file restates the end-to-end headlines for that.

## The composition

`NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep` replaces the shared-blind MAC
slot `aP κ + decode c = 0` by `MacSep.SepMacBad`: two candidates, one per side, both fixed by the
commitment context `κ = (roots, cut trace)` before the key point is answered, with different
common values and agreeing MAC equations at the multiplier.  Its count is `|L₁| · |L₂| · kmac`
(`MacSep.sepMacBad_card_le`); at the lift lists' bound `cardCand = 2` the slot costs
`4/2^128 = 2^-126`, per key-point query too, below `κ ≈ 2^-117.1`
(`TwoFieldV1Rows.v7P256ShaK_sep_mac_le_coeff`).

* `CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT_sep` — at two `CompiledZkSide`s,
  `hright` discharged;
* `CircuitSide.cands`, `cands_card_le`, `good_mem_cands` — a circuit side's candidates are its
  lift list's committed witnesses, a function of `κ` alone (`sideLift` reads `σ.1`), at most
  `cardCand`, and every good witness at `(κ, av, pub)` is one;
* `twofield_circuit_ratio_leT_sep` — any two certified rows, both sides from circuits, any MAC
  formula with the fixed-pair collision bound (`hcoll`):

```text
Pr[ both accept ∧ av = ro(key point) ∧ no good pair agrees on the common value ]
    ≤  zkCore₁ + zkCore₂ + cardCand₁·cardCand₂/|Fmac|
       +  N · max(κ₁, κ₂, cardCand₁·cardCand₂/|Fmac|)
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^256
```

* **the headlines**, at the four registered v7 pairs, T-secure at `λ = 115` exactly as before:
  - `v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac` — the **v7** formula `MacSep.shiftTag` with
    per-side private shares `share₁`, `share₂` (the deployed path);
  - `v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepBlind` — the **v8** formula `Mac.macTag` with per-side
    private blinds `blind₁`, `blind₂`.

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

## Which premise was replaced by what

* `keyB : Out → Fin nblk → Fmac` — one private blind, read from the proof, on both sides —
  becomes `share₁`, `share₂` (v7) or `blind₁`, `blind₂` (v8): each side's private MAC witness,
  read from **that side's** witness;
* `hrow₁`: `macTag (aP κ + av) (keyB out) (common₁ a) = tagOf out` becomes
  `shiftTag (aP κ + av) (share₁ a) (common₁ a) = tagOf out` (v7) or
  `macTag (aP κ + av) (blind₁ a) (common₁ a) = tagOf out` (v8);
* `hrow₂`: the same with `share₂ a`, `blind₂ a`.

All other premises are unchanged.  `hrow₁`, `hrow₂` remain assumptions about the circuits: each
asserts its own MAC equation on its bit-packed common value and its own private witness.  `aP` is
kept (an optional public shift of the multiplier fixed by `κ`; deployed it is `0`).

## What is still a hypothesis

`v7P256ShaK_zk_circuit_tsec`'s, with the MAC rows as above.  The Hahn/Delsarte signature row has no
two-field headline in `CompiledZkProfileHahn`; `twofield_circuit_ratio_leT_sep` applies to it as to
any certified row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. Two deployed zero-knowledge sides with separate private MAC witnesses -/

namespace Lfzk.CompiledZkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk
  Lfzk.NizkZkDeployedHash Lfzk.CertifiedV1 Lfzk.Mac
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2 responseOfAt)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open scoped Classical

section ComposeSep

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the deployed zero-knowledge verifiers, each circuit with its own private
MAC witness, against one re-committing prefix-only Fiat–Shamir prover, with no bound on the
prover's Merkle queries.**  `twofield_zk_deployed_ratio_leT` with its shared-blind MAC rows replaced
by per-side MAC rows (`mac₁`, `mac₂`, `hcoll`) and `κ`-indexed candidate sets:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  zkCore₁ + zkCore₂ + B₁·B₂/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, B₁·B₂/|Fmac|)
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

`NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep` at `L₁.toZkSide`, `L₂.toZkSide`,
`hright` discharged by `CompiledZkSide.hrightDH`.
-/
theorem twofield_zk_deployed_ratio_leT_sep {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac) (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (cands₁ : (D × D) × List (Enc × D) → Finset Witness₁)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂) {B₁ B₂ : ℕ}
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁) (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (hcands₁ : ∀ (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) (a : Witness₁), L₁.Good σ a →
      a ∈ cands₁ σ.1)
    (hcands₂ : ∀ (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) (a : Witness₂), L₂.Good σ a →
      a ∈ cands₂ σ.1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand
        + (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            ((B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
            (len2 R₁ R₂ + N) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  have key₁ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
          (slice1 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
            (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁)) codec₁
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
          (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
          (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
          (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  have key₂ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
          (slice2 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
            (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂)) codec₂
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
          (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
          (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
          (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  refine le_trans (le_of_eq ?_)
    (twofield_zk_deployed_adaptive_ratio_leT_sep h₁ dec₁ dec₂
      (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
        (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
        (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      L₁.toZkSide L₂.toZkSide L₁.hF L₂.hF hD₁ hD₂ aP decode kmac hbal hmac tagOf
      common₁ common₂ mac₁ mac₂ hcoll cands₁ cands₂ hcard₁ hcard₂ hcands₁ hcands₂
      (fun mt ro hacc hexp => L₁.hrightDH _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro hacc hexp)
      (fun mt ro hacc hexp => L₂.hrightDH _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro hacc hexp)
      (fun mt ro a hacc hgood => hrow₁ mt ro a ((key₁ (mt, ro)).mpr hacc) hgood)
      (fun mt ro a hacc hgood => hrow₂ mt ro a ((key₂ (mt, ro)).mpr hacc) hgood)
      htape hTM)
  exact congrArg (fun t : Finset ((Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)) =>
      ((t.card : ℕ) : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds)))
    (Finset.filter_congr fun ω _ => and_congr (key₁ ω) (and_congr_left' (key₂ ω)))


end ComposeSep

end Lfzk.CompiledZkDeployedHash

/-! ## 2. A circuit side's candidates are fixed by the commitment context -/

namespace Lfzk.CompiledZk.CircuitSide

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Lfzk.ZkLigeroV1 Lfzk.CertifiedV1
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- **A circuit side's candidates at a commitment context** `κ = (roots, cut trace)`: the committed
witnesses of its extracted matrix's lift list.  A function of `κ` alone — not of the MAC key `av`
or the public data — because the extracted matrix is (`sideLift` reads `σ.1` only). -/
noncomputable def cands (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) : Finset (Fin S.c.ninp → F) :=
  univ.image fun ℓ : ZkLigeroV1.Lift (Row.rowValid hR) S.dom (Row.hkrow hR)
      (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey κ.1, κ.2)) =>
    (asgOf S.pl ℓ).1

/-- At most `cardCand` candidates: the lift list's bound. -/
theorem cands_card_le (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) : (S.cands κ).card ≤ R.cardCand :=
  card_image_le.trans ((card_univ.trans_le (lift_card_le (Row.rowValid hR) S.dom (Row.hkrow hR)
    _)).trans_eq (Row.cand_eq hR).symm)

/-- **Every good witness at a side context `(κ, av, pub)` is a candidate at `κ`**: goodness may
depend on `av` and `pub` (the public input), membership does not. -/
theorem good_mem_cands (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) (a : Fin S.c.ninp → F)
    (h : S.toSide.Good σ a) : a ∈ S.cands σ.1 := by
  obtain ⟨ℓ, -, rfl⟩ := h
  exact mem_image_of_mem _ (mem_univ ℓ)

end Lfzk.CompiledZk.CircuitSide

/-! ## 3. Any two certified rows, both sides from circuits -/

namespace Lfzk.CompiledZkProfileRows

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk
  Lfzk.CompiledZkDeployedHash Lfzk.CertifiedV1 Lfzk.TSec
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.TwoFieldV1Rows Lfzk.Mac Lfzk.MacSep
open scoped Classical

section CircuitSep

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at any two certified rows, both sides from circuits, each circuit with its
own private MAC witness, with no bound on the prover's Merkle queries.**  The candidates are the
lift lists (`CircuitSide.cands`, at most `cardCand` each), so `hcands` and `hcard` are theorems
(`CircuitSide.good_mem_cands`, `CircuitSide.cands_card_le`) and the MAC slot costs
`cardCand₁ · cardCand₂ / |Fmac|`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  zkCore₁ + zkCore₂ + B₁·B₂/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, B₁·B₂/|Fmac|)
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

with `B₁ = R₁.cardCand`, `B₂ = R₂.cardCand`.
`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT_sep` at `S₁.toSide`, `S₂.toSide`.  Any
certified rows: in particular the signature side may be the Hahn/Delsarte row `CertifiedV1.v7SigHahn`.
-/
theorem twofield_circuit_ratio_leT_sep {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin S₁.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 R₁ R₂) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 R₁ R₂) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand
        + (R₁.cardCand * R₂.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            ((R₁.cardCand * R₂.cardCand : ℚ) / (Fintype.card Fmac : ℚ))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
            (len2 R₁ R₂ + N) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have key := twofield_zk_deployed_ratio_leT_sep h₁ h₂ hr₁ hr₂ S₁.toSide S₂.toSide body rootOf₁
    rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD₁ hD₂ aP decode kmac hbal hmac tagOf
    common₁ common₂ mac₁ mac₂ hcoll S₁.cands S₂.cands S₁.cands_card_le S₂.cands_card_le
    S₁.good_mem_cands S₂.good_mem_cands hrow₁ hrow₂ htape hTM
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  convert key using 6

end CircuitSep

/-! ## 4. The v7 pairs, T-secure, with the v7 and the v8 MAC formulas -/

section V7PairsSepTSec


variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1`, as deployed, with the v7 MAC and a separate private share per
circuit, T-secure at `λ = 115`.**  The v7 1-attribute hash circuit over `GF(2^128)` proved first,
then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript with
deployed hash inputs, both field halves constructed from the circuits.  Each circuit asserts the
**v7** MAC (`push_legacy_macs`, `mac_circuit.h` `assert_mac`) on its own witness:

```text
tag j = (av + share_k(a) j) · common_k(a) j          (MacSep.shiftTag)
```

with its own private share `share₁ a` (hash) or `share₂ a` (signature) and the proof's public
tags; nothing relates the two shares.  Against one adaptive program making `tA` Merkle-oracle and
`N` deployed hash queries, **with no bound on either**:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v7 formula (`MacSep.shiftTag_hcoll`), with `twofield_tsec`
and the pair's slack numerals at the separate-MAC slot `4/2^128`
(`TwoFieldV1Rows.v7P256Sha1_sep_slack_bound`, `_sep_slack_coeff`).  The premises are
`v7P256Sha1_zk_circuit_tsec`'s with the shared blind `keyB` and its rows replaced by the per-side shares
`share₁`, `share₂` and the per-side v7 rows.
-/
theorem v7P256Sha1_zk_circuit_tsec_sepMac {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha1.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_sep_slack_bound
  have hsc := v7P256Sha1_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1` with the v8 additive-blind MAC and a separate private blind per
circuit, T-secure at `λ = 115`.**  `v7P256Sha1_zk_circuit_tsec_sepMac` with each circuit asserting the
**v8** MAC (`push_modern_macs`, `circuits_mac::concrete::compute_mac`) on its own witness:

```text
tag j = av · common_k(a) j + blind_k(a) j          (Mac.macTag)
```

with its own private blinds `blind₁ a`, `blind₂ a`; nothing relates them (the case
`SoundnessAudit.separate_blinds_collision` shows the shared-blind argument does not cover):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v8 formula (`MacSep.macTag_hcoll`).  The registered v7
circuits assert the v7 formula; this is the statement for circuits at the v7 rows that assert the
v8 one.
-/
theorem v7P256Sha1_zk_circuit_tsec_sepBlind {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha1.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_sep_slack_bound
  have hsc := v7P256Sha1_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, as deployed, with the v7 MAC and a separate private share per
circuit, T-secure at `λ = 115`.**  The v7 2-attribute hash circuit over `GF(2^128)` proved first,
then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript with
deployed hash inputs, both field halves constructed from the circuits.  Each circuit asserts the
**v7** MAC (`push_legacy_macs`, `mac_circuit.h` `assert_mac`) on its own witness:

```text
tag j = (av + share_k(a) j) · common_k(a) j          (MacSep.shiftTag)
```

with its own private share `share₁ a` (hash) or `share₂ a` (signature) and the proof's public
tags; nothing relates the two shares.  Against one adaptive program making `tA` Merkle-oracle and
`N` deployed hash queries, **with no bound on either**:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v7 formula (`MacSep.shiftTag_hcoll`), with `twofield_tsec`
and the pair's slack numerals at the separate-MAC slot `4/2^128`
(`TwoFieldV1Rows.v7P256Sha2_sep_slack_bound`, `_sep_slack_coeff`).  The premises are
`v7P256Sha2_zk_circuit_tsec`'s with the shared blind `keyB` and its rows replaced by the per-side shares
`share₁`, `share₂` and the per-side v7 rows.
-/
theorem v7P256Sha2_zk_circuit_tsec_sepMac {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha2.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_sep_slack_bound
  have hsc := v7P256Sha2_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2` with the v8 additive-blind MAC and a separate private blind per
circuit, T-secure at `λ = 115`.**  `v7P256Sha2_zk_circuit_tsec_sepMac` with each circuit asserting the
**v8** MAC (`push_modern_macs`, `circuits_mac::concrete::compute_mac`) on its own witness:

```text
tag j = av · common_k(a) j + blind_k(a) j          (Mac.macTag)
```

with its own private blinds `blind₁ a`, `blind₂ a`; nothing relates them (the case
`SoundnessAudit.separate_blinds_collision` shows the shared-blind argument does not cover):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v8 formula (`MacSep.macTag_hcoll`).  The registered v7
circuits assert the v7 formula; this is the statement for circuits at the v7 rows that assert the
v8 one.
-/
theorem v7P256Sha2_zk_circuit_tsec_sepBlind {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha2.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_sep_slack_bound
  have hsc := v7P256Sha2_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, as deployed, with the v7 MAC and a separate private share per
circuit, T-secure at `λ = 115`.**  The v7 3-attribute hash circuit over `GF(2^128)` proved first,
then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript with
deployed hash inputs, both field halves constructed from the circuits.  Each circuit asserts the
**v7** MAC (`push_legacy_macs`, `mac_circuit.h` `assert_mac`) on its own witness:

```text
tag j = (av + share_k(a) j) · common_k(a) j          (MacSep.shiftTag)
```

with its own private share `share₁ a` (hash) or `share₂ a` (signature) and the proof's public
tags; nothing relates the two shares.  Against one adaptive program making `tA` Merkle-oracle and
`N` deployed hash queries, **with no bound on either**:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v7 formula (`MacSep.shiftTag_hcoll`), with `twofield_tsec`
and the pair's slack numerals at the separate-MAC slot `4/2^128`
(`TwoFieldV1Rows.v7P256Sha3_sep_slack_bound`, `_sep_slack_coeff`).  The premises are
`v7P256Sha3_zk_circuit_tsec`'s with the shared blind `keyB` and its rows replaced by the per-side shares
`share₁`, `share₂` and the per-side v7 rows.
-/
theorem v7P256Sha3_zk_circuit_tsec_sepMac {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha3.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_sep_slack_bound
  have hsc := v7P256Sha3_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3` with the v8 additive-blind MAC and a separate private blind per
circuit, T-secure at `λ = 115`.**  `v7P256Sha3_zk_circuit_tsec_sepMac` with each circuit asserting the
**v8** MAC (`push_modern_macs`, `circuits_mac::concrete::compute_mac`) on its own witness:

```text
tag j = av · common_k(a) j + blind_k(a) j          (Mac.macTag)
```

with its own private blinds `blind₁ a`, `blind₂ a`; nothing relates them (the case
`SoundnessAudit.separate_blinds_collision` shows the shared-blind argument does not cover):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v8 formula (`MacSep.macTag_hcoll`).  The registered v7
circuits assert the v7 formula; this is the statement for circuits at the v7 rows that assert the
v8 one.
-/
theorem v7P256Sha3_zk_circuit_tsec_sepBlind {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha3.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_sep_slack_bound
  have hsc := v7P256Sha3_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, as deployed, with the v7 MAC and a separate private share per
circuit, T-secure at `λ = 115`.**  The v7 4-attribute hash circuit over `GF(2^128)` proved first,
then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript with
deployed hash inputs, both field halves constructed from the circuits.  Each circuit asserts the
**v7** MAC (`push_legacy_macs`, `mac_circuit.h` `assert_mac`) on its own witness:

```text
tag j = (av + share_k(a) j) · common_k(a) j          (MacSep.shiftTag)
```

with its own private share `share₁ a` (hash) or `share₂ a` (signature) and the proof's public
tags; nothing relates the two shares.  Against one adaptive program making `tA` Merkle-oracle and
`N` deployed hash queries, **with no bound on either**:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v7 formula (`MacSep.shiftTag_hcoll`), with `twofield_tsec`
and the pair's slack numerals at the separate-MAC slot `4/2^128`
(`TwoFieldV1Rows.v7P256Sha4_sep_slack_bound`, `_sep_slack_coeff`).  The premises are
`v7P256Sha4_zk_circuit_tsec`'s with the shared blind `keyB` and its rows replaced by the per-side shares
`share₁`, `share₂` and the per-side v7 rows.
-/
theorem v7P256Sha4_zk_circuit_tsec_sepMac {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha4.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_sep_slack_bound
  have hsc := v7P256Sha4_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4` with the v8 additive-blind MAC and a separate private blind per
circuit, T-secure at `λ = 115`.**  `v7P256Sha4_zk_circuit_tsec_sepMac` with each circuit asserting the
**v8** MAC (`push_modern_macs`, `circuits_mac::concrete::compute_mac`) on its own witness:

```text
tag j = av · common_k(a) j + blind_k(a) j          (Mac.macTag)
```

with its own private blinds `blind₁ a`, `blind₂ a`; nothing relates them (the case
`SoundnessAudit.separate_blinds_collision` shows the shared-blind argument does not cover):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_circuit_ratio_leT_sep` at the v8 formula (`MacSep.macTag_hcoll`).  The registered v7
circuits assert the v7 formula; this is the statement for circuits at the v7 rows that assert the
v8 one.
-/
theorem v7P256Sha4_zk_circuit_tsec_sepBlind {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_circuit_ratio_leT_sep (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha4.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_sep_slack_bound
  have hsc := v7P256Sha4_sep_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

end V7PairsSepTSec

end Lfzk.CompiledZkProfileRows
