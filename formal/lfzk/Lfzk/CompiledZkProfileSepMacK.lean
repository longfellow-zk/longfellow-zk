import Lfzk.CompiledZkProfileK
import Lfzk.CompiledZkProfileSepMac

/-!
# The separate-MAC headlines with decoders balanced up to a virtual card

`Lfzk.CompiledZkProfileSepMac`'s headlines (`v7P256Sha{1..4}_zk_circuit_tsec_sepMac`, v7 MAC with a
private share per circuit; `…_sepBlind`, v8 MAC with a private blind per circuit) take each side as
a `CircuitSide`, with exactly balanced decoders.  This file restates them with each side a
`CompiledZkProfileK.CircuitSideK` — the decoders balanced up to a virtual card `K` — so that
`Lfzk.StreamCircuitSide`'s stream decoders can discharge them:

* `ZkVirtualCard.twofield_zk_deployed_adaptive_ratio_leT_sepK` — the separate-MAC composition
  (`NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep`) on `ZkVirtualCard`'s chain;
* `CircuitSideK.cands`, `cands_card_le`, `good_mem_cands` — the lift-list candidates, as for
  `CircuitSide`;
* `twofield_circuit_ratio_leT_sepK`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  (K / |C|) · ( zkCore₁ + zkCore₂ + B₁·B₂/|Fmac|
                      + N · max(κ₁, κ₂, B₁·B₂/|Fmac|) )
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^256
```

* `v7P256Sha{1..4}_zk_circuit_tsec_sepMacK`, `…_sepBlindK` — at `K / |C| ≤ 1 + 2^-40`,
  `(1 + tA + N) · 2^-115`, from the slack numerals `v7P256ShaK_sep_slackK_bound`, `_coeff`
  (`native_decide`, with the inflation `lam₀ = 1 + 2^-40`).

## What is still a hypothesis

Those of `CompiledZkProfileSepMac`'s headlines with the exact-balance fields replaced by balance up
to `K`, and `K / |C| ≤ 1 + 2^-40`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. The separate-MAC composition at the virtual card -/

namespace Lfzk.ZkVirtualCard

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashAdaptive Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
  Lfzk.NizkZk Lfzk.CertifiedV1 Lfzk.NizkZkDeployedHash
open scoped Classical

section ComposeSepK

open Lfzk.NizkAdaptiveTwoField (SideCtx check2 len2 sum_roleAt)
open Lfzk.NizkDeployedHashTwoField (Pt2 ctxOf hash2 hash2_zero hash2_side1 hash2_side2 pts2 pget
  pget_side1 pget_side2 setup2)
open Lfzk.Mac Lfzk.MacSep

variable {R₁ R₂ : Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁] [Fintype Q₁] [DecidableEq Q₁]
  [Inhabited Msg₁] [DecidableEq Msg₁] [Fintype Msg₁] {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
  [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂] [Fintype Q₂] [DecidableEq Q₂]
  [Inhabited Msg₂] [DecidableEq Msg₂] [Fintype Msg₂] {M₂ ninp₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ Mc₁ Salt₂ Mc₂ : Type} [Inhabited Salt₁] [Inhabited Mc₁] [Inhabited Salt₂]
  [Inhabited Mc₂] {n₁ n₂ : ℕ}

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow, each circuit with its own private MAC witness, decoders balanced up to a
virtual card `K`.**  `NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep` with every
slot budget computed at `K` (`ZkSideK.budgets`):

```text
Pr[ both verifiers accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  (K / |C|) · ( zkCore₁ + zkCore₂ + B₁·B₂/|Fmac|
                      + N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, B₁·B₂/|Fmac|) )
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```
-/
theorem twofield_zk_deployed_adaptive_ratio_leT_sepK (_h₁ : R₁.Valid) {tA N TM : ℕ} (K : ℕ)
    (hKpos : 0 < K)
    {codec₁ : Codec Salt₁ Mc₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ Mc₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ Mc₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ Mc₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ Mc₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ Mc₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    (S₁ : ZkSideK R₁ logv₁ (((D × D) × List (Enc × D)) × C × X) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁ K)
    (S₂ : ZkSideK R₂ logv₂ (((D × D) × List (Enc × D)) × C × X) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂ K)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (_hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac) (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (cands₁ : (D × D) × List (Enc × D) → Finset Witness₁)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂) {B₁ B₂ : ℕ}
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁) (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (hcands₁ : ∀ (σ : ((D × D) × List (Enc × D)) × C × X) (a : Witness₁), S₁.Good σ a →
      a ∈ cands₁ σ.1)
    (hcands₂ : ∀ (σ : ((D × D) × List (Enc × D)) × C × X) (a : Witness₂), S₂.Good σ a →
      a ∈ cands₂ σ.1)
    (hright₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ) (S₁.LD σ)
          (msgOf₁ (S.proof mt ro)))
        (fun i => S.challenges mt ro ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ) (S₂.LD σ)
          (msgOf₂ (S.proof mt ro)))
        (fun i => S.challenges mt ro
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        JointAccepts K₁ codec₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2 ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ (K : ℚ) / (Fintype.card C : ℚ) * (zkCoreAt R₁ logv₁ R₁.cardCand
          + zkCoreAt R₂ logv₂ R₂.cardCand + (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            ((B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ)))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
          / 2 ^ R₁.params.digestBits) := by
  set S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ with hS
  set dflt : C := Classical.arbitrary C with hdflt
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bz₁ := zkPairBudget K R₁.params.row.fieldSize logv₁
  set bp₁ := pairBudget K R₁.params.row.fieldSize
  set bi₁ := inBudget K R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row K
  set bq₁ := queryBudget R₁.params.row K
  set bz₂ := zkPairBudget K R₂.params.row.fieldSize logv₂
  set bp₂ := pairBudget K R₂.params.row.fieldSize
  set bi₂ := inBudget K R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row K
  set bq₂ := queryBudget R₂.params.row K
  have hB₁ := S₁.budgets hF₁
  have hB₂ := S₂.budgets hF₂
  have hcongr₁ : ∀ σ (ms ms' : ℕ → Msg₁) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (S₁.chainAt σ ms).doomed j p ↔ (S₁.chainAt σ ms').doomed j p :=
    fun σ => zkChain_doomed_congr (S₁.V σ) (S₁.H σ) (S₁.asg σ) (S₁.Sat σ) (S₁.LD σ)
  have hcongr₂ : ∀ σ (ms ms' : ℕ → Msg₂) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (S₂.chainAt σ ms).doomed j p ↔ (S₂.chainAt σ ms').doomed j p :=
    fun σ => zkChain_doomed_congr (S₂.V σ) (S₂.H σ) (S₂.asg σ) (S₂.Sat σ) (S₂.LD σ)
  -- the bad event at a point, by role, reading the ancestors' answers as a total function
  let L₁ := Rounds.Role.length R₁.params.nl R₁.params.rounds
  obtain ⟨Bad', hBad'⟩ : ∃ Bad' : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
        (ℕ → C) → C → Prop,
      Bad' = fun κ q g c => Sum.elim
        (fun _ => SepMacBad (cands₁ κ) (cands₂ κ) common₁ common₂ mac₁ mac₂ (aP κ + decode c))
        (Sum.elim
          (fun p => ZkFails S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) ∧
            (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2) p.msgFn).doomed p.role.slot
              (fun j => g (1 + j.val)) ∧
            ¬ (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2) p.msgFn).doomed (p.role.slot + 1)
              (Bcs.extend (fun j => g (1 + j.val)) c))
          (fun p => ZkFails S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2) ∧
            (S₂.chainAt (κ, p.ctx.1.2.1, p.ctx.1.2.2) p.msgFn).doomed p.role.slot
              (fun j => g (1 + L₁ + j.val)) ∧
            ¬ (S₂.chainAt (κ, p.ctx.1.2.1, p.ctx.1.2.2) p.msgFn).doomed (p.role.slot + 1)
              (Bcs.extend (fun j => g (1 + L₁ + j.val)) c))) q := ⟨_, rfl⟩
  let Bad : (D × D) × List (Enc × D) →
      (x : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds) →
        (Fin (pts2.slot x) → C) → C → Prop :=
    fun κ x pref c => Bad' κ x (pget dflt pref) c
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => B₁ * B₂ * kmac) (Sum.elim
    (fun p => mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
      bz₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
      bz₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x := by
    intro κ x pref
    rcases x with r | p | p
    · have hle : (cands₁ κ).card * (cands₂ κ).card * kmac ≤ B₁ * B₂ * kmac :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (hcard₁ κ) (hcard₂ κ))
      have hcnt := sepMacBad_card_le (cands₁ κ) (cands₂ κ) common₁ common₂ mac₁ mac₂
        (fun a₁ a₂ h => by convert hcoll a₁ a₂ h) (aP κ) decode hbal
      show _ ≤ B₁ * B₂ * kmac
      refine le_trans (Finset.card_le_card ?_) (le_trans hcnt hle)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inl] at hc ⊢
      exact hc
    · set σ := (κ, p.ctx.2.1, p.ctx.2.2) with hσdef
      set g := pget dflt pref
      by_cases hd : (S₁.chainAt σ p.msgFn).doomed p.role.slot (fun j => g (1 + j.val))
      · have hpres := (S₁.FD σ).doom_preserved_chain (S₁.LD σ) (hB₁ σ) p.msgFn p.role.index
          (fun j => g (1 + j.val)) hd
        rw [indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_)
          (le_trans hpres (mixedBudget_mono (S₁.hcand σ) bz₁ bp₁ bi₁ bl₁ bq₁ p.role))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl]
          at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl] at hc
        exact absurd hc.2.1 hd
    · set σ := (κ, p.ctx.1.2.1, p.ctx.1.2.2) with hσdef
      set g := pget dflt pref
      by_cases hd : (S₂.chainAt σ p.msgFn).doomed p.role.slot (fun j => g (1 + L₁ + j.val))
      · have hpres := (S₂.FD σ).doom_preserved_chain (S₂.LD σ) (hB₂ σ) p.msgFn p.role.index
          (fun j => g (1 + L₁ + j.val)) hd
        rw [indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_)
          (le_trans hpres (mixedBudget_mono (S₂.hcand σ) bz₂ bp₂ bi₂ bl₂ bq₂ p.role))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc
        exact absurd hc.2.1 hd
  -- the worst point, and each verifier round's point
  set βmax := max (B₁ * B₂ * kmac) (max
    (NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁) (R₁.cardCand * bi₁) bl₁ bq₁)
    (NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂) (R₂.cardCand * bi₂) bl₂ bq₂))
    with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then B₁ * B₂ * kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
        bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
        bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)), beta (S.hashInput out i.val) ≤ slotBeta i := by
    intro out i
    show beta (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = B₁ * B₂ * kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = B₁ * B₂ * kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
            bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
            bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, mixed_budget_sum, mixed_budget_sum]
  -- the chain: the three-way split of the composed failure, at the verifier's rounds
  have hchain : ∀ (mt : Fin TM → D)
      (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      (JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
        JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
        S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro)) →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro → S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      (¬ ∃ a₁ a₂,
        S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
        S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
        common₁ a₁ = common₂ a₂) →
      (S.grinding mt pts2 Bad beta hbad).RoundBad ro := by
    intro mt ro hacc hex₁ hex₂ hcomp
    set out := S.proof mt ro with hout
    set σ := (S.context mt ro, avOf out, pubOf out) with hσdef
    set ctx₁ := ctxOf rootOf₁ rootOf₂ avOf pubOf out with hctx₁
    by_cases hσ₁ : ZkFails S₁.Sat σ
    · -- side 1 has no good witness: its zero-knowledge LayerStep sheds doom at a side-1 round
      have hz := hright₁ mt ro hacc.1 hex₁
      let ro₁ : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inl p))
      have hch : (fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          S.challenges mt ro ⟨1 + i.val, by omega⟩)
          = fun i => ro₁ (msgPoint ctx₁ msgOf₁ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + i.val)) = _
        rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.isLt]
      rw [hch] at hz
      obtain ⟨k₁, hd, he⟩ := (S₁.FD σ).exists_escape_chain (S₁.LD σ) (hB₁ σ) (msgOf₁ out) _
        hσ₁ hz
      have hsh := shed_at_msgPoint_of (fun ms => (S₁.chainAt σ ms).doomed) (hcongr₁ σ) ctx₁
        msgOf₁ out ro₁ k₁ hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val)))
      rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₁.isLt, hBad']
      simp only [Sum.elim_inr, Sum.elim_inl]
      refine ⟨hσ₁, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₁.params.nl) (w := R₁.params.rounds) ctx₁ msgOf₁
            out k₁.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inl (msgPoint ctx₁ msgOf₁ out k₁.val))))
            (1 + j.val))
          = mpoints.chal ro₁ (msgPoint ctx₁ msgOf₁ out k₁.val) := by
        funext j
        rw [pget_side1]
        rfl
      rw [hpre]
      exact hsh
    by_cases hσ₂ : ZkFails S₂.Sat σ
    · -- side 2 has no good witness
      have hz := hright₂ mt ro hacc.2.1 hex₂
      set ctx₂ := (ctx₁, fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
        msgOf₁ out i.val) with hctx₂
      let ro₂ : MPoint (SideCtx D C X × (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds)
          → Msg₁)) Msg₂ R₂.params.nl R₂.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inr p))
      have hch : (fun i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) =>
          S.challenges mt ro
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩)
          = fun i => ro₂ (msgPoint ctx₂ msgOf₂ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val)) = _
        rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val]
      rw [hch] at hz
      obtain ⟨k₂, hd, he⟩ := (S₂.FD σ).exists_escape_chain (S₂.LD σ) (hB₂ σ) (msgOf₂ out) _
        hσ₂ hz
      have hsh := shed_at_msgPoint_of (fun ms => (S₂.chainAt σ ms).doomed) (hcongr₂ σ) ctx₂
        msgOf₂ out ro₂ k₂ hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)))
      rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₂.val, hBad']
      simp only [Sum.elim_inr]
      refine ⟨hσ₂, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₂.params.nl) (w := R₂.params.rounds) ctx₂ msgOf₂
            out k₂.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inr (msgPoint ctx₂ msgOf₂ out k₂.val))))
            (1 + L₁ + j.val))
          = mpoints.chal ro₂ (msgPoint ctx₂ msgOf₂ out k₂.val) := by
        funext j
        rw [pget_side2]
        rfl
      rw [hpre]
      exact hsh
    -- both sides have good witnesses, which disagree: two fixed candidates collide at the key
    simp only [ZkFails, not_forall, not_not] at hσ₁ hσ₂
    obtain ⟨ℓ₁, hs₁⟩ := hσ₁
    obtain ⟨ℓ₂, hs₂⟩ := hσ₂
    have hg₁ : S₁.Good σ (S₁.wit σ ℓ₁) := ⟨ℓ₁, hs₁, rfl⟩
    have hg₂ : S₂.Good σ (S₂.wit σ ℓ₂) := ⟨ℓ₂, hs₂, rfl⟩
    have hne : common₁ (S₁.wit σ ℓ₁) ≠ common₂ (S₂.wit σ ℓ₂) :=
      fun heq => hcomp ⟨_, _, hg₁, hg₂, heq⟩
    have hm₁ := hrow₁ mt ro _ hacc.1 hg₁
    have hm₂ := hrow₂ mt ro _ hacc.2.1 hg₂
    have hzero : SepMacBad (cands₁ (S.context mt ro)) (cands₂ (S.context mt ro)) common₁ common₂
        mac₁ mac₂ (aP (S.context mt ro) + decode (avOf out)) :=
      ⟨_, hcands₁ σ _ hg₁, _, hcands₂ σ _ hg₂, hne, hm₁.trans hm₂.symm⟩
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
      S.grinding_point mt pts2 Bad beta hbad ro _]
    show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)
      (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)))
      (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0))
    have hav : ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0) = avOf out := hacc.2.2
    rw [hav, hash2_zero rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out, hBad']
    simp only [Sum.elim_inl]
    exact hzero
  -- the generic two-root count
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (NizkAdaptive.lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (NizkAdaptive.lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hgen := S.ratio_le_two codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    Prod.fst Prod.snd claimOf₁ claimOf₂ hcheck₁ hcheck₂ pts2 Bad beta hbad βmax hmax slotBeta hslot
    (by omega) (by omega) htape (by omega)
    (fun mt ro => JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁
        claimOf₁ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
      S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro))
    (fun mt ro => ¬ ∃ a₁ a₂,
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
      common₁ a₁ = common₂ a₂)
    (fun mt ro h => h.1.2.1) (fun mt ro h => h.2.1.2.1) hchain
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (by positivity)) (le_trans hgen ?_)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨⟨hω.1, hω.2.1, hω.2.2.1⟩, hω.2.2.2⟩
  -- the densities, at the virtual card `K`
  rw [hsum]
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hKq : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hKpos
  have hseq₁ := budgets_le_zkCore R₁ logv₁ hKpos hFpos₁ (cardCand := R₁.cardCand)
  have hseq₂ := budgets_le_zkCore R₂ logv₂ hKpos hFpos₂ (cardCand := R₂.cardCand)
  have hmacq₁ : (kmac : ℚ) / (K : ℚ) ≤ 1 / (Fintype.card Fmac : ℚ) := by
    rw [div_le_div_iff₀ hKq (by exact_mod_cast Fintype.card_pos), one_mul]
    exact_mod_cast hmac
  have hmacq : ((B₁ * B₂ * kmac : ℕ) : ℚ) / (K : ℚ)
      ≤ (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ) := by
    have hBB : (0 : ℚ) ≤ (B₁ * B₂ : ℚ) := by positivity
    have := mul_le_mul_of_nonneg_left hmacq₁ hBB
    calc ((B₁ * B₂ * kmac : ℕ) : ℚ) / (K : ℚ)
        = (B₁ * B₂ : ℚ) * ((kmac : ℚ) / (K : ℚ)) := by push_cast; ring
      _ ≤ (B₁ * B₂ : ℚ) * (1 / (Fintype.card Fmac : ℚ)) := this
      _ = (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ) := by ring
  set MM := max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
    ((B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ)) with hMM
  have hβ : (βmax : ℚ) / (K : ℚ) ≤ MM := by
    rw [div_le_iff₀ hKq, hβmax]
    push_cast
    have hk : (B₁ : ℚ) * B₂ * kmac ≤ MM * K := by
      have h := (div_le_iff₀ hKq).mp hmacq
      have hle : (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ) ≤ MM := le_max_right _ _
      push_cast at h
      nlinarith
    have h1 : ((NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁)
          (R₁.cardCand * bi₁) bl₁ bq₁ : ℕ) : ℚ) ≤ MM * K := by
      have hmd := maxBudget_le_zkDensity R₁ logv₁ hKpos hFpos₁ (cardCand := R₁.cardCand)
      have hle : R₁.zkCoefficient logv₁ ≤ MM := le_trans (le_max_left _ _) (le_max_left _ _)
      have hκ : R₁.zkCoefficient logv₁ = zkMaxDensityAt R₁ logv₁ R₁.cardCand := rfl
      rw [← hκ] at hmd
      nlinarith
    have h2 : ((NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂)
          (R₂.cardCand * bi₂) bl₂ bq₂ : ℕ) : ℚ) ≤ MM * K := by
      have hmd := maxBudget_le_zkDensity R₂ logv₂ hKpos hFpos₂ (cardCand := R₂.cardCand)
      have hle : R₂.zkCoefficient logv₂ ≤ MM := le_trans (le_max_right _ _) (le_max_left _ _)
      have hκ : R₂.zkCoefficient logv₂ = zkMaxDensityAt R₂ logv₂ R₂.cardCand := rfl
      rw [← hκ] at hmd
      nlinarith
    exact max_le hk (max_le h1 h2)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R₁.params.digestBits := by rw [hD₁]; push_cast; rfl
  have hsplit : ((N * βmax + (B₁ * B₂ * kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = (K : ℚ) / (Fintype.card C : ℚ) * (N * ((βmax : ℚ) / (K : ℚ))
        + ((B₁ * B₂ * kmac : ℕ) : ℚ) / (K : ℚ)
        + ((R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁ : ℕ)
            : ℚ) / (K : ℚ)
        + ((R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂ : ℕ)
            : ℚ) / (K : ℚ)) := by
    push_cast
    field_simp
    ring
  rw [hsplit, hDq]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have hNβ := mul_le_mul_of_nonneg_left hβ hN
  have hlam : (0 : ℚ) ≤ (K : ℚ) / (Fintype.card C : ℚ) := by positivity
  have inner : N * ((βmax : ℚ) / (K : ℚ)) + ((B₁ * B₂ * kmac : ℕ) : ℚ) / (K : ℚ)
        + ((R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁ : ℕ)
            : ℚ) / (K : ℚ)
        + ((R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂ : ℕ)
            : ℚ) / (K : ℚ)
      ≤ zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand
        + (B₁ * B₂ : ℚ) / (Fintype.card Fmac : ℚ) + N * MM := by
    linarith
  have := mul_le_mul_of_nonneg_left inner hlam
  linarith

end ComposeSepK

end Lfzk.ZkVirtualCard

/-! ## 2. A circuit side's candidates -/

namespace Lfzk.CompiledZkProfileK.CircuitSideK

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.ZkLigeroV1
  Lfzk.CompiledZk Lfzk.CertifiedV1
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D} {K : ℕ}

/-- **A circuit side's candidates at a commitment context** (`CircuitSide.cands`): the committed
witnesses of its extracted matrix's lift list, a function of `κ` alone. -/
noncomputable def cands (S : CircuitSideK R hR hr logv C F Msg M nt nlin X dec rootOfKey K)
    (κ : (D × D) × List (Enc × D)) : Finset (Fin S.c.ninp → F) :=
  univ.image fun ℓ : ZkLigeroV1.Lift (Row.rowValid hR) S.dom (Row.hkrow hR)
      (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey κ.1, κ.2)) =>
    (asgOf S.pl ℓ).1

theorem cands_card_le (S : CircuitSideK R hR hr logv C F Msg M nt nlin X dec rootOfKey K)
    (κ : (D × D) × List (Enc × D)) : (S.cands κ).card ≤ R.cardCand :=
  card_image_le.trans ((card_univ.trans_le (lift_card_le (Row.rowValid hR) S.dom (Row.hkrow hR)
    _)).trans_eq (Row.cand_eq hR).symm)

theorem good_mem_cands (S : CircuitSideK R hR hr logv C F Msg M nt nlin X dec rootOfKey K)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) (a : Fin S.c.ninp → F)
    (h : S.toZkSideK.Good σ a) : a ∈ S.cands σ.1 := by
  obtain ⟨ℓ, -, rfl⟩ := h
  exact mem_image_of_mem _ (mem_univ ℓ)

end Lfzk.CompiledZkProfileK.CircuitSideK

/-! ## 3. Two circuit sides with separate MAC witnesses, at the virtual card -/

namespace Lfzk.CompiledZkProfileK

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk
  Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1 Lfzk.ZkVirtualCard Lfzk.CompiledZkDeployedHash
  Lfzk.NizkZkDeployedHash Lfzk.Mac Lfzk.MacSep
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (Sig responseOfAt slice1 slice2)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open scoped Classical

section ComposeSepK

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
**Two-field Longfellow at any two certified rows, both sides from circuits with decoders balanced
up to `K`, each circuit with its own private MAC witness**:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  (K / |C|) · ( zkCore₁ + zkCore₂ + cardCand₁·cardCand₂/|Fmac|
                      + N · max(κ₁, κ₂, cardCand₁·cardCand₂/|Fmac|) )
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

`CompiledZkProfileSepMac.twofield_circuit_ratio_leT_sep` on the virtual-card chain.
-/
theorem twofield_circuit_ratio_leT_sepK {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ} (K : ℕ) (hKpos : 0 < K)
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CircuitSideK R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (L₂ : CircuitSideK R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin L₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin L₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin L₁.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin L₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin L₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin L₂.c.ninp → F₂),
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
      ≤ (K : ℚ) / (Fintype.card C : ℚ) * (zkCoreAt R₁ logv₁ R₁.cardCand
          + zkCoreAt R₂ logv₂ R₂.cardCand
          + (R₁.cardCand * R₂.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            ((R₁.cardCand * R₂.cardCand : ℚ) / (Fintype.card Fmac : ℚ)))
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
    (twofield_zk_deployed_adaptive_ratio_leT_sepK h₁ K hKpos dec₁ dec₂
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
      L₁.toZkSideK L₂.toZkSideK L₁.hF L₂.hF hD₁ hD₂ aP decode kmac hbal hmac tagOf
      common₁ common₂ mac₁ mac₂ hcoll L₁.cands L₂.cands L₁.cands_card_le L₂.cands_card_le
      L₁.good_mem_cands L₂.good_mem_cands
      (fun mt ro hacc hexp => L₁.hrightDH _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro hacc hexp)
      (fun mt ro hacc hexp => L₂.hrightDH _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro hacc hexp)
      (fun mt ro a hacc hgood => hrow₁ mt ro a ((key₁ (mt, ro)).mpr hacc) hgood)
      (fun mt ro a hacc hgood => hrow₂ mt ro a ((key₂ (mt, ro)).mpr hacc) hgood)
      htape hTM)
  congr 3
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  exact and_congr (key₁ ω) (and_congr_left' (key₂ ω))

end ComposeSepK

/-! ## 4. The v7 pairs, T-secure, decoders balanced up to `K` -/

section TSecSepK

open Lfzk.TSec Lfzk.TwoFieldV1Rows

/-- `v7P256Sha1` with the separate-MAC slot, inflated by `lam₀ = 1 + 2^-40`, at `N = 0`: at most
`2^-115`. -/
theorem v7P256Sha1_sep_slackK_bound :
    lam₀ * (v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3
        + (v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha1`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-116`. -/
theorem v7P256Sha1_sep_slackK_coeff :
    lam₀ * max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        ((v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2` with the separate-MAC slot, inflated by `lam₀ = 1 + 2^-40`, at `N = 0`: at most
`2^-115`. -/
theorem v7P256Sha2_sep_slackK_bound :
    lam₀ * (v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4
        + (v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-116`. -/
theorem v7P256Sha2_sep_slackK_coeff :
    lam₀ * max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        ((v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3` with the separate-MAC slot, inflated by `lam₀ = 1 + 2^-40`, at `N = 0`: at most
`2^-115`. -/
theorem v7P256Sha3_sep_slackK_bound :
    lam₀ * (v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4
        + (v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-116`. -/
theorem v7P256Sha3_sep_slackK_coeff :
    lam₀ * max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        ((v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4` with the separate-MAC slot, inflated by `lam₀ = 1 + 2^-40`, at `N = 0`: at most
`2^-115`. -/
theorem v7P256Sha4_sep_slackK_bound :
    lam₀ * (v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5
        + (v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-116`. -/
theorem v7P256Sha4_sep_slackK_coeff :
    lam₀ * max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        ((v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

end TSecSepK

section V7PairsSepTSecK

open Lfzk.TSec Lfzk.TwoFieldV1Rows

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
**`CompiledZkProfileSepMac.v7P256Sha1_zk_circuit_tsec_sepMac` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha1_zk_circuit_tsec_sepMac`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha1_zk_circuit_tsec_sepMacK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha1.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_sep_slackK_bound
  have hsc := v7P256Sha1_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha1_zk_circuit_tsec_sepBlind` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha1_zk_circuit_tsec_sepBlind`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha1_zk_circuit_tsec_sepBlindK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha1.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_sep_slackK_bound
  have hsc := v7P256Sha1_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha2_zk_circuit_tsec_sepMac` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha2_zk_circuit_tsec_sepMac`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha2_zk_circuit_tsec_sepMacK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha2.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_sep_slackK_bound
  have hsc := v7P256Sha2_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha2_zk_circuit_tsec_sepBlind` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha2_zk_circuit_tsec_sepBlind`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha2_zk_circuit_tsec_sepBlindK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha2.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_sep_slackK_bound
  have hsc := v7P256Sha2_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha3_zk_circuit_tsec_sepMac` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha3_zk_circuit_tsec_sepMac`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha3_zk_circuit_tsec_sepMacK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha3.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_sep_slackK_bound
  have hsc := v7P256Sha3_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha3_zk_circuit_tsec_sepBlind` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha3_zk_circuit_tsec_sepBlind`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha3_zk_circuit_tsec_sepBlindK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha3.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_sep_slackK_bound
  have hsc := v7P256Sha3_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha4_zk_circuit_tsec_sepMac` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha4_zk_circuit_tsec_sepMac`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha4_zk_circuit_tsec_sepMacK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (share₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (share₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      shiftTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (share₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => shiftTag x (share₁ a) (common₁ a))
    (fun a x => shiftTag x (share₂ a) (common₂ a))
    (shiftTag_hcoll common₁ common₂ share₁ share₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha4.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_sep_slackK_bound
  have hsc := v7P256Sha4_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**`CompiledZkProfileSepMac.v7P256Sha4_zk_circuit_tsec_sepBlind` with decoders balanced up to a virtual card `K`,
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  Each side is a `CircuitSideK`, the MAC decoder is
balanced up to `K`; otherwise the premises are `v7P256Sha4_zk_circuit_tsec_sepBlind`'s:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha4_zk_circuit_tsec_sepBlindK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
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
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (blind₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (blind₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₁ a) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (blind₂ a) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_circuit_ratio_leT_sepK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos K hKpos S₁ S₂
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac tagOf common₁
    common₂ (fun a x => macTag x (blind₁ a) (common₁ a))
    (fun a x => macTag x (blind₂ a) (common₂ a))
    (macTag_hcoll common₁ common₂ blind₁ blind₂) hrow₁ hrow₂ htape hTM
  have hm : ((v7P256Sha4.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_sep_slackK_bound
  have hsc := v7P256Sha4_sep_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

end V7PairsSepTSecK

end Lfzk.CompiledZkProfileK
