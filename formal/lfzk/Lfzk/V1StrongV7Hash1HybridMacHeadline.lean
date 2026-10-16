import Lfzk.V1StrongV7Hash1HybridHeadline

/-! The concrete commitment-fixed MAC event in the v7 hash1 hybrid FS bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Hash1HybridFS

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkZkDeployedHash
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

theorem flatEvent_hybrid_fs_ratio_le_116_mac
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Witness₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt₁] [Inhabited Salt₂]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {F₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
    [SumcheckInterp F₂]
    {M nt nlin M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ nblk tA N TM fc : ℕ}
    {codec₁ : Codec Salt₁ (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq)
      D Enc}
    {dec₂ : RoleDecoders codec₂}
    (Hside : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 Coin F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D (HashPoint D Coin X Other F Msg₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (common₁ : (Fin Hside.c.ninp → F) → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (check : Out → Merkle.RandomOracle.Tree Enc D Unit fc)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ v7Hash1.params.row.n
          (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * v7Hash1.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ v7SigHahn.params.row.n
          (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * v7SigHahn.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out))
    (hdecode : ∀ out, wellFormed out →
      Hside.respOf (Sum.inr (responseOf out)) =
        Lfzk.V1StrongV7Terminal.decodePayload 0 Hside.dom
          baseNodes responseNodes (responseOf out))
    (aP : ((D × D) × List (Enc × D)) → Fmac)
    (decode : Coin → Fmac) (tagOf : Out → Fin nblk → Fmac)
    (cands₂ : ((D × D) × List (Enc × D)) → Finset Witness₂)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ v7SigHahn.cardCand)
    (hcands₂ : ∀ σ a, L₂.toZkSide.Good σ a → a ∈ cands₂ σ.1)
    (mac₁ : (Fin Hside.c.ninp → F) → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : Coin => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (dflt : Coin)
    (hC : Fintype.card Coin = 2 ^ 256)
    (hD : Fintype.card D = 2 ^ 256)
    (htA : tA ≤ 2 ^ 116)
    (hfc : fc = 2 * v7Hash1.params.row.n +
      2 * v7SigHahn.params.row.n)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (hwell : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro) →
      wellFormed (Ssetup.proof mt ro))
    (hrow₁ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin Hside.c.ninp → F),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      (v7Hash1_flatSide Hside).Good σ a →
        mac₁ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out)
    (hrow₂ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Witness₂),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      L₂.toZkSide.Good σ a →
        mac₂ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out) :
    let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let Acc := fun (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro)
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
          Acc ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let keyBad : ((D × D) × List (Enc × D)) → Coin → Prop :=
    fun κ c => Lfzk.MacSep.SepMacBad
      (Hside.candsAt (Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g) κ)
      (cands₂ κ) common₁ common₂ mac₁ mac₂
      (aP κ + decode c)
  have hkeyLocal : ∀ κ : ((D × D) × List (Enc × D)),
      (∑ c : Coin, if keyBad κ c then (1 : ℚ) else 0) ≤
        (4 * 2 ^ 128 : ℚ) := by
    intro κ
    have hc := Lfzk.CompiledZk.FlatV7TwoField.v7Hash1_flat_macKey_card_le
      Hside cands₂ hcard₂ common₁ common₂ mac₁ mac₂ hcoll aP decode
      hbal κ
    have h₁ : v7Hash1.cardCand = 2 := by decide
    have h₂ : v7SigHahn.cardCand = 2 := by decide
    rw [h₁, h₂] at hc
    have hcq :
        ((univ.filter fun c : Coin => keyBad κ c).card : ℚ) ≤
          (4 * 2 ^ 128 : ℚ) := by
      have hc' : (univ.filter fun c : Coin => keyBad κ c).card ≤
          4 * 2 ^ 128 := by
        simpa only [keyBad, Nat.reduceMul] using hc
      exact_mod_cast hc'
    simpa only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hcq
  have hkey : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        out (Ssetup.challenges mt ro) →
      ¬ Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat σ →
      ¬ Lfzk.NizkZk.ZkFails L₂.toZkSide.Sat σ →
      keyBad (Ssetup.context mt ro)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))) := by
    intro mt ro
    dsimp only
    intro hflat hg₁ hg₂
    let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt ro
    simp only [v7Hash1_flatEvent] at hflat
    have hav : ro (Sum.inl (rootOf₁ out, rootOf₂ out)) =
        avOf out := by
      simpa [Ssetup, out, Bcs.TotalOracleCommit.Setup.challenges,
        setup2, hash2] using hflat.2.2.1
    have hm := v7Hash1_flatEvent_macKey Hside L₂
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      claimOf₁ claimOf₂ cands₂ hcands₂
      common₁ common₂ mac₁ mac₂ aP decode (tagOf out)
      (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
      out (Ssetup.challenges mt ro) hflat
      (hrow₁ mt ro) (hrow₂ mt ro) hg₁ hg₂
    dsimp only [keyBad]
    rw [hav]
    exact hm
  exact flatEvent_hybrid_fs_ratio_le_116
    Hside L₂ baseNodes responseNodes body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ common₁ common₂ check hcheck₁ hcheck₂
    responseOf wellFormed hresponse hdecode
    keyBad dflt hkeyLocal hC hD htA hfc ht hF hTM hwell hkey

end Lfzk.V1StrongV7Hash1HybridFS
