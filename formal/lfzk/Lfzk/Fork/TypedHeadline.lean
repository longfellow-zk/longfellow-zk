import Lfzk.V1StrongV7Hash1HybridTypedHeadline
import Lfzk.Fork.MacHeadline

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The forked four-slice response constructor discharges the transcript
shape and decoder premises of the v7 hash1 hybrid FS bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.Fork.HybridFS

open Lfzk.V1StrongV7Hash1HybridFS

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkZkDeployedHash
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open Lfzk.V1StrongV7Hash1Adapter (withTypedRespOf withTypedRespOf_response)
open Lfzk.LigeroTranscriptInputs (withResponse withResponse_querySlot)
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

private abbrev typedMsg {Other F Out : Type}
    (raw : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (response : Out → Lfzk.V1StrongV7Terminal.Payload 0 F) :
    Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings) :=
  fun out => withResponse
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (raw out) (response out)

/-- The 116-bit bound with the response message and decoder fixed by the
four-slice V1 payload.  The remaining hypotheses describe the two circuits,
their MAC rows, and the Merkle check. -/
theorem flatEvent_hybrid_fs_ratio_le_116_mac_typed
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
    (Hraw : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
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
    (rawMsgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (common₁ : (Fin Hraw.c.ninp → F) → Fin nblk → Fmac)
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
    (aP : ((D × D) × List (Enc × D)) → Fmac)
    (decode : Coin → Fmac) (tagOf : Out → Fin nblk → Fmac)
    (cands₂ : ((D × D) × List (Enc × D)) → Finset Witness₂)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ v7SigHahn.cardCand)
    (hcands₂ : ∀ σ a, L₂.toZkSide.Good σ a → a ∈ cands₂ σ.1)
    (mac₁ : (Fin Hraw.c.ninp → F) → Fmac → Fin nblk → Fmac)
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
    (hrow₁ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin Hraw.c.ninp → F),
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      (v7Hash1_flatSide (withTypedRespOf Hraw baseNodes responseNodes)).Good σ a →
        mac₁ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out)
    (hrow₂ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Witness₂),
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      L₂.toZkSide.Good σ a →
        mac₂ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf (typedMsg rawMsgOf₁ responseOf) msgOf₂
    let Acc := fun (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
      v7Hash1_flatEvent (withTypedRespOf Hraw baseNodes responseNodes) L₂ rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro)
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
          Acc ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let Htyped := withTypedRespOf
    Hraw baseNodes responseNodes
  let msgTyped := typedMsg rawMsgOf₁ responseOf
  have hresponse : ∀ out, True →
      msgTyped out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out) := by
    intro out _
    exact withResponse_querySlot
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (rawMsgOf₁ out) (responseOf out)
  have hdecode : ∀ out, True →
      Htyped.respOf (Sum.inr (responseOf out)) =
        Lfzk.V1StrongV7Terminal.decodePayload 0 Htyped.dom
          baseNodes responseNodes (responseOf out) := by
    intro out _
    exact withTypedRespOf_response
      Hraw baseNodes responseNodes (responseOf out)
  have hwell : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin),
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
      v7Hash1_flatEvent Htyped L₂ rootOf₁ rootOf₂ avOf pubOf
        msgTyped msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro) →
      True := by
    intro mt ro
    dsimp only
    intro _
    trivial
  exact Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le_116_mac
    Htyped L₂ baseNodes responseNodes body
    rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
    claimOf₁ claimOf₂ common₁ common₂ check hcheck₁ hcheck₂
    responseOf (fun _ => True) hresponse hdecode
    aP decode tagOf cands₂ hcard₂ hcands₂ mac₁ mac₂ hbal hcoll
    dflt hC hD htA hfc ht hF hTM hwell hrow₁ hrow₂

end Lfzk.Fork.HybridFS
