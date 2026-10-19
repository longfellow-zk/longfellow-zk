import Lfzk.V1StrongV7Hash1DeployedBridge
import Lfzk.Fork.Cover

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The forked flat extraction event feeds the exact strong V1 terminal
event used by the local probability theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.Fork.DeployedBridge

open Lfzk.V1StrongV7Hash1DeployedBridge

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

theorem flatEvent_field_or_bounded_terminal
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Witness₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X]
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
    (body : TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds)
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
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out))
    (hdecode : ∀ out, wellFormed out →
      Hside.respOf (Sum.inr (responseOf out)) =
        Lfzk.V1StrongV7Terminal.decodePayload 0 Hside.dom
          baseNodes responseNodes (responseOf out))
    (mt : Fin TM → D)
    (ro : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → Coin)
    (hflat :
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro))
    (hexp₁ : (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).Explains dec₁ Prod.fst claimOf₁ mt ro)
    (hexp₂ : (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).Explains dec₂ Prod.snd claimOf₂ mt ro)
    (hwell : wellFormed
      ((Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hfalse :
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      ∀ ℓ, ¬ (v7Hash1_flatSide Hside).Sat σ ℓ) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt ro
    let σ := (Ssetup.context mt ro, avOf out, pubOf out)
    let tape : Fin (Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds) → Coin :=
      fun j => ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ out (1 + j.val))
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p ro
    Lfzk.RbrZkFlat.fieldPrefixEscape
      (H := (v7Hash1_flatSide Hside).H σ)
      (Sat := (v7Hash1_flatSide Hside).Sat σ)
      ((v7Hash1_flatSide Hside).LD σ) (msgOf₁ out)
      (Bcs.trunc tape
        (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1)
        (by dsimp [Rounds.Role.length]; omega)) ∨
    Lfzk.V1StrongV7Hash1Local.terminalFailureAt
      Hside baseNodes responseNodes st p (wellFormed out)
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      (responseOf out)
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 2)))) := by
  let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let out := Ssetup.proof mt ro
  have hroot₁ : ∀ out, (Ssetup.keyOut out).1 = rootOf₁ out := by
    intro x
    rfl
  have hroot₂ : ∀ out, (Ssetup.keyOut out).2 = rootOf₂ out := by
    intro x
    rfl
  have hc := v7Hash1_flatEvent_cover Hside L₂ Ssetup
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ common₁ common₂ check
    hroot₁ hroot₂ mt ro hflat hexp₁ hexp₂
  have htape :
      Lfzk.CompiledLongfellowAdaptive.slice1 v7Hash1 v7SigHahn
        (Ssetup.challenges mt ro) =
      (fun i => ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ out (1 + i.val))) := by
    funext i
    rfl
  have hacc : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        ((v7Hash1_flatSide Hside).V
          (Ssetup.context mt ro, avOf out, pubOf out))
        ((v7Hash1_flatSide Hside).LD
          (Ssetup.context mt ro, avOf out, pubOf out))
        (msgOf₁ out))
      (fun i => ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ out (1 + i.val))) := by
    simpa only [out, Ssetup, htape]
      using hc.1
  exact Lfzk.Fork.Cover.hash1_accepted_at_cut_cover
    Hside baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ responseOf wellFormed hresponse mt ro
    hfalse hacc hwell (hdecode out hwell)

end Lfzk.Fork.DeployedBridge

namespace Lfzk.Fork.DeployedBridge

open Lfzk.V1StrongV7Hash1DeployedBridge

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

/-- The four-slice schedule and decoder identities are definitional when
the forked side is instantiated with the typed response constructors. -/
theorem flatEvent_field_or_bounded_terminal_typed
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Witness₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X]
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
    (body : TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds)
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
    (common₁ : (Fin Hside.c.ninp → F) → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (check : Out → Merkle.RandomOracle.Tree Enc D Unit fc)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (mt : Fin TM → D)
    (ro : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → Coin)
    (hflat :
      let Htyped := Lfzk.V1StrongV7Hash1Adapter.withTypedRespOf
        Hside baseNodes responseNodes
      let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
        (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
        (rawMsgOf₁ out) (responseOf out)
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
      v7Hash1_flatEvent Htyped L₂ rootOf₁ rootOf₂ avOf pubOf
        msgTyped msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro))
    (hexp₁ :
      let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
        (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
        (rawMsgOf₁ out) (responseOf out)
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂).Explains
        dec₁ Prod.fst claimOf₁ mt ro)
    (hexp₂ :
      let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
        (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
        (rawMsgOf₁ out) (responseOf out)
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂).Explains
        dec₂ Prod.snd claimOf₂ mt ro)
    (hfalse :
      let Htyped := Lfzk.V1StrongV7Hash1Adapter.withTypedRespOf
        Hside baseNodes responseNodes
      let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
        (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
        (rawMsgOf₁ out) (responseOf out)
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      ∀ ℓ, ¬ (v7Hash1_flatSide Htyped).Sat σ ℓ) :
    let Htyped := Lfzk.V1StrongV7Hash1Adapter.withTypedRespOf
      Hside baseNodes responseNodes
    let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (rawMsgOf₁ out) (responseOf out)
    let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
    let out := Ssetup.proof mt ro
    let σ := (Ssetup.context mt ro, avOf out, pubOf out)
    let tape : Fin (Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds) → Coin :=
      fun j => ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgTyped msgOf₂ out (1 + j.val))
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out) (msgTyped out)
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p ro
    Lfzk.RbrZkFlat.fieldPrefixEscape
      (H := (v7Hash1_flatSide Htyped).H σ)
      (Sat := (v7Hash1_flatSide Htyped).Sat σ)
      ((v7Hash1_flatSide Htyped).LD σ) (msgTyped out)
      (Bcs.trunc tape
        (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1)
        (by dsimp [Rounds.Role.length]; omega)) ∨
    Lfzk.V1StrongV7Hash1Local.terminalFailureAt
      Htyped baseNodes responseNodes st p True
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      (responseOf out)
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 2)))) := by
  let Htyped := Lfzk.V1StrongV7Hash1Adapter.withTypedRespOf
    Hside baseNodes responseNodes
  let msgTyped := fun out => Lfzk.LigeroTranscriptInputs.withResponse
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (rawMsgOf₁ out) (responseOf out)
  have hresponse : ∀ out, True →
      msgTyped out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out) := by
    intro out _
    exact Lfzk.LigeroTranscriptInputs.withResponse_querySlot
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (rawMsgOf₁ out) (responseOf out)
  have hdecode : ∀ out, True →
      Htyped.respOf (Sum.inr (responseOf out)) =
        Lfzk.V1StrongV7Terminal.decodePayload 0 Htyped.dom
          baseNodes responseNodes (responseOf out) := by
    intro out _
    exact Lfzk.V1StrongV7Hash1Adapter.withTypedRespOf_response
      Hside baseNodes responseNodes (responseOf out)
  exact Lfzk.Fork.DeployedBridge.flatEvent_field_or_bounded_terminal Htyped L₂ baseNodes responseNodes
    body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂ claimOf₁ claimOf₂
    common₁ common₂ check responseOf (fun _ => True) hresponse hdecode
    mt ro hflat hexp₁ hexp₂ trivial hfalse

end Lfzk.Fork.DeployedBridge
