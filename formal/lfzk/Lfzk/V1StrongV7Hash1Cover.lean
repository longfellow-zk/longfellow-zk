import Lfzk.V1StrongV7Hash1Bound

/-! Accepted hash1 paths at the deployed cut: field escape or V1 pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Hash1Cover

open LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
open Merkle.RandomOracle
open scoped Classical

/-- With no satisfying hash-side lift, the compiled accepted path is covered
by the earlier field escape or by the exact terminal event charged in
`hash1_cut_failure_le`. -/
theorem hash1_accepted_at_cut_cover
    {Coin F Other Enc D Salt X Msg₂ Out : Type}
    [Fintype Coin] [Inhabited Coin] [Inhabited Other]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    [Inhabited Msg₂]
    {M nt nlin nl₂ tA N TM : ℕ} {rounds₂ : ℕ → ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out))
    (mt : Fin TM → D)
    (H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂ → Coin) :
    let Ssetup := Lfzk.NizkDeployedHashTwoField.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt H
    let σ : Lfzk.CompiledLongfellowAdaptive.Sig D Coin X Enc :=
      (Ssetup.context mt H, avOf out, pubOf out)
    let tape : Fin (Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds) → Coin :=
      fun j => H (Lfzk.NizkDeployedHashTwoField.hash2
        (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
        (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + j.val))
    let u := Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 1
    let pair := Bcs.terminalPairEquiv u tape
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p H
    (∀ ℓ, ¬ (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ ℓ) →
    Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).V σ)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
        (msgOf₁ out)) tape →
    wellFormed out →
    S.respOf (Sum.inr (responseOf out)) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 S.dom
        baseNodes responseNodes (responseOf out) →
    Lfzk.RbrZkFlat.fieldPrefixEscape
      (H := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).H σ)
      (Sat := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ)
      ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
      (msgOf₁ out) pair.1 ∨
    Lfzk.V1StrongV7Hash1Local.terminalFailureAt
      S baseNodes responseNodes st p (wellFormed out)
      (H (Lfzk.NizkDeployedHashTwoField.hash2
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      (responseOf out)
      (H (Lfzk.NizkDeployedHashTwoField.hash2
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 2)))) := by
  dsimp only
  intro hfalse hacc hwell hdecode
  let Ssetup := Lfzk.NizkDeployedHashTwoField.setup2 body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let out := Ssetup.proof mt H
  let σ : Lfzk.CompiledLongfellowAdaptive.Sig D Coin X Enc :=
    (Ssetup.context mt H, avOf out, pubOf out)
  let tape : Fin (Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds) → Coin :=
    fun j => H (Lfzk.NizkDeployedHashTwoField.hash2
      (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
      (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + j.val))
  let u := Rounds.Role.layerBase v7Hash1.params.rounds
    v7Hash1.params.nl + 1
  let pair := Bcs.terminalPairEquiv u tape
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf
      rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
  let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p H
  have hsplit := Lfzk.V1StrongV7Hash1Adapter.hash1_accepted_field_or_strong_terminal
    S σ baseNodes responseNodes (responseOf out) hdecode
    (msgOf₁ out) (hresponse out hwell) tape hfalse hacc
  dsimp only at hsplit ⊢
  rcases hsplit with hfield | ⟨sys, hbuilt, _, hterminal⟩
  · exact Or.inl hfield
  · right
    have ht := Lfzk.V1StrongV7Hash1Local.deployed_accepts_at_cut
      S baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ mt H sys
      ((S.Vc (avOf out) (pubOf out)).decodeChal pair.2.1)
      (responseOf out)
      ((S.Vc (avOf out) (pubOf out)).decodeQuery pair.2.2)
      hbuilt hterminal
    exact ⟨hwell, ht⟩

end Lfzk.V1StrongV7Hash1Cover
