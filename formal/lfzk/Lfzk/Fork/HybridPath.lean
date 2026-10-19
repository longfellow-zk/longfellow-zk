import Lfzk.V1StrongV7Hash1HybridPath
import Lfzk.Fork.PotentialFS

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! Charge a forked V1 hash-side field escape along the same two-field
verifier path used by the potential FS compiler.  The direct terminal event
is explicitly excluded here and bounded separately. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Lfzk.Fork.HybridPath

open Lfzk.V1StrongV7Hash1HybridPath

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkDeployedHash
  Lfzk.NizkZkDeployedHash
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

theorem flatEvent_pays_outside_terminal
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
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      ((v7Hash1_flatSide Hside).LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      (L₂.toZkSide.LD σ))
    (keyBad : ((D × D) × List (Enc × D)) → Coin → Prop)
    (dflt : Coin)
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
    (hkey :
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      ¬ Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat σ →
      ¬ Lfzk.NizkZk.ZkFails L₂.toZkSide.Sat σ →
      keyBad (Ssetup.context mt ro)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hnoTerminal :
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let p := Lfzk.LigeroPairGeometry.ofMessages
        (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
      let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p ro
      ¬ Lfzk.V1StrongV7Hash1Local.terminalFailureAt
        Hside baseNodes responseNodes st p (wellFormed out)
        (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 1))))
        (responseOf out)
        (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 2))))) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt ro
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds +
        Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
      twoFieldHybridCharge (v7Hash1_flatSide Hside) L₂.toZkSide
        P₁ P₂ keyBad dflt (Ssetup.context mt ro)
        (Ssetup.hashInput out i.val)
        (pts2.chal ro (Ssetup.hashInput out i.val))
        (ro (Ssetup.hashInput out i.val)) := by
  let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let out := Ssetup.proof mt ro
  let cut := (Ssetup.context mt ro).2
  have hctx : Ssetup.context mt ro =
      ((rootOf₁ out, rootOf₂ out), cut) := by
    apply Prod.ext <;> rfl
  have hroot₁ : ∀ out, (Ssetup.keyOut out).1 = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, (Ssetup.keyOut out).2 = rootOf₂ out := fun _ => rfl
  have hc := v7Hash1_flatEvent_cover Hside L₂ Ssetup
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ common₁ common₂ check
    hroot₁ hroot₂ mt ro hflat hexp₁ hexp₂
  have hfield : Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat
      (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      let tape : Fin (Rounds.Role.length v7Hash1.params.nl
          v7Hash1.params.rounds) → Coin :=
        fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))
      Lfzk.RbrZkFlat.fieldPrefixEscape
        (H := (v7Hash1_flatSide Hside).H
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (Sat := (v7Hash1_flatSide Hside).Sat
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        ((v7Hash1_flatSide Hside).LD
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₁ out)
        (Bcs.trunc tape
          (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 1)
          (by dsimp [Rounds.Role.length]; omega)) := by
    intro hf
    have hb := Lfzk.Fork.DeployedBridge.flatEvent_field_or_bounded_terminal
      Hside L₂ baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ check
      responseOf wellFormed hresponse hdecode mt ro hflat hexp₁ hexp₂
      hwell (by
        change ∀ ℓ, ¬ (v7Hash1_flatSide Hside).Sat
          (Ssetup.context mt ro, avOf out, pubOf out) ℓ
        rw [hctx]
        exact hf)
    have he := hb.resolve_right hnoTerminal
    dsimp only at he ⊢
    rw [hctx] at he
    convert he using 1
    funext i
    change ro (Sum.inr (Sum.inl (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val))) =
      ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
        out (1 + i.val))
    rw [Lfzk.Fork.Transcript.hash2_side1]
    simp only [Rounds.Role.length]
    omega
  have hacc₂ : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := v7SigHahn.params.nl)
        (w := v7SigHahn.params.rounds)
        (L₂.toZkSide.V
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (L₂.toZkSide.LD
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₂ out))
      (fun i => ro (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun _ : Fin (Rounds.Role.length v7Hash1.params.nl
            v7Hash1.params.rounds) => default)
          msgOf₂ out i.val)))) := by
    have hh := hc.2.1
    rw [hctx] at hh
    convert hh using 1
    funext i
    symm
    change Ssetup.challenges mt ro
      ⟨1 + Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds + i.val, by omega⟩ = _
    change ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      out (1 + Rounds.Role.length v7Hash1.params.nl
        v7Hash1.params.rounds + i.val)) = _
    rw [Lfzk.Fork.Transcript.hash2_side2]
  have hkey' : ¬ Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ Lfzk.NizkZk.ZkFails L₂.toZkSide.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))) := by
    change ¬ Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat
        (Ssetup.context mt ro, avOf out, pubOf out) →
      ¬ Lfzk.NizkZk.ZkFails L₂.toZkSide.Sat
        (Ssetup.context mt ro, avOf out, pubOf out) →
      keyBad (Ssetup.context mt ro)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))) at hkey
    rw [hctx] at hkey
    exact hkey
  have hp := Lfzk.Fork.HybridCharge.twoFieldHybridCharge_accepted_path_of_field
    (v7Hash1_flatSide Hside) L₂.toZkSide P₁ P₂ keyBad dflt
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out cut ro
    hkey' hfield hacc₂
  change 1 ≤ ∑ i : Fin (1 + Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
    twoFieldHybridCharge (v7Hash1_flatSide Hside) L₂.toZkSide
      P₁ P₂ keyBad dflt (Ssetup.context mt ro)
      (Ssetup.hashInput out i.val)
      (pts2.chal ro (Ssetup.hashInput out i.val))
      (ro (Ssetup.hashInput out i.val))
  rw [hctx]
  exact hp

end Lfzk.Fork.HybridPath
