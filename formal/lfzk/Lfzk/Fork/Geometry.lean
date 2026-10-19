import Lfzk.LigeroPairGeometryTwoSide
import Lfzk.Fork.Transcript

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! Embed the V1 terminal pair in the full two-side forked oracle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Fork.Geometry

open Lfzk.LigeroPairGeometryTwoSide

open Lfzk.LigeroPairGeometry Lfzk.NizkDeployedHashTwoField
open Lfzk.LigeroTranscriptInputs

variable {D C X Other F Msg₂ : Type} {nl nl₂ block dblock r : ℕ}
  {w w₂ : ℕ → ℕ} [Inhabited Other]

theorem setup2_key_parent_eq_child [Nonempty C] [Inhabited Msg₂]
    {Enc Out : Type} {tA N : ℕ}
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
        (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂))
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (msgOf₂ : Out → ℕ → Msg₂)
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).key
        (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p) =
    (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).key
        (child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p response) := by
  exact key_parent_eq_child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂)
    p response

theorem fieldTape_ofMessages_eq_hash2 [Inhabited Msg₂]
    {Out : Type}
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (msgOf₂ : Out → ℕ → Msg₂)
    (H : Point (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → C)
    (out : Out) (j : Fin (Rounds.Role.layerBase w nl + 1)) :
    fieldTape (outsideTerminal H)
      (Lfzk.LigeroPairGeometry.ofMessages (nl := nl) (w := w)
        (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out)
        (msgOf₁ out)) j =
      H (Lfzk.Fork.Transcript.hash2
        (nl₁ := nl) (nl₂ := nl₂) (w₁ := w) (w₂ := w₂)
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + j.val)) := by
  let ctx := Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out
  have hc : Rounds.Role.layerBase w nl + 1 < Rounds.Role.length nl w := by
    simp [Rounds.Role.length]
  have hparent := Lfzk.LigeroPairGeometry.parent_ofMessages
    (nl := nl) (w := w) ctx (msgOf₁ out)
  have hanc := Lfzk.NizkDeployedHash.anc_msgPoint
    (nl := nl) (w := w) ctx msgOf₁ out j.isLt hc
  have hanc' : (Lfzk.NizkDeployedHash.mpoints
      (Ctx := Lfzk.NizkAdaptiveTwoField.SideCtx D C X)
      (Msg := FirstMessage (Other := Other) (F := F)
        (block := block) (dblock := dblock) (r := r))
      (nl := nl) (w := w)).anc
        (Lfzk.LigeroTranscriptInputs.parentPoint (nl := nl) (w := w)
          ctx (msgOf₁ out)) j.val =
      Lfzk.NizkDeployedHash.msgPoint (nl := nl) (w := w)
        ctx msgOf₁ out j.val := hanc
  have hh := Lfzk.Fork.Transcript.hash2_side1
    (nl₁ := nl) (nl₂ := nl₂) (w₁ := w) (w₂ := w₂)
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
    (show j.val < Rounds.Role.length nl w by omega)
  rw [fieldTape_outsideTerminal, hparent]
  rw [hanc', hh]


end Lfzk.Fork.Geometry
