import LfzkV2.Current.ZeroKnowledge.FrontendCompleteShape
import LfzkV2.Current.Format

/-! Canonical boundary bytes from the public prefix alone are the format's
node encoder `Format.node`. The honest image is identified with the
format's request encoding below. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteWire
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C : Type} {publicCount : ℕ}
variable (fmt : Format g fields Advice publicCount)
variable (binaryRequest : fmt.BinaryRequest) (metadata : fmt.RequestMetadata C) (request : fmt.Request)

/-- Analysis readback of an already generated prefix. The simulator itself
uses `CompleteTranscript.initial/advance`, never this body-facing helper. -/
def prefixState
    (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length)
    (history : History fmt.Key (fmt.Base × ProtocolWrites.Fresh g fields Advice) Digest i.val)
    (past : Fin i.val → C) (fallback : C) :
    CompleteTranscript.State g fields Advice fmt.Key fmt.Base C where
  rank := ⟨i.val,by omega⟩
  history := history
  past := past
  writes j := ProtocolWrites.fresh proof.body ⟨j.val,j.isLt.trans i.isLt⟩
  pending := ProtocolWrites.fresh proof.body i
  lastAnswer := fallback

theorem currentBlock_body
    (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length)
    (history : History fmt.Key (fmt.Base × ProtocolWrites.Fresh g fields Advice) Digest i.val)
    (past : Fin i.val → C) (fallback : C) :
    CompleteTranscript.currentBlock (fmt.node binaryRequest metadata request proof.body.commitment)
        (prefixState fmt proof i history past fallback) i.isLt =
      (fmt.encoding binaryRequest metadata request).block proof i past := by
  have hw : Fin.snoc (fun j : Fin i.val => ProtocolWrites.fresh proof.body ⟨j.val,j.isLt.trans i.isLt⟩)
      (ProtocolWrites.fresh proof.body i) = Format.writes proof.body i := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last,Format.writes,Fin.val_last]
    · simp only [Fin.snoc_castSucc,Format.writes,Fin.val_castSucc]
  dsimp only [CompleteTranscript.currentBlock,prefixState]
  rw [hw,fmt.encoding_block_node]

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteWire
