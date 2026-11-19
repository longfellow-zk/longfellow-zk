import LfzkV2.Current.ZeroKnowledge.FrontendPrefix

/-! Match the body-free generator's state to the complete proof encoder.
The generator's local pending write is checked only at the boundary where
it becomes a query. The rest of the proof body is absent from its state.
Advancing feeds back the same oracle answer on both sides. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalPrefix

open SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (e : Replay.Encoding g fields Advice Authentication Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (proof : Replay.Output g fields Advice Authentication) (initialLink : Digest)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

def toReplay (state : CompleteTranscript.State g fields Advice Key Base C) :
    Replay.State g fields Advice Authentication Key (Base × ProtocolWrites.Fresh g fields Advice) C :=
  e.stateAt proof state.rank.val (by have := state.rank.isLt; omega) state.history state.past

def Matches (state : CompleteTranscript.State g fields Advice Key Base C) : Prop :=
  toReplay e proof state = (e.chain initialLink).replay proof H state.rank.val

theorem point_eq (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length)
    (block : CompleteTranscript.currentBlock base state inside =
      e.block proof ⟨state.rank.val,inside⟩ state.past) :
    CompleteTranscript.query (Authentication := Authentication) base state inside =
      (toReplay e proof state).point := by
  simp only [CompleteTranscript.query,toReplay,Replay.Encoding.stateAt,dif_pos inside]
  rw [block]

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalPrefix
