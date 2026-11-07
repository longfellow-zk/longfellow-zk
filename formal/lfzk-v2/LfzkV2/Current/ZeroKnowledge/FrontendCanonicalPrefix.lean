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

theorem initial_matches (fallback : C) :
    Matches e proof initialLink H (CompleteTranscript.initial (e.context proof) fallback) := rfl

theorem point_eq (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length)
    (block : CompleteTranscript.currentBlock base state inside =
      e.block proof ⟨state.rank.val,inside⟩ state.past) :
    CompleteTranscript.query (Authentication := Authentication) base state inside =
      (toReplay e proof state).point := by
  simp only [CompleteTranscript.query,toReplay,Replay.Encoding.stateAt,dif_pos inside]
  rw [block]

theorem advance_eq (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (answer : Digest × C)
    (block : CompleteTranscript.currentBlock base state inside =
      e.block proof ⟨state.rank.val,inside⟩ state.past) :
    toReplay e proof (CompleteTranscript.advance base state inside answer) =
      e.advance proof (toReplay e proof state) answer := by
  simp only [toReplay,Replay.Encoding.stateAt,dif_pos inside,Replay.Encoding.advance,
    CompleteTranscript.advance]
  rw [block]
  rfl

theorem step_matches (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length)
    (matching : Matches e proof initialLink H state)
    (block : CompleteTranscript.currentBlock base state inside =
      e.block proof ⟨state.rank.val,inside⟩ state.past) :
    Matches e proof initialLink H (CompleteTranscript.step base H state).2 := by
  rw [CompleteTranscript.step_query base H state inside]
  unfold Matches
  rw [advance_eq base e proof state inside _ block]
  have query := point_eq base e proof state inside block
  change e.advance proof (toReplay e proof state)
    (H (CompleteTranscript.query base state inside)) =
      (e.chain initialLink).replay proof H (state.rank.val+1)
  rw [query,matching]
  simp only [TranscriptV2.Chain.replay,dif_pos inside,Replay.Encoding.chain]

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalPrefix
