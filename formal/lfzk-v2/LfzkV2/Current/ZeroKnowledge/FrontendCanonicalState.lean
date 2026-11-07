import LfzkV2.Current.ZeroKnowledge.FrontendHistory

/-! Identifying the final stored write prefix with the actual proof body
identifies its whole history with canonical verifier replay. The statement
uses the public request serializer, including metadata and actual link
feedback. It does not ask an earlier round to inspect future proof fields. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalState

open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (shape : WireBlocks.Shape g fields) (defaultAdvice : Advice)
variable (repr : ProofBodyCodec.Representations fields Advice) (setup : FingerprintPrefix.Setup)
variable (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)
variable (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
local notation "e" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request
local notation "base" => CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata
  request proof.body.commitment

theorem block (i : Fin g.roles.length) (past : Fin i.val → C) :
    (e).block proof i past =
      (base i (CanonicalRequest.writes proof.body i) past,ProtocolWrites.fresh proof.body i) := by
  apply Prod.ext
  · exact (CompleteWire.canonicalBase_body shape defaultAdvice repr setup publicCount binaryRequest metadata
      request proof i past).symm
  · exact CanonicalRequest.block_fresh repr shape setup publicCount binaryRequest metadata request proof i past

variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := OpeningBody.Authentication g) (Key := FingerprintPrefix.Key publicCount)
  (Base := CanonicalRequest.Base repr shape setup publicCount) → Digest × C)
variable (initialLink : Digest)

theorem matches_of_writes
    (state : CompleteTranscript.State g fields Advice (FingerprintPrefix.Key publicCount)
      (CanonicalRequest.Base repr shape setup publicCount) C)
    (good : History.Good base H (FingerprintPrefix.context request proof.body.commitment) state)
    (written : ∀ i, state.writes i = ProtocolWrites.fresh proof.body
      ⟨i.val,by have := i.isLt; have := state.rank.isLt; omega⟩) :
    CanonicalPrefix.Matches e proof initialLink H state := by
  exact History.valid_replay base H e proof initialLink (ProtocolWrites.fresh proof.body)
    (block shape defaultAdvice repr setup publicCount binaryRequest metadata request proof)
    state.rank.val (by have := state.rank.isLt; omega) state.history state.past state.writes good written

theorem query_eq
    (state : CompleteTranscript.State g fields Advice (FingerprintPrefix.Key publicCount)
      (CanonicalRequest.Base repr shape setup publicCount) C)
    (inside : state.rank.val < g.roles.length)
    (good : History.Good base H (FingerprintPrefix.context request proof.body.commitment) state)
    (written : ∀ i, state.writes i = ProtocolWrites.fresh proof.body
      ⟨i.val,by have := i.isLt; have := state.rank.isLt; omega⟩)
    (pending : state.pending = ProtocolWrites.fresh proof.body ⟨state.rank.val,inside⟩) :
    CompleteTranscript.query base state inside = ((e).chain initialLink).point proof H state.rank.val := by
  have matching := matches_of_writes shape defaultAdvice repr setup publicCount binaryRequest metadata
    request proof H initialLink state good written
  have log : state.writes = fun i => ProtocolWrites.fresh proof.body
      ⟨i.val,by have := i.isLt; have := state.rank.isLt; omega⟩ := funext written
  have current : CompleteTranscript.currentBlock base state inside =
      (e).block proof ⟨state.rank.val,inside⟩ state.past := by
    change (base ⟨state.rank.val,inside⟩ (Fin.snoc state.writes state.pending) state.past,state.pending) = _
    rw [log,pending]
    exact CompleteWire.currentBlock_body shape defaultAdvice repr setup publicCount binaryRequest metadata
      request proof ⟨state.rank.val,inside⟩ state.history state.past state.lastAnswer
  rw [CanonicalPrefix.point_eq base e proof state inside current,matching]
  rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalState
