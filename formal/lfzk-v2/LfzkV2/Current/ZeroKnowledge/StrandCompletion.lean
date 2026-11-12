import LfzkV2.Current.ZeroKnowledge.OracleProgramming
import LfzkV2.Current.StrandRuntime

/-! Complete-proof finalization for the strand runtime. The complete
canonical body contains terminal authentication before its final-node
input is derived. Its seal is PRF counter zero of that final node, not
the node digest used by the earlier transcript interface. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCompletion
open TranscriptV2 CanonicalPrefix QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key C : Type} {capacity blocks : ℕ}
local notation "Body" => Current.Body g fields Advice Authentication
local notation "Proof" => Current.Proof g fields Advice Authentication
local notation "PacketBlock" => QueryRuntime.Block capacity (ProtocolWrites.Fresh g fields Advice)
local notation "Point" => Replay.Point g fields Advice Authentication Key PacketBlock

variable (bodyCodec : PrefixCodec (Current.Body g fields Advice Authentication))
variable (e : OracleProgramming.BodyEncoding (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Context := Key) (Block := QueryRuntime.Block capacity (ProtocolWrites.Fresh g fields Advice)) (C := C))
variable (sample : Replay.Point g fields Advice Authentication Key
  (QueryRuntime.Block capacity (ProtocolWrites.Fresh g fields Advice)) →
  Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
variable (fallback : C) (initial : Digest)

def finish (body : Body) (SHA : Strand.Oracle) : Proof :=
  let H := StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback SHA
  let pending : Proof := ⟨body,fun _ => 0⟩
  let final := (e.encoding.chain initial).finalSealPoint pending H
  let node := StrandRuntime.history bodyCodec final
  ⟨body,SHA (Strand.Input.prf node.id (SHA node.input.encode) 0).encode⟩

@[simp] theorem finish_body (body : Body) (SHA : Strand.Oracle) :
    (finish bodyCodec e sample fallback initial body SHA).body = body := rfl

def Valid (proof : Proof) (SHA : Strand.Oracle) : Prop :=
  StrandVerifier.sealValid (StrandRuntime.history bodyCodec) sample fallback (e.encoding.chain initial) proof SHA

/-- The actual reconstructed runtime final point supplies the seal input.
No caller-selected final-message buffer or final-node digest is accepted. -/
theorem finish_valid (body : Body) (SHA : Strand.Oracle) :
    Valid bodyCodec e sample fallback initial (finish bodyCodec e sample fallback initial body SHA) SHA := by
  let H := StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback SHA
  have same := OracleProgramming.replay_same_body e initial
    (finish bodyCodec e sample fallback initial body SHA) (⟨body,fun _ => 0⟩ : Proof) rfl H g.roles.length
  rw [Valid,StrandVerifier.sealValid_iff]
  change SHA (Strand.Input.prf
    (StrandRuntime.history bodyCodec ((e.encoding.chain initial).input _)).id
    (SHA (StrandRuntime.history bodyCodec ((e.encoding.chain initial).input _)).input.encode) 0).encode = _
  rw [same]
  rfl

/-- The final node binds exactly the actual complete proof body according
to the same canonical encoder as runtime replay. -/
theorem final_body (proof : Proof) (SHA : Strand.Oracle) :
    ∃ state, (StrandRuntime.history bodyCodec
      ((e.encoding.chain initial).finalSealPoint proof
        (StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback SHA))).input.encode =
      StrandTranscript.finalNodeInput state (bodyCodec.encode proof.body) :=
  StrandRuntime.complete_body_node bodyCodec e.encoding initial proof _

end LfzkV2.Current.ZeroKnowledge.StrandCompletion
