import TranscriptV2.StrandReader

/-! Typed round operations over strands, matching transcript.rs. Labels are
numeric protocol-domain tags; their Longfellow names belong to the enclosing
protocol. Boundary finalization and every PRF block are separate SHA queries.
The final seal hashes the actual proof body. -/
namespace TranscriptV2.StrandTranscript
open Framing Strand Merkle.RandomOracle

def utf8 (text : String) : Bytes := text.toUTF8.data.toList.map fun byte =>
  ⟨byte.toNat,UInt8.toNat_lt _⟩

def frame (payload : Bytes) : Bytes := [0] ++ encodeLE 8 payload.length ++ payload

@[simp] theorem frame_drop (payload : Bytes) : (frame payload).drop 9 = payload := rfl

def sessionDomain : Bytes := utf8 "longfellow/transcript/v2/strands/v1"

def new (context : Bytes) : Absorbing := .root (frame sessionDomain ++ frame context)

structure Reading where
  reader : Reader
  next : Absorbing

/-! The final node writes a seal frame of the complete body. The frame is a
parameter, so that a transcript format chooses it. -/

/-- The final node under seal frame `close`. -/
def sealState (close : Bytes → Bytes) (state : Absorbing) (body : Bytes) : Absorbing :=
  state.write (close body)

def sealNodeInput (close : Bytes → Bytes) (state : Absorbing) (body : Bytes) : Bytes :=
  (sealState close state body).input.encode

theorem sealNodeInput_id (close : Bytes → Bytes) (input : Input) (state : Absorbing) (body : Bytes)
    (valid : input.Valid) (encoded : input.encode = sealNodeInput close state body) :
    input.id = state.id := by
  have equal := Input.encode_injective valid (sealState close state body).valid encoded
  simpa only [Absorbing.input_id,sealState,Absorbing.write_id] using congrArg Input.id equal

end TranscriptV2.StrandTranscript
