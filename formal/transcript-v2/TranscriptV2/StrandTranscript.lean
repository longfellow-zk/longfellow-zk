import TranscriptV2.StrandReader

/-! Typed round operations over strands, matching transcript.rs. Labels are
numeric protocol-domain tags; their Longfellow names belong to the enclosing
protocol. Boundary finalization and every PRF block are separate SHA queries.
The complete-proof encoder supplies the actual body to the final seal. -/
namespace TranscriptV2.StrandTranscript
open Framing Strand Merkle.RandomOracle

def utf8 (text : String) : Bytes := text.toUTF8.data.toList.map fun byte =>
  ⟨byte.toNat,UInt8.toNat_lt _⟩

def frame (payload : Bytes) : Bytes := [0] ++ encodeLE 8 payload.length ++ payload

@[simp] theorem frame_drop (payload : Bytes) : (frame payload).drop 9 = payload := rfl

theorem frame_injective : Function.Injective frame := by
  intro a b h
  have hh := congrArg (List.drop 9) h
  simpa only [frame_drop] using hh

def sessionDomain : Bytes := utf8 "longfellow/transcript/v2/strands/v1"
def roundDomain : Bytes := utf8 "longfellow/transcript/v2/round"
def finalDomain : Bytes := utf8 "longfellow/transcript/v2/final"

def new (context : Bytes) : Absorbing := .root (frame sessionDomain ++ frame context)

def writeBytes (state : Absorbing) (bytes : Bytes) : Absorbing := state.write (frame bytes)

def writeScalar {F : Type} (codec : FieldCodec F) (state : Absorbing) (value : F) :
    Absorbing := state.write (1 :: codec.encode value)

def writeSlice {F : Type} (codec : FieldCodec F) (state : Absorbing) (values : List F) :
    Absorbing := state.write (2 :: (encodeLE 8 values.length ++ codec.encodeSlice values))

def roundState (state : Absorbing) (label : Byte) : Absorbing :=
  state.write (frame roundDomain ++ frame [label])

structure Reading where
  reader : Reader
  next : Absorbing

def beginSqueeze (state : Absorbing) (label : Byte) : Tree Bytes Digest (Option Reading) 1 :=
  (continueStrand (roundState state label)).map fun result =>
    result.map fun value => ⟨Reader.ofPrf value.1,value.2⟩

theorem beginSqueeze_run (state : Absorbing) (label : Byte) (id : Word)
    (next : nextCounter state.id = some id) (H : Oracle) :
    (beginSqueeze state label).run H =
      (some ⟨Reader.ofPrf ⟨state.id,H (roundState state label).input.encode,0⟩,
         continuation id (H (roundState state label).input.encode)⟩,
       [((roundState state label).input.encode,H (roundState state label).input.encode)]) := by
  have nextRound : nextCounter (roundState state label).id = some id := by
    simpa only [roundState,Absorbing.write_id] using next
  rw [beginSqueeze,Tree.run_map,continueStrand_run _ id nextRound H]
  simp only [Option.map_some,roundState,Absorbing.write_id]

def Reading.read (state : Reading) (count : ℕ) :
    Tree Bytes Digest (Option (Bytes × Reading)) count :=
  (Reader.read count state.reader).map fun result =>
    result.map fun value => (value.1,⟨value.2,state.next⟩)

def Reading.endRound {A : Type} (state : Reading) (value : A) : Absorbing × A := (state.next,value)

theorem Reading.endRound_does_not_absorb {A : Type} (state : Reading) (a b : A) :
    (state.endRound a).1 = (state.endRound b).1 := rfl

def finalState (state : Absorbing) (body : Bytes) : Absorbing :=
  state.write (frame finalDomain ++ frame body)

def finalNodeInput (state : Absorbing) (body : Bytes) : Bytes := (finalState state body).input.encode

theorem finalNodeInput_id (input : Input) (state : Absorbing) (body : Bytes)
    (valid : input.Valid) (encoded : input.encode = finalNodeInput state body) :
    input.id = state.id := by
  have equal := Input.encode_injective valid (finalState state body).valid encoded
  simpa only [Absorbing.input_id,finalState,Absorbing.write_id] using congrArg Input.id equal

def finalSealInput (state : Absorbing) (body : Bytes) (H : Oracle) : Bytes :=
  (Input.prf state.id (H (finalNodeInput state body)) 0).encode

def finalSeal (state : Absorbing) (body : Bytes) : Tree Bytes Digest Digest 2 :=
  .query (finalNodeInput state body) fun parent =>
    .query (Input.prf state.id parent 0).encode fun finalDigest => .done finalDigest

@[simp] theorem finalSeal_run (state : Absorbing) (body : Bytes) (H : Oracle) :
    (finalSeal state body).run H =
      (H (finalSealInput state body H),
        [(finalNodeInput state body,H (finalNodeInput state body)),
         (finalSealInput state body H,H (finalSealInput state body H))]) := rfl

/-- Canonical body changes alter the final node's preimage without relying
on hash injectivity. Equality of final digests is a separate collision event. -/
theorem finalNodeInput_injective (state : Absorbing) :
    Function.Injective (finalNodeInput state) := by
  intro a b h
  simp only [finalNodeInput,finalState,Absorbing.write_input] at h
  exact frame_injective (List.append_cancel_left (List.append_cancel_left h))

theorem finalSealInput_ne_node (state : Absorbing) (body : Bytes) (H : Oracle) :
    finalSealInput state body H ≠ finalNodeInput state body := by
  unfold finalSealInput finalNodeInput
  cases hs : finalState state body with
  | root message => exact Input.prf_ne_root _ _ _ _
  | node id parent message => exact Input.prf_ne_node _ _ _ _ _ _

/-- This is an encoder-owned operation: the bytes are derived from the
proof's actual body, not accepted as an independent caller-selected message. -/
structure CompleteProof (Body : Type) where
  body : Body
  finalSeal : Digest

def complete {Body : Type} (encodeBody : Body → Bytes) (state : Absorbing) (body : Body) :
    Tree Bytes Digest (CompleteProof Body) 2 :=
  (finalSeal state (encodeBody body)).map fun finalDigest => ⟨body,finalDigest⟩

def verifyFinalSeal {Body : Type} (encodeBody : Body → Bytes) (state : Absorbing)
    (proof : CompleteProof Body) (H : Oracle) : Prop :=
  ((finalSeal state (encodeBody proof.body)).run H).1 = proof.finalSeal

theorem verifyFinalSeal_complete {Body : Type} (encodeBody : Body → Bytes) (state : Absorbing)
    (body : Body) (H : Oracle) :
    verifyFinalSeal encodeBody state ((complete encodeBody state body).run H).1 H := by
  simp only [complete,Tree.run_map,verifyFinalSeal]

/-- A stored final seal differing from the recomputed challenge is rejected.
The actual body is always obtained from the complete proof encoder. -/
theorem verifyFinalSeal_iff {Body : Type} (encodeBody : Body → Bytes) (state : Absorbing)
    (proof : CompleteProof Body) (H : Oracle) :
    verifyFinalSeal encodeBody state proof H ↔
      H (finalSealInput state (encodeBody proof.body) H) = proof.finalSeal := by
  simp only [verifyFinalSeal,finalSeal_run]

/-- Actual wire bytes: the complete-proof encoder appends one 32-byte seal
and stores the body including its terminal authentication data. -/
def encodeComplete {Body : Type} (encodeBody : Body → Bytes) (proof : CompleteProof Body) : Bytes :=
  encodeBody proof.body ++ digestCodec.encode proof.finalSeal

/-- The seal checker binds the received body bytes themselves, as in Rust's
immutable decoded wrapper; it does not trust a separate final-message buffer.
Body parsing and algebraic verification remain distinct, necessary checks. -/
def checkEncodedSeal (state : Absorbing) (encoded : Bytes) (H : Oracle) : Prop :=
  32 ≤ encoded.length ∧
    encoded.drop (encoded.length-32) = digestCodec.encode
      ((finalSeal state (encoded.take (encoded.length-32))).run H).1

theorem checkEncodedSeal_iff {Body : Type} (encodeBody : Body → Bytes) (state : Absorbing)
    (proof : CompleteProof Body) (H : Oracle) :
    checkEncodedSeal state (encodeComplete encodeBody proof) H ↔
      verifyFinalSeal encodeBody state proof H := by
  simp only [checkEncodedSeal,encodeComplete,List.length_append,digestCodec.length,
    show digestCodec.width = 32 from rfl,Nat.add_sub_cancel_right,List.take_left,List.drop_left]
  have hlength : 32 ≤ (encodeBody proof.body).length+32 := by omega
  simp only [hlength,true_and,verifyFinalSeal]
  exact ⟨fun h => (digestCodec.encode_injective h).symm,
    fun h => congrArg digestCodec.encode h.symm⟩

end TranscriptV2.StrandTranscript
