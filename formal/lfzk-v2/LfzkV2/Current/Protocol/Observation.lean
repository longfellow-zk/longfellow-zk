import LfzkV2.Current.StrandAuthentication
import LfzkV2.Joint.Indexed
import LfzkV2.Current.Protocol.Execution

/-! An actual shared-SHA execution determines its accepting decision and
its paired extracted witness. The observation retains the whole verifier
trace and the exact first-context cuts; no successful-execution or decoder
correspondence certificate is supplied by the application. -/
noncomputable section
namespace LfzkV2.Current.Protocol.Observation
open Application ApplicationSetup CanonicalPrefix
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open Protocol.Execution
open scoped Classical

/-- Complete a recorded verifier trace with a fixed answer elsewhere.
The unused coordinates cannot affect that verifier's decision. -/
def complete {Raw D : Type} [DecidableEq Raw] [Zero D] : List (Raw × D) → Raw → D
  | [],_ => 0
  | (point,answer)::rest,raw => if raw = point then answer else complete rest raw

/-- Repeated raw inputs in an oracle execution have the same answer.
Consequently this simple first-occurrence completion reproduces every
recorded answer, with no uniqueness assumption on the query list. -/
theorem complete_agrees {Raw D : Type} [DecidableEq Raw] [Zero D]
    (trace : List (Raw × D)) (SHA : Raw → D)
    (sound : ∀ qa ∈ trace, qa.2 = SHA qa.1) (raw : Raw) (answer : D)
    (member : (raw,answer) ∈ trace) : complete trace raw = answer := by
  induction trace with
  | nil => cases member
  | cons first rest ih =>
      by_cases same : raw = first.1
      · rw [complete,if_pos same]
        exact (sound first List.mem_cons_self).trans
          ((congrArg SHA same.symm).trans (sound (raw,answer) member).symm)
      · rw [complete,if_neg same]
        apply ih (fun qa present => sound qa (List.mem_cons_of_mem _ present))
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Prod.fst equal))
        · exact present

theorem complete_run_agrees {Raw D Out : Type} [DecidableEq Raw] [Zero D] {fuel : ℕ}
    (program : Tree Raw D Out fuel) (SHA : Raw → D) (qa : Raw × D) (member : qa ∈ (program.run SHA).2) :
    complete (program.run SHA).2 qa.1 = qa.2 :=
  complete_agrees _ SHA (Tree.trace_sound program SHA) _ _ member

section Tuple
variable {Key Out Result Salt : Type} {k s n t : ℕ}
variable (binary prime : Joint.Participant k s n t)
variable (codec : Codec Salt (Joint.Pair.family binary prime).Leaf Digest Bytes)
variable (dec : RoleDecoders codec)
variable [Inhabited (Joint.Pair.family binary prime).Leaf]

/-- One extracted tuple supplies both field participants. This is a pure
function of the context's actual raw cut, not of later verifier queries. -/
def extracted (root : Key → Digest)
    (view : View Out Result Key) (key : Key) :
    JointResponse.Oracle binary prime :=
  Joint.Pair.oracleEquiv binary prime
    ((Joint.Pair.family binary prime).indexedOracle dec (root key) (view.cuts key))

end Tuple

section Runtime
variable {g : Geometry} {fields : Fields} {Advice Key C B Salt Enc Request Context Result : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t capacity blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := BoundedBytes capacity)) C)
variable (bodyCodec : PrefixCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
variable (sample : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) → Tree Strand.Word Digest (Option C) blocks)
variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : BoundedBytes capacity → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
local notation "Annotated" => RuntimeAdaptiveMerkle.Annotated (g := g) (fields := fields)
  (Advice := Advice) (Base := BoundedBytes capacity) (Key := Key) (C := C) (Request := Request)
local notation "fullReplay" => StrandAuthentication.replay binary prime P R cfg earlier bodyCodec sample codec merkleInput

/-- The decoded application is recovered from the same recorded trace as
acceptance, so observing extraction failure needs no additional oracle reads. -/
def decoded (view : View Output Result Context) :=
  RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw view.original.1
    (StrandVerifier.oracle binary prime P R cfg bodyCodec sample (complete view.verifier.2))

/-- Decoding depends only on the verifier trace. Its retained result and
application bookkeeping need no equality conversion. -/
theorem decoded_of_trace (view : View Output Result Context) (SHA : Bytes → Digest)
    (replayed : view.verifier.2 = ((fullReplay view.original.1).run SHA).2) :
    decoded binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw view =
      RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw view.original.1
        (StrandVerifier.oracle binary prime P R cfg bodyCodec sample SHA) := by
  unfold decoded
  rw [replayed]
  exact (StrandAuthentication.decode_raw_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw view.original.1 SHA (complete ((fullReplay view.original.1).run SHA).2)
    (complete_run_agrees (fullReplay view.original.1) SHA)).symm

theorem decoded_actual (output : Output) (SHA : Bytes → Digest)
    (original : List (Bytes × Digest)) (cuts : Context → List (Bytes × Digest)) :
    decoded binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw
        { original := (output,original), verifier := (fullReplay output).run SHA, cuts := cuts } =
      RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
        (StrandVerifier.oracle binary prime P R cfg bodyCodec sample SHA) :=
  decoded_of_trace binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw
    _ SHA rfl

/-- Actual runtime acceptance read from the submitted proof and complete
verifier observation. This invokes the existing verifier, including tuple
Merkle authentication and the final seal, against the trace completion. -/
def decision (view : View Output Result Context) : Bool :=
  StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
    (complete view.verifier.2) merkleInput view.original.1

/-- Acceptance uses the same trace completion as decoding. -/
theorem decision_of_trace (view : View Output Result Context) (SHA : Bytes → Digest)
    (replayed : view.verifier.2 = ((fullReplay view.original.1).run SHA).2) :
    decision binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw view =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA merkleInput view.original.1 := by
  unfold decision
  rw [replayed]
  exact (StrandAuthentication.verify_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw view.original.1 SHA (complete ((fullReplay view.original.1).run SHA).2)
    (complete_run_agrees (fullReplay view.original.1) SHA)).symm

theorem decision_actual (output : Output) (SHA : Bytes → Digest)
    (original : List (Bytes × Digest)) (cuts : Context → List (Bytes × Digest)) :
    decision binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw
      { original := (output,original), verifier := (fullReplay output).run SHA, cuts := cuts } =
        StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
          SHA merkleInput output :=
  decision_of_trace binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw
    _ SHA rfl

end Runtime
end LfzkV2.Current.Protocol.Observation
