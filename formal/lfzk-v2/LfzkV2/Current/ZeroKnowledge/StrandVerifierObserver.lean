import LfzkV2.Current.StrandExecution

/-! The actual runtime verifier is an ordinary raw-oracle observer. Its
program records the complete physical replay before computing the decision
from the resulting table. The trace-completion lemma proves this is exactly
the runtime decision, including authentication, sampler failure and the final
seal; it is not an abstract acceptance predicate supplied by a caller. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandVerifierObserver
open Application ApplicationSetup CanonicalPrefix TranscriptV2
open Merkle Merkle.Indexed Merkle.RandomOracle
open scoped Classical
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


def observe (output : Output) : Tree Bytes Digest Bool (2+2*n+(blocks+1)*g.roles.length) :=
  (recordTrace (fullReplay output)).map fun recorded =>
    StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      (StrandExecution.complete recorded.2) merkleInput output

theorem observe_result (output : Output) (SHA : Bytes → Digest) :
    ((observe binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw output).run SHA).1 =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec SHA merkleInput output := by
  rw [observe,Tree.run_map,run_recordTrace]
  exact (StrandAuthentication.verify_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw output SHA (StrandExecution.complete ((fullReplay output).run SHA).2)
    (StrandExecution.complete_run_agrees (fullReplay output) SHA)).symm

/-- A missing proof is rejected, using the same budget as a supplied proof.
This lets privacy compare actual acceptance even on simulator aborts. -/
def optional : Option Output → Tree Bytes Digest Bool (2+2*n+(blocks+1)*g.roles.length)
  | none => .done false
  | some output => observe binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw output

theorem optional_result (output : Option Output) (SHA : Bytes → Digest) :
    ((optional binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw output).run SHA).1 =
      output.any (StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec SHA merkleInput) := by
  cases output with
  | none => rfl
  | some out => exact observe_result binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw out SHA

end LfzkV2.Current.ZeroKnowledge.StrandVerifierObserver
