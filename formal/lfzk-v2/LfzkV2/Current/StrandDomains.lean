import LfzkV2.Current.OracleDomain
import LfzkV2.Current.StrandAuthentication
import LfzkV2.Current.SHAOracle
import LfzkV2.Current.MdocIdentifiers

/-! Transcript and authentication queries occupy a fixed byte domain.
Public setup hashes occupy its complement, so fixing setup answers does
not fix any answer used by the runtime verifier. -/
namespace LfzkV2.Current.StrandDomains
open TranscriptV2 Merkle.RandomOracle OracleDomain
open scoped Classical

def protocol (raw : Bytes) : Prop :=
  raw.head? = some 0 ∨ raw.head? = some 1 ∨ SHAOracle.merkleDomain raw

theorem strand (input : Strand.Input) : protocol input.encode := by
  cases input with
  | prf id parent counter => exact Or.inl rfl
  | root message => exact Or.inr (Or.inl rfl)
  | node id parents message => exact Or.inr (Or.inl rfl)

theorem of_merkle {raw : Bytes} (member : SHAOracle.merkleDomain raw) : protocol raw :=
  Or.inr (Or.inr member)

private theorem outside {raw : Bytes} (notZero : raw.head? ≠ some 0) (notOne : raw.head? ≠ some 1)
    (notMerkle : ¬SHAOracle.merkleDomain raw) : ¬protocol raw := by
  rintro (zero | one | merkle)
  · exact notZero zero
  · exact notOne one
  · exact notMerkle merkle


section Setup
variable {F : Type} [Field F]

/-- Setup identifiers hash LFC3 circuit bytes, which start with `L`, so
they lie outside the protocol domain. -/
theorem identifier_not_protocol (fieldId : ℕ) (isBinary : Bool) (width : ℕ) (encode : F → Bytes)
    (outputs logOutput inputs publicInputs : ℕ) (constants : List F) (layers : List SegmentedCircuit.Layer) :
    ¬protocol (MetadataIdentifiers.circuitBytes fieldId isBinary width encode outputs logOutput inputs publicInputs
      constants layers) := by
  have head : (MetadataIdentifiers.circuitBytes fieldId isBinary width encode outputs logOutput inputs publicInputs
      constants layers).head? = some (76 : Framing.Byte) := rfl
  exact outside (by rw [head]; decide) (by rw [head]; decide)
    (SHAOracle.identifier_not_domain fieldId isBinary width encode outputs logOutput inputs publicInputs constants layers)

/-- Fixing the complement of the protocol domain fixes the adapter fragment
identifier. -/
theorem fragment_identifier (complement inside : Bytes → Digest) {leaves : ℕ}
    (encode : F → Bytes) (shape : Adapter.ProductTree.Shape (Adapter.Circuit.half leaves))
    (inputs publicInputs virtualStart : ℕ) :
    MetadataIdentifiers.fragmentId (SHAOracle.merge protocol complement inside) encode shape
        inputs publicInputs virtualStart =
      MetadataIdentifiers.fragmentId complement encode shape inputs publicInputs virtualStart := by
  apply SHAOracle.merge_outside
  exact identifier_not_protocol (F := F) _ _ _ _ _ _ _ _ _ _

end Setup

section Transcript
variable {Point C Out : Type} {rounds blocks : ℕ}
variable (history : Point → Strand.History)
variable (sample : Point → Tree Strand.Word Digest (Option C) blocks) (fallback : C)
variable (model : Chain Point Digest C Out rounds)

theorem readRound (point : Point) :
    UsesOnly protocol (StrandVerifier.readRound history sample fallback point) :=
  ⟨strand _,fun _ => (UsesOnly.mapQueries_all (sample point) _ (fun _ => strand _)).map _⟩

theorem ordinary (out : Out) : UsesOnly protocol (StrandVerifier.replay history sample fallback model out) :=
  UsesOnly.expandQueries _ _ (readRound history sample fallback)

variable {authenticationBudget : ℕ}
variable (authentication : Out × model.State → Tree Bytes Digest Unit authenticationBudget)

theorem complete (out : Out) (allowed : ∀ annotated, UsesOnly protocol (authentication annotated)) :
    UsesOnly protocol (StrandAuthentication.Physical.authenticate history sample fallback model authentication out) := by
  apply (ordinary history sample fallback model out).bind
  intro annotated
  apply (allowed annotated).bind
  intro _
  exact ⟨strand _,fun _ => ⟨strand _,fun _ => trivial⟩⟩

end Transcript

section Indexed
variable {Salt M D Enc : Type} [Inhabited D]
variable (codec : Merkle.Indexed.Codec Salt M D Enc)
variable (domain : Enc → Prop)
variable (leaf : ∀ value, domain (codec.leafEnc value))
variable (node : ∀ index value, domain (codec.nodeEnc index value))
variable (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (proof : Merkle.Indexed.Opening n I Salt D)

include leaf node in
private theorem indexed_operation (values : ℕ → D) (vertex : ℕ) :
    UsesOnly domain (Merkle.Indexed.execute (Merkle.Indexed.operation codec n I a proof values vertex)) := by
  unfold Merkle.Indexed.operation
  split_ifs
  all_goals try trivial
  · exact ⟨leaf _,fun _ => trivial⟩
  · exact ⟨node _ _,fun _ => trivial⟩

include leaf node in
theorem indexed_checkPass : ∀ count values, UsesOnly domain (Merkle.Indexed.checkPass codec n I a proof count values) := by
  intro count
  induction count with
  | zero => intro values; trivial
  | succ count ih =>
      intro values
      exact (indexed_operation codec domain leaf node n I a proof values _).bind _ (fun _ => ih _)

include leaf node in
theorem indexed_check : UsesOnly domain (Merkle.Indexed.check codec n I a proof) :=
  indexed_checkPass codec domain leaf node n I a proof _ _

end Indexed

section Runtime
open Application ApplicationSetup CanonicalPrefix
variable {g : Geometry} {fields : Fields} {Advice Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t capacity blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := BoundedBytes capacity)) C)
variable (wire : NodeWire) (bodyCodec : WholeCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
variable (sample : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) → Tree Strand.Word Digest (Option C) blocks)
variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)
variable (leaf : ∀ value, protocol (merkleInput (codec.leafEnc value)))
variable (node : ∀ index value, protocol (merkleInput (codec.nodeEnc index value)))

include leaf node in
theorem replay (output : RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
    (Advice := Advice) (Request := Request)) :
    UsesOnly protocol (StrandAuthentication.replay binary prime P R cfg earlier wire bodyCodec sample codec merkleInput output) := by
  apply complete _ _ _ _ _ _
  intro annotated
  exact ((indexed_check codec (fun input => protocol (merkleInput input)) leaf node _ _ _ _).map _).mapQueries
    merkleInput (fun _ member => member)

end Runtime

end LfzkV2.Current.StrandDomains
