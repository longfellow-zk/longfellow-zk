import LfzkV2.Current.OracleDomain
import LfzkV2.Current.StrandAuthentication
import LfzkV2.Current.SHASetupDomains

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

theorem circuit_outside {F : Type} [Field F] (fieldId : ℕ) (binary : Bool) (width : ℕ) (encode : F → Bytes)
    (outputs logOutput inputs publicInputs : ℕ) (constants : List F) (layers : List SegmentedCircuit.Layer) :
    ¬protocol (MetadataIdentifiers.circuitBytes fieldId binary width encode outputs logOutput inputs publicInputs constants layers) :=
  outside (by change some (76 : Framing.Byte) ≠ some 0; decide)
    (by change some (76 : Framing.Byte) ≠ some 1; decide)
    (SHAOracle.identifier_not_domain _ _ _ _ _ _ _ _ _ _)

theorem context_outside (domain : Bytes) (cells : ℕ) :
    ¬protocol (MdocIdentifiers.contextBytes domain cells) :=
  outside (by change some (112 : Framing.Byte) ≠ some 0; decide)
    (by change some (112 : Framing.Byte) ≠ some 1; decide)
    (SHAOracle.context_not_domain domain cells)

theorem joint_context_outside (binary prime : Digest) :
    ¬protocol (MdocIdentifiers.jointContextBytes binary prime) :=
  outside (by change some (112 : Framing.Byte) ≠ some 0; decide)
    (by change some (112 : Framing.Byte) ≠ some 1; decide)
    (SHAOracle.joint_context_not_domain binary prime)

theorem context_merge (outside inside : Bytes → Digest) (domain : Bytes) (cells : ℕ) :
    SHAOracle.merge protocol outside inside (MdocIdentifiers.contextBytes domain cells) =
      outside (MdocIdentifiers.contextBytes domain cells) :=
  SHAOracle.merge_outside protocol outside inside _ (context_outside domain cells)

theorem joint_context_merge (outside inside : Bytes → Digest) (binary prime : Digest) :
    SHAOracle.merge protocol outside inside (MdocIdentifiers.jointContextBytes binary prime) =
      outside (MdocIdentifiers.jointContextBytes binary prime) :=
  SHAOracle.merge_outside protocol outside inside _ (joint_context_outside binary prime)

theorem adapter_merge {F : Type} [Field F] (outside inside : Bytes → Digest) {d q : ℕ}
    (encode : F → Bytes) (shape : Adapter.Circuit.Shape d q) (inputs publicInputs : ℕ)
    (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ) (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) :
    MetadataIdentifiers.adapterId (SHAOracle.merge protocol outside inside) encode shape inputs publicInputs
      sources pads powers base masked targets =
      MetadataIdentifiers.adapterId outside encode shape inputs publicInputs sources pads powers base masked targets :=
  SHAOracle.merge_outside protocol outside inside _ (circuit_outside (F := F) _ _ _ _ _ _ _ _ _ _)

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
variable (bodyCodec : PrefixCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
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
    UsesOnly protocol (StrandAuthentication.replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output) := by
  apply complete _ _ _ _ _ _
  intro annotated
  exact ((indexed_check codec (fun input => protocol (merkleInput input)) leaf node _ _ _ _).map _).mapQueries
    merkleInput (fun _ member => member)

include leaf node in
theorem replay_merge (outside inside : Bytes → Digest)
    (output : RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)) :
    (StrandAuthentication.replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run
        (SHAOracle.merge protocol outside inside) =
      (StrandAuthentication.replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run inside :=
  (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput leaf node output).run_eq _ _
    (fun raw member => SHAOracle.merge_inside protocol outside inside raw member)

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : BoundedBytes capacity → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)

include leaf node in
theorem verify_merge (outside inside : Bytes → Digest)
    (output : RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)) :
    StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        (SHAOracle.merge protocol outside inside) merkleInput output =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec inside merkleInput output := by
  apply Eq.symm
  apply StrandAuthentication.verify_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw output inside _
  intro qa member
  exact (SHAOracle.merge_inside protocol outside inside qa.1
    ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput leaf node output).trace inside qa member)).trans
      (Tree.trace_sound _ inside qa member).symm

end Runtime

end LfzkV2.Current.StrandDomains
