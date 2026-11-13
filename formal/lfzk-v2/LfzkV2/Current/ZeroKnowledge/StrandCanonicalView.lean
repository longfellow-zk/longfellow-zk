import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBridge
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSchedule

/-! Literal public completion and raw observer view for the remaining
pointwise coupling. No private cell vector or witness enters this encoder. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
local notation "Masks" => Backend.JointMasks binaryNodes primeNodes binary.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

variable {blocks : ℕ}

def complete (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (prior : List (Bytes × Digest))
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (frontend : Body) (backend : Option (BackendOutput binary prime)) (SHA : Strand.Oracle) :
    Option (CanonicalRuntime.Output (Advice := Advice) binary shape) × Strand.Oracle :=
  match backend with
  | none | some (_,none) => (none,SHA)
  | some (responses,some ⟨indices,opened⟩) =>
    let runtimePublic := CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration
    let first := RuntimeVerifier.first binary prime P R runtimePublic
    let second := RuntimeVerifier.second binary prime P R runtimePublic
    let codec := MerkleWireCodec.codec first.participant second.participant repr
      configuration.binaryField configuration.primeField setup.jointContext (by decide : 2443 ≤ 2^64)
    let dec := MerkleWireCodec.decoders first.participant second.participant repr configuration.binaryField configuration.primeField
      setup.jointContext (by decide : 2443 ≤ 2^64)
    let Q := (OrderedOpening.query indices).coordinates
    let physical := openedColumns binary prime indices opened
    let columns := fun index : Q => leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration (physical index)
    let revealed := fun index : Q => nonces index.val
    if ∀ entry ∈ prior, ∀ index : Q,
        entry.1 ≠ codec.leafEnc ((index.val,revealed index),columns index) then
      let updated := StrandGhostMerkle.Tree.installOpened codec dec SHA Q revealed columns leaves
      let opening := StrandGhostMerkle.Tree.opening codec SHA leaves Q revealed
      (some (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend responses indices physical opening updated),updated)
    else (none,SHA)

variable {Context Observed : Type} {postQueries : ℕ}

def fullView (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (frontend : Body) (backend : Option (BackendOutput binary prime)) (SHA : Strand.Oracle) :=
  let result := complete binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
    request prior leaves nonces frontend backend SHA
  let later := (after result.1).run result.2
  ((context,prior),((result.1,later.1),later.2))

/-- The nonce-independent stage of canonical completion. The selector has
already read both complete H/Z responses. Authentication supplies only the
chosen columns and their nonces to the continuation. The raw oracle passed
here is the extension of the public non-leaf oracle at the hiding boundary. -/
def prepare (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (SHA : Strand.Oracle)
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries) :
    StrandGhostMerkle.Schedule.Prepared 2443 MerkleNonce
      (Leaf binary prime binaryNodes primeNodes repr shape setup configuration) Digest Bytes
      (Option (CanonicalRuntime.Output (Advice := Advice) binary shape) × Observed) postQueries :=
  match backend with
  | none | some (_,none) =>
      { opened := ∅
        finish := fun _ _ => (after none).map fun observed => (none,observed) }
  | some (responses,some ⟨indices,_⟩) =>
      { opened := (OrderedOpening.query indices).coordinates
        finish := fun columns opening =>
          let physical := fun index =>
            (leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration).symm (columns index)
          let output := finish binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount metadata roundSampler request frontend responses indices physical opening SHA
          (after (some output)).map fun observed => (some output,observed) }

/-- Leaf-only oracle programming preserves the entire prepared encoder.
All its private hash evaluations are strand nodes or indexed PRF blocks;
the later observer remains an explicit raw-query program. -/
theorem prepare_oracle_congr_reads (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (SHA SHA' : Strand.Oracle)
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    prepare binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend backend SHA after =
      prepare binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend backend SHA' after := by
  cases backend with
  | none => rfl
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => rfl
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          dsimp only [prepare]
          congr 1
          funext columns opening
          rw [finish_oracle_congr_reads binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount metadata roundSampler request frontend responses indices _ opening SHA SHA' agree]

theorem prepare_oracle_congr (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (SHA SHA' : Strand.Oracle)
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (agree : ∀ input : Strand.Input, SHA input.encode = SHA' input.encode) :
    prepare binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend backend SHA after =
      prepare binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend backend SHA' after := by
  cases backend with
  | none => rfl
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => rfl
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          dsimp only [prepare]
          congr 1
          funext columns opening
          rw [finish_oracle_congr binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount metadata roundSampler request frontend responses indices _ opening SHA SHA' agree]

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
