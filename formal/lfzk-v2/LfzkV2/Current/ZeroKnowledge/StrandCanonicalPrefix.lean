import LfzkV2.Current.LegacyFormat
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
import LfzkV2.Current.ZeroKnowledge.StrandCompletenessPrefix

/-! Completeness of the current canonical numbered-strand proof constructor. -/
noncomputable section
set_option maxRecDepth 4096
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
variable (fmt : Format g fields Advice binary.nPublic)
variable {blocks : ℕ}


variable (configuration : RuntimeVerifier.Public (g := g) binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := fmt.Base)
  (Key := fmt.Key) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : fmt.binaryPublic = binary.nPublic)
variable (metadata : fmt.RequestMetadata C)
variable (roundSampler : (fmt.Point) → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)

theorem finish_point_before
    (request : (fmt.Request)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → (PhysicalColumn binary prime))
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) (H : (fmt.Point) → Digest × C) (index : ℕ)
    (before : index < g.openingIndex.val) :
    ((((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).point
      ((finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA).proof H index) =
      ((((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).point ⟨frontend,fun _ => 0⟩ H index) := by
  let output := (finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA
  let pending : Replay.Output g fields Advice (OpeningBody.Authentication g) := ⟨frontend,fun _ => 0⟩
  have same := congrArg (((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).input
    (ProofBodyReplay.replay_same_body ((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request) configuration.initialLink output.proof
      (CompleteTerminal.proof pending output.proof.body) rfl H index)
  exact same.trans (CompleteTerminal.point_before fmt (CanonicalRuntime.binaryRequest binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) fmt (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes fmt configuration) binaryCount) metadata request
    configuration.initialLink pending output.proof.body H index before)

theorem finish_point_responses
    (request : (fmt.Request)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → (PhysicalColumn binary prime))
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) (H : (fmt.Point) → Digest × C) (index : ℕ)
    (inside : index < g.roles.length) :
    ((((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).point
      ((finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA).proof H index) =
      ((((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).point
        ⟨responseBody binary prime binaryNodes primeNodes fmt configuration frontend response,fun _ => 0⟩ H index) := by
  let output := (finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA
  let pending : Replay.Output g fields Advice (OpeningBody.Authentication g) :=
    ⟨responseBody binary prime binaryNodes primeNodes fmt configuration frontend response,fun _ => 0⟩
  have same := congrArg (((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding.chain configuration.initialLink).input
    (ProofBodyReplay.replay_same_body ((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request) configuration.initialLink output.proof
      (CompleteTerminal.proof pending output.proof.body) rfl H index)
  exact same.trans (CompleteTerminal.point_same_responses fmt (CanonicalRuntime.binaryRequest binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) fmt (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes fmt configuration) binaryCount) metadata request
    configuration.initialLink pending output.proof.body rfl rfl H index inside)

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
