import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
import LfzkV2.Current.StrandVerifier

/-! Honest completion passes the actual current indexed strand verifier. -/
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



/-- The canonical prover and verifier replay literally the same encoder. -/
theorem completion_encodings (request : (fmt.Request)) :
    RuntimeAdaptiveVerifier.encodings binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request = ((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) request).encoding :=
  CanonicalRuntime.encodings_eq binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) fmt
    (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes fmt configuration)
    binaryCount metadata request

theorem finish_responses
    (request : (fmt.Request)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → (PhysicalColumn binary prime))
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) :
    RuntimeVerifier.responses binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)
      ((finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA).proof = response := by
  change (BackendVerifier.responsesEquiv (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)) (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)) configuration.binaryField configuration.primeField
    configuration.rowDimension configuration.maskingDegree
    (RuntimeVerifier.productFits binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)))
      ((BackendVerifier.responsesEquiv (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)) (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration)) configuration.binaryField configuration.primeField
        configuration.rowDimension configuration.maskingDegree
        (RuntimeVerifier.productFits binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration))).symm response) = response
  exact Equiv.apply_symm_apply _ response

theorem finish_current_seal
    (request : (fmt.Request)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → (PhysicalColumn binary prime))
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) :
    StrandVerifier.finalSeal binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes fmt configuration binaryCount metadata) fmt.wire (fmt.body) roundSampler
      ((finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA) SHA =
      ((finish binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler) request frontend response indices columns opening SHA).proof.finalSeal := by
  have valid := finish_valid binary prime binaryNodes primeNodes fmt configuration
    binaryCount metadata roundSampler request frontend response indices columns opening SHA
  rw [StrandCompletion.Valid,TranscriptV2.StrandVerifier.sealValid_iff] at valid
  unfold StrandVerifier.finalSeal StrandVerifier.finalSealAddress
  rw [RuntimeAdaptiveVerifier.finalSealPoint_eq,completion_encodings]
  exact valid

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
