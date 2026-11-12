import LfzkV2.Current.ZeroKnowledge.StrandHonestBackend
import LfzkV2.Current.ZeroKnowledge.StrandHonestAcceptance
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackendCompleteness

/-! Completeness at the operational honest-backend boundary. Successful
generation supplies the statement parse, actual responses and physical
reader success; ordinary statement truth supplies the algebraic proof. -/
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
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)

variable {blocks : ℕ}


variable (configuration : RuntimeVerifier.Public (g := g) binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (roundSampler : (QueryRuntime.Runtime.Point repr shape setup binary.nPublic) → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)



theorem respondHonest_accepts
    (primeCount : shape.primePublic = prime.nPublic)
    (draw : C → RuntimeVerifier.RawSamples binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (SHA : Strand.Oracle) (cells : (Backend.Cells B (ConcreteSetup.rows binary.cells) 265 × Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)) (tape : (CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads)))
    (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (opened : Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (OrderedOpening.query indices))
    (nonces : Fin 2443 → MerkleNonce)
    (truth : ∀ data,
      CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata request frontend
        (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA) = some data →
      data.2.statement.1.Satisfies (Backend.logical cells.1) ∧
        data.2.statement.2.Satisfies (Backend.logical cells.2))
    (generated : respondHonest binary prime binaryNodes primeNodes repr shape setup configuration binaryCount primeCount
      metadata roundSampler draw request frontend SHA cells tape = some (response,some ⟨indices,opened⟩))
    (committed : frontend.commitment = Merkle.Indexed.root (((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA) 2443
      (fun i => (i,nonces i))
      (fun i => (leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration) (committedColumns binary prime binaryNodes primeNodes cells tape i))) :
    let columns := fun i => (leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration) (committedColumns binary prime binaryNodes primeNodes cells tape i)
    let output := (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices
      (fun i => committedColumns binary prime binaryNodes primeNodes cells tape i.val)
      (Merkle.Indexed.openCore (((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA) 2443 (OrderedOpening.query indices).coordinates
        (fun i => (i,nonces i)) columns) SHA
    StrandVerifier.verify binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) (ProofBodyCodec.codec repr g) roundSampler
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
      draw (indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration) SHA id output = true := by
  obtain ⟨data,parsed,responseEq,selected⟩ := respondHonest_spec binary prime binaryNodes primeNodes repr shape setup
    configuration binaryCount metadata roundSampler primeCount draw request frontend SHA cells tape response indices opened generated
  let coin := CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount metadata draw request frontend
    (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA)
  have backend := honest_family_verifies binary prime binaryNodes primeNodes repr shape setup configuration
    cells tape data.2.statement coin (truth data parsed) (OrderedOpening.query indices)
  have backendResponse : ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).Verify
      ((Joint.Pair.statementEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm data.2.statement)
      (honestOracle binary prime binaryNodes primeNodes repr shape setup configuration cells tape)
      ((Joint.Pair.coinEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm coin)
      ((Joint.Pair.responseEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm response) (OrderedOpening.query indices) := by
    cases responseEq
    exact backend
  have rootEq : frontend.commitment = Merkle.Indexed.root (((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA) 2443
      (fun i => (i,nonces i))
      (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv (honestOracle binary prime binaryNodes primeNodes repr shape setup configuration cells tape)) := by
    rw [← honest_columns binary prime binaryNodes primeNodes repr shape setup configuration cells tape]
    exact committed
  have prefixZero : BackendPrefix.Zero (ConcreteSetup.backend binaryNodes binary.cells).participant response.1 ∧
      BackendPrefix.Zero (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)).participant response.2 := by
    rw [responseEq]
    constructor
    · intro i
      exact BackendPrefix.payload_random (Backend.profileGeometry binaryNodes)
        (Backend.profileGeometry binaryNodes).positive data.2.statement.1
        coin.1 (Backend.messages cells.1) tape.1 i
    · intro i
      exact BackendPrefix.payload_random (Backend.profileGeometry primeNodes)
        (Backend.profileGeometry primeNodes).positive data.2.statement.2
        coin.2 (Backend.messages cells.2) tape.2 i
  have accepted := finish_accepts binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
    roundSampler primeCount draw request frontend response indices nonces
    (honestOracle binary prime binaryNodes primeNodes repr shape setup configuration cells tape) SHA data parsed backendResponse selected prefixZero rootEq
  rw [← honest_columns binary prime binaryNodes primeNodes repr shape setup configuration cells tape] at accepted
  simpa only [Equiv.symm_apply_apply] using accepted

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
