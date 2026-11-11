import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
import LfzkV2.Current.ZeroKnowledge.IndexedCompleteOpening
import LfzkV2.Current.ZeroKnowledge.CompletionBody

/-! Completeness of the current canonical numbered-strand proof constructor. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical
attribute [local irreducible] Heap.frontierList
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

/-- The physical row encoder used by the actual prover is exactly the
inverse of the verifier's tuple decoder. -/
theorem finish_body_as_fill
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → (StrandCanonicalBackend.Leaf binary prime binaryNodes primeNodes repr shape setup configuration))
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) :
    ((finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i)) opening SHA).proof.body =
      CompletePublicBody.fill ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant configuration.binaryField configuration.primeField
        configuration.binaryRows configuration.primeRows configuration.openings frontend
        (CompleteVerifier.wireResponses binary prime binaryNodes primeNodes (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) response)
        (CompletePublicBody.ordered indices columns ⟨fun i => (opening.nonce i).2,opening.frontierValue⟩)
        setup.jointContext
        (capacity binary prime binaryNodes primeNodes repr shape setup configuration indices
          (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i)) opening) := rfl

theorem ordered_indexed_openCore {Column Enc : Type} {n t : ℕ}
    (scheme : Merkle.Indexed.Scheme (Fin n × MerkleNonce) Column Digest Enc)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → MerkleNonce)
    (columns : Fin n → Column) :
    CompletePublicBody.ordered indices (fun i => columns i.val)
      ⟨fun i => (Merkle.Indexed.openCore scheme n (OrderedOpening.query indices).coordinates
        (fun i => (i,nonces i)) columns).nonce i |>.2,
       (Merkle.Indexed.openCore scheme n (OrderedOpening.query indices).coordinates
        (fun i => (i,nonces i)) columns).frontierValue⟩ =
      IndexedCompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns := by
  have frontier :
      List.ofFn (fun i : Fin (Heap.frontierList n (OrderedOpening.query indices).coordinates).length =>
        Merkle.Indexed.commitLabels scheme n (fun j => (j,nonces j)) columns
          ((Heap.frontierList n (OrderedOpening.query indices).coordinates)[i.val]'i.isLt)) =
      (Heap.frontierList n (OrderedOpening.query indices).coordinates).map
        (Merkle.Indexed.commitLabels scheme n (fun j => (j,nonces j)) columns) :=
    List.ofFn_getElem_eq_map _ _
  unfold CompletePublicBody.ordered IndexedCompleteOpening.raw Merkle.Indexed.openCore
  simp only [OrderedOpening.order_val]
  rw [frontier]

/-- Replaying the actual physical row decoder recovers the exact honest
indexed opening; no decoded proof is supplied by the caller. -/
theorem finish_raw_honest {Enc : Type}
    (scheme : Merkle.Indexed.Scheme (Fin 2443 × MerkleNonce) (StrandCanonicalBackend.Leaf binary prime binaryNodes primeNodes repr shape setup configuration) Digest Enc)
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce) (columns : Fin 2443 → (StrandCanonicalBackend.Leaf binary prime binaryNodes primeNodes repr shape setup configuration)) (SHA : Strand.Oracle) :
    OpeningBody.raw ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant configuration.binaryField configuration.primeField
      configuration.binaryRows configuration.primeRows configuration.openings
      ((finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val))
        (Merkle.Indexed.openCore scheme 2443 (OrderedOpening.query indices).coordinates
          (fun i => (i,nonces i)) columns) SHA).proof =
      IndexedCompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns := by
  let output := (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val))
    (Merkle.Indexed.openCore scheme 2443 (OrderedOpening.query indices).coordinates
      (fun i => (i,nonces i)) columns) SHA
  change OpeningBody.raw _ _ _ _ _ _ _ ⟨output.proof.body,output.proof.finalSeal⟩ = _
  dsimp only [output]
  rw [finish_body_as_fill]
  apply Eq.trans ?_ (ordered_indexed_openCore scheme indices nonces columns)
  exact CompletePublicBody.raw_fill
    (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells)
      (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant
    (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells)
      (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant
    configuration.binaryField configuration.primeField configuration.binaryRows configuration.primeRows
    configuration.openings frontend
    (CompleteVerifier.wireResponses binary prime binaryNodes primeNodes
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) response)
    _ setup.jointContext _ _


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
