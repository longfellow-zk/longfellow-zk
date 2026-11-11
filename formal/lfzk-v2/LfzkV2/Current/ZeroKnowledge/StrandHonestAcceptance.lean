import LfzkV2.Current.ZeroKnowledge.StrandCanonicalAcceptance
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalCompleteness
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrefix
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalSelection
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalSchedule
import LfzkV2.Current.ZeroKnowledge.RuntimeDecodeCompleteness

/-! Completion from an actual response-bound physical read and honest
algebraic response, including indexed authentication and final seal. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical
attribute [local irreducible] Heap.frontierList OrderedOpening.query
  Merkle.Indexed.root Merkle.Indexed.openCore
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



/-- Successful physical reads and the ordinary affine backend equations
make the current honest completion pass the actual verifier. -/
theorem finish_accepts
    (primeCount : shape.primePublic = prime.nPublic)
    (draw : C → RuntimeVerifier.RawSamples binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce) (W : ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).Oracle) (SHA : Strand.Oracle)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)) (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)))
    (parsed : CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
      binaryCount primeCount metadata request frontend
      (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA) = some data)
    (backend : ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).Verify ((Joint.Pair.statementEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm data.2.statement)
      W ((Joint.Pair.coinEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm
        (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
          binaryCount metadata draw request frontend
          (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA)))
      ((Joint.Pair.responseEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm response) (OrderedOpening.query indices))
    (selected : select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend SHA response = some indices)
    (committed : frontend.commitment = Merkle.Indexed.root (((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA) 2443
      (fun i => (i,nonces i)) (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv W)) :
    let output := (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices
      (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv W i.val))
      (Merkle.Indexed.openCore (((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA) 2443 (OrderedOpening.query indices).coordinates
        (fun i => (i,nonces i)) (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv W)) SHA
    StrandVerifier.verify binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) (ProofBodyCodec.codec repr g) roundSampler
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
      draw (indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration) SHA id output = true := by
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  let scheme := ((indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration)).withOracle SHA
  let columns := ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv W
  let opening := Merkle.Indexed.openCore scheme 2443 (OrderedOpening.query indices).coordinates
    (fun i => (i,nonces i)) columns
  let output := (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler) request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val)) opening SHA
  have outputRequest : output.request = request := rfl
  let e := (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) request
  let parent := BackendPath.parent e.encoding configuration.initialLink output.proof H g.batchingIndex
  let coin := CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount metadata draw request frontend H
  let claim := IndexedCompleteOpening.claim scheme (fun i nonce => (i,nonce)) indices nonces columns
  let decoded : RuntimeVerifier.Decoded binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) :=
    ⟨data.1,data.2,claim,coin,OrderedOpening.query indices⟩
  have encoded := completion_encodings binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount metadata request
  have priorPoint : parent.point =
      CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount metadata request frontend H := by
    rw [BackendPath.parent_point,CompleteCanonicalVerifier.batchingPoint,BackendPath.parent_point]
    exact finish_point_before binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val)) opening SHA H
      g.batchingIndex.val (by rw [g.openingIndex_val]; omega)
  have statement : RuntimeAdaptive.statementAt binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
      parent.point (parent.point.priorAnswers H) = some data := by
    rw [priorPoint]
    exact parsed
  have sampleFacts := select_spec binary prime binaryNodes primeNodes repr shape setup configuration binaryCount
    metadata roundSampler request frontend response SHA indices selected
  have queryEq : configuration.sample
      (H ((RuntimeAdaptiveVerifier.encodings binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) request).chain
        configuration.initialLink |>.point output.proof H g.openingIndex.val)).2 = indices := by
    rw [encoded]
    rw [finish_point_responses binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val)) opening SHA H
      g.openingIndex.val g.openingIndex.isLt]
    exact sampleFacts.2
  have raw := finish_raw_honest binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
    roundSampler scheme request frontend response indices nonces columns SHA
  apply (StrandVerifier.verify_true_iff binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) (ProofBodyCodec.codec repr g) roundSampler
    (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
      (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
    draw (indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration) SHA id output).mpr
  refine ⟨decoded,?_,?_⟩
  · have chosenOnE : configuration.sample
        (H ((e.encoding.chain configuration.initialLink).point output.proof H g.openingIndex.val)).2 = indices := by
      simpa only [encoded] using queryEq
    have openingPart :
        let actual := RuntimeAdaptiveVerifier.encodings binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) output.request
        let chosen := ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).sample (H ((actual.chain ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).initialLink).point output.proof H g.openingIndex.val)).2
        OrderedOpening.decode (((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).bindSalt (actual.context output.proof)) chosen
          (OpeningBody.raw ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).binaryField ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).primeField
            ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).binaryRows ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).primeRows ((CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).openings output.proof) = some claim := by
      dsimp only
      rw [outputRequest,encoded]
      change OrderedOpening.decode (fun i nonce => (i,nonce))
        (configuration.sample (H ((e.encoding.chain configuration.initialLink).point output.proof H g.openingIndex.val)).2)
        (OpeningBody.raw ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant configuration.binaryField configuration.primeField
          configuration.binaryRows configuration.primeRows configuration.openings output.proof) = some claim
      rw [chosenOnE,raw]
      exact IndexedCompleteOpening.decode_raw scheme (fun i nonce => (i,nonce)) indices nonces columns
    have decodedEq := RuntimeAdaptiveVerifier.decode_of_parts binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
      draw output H data claim (by dsimp only; rw [outputRequest,encoded]; exact statement) openingPart
    have coinEq : RuntimeVerifier.batchingDecoder binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) draw (H parent.point).2 = coin := by
      rw [priorPoint]
      rfl
    dsimp only at decodedEq
    rw [outputRequest,encoded] at decodedEq
    change RuntimeAdaptiveVerifier.decode binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup configuration) primeCount)
      draw output H =
        some ⟨data.1,data.2,claim,RuntimeVerifier.batchingDecoder binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) draw (H parent.point).2,
          OrderedOpening.query (configuration.sample
            (H ((e.encoding.chain configuration.initialLink).point output.proof H g.openingIndex.val)).2)⟩ at decodedEq
    rw [chosenOnE,coinEq] at decodedEq
    exact decodedEq
  · change StrandVerifier.samplersSucceeded binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) (CompleteCanonicalVerifier.earlier binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) (ProofBodyCodec.codec repr g)
      roundSampler output SHA ∧ _
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      rw [RuntimeAdaptiveVerifier.point_eq,outputRequest,encoded]
      change TranscriptV2.StrandVerifier.sampled (StrandRuntime.history (ProofBodyCodec.codec repr g))
        roundSampler SHA ((e.encoding.chain configuration.initialLink).point output.proof H i.val)
      rw [finish_point_responses binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend response indices (fun j => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns j.val)) opening SHA H
        i.val i.isLt]
      exact sampleFacts.1 i
    · rfl
    · rfl
    · have accepted := (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).compiler configuration.openingPositive).indexed_complete_with_defaults
        scheme (fun i => (i,nonces i)) W
        ((Joint.Pair.statementEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm data.2.statement)
        ((Joint.Pair.coinEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm coin)
        ((Joint.Pair.responseEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm response)
        (OrderedOpening.query indices)
        ((((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).compiler_verify configuration.openingPositive _ W _ _ _).mpr backend)
      change (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).compiler configuration.openingPositive).AcceptsIndexed scheme _
        output.proof.body.commitment _ _ _ _
      rw [finish_responses]
      change (((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).compiler configuration.openingPositive).AcceptsIndexed scheme _ frontend.commitment _ _ _ _
      rw [committed]
      exact accepted
    · exact finish_current_seal binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
        roundSampler request frontend response indices (fun i => ((leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration)).symm (columns i.val)) opening SHA

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
