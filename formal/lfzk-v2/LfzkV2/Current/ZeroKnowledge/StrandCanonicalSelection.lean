import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend

/-! A successful actual response-bound opening reader entails successful
physical reads at every ordinary boundary and fixes the sampled columns. -/
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


theorem select_spec
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (response : (ResponsePair B)) (SHA : Strand.Oracle)
    (indices : Fin 84 ↪ Fin 2443)
    (selected : select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend SHA response = some indices) :
    let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
    let e := (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) request
    let pending : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice) :=
      ⟨responseBody binary prime binaryNodes primeNodes repr shape setup configuration frontend response,fun _ => 0⟩
    let points := (e.encoding.chain configuration.initialLink).point pending H
    (∀ i : Fin g.roles.length,
      TranscriptV2.StrandVerifier.sampled (StrandRuntime.history (ProofBodyCodec.codec repr g))
        roundSampler SHA (points i.val)) ∧
      configuration.sample (H (points g.openingIndex.val)).2 = indices := by
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  let pending : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice) :=
    ⟨responseBody binary prime binaryNodes primeNodes repr shape setup configuration frontend response,fun _ => 0⟩
  let points := (((CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata) request).encoding.chain configuration.initialLink).point pending H
  let history : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Strand.History :=
    StrandRuntime.history (ProofBodyCodec.codec repr g)
  let node := history (points g.openingIndex.val)
  let result := (roundSampler (points g.openingIndex.val)).run
    (fun counter => SHA (Strand.Input.prf node.id (SHA node.input.encode) counter).encode)
  change (∀ i : Fin g.roles.length,
    TranscriptV2.StrandVerifier.sampled history roundSampler SHA (points i.val)) ∧
    configuration.sample (H (points g.openingIndex.val)).2 = indices
  change (if ∀ i : Fin g.openingIndex.val,
    TranscriptV2.StrandVerifier.sampled history roundSampler SHA (points i.val)
    then result.1.map configuration.sample else none) = some indices at selected
  split_ifs at selected with earlierSucceeded
  · cases successful : result.1 with
    | none => simp only [successful,Option.map_none,reduceCtorEq] at selected
    | some value =>
      have chosen : configuration.sample value = indices := by
        simpa only [successful,Option.map_some,Option.some.injEq] using selected
      have opening : TranscriptV2.StrandVerifier.sampled history roundSampler SHA
          (points g.openingIndex.val) := by
        change result.1.isSome
        rw [successful]
        rfl
      have challenge : (H (points g.openingIndex.val)).2 = value := by
        change (TranscriptV2.StrandVerifier.oracle history roundSampler configuration.fallback SHA
          (points g.openingIndex.val)).2 = value
        rw [TranscriptV2.StrandVerifier.oracle_challenge]
        change result.1.getD configuration.fallback = value
        rw [successful]
        rfl
      refine ⟨?_,?_⟩
      · intro i
        by_cases earlier : i.val < g.openingIndex.val
        · exact earlierSucceeded ⟨i.val,earlier⟩
        · have last : i.val = g.openingIndex.val := by
            have := g.openingIndex_last
            have := i.isLt
            omega
          rw [last]
          exact opening
      · rw [challenge]
        exact chosen

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
