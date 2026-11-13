import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend

/-! Exact backend privacy at the actual canonical SHA opening reader.
The statement and all batching scalars are fixed by the preceding frontend.
Only the reader of the two complete H/Z responses is adaptive. No oracle
answer, opening set, or reader state is independently refreshed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits blocks : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Masks" => Backend.JointMasks binaryNodes primeNodes binary.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Cells" => Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
  Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265

/-- The actual witness-bearing backend, using the same canonical parser,
batching round, complete response payloads and physical opening reader. -/
def respondHonest (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (cells : Cells) (tape : Masks) :
    Option (BackendOutput binary prime) := do
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  let data ← CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount primeCount metadata request frontend H
  let coin := typedCoin binary prime binaryNodes primeNodes repr shape setup configuration
    (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
      binaryCount metadata batchingSamples request frontend H)
  pure (Backend.Adaptive.honest (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
    (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement) coin OrderedOpening.query
    (select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA)
    cells tape)

theorem respondHonest_congr_reads (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA SHA' : Strand.Oracle) (cells : Cells) (tape : Masks)
    (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells tape =
      respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA' cells tape := by
  simp only [respondHonest,
    logicalOracle_congr_reads binary repr shape setup roundSampler configuration.fallback SHA SHA' agree,
    select_congr_reads binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend SHA SHA' agree]

theorem respondHonest_congr (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA SHA' : Strand.Oracle) (cells : Cells) (tape : Masks)
    (agree : ∀ input : Strand.Input, SHA input.encode = SHA' input.encode) :
    respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells tape =
      respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA' cells tape := by
  simp only [respondHonest,
    logicalOracle_congr binary repr shape setup roundSampler configuration.fallback SHA SHA' agree,
    select_congr binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend SHA SHA' agree]

/-- Instantiate the existing response-adaptive equivalence at the actual
canonical statement, batching reader, and numbered SHA opening selector. -/
def responseCoupling (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (cells : Cells)
    (satisfied : ∀ data,
      CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata request frontend
        (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA) = some data →
      data.2.statement.1.Satisfies (Backend.logical cells.1) ∧
        data.2.statement.2.Satisfies (Backend.logical cells.2)) : Masks ≃ Masks :=
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  match parsed : CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
      binaryCount primeCount metadata request frontend H with
  | none => Equiv.refl _
  | some data =>
    let coin := typedCoin binary prime binaryNodes primeNodes repr shape setup configuration
      (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount metadata batchingSamples request frontend H)
    Backend.Adaptive.adaptiveCoupling (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
      Backend.Adaptive.Profile.reference 0 (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement) coin OrderedOpening.query
      (select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA)
      cells (typedStatement_holds binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement cells (satisfied data parsed))

theorem backend_view (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (cells : Cells)
    (satisfied : ∀ data,
      CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata request frontend
        (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA) = some data →
      data.2.statement.1.Satisfies (Backend.logical cells.1) ∧
        data.2.statement.2.Satisfies (Backend.logical cells.2)) (tape : Masks) :
    respond binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA
        (responseCoupling binary prime binaryNodes primeNodes repr shape setup configuration
          binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells satisfied tape) =
      respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells tape := by
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  cases parsed : CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
      binaryCount primeCount metadata request frontend H with
  | none =>
      dsimp only [H] at parsed
      simp only [respond,respondHonest,responseCoupling,parsed,Option.bind_eq_bind,Option.bind_none]
  | some data =>
      dsimp only [H] at parsed
      let coin := typedCoin binary prime binaryNodes primeNodes repr shape setup configuration
        (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
          binaryCount metadata batchingSamples request frontend H)
      let choose := select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend SHA
      have couplingEq :
          responseCoupling binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells satisfied =
          Backend.Adaptive.adaptiveCoupling (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
            Backend.Adaptive.Profile.reference 0 (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement) coin OrderedOpening.query choose cells (typedStatement_holds binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement cells (satisfied data parsed)) := by
        unfold responseCoupling
        dsimp only
        split
        · rename_i missing
          have impossible := missing.symm.trans parsed
          cases impossible
        · rename_i result selected
          have same : result = data := Option.some.inj (selected.symm.trans parsed)
          subst result
          rfl
      rw [couplingEq]
      simp only [respond,respondHonest,parsed,Option.bind_eq_bind,Option.bind_some]
      apply congrArg some
      exact Backend.Adaptive.adaptiveCoupling_view
        (r := 84) (w := 265) (n := 2443) (s := 12)
        (bw := ConcreteSetup.rows binary.cells)
        (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads))
        (BE := Fin configuration.countBinary) (NE := Fin configuration.countPrime)
        (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
        Backend.Adaptive.Profile.reference 0 (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement) coin OrderedOpening.query choose cells
        (typedStatement_holds binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement cells (satisfied data parsed)) tape

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
