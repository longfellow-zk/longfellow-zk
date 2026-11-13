import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalReaders
import LfzkV2.Current.ZeroKnowledge.CompletePublicBody
import LfzkV2.Current.RuntimeVerifier
import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveProfile
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleDomains

/-! Public backend completion for the numbered runtime. Both H/Z responses
are constructed before the actual opening reader is run. The reader's result
selects the correction-normalized physical columns; its PRF row is never
resampled or programmed. Canonical completion receives only those columns,
their authentication and the actual public frontend body. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
abbrev PrimeField := ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
abbrev PhysicalColumn :=
  (Fin (ConcreteSetup.rows binary.cells+3) → B) ×
    (Fin (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)+3) → PrimeField)
local notation "Physical" => PhysicalColumn binary prime
abbrev ResponsePair (B : Type) [Field B] := Backend.Adaptive.Responses
  (B := B) (N := PrimeField) (r := 84) (w := 265) (s := 12)
local notation "Responses" => ResponsePair B
local notation "Masks" => Backend.JointMasks binaryNodes primeNodes binary.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

variable {blocks : ℕ}

def logicalOracle (sampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (fallback : C) (SHA : Strand.Oracle) : Point → Digest × C :=
  StrandVerifier.oracle (StrandRuntime.history (ProofBodyCodec.codec repr g)) sampler fallback SHA

omit [Fintype B] [DecidableEq B] in
theorem logicalOracle_congr_reads (sampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (fallback : C) (SHA SHA' : Strand.Oracle)
    (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    logicalOracle binary repr shape setup sampler fallback SHA =
      logicalOracle binary repr shape setup sampler fallback SHA' :=
  StrandReadWindow.Agree.oracle _ sampler fallback agree

omit [Fintype B] [DecidableEq B] in
theorem logicalOracle_congr (sampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (fallback : C) (SHA SHA' : Strand.Oracle)
    (agree : ∀ input : Strand.Input, SHA input.encode = SHA' input.encode) :
    logicalOracle binary repr shape setup sampler fallback SHA =
      logicalOracle binary repr shape setup sampler fallback SHA' :=
  StrandGhostMerkle.Domains.oracle_congr _ sampler fallback SHA SHA' agree


def responseBody (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (frontend : Body) (response : Responses) : Body :=
  let wire := RuntimeVerifier.wireResponses binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration) response
  { frontend with
    binaryBackend := { frontend.binaryBackend with response := wire.1 }
    primeBackend := { frontend.primeBackend with response := wire.2 } }

/-- Read the actual round stream after binding both complete response arrays.
Replay uses a dummy value after sampler failure only to finish locating
the rounds. Reject that replay before returning any opening. Each check
uses the same numbered oracle inputs as the original read. -/
def select (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (response : Responses) :
    Option (Fin 84 ↪ Fin 2443) :=
  let encoding := CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount metadata request
  let body := responseBody binary prime binaryNodes primeNodes repr shape setup configuration frontend response
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  let replay := (encoding.encoding.chain configuration.initialLink).point ⟨body,fun _ => 0⟩ H
  let history : Point → Strand.History := StrandRuntime.history (ProofBodyCodec.codec repr g)
  let point := replay g.openingIndex
  let node := history point
  if ∀ i : Fin g.openingIndex.val,
      TranscriptV2.StrandVerifier.sampled history roundSampler SHA (replay i.val) then
    let values := (roundSampler point).run fun counter => SHA (Strand.Input.prf node.id (SHA node.input.encode) counter).encode
    values.1.map configuration.sample
  else none

theorem select_congr_reads (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (SHA SHA' : Strand.Oracle)
    (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA =
      select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA' := by
  funext response
  have stream := StrandReadWindow.Agree.stream _ agree
  simp only [select,logicalOracle_congr_reads binary repr shape setup roundSampler configuration.fallback SHA SHA' agree,
    TranscriptV2.StrandVerifier.sampled,stream]

theorem select_congr (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (SHA SHA' : Strand.Oracle)
    (agree : ∀ input : Strand.Input, SHA input.encode = SHA' input.encode) :
    select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA =
      select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA' := by
  funext response
  have stream (node : Strand.History) :
      (fun counter => SHA (Strand.Input.prf node.id (SHA node.input.encode) counter).encode) =
        (fun counter => SHA' (Strand.Input.prf node.id (SHA' node.input.encode) counter).encode) := by
    funext counter
    rw [agree node.input,agree]
  simp only [select,logicalOracle_congr binary repr shape setup roundSampler configuration.fallback SHA SHA' agree,
    TranscriptV2.StrandVerifier.sampled,stream]

abbrev BackendOutput := Backend.Adaptive.JointOutput
  (B := B) (N := PrimeField) (w := 265) (bw := ConcreteSetup.rows binary.cells)
  (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)
  (OrderedOpening.query (n := 2443) (t := 84))


/-- Expose the fixed backend geometry at the canonical-reader boundary.
The public reader returns the existing participant-indexed statement; the
adaptive masking proof uses these same matrices with explicit dimensions. -/
def typedStatement (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (statement : JointResponse.Statement (RuntimeVerifier.first binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant) :
    LigeroFamily.ConstraintSystem B (ConcreteSetup.rows binary.cells) 0 265 (Fin configuration.countBinary) ×
      LigeroFamily.ConstraintSystem PrimeField
        (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0 265 (Fin configuration.countPrime) :=
  statement

/-- The type normalization preserves the existing statement-truth proof. -/
theorem typedStatement_holds (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (statement : JointResponse.Statement (RuntimeVerifier.first binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant)
    (cells : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (truth : statement.1.Satisfies (Backend.logical cells.1) ∧ statement.2.Satisfies (Backend.logical cells.2)) :
    (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration statement).1.Satisfies (Backend.logical cells.1) ∧
      (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration statement).2.Satisfies (Backend.logical cells.2) :=
  truth

/-- The batching reader supplies exactly these equation and row weights.
Give the masking proof the same values with explicit backend dimensions. -/
def typedCoin (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (coin : JointResponse.Coin (RuntimeVerifier.first binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime P R (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant) :
    RecursivePolygero.Local.Polygero.Coin B (Fin configuration.countBinary) (ConcreteSetup.rows binary.cells) 0 12 ×
      RecursivePolygero.Local.Polygero.Coin PrimeField (Fin configuration.countPrime)
        (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0 12 :=
  coin

/-- This sampler receives no logical cell vector or satisfying witness.
The actual public statement and batching answer are read from the frontend. -/
def respond (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (tape : Masks) :
    Option (BackendOutput binary prime) := do
  let H := logicalOracle binary repr shape setup roundSampler configuration.fallback SHA
  let data ← CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount primeCount metadata request frontend H
  let coin := typedCoin binary prime binaryNodes primeNodes repr shape setup configuration
    (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
      binaryCount metadata batchingSamples request frontend H)
  pure (Backend.Adaptive.simulate (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
    Backend.Adaptive.Profile.reference 0 (typedStatement binary prime binaryNodes primeNodes repr shape setup configuration data.2.statement) coin OrderedOpening.query
    (select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler request frontend SHA) tape)

theorem respond_congr_reads (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : Request) (frontend : Body) (SHA SHA' : Strand.Oracle) (tape : Masks)
    (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    respond binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA tape =
      respond binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA' tape := by
  simp only [respond,
    logicalOracle_congr_reads binary repr shape setup roundSampler configuration.fallback SHA SHA' agree,
    select_congr_reads binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
      roundSampler request frontend SHA SHA' agree]


/-- Actual physical rows u,m,witness,fstar are encoded using the same tuple
leaf equivalence as the runtime codec. Only the selected columns are read. -/
def openedColumns (indices : Fin 84 ↪ Fin 2443)
    (opened : Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads))
      (OrderedOpening.query indices)) :
    (OrderedOpening.query indices).coordinates → Physical :=
  fun index =>
    ((OpeningBody.leafEquiv B (ConcreteSetup.rows binary.cells)).symm (opened.1.1 index,opened.1.2 index),
      (OpeningBody.leafEquiv PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads))).symm
        (opened.2.1 index,opened.2.2 index))

abbrev Leaf (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce)) :=
  (RuntimeVerifier.Family binary prime P R
    (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).Leaf

def leafEquiv (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce)) :
    Physical ≃ Leaf binary prime binaryNodes primeNodes repr shape setup configuration :=
  let runtimePublic := CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration
  let first := RuntimeVerifier.first binary prime P R runtimePublic
  let second := RuntimeVerifier.second binary prime P R runtimePublic
  MerkleWireCodec.physicalLeafEquiv first.participant second.participant

/-- Order the physical rows and nonces for serialization. Merkle hashing
uses the same columns with their checked indices attached to the salts. -/
def rawOpening (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest) :=
  CompletePublicBody.ordered indices columns ⟨fun index => (opening.nonce index).2,opening.frontierValue⟩

omit [DecidableEq B] in
theorem capacity (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest) :
    (rawOpening binary prime indices columns opening).frontier.length ≤ OpeningBody.frontierCapacity g := by
  have bound := CompletePublicBody.ordered_frontier_bound indices columns
    ⟨fun index => (opening.nonce index).2,opening.frontierValue⟩
  have fits : 84*(Heap.heapDepth 2443+1) ≤ OpeningBody.frontierCapacity g := by
    unfold OpeningBody.frontierCapacity
    rw [configuration.openings,configuration.columns]
    decide
  exact bound.trans fits

/-- The complete body owns actual opened rows, nonces and frontier. The
mandatory final seal is computed by the same encoder as verifier replay. -/
def finish (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (response : Responses) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) : CanonicalRuntime.Output (Advice := Advice) binary shape :=
  let runtimePublic := CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration
  let raw := rawOpening binary prime indices columns opening
  let full := CompletePublicBody.fillRows frontend
    (RuntimeVerifier.wireResponses binary prime P R runtimePublic response)
    (fun side => match side with
      | .binary => fun row query => configuration.binaryField.symm
          ((raw.values (Fin.cast configuration.openings query)).1
            (Fin.cast (congrArg (·+3) configuration.binaryRows) row))
      | .prime => fun row query => configuration.primeField.symm
          ((raw.values (Fin.cast configuration.openings query)).2
            (Fin.cast (congrArg (·+3) configuration.primeRows) row)))
    (fun query => raw.nonce (Fin.cast configuration.openings query)) raw.frontier setup.jointContext
    (capacity binary prime binaryNodes primeNodes repr shape setup configuration indices columns opening)
  let encoding := CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount metadata request
  ⟨request,StrandCompletion.finish (ProofBodyCodec.codec repr g) encoding roundSampler configuration.fallback configuration.initialLink full SHA⟩

theorem finish_valid (configuration : RuntimeVerifier.Public (g := g) binary prime P R
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (response : Responses) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) :
    StrandCompletion.Valid (ProofBodyCodec.codec repr g)
      (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata request)
      roundSampler configuration.fallback configuration.initialLink
      (finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend response indices columns opening SHA).proof SHA := by
  exact StrandCompletion.finish_valid _ _ _ _ _ _ _

theorem finish_oracle_congr_reads (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (response : Responses) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA SHA' : Strand.Oracle) (agree : @StrandReadWindow.Agree Point (StrandRuntime.history (ProofBodyCodec.codec repr g)) SHA SHA') :
    finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend response indices columns opening SHA =
      finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend response indices columns opening SHA' := by
  unfold finish
  apply congrArg (fun proof => (⟨request,proof⟩ : CanonicalRuntime.Output (Advice := Advice) binary shape))
  exact StrandGhostMerkle.Domains.finish_congr_reads _ _ _ _ _ _ SHA SHA' agree

theorem finish_oracle_congr (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
    (request : Request) (frontend : Body) (response : Responses) (indices : Fin 84 ↪ Fin 2443)
    (columns : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Opening 2443 (OrderedOpening.query indices).coordinates (Fin 2443 × MerkleNonce) Digest)
    (SHA SHA' : Strand.Oracle) (agree : ∀ input : Strand.Input, SHA input.encode = SHA' input.encode) :
    finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend response indices columns opening SHA =
      finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend response indices columns opening SHA' := by
  unfold finish
  apply congrArg (fun proof => (⟨request,proof⟩ : CanonicalRuntime.Output (Advice := Advice) binary shape))
  exact StrandGhostMerkle.Domains.finish_congr _ _ _ _ _ _ SHA SHA' agree

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
