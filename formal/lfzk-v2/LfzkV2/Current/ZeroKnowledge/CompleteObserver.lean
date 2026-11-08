import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalCompletion
import LfzkV2.Current.ZeroKnowledge.CompletePublicBody
import LfzkV2.Current.ZeroKnowledge.MerkleRuntime
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment

/-! The backend hybrid's observer receives only public data: the frontend
body, both H/Z responses, the opened tuple columns and their authentication.
It constructs the current complete proof, programs the whole opening answer,
computes its final seal, and runs the original mixed post-proof observer.
Neither backend private masks nor unopened columns enter this constructor. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteObserver
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
local notation "Cfg" => CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R Cfg
local notation "Second" => RuntimeVerifier.second binary prime P R Cfg
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "Leaf" => (MerkleCompiler.Leaf B (ConcreteSetup.rows binary.cells) 0 ×
  MerkleCompiler.Leaf N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0)

theorem capacity (indices : Fin 84 ↪ Fin 2443)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opening : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    (CompletePublicBody.raw (First).participant (Second).participant indices
      (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) opening).frontier.length ≤
        OpeningBody.frontierCapacity g := by
  have bound := CompletePublicBody.raw_frontier_bound (First).participant (Second).participant indices
    (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) opening
  have fits : 84*(Heap.heapDepth 2443+1) ≤ OpeningBody.frontierCapacity g := by
    unfold OpeningBody.frontierCapacity
    rw [cfg.openings,cfg.columns]
    decide
  exact bound.trans fits

def body (indices : Fin 84 ↪ Fin 2443) (frontend : Body)
    (responses : JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opening : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest) : Body :=
  CompletePublicBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings { frontend with commitment := opening.rt }
    (CompleteVerifier.wireResponses binary prime binaryNodes primeNodes Cfg responses)
    (CompletePublicBody.raw (First).participant (Second).participant indices
      (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) opening)
    setup.jointContext (capacity binary prime binaryNodes primeNodes repr shape setup cfg indices columns opening)

/-- A public failed parse is propagated as `none`. On success the complete
encoder owns both the actual opening replacement and normal final seal. -/
def complete (request : Request) (indices : Fin 84 ↪ Fin 2443) (frontend : Body)
    (responses : JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opening : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest)
    (H : Point → Digest × C) (answer : Digest × C) : Option (Output × (Point → Digest × C)) := do
  let full := body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend responses columns opening
  let _ ← CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg
    binaryCount primeCount metadata request full H
  let result := OracleProgramming.programAndFinalize
    (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request)
    cfg.initialLink full H g.openingIndex answer
  pure (⟨request,result.1⟩,result.2)

variable {Observed : Type} {postM postT : ℕ}
variable (after : CanonicalRequest.Request shape binary.nPublic →
  Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.nPublic) (Digest × C) Observed postM postT)

def observe (request : Request)
    (prior : List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × C)))
    (indices : Fin 84 ↪ Fin 2443) (H : Point → Digest × C) (answer : Digest × C)
    (publicView : Body × JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (_labels : Fin (2*2443-1) → Digest)
    (opening : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    Merkle.RandomOracle.Tree Bytes Digest
      (Observer.View Bytes Digest Point (Digest × C) Request (Option Output) Observed) postM :=
  let completed := complete binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata
    request indices publicView.1 publicView.2 columns opening H answer
  let result : Option Output × (Point → Digest × C) :=
    match completed with | none => (none,H) | some result => (some result.1,result.2)
  (Observer.fixTranscript result.2 (after request result.1)).map fun later =>
    ⟨request,result.1,prior,later.1,later.2⟩

end LfzkV2.Current.ZeroKnowledge.CompleteObserver
