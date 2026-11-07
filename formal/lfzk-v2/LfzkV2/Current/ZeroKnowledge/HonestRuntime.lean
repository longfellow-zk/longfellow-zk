import LfzkV2.Current.ZeroKnowledge.CompleteFrontendSetup
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalCompletion
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest
import LfzkV2.Current.ZeroKnowledge.CompleteResponse
import LfzkV2.Current.ZeroKnowledge.BackendCells

/-! The complete honest current runtime, with causal private sampling.
Every logical cell, including the dedicated selector masks and derived pad
products, is fixed before the Merkle root and the fingerprint challenge.
The honest H/Z payload is independent of the opening set. The opening set
is read only after that full pair is bound; authentication and the ordinary
final seal are filled last. No simulation correction is used on this path. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestRuntime
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Family" => RuntimeVerifier.Family binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)

structure Tape where
  frontend : CompleteHonest.Tape binary prime
  selectors : CompleteHonest.Masks (B := B)
  backend : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads)
  nonces : Fin 2443 → Digest

def logical (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : Tape binary prime binaryNodes) :
    Backend.Cells B (rows binary.description.cells) 265 ×
      Backend.Cells N (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265 :=
  (BackendCells.tableau (CompleteHonest.binaryCells binary prime original tape.frontend
      ((finTwoArrowEquiv B).symm tape.selectors.1)),
    BackendCells.tableau (CompleteHonest.primeCells binary prime remaining tape.frontend
      ((finTwoArrowEquiv N).symm tape.selectors.2)))

def columns (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : Tape binary prime binaryNodes) : Fin 2443 →
      (RuntimeVerifier.Family binary.description prime P R Public).Leaf :=
  let cells := logical binary prime binaryNodes original remaining tape
  (RuntimeVerifier.Family binary.description prime P R Public).columnsEquiv
    ((Joint.Pair.oracleEquiv _ _).symm
      (PolygeroZk.oracle (Backend.profileGeometry binaryNodes) (Backend.messages cells.1) tape.backend.1,
        PolygeroZk.oracle (Backend.profileGeometry ConcreteSetup.primeNodes) (Backend.messages cells.2) tape.backend.2))

def commitment (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (HM : Bytes → Digest) (tape : Tape binary prime binaryNodes) : Digest :=
  root ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes
      ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM) 2443
    (fun i => (i,tape.nonces i)) (columns binary prime primePlan binaryNodes repr shape setup cfg original remaining tape)

def frontendAtRoot (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (request : Request) (root : Digest) (H : Point → Digest × C)
    (tape : CompleteHonest.Tape binary prime) (selectors : CompleteHonest.Masks (B := B)) :=
  CompleteHonest.run binary prime primePlan
    (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
    (CompleteSimulator.base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request root) H
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request root) original remaining tape selectors

def frontendResult (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (tape : Tape binary prime binaryNodes) :=
  frontendAtRoot binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining request
    (commitment binary prime primePlan binaryNodes repr shape setup cfg original remaining HM tape) H
    tape.frontend tape.selectors

def responseBody (frontend : Body)
    (responses : Response G B × Response G N) : Body :=
  { frontend with
    binaryBackend := { frontend.binaryBackend with response := responses.1 }
    primeBackend := { frontend.primeBackend with response := responses.2 } }

theorem frontier_capacity (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443)
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : Tape binary prime binaryNodes) :
    (CompleteBody.frontier (First).participant (Second).participant
      ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM)
      indices tape.nonces (columns binary prime primePlan binaryNodes repr shape setup cfg original remaining tape)).length ≤
        OpeningBody.frontierCapacity G := by
  have bound := CompleteOpening.raw_frontier_bound
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM)
    (fun i nonce => (i,nonce)) indices tape.nonces
    (columns binary prime primePlan binaryNodes repr shape setup cfg original remaining tape)
  have fits : 84*(Heap.heapDepth 2443+1) ≤ OpeningBody.frontierCapacity G := by
    unfold OpeningBody.frontierCapacity
    rw [cfg.openings,cfg.columns]
    decide
  exact bound.trans fits

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
    ConcreteSetup.primeNodes repr shape setup cfg))

/-- The complete honest prover binds both real responses before asking for
the shared opening set. It returns the original oracles unchanged. -/
def prove (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : Tape binary prime binaryNodes) (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C) :
    Option Output × ((Bytes → Digest) × (Point → Digest × C)) :=
  let root := commitment binary prime primePlan binaryNodes repr shape setup cfg original remaining HM tape
  let frontend := CompleteFrontendBody.rawBody binary prime primePlan root
    (frontendResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining request HM H tape)
  let completed : Option Output := do
    let data ← CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
      repr shape setup cfg binaryCount primeCount metadata request frontend H
    let coin := CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes
      repr shape setup cfg binaryCount metadata draw request frontend H
    let responses := CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
      (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
        (logical binary prime binaryNodes original remaining tape) data.2.statement coin tape.backend)
    let pending := responseBody binary prime primePlan frontend responses
    let e := CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes
      repr shape setup cfg binaryCount metadata request
    let indices := cfg.sample (H ((e.encoding.chain cfg.initialLink).point ⟨pending,fun _ => 0⟩ H (G).openingIndex.val)).2
    let full := CompleteBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings
      ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM)
      indices tape.nonces (columns binary prime primePlan binaryNodes repr shape setup cfg original remaining tape)
      frontend responses setup.jointContext
      (frontier_capacity binary prime primePlan binaryNodes repr shape setup cfg HM indices original remaining tape)
    pure ⟨request,OracleProgramming.finalize e cfg.initialLink full H⟩
  (completed,(HM,H))

variable {Observed : Type} {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

def experiment (original : Request → Fin binary.nPrivate → Bool) (remaining : Request → Fin prime.remaining → N)
    (tape : Tape binary prime binaryNodes) (HM : Bytes → Digest) (H : Point → Digest × C) :=
  Observer.experiment prior
    (fun request => prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      (original request) (remaining request) tape request) after HM H

end LfzkV2.Current.ZeroKnowledge.HonestRuntime
