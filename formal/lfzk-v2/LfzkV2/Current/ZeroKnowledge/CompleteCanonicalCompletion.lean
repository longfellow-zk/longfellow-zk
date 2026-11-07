import LfzkV2.Current.ZeroKnowledge.CompleteSimulationBody
import LfzkV2.Current.ZeroKnowledge.OracleRuntime
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalPublic
import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.MerkleWireCodec

/-! Canonical public completion algorithms. The actual parser constructs
the authenticated statement, fills terminal data, programs one complete
opening answer and computes the normal final seal. Acceptance and privacy
proofs consume these definitions without being dependencies of them. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
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
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)

def earlier := CanonicalRuntime.earlier binary prime P R repr shape setup
  (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount metadata

def encoding (request : CanonicalRequest.Request shape binary.nPublic) :=
  OracleRuntime.bodyEncoding repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup
      (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount) metadata request

local notation "Cfg" => publicConfig binary prime binaryNodes primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R Cfg
local notation "Second" => RuntimeVerifier.second binary prime P R Cfg
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic

def body (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) : Body :=
  CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes Cfg
    (merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg)
    HM indices nonces tape data.2.statement coin frontend setup.jointContext

def simulate (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) (H : Point → Digest × C) (answer : Digest × C) :
    CanonicalRuntime.Output (Advice := Advice) binary shape × (Point → Digest × C) :=
  let full := body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend
  let result := OracleProgramming.programAndFinalize
    (encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request)
    cfg.initialLink full H g.openingIndex answer
  (⟨request,result.1⟩,result.2)

variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg))

/-- Commit the zero-cell backend before any frontend challenge. Terminal
fields here are placeholders; they do not enter the batching prefix. -/
def committedFrontend (HM : Bytes → Digest) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) (frontend : Body) : Body :=
  { frontend with commitment :=
      (root ((merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg).withOracle HM)
        2443 (fun i => (i,nonces i))
        (CompleteVerifier.dummyColumns binary prime binaryNodes primeNodes Cfg tape)) }

def batchingPoint (request : CanonicalRequest.Request shape binary.nPublic) (frontend : Body)
    (H : Point → Digest × C) : Point :=
  (BackendPath.parent
    (encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request).encoding
    cfg.initialLink ⟨frontend,fun _ => 0⟩ H g.batchingIndex).point

def statementAt (request : CanonicalRequest.Request shape binary.nPublic) (frontend : Body)
    (H : Point → Digest × C) : Option Data :=
  let point := batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H
  RuntimeAdaptive.statementAt binary prime P R Cfg (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
      (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount)
    point (point.priorAnswers H)

def batchingCoin (request : CanonicalRequest.Request shape binary.nPublic) (frontend : Body)
    (H : Point → Digest × C) : JointResponse.Coin (First).participant (Second).participant :=
  RuntimeVerifier.batchingDecoder binary prime P R Cfg draw
    (H (batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H)).2

/-- This total completion algorithm obtains the statement from the actual
public parser. It has no statement/correctness argument. Invalid frontend
encodings return `none`; the frontend correctness proof rules that out for
the complete public simulator. -/
def complete (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (frontend : Body) (H : Point → Digest × C) (answer : Digest × C) :
    Option (CanonicalRuntime.Output (Advice := Advice) binary shape × (Point → Digest × C)) := do
  let early := committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend
  let data ← statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata
    request early H
  pure (simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata
    request HM indices nonces tape data
    (batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request early H)
    frontend H answer)


end LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
