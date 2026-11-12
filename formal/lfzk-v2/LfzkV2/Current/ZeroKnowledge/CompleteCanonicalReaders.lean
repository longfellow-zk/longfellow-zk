import LfzkV2.Current.ZeroKnowledge.OracleRuntime
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalPublic

/-! Canonical public statement and batching readers. These unchanged
runtime constructors are shared by the existing completeness proof and the
numbered-SHA coupling; importing them does not import an opening-programming
simulator or its privacy proof. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical

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

def batchingCoin (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R Cfg) (request : CanonicalRequest.Request shape binary.nPublic) (frontend : Body)
    (H : Point → Digest × C) : JointResponse.Coin (First).participant (Second).participant := by
  let point : Point := batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H
  let answer : C := (H point).2
  exact RuntimeVerifier.batchingDecoder binary prime P R Cfg batchingSamples answer



end LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
