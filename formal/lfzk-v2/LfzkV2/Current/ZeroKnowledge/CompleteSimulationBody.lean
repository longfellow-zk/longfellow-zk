import LfzkV2.Current.ZeroKnowledge.CompleteBody
import LfzkV2.Current.ZeroKnowledge.CompleteBackend
import LfzkV2.Current.RuntimeVerifier
import LfzkV2.Current.ConcreteSetup

/-! The explicit backend simulation body and its wire encoding. These
constructors do not depend on verifier acceptance or statistical privacy
theorems. Their definitions remain shared by execution and its proof. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteVerifier

open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice Base Key C Enc Request : Type}
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Fin 2443 × Digest))
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Family" => RuntimeVerifier.Family binary prime P R cfg
variable (codec : Codec (Fin 2443 × Digest) (RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf Digest Enc)

def dummyColumns (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
    (CellLayout.Prime.cells prime.remaining prime.pads)) :
    Fin 2443 → (RuntimeVerifier.Family binary prime P R cfg).Leaf :=
  (RuntimeVerifier.Family binary prime P R cfg).columnsEquiv
    (CompleteBackend.familyOracle binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime tape)

def wireResponses (response : JointResponse.Response (First).participant (Second).participant) :
    Response g (fields .binary) × Response g (fields .prime) :=
  (BackendVerifier.responsesEquiv First Second cfg.binaryField cfg.primeField cfg.rowDimension cfg.maskingDegree
    (RuntimeVerifier.productFits binary prime P R cfg)).symm response

theorem frontier_capacity (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) :
    (CompleteBody.frontier (First).participant (Second).participant (codec.withOracle HM) indices nonces
      (dummyColumns binary prime binaryNodes primeNodes cfg tape)).length ≤ OpeningBody.frontierCapacity g := by
  have bound := CompleteOpening.raw_frontier_bound (codec.withOracle HM) (fun i nonce => (i,nonce))
    indices nonces (dummyColumns binary prime binaryNodes primeNodes cfg tape)
  have capacity : 84*(Heap.heapDepth 2443+1) ≤ OpeningBody.frontierCapacity g := by
    unfold OpeningBody.frontierCapacity
    rw [cfg.openings,cfg.columns]
    decide
  exact bound.trans capacity

/-- Fill the complete body with the explicit public correction and the
honest opening of the dummy zero-cell commitment. All private randomness
is supplied by the backend mask/nonce tapes; no witness is an input. -/
def simulatedBody (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body g fields Advice (OpeningBody.Authentication g)) (context : Digest) :
    Body g fields Advice (OpeningBody.Authentication g) :=
  CompleteBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings (codec.withOracle HM) indices nonces
    (dummyColumns binary prime binaryNodes primeNodes cfg tape)
    { frontend with commitment :=
        (root (codec.withOracle HM) 2443 (fun i => (i,nonces i))
          (dummyColumns binary prime binaryNodes primeNodes cfg tape)) }
    (wireResponses binary prime binaryNodes primeNodes cfg
      (CompleteBackend.responses binaryNodes primeNodes binary.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
        (OrderedOpening.query indices) statement coin tape)) context
    (frontier_capacity binary prime binaryNodes primeNodes cfg codec HM indices nonces tape)


end LfzkV2.Current.ZeroKnowledge.CompleteVerifier
