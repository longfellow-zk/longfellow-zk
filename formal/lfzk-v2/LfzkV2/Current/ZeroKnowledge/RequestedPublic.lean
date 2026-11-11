import LfzkV2.Current.ZeroKnowledge.CompleteFrontendSetup
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest

/-! Public requests choose public circuit values, not circuit topology.
These constructors install the chosen binary bits and prime input vector
before running either frontend. No semantic correspondence assumption is
needed to connect those values to the request packets. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedSimulator
open Application ApplicationSetup ConcreteSetup Frontend
open scoped Classical

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)

def binaryFor (bits : Fin binary.nPublic → Bool) : BinaryCircuit B :=
  { binary with publicBits := bits }

def primeFor (inputs : Fin prime.nPublic → Adapter.Mdoc.P) : PrimePublic Adapter.Mdoc.P 768 :=
  { prime with publicInputs := inputs }

omit [Fintype B] [DecidableEq B] in
theorem binary_description (bits : Fin binary.nPublic → Bool) :
    (binaryFor binary bits).description = RuntimeAdaptive.binaryWithBits binary.description bits := rfl

theorem prime_inputs (inputs : Fin prime.nPublic → Adapter.Mdoc.P) :
    (primeFor prime inputs).publicInputs = inputs := rfl

variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic

def requestedBinary (request : Request) : BinaryCircuit B := binaryFor binary request.publicBits

def requestedPrime (request : Request) : PrimePublic Adapter.Mdoc.P 768 :=
  primeFor prime (fun i => request.primeInputs (Fin.cast primeCount.symm i))

def configuration (request : Request) : RuntimeVerifier.Public
    (g := MdocRuntime.geometry (requestedBinary binary prime primePlan shape request).description
      (requestedPrime binary prime primePlan shape primeCount request)
      (requestedBinary binary prime primePlan shape request).plan primePlan)
    (requestedBinary binary prime primePlan shape request).description
    (requestedPrime binary prime primePlan shape primeCount request)
    (backend binaryNodes binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
    (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce) := {
  card := cfg.card
  generator := cfg.generator
  quotientBound := cfg.quotientBound
  packingDegree := cfg.packingDegree
  binaryField := cfg.binaryField
  primeField := cfg.primeField
  binaryDecode := cfg.binaryDecode
  binaryNonzero := cfg.binaryNonzero
  primeDecode := cfg.primeDecode
  primeNonzero := cfg.primeNonzero
  conversion := cfg.conversion
  fingerprintBinary := cfg.fingerprintBinary
  fingerprintPrime := cfg.fingerprintPrime
  advice := cfg.advice
  fallback := cfg.fallback
  countBinary := cfg.countBinary
  countPrime := cfg.countPrime
  rowDimension := cfg.rowDimension
  maskingDegree := cfg.maskingDegree
  binaryRows := cfg.binaryRows
  primeRows := cfg.primeRows
  openings := cfg.openings
  columns := cfg.columns
  openingPositive := cfg.openingPositive
  context := cfg.context
  bindOnly := cfg.bindOnly
  openingBase := cfg.openingBase
  initialLink := cfg.initialLink
  root := cfg.root
  authenticationContext := cfg.authenticationContext
  bindSalt := cfg.bindSalt
  sample := cfg.sample }

def privateFrontendEquiv (request : Request) : CompleteHonest.Tape binary prime ≃
    CompleteHonest.Tape (requestedBinary binary prime primePlan shape request)
      (requestedPrime binary prime primePlan shape primeCount request) where
  toFun coins := ⟨coins.prime,coins.mask,coins.otp,coins.binary,coins.packing⟩
  invFun coins := ⟨coins.prime,coins.mask,coins.otp,coins.binary,coins.packing⟩
  left_inv _ := rfl
  right_inv _ := rfl

def publicFrontendEquiv (request : Request) : CompleteSimulation.Coins binary prime ≃
    CompleteSimulation.Coins (requestedBinary binary prime primePlan shape request)
      (requestedPrime binary prime primePlan shape primeCount request) where
  toFun coins := ⟨coins.fingerprints,coins.prime,coins.mu,coins.advice,coins.otpUnused,coins.binary,coins.packing⟩
  invFun coins := ⟨coins.fingerprints,coins.prime,coins.mu,coins.advice,coins.otpUnused,coins.binary,coins.packing⟩
  left_inv _ := rfl
  right_inv _ := rfl


end LfzkV2.Current.ZeroKnowledge.RequestedSimulator
