import LfzkV2.Current.ZeroKnowledge.CompleteSimulator

/-! Public requests choose public circuit values, not circuit topology.
These constructors install the chosen binary bits and prime input vector
before running either frontend. No semantic correspondence assumption is
needed to connect those values to the request packets. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedSimulator
open Application ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

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
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic

def requestedBinary (request : Request) : BinaryCircuit B := binaryFor binary request.publicBits

def requestedPrime (request : Request) : PrimePublic Adapter.Mdoc.P 768 :=
  primeFor prime (fun i => request.primeInputs (Fin.cast primeCount.symm i))

def configuration (request : Request) : RuntimeVerifier.Public
    (g := CompleteSimulation.geometry (requestedBinary binary prime primePlan shape request)
      (requestedPrime binary prime primePlan shape primeCount request) primePlan)
    (requestedBinary binary prime primePlan shape request).description
    (requestedPrime binary prime primePlan shape primeCount request)
    (backend binaryNodes binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
    (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest) := {
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

def tape (request : Request) (coins : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    CompleteSimulator.Tape (C := C) (requestedBinary binary prime primePlan shape request)
      (requestedPrime binary prime primePlan shape primeCount request) binaryNodes where
  frontend := {
    fingerprints := coins.frontend.fingerprints
    prime := coins.frontend.prime
    mu := coins.frontend.mu
    advice := coins.frontend.advice
    otpUnused := coins.frontend.otpUnused
    binary := coins.frontend.binary
    packing := coins.frontend.packing }
  backend := coins.backend
  nonces := coins.nonces
  answer := coins.answer

/-- The partial body generated for a request, before backend responses and
terminal authentication are filled. Its public topology is unchanged. -/
def frontendBody (request : Request) (HM : Bytes → Digest)
    (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
    (coins : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    Current.Body (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B)
      MdocAdvice.Value (OpeningBody.Authentication (CompleteSimulation.geometry binary prime primePlan)) :=
  let b := requestedBinary binary prime primePlan shape request
  let p := requestedPrime binary prime primePlan shape primeCount request
  let config := configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := tape binary prime primePlan binaryNodes shape primeCount request coins
  CompleteFrontendBody.body b p primePlan
    (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM source)
    (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata request HM H source)

def tapeEquiv (request : Request) : CompleteSimulator.Tape (C := C) binary prime binaryNodes ≃
    CompleteSimulator.Tape (C := C) (requestedBinary binary prime primePlan shape request)
      (requestedPrime binary prime primePlan shape primeCount request) binaryNodes where
  toFun := tape binary prime primePlan binaryNodes shape primeCount request
  invFun coins := {
    frontend := {
      fingerprints := coins.frontend.fingerprints
      prime := coins.frontend.prime
      mu := coins.frontend.mu
      advice := coins.frontend.advice
      otpUnused := coins.frontend.otpUnused
      binary := coins.frontend.binary
      packing := coins.frontend.packing }
    backend := coins.backend
    nonces := coins.nonces
    answer := coins.answer }
  left_inv _ := rfl
  right_inv _ := rfl

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

omit [Fintype B] [DecidableEq B] in
theorem requested_publics (request : Request) :
    (requestedBinary binary prime primePlan shape request).publicBits = request.publicBits ∧
      (requestedPrime binary prime primePlan shape primeCount request).publicInputs =
        (fun i => request.primeInputs (Fin.cast primeCount.symm i)) := ⟨rfl,rfl⟩

omit [Fintype B] [DecidableEq B] in
theorem requested_geometry (request : Request) :
    CompleteSimulation.geometry (requestedBinary binary prime primePlan shape request)
        (requestedPrime binary prime primePlan shape primeCount request) primePlan =
      CompleteSimulation.geometry binary prime primePlan := rfl

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

/-- The selected public values are copied into the frontend structs before
simulation. The private tape and all circuit/field setup remain unchanged. -/
def forRequest (request : Request) (HM : Bytes → Digest)
    (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
    (coins : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :=
  CompleteSimulator.simulate
    (requestedBinary binary prime primePlan shape request)
    (requestedPrime binary prime primePlan shape primeCount request) primePlan binaryNodes repr shape setup
    (configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
    binaryCount primeCount metadata draw request HM H
    (tape binary prime primePlan binaryNodes shape primeCount request coins)

end LfzkV2.Current.ZeroKnowledge.RequestedSimulator
