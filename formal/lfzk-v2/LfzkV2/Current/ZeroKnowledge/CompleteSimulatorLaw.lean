import LfzkV2.Current.ZeroKnowledge.CompleteSimulator
import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling

/-! Exact frontend distribution laws for the complete simulator. Witnesses
occur only in the honest comparison and its change of private coins, never
in the public simulator constructor. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteSimulator
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH
open Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public
  (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)

local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def honestFrontend (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (backend : Tape (C := C) binary prime binaryNodes)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) :
    CompleteSimulation.RawResult binary prime primePlan (FingerprintPrefix.Key binary.description.nPublic)
      (CanonicalRequest.Base repr shape setup binary.description.nPublic) C :=
  let root := commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend
  CompleteHonest.run binary prime primePlan
    (samples binary prime primePlan binaryNodes repr shape setup cfg)
    (base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request root) H
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request root) original remaining tape masks

/-- Once the committed backend has been replaced by zero cells, its root
depends on no frontend coin. The exact current frontend change of coins
therefore preserves the completed canonical proof, programmed opening input,
resulting oracle and any subsequent observation together. -/
theorem frontend_sameDistribution {Observed : Type} [DecidableEq Observed]
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (backend : Tape (C := C) binary prime binaryNodes)
    (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted,
      FullCoupling.hashChecks binary prime primePlan
        (samples binary prime primePlan binaryNodes repr shape setup cfg)
        (base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request
          (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend)) H
        (FingerprintPrefix.context request (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend))
        original responses coin converted)
    (observe : Option (Output × (Point → Digest × C)) → Observed) :
    LigeroFamily.SameDistribution
      (fun coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B) =>
        observe (completeRaw binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          request HM H backend
          (honestFrontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
            original remaining request HM H backend coins.1 coins.2)))
      (fun coins : CompleteSimulation.Coins binary prime =>
        observe (simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          request HM H { backend with frontend := coins })) := by
  exact FullCoupling.sameDistribution binary prime primePlan
    (samples binary prime primePlan binaryNodes repr shape setup cfg)
    (base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request
      (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend)) H
    (FingerprintPrefix.context request (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend))
    original remaining pivotOne hash (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (fun raw => observe (completeRaw binary prime primePlan binaryNodes repr shape setup cfg
      binaryCount primeCount metadata draw request HM H backend raw))

variable {Observed : Type} {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

def zeroBackendHonestExperiment (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (backend : Tape (C := C) binary prime binaryNodes)
    (coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
    (HM : Bytes → Digest) (H : Point → Digest × C) :=
  let before := Observer.run HM H prior
  observeCompletion binary prime primePlan repr shape setup after before.1 before.2 HM H
    (completeRaw binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      before.1 HM H backend
      (honestFrontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
        original remaining before.1 HM H backend coins.1 coins.2))

/-- The last hybrid retains the observer's adaptive request and both whole
mixed traces. It changes no queried oracle answer except the already specified
opening replacement; the point and replacement are preserved jointly. -/
theorem frontend_experiment_sameDistribution [DecidableEq Observed]
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (backend : Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted,
      FullCoupling.hashChecks binary prime primePlan
        (samples binary prime primePlan binaryNodes repr shape setup cfg)
        (base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata (Observer.run HM H prior).1
          (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend)) H
        (FingerprintPrefix.context (Observer.run HM H prior).1
          (commitment binary prime primePlan binaryNodes repr shape setup cfg HM backend))
        original responses coin converted) :
    LigeroFamily.SameDistribution
      (fun coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B) =>
        zeroBackendHonestExperiment binary prime primePlan binaryNodes repr shape setup cfg
          binaryCount primeCount metadata draw prior after original remaining backend coins HM H)
      (fun coins : CompleteSimulation.Coins binary prime =>
        experiment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          prior after { backend with frontend := coins } HM H) := by
  have exactView := frontend_sameDistribution binary prime primePlan binaryNodes repr shape setup cfg
    binaryCount primeCount metadata draw original remaining (Observer.run HM H prior).1 HM H backend pivotOne hash
    (observeCompletion binary prime primePlan repr shape setup after
      (Observer.run HM H prior).1 (Observer.run HM H prior).2 HM H)
  convert exactView using 1
  · rfl
  · funext coins
    exact experiment_eq_observeCompletion binary prime primePlan binaryNodes repr shape setup cfg
      binaryCount primeCount metadata draw prior after { backend with frontend := coins } HM H

end LfzkV2.Current.ZeroKnowledge.CompleteSimulator
