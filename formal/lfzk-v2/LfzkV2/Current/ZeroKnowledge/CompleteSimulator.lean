import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalCompletion
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendSetup
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody
import LfzkV2.Current.ZeroKnowledge.FrontendGlobalCoins
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment

/-! The complete public simulator, from independent frontend/backend
coins to current canonical proof bytes and the resulting oracle. The
application's circuit descriptions, public request and arithmetic setup
are inputs; private application values are absent from its interface.

Malformed public prefixes return `none`. The concrete frontend correctness
theorem discharges that branch for the simulator's own generated prefixes.
The observer sees the proof and its queried coordinates, never the internal
oracle tables used in the coupling. -/
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

structure Tape where
  frontend : CompleteSimulation.Coins binary prime
  backend : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads)
  nonces : Fin 2443 → Digest
  answer : Digest × C

def tapeEquiv : Tape (C := C) binary prime binaryNodes ≃
    CompleteSimulation.Coins binary prime ×
      (CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) × ((Fin 2443 → Digest) × (Digest × C))) where
  toFun tape := (tape.frontend,tape.backend,tape.nonces,tape.answer)
  invFun coin := ⟨coin.1,coin.2.1,coin.2.2.1,coin.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype C] : Fintype (Tape (C := C) binary prime binaryNodes) :=
  letI : Fintype (CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) := Fintype.ofFinite _
  Fintype.ofEquiv _ (tapeEquiv binary prime binaryNodes).symm

def commitment (HM : Bytes → Digest)
    (tape : Tape (C := C) binary prime binaryNodes) : Digest :=
  root ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes
    ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM) 2443
    (fun i => (i,tape.nonces i))
    (CompleteVerifier.dummyColumns binary.description prime binaryNodes ConcreteSetup.primeNodes Public tape.backend)

def frontendResult (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (tape : Tape (C := C) binary prime binaryNodes) :
    CompleteSimulation.Result binary prime primePlan (FingerprintPrefix.Key binary.description.nPublic)
      (CanonicalRequest.Base repr shape setup binary.description.nPublic) C :=
  let root := commitment binary prime primePlan binaryNodes repr shape setup cfg HM tape
  CompleteSimulation.simulate binary prime primePlan
    (samples binary prime primePlan binaryNodes repr shape setup cfg)
    (base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request root) H
    (FingerprintPrefix.context request root) tape.frontend

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def completeRaw (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (tape : Tape (C := C) binary prime binaryNodes)
    (raw : CompleteSimulation.RawResult binary prime primePlan
      (FingerprintPrefix.Key binary.description.nPublic)
      (CanonicalRequest.Base repr shape setup binary.description.nPublic) C) :
    Option (Output × (Point → Digest × C)) :=
  let frontend := CompleteFrontendBody.rawBody binary prime primePlan
    (commitment binary prime primePlan binaryNodes repr shape setup cfg HM tape)
    raw
  CompleteCanonicalVerifier.complete binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata draw request HM (cfg.sample tape.answer.2)
    tape.nonces tape.backend frontend H tape.answer

/-- All frontend messages, affine rows, backend correction, ordered Merkle
authentication and the final seal are computed here from public values and
independent private coins. The statement is parsed, not supplied. -/
def simulate (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (tape : Tape (C := C) binary prime binaryNodes) : Option (Output × (Point → Digest × C)) :=
  completeRaw binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    request HM H tape
    (frontendResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM H tape).raw

/-- The full observer receives the updated transcript oracle on success;
the original table is only an internal source of simulator randomness. -/
def prove (tape : Tape (C := C) binary prime binaryNodes) (request : Request)
    (HM : Bytes → Digest) (H : Point → Digest × C) :
    Option Output × ((Bytes → Digest) × (Point → Digest × C)) :=
  match simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape with
  | none => (none,(HM,H))
  | some result => (some result.1,(HM,result.2))

variable {Observed : Type} {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

def observeCompletion (request : Request)
    (before : List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × C)))
    (HM : Bytes → Digest) (H : Point → Digest × C)
    (completed : Option (Output × (Point → Digest × C))) :
    Observer.View Bytes Digest Point (Digest × C) Request (Option Output) Observed :=
  let result : Option Output × (Point → Digest × C) :=
    match completed with | none => (none,H) | some result => (some result.1,result.2)
  let later := Observer.run HM result.2 (after request result.1)
  ⟨request,result.1,before,later.1,later.2⟩

def experiment (tape : Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :=
  Observer.experiment prior
    (prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape)
    after HM H

theorem experiment_eq_observeCompletion (tape : Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :
    experiment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw prior after
        tape HM H =
      observeCompletion binary prime primePlan repr shape setup after
        (Observer.run HM H prior).1 (Observer.run HM H prior).2 HM H
        (simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          (Observer.run HM H prior).1 HM H tape) := by
  unfold experiment Observer.experiment prove observeCompletion
  dsimp only
  cases simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (Observer.run HM H prior).1 HM H tape <;> rfl

end LfzkV2.Current.ZeroKnowledge.CompleteSimulator
