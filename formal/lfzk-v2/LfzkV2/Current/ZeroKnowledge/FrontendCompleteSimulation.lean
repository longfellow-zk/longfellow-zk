import LfzkV2.Layered.Prover
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteWire
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteInputs
import LfzkV2.Current.ZeroKnowledge.FrontendPacking
import LfzkV2.Current.MdocRuntime

/-! The complete public frontend simulator in runtime order. It samples
fingerprint responses, every masked sumcheck message, the masked prime scalar,
canonical masked quotients and the packing response from public spaces. All
challenges come from the actual chained state; no witness is an input.

`base` is instantiated by `CompleteWire.canonicalBase`, with the runtime's
public metadata constructor. It receives only actual prefix writes and strict
prior answers. The output leaves A pending for the next backend boundary. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteSimulation
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]

abbrev P := Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)

abbrev Fields := MdocRuntime.fields B
abbrev State := CompleteTranscript.State (MdocRuntime.geometry binary.description prime binary.plan primePlan) (Fields (B := B))
  MdocAdvice.Value Key Base C
abbrev Fresh := ProtocolWrites.Fresh (MdocRuntime.geometry binary.description prime binary.plan primePlan) (Fields (B := B)) MdocAdvice.Value
abbrev Point := CompleteTranscript.Point (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
  (fields := Fields (B := B)) (Advice := MdocAdvice.Value)
  (Authentication := OpeningBody.Authentication (MdocRuntime.geometry binary.description prime binary.plan primePlan)) (Key := Key) (Base := Base)
abbrev BaseWriter := (i : Fin (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length) →
  (Fin (i.val+1) → Fresh binary prime primePlan) → (Fin i.val → C) → Base

structure Coins (binary : BinaryCircuit B) (prime : PrimePublic P 768) where
  fingerprints : Current.Fingerprints (Fields (B := B))
  prime : CircuitTape prime.circuit
  mu : P
  advice : MdocAdvice.Value
  /-- The six discarded high bits of each pad's two raw bytes. -/
  otpUnused : AdapterBits.Unused
  binary : CircuitTape binary.description.circuit
  packing : Packing.Tape (F := B) (0 : Fin 128)

def primeConstraints (messages : Layered.Circuit.Messages (Fin prime.pads) prime.circuit) :
    Linear.Constraints (Fin prime.pads) P :=
  (Linear.buildConstraints (prime.circuit.proof messages 0)).getD ⟨[],zeroClaim⟩

def primeRows (messages : Layered.Circuit.Messages (Fin prime.pads) prime.circuit) :
    List (LinearRow (Fin 768 ⊕ prime.Other) P) :=
  CellLayout.Prime.rows (primeConstraints prime messages)
    (fun i => prime.circuit.inputWeights messages 0 (prime.inputIndex (.inl i))) prime.publicInputs
    (fun i => prime.circuit.inputWeights messages 0 (prime.inputIndex (.inr i)))

/-- `split.rs::split_claim` of the same compiled constraints: the unbatched
layer rows on native pads and the split input equation. -/
def primeClaim (messages : Layered.Circuit.Messages (Fin prime.pads) prime.circuit) :
    Current.Prime.Claim (Fin 768) prime.Other P :=
  CellLayout.Prime.claim (primeConstraints prime messages)
    (fun i => prime.circuit.inputWeights messages 0 (prime.inputIndex (.inl i))) prime.publicInputs
    (fun i => prime.circuit.inputWeights messages 0 (prime.inputIndex (.inr i)))

structure Result (binary : BinaryCircuit B) (prime : PrimePublic P 768)
    (primePlan : FrontendSchedule.Plan P prime.circuit) (Key Base C : Type) where
  fingerprints : Current.Fingerprints (Fields (B := B))
  primePayload : Layered.Replay.Payload prime.circuit
  primeClaim : Current.Prime.Claim (Fin 768) prime.Other P
  eta : {x : P // x ≠ 0}
  mu : P
  alpha : Fin 2 → {x : P // x ≠ 0}
  advice : MdocAdvice.Value
  binaryPayload : Layered.Replay.Payload binary.description.circuit
  packing : Packing.Payload (ZMod 2) B (Fin 128)
  delta : Fin 128 → B
  state : State binary prime primePlan (Key := Key) (Base := Base) (C := C)

/-- A wire-facing view also represents rejected honest attempts. In that
view U has no presumed trace property; simulation proves its trace check. -/
structure RawResult (binary : BinaryCircuit B) (prime : PrimePublic P 768)
    (primePlan : FrontendSchedule.Plan P prime.circuit) (Key Base C : Type) where
  fingerprints : Current.Fingerprints (Fields (B := B))
  primePayload : Layered.Replay.Payload prime.circuit
  primeClaim : Current.Prime.Claim (Fin 768) prime.Other P
  eta : {x : P // x ≠ 0}
  mu : P
  alpha : Fin 2 → {x : P // x ≠ 0}
  advice : MdocAdvice.Value
  binaryPayload : Layered.Replay.Payload binary.description.circuit
  packing : (Fin 128 → B) × B
  delta : Fin 128 → B
  state : State binary prime primePlan (Key := Key) (Base := Base) (C := C)

def Result.raw (result : Result binary prime primePlan Key Base C) : RawResult binary prime primePlan Key Base C :=
  { fingerprints := result.fingerprints
    primePayload := result.primePayload
    primeClaim := result.primeClaim
    eta := result.eta
    mu := result.mu
    alpha := result.alpha
    advice := result.advice
    binaryPayload := result.binaryPayload
    packing := (fun i => (result.packing.1 i).val,result.packing.2)
    delta := result.delta
    state := result.state }

structure PrimePrefix (binary : BinaryCircuit B) (prime : PrimePublic P 768)
    (primePlan : FrontendSchedule.Plan P prime.circuit) (Key Base C : Type) where
  claim : Current.Prime.Claim (Fin 768) prime.Other P
  eta : {x : P // x ≠ 0}
  state : State binary prime primePlan (Key := Key) (Base := Base) (C := C)

structure ConversionPrefix (binary : BinaryCircuit B) (prime : PrimePublic P 768)
    (primePlan : FrontendSchedule.Plan P prime.circuit) (Key Base C : Type) where
  mu : P
  alpha : Fin 2 → {x : P // x ≠ 0}
  state : State binary prime primePlan (Key := Key) (Base := Base) (C := C)

variable (samples : ConcreteMetadata.Samples B C)
variable (base : BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def selectedState (context : Key) (fingerprints : Current.Fingerprints (Fields (B := B))) :
    State binary prime primePlan (Key := Key) (Base := Base) (C := C) :=
  let first := CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)
  CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some fingerprints }

def primePrefix (state : State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (payload : Layered.Replay.Payload prime.circuit) : PrimePrefix binary prime primePlan Key Base C :=
  let read := readSetup
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan prime.setup.plan payload state false
  let claim := primeClaim prime (messagesFromSetup prime.circuit read.1 payload)
  let rescaled := CompleteTranscript.step base H read.2
  ⟨claim,samples.primeNonzero rescaled.1,rescaled.2⟩

/-- Conversion is completed before masked advice is available to the reader. -/
def conversionPrefix (native : PrimePrefix binary prime primePlan Key Base C) (mu : P) :
    ConversionPrefix binary prime primePlan Key Base C :=
  let state := CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }
  let converted := CompleteTranscript.step base H state
  ⟨mu,samples.conversion converted.1,converted.2⟩

def powers (native : PrimePrefix binary prime primePlan Key Base C)
    (converted : ConversionPrefix binary prime primePlan Key Base C) (tree : Fin 2) (i : Fin 1024) : Bˣ :=
  MdocRuntime.generator binary.basis ^
    ((converted.alpha tree).val * Handoff.weights (maskBits := 256) native.claim.sharedWeights native.eta.val i).val

def targets (converted : ConversionPrefix binary prime primePlan Key Base C) (tree : Fin 2) : Bˣ :=
  MdocRuntime.generator binary.basis ^ ((converted.alpha tree).val*converted.mu).val

def generatorBase : Bˣ := MdocRuntime.generator binary.basis ^ (-(Current.Adapter.Mdoc.primeOrder : ℤ))

/-- The per-proof virtual definitions of the fixed binary circuit. -/
def entries (native : PrimePrefix binary prime primePlan Key Base C)
    (converted : ConversionPrefix binary prime primePlan Key Base C) (advice : MdocAdvice.Value) :
    Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B :=
  binary.description.entries (powers binary prime primePlan native converted) (generatorBase binary)
    (MdocAdvice.bits advice) (targets binary prime primePlan converted)

def binaryStart (converted : ConversionPrefix binary prime primePlan Key Base C) (advice : MdocAdvice.Value) :
    State binary prime primePlan (Key := Key) (Base := Base) (C := C) :=
  CompleteTranscript.bind converted.state fun writes => { writes with advice := some advice }

def binaryReplay (converted : ConversionPrefix binary prime primePlan Key Base C) (advice : MdocAdvice.Value)
    (payload : Layered.Replay.Payload binary.description.circuit) :
    Layered.Circuit.Setup (Fin binary.description.pads) binary.description.circuit ×
        State binary prime primePlan (Key := Key) (Base := Base) (C := C) :=
  readSetup (CompleteTranscript.reader .binary (Equiv.refl B) samples.binary samples.binaryNonzero base H)
    binary.plan binary.description.padPlan payload
    (binaryStart binary prime primePlan converted advice) false

def simulate
    (context : Key) (coins : Coins binary prime) : Result binary prime primePlan Key Base C :=
  let selected := selectedState binary prime primePlan samples base H context coins.fingerprints
  let primePayload := simulateCircuit prime.circuit coins.prime
  let native := primePrefix binary prime primePlan samples base H selected primePayload
  let converted := conversionPrefix binary prime primePlan samples base H native coins.mu
  let binaryRead := binaryReplay binary prime primePlan samples base H converted coins.advice
    (simulateCircuit binary.description.circuit coins.binary)
  let packing := Packing.simulate binary.basis 0 coins.packing
  let packingState := CompleteTranscript.bind binaryRead.2 fun writes =>
    { writes with packingU := some (fun i => (packing.1 i).val) }
  let packed := CompleteTranscript.step base H packingState
  let finished := CompleteTranscript.bind packed.2 fun writes => { writes with packingA := some packing.2 }
  { fingerprints := coins.fingerprints
    primePayload := primePayload
    primeClaim := native.claim
    eta := native.eta
    mu := coins.mu
    alpha := converted.alpha
    advice := coins.advice
    binaryPayload := simulateCircuit binary.description.circuit coins.binary
    packing := packing
    delta := fun i => samples.binary packed.1 i.val
    state := finished }

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteSimulation
