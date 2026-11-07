import LfzkV2.Current.ZeroKnowledge.FrontendReplay
import WitnessSelection.Algebra

/-! Joint hiding of selection responses and the later frontend.

The fingerprints cover the complete committed frontend vector, including
every later pad. Thus their responses and those pads cannot be treated as
independent after replay. The global inverse instead recovers all pads from
the simulated frontend at the selected responses, then recovers the two
dedicated masks. Coefficient vectors are fixed before either response; only
the later public reader is allowed to depend on them. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F State Index : Type} [Field F] [Fintype Index]

/-- A triangular change of coins: first expose the masked response, then
change the remaining secret coins in the fiber selected by that response.
This also handles simultaneous fingerprints in several committed fields. -/
def responsePayloadEquiv {Secret Masks Responses Payload : Type}
    (selection : Secret → Masks ≃ Responses) (payload : Responses → Secret ≃ Payload) :
    (Secret × Masks) ≃ (Responses × Payload) :=
  ((Equiv.prodCongrRight selection).trans (Equiv.prodComm _ _)).trans
    (Equiv.prodCongrRight payload)

def selectionPayloadEquiv {Secret Payload : Type}
    (coefficients : WitnessSelection.Coins F Index) (cells : Secret → Index → F)
    (payload : (F × F) → Secret ≃ Payload) :
    (Secret × (F × F)) ≃ ((F × F) × Payload) :=
  responsePayloadEquiv (fun secret => WitnessSelection.maskTranslation coefficients (cells secret)) payload

theorem selectionPayloadEquiv_response {Secret Payload : Type}
    (coefficients : WitnessSelection.Coins F Index) (cells : Secret → Index → F)
    (payload : (F × F) → Secret ≃ Payload) (secret : Secret) (masks : F × F) :
    (selectionPayloadEquiv coefficients cells payload (secret,masks)).1 =
      WitnessSelection.fingerprint coefficients (cells secret,masks) := rfl

theorem selectionPayloadEquiv_recovered {Secret Payload : Type}
    (coefficients : WitnessSelection.Coins F Index) (cells : Secret → Index → F)
    (payload : (F × F) → Secret ≃ Payload) (response : F × F) (message : Payload) :
    let recovered := (selectionPayloadEquiv coefficients cells payload).symm (response,message)
    recovered.1 = (payload response).symm message ∧
      WitnessSelection.fingerprint coefficients (cells recovered.1,recovered.2) = response := by
  constructor
  · rfl
  · exact (WitnessSelection.maskTranslation coefficients _).apply_symm_apply response

def selectedCircuitEquiv {out input : ℕ} {circuit : Layered.Circuit F out input}
    (coefficients : WitnessSelection.Coins F Index) (cells : CircuitTape circuit → Index → F)
    (reader : (F × F) → CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : (F × F) → State) :
    (CircuitTape circuit × (F × F)) ≃ ((F × F) × Layered.Replay.Payload circuit) :=
  selectionPayloadEquiv coefficients cells
    (fun response => circuitEquiv (reader response) plan w weights (state response))

/-- This is the public simulator: neither the field-cell function nor a
circuit witness is an argument. -/
def simulateSelectedCircuit {out input : ℕ} (circuit : Layered.Circuit F out input)
    (coins : (F × F) × CircuitTape circuit) : (F × F) × Layered.Replay.Payload circuit :=
  (coins.1,simulateCircuit circuit coins.2)

def selectedCircuitCoupling {out input : ℕ} {circuit : Layered.Circuit F out input}
    (coefficients : WitnessSelection.Coins F Index) (cells : CircuitTape circuit → Index → F)
    (reader : (F × F) → CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : (F × F) → State) :
    (CircuitTape circuit × (F × F)) ≃ ((F × F) × CircuitTape circuit) :=
  (selectedCircuitEquiv coefficients cells reader plan w weights state).trans
    (Equiv.prodCongr (Equiv.refl _) (circuitPayloadEquiv circuit).symm)

theorem selectedCircuitCoupling_view {out input : ℕ} {circuit : Layered.Circuit F out input}
    (coefficients : WitnessSelection.Coins F Index) (cells : CircuitTape circuit → Index → F)
    (reader : (F × F) → CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : (F × F) → State)
    (tape : CircuitTape circuit × (F × F)) :
    simulateSelectedCircuit circuit
        (selectedCircuitCoupling coefficients cells reader plan w weights state tape) =
      selectedCircuitEquiv coefficients cells reader plan w weights state tape := by
  apply Prod.ext
  · rfl
  · exact (circuitPayloadEquiv circuit).apply_symm_apply _

theorem selectedCircuit_sameDistribution [Fintype F] {Observed : Type} [DecidableEq Observed]
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (coefficients : WitnessSelection.Coins F Index) (cells : CircuitTape circuit → Index → F)
    (reader : (F × F) → CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : (F × F) → State)
    (observe : (F × F) × Layered.Replay.Payload circuit → Observed) :
    LigeroFamily.SameDistribution
      (fun tape => observe (selectedCircuitEquiv coefficients cells reader plan w weights state tape))
      (fun coins => observe (simulateSelectedCircuit circuit coins)) := by
  apply LigeroFamily.sameDistribution_of_equiv
    (selectedCircuitCoupling coefficients cells reader plan w weights state)
  intro tape
  rw [selectedCircuitCoupling_view]

/-- The same inverse supplies both the later frontend's honest pads and
the earlier fingerprint equations. There is no separate assumption that
fingerprinting excluded later masks or terminal cells. -/
theorem selectedCircuit_recovered_constraints
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (coefficients : WitnessSelection.Coins F Index) (cells : CircuitTape circuit → Index → F)
    (reader : (F × F) → CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (hvalid : circuit.Satisfies w) (state : (F × F) → State)
    (response : F × F) (payload : Layered.Replay.Payload circuit) :
    let recovered := (selectedCircuitEquiv coefficients cells reader plan w 0 state).symm (response,payload)
    let ids := CellLayout.Pads.plan circuit id
    let setup := (readSetup (reader response) plan ids payload (state response) false).1
    let messages := messagesFromSetup circuit setup payload
    WitnessSelection.fingerprint coefficients (cells recovered.1,recovered.2) = response ∧
      ∃ cs, Linear.buildConstraints (circuit.proof messages 0) = some cs ∧
        cs.Holds (circuitPadValues circuit recovered.1) (dot (circuit.inputWeights messages 0) w) := by
  constructor
  · exact (selectionPayloadEquiv_recovered coefficients cells _ response payload).2
  · exact simulated_constraints (reader response) plan w hvalid (state response) payload

section Joint
variable {B N BinaryIndex PrimeIndex : Type} [Field B] [Field N]
  [Fintype BinaryIndex] [Fintype PrimeIndex]

/-- The response is a pair in each field, sampled in the same pre-frontend
phase. The shared secret may contain the pads and packing randomness of
both participants; neither coefficient vector depends on any response. -/
def jointSelectionPayloadEquiv {Secret Payload : Type}
    (binaryCoefficients : WitnessSelection.Coins B BinaryIndex)
    (primeCoefficients : WitnessSelection.Coins N PrimeIndex)
    (binaryCells : Secret → BinaryIndex → B) (primeCells : Secret → PrimeIndex → N)
    (payload : ((B × B) × (N × N)) → Secret ≃ Payload) :
    (Secret × ((B × B) × (N × N))) ≃ (((B × B) × (N × N)) × Payload) :=
  responsePayloadEquiv (fun secret => Equiv.prodCongr
    (WitnessSelection.maskTranslation binaryCoefficients (binaryCells secret))
    (WitnessSelection.maskTranslation primeCoefficients (primeCells secret))) payload

theorem jointSelectionPayloadEquiv_recovered {Secret Payload : Type}
    (binaryCoefficients : WitnessSelection.Coins B BinaryIndex)
    (primeCoefficients : WitnessSelection.Coins N PrimeIndex)
    (binaryCells : Secret → BinaryIndex → B) (primeCells : Secret → PrimeIndex → N)
    (payload : ((B × B) × (N × N)) → Secret ≃ Payload)
    (response : (B × B) × (N × N)) (message : Payload) :
    let recovered := (jointSelectionPayloadEquiv binaryCoefficients primeCoefficients
      binaryCells primeCells payload).symm (response,message)
    recovered.1 = (payload response).symm message ∧
      WitnessSelection.fingerprint binaryCoefficients (binaryCells recovered.1,recovered.2.1) = response.1 ∧
      WitnessSelection.fingerprint primeCoefficients (primeCells recovered.1,recovered.2.2) = response.2 := by
  refine ⟨rfl,?_,?_⟩
  · exact (WitnessSelection.maskTranslation binaryCoefficients _).apply_symm_apply response.1
  · exact (WitnessSelection.maskTranslation primeCoefficients _).apply_symm_apply response.2
end Joint

end LfzkV2.Current.ZeroKnowledge.Frontend
