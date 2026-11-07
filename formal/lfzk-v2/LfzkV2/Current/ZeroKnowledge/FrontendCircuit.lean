import LfzkV2.Current.ZeroKnowledge.FrontendLayerCorrectness
import LfzkV2.Current.FrontendSchedule

/-! A simulator for the complete grouped layered frontend.  The recursion is
on the current public normalized schedule, so an entry and its following
assertions share a boundary, while input-only entries continue the last
combine answer.  There are no oracle calls for fragments or pad products.

The simulator draws the public payload directly.  Secret input tables occur
only in the inverse coupling used to prove its exact distribution. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F State Pad : Type} [Field F]

structure CircuitReader (F State : Type) [Field F] extends Reader F State where
  /-- Begin the single shared entry/assertion round at this layer. -/
  assertions : State → (count : ℕ) → (Fin count → F) × State
  /-- Continue the final combine answer, after its alpha coordinate. -/
  inputAssertions : State → (count : ℕ) → (Fin count → F) × State

abbrev CircuitTape : {out input : ℕ} → Layered.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .entry _ _ rest => CircuitTape rest
  | _, _, .layer (mid := mid) _ _ rest => LayerTape F mid × CircuitTape rest

def circuitPayloadEquiv : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    CircuitTape circuit ≃ Layered.Replay.Payload circuit
  | _, _, .input => Equiv.refl _
  | _, _, .entry _ _ rest => circuitPayloadEquiv rest
  | _, _, .layer (mid := mid) _ _ rest =>
      Equiv.prodCongr (payloadEquiv F mid) (circuitPayloadEquiv rest)

instance [Fintype F] {out input : ℕ} (circuit : Layered.Circuit F out input) :
    Fintype (CircuitTape circuit) := by
  induction circuit with
  | input => exact inferInstance
  | entry _ _ _ ih => exact ih
  | layer _ _ _ ih =>
      letI := ih
      exact inferInstance

instance [Fintype F] {out input : ℕ} (circuit : Layered.Circuit F out input) :
    Fintype (Layered.Replay.Payload circuit) :=
  Fintype.ofEquiv (CircuitTape circuit) (circuitPayloadEquiv circuit)

def simulateCircuit {out input : ℕ} (circuit : Layered.Circuit F out input)
    (coins : CircuitTape circuit) : Layered.Replay.Payload circuit :=
  circuitPayloadEquiv circuit coins

def inputCoefficients (reader : CircuitReader F State) (continuing : Bool)
    (state : State) (count : ℕ) : (Fin count → F) × State :=
  if continuing then reader.inputAssertions state count else reader.assertions state count

def setupLayer {n assertions : ℕ} (reader : CircuitReader F State)
    (state : State) (payload : LayerPayload F n) (beta : Fin assertions → F)
    (ids : Layered.Replay.LayerPads Pad n) : Layered.Circuit.LayerSetup Pad F n assertions :=
  let replay := readLayer reader.toReader state payload
  ⟨linearPlan ids,replay.point,replay.scale,replay.alpha,beta⟩

def readSetup (reader : CircuitReader F State) :
    {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    FrontendSchedule.Plan F circuit → Layered.Replay.PadPlan (Pad := Pad) circuit →
    Layered.Replay.Payload circuit → State → Bool → Layered.Circuit.Setup Pad circuit × State
  | _, _, _, .input, _, _, state, continuing =>
      ((),if continuing then state else (reader.assertions state 0).2)
  | _, _, _, .inputEntry (checks := checks) _ _, _, _, state, continuing =>
      let coefficients := inputCoefficients reader continuing state checks
      ((coefficients.1,()),coefficients.2)
  | _, _, _, .layer (assertions := assertions) _ tail, ids, payload, state, _ =>
      let coefficients := reader.assertions state assertions
      let replay := readLayer reader.toReader coefficients.2 payload.1
      let next := readSetup reader tail ids.2 payload.2 replay.state true
      ((setupLayer reader coefficients.2 payload.1 coefficients.1 ids.1,next.1),next.2)
  | _, _, _, .entryLayer (checks := checks) (assertions := assertions) _ _ _ tail,
      ids, payload, state, _ =>
      let coefficients := reader.assertions state (checks+assertions)
      let entering := fun i : Fin checks => coefficients.1 ⟨i.val,by omega⟩
      let beta := fun i : Fin assertions => coefficients.1 ⟨checks+i.val,by omega⟩
      let replay := readLayer reader.toReader coefficients.2 payload.1
      let next := readSetup reader tail ids.2 payload.2 replay.state true
      ((entering,(setupLayer reader coefficients.2 payload.1 beta ids.1,next.1)),next.2)

/-- Read the public payload at already replayed public challenges. -/
def messagesFromSetup : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Circuit.Setup Pad circuit → Layered.Replay.Payload circuit →
    Layered.Circuit.Messages Pad circuit
  | _, _, .input, _, _ => ()
  | _, _, .entry _ _ rest, setup, payload =>
      (setup.1,messagesFromSetup rest setup.2 payload)
  | _, _, .layer _ _ rest, setup, payload =>
      ({ roundMessages := payload.1.rounds, roundPads := setup.1.pads.round
         point := setup.1.point, beta := setup.1.beta, cross := payload.1.cross
         scale := setup.1.scale.val, messageA := payload.1.claimA, messageB := payload.1.claimB
         padA := setup.1.pads.a, padB := setup.1.pads.b
         padAB := setup.1.pads.ab, padD := setup.1.pads.d, alpha := setup.1.alpha },
       messagesFromSetup rest setup.2 payload.2)

/-- The adaptive bijection uses only previously public messages when choosing
the next fiber.  Later pads are never exposed to an earlier reader call. -/
def circuitEquiv (reader : CircuitReader F State) :
    {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    FrontendSchedule.Plan F circuit → (Cube input → F) → (Cube out → F) → State →
    CircuitTape circuit ≃ Layered.Replay.Payload circuit
  | _, _, _, .input, _, _, _ => Equiv.refl _
  | _, _, _, .inputEntry _ _, _, _, _ => Equiv.refl _
  | _, _, _, .layer (assertions := assertions) (body := body) (rest := rest)
      _ tail, w, weights, state =>
      let coefficients := reader.assertions state assertions
      let Q := body.effectiveQuadratic weights coefficients.1
      let L := body.effectiveLinear weights coefficients.1
      let head := layerEquiv reader.toReader (bindRightAffine Q L (rest.eval w))
        (rest.eval w) coefficients.2
      (Equiv.prodCongr head (Equiv.refl _)).trans (Equiv.prodCongrRight fun payload =>
        let replay := readLayer reader.toReader coefficients.2 payload
        circuitEquiv reader tail w (nextWeights Q (monomialWeights replay.point) replay.alpha)
          replay.state)
  | _, _, _, .entryLayer (checks := checks) (assertions := assertions) (body := body)
      (rest := rest) _ entry _ tail, w, weights, state =>
      let coefficients := reader.assertions state (checks+assertions)
      let entering := fun i : Fin checks => coefficients.1 ⟨i.val,by omega⟩
      let beta := fun i : Fin assertions => coefficients.1 ⟨checks+i.val,by omega⟩
      let previous := entry.weights weights entering
      let Q := body.effectiveQuadratic previous beta
      let L := body.effectiveLinear previous beta
      let head := layerEquiv reader.toReader (bindRightAffine Q L (rest.eval w))
        (rest.eval w) coefficients.2
      (Equiv.prodCongr head (Equiv.refl _)).trans (Equiv.prodCongrRight fun payload =>
        let replay := readLayer reader.toReader coefficients.2 payload
        circuitEquiv reader tail w (nextWeights Q (monomialWeights replay.point) replay.alpha)
          replay.state)

def realCircuit {out input : ℕ} {circuit : Layered.Circuit F out input}
    (reader : CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : State)
    (pads : CircuitTape circuit) : Layered.Replay.Payload circuit :=
  circuitEquiv reader plan w weights state pads

def circuitCoupling {out input : ℕ} {circuit : Layered.Circuit F out input}
    (reader : CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : State) :
    CircuitTape circuit ≃ CircuitTape circuit :=
  (circuitEquiv reader plan w weights state).trans (circuitPayloadEquiv circuit).symm

theorem circuitCoupling_view {out input : ℕ} {circuit : Layered.Circuit F out input}
    (reader : CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : State) (pads : CircuitTape circuit) :
    simulateCircuit circuit (circuitCoupling reader plan w weights state pads) =
      realCircuit reader plan w weights state pads :=
  (circuitPayloadEquiv circuit).apply_symm_apply _

theorem circuit_sameDistribution [Fintype F] {Observed : Type} [DecidableEq Observed]
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (reader : CircuitReader F State) (plan : FrontendSchedule.Plan F circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : State)
    (observe : Layered.Replay.Payload circuit → Observed) :
    LigeroFamily.SameDistribution
      (fun pads => observe (realCircuit reader plan w weights state pads))
      (fun coins => observe (simulateCircuit circuit coins)) := by
  apply LigeroFamily.sameDistribution_of_equiv (circuitCoupling reader plan w weights state)
  intro pads
  rw [circuitCoupling_view]

end LfzkV2.Current.ZeroKnowledge.Frontend
