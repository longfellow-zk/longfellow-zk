import LfzkV2.Current.ZeroKnowledge.FrontendPads

/-! The payload bijection is tied to the existing honest layered prover,
including its derived product cells, and hence to the affine rows checked by
the current backend. No assertion of verifier acceptance is assumed here. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F State Pad : Type} [Field F]

theorem realLayer_messages_eq_honest_at {out n assertions : ℕ}
    (reader : Reader F State) (state : State)
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin assertions) F)
    (weights : Cube out → F) (wires : Cube n → F) (beta : Fin assertions → F)
    (tape : LayerTape F n) (ids : Layered.Replay.LayerPads Pad n) (pads : Pad → F)
    (hvalues : ∀ j, pads (layerAddress ids j) = padValues tape j) :
    let q := bindRightAffine (body.effectiveQuadratic weights beta) (body.effectiveLinear weights beta) wires
    let payload := realLayer reader q wires state tape
    let replay := readLayer reader state payload
    readMessages reader state payload beta ids =
      Linear.honestLayer body weights wires replay.point replay.scale.val replay.alpha beta
        (linearPlan ids) pads := by
  have ha : pads ids.a = tape.2.1 := hvalues (.inr 0)
  have hb : pads ids.b = tape.2.2.1 := hvalues (.inr 1)
  have hd : pads ids.d = tape.2.2.2 := hvalues (.inr 3)
  have hr : ∀ i, (⟨pads (ids.round i).1,pads (ids.round i).2⟩ : RoundPoly F) = tape.1 i := by
    intro i
    have h0 := hvalues (.inl (i,0))
    have h1 := hvalues (.inl (i,1))
    dsimp only [layerAddress,padValues] at h0 h1
    norm_num at h0 h1
    cases h : tape.1 i
    simp_all
  dsimp only
  let q := bindRightAffine (body.effectiveQuadratic weights beta) (body.effectiveLinear weights beta) wires
  have hround : (realLayer reader q wires state tape).rounds = fun i =>
      mask ((honestMessages q wires (readRounds reader state
        (realRounds reader q wires state tape.1)).1).get
          (i.cast (honestMessages_length _ _ _).symm)) (tape.1 i) := by
    funext i
    exact realRounds_eq_masked reader q wires state tape.1 i
  dsimp only [readMessages,Linear.honestLayer,linearPlan]
  simp only [ha,hb,hd,hr]
  congr 1

def SetupUses : {out input : ℕ} → (c : Layered.Circuit F out input) →
    Layered.Replay.PadPlan (Pad := Pad) c → Layered.Circuit.Setup Pad c → Prop
  | _, _, .input, _, _ => True
  | _, _, .entry _ _ rest, ids, setup => SetupUses rest ids setup.2
  | _, _, .layer _ _ rest, ids, setup =>
      setup.1.pads = linearPlan ids.1 ∧ SetupUses rest ids.2 setup.2

theorem assignment_honest {out input : ℕ} (circuit : Layered.Circuit F out input)
    (ids : Layered.Replay.PadPlan (Pad := Pad) circuit) (tape : CircuitTape circuit)
    (pads : Pad → F) (setup : Layered.Circuit.Setup Pad circuit)
    (hids : SetupUses circuit ids setup)
    (hvalues : Assignment circuit ids tape pads) :
    Layered.Circuit.HonestPads circuit setup pads := by
  induction circuit with
  | input => trivial
  | entry _ _ _ ih => exact ih ids tape setup.2 hids hvalues
  | layer _ _ _ ih =>
      obtain ⟨hhead,htail⟩ := hids
      obtain ⟨hvalues,htape⟩ := hvalues
      constructor
      · rw [hhead]
        have ha := hvalues (.inr 0)
        have hb := hvalues (.inr 1)
        have hab := hvalues (.inr 2)
        exact hab.trans (congrArg₂ (·*·) ha hb).symm
      · exact ih ids.2 tape.2 setup.2 htail htape

theorem readSetup_uses (reader : CircuitReader F State)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit)
    (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (state : State) (continuing : Bool) :
    SetupUses circuit ids (readSetup reader plan ids payload state continuing).1 := by
  induction plan generalizing state continuing with
  | input => trivial
  | inputEntry => trivial
  | layer _ _ ih => exact ⟨rfl,ih _ _ _ true⟩
  | entryLayer _ _ _ _ ih => exact ⟨rfl,ih _ _ _ true⟩

theorem realCircuit_honest (reader : CircuitReader F State)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit)
    (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (w : Cube input → F) (weights : Cube out → F) (state : State) (continuing : Bool)
    (tape : CircuitTape circuit) (pads : Pad → F)
    (hvalues : Assignment circuit ids tape pads) :
    let payload := realCircuit reader plan w weights state tape
    let setup := (readSetup reader plan ids payload state continuing).1
    messagesFromSetup circuit setup payload = Layered.Circuit.prove circuit setup w weights pads := by
  induction plan generalizing state continuing with
  | input => rfl
  | inputEntry => rfl
  | layer _ _ ih =>
      apply Prod.ext
      · exact realLayer_messages_eq_honest_at _ _ _ _ _ _ _ _ _ hvalues.1
      · exact ih _ _ _ _ true _ hvalues.2
  | entryLayer _ _ _ _ ih =>
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact realLayer_messages_eq_honest_at _ _ _ _ _ _ _ _ _ hvalues.1
        · exact ih _ _ _ _ true _ hvalues.2

/-- Recovering cells is a proof coupling, not an input to the simulator.
All its product cells are in the ordinary committed pad suffix. -/
def recoveredPadValues (reader : CircuitReader F State)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (w : Cube input → F)
    (weights : Cube out → F) (state : State) (payload : Layered.Replay.Payload circuit) :
    Fin (CellLayout.Pads.count circuit) → F :=
  circuitPadValues circuit ((circuitEquiv reader plan w weights state).symm payload)

theorem realCircuit_constraints (reader : CircuitReader F State)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (w : Cube input → F) (hvalid : circuit.Satisfies w) (state : State)
    (tape : CircuitTape circuit) (pads : Pad → F) (hvalues : Assignment circuit ids tape pads) :
    let payload := realCircuit reader plan w 0 state tape
    let setup := (readSetup reader plan ids payload state false).1
    let messages := messagesFromSetup circuit setup payload
    ∃ cs, Linear.buildConstraints (circuit.proof messages 0) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages 0) w) := by
  dsimp only
  let payload := realCircuit reader plan w 0 state tape
  let setup := (readSetup reader plan ids payload state false).1
  have hm := realCircuit_honest reader plan ids w 0 state false tape pads hvalues
  have hpads := assignment_honest circuit ids tape pads setup
    (readSetup_uses reader plan ids payload state false) hvalues
  have h := Layered.Circuit.prove_complete circuit setup w pads hvalid hpads
  dsimp only at h
  rw [← hm] at h
  exact h

/-- Every public simulated frontend payload has recovered honest pads which
satisfy the exact affine rows of the existing compiler.  The only semantic
premise is that the ordinary circuit statement is true. -/
theorem simulated_constraints (reader : CircuitReader F State)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (w : Cube input → F) (hvalid : circuit.Satisfies w)
    (state : State) (payload : Layered.Replay.Payload circuit) :
    let ids := CellLayout.Pads.plan circuit id
    let setup := (readSetup reader plan ids payload state false).1
    let messages := messagesFromSetup circuit setup payload
    let pads := recoveredPadValues reader plan w 0 state payload
    ∃ cs, Linear.buildConstraints (circuit.proof messages 0) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages 0) w) := by
  dsimp only
  let ids := CellLayout.Pads.plan circuit id
  let setup := (readSetup reader plan ids payload state false).1
  let tape := (circuitEquiv reader plan w 0 state).symm payload
  let pads := circuitPadValues circuit tape
  have hvalues := circuitPadValues_assignment circuit tape
  have hreal : realCircuit reader plan w 0 state tape = payload :=
    (circuitEquiv reader plan w 0 state).apply_symm_apply payload
  have hmessages := realCircuit_honest reader plan ids w 0 state false tape pads hvalues
  rw [hreal] at hmessages
  have hpads := assignment_honest circuit ids tape pads setup
    (readSetup_uses reader plan ids payload state false) hvalues
  obtain ⟨cs,hbuilt,hholds⟩ := Layered.Circuit.prove_complete circuit setup w pads hvalid hpads
  refine ⟨cs,?_,?_⟩
  · rw [hmessages]
    exact hbuilt
  · rw [hmessages]
    exact hholds

end LfzkV2.Current.ZeroKnowledge.Frontend
