import LfzkV2.Current.ZeroKnowledge.FrontendSelection

/-! Frontend simulator regression and axiom audits. The example has a
nonlinear layer, a grouped entering-output check, and an input-only check
sharing the final combine answer. Public readers may depend on every prior
masked message, including the cross coefficient before its nonzero scale. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgeFrontend
open SumcheckV2
open ZeroKnowledge.Frontend
open scoped Classical
variable {F : Type} [Field F]

def adaptiveReader : CircuitReader F F where
  round state message := (state+message.c0,message.c1)
  terminal state cross := (if h : cross = 0 then ⟨1,one_ne_zero⟩ else ⟨cross,h⟩,state+cross)
  combine state factors := (state+factors.1*factors.2,state+factors.1+factors.2)
  assertions state count := (fun i : Fin count => state+(i.val:F),state+1)
  inputAssertions state count := (fun i : Fin count => state+(i.val:F),state)

def body : Native.CircuitLayer (Cube 0) (Cube 1) (Fin 1) F where
  quadratic := fun _ _ _ => 1
  linear := fun _ _ => 0
  constant := fun _ => 0
  assertions := fun _ => .quadratic (false,()) (true,())

def outputEntry : Layered.Entry (Cube 0) (Cube 0) 1 := ⟨fun _ => none,fun _ => ()⟩
def inputEntry : Layered.Entry (Cube 1) (Cube 1) 1 := ⟨some,fun _ => (false,())⟩

def circuit : Layered.Circuit F 0 1 :=
  .entry 1 outputEntry (.layer 1 body (.entry 1 inputEntry .input))

def plan : FrontendSchedule.Plan F (circuit (F := F)) :=
  .entryLayer ⟨[⟨0,1⟩],rfl⟩ outputEntry
    ⟨[⟨0,0,1,0⟩],rfl,by intro i; fin_cases i; rfl⟩
    (.inputEntry ⟨[⟨0,1⟩],rfl⟩ inputEntry)

theorem circuit_valid : (circuit (F := F)).Satisfies 0 := by
  simp [circuit,Layered.Circuit.Satisfies,Layered.Entry.residuals,Layered.Entry.previous,Layered.Circuit.eval,
    outputEntry,inputEntry,body,Native.CircuitLayer.outputs,Native.CircuitLayer.residuals,
    Native.AssertionTerm.residual,LfzkV2.quadratic,dot]
  exact ⟨Or.inl rfl,rfl⟩

example [Fintype F] {Observed : Type} [DecidableEq Observed]
    (observe : Layered.Replay.Payload (circuit (F := F)) → Observed) :
    LigeroFamily.SameDistribution
      (fun pads => observe (realCircuit adaptiveReader plan 0 0 0 pads))
      (fun coins => observe (simulateCircuit circuit coins)) :=
  circuit_sameDistribution adaptiveReader plan 0 0 0 observe

example (payload : Layered.Replay.Payload (circuit (F := F))) :
    let ids := CellLayout.Pads.plan circuit id
    let messages := messagesFromSetup circuit
      (readSetup adaptiveReader plan ids payload 0 false).1 payload
    let pads := recoveredPadValues adaptiveReader plan 0 0 0 payload
    ∃ cs, Linear.buildConstraints (circuit.proof messages 0) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages 0) 0) :=
  simulated_constraints adaptiveReader plan 0 circuit_valid 0 payload

/-- Scalar layers still mask the cross and both factors; the zero-round
polynomial vector is not a special terminal protocol. -/
example (q w : Cube 0 → F) (state : F) (messages : Fin 0 → RoundPoly F) :
    realRounds adaptiveReader.toReader q w state
      (recoverRounds adaptiveReader.toReader q w state messages) = messages :=
  real_recover _ _ _ _ _

#print axioms roundsEquiv
#print axioms layer_sameDistribution
#print axioms circuit_sameDistribution
#print axioms circuitPadValues_assignment
#print axioms realCircuit_honest
#print axioms simulated_constraints
#print axioms readSetup_answers_initial
#print axioms simulated_current_constraints
#print axioms selectionPayloadEquiv_recovered
#print axioms selectedCircuit_sameDistribution
#print axioms selectedCircuit_recovered_constraints
#print axioms jointSelectionPayloadEquiv_recovered
end LfzkV2.Current.Tests.ZeroKnowledgeFrontend
