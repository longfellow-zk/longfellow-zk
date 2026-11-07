import LfzkV2.Current.ZeroKnowledge.FrontendRounds

/-! Joint privacy of every message at one current sumcheck layer.  The
simulator samples two coefficients per round, the cross coefficient, then
the two masked factors. Challenge sampling is replayed through the public
reader at the same boundaries. The product pad is derived from its two
fresh factors and remains part of the secret commitment coupling. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical

variable {F State : Type} [Field F] {n : ℕ}

abbrev LayerTape (F : Type) (n : ℕ) := (Fin n → RoundPoly F) × (F × F × F)
abbrev LayerPayload := Layered.Replay.LayerPayload

def payloadEquiv (F : Type) (n : ℕ) : LayerTape F n ≃ LayerPayload F n where
  toFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
  invFun p := (p.rounds,p.cross,p.claimA,p.claimB)
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype F] : Fintype (LayerPayload F n) :=
  Fintype.ofEquiv (LayerTape F n) (payloadEquiv F n)

def terminalEquiv (reader : Reader F State) (q w : Cube n → F) (state : State)
    (messages : Fin n → RoundPoly F) : (F × F × F) ≃ (F × F × F) :=
  let rounds := readRounds reader state messages
  LinearTerminal.adaptiveMaskingEquiv (evaluate w rounds.1) (evaluate q rounds.1)
    (fun cross => (reader.terminal rounds.2 cross).1)

def layerEquiv (reader : Reader F State) (q w : Cube n → F) (state : State) :
    LayerTape F n ≃ LayerPayload F n :=
  ((Equiv.prodCongr (roundsEquiv reader q w state) (Equiv.refl _)).trans
    (Equiv.prodCongrRight (terminalEquiv reader q w state))).trans (payloadEquiv F n)

def simulateLayer (coins : LayerTape F n) : LayerPayload F n := payloadEquiv F n coins

def realLayer (reader : Reader F State) (q w : Cube n → F) (state : State)
    (pads : LayerTape F n) : LayerPayload F n := layerEquiv reader q w state pads

structure LayerRead (F State : Type) [Field F] (n : ℕ) where
  point : Fin n → F
  scale : {r : F // r ≠ 0}
  alpha : F
  state : State

/-- There is no secret input to replay, and no message between the two
masked factors. In particular alpha follows both factors, not just one. -/
def readLayer (reader : Reader F State) (state : State) (payload : LayerPayload F n) :
    LayerRead F State n :=
  let rounds := readRounds reader state payload.rounds
  let terminal := reader.terminal rounds.2 payload.cross
  let combine := reader.combine terminal.2 (payload.claimA,payload.claimB)
  ⟨rounds.1,terminal.1,combine.1,combine.2⟩

theorem realLayer_rounds (reader : Reader F State) (q w : Cube n → F) (state : State)
    (pads : LayerTape F n) : (realLayer reader q w state pads).rounds =
      realRounds reader q w state pads.1 := rfl

theorem realLayer_terminal (reader : Reader F State) (q w : Cube n → F) (state : State)
    (pads : LayerTape F n) :
    let payload := realLayer reader q w state pads
    let rounds := readRounds reader state payload.rounds
    (payload.cross,payload.claimA,payload.claimB) =
      LinearTerminal.adaptiveHonestMessages (evaluate w rounds.1) (evaluate q rounds.1)
        (fun cross => (reader.terminal rounds.2 cross).1) pads.2 := rfl

/-- Both the round masking and terminal masking are one global bijection.
The simulator is the witness-free representation map `simulateLayer`. -/
def layerCoupling (reader : Reader F State) (q w : Cube n → F) (state : State) :
    LayerTape F n ≃ LayerTape F n :=
  (layerEquiv reader q w state).trans (payloadEquiv F n).symm

theorem layerCoupling_view (reader : Reader F State) (q w : Cube n → F) (state : State)
    (pads : LayerTape F n) :
    simulateLayer (layerCoupling reader q w state pads) = realLayer reader q w state pads := by
  exact (payloadEquiv F n).apply_symm_apply _

theorem layer_sameDistribution [Fintype F] {Observed : Type} [DecidableEq Observed]
    (reader : Reader F State) (q w : Cube n → F) (state : State)
    (observe : LayerPayload F n → Observed) :
    LigeroFamily.SameDistribution
      (fun pads => observe (realLayer reader q w state pads))
      (fun coins => observe (simulateLayer coins)) := by
  apply LigeroFamily.sameDistribution_of_equiv (layerCoupling reader q w state)
  intro pads
  rw [layerCoupling_view]

abbrev LayerPad (n : ℕ) := (Fin n × Fin 2) ⊕ Fin 4

def layerPlan (n : ℕ) : Layered.Replay.LayerPads (LayerPad n) n where
  round i := (.inl (i,0),.inl (i,1))
  a := .inr 0
  b := .inr 1
  ab := .inr 2
  d := .inr 3

def padValues (pads : LayerTape F n) : LayerPad n → F
  | .inl (i,j) => if j = 0 then (pads.1 i).c0 else (pads.1 i).c1
  | .inr j => ![pads.2.1,pads.2.2.1,pads.2.1*pads.2.2.1,pads.2.2.2] j

@[simp] theorem padValues_a (pads : LayerTape F n) : padValues pads (layerPlan n).a = pads.2.1 := rfl
@[simp] theorem padValues_b (pads : LayerTape F n) : padValues pads (layerPlan n).b = pads.2.2.1 := rfl
@[simp] theorem padValues_ab (pads : LayerTape F n) : padValues pads (layerPlan n).ab = pads.2.1*pads.2.2.1 := rfl
@[simp] theorem padValues_d (pads : LayerTape F n) : padValues pads (layerPlan n).d = pads.2.2.2 := rfl

theorem padValues_product (pads : LayerTape F n) :
    padValues pads (layerPlan n).ab = padValues pads (layerPlan n).a * padValues pads (layerPlan n).b := rfl

end LfzkV2.Current.ZeroKnowledge.Frontend
