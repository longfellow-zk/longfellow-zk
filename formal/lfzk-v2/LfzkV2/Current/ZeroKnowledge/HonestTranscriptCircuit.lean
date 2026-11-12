import LfzkV2.Layered.Prover
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptLayer
import LfzkV2.Current.FrontendTopology

/-! The normalized circuit schedule as an honest causal oracle tree.
Entry/assertion coefficients share their existing boundary. Input-only
assertions continue the last combine answer without another query.

The output theorem identifies both the honest payload and its exact replay
state/setup with the existing frontend algorithms. Thus oracle-dependent
honest payloads are produced causally rather than treated as fixed proofs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical

variable {F State Query Answer Pad : Type} [Field F]

def circuitFuel : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    FrontendSchedule.Plan F circuit → Bool → ℕ
  | _,_,_,.input,continuing => if continuing then 0 else 1
  | _,_,_,.inputEntry ..,continuing => if continuing then 0 else 1
  | _,_,_,.layer (mid := mid) _ tail,_ => circuitFuel tail true+(2+mid)+1
  | _,_,_,.entryLayer (mid := mid) _ _ _ tail,_ => circuitFuel tail true+(2+mid)+1

omit [Field F] in
theorem circuitFuel_same {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : FrontendTopology.Same first second) (original : FrontendSchedule.Plan F first)
    (continuing : Bool) : circuitFuel (same.plan original) continuing = circuitFuel original continuing := by
  induction original generalizing continuing with
  | input => cases same; rfl
  | inputEntry entries entry =>
      cases same with
      | entry next => cases next; rfl
  | layer metadata tail ih =>
      cases same with
      | layer classes next => simp only [FrontendTopology.Same.plan,circuitFuel,ih next]
  | entryLayer entries entry metadata tail ih =>
      cases same with
      | entry next =>
          cases next with
          | layer classes rest => simp only [FrontendTopology.Same.plan,circuitFuel,ih rest]

/-- Change only a proved-equal static budget; no query is added. -/
def retime {Result : Type} {first second : ℕ} (equal : first = second)
    (tree : Tree Query Answer Result first) : Tree Query Answer Result second := equal ▸ tree

@[simp] theorem retime_run {Result : Type} {first second : ℕ} (equal : first = second)
    (tree : Tree Query Answer Result first) (H : Query → Answer) : (retime equal tree).run H = tree.run H := by
  cases equal
  rfl

structure CircuitResult (F State Pad : Type) [Field F] {out input : ℕ}
    (circuit : Layered.Circuit F out input) where
  payload : Layered.Replay.Payload circuit
  setup : Layered.Circuit.Setup Pad circuit
  state : State

variable (queries : Queries F State Query Answer)

def circuit : {out input : ℕ} → {source : Layered.Circuit F out input} →
    (plan : FrontendSchedule.Plan F source) → Layered.Replay.PadPlan (Pad := Pad) source →
    (Cube input → F) → (Cube out → F) → State → Frontend.CircuitTape source →
    (continuing : Bool) → Tree Query Answer (CircuitResult F State Pad source) (circuitFuel plan continuing)
  | _,_,_,.input,_,_,_,state,_,continuing =>
      match continuing with
      | true => .done ⟨(),(),state⟩
      | false => (queries.assertions state 0).map fun answer => ⟨(),(),answer.2⟩
  | _,_,_,.inputEntry (checks := checks) _ _,_,_,_,state,_,continuing =>
      match continuing with
      | true =>
          let answer := queries.inputAssertions state checks
          .done ⟨(),(answer.1,()),answer.2⟩
      | false => (queries.assertions state checks).map fun answer => ⟨(),(answer.1,()),answer.2⟩
  | _,_,.layer assertions body rest,.layer _ tail,ids,w,weights,state,pads,_ =>
      (queries.assertions state assertions).bind fun coefficients =>
        let Q := body.effectiveQuadratic weights coefficients.1
        let L := body.effectiveLinear weights coefficients.1
        (layer queries (bindRightAffine Q L (rest.eval w)) (rest.eval w) coefficients.2 pads.1).bind fun head =>
          (circuit tail ids.2 w (nextWeights Q (monomialWeights head.read.point) head.read.alpha)
            head.read.state pads.2 true).map fun next =>
              ⟨(head.payload,next.payload),
                (⟨Frontend.linearPlan ids.1,head.read.point,head.read.scale,head.read.alpha,coefficients.1⟩,
                  next.setup),next.state⟩
  | _,_,.entry checks entry (.layer assertions body rest),.entryLayer _ _ _ tail,ids,w,weights,state,pads,_ =>
      (queries.assertions state (checks+assertions)).bind fun coefficients =>
        let entering := fun i : Fin checks => coefficients.1 ⟨i.val,by omega⟩
        let beta := fun i : Fin assertions => coefficients.1 ⟨checks+i.val,by omega⟩
        let previous := entry.weights weights entering
        let Q := body.effectiveQuadratic previous beta
        let L := body.effectiveLinear previous beta
        (layer queries (bindRightAffine Q L (rest.eval w)) (rest.eval w) coefficients.2 pads.1).bind fun head =>
          (circuit tail ids.2 w (nextWeights Q (monomialWeights head.read.point) head.read.alpha)
            head.read.state pads.2 true).map fun next =>
              ⟨(head.payload,next.payload),
                (entering,(⟨Frontend.linearPlan ids.1,head.read.point,head.read.scale,head.read.alpha,beta⟩,
                  next.setup)),next.state⟩

set_option backward.isDefEq.respectTransparency false in
/-- All honest messages and all challenge-dependent setup values arise from
the same actual query path. No independent complete-proof consistency premise
is used to connect the prover to that path. -/
theorem circuit_output {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (w : Cube input → F) (weights : Cube out → F) (state : State)
    (pads : Frontend.CircuitTape body) (continuing : Bool) (H : Query → Answer) :
    ((circuit queries plan ids w weights state pads continuing).run H).1 =
      let reader := queries.reader H
      let payload := Frontend.realCircuit reader plan w weights state pads
      let replay := Frontend.readSetup reader plan ids payload state continuing
      (⟨payload,replay.1,replay.2⟩ : CircuitResult F State Pad body) := by
  induction plan generalizing state continuing with
  | input =>
      cases pads
      cases continuing <;> dsimp only [circuit,circuitFuel]
      · rw [Tree.run_map]
        rfl
      · rfl
  | inputEntry entry empty =>
      cases pads
      cases continuing <;> dsimp only [circuit,circuitFuel]
      · rw [Tree.run_map]
        rfl
      · rfl
  | layer h tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map,layer_output,ih]
      rfl
  | entryLayer h entry empty tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map,layer_output,ih]
      rfl

end LfzkV2.Current.ZeroKnowledge.HonestTranscript
