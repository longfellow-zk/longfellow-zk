import LfzkV2.Layered.Schedule
import LfzkV2.Layered.Soundness
import LfzkV2.RoundReplay

/-! Exact challenge tests reconstructed from layered circuit semantics. The
terminal test is fixed before its scale; the combination test can depend on
that scale and the two subsequently transmitted masked claims. -/

namespace LfzkV2.Layered.Replay

open SumcheckV2 Linear.Challenges
open LfzkV2.Replay (vectorSlots)

variable {F Pad C : Type} [Field F]

def clearMessages {n : ℕ} (plan : LayerPads Pad n) (payload : LayerPayload F n)
    (pads : Pad → F) : Fin n → RoundPoly F :=
  fun i => unmask (payload.rounds i) ⟨pads (plan.round i).1, pads (plan.round i).2⟩

theorem read_clearMessages (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input) (plan : PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Payload (.layer a body rest)) (answers : ℕ → C) (start : ℕ)
    (weights : Cube out → F) (pads : Pad → F) :
    ((readFrom decode nonzero (.layer a body rest) plan payload answers start).1.transcript body weights).clearRounds
        pads = List.ofFn (clearMessages plan.1 payload.1 pads) := by
  simp only [readFrom, Linear.LayerMessages.transcript, Linear.LayerTranscript.clearRounds, List.map_ofFn]
  rfl

/-- A combination test that the reduction reports only when `valid` holds;
otherwise its claims are the true values, which no challenge can repair. -/
noncomputable def gatedCombine (valid : Prop) (d : CombineData F) : CombineData F :=
  open Classical in if valid then d else ⟨d.trueA, d.trueB, d.trueA, d.trueB⟩

theorem gatedCombine_bad (valid : Prop) (d : CombineData F) (alpha : F) :
    BadCombineEvent (gatedCombine valid d).trueA (gatedCombine valid d).trueB
      (gatedCombine valid d).claimA (gatedCombine valid d).claimB alpha ↔
      valid ∧ BadCombineEvent d.trueA d.trueB d.claimA d.claimB alpha := by
  classical
  by_cases h : valid
  · simp [gatedCombine, h]
  · simp [gatedCombine, h, BadCombineEvent]

noncomputable def layerData (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    PadPlan (Pad := Pad) circuit → Payload circuit → (ℕ → C) → ℕ →
    (Cube input → F) → (Cube out → F) → (Pad → F) → F →
    (role : LayerRole circuit) → Data F (LayerRole.kind circuit role)
  | _, _, .input, _, _, _, _, _, _, _, _, role => Fin.elim0 role
  | _, _, .entry n e rest, plan, payload, answers, start, w, weights, pads, claim, role =>
      match role with
      | .inl _ => (dot weights (e.previous (rest.eval w)), claim, Circuit.entryResiduals e rest w)
      | .inr role => layerData decode nonzero rest plan payload answers (start + vectorSlots n)
          w (e.weights weights (decode n (answers start))) pads claim role
  | _, _, .layer (mid := mid) a body rest, plan, payload, answers, start, w, weights,
      pads, claim, role =>
      let ml := (readFrom decode nonzero (.layer a body rest) plan payload answers start).1
      let wires := rest.eval w
      let Q := body.effectiveQuadratic weights ml.beta
      let L := body.effectiveLinear weights ml.beta
      let K := body.effectiveConstant weights
      let q := bindRightAffine Q L wires
      let t := ml.transcript body weights
      match role with
      | .inl _ => (dot weights (body.outputs wires), claim, body.residuals wires)
      | .inr (.inl i) => RoundReplay.dataAt q wires
          (clearMessages plan.1 payload.1 pads) (claim - K) i
          (SumcheckV1.extract_prefix ml.point i)
      | .inr (.inr (.inl _)) =>
          ⟨t.finalClaim pads claim, evaluate wires ml.point, evaluate q ml.point,
            payload.1.cross, t.terminalPads pads⟩
      | .inr (.inr (.inr (.inl _))) => gatedCombine (∀ i, rest.headResiduals w i = 0)
          ⟨evaluate wires ml.point, evaluate q ml.point, t.clearA pads, t.clearB pads⟩
      | .inr (.inr (.inr (.inr role))) =>
          layerData decode nonzero rest plan.2 payload.2 answers
            (start + vectorSlots a + mid + 2) w
            (nextWeights Q (monomialWeights ml.point) ml.alpha) pads (t.nextValue pads) role

end LfzkV2.Layered.Replay
