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

def decodeSample (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    (kind : Kind) → C → Sample F kind
  | .ordinary block => decode block.dimension
  | .terminal => nonzero

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

noncomputable def layerData (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    PadPlan (Pad := Pad) circuit → Payload circuit → (ℕ → C) → ℕ →
    (Cube input → F) → (Cube out → F) → (Pad → F) → F →
    (role : LayerRole circuit) → Data F (LayerRole.kind circuit role)
  | _, _, .input, _, _, _, _, _, _, _, _, role => Fin.elim0 role
  | _, _, .entry n e rest, plan, payload, answers, start, w, weights, pads, claim, role =>
      match role with
      | .inl _ => (dot weights (e.previous (rest.eval w)), claim, e.residuals (rest.eval w))
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
      | .inr (.inr (.inr (.inl _))) =>
          ⟨evaluate wires ml.point, evaluate q ml.point, t.clearA pads, t.clearB pads⟩
      | .inr (.inr (.inr (.inr role))) =>
          layerData decode nonzero rest plan.2 payload.2 answers
            (start + vectorSlots a + mid + 2) w
            (nextWeights Q (monomialWeights ml.point) ml.alpha) pads (t.nextValue pads) role

theorem layerData_valid (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C)
    (start : ℕ) (w : Cube input → F) (weights : Cube out → F) (pads : Pad → F)
    (claim : F) (role : LayerRole circuit) :
    Data.Valid (layerData decode nonzero circuit plan payload answers start w weights pads claim role) := by
  induction circuit generalizing start claim with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => trivial
      | inr role => apply ih
  | layer a body rest ih =>
      rcases role with i | i | i | i | role
      · trivial
      · exact RoundReplay.dataAt_valid _ _ _ _ _ _
      · trivial
      · trivial
      · apply ih

theorem layer_bad_of_bad (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C)
    (start : ℕ) (w : Cube input → F) (weights : Cube out → F) (pads : Pad → F) (claim : F)
    (hbad : Circuit.Bad circuit (readFrom decode nonzero circuit plan payload answers start)
      w weights pads claim) :
    ∃ role : LayerRole circuit,
      Data.Bad (layerData decode nonzero circuit plan payload answers start w weights pads claim role)
        (decodeSample decode nonzero (LayerRole.kind circuit role)
          (answers (start + layerSlot circuit role))) := by
  induction circuit generalizing start claim with
  | input => exact hbad.elim
  | entry n e rest ih =>
      rcases hbad with he | hr
      · have hn : n ≠ 0 := by
          obtain ⟨i, _⟩ := he
          exact Nat.ne_zero_of_lt i.isLt
        exact ⟨.inl ⟨0, by simp [vectorSlots, hn]⟩, he⟩
      · obtain ⟨role,hrole⟩ := ih plan payload _ _ _ _ hr
        refine ⟨.inr role, ?_⟩
        simpa only [layerData, LayerRole.kind, layerSlot_after_entry, readFrom, Nat.add_assoc] using hrole
  | layer a body rest ih =>
      rcases hbad with hassert | hlayer | hrest
      · have ha : a ≠ 0 := by
          obtain ⟨i, _⟩ := hassert
          exact Nat.ne_zero_of_lt i.isLt
        let i : Fin (vectorSlots a) := ⟨0, by simp [vectorSlots, ha]⟩
        exact ⟨.inl i, hassert⟩
      · rcases hlayer with hround | hterminal | hcombine
        · rw [read_clearMessages] at hround
          obtain ⟨i, hi⟩ := (RoundReplay.round_bad_iff _ _ _ _ _).1 hround
          refine ⟨.inr (.inl i), ?_⟩
          simp only [layerData, LayerRole.kind, layerSlot_round, Data.Bad, readFrom,
            ChallengeBlocks.Data.Bad, ChallengeTest.Bad, decodeSample,
            ChallengeBlocks.Kind.dimension, Nat.add_assoc] at hi ⊢
          convert! hi using 1
        · refine ⟨.inr (.inr (.inl 0)), ?_⟩
          simpa only [layerData, LayerRole.kind, layerSlot_terminal, Data.Bad, readFrom,
            Linear.LayerMessages.transcript, decodeSample, Nat.add_assoc] using hterminal
        · refine ⟨.inr (.inr (.inr (.inl 0))), ?_⟩
          simpa only [layerData, LayerRole.kind, layerSlot_combine, Data.Bad, readFrom,
            Linear.LayerMessages.transcript, ChallengeBlocks.Data.Bad, decodeSample,
            ChallengeBlocks.Kind.dimension, Nat.add_assoc] using hcombine
      · obtain ⟨role, hrole⟩ := ih plan.2 payload.2 _ _ _ _ hrest
        refine ⟨.inr (.inr (.inr (.inr role))), ?_⟩
        simpa only [layerData, LayerRole.kind, layerSlot_there, readFrom,
          Linear.LayerMessages.transcript, Nat.add_assoc] using hrole

noncomputable def semanticData (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C)
    (w : Cube input → F) (pads : Pad → F) :
    (role : Role circuit) → Data F (roleKind circuit role) :=
  layerData decode nonzero circuit plan payload answers 0 w 0 pads 0

theorem semanticData_valid (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C)
    (w : Cube input → F) (pads : Pad → F) (role : Role circuit) :
    Data.Valid (semanticData decode nonzero circuit plan payload answers w pads role) :=
  layerData_valid _ _ _ _ _ _ _ _ _ _ _ _

/-- False satisfaction of the actual affine rows yields a bad challenge on
this schedule. The reduction includes entries at any depth and scalar cases. -/
theorem semantic_bad_of_accepts (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C)
    (w : Cube input → F) (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : circuit.Accepts (read decode nonzero circuit plan payload answers) w pads) :
    ∃ role : Role circuit,
      Data.Bad (semanticData decode nonzero circuit plan payload answers w pads role)
        (decodeSample decode nonzero (roleKind circuit role)
          (answers (roleEquiv circuit role).val)) := by
  have h := Circuit.soundness_reduction circuit _ w pads hfalse haccept
  obtain ⟨role,hr⟩ := layer_bad_of_bad decode nonzero circuit plan payload answers 0 w 0 pads 0 h
  refine ⟨role, ?_⟩
  dsimp only [semanticData, roleKind, roleEquiv, layerSlot, slots, Role] at hr ⊢
  simpa only [Nat.zero_add] using hr

end LfzkV2.Layered.Replay
