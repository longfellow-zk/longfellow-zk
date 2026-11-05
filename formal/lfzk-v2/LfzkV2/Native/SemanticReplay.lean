import LfzkV2.Native.Replay
import LfzkV2.SemanticReplay

/-!
# Native algebraic tests at the shared challenge roles

The role schedule is reused only through `circuit.shape`. The true tables,
round input `claim-K`, and corrected suffix claim all come from the native
three-stream circuit. Thus the semantic bridge retains both affine corrections.
-/

namespace LfzkV2.Native.Replay

open SumcheckV2 ChallengeBlocks

variable {F Pad Slot C : Type} [Field F]

theorem read_clearMessages (decode : (n : ℕ) → C → Fin n → F)
    {out mid input a : ℕ} (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Circuit F mid input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) (.layer a body rest))
    (payload : Payload (.layer a body rest)) (answers : ℕ → C) (start : ℕ) (pads : Pad → F) :
    (readFrom decode (.layer a body rest) plan payload answers start).1.transcript.clearRounds pads =
      List.ofFn (LfzkV2.Replay.clearMessages plan.1 payload.1 pads) := by
  simp only [readFrom, LfzkV2.LayerMessages.transcript, LfzkV2.LayerTranscript.clearRounds,
    List.map_ofFn]
  rfl

noncomputable def layerData (decode : (n : ℕ) → C → Fin n → F) :
    {out input : ℕ} → (circuit : Circuit F out input) →
    PadPlan (Pad := Pad) (Slot := Slot) circuit → Payload circuit → (ℕ → C) → ℕ →
    (Cube input → F) → (Cube out → F) → (Pad → F) → F →
    (role : LfzkV2.Replay.LayerRole circuit.shape) →
      Data F (LfzkV2.Replay.LayerRole.kind circuit.shape role)
  | _, _, .input, _, _, _, _, _, _, _, _, role => Fin.elim0 role
  | _, _, .layer (mid := mid) a body rest, plan, payload, answers, start, w, weights,
      pads, claim, role =>
      let ml := (readFrom decode (.layer a body rest) plan payload answers start).1
      let wires := rest.eval w
      let Q := body.effectiveQuadratic weights ml.beta
      let L := body.effectiveLinear weights ml.beta
      let K := body.effectiveConstant weights
      let q := bindRightAffine Q L wires
      match role with
      | .inl _ => (dot weights (body.outputs wires), claim, body.residuals wires)
      | .inr (.inl i) => RoundReplay.dataAt q wires
          (LfzkV2.Replay.clearMessages plan.1 payload.1 pads) (claim - K) i
          (SumcheckV1.extract_prefix ml.point i)
      | .inr (.inr (.inl _)) =>
          ⟨evaluate wires ml.point, evaluate q ml.point,
            ml.transcript.clearA pads, ml.transcript.clearB pads⟩
      | .inr (.inr (.inr role)) =>
          layerData decode rest plan.2 payload.2 answers
            (start + LfzkV2.Replay.vectorSlots a + mid + 1) w
            (nextWeights Q (monomialWeights ml.point) ml.alpha) pads
            ((body.transcript weights ml).nextValue pads) role

theorem layerData_valid (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (role : LfzkV2.Replay.LayerRole circuit.shape) :
    Data.Valid (layerData decode circuit plan payload answers start w weights pads claim role) := by
  induction circuit generalizing start claim with
  | input => exact Fin.elim0 role
  | layer a body rest ih =>
      rcases role with i | i | i | role
      · trivial
      · exact RoundReplay.dataAt_valid _ _ _ _ _ _
      · trivial
      · apply ih

theorem layer_bad_of_bad (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (hbad : circuit.Bad (readFrom decode circuit plan payload answers start) w weights pads claim) :
    ∃ role : LfzkV2.Replay.LayerRole circuit.shape,
      Data.Bad (layerData decode circuit plan payload answers start w weights pads claim role)
        (decode (LfzkV2.Replay.LayerRole.kind circuit.shape role).dimension
          (answers (start + LfzkV2.Replay.layerSlot circuit.shape role))) := by
  induction circuit generalizing start claim with
  | input => exact hbad.elim
  | layer a body rest ih =>
      rcases hbad with hassert | hlayer | hrest
      · have ha : a ≠ 0 := by
          obtain ⟨i, _⟩ := hassert
          exact Nat.ne_zero_of_lt i.isLt
        let i : Fin (LfzkV2.Replay.vectorSlots a) :=
          ⟨0, by simp [LfzkV2.Replay.vectorSlots, ha]⟩
        exact ⟨.inl i, hassert⟩
      · rcases hlayer with hround | hcombine
        · rw [read_clearMessages] at hround
          obtain ⟨i, hi⟩ := (RoundReplay.round_bad_iff _ _ _ _ _).1 hround
          refine ⟨.inr (.inl i), ?_⟩
          simp only [layerData, Circuit.shape, LfzkV2.Replay.LayerRole.kind,
            LfzkV2.Replay.layerSlot_round, Data.Bad, readFrom, ChallengeTest.Bad,
            Kind.dimension, Nat.add_assoc] at hi ⊢
          convert! hi using 1
        · refine ⟨.inr (.inr (.inl 0)), ?_⟩
          simp only [layerData, Circuit.shape, LfzkV2.Replay.LayerRole.kind,
            LfzkV2.Replay.layerSlot_combine, Data.Bad, readFrom,
            LfzkV2.LayerMessages.transcript, Kind.dimension, Nat.add_assoc] at hcombine ⊢
          convert! hcombine using 1
      · obtain ⟨role, hrole⟩ := ih plan.2 payload.2 _ _ _ _ hrest
        refine ⟨.inr (.inr (.inr role)), ?_⟩
        simpa only [layerData, Circuit.shape, LfzkV2.Replay.LayerRole.kind,
          LfzkV2.Replay.layerSlot_there, readFrom, LfzkV2.LayerMessages.transcript,
          Nat.add_assoc] using hrole

noncomputable def semanticData (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) :
    (role : LfzkV2.Replay.Role circuit.shape) → Data F (LfzkV2.Replay.roleKind circuit.shape role)
  | .inl _ => circuit.eval w
  | .inr role => layerData decode circuit plan payload answers (LfzkV2.Replay.vectorSlots out) w
      (monomialWeights (LfzkV2.Replay.outputPoint decode out answers)) pads 0 role

theorem semanticData_valid (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F)
    (role : LfzkV2.Replay.Role circuit.shape) :
    Data.Valid (semanticData decode circuit plan payload answers w pads role) := by
  cases role with
  | inl _ => trivial
  | inr role => exact layerData_valid _ _ _ _ _ _ _ _ _ _ _

/-- Accepted native constraints select an actual bad challenge block on the shared
schedule. The premise and the reconstructed algebra both use native semantics. -/
theorem semantic_bad_of_accepts (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F)
    (hfalse : ¬ circuit.Satisfies w)
    (haccept : Native.ClearAccepts pads 0
      (circuit.proof (read decode circuit plan payload answers)
        (monomialWeights (LfzkV2.Replay.outputPoint decode out answers)))
      (dot (circuit.inputWeights (read decode circuit plan payload answers)
        (monomialWeights (LfzkV2.Replay.outputPoint decode out answers))) w)) :
    ∃ role : LfzkV2.Replay.Role circuit.shape,
      Data.Bad (semanticData decode circuit plan payload answers w pads role)
        (decode (LfzkV2.Replay.roleKind circuit.shape role).dimension
          (answers (LfzkV2.Replay.roleEquiv circuit.shape role).val)) := by
  rcases circuit.soundness_reduction _ w (LfzkV2.Replay.outputPoint decode out answers)
    pads hfalse haccept with houtput | hlayer
  · have hout : out ≠ 0 := by
      intro h
      subst out
      exact houtput.elim
    let i : Fin (LfzkV2.Replay.vectorSlots out) :=
      ⟨0, by simp [LfzkV2.Replay.vectorSlots, hout]⟩
    exact ⟨.inl i, houtput⟩
  · obtain ⟨role, hrole⟩ := layer_bad_of_bad decode circuit plan payload answers
      (LfzkV2.Replay.vectorSlots out) w _ pads 0 hlayer
    exact ⟨.inr role, hrole⟩

end LfzkV2.Native.Replay
