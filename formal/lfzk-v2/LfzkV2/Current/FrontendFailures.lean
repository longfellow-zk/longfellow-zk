import LfzkV2.Current.FrontendReplay
import LfzkV2.Layered.SemanticReplay

/-! Failure coverage for the current grouped frontend replay. The circuit
algebra and affine compiler are reused unchanged. Algebraic failure positions
are mapped onto the actual query schedule; several positions may share one
answer. Their local counts and prefix causality must be checked together at
that answer before applying Fiat--Shamir charging. -/
namespace LfzkV2.Current.FrontendReplay
open SumcheckV2 Linear.Challenges
open Layered.Replay (LayerRole clearMessages)

variable {F Pad C : Type} [Field F]

def sampleAtRole (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    (role : LayerRole circuit) → (ℕ → C) → ℕ → ℕ → Sample F (LayerRole.kind circuit role)
  | _, _, .input, role, _, _, _ => Fin.elim0 role
  | _, _, .entry n _ rest, role, answers, start, offset =>
      match role with
      | .inl _ => fun i => decode (answers start) (offset+i.val)
      | .inr role => sampleAtRole decode nonzero rest role answers start (offset+n)
  | _, _, .layer (mid := mid) _ _ rest, role, answers, start, offset =>
      match role with
      | .inl _ => fun i => decode (answers start) (offset+i.val)
      | .inr (.inl i) => fun _ => decode (answers (start+1+i.val)) 0
      | .inr (.inr (.inl _)) => nonzero (answers (start+1+mid))
      | .inr (.inr (.inr (.inl _))) => fun _ => decode (answers (start+mid+2)) 0
      | .inr (.inr (.inr (.inr role))) =>
          sampleAtRole decode nonzero rest role answers
            (if hasLayers rest then start+mid+3 else start+mid+2)
            (if hasLayers rest then 0 else 1)

noncomputable def dataAtRole (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.PadPlan (Pad := Pad) circuit → Layered.Replay.Payload circuit →
    (ℕ → C) → ℕ → ℕ → (Cube input → F) → (Cube out → F) → (Pad → F) → F →
    (role : LayerRole circuit) → Data F (LayerRole.kind circuit role)
  | _, _, .input, _, _, _, _, _, _, _, _, _, role => Fin.elim0 role
  | _, _, .entry n e rest, plan, payload, answers, start, offset, w, weights, pads, claim, role =>
      match role with
      | .inl _ => (dot weights (e.previous (rest.eval w)), claim, e.residuals (rest.eval w))
      | .inr role => dataAtRole decode nonzero rest plan payload answers start (offset+n)
          w (e.weights weights (fun i => decode (answers start) (offset+i.val))) pads claim role
  | _, _, .layer (mid := mid) _ body rest, plan, payload, answers, start, offset,
      w, weights, pads, claim, role =>
      let ml := (readFrom decode nonzero (.layer _ body rest) plan payload answers start offset).1
      let wires := rest.eval w
      let Q := body.effectiveQuadratic weights ml.beta
      let L := body.effectiveLinear weights ml.beta
      let K := body.effectiveConstant weights
      let q := bindRightAffine Q L wires
      let t := ml.transcript body weights
      match role with
      | .inl _ => (dot weights (body.outputs wires), claim, body.residuals wires)
      | .inr (.inl i) => RoundReplay.dataAt q wires (clearMessages plan.1 payload.1 pads)
          (claim-K) i (SumcheckV1.extract_prefix ml.point i)
      | .inr (.inr (.inl _)) =>
          ⟨t.finalClaim pads claim, evaluate wires ml.point, evaluate q ml.point,
            payload.1.cross, t.terminalPads pads⟩
      | .inr (.inr (.inr (.inl _))) =>
          ⟨evaluate wires ml.point, evaluate q ml.point, t.clearA pads, t.clearB pads⟩
      | .inr (.inr (.inr (.inr role))) =>
          dataAtRole decode nonzero rest plan.2 payload.2 answers
            (if hasLayers rest then start+mid+3 else start+mid+2)
            (if hasLayers rest then 0 else 1) w
            (nextWeights Q (monomialWeights ml.point) ml.alpha) pads (t.nextValue pads) role

theorem dataAtRole_valid (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (role : LayerRole circuit) :
    Data.Valid (dataAtRole decode nonzero circuit plan payload answers start offset
      w weights pads claim role) := by
  induction circuit generalizing start offset claim with
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

theorem read_clearMessages (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest)) (answers : ℕ → C)
    (start offset : ℕ) (weights : Cube out → F) (pads : Pad → F) :
    ((readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1.transcript
      body weights).clearRounds pads = List.ofFn (clearMessages plan.1 payload.1 pads) := by
  simp only [readFrom, Linear.LayerMessages.transcript, Linear.LayerTranscript.clearRounds,
    List.map_ofFn]
  rfl

/-- This is derived from the actual circuit reduction, with no premise that
a false accepted circuit encounters a bad oracle answer. -/
theorem bad_at_role (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (hbad : Layered.Circuit.Bad circuit
      (readFrom decode nonzero circuit plan payload answers start offset) w weights pads claim) :
    ∃ role : LayerRole circuit,
      Data.Bad (dataAtRole decode nonzero circuit plan payload answers start offset
        w weights pads claim role)
        (sampleAtRole decode nonzero circuit role answers start offset) := by
  induction circuit generalizing start offset claim with
  | input => exact hbad.elim
  | entry n e rest ih =>
      rcases hbad with he | hr
      · have hn : n ≠ 0 := by obtain ⟨i,_⟩ := he; exact Nat.ne_zero_of_lt i.isLt
        exact ⟨.inl ⟨0, by simp [LfzkV2.Replay.vectorSlots, hn]⟩, he⟩
      · obtain ⟨role,hrole⟩ := ih plan payload _ _ _ _ _ hr
        exact ⟨.inr role,hrole⟩
  | layer a body rest ih =>
      rcases hbad with ha | hl | hr
      · have hn : a ≠ 0 := by obtain ⟨i,_⟩ := ha; exact Nat.ne_zero_of_lt i.isLt
        refine ⟨.inl ⟨0, by simp [LfzkV2.Replay.vectorSlots, hn]⟩, ?_⟩
        exact ha
      · rcases hl with hround | hterminal | hcombine
        · rw [read_clearMessages] at hround
          obtain ⟨i,hi⟩ := (RoundReplay.round_bad_iff _ _ _ _ _).1 hround
          refine ⟨.inr (.inl i), ?_⟩
          simp only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad, readFrom,
            ChallengeBlocks.Data.Bad, ChallengeTest.Bad] at hi ⊢
          convert! hi using 1
        · refine ⟨.inr (.inr (.inl 0)), ?_⟩
          simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad, readFrom,
            Linear.LayerMessages.transcript] using hterminal
        · refine ⟨.inr (.inr (.inr (.inl 0))), ?_⟩
          simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad, readFrom,
            Linear.LayerMessages.transcript, ChallengeBlocks.Data.Bad,
            ChallengeBlocks.Kind.dimension] using hcombine
      · obtain ⟨role,hrole⟩ := ih plan.2 payload.2 _ _ _ _ _ hr
        exact ⟨.inr (.inr (.inr (.inr role))),hrole⟩

noncomputable def BadAt (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) (query : ℕ) : Prop :=
  ∃ role : LayerRole circuit, queryIndex circuit role 0 = query ∧
    Data.Bad (dataAtRole decode nonzero circuit plan payload answers 0 0 w 0 pads 0 role)
      (sampleAtRole decode nonzero circuit role answers 0 0)

/-- A false accepted frontend has a failing algebraic test at one actual
query index. Several tests sharing that index do not introduce extra queries. -/
theorem accepted_failure_cover (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F)
    (hfalse : ¬ circuit.Satisfies w)
    (haccept : circuit.Accepts (read decode nonzero circuit plan payload answers) w pads) :
    ∃ query < slots circuit, BadAt decode nonzero circuit plan payload answers w pads query := by
  have hbad := Layered.Circuit.soundness_reduction circuit _ w pads hfalse haccept
  obtain ⟨role,hr⟩ := bad_at_role decode nonzero circuit plan payload answers 0 0 w 0 pads 0 hbad
  exact ⟨queryIndex circuit role 0, by simpa using queryIndex_lt circuit role 0, role,rfl,hr⟩

end LfzkV2.Current.FrontendReplay
