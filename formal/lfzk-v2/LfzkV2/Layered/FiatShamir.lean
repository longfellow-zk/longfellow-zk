import LfzkV2.Layered.Sampling

/-!
# Adaptive Fiat–Shamir soundness of the linear-terminal frontend

Tests are reconstructed from actual layered circuits and message prefixes.
Commitment contexts remain fixed off the point being resampled. The only
candidate factor is the size of that fixed family; later masked claims are
not guessed or enumerated. Ordinary blocks and terminal scales retain their
separate sampler costs.
-/

namespace LfzkV2.Layered.FiatShamir

open SumcheckV2 Linear.Challenges Replay Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Key Context Candidate Pad Out : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq Key]
variable {out input N : ℕ}

structure Setup (circuit : Layered.Circuit F out input) (C Key Context Candidate Pad Out : Type)
    [Fintype C] [DecidableEq Key] (N : ℕ) where
  adversary : Tree (Point Key F circuit) C Out N
  proofOf : Out → Key × Payload circuit
  plan : PadPlan (Pad := Pad) circuit
  sampling : Sampling (C := C) circuit
  dflt : C
  context : (Point Key F circuit → C) → Key → Context
  context_off : ∀ (H H' : Point Key F circuit → C) (x : Point Key F circuit),
    AgreeOff x H H' → context H' x.1 = context H x.1
  inputValue : Context → Candidate → Cube input → F
  padValue : Context → Candidate → Pad → F

namespace Setup

variable (circuit : Layered.Circuit F out input)
variable (S : Setup circuit C Key Context Candidate Pad Out N) [Fintype Candidate]

noncomputable def pointBad (ctx : Context) (x : Point Key F circuit)
    (pref : Fin ((points circuit).slot x) → C) (answer : C) : Prop :=
  ∃ candidate, Data.Bad
    (pointData S.sampling.decode S.sampling.terminal.decode S.dflt circuit S.plan x pref
      (S.inputValue ctx candidate) (S.padValue ctx candidate))
    ((pointSampler circuit S.sampling x).decode answer)

def rawBudget (x : Point Key F circuit) : ℕ :=
  Fintype.card Candidate * (pointKind circuit x).rawBudget S.sampling.fieldFiber S.sampling.terminal.fiber

theorem pointBad_card_le (ctx : Context) (x : Point Key F circuit)
    (pref : Fin ((points circuit).slot x) → C) :
    (univ.filter (S.pointBad circuit ctx x pref)).card ≤ S.rawBudget circuit x := by
  have he : (univ.filter (S.pointBad circuit ctx x pref)) =
      univ.biUnion (fun candidate => univ.filter fun answer : C => Data.Bad
        (pointData S.sampling.decode S.sampling.terminal.decode S.dflt circuit S.plan x pref
          (S.inputValue ctx candidate) (S.padValue ctx candidate))
        ((pointSampler circuit S.sampling x).decode answer)) := by
    ext answer
    simp [pointBad]
  rw [he]
  exact card_biUnion_le.trans ((sum_le_sum fun candidate _ =>
    pointSampler_bad_card circuit S.sampling x _ (pointData_valid _ _ _ _ _ _ _ _ _)).trans_eq
      (by simp [rawBudget]))

noncomputable def grinding : CtxGrinding C (Point Key F circuit) Out Key Context N (slots circuit) where
  adversary := S.adversary
  hashInput proof := hashInput circuit (S.proofOf proof).1 (S.proofOf proof).2
  pts := points circuit
  key := Prod.fst
  ctxAt := S.context
  ctxAt_off := S.context_off
  Bad := S.pointBad circuit
  beta := S.rawBudget circuit
  bad_bound ctx x pref := by
    convert! S.pointBad_card_le circuit ctx x pref using 1

noncomputable def view (H : Point Key F circuit → C) (proof : Out) : Reconstruction circuit Pad :=
  reconstructionFromAnswers S.sampling.decode S.sampling.terminal.decode circuit S.plan
    (S.proofOf proof).2 (fun j => H (hashInput circuit (S.proofOf proof).1 (S.proofOf proof).2 j))

/-- Authenticated equations for one member of the fixed candidate family.
The source input equality may be supplied by either the direct or packed
compiler; the latter has its separate packing bad event. -/
noncomputable def Accepts (H : Point Key F circuit → C) (proof : Out) (candidate : Candidate) : Prop :=
  let v := S.view circuit H proof
  let ctx := S.context H (S.proofOf proof).1
  v.constraints.Holds (S.padValue ctx candidate)
    (dot (Circuit.inputWeights circuit v.messages 0) (S.inputValue ctx candidate))

noncomputable def FalseAccepted (H : Point Key F circuit → C) : Prop :=
  let proof := (S.adversary.run H).1
  ∃ candidate, S.Accepts circuit H proof candidate ∧
    ¬ circuit.Satisfies (S.inputValue (S.context H (S.proofOf proof).1) candidate)

theorem bad_of_falseAccepted (H : Point Key F circuit → C)
    (hbad : S.FalseAccepted circuit H) : (S.grinding circuit).RoundBad H := by
  obtain ⟨candidate, haccept, hfalse⟩ := hbad
  let proof := (S.adversary.run H).1
  let payload := (S.proofOf proof).2
  let key := (S.proofOf proof).1
  let ctx := S.context H key
  let w := S.inputValue ctx candidate
  let pads := S.padValue ctx candidate
  have hc : Linear.ClearAccepts pads 0
      (Circuit.proof circuit (S.view circuit H proof).messages
        0)
      (dot (Circuit.inputWeights circuit (S.view circuit H proof).messages
        0) w) :=
    (Linear.buildConstraints_correct _ _ _).mp ⟨_, (S.view circuit H proof).built, haccept⟩
  obtain ⟨role, hrole⟩ := semantic_bad_of_accepts S.sampling.decode S.sampling.terminal.decode
    circuit S.plan payload (fun j => H (hashInput circuit key payload j)) w pads hfalse hc
  let i := roleEquiv circuit role
  refine ⟨i, candidate, ?_⟩
  change Data.Bad
    (pointData S.sampling.decode S.sampling.terminal.decode S.dflt circuit S.plan
      (hashInput circuit key payload i.val)
      ((points circuit).chal H (hashInput circuit key payload i.val))
      (S.inputValue (S.context H (hashInput circuit key payload i.val).1) candidate)
      (S.padValue (S.context H (hashInput circuit key payload i.val).1) candidate))
    ((pointSampler circuit S.sampling (hashInput circuit key payload i.val)).decode
      (H (hashInput circuit key payload i.val)))
  rw [hashInput_at, pointData_eq]
  change Data.Bad (semanticData _ _ _ _ _ _ w pads ((roleEquiv circuit).symm i))
    ((S.sampling.blocks i).decode (H (pointAt circuit key payload i)))
  rw [S.sampling.agrees]
  dsimp only [i]
  rw [(roleEquiv circuit).symm_apply_apply]
  simpa only [hashInput_at] using hrole

/-- A finite adaptive-oracle bound derived from actual compiled frontend
acceptance. `maxBudget` and the slot sum are in raw-answer units; their
normalization must retain the nonzero terminal denominator. -/
theorem soundness_le [Fintype Key] [Nonempty C]
    (maxBudget : ℕ) (hmax : ∀ x, S.rawBudget circuit x ≤ maxBudget) :
    ((univ.filter (S.FalseAccepted circuit)).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card (Point Key F circuit) ≤
      (N * maxBudget + Fintype.card Candidate *
        ∑ i : Fin (slots circuit), (roleKind circuit ((roleEquiv circuit).symm i)).rawBudget
          S.sampling.fieldFiber S.sampling.terminal.fiber : ℕ) / Fintype.card C := by
  have h := (S.grinding circuit).ratio_le maxBudget hmax
    (fun i => Fintype.card Candidate *
      (roleKind circuit ((roleEquiv circuit).symm i)).rawBudget
        S.sampling.fieldFiber S.sampling.terminal.fiber)
    (fun proof i => by
      change S.rawBudget circuit (hashInput circuit (S.proofOf proof).1 (S.proofOf proof).2 i.val) ≤ _
      rw [hashInput_at]
      exact le_rfl)
    (S.FalseAccepted circuit) (S.bad_of_falseAccepted circuit)
  simpa only [← Finset.mul_sum] using h

end Setup
end LfzkV2.Layered.FiatShamir
