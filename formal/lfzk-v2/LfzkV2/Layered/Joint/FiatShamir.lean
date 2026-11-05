import LfzkV2.Layered.Joint.Extraction
import LfzkV2.Layered.Joint.Cost
import Bcs.VerifierQuery

/-! Adaptive Fiat–Shamir extraction for the joint transcript. Each query
pays one local budget, including both residuals at the shared opening. -/

namespace LfzkV2.Layered.Joint.FiatShamir

open Finset RecursivePolygero Bcs.TotalOracle Merkle.RandomOracle Replay Cost
open LfzkV2.Joint (Participant Family)
open scoped Classical

variable {F₁ F₂ Key C Public Fmac Out : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks N : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Layered.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Layered.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Layered.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Layered.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def grinding
    [DecidableEq (Domain S₁ S₂)]
    (tree : Tree (Domain S₁ S₂) C Out N)
    (proofOf : Out → Proof S₁ S₂)
    (context : (Domain S₁ S₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key S₁ S₂ x) = context H (key S₁ S₂ x)) :
    CtxGrinding C (Domain S₁ S₂) Out Key
      (I₁.layer.Oracle × I₂.layer.Oracle) N (slots S₁ S₂) where
  adversary := tree
  hashInput out := hashInput S₁ S₂ (proofOf out)
  pts := points S₁ S₂
  key := key S₁ S₂
  ctxAt := context
  ctxAt_off := context_off
  Bad _ _ _ _ := False
  beta _ := 0
  bad_bound := by intros; simp

/-- The merged extraction/MAC bound for the actual two-field transcript.
The MAC rows are stated separately for each satisfying committed witness;
their private affine blinds may differ. -/
theorem extraction_le_of_total [Fintype Key] [Fintype Public]
    [Fintype S₁.Data] [Fintype S₂.Data]
    [DecidableEq (Domain S₁ S₂)]
    (tree : Tree (Domain S₁ S₂) C Out N)
    (proofOf : Out → Proof S₁ S₂)
    (context : (Domain S₁ S₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key S₁ S₂ x) = context H (key S₁ S₂ x))
    (B : ℚ)
    (htotal : ∀ H, ∑ x ∈ (univ.filter fun x =>
        (grinding S₁ S₂ tree proofOf context context_off).Charged x H),
      Charges.budget S₁ S₂ M x ≤ B)
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : Side.Frontend S₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.1.2.1) = tag ctx.1.1.2.2) :
    let fails := fun H : Domain S₁ S₂ → C =>
      let proof := proofOf (tree.run H).1
      let W := context H (Replay.context S₁ S₂ proof).1
      (Replay.context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) ∧
      S₁.Accepts W.1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof) ∧
      S₂.Accepts W.2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof) ∧
      Extraction.extract S₁ S₂ M W proof = none
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂) ≤
      B/Fintype.card C := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  intro fails
  let G := grinding S₁ S₂ tree proofOf context context_off
  refine G.potential_ratio_le_of_total
    (Charges.charge S₁ S₂ M)
    (Charges.charge_nonneg S₁ S₂ M)
    (Charges.budget S₁ S₂ M)
    (Charges.charge_sum_le S₁ S₂ M)
    B htotal fails ?_
  intro H hH
  let proof := proofOf (tree.run H).1
  let W := context H (Replay.context S₁ S₂ proof).1
  have hp := Extraction.path_charge_ge_one S₁ S₂ M W H proof
    hH.1 hH.2.1 hH.2.2.1 (tag (Replay.context S₁ S₂ proof).2.2)
    (hrowOne (Replay.context S₁ S₂ proof) W.1) (hrowTwo (firstFrontend S₁ S₂ proof) W.2)
    ((Extraction.extract_none_iff S₁ S₂ M W proof).mp hH.2.2.2)
  let f := fun x : Domain S₁ S₂ =>
    Charges.charge S₁ S₂ M (context H (G.key x)) x (G.pts.chal H x) (H x)
  apply le_trans _ (G.verifier_charge_le_total
    (fun out => hashInput_injective S₁ S₂ (proofOf out)) f
    (fun x => Charges.charge_nonneg S₁ S₂ M
      (context H (G.key x)) x (G.pts.chal H x) (H x)) H)
  refine hp.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [f]
  have hk : G.key (G.point H i.val) = (Replay.context S₁ S₂ proof).1 :=
    hashInput_key S₁ S₂ proof i.val
  rw [hk]
  rfl

/-- The usual shared adversarial-query budget and all verifier-slot costs. -/
theorem extraction_le [Fintype Key] [Fintype Public]
    [Fintype S₁.Data] [Fintype S₂.Data]
    [DecidableEq (Domain S₁ S₂)]
    (tree : Tree (Domain S₁ S₂) C Out N)
    (proofOf : Out → Proof S₁ S₂)
    (context : (Domain S₁ S₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key S₁ S₂ x) = context H (key S₁ S₂ x))
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : Side.Frontend S₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.1.2.1) = tag ctx.1.1.2.2) :
    let fails := fun H : Domain S₁ S₂ → C =>
      let proof := proofOf (tree.run H).1
      let W := context H (Replay.context S₁ S₂ proof).1
      (Replay.context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) ∧
      S₁.Accepts W.1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof) ∧
      S₂.Accepts W.2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof) ∧
      Extraction.extract S₁ S₂ M W proof = none
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂) ≤
      (N*maxBudget S₁ S₂ M+
        ∑ i, slotBudget S₁ S₂ M i)/Fintype.card C := by
  let G := grinding S₁ S₂ tree proofOf context context_off
  exact extraction_le_of_total S₁ S₂ M tree proofOf context context_off _
    (G.charged_rational_budget_le
      (Charges.budget S₁ S₂ M)
      (Charges.budget_nonneg S₁ S₂ M)
      (maxBudget S₁ S₂ M) (maxBudget_nonneg S₁ S₂ M)
      (budget_le_max S₁ S₂ M) (slotBudget S₁ S₂ M)
      (fun out i => (budget_hashInput S₁ S₂ M (proofOf out) i).le))
    tag hrowOne hrowTwo

end LfzkV2.Layered.Joint.FiatShamir
