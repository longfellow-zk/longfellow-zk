import polygero.Recursion.ProbabilityEvent
import polygero.Recursion.Error

/-! The single recursive random-target induction and its paper-certificate transport. -/

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

set_option maxHeartbeats 1000000 in
/-- Random-target induction discharged by a `HahnProfileProof`. -/
theorem randomTargetProbability_le (r : protocol.HahnProfileProof p) :
    ∀ {Z : Type} [Fintype Z] [Nonempty Z]
      (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
      (messages : Z → Strategy protocol.chain)
      (D : Z → (r.family W).Index → Prop) (rate : ℚ),
      0 ≤ rate → rate ≤ 1 →
      (∀ g, mean (fun z => indicator (D z g)) ≤ rate) →
      mean (fun z => r.familyProbability (σ z) W (messages z) (D z)) ≤
        r.error + (1 - r.error) * rate := by
  induction r with
  | @terminal I p =>
    intro Z _ _ σ W messages D rate hr0 hr1 hD
    simp_rw [familyProbability_terminal]
    apply (mean_mono (fun z => mean_mono (fun coin =>
      family_response_mean I p.toProfileParameters (σ z) W p.threshold p.columnFloor_le
        p.threshold_lt_one.le (D z) coin (messages z coin)))).trans
    exact localEnvelope_mean_of_hahn I p σ W rate hr0 hr1 D hD
  | @step I child tail p cp rest ih =>
    intro Z _ _ σ W messages D rate hr0 hr1 hD
    have hc1 := rest.error_bounds.2.le
    have hcoin (z : Z) (coin : I.layer.Coin) :
        mean (fun Q => if child.link.direct W Q then
          rest.familyProbability (child.link.statement (σ z) W coin Q) ((messages z).1 coin)
            ((messages z).2 coin Q) (ProfileProof.inducedFamily (child := child) (σ z) W coin (D z) Q) else 0) ≤
          rest.error + (1 - rest.error) * localEnvelope I p.toProfileParameters (σ z) W p.threshold (D z) coin := by
      let E := ProfileProof.inducedFamily (child := child) (σ z) W coin (D z)
      have hfreq (g) : mean (fun Q => indicator (E Q g)) ≤
          localEnvelope I p.toProfileParameters (σ z) W p.threshold (D z) coin := by
        change mean (fun Q => indicator (ProfileProof.inducedFamily (child := child) (σ z) W coin (D z) Q g)) ≤ _
        rw [ProfileProof.inducedFamily_frequency]
        unfold indicator
        split_ifs with hout
        · rw [one_mul]
          exact response_fraction_le_envelope I p.toProfileParameters (σ z) W p.threshold
            p.columnFloor_le p.threshold_lt_one.le (D z) coin _ hout
        · rw [zero_mul]
          exact (localEnvelope_bounds I p.toProfileParameters (σ z) W p.threshold
            p.threshold_nonneg p.threshold_lt_one.le (D z) coin).1
      have hb := localEnvelope_bounds I p.toProfileParameters (σ z) W p.threshold
        p.threshold_nonneg p.threshold_lt_one.le (D z) coin
      have hchild := ih (fun Q => child.link.statement (σ z) W coin Q)
        ((messages z).1 coin) (fun Q => (messages z).2 coin Q) E
        (localEnvelope I p.toProfileParameters (σ z) W p.threshold (D z) coin) hb.1 hb.2 hfreq
      apply le_trans (mean_mono (fun Q => ?_)) hchild
      by_cases hd : child.link.direct W Q
      · simp only [if_pos hd]
        exact le_rfl
      · rw [if_neg hd]
        exact (show mean (fun _ : tail.chain.Coins => (0 : ℚ)) ≤ _ from
          mean_mono (fun _ => indicator_nonneg _)).trans_eq' (mean_const 0)
    simp_rw [familyProbability_step]
    have h := mean_mono (fun z => mean_mono (hcoin z))
    simp only [mean_add, mean_const, mean_mul_left] at h
    have hlocal := localEnvelope_mean_of_hahn I p σ W rate hr0 hr1 D hD
    have hm := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hc1)
    apply h.trans
    change _ ≤ (p.error + (1 - p.error) * rest.error) + (1 - (p.error + (1 - p.error) * rest.error)) * rate
    dsimp only [HahnSystemCertificate.error] at *
    nlinarith only [hm]

/-- Extraction failure is the empty-target specialization for `HahnProfileProof`. -/
theorem extraction_failure_le (r : protocol.HahnProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    r.familyProbability σ W messages (fun _ => False) ≤ r.error := by
  have h := r.randomTargetProbability_le (fun _ : Unit => σ) W (fun _ => messages)
    (fun _ _ => False) 0 le_rfl zero_le_one (fun _ => by simp [indicator])
  simpa only [mean_const, mul_zero, add_zero] using h

end RecursivePolygero.Protocol.HahnProfileProof

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

/-- The paper and Hahn analyses assign the same event to every random tape. -/
theorem toHahnProfileProof_familyProbability (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (D : (r.family W).Index → Prop) :
    r.toHahnProfileProof.familyProbability σ W messages D =
      r.familyProbability σ W messages D := by
  unfold HahnProfileProof.familyProbability familyProbability
  apply mean_congr
  intro coins
  rw [r.toHahnProfileProof_run]
  rfl

/-- A fixed oracle is tested against targets selected using earlier randomness.
Every fixed witness has target frequency at most `rate`. -/
theorem randomTargetProbability_le (r : protocol.ProfileProof p) :
    ∀ {Z : Type} [Fintype Z] [Nonempty Z]
      (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
      (messages : Z → Strategy protocol.chain)
      (D : Z → (r.family W).Index → Prop) (rate : ℚ),
      0 ≤ rate → rate ≤ 1 →
      (∀ g, mean (fun z => indicator (D z g)) ≤ rate) →
      mean (fun z => r.familyProbability (σ z) W (messages z) (D z)) ≤
        r.error + (1 - r.error) * rate := by
  intro Z _ _ σ W messages D rate hr0 hr1 hD
  have h := r.toHahnProfileProof.randomTargetProbability_le σ W messages D rate hr0 hr1 hD
  simpa only [r.toHahnProfileProof_familyProbability, r.toHahnProfileProof_error] using h

/-- Extraction failure is the empty-target specialization. -/
theorem extraction_failure_le (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    r.familyProbability σ W messages (fun _ => False) ≤ r.error := by
  have h := r.randomTargetProbability_le (fun _ : Unit => σ) W (fun _ => messages)
    (fun _ _ => False) 0 le_rfl zero_le_one (fun _ => by simp [indicator])
  simpa only [mean_const, mul_zero, add_zero] using h

end RecursivePolygero.Protocol.ProfileProof
