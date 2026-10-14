import polygero.Recursion.Correctness
import polygero.Recursion.Error
import polygero.Local.Probability

/-! Random-target induction using the response-uniform local recovery interface. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

private theorem run_terminal (p : ProfileCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.terminal I.layer))
    (coins : I.layer.Coin × I.layer.Query) :
    (ProfileProof.terminal p).run σ W messages coins =
      scanRecoverAt I σ W coins.1 (messages coins.1) := rfl

private theorem run_step {child : Child I} {tail : Protocol child.instance}
    (p : ProfileCertificate I) {cp : ProfileCertificate child.instance}
    (rest : tail.ProfileProof cp)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.step child.link tail.chain))
    (coins : (I.layer.Coin × I.layer.Query) × tail.chain.Coins) :
    (ProfileProof.step (child := child) p rest).run σ W messages coins =
      match rest.run (child.link.statement σ W coins.1.1 coins.1.2)
          (messages.1 coins.1.1) (messages.2 coins.1.1 coins.1.2) coins.2 with
      | none => none
      | some g => scanRecoverAt I σ W coins.1.1
          (child.link.decode ((rest.family (messages.1 coins.1.1)).witness g)) := by
  simp only [run, runTranscript, Protocol.chain, Chain.record]
  split <;> simp_all only

noncomputable def familyProbability (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain)
    (D : (r.family W).Index → Prop) : ℚ :=
  mean (fun coins : protocol.chain.Coins => indicator
    (executionVerify protocol.chain σ W messages coins = true ∧ outputHit D (r.run σ W messages coins)))

theorem familyProbability_terminal (p : ProfileCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.terminal I.layer))
    (D : (tupleCounts I).Index → Prop) :
    (ProfileProof.terminal p).familyProbability σ W messages D =
      mean (fun coin => mean (fun Q : I.layer.Query => indicator
        (I.layer.verify σ W coin (messages coin) Q ∧
          outputHit D (scanRecoverAt I σ W coin (messages coin))))) := by
  unfold familyProbability
  change (mean (fun coins : I.layer.Coin × I.layer.Query => _)) = _
  rw [mean_prod]
  simp only [Protocol.chain,executionVerify,decide_eq_true_eq,run_terminal]
  congr 1

noncomputable def inducedFamily {child : Child I}
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) (D : (tupleCounts I).Index → Prop)
    (Q : I.layer.Query) : (tupleCounts child.instance).Index → Prop :=
  fun g => I.layer.verify σ W coin (child.link.decode ((tupleCounts child.instance).witness g)) Q ∧
    outputHit D (scanRecoverAt I σ W coin (child.link.decode ((tupleCounts child.instance).witness g)))

/-- Fixing a child tuple fixes its unpacked response before the parent query. -/
theorem inducedFamily_frequency {child : Child I}
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop) (g : (tupleCounts child.instance).Index) :
    mean (fun Q => indicator (inducedFamily (child := child) σ W coin D Q g)) =
    indicator (outputHit D (scanRecoverAt I σ W coin
      (child.link.decode ((tupleCounts child.instance).witness g)))) *
      ((responseCount I.layer σ W coin (child.link.decode ((tupleCounts child.instance).witness g)) : ℚ) /
        Fintype.card I.layer.Query) := by
  simp_rw [inducedFamily]
  by_cases h : outputHit D (scanRecoverAt I σ W coin
      (child.link.decode ((tupleCounts child.instance).witness g)))
  · simp only [h,and_true,indicator,if_true,one_mul]
    exact mean_indicator _
  · simp only [h,and_false,indicator,if_false,mean_const,zero_mul]

theorem familyProbability_step {child : Child I} {tail : Protocol child.instance}
    (p : ProfileCertificate I) {cp : ProfileCertificate child.instance}
    (rest : tail.ProfileProof cp)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.step child.link tail.chain))
    (D : (tupleCounts I).Index → Prop) :
    (ProfileProof.step (child := child) p rest).familyProbability σ W messages D =
      mean (fun coin => mean (fun Q => if child.link.direct W Q then
        rest.familyProbability (child.link.statement σ W coin Q) (messages.1 coin) (messages.2 coin Q)
          (inducedFamily (child := child) σ W coin D Q) else 0)) := by
  unfold familyProbability
  change (mean (fun coins : (I.layer.Coin × I.layer.Query) × tail.chain.Coins => _)) = _
  rw [mean_prod]
  rw [mean_prod]
  apply mean_congr
  intro coin
  apply mean_congr
  intro Q
  by_cases hd : child.link.direct W Q
  · rw [if_pos hd]
    apply mean_congr
    intro coins
    simp only [Protocol.chain,executionVerify,Bool.and_eq_true,decide_eq_true_eq,run_step,hd,true_and]
    cases he : rest.run (child.link.statement σ W coin Q) (messages.1 coin)
        (messages.2 coin Q) coins with
    | none => simp only [outputHit]
    | some g =>
      have hs := rest.run_valid _ _ _ _ _ he
      dsimp only [family] at hs
      have hv := (child.verify_iff σ W coin Q _).mp ⟨hd,hs⟩
      simp only [outputHit,inducedFamily,hv,true_and]
      rfl
  · simp only [Protocol.chain,executionVerify,Bool.and_eq_true,decide_eq_true_eq,
      hd,false_and,indicator,if_false,mean_const]

set_option maxHeartbeats 1000000 in
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
        r.error+(1-r.error)*rate := by
  induction r with
  | @terminal I p =>
    intro Z _ _ σ W messages D rate hr0 hr1 hD
    simp_rw [familyProbability_terminal]
    apply (mean_mono (fun z => mean_mono (fun coin =>
      family_response_mean I p.toProfileParameters (σ z) W p.threshold p.floor_le
        p.threshold_lt_one.le (D z) coin (messages z coin)))).trans
    exact localEnvelope_mean I p.toProfileParameters σ W p.threshold rate p.threshold_lt_one.le
      hr0 hr1 p.field_error_lt_one.le
      p.threshold_condition D hD
  | @step I child tail p cp rest ih =>
    intro Z _ _ σ W messages D rate hr0 hr1 hD
    have hc1 := rest.error_bounds.2.le
    have hcoin (z : Z) (coin : I.layer.Coin) :
        mean (fun Q => if child.link.direct W Q then
          rest.familyProbability (child.link.statement (σ z) W coin Q) ((messages z).1 coin)
            ((messages z).2 coin Q) (inducedFamily (child := child) (σ z) W coin (D z) Q) else 0) ≤
          rest.error+(1-rest.error)*localEnvelope I p.toProfileParameters (σ z) W p.threshold (D z) coin := by
      let E := inducedFamily (child := child) (σ z) W coin (D z)
      have hfreq (g) : mean (fun Q => indicator (E Q g)) ≤
          localEnvelope I p.toProfileParameters (σ z) W p.threshold (D z) coin := by
        change mean (fun Q => indicator (inducedFamily (child := child) (σ z) W coin (D z) Q g)) ≤ _
        rw [inducedFamily_frequency]
        unfold indicator
        split_ifs with hout
        · rw [one_mul]
          exact response_fraction_le_envelope I p.toProfileParameters (σ z) W p.threshold
            p.floor_le p.threshold_lt_one.le (D z) coin _ hout
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
    simp only [mean_add,mean_const,mean_mul_left] at h
    have hlocal := localEnvelope_mean I p.toProfileParameters σ W p.threshold rate p.threshold_lt_one.le
      hr0 hr1 p.field_error_lt_one.le
      p.threshold_condition D hD
    have hm := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hc1)
    apply h.trans
    change _ ≤ (p.error+(1-p.error)*rest.error)+(1-(p.error+(1-p.error)*rest.error))*rate
    dsimp only [ProfileCertificate.error] at *
    nlinarith only [hm]

/-- Extraction failure is the empty-target specialization. -/
theorem extraction_failure_le (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    r.familyProbability σ W messages (fun _ => False) ≤ r.error := by
  have h := r.randomTargetProbability_le (fun _ : Unit => σ) W (fun _ => messages)
    (fun _ _ => False) 0 le_rfl zero_le_one (fun _ => by simp [indicator])
  simpa only [mean_const,mul_zero,add_zero] using h

end RecursivePolygero.Protocol.ProfileProof
