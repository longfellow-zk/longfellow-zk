import polygero.Recursion.Correctness
import polygero.Local.Probability

/-! Probability events and one-step identities for the recursive extractor. -/

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

end RecursivePolygero.Protocol.ProfileProof

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

private theorem run_terminal (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.terminal I.layer))
    (coins : I.layer.Coin × I.layer.Query) :
    (HahnProfileProof.terminal p).run σ W messages coins =
      scanRecoverAt I σ W coins.1 (messages coins.1) := rfl

private theorem run_step {child : Child I} {tail : Protocol child.instance}
    (p : HahnSystemCertificate I) {cp : HahnSystemCertificate child.instance}
    (rest : tail.HahnProfileProof cp)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.step child.link tail.chain))
    (coins : (I.layer.Coin × I.layer.Query) × tail.chain.Coins) :
    (HahnProfileProof.step (child := child) p rest).run σ W messages coins =
      match rest.run (child.link.statement σ W coins.1.1 coins.1.2)
          (messages.1 coins.1.1) (messages.2 coins.1.1 coins.1.2) coins.2 with
      | none => none
      | some g => scanRecoverAt I σ W coins.1.1
          (child.link.decode ((rest.family (messages.1 coins.1.1)).witness g)) := by
  simp only [run, runTranscript, Protocol.chain, Chain.record]
  split <;> simp_all only

noncomputable def familyProbability (r : protocol.HahnProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain)
    (D : (r.family W).Index → Prop) : ℚ :=
  mean (fun coins : protocol.chain.Coins => indicator
    (executionVerify protocol.chain σ W messages coins = true ∧ outputHit D (r.run σ W messages coins)))

theorem familyProbability_terminal (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.terminal I.layer))
    (D : (tupleCounts I).Index → Prop) :
    (HahnProfileProof.terminal p).familyProbability σ W messages D =
      mean (fun coin => mean (fun Q : I.layer.Query => indicator
        (I.layer.verify σ W coin (messages coin) Q ∧
          outputHit D (scanRecoverAt I σ W coin (messages coin))))) := by
  unfold familyProbability
  change (mean (fun coins : I.layer.Coin × I.layer.Query => _)) = _
  rw [mean_prod]
  simp only [Protocol.chain, executionVerify, decide_eq_true_eq, run_terminal]
  congr 1

theorem familyProbability_step {child : Child I} {tail : Protocol child.instance}
    (p : HahnSystemCertificate I) {cp : HahnSystemCertificate child.instance}
    (rest : tail.HahnProfileProof cp)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy (.step child.link tail.chain))
    (D : (tupleCounts I).Index → Prop) :
    (HahnProfileProof.step (child := child) p rest).familyProbability σ W messages D =
      mean (fun coin => mean (fun Q => if child.link.direct W Q then
        rest.familyProbability (child.link.statement σ W coin Q) (messages.1 coin) (messages.2 coin Q)
          (ProfileProof.inducedFamily (child := child) σ W coin D Q) else 0)) := by
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
    simp only [Protocol.chain, executionVerify, Bool.and_eq_true, decide_eq_true_eq, run_step, hd, true_and]
    cases he : rest.run (child.link.statement σ W coin Q) (messages.1 coin)
        (messages.2 coin Q) coins with
    | none => simp only [outputHit]
    | some g =>
      have hs := rest.run_valid _ _ _ _ _ he
      dsimp only [family] at hs
      have hv := (child.verify_iff σ W coin Q _).mp ⟨hd, hs⟩
      simp only [outputHit, ProfileProof.inducedFamily, hv, true_and]
      rfl
  · simp only [Protocol.chain, executionVerify, Bool.and_eq_true, decide_eq_true_eq,
      hd, false_and, indicator, if_false, mean_const]

end RecursivePolygero.Protocol.HahnProfileProof
