import polygero.Local.RigidResponseIncidence

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace RecursivePolygero.ProfileAnalysis
open Finset Counting Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def rigidExcessMass (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) : ℚ :=
  ∑ d ∈ (highSystems I p W).filter (RigidSystem I p W), max 0 (systemCap I W d-p.threshold)

noncomputable def nonrigidMass (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) : ℚ :=
  ((highSystems I p W).filter (fun d => ¬ RigidSystem I p W d)).card

noncomputable def rigidBudget (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) : ℚ :=
  (1-p.threshold)*p.toProfileParameters.rankError + rigidExcessMass I p W/Nat.card F

noncomputable def nonrigidBudget (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) : ℚ := nonrigidMass I p W/Nat.card F

/-- The geometry enters only through a nonnegative capacity constant `C`. -/
noncomputable def splitChildSlope (I : Instance F) (p : HahnSystemCertificate I) (C : ℚ) : ℚ :=
  (1-p.threshold)*p.toProfileParameters.rankError+C/Nat.card F

theorem splitChildSlope_nonneg (I : Instance F) (p : HahnSystemCertificate I) (C : ℚ)
    (hC : 0 ≤ C) : 0 ≤ splitChildSlope I p C := by
  have ht := sub_nonneg.mpr p.threshold_lt_one.le
  unfold splitChildSlope ProfileParameters.rankError
  positivity

theorem splitChildSlope_mono (I : Instance F) (p : HahnSystemCertificate I)
    {C C' : ℚ} (h : C ≤ C') : splitChildSlope I p C ≤ splitChildSlope I p C' :=
  add_le_add le_rfl (div_le_div_of_nonneg_right h (show (0 : ℚ) ≤ Nat.card F from Nat.cast_nonneg _))

/-- The same baseline inequality pays the fresh local error, so joint
completion needs no additional numerical soundness premise. -/
theorem error_le_splitChildSlope (I : Instance F) (p : HahnSystemCertificate I) (C : ℚ)
    (hbase : p.threshold+(1-p.threshold)/(Nat.card F : ℚ) ≤ C/Nat.card F) :
    p.error ≤ splitChildSlope I p C := by
  unfold HahnSystemCertificate.error profile splitChildSlope
  calc
    _ = (1-p.threshold)*p.toProfileParameters.rankError+
        (p.threshold+(1-p.threshold)/(Nat.card F : ℚ)) := by ring
    _ ≤ _ := add_le_add le_rfl hbase

theorem threshold_le_splitChildSlope (I : Instance F) (p : HahnSystemCertificate I) (C : ℚ)
    (hbase : p.threshold+(1-p.threshold)/(Nat.card F : ℚ) ≤ C/Nat.card F) :
    p.threshold ≤ splitChildSlope I p C := by
  have hr : 0 ≤ (1-p.threshold)*p.toProfileParameters.rankError := by
    have ht := sub_nonneg.mpr p.threshold_lt_one.le
    unfold ProfileParameters.rankError
    positivity
  have ht : 0 ≤ (1-p.threshold)/(Nat.card F : ℚ) :=
    div_nonneg (sub_nonneg.mpr p.threshold_lt_one.le) (by positivity)
  unfold splitChildSlope
  linarith

theorem rigidBudget_nonneg (I : Instance F) (p : HahnSystemCertificate I) (W : I.layer.Oracle) :
    0 ≤ rigidBudget I p W := by
  have ht := sub_nonneg.mpr p.threshold_lt_one.le
  unfold rigidBudget rigidExcessMass ProfileParameters.rankError
  positivity

theorem nonrigidBudget_nonneg (I : Instance F) (p : HahnSystemCertificate I) (W : I.layer.Oracle) :
    0 ≤ nonrigidBudget I p W := by unfold nonrigidBudget nonrigidMass; positivity

/-- The rigid part is priced separately from the nonrigid Boolean event.
Their separate worst cases will not be added in the shared-query load. -/
theorem rigid_response_excess_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun a => responseIncidence I p σ W a
      (coveredRigidResponses I p σ W a (fun _ => False) (highSystems I p W))-p.threshold) ≤
        rigidBudget I p W := by
  let T := highSystems I p W
  let R := T.filter (RigidSystem I p W)
  have hp (a : I.layer.Coin) : responseIncidence I p σ W a
      (coveredRigidResponses I p σ W a (fun _ => False) T)-p.threshold ≤
      (1-p.threshold)*indicator (a.2 ∈ ReducedSystems.badChallenges
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask) +
        ∑ d ∈ R, max 0 (systemCap I W d-p.threshold)*
          indicator (a ∈ systemExceptions p.positive_degree I.layout σ d) := by
    have h := responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge I p σ W a
      (fun _ => False) _ T (fun _ => coveredRigidResponses_cover I p σ W a (fun _ => False) T)
    have hz (d : systems I.domain I.primary_le W) :
        ¬ systemTarget I p.positive_degree W (fun _ => False) d := by rintro ⟨_,h⟩; exact h
    simp only [rigidBlockCharge, rigidExceptionExcess, indicator, hz, if_false, mul_zero,
      sum_const_zero, add_zero] at h
    dsimp only [R]
    dsimp only [indicator]
    linarith
  have he : mean (fun a : I.layer.Coin => ∑ d ∈ R, max 0 (systemCap I W d-p.threshold)*
      indicator (a ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
        rigidExcessMass I p W/Nat.card F := by
    rw [SystemException.mean_finset_sum]
    simp_rw [mean_mul_left]
    calc
      _ ≤ ∑ d ∈ R, max 0 (systemCap I W d-p.threshold)*(1/Nat.card F) :=
        sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (systemExceptions_mean I p.toProfileParameters σ W d) (le_max_left _ _))
      _ = _ := by rw [← sum_mul]; simp only [rigidExcessMass,R,T,div_eq_mul_inv,one_mul]
  refine (mean_mono hp).trans ?_
  rw [mean_add,mean_mul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left (rank_bad_mean I p.toProfileParameters W)
    (sub_nonneg.mpr p.threshold_lt_one.le)) he

/-- Shared child-challenge loads consume rigid excess and nonrigid systems
jointly. This theorem is independent of field size, openings, and geometry. -/
theorem split_budget_joint_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (C : ℚ)
    (hcapacity : rigidExcessMass I p W+nonrigidMass I p W ≤ C) :
    rigidBudget I p W+nonrigidBudget I p W ≤ splitChildSlope I p C := by
  have hd := div_le_div_of_nonneg_right hcapacity
    (show (0 : ℚ) ≤ Nat.card F by positivity)
  simpa only [rigidBudget,nonrigidBudget,splitChildSlope,add_div,
    add_assoc,add_comm,add_left_comm] using
      add_le_add_left hd ((1-p.threshold)*p.toProfileParameters.rankError)

theorem split_budget_terminal_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (C : ℚ) (hsmall : p.listBound < Nat.card F)
    (hbase : p.threshold+(1-p.threshold)/(Nat.card F : ℚ) ≤ C/Nat.card F) :
    rigidBudget I p W+p.threshold ≤ splitChildSlope I p C := by
  have h := systemCap_excess_of_hahn I p W ((highSystems I p W).filter (RigidSystem I p W))
    ((card_filter_le _ _).trans ((highSystems_card_le I p hsmall W).trans hsmall.le))
  have hd := div_le_div_of_nonneg_right h (show (0 : ℚ) ≤ Nat.card F by positivity)
  change rigidExcessMass I p W/(Nat.card F : ℚ) ≤ (1-p.threshold)/Nat.card F at hd
  unfold rigidBudget splitChildSlope
  linarith

end RecursivePolygero.ProfileAnalysis
