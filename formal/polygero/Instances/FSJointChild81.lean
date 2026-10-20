import polygero.Recursion.FSRootComposition
import polygero.Recursion.FSRootSoundness
import polygero.Recursion.FSRootChildCompletion
import polygero.Instances.FSShifted81
import polygero.Instances.FSIOPReference81

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSJointChild81
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open FiatShamir.MerkleFS
open scoped Classical

def childSlope : ℚ := (1-FSTwoLevel.theta FSDefect81.childRow)*FSTwoLevel.rankError+
  2/(FSTwoLevel.fieldSize : ℚ)

/-- The old 2.622/q child price is still the intercept. Its slope can be
reduced to essentially 2/q, below the stronger complete IOP reference. -/
theorem checked :
    FSTwoLevel.theta FSDefect81.childRow+
      (1-FSTwoLevel.theta FSDefect81.childRow)/(FSTwoLevel.fieldSize : ℚ) ≤ 2/FSTwoLevel.fieldSize ∧
    childSlope+FSTwoLevel.theta FSDefect81.childRow = FSDefect81.childPrice ∧
    0 ≤ childSlope ∧ childSlope ≤ FSIOPReference81.strongIOPError ∧
    childSlope < FSDefect81.childPrice := by
  simp only [childSlope,FSDefect81.childPrice,FSWholeBlock81.childPrice,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,twoError,profile,FSTwoLevel.theta,
    FSDefect81.childRow,FSWholeBlock81.childRow,FSIntegerAffine.childRow,
    FSTwoLevel.rankError,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel


theorem checked_completion :
    FSTwoLevel.theta FSDefect81.childRow ≤ childSlope ∧
    profile FSTwoLevel.fieldSize FSTwoLevel.rankError (FSTwoLevel.theta FSDefect81.childRow) ≤ childSlope := by
  simp only [childSlope,profile,FSTwoLevel.theta,FSDefect81.childRow,FSWholeBlock81.childRow,
    FSIntegerAffine.childRow,FSTwoLevel.rankError,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

/-- Capacity certificate for the checked child geometry. The generic ROM
and charging theorems do not assume this geometry or the constant two. -/
theorem capacity_le_two (cp : HahnSystemCertificate child.instance)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hsmall : cp.listBound < Nat.card F) (hcut : cp.columnCutoff = 2714)
    (V : child.instance.layer.Oracle) :
    rigidExcessMass child.instance cp V+nonrigidMass child.instance cp V ≤ 2 := by
  have hT : (highSystems child.instance cp V).card ≤ Nat.card F :=
    (highSystems_card_le child.instance cp hsmall V).trans hsmall.le
  exact fixed_rigid_excess_add_nonrigid_count_le_two child.instance cp V
    (highSystems child.instance cp V) hT h1.length h1.dimension h1.masks hcut

theorem child_oracle_sound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hsmall : cp.listBound < Nat.card F)
    (hcut : cp.columnCutoff = 2714) (htheta : cp.threshold = FSTwoLevel.theta FSDefect81.childRow)
    (hmu : cp.toProfileParameters.rankError = FSTwoLevel.rankError) :
    OracleSound (MerkleFS.terminalDomain child)
      (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H)
      ⟨FSDefect81.childPrice,childSlope,FSCompletion81.checked.2.2.2.2,checked.2.2.1⟩ := by
  have hbase : cp.threshold+(1-cp.threshold)/(Nat.card F : ℚ) ≤ 2/Nat.card F := by
    rw [htheta,hq]; exact checked.1
  have h := MerkleFS.SplitChild.oracle_sound child ctx cp p σ 2 (by norm_num) hsmall
    (capacity_le_two child cp h1 hsmall hcut) hbase
  have hs : splitChildSlope child.instance cp 2 = childSlope := by rw [splitChildSlope,htheta,hmu,hq]; rfl
  simpa only [hs,htheta,checked.2.1] using h


/-- Joint completion removes the baseline from the intercept as well.
Only unread selected coordinates are completed, so the child block has
both ABS parameters at essentially two field units. -/
theorem child_oracle_sound_joint (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hsmall : cp.listBound < Nat.card F)
    (hcut : cp.columnCutoff = 2714) (htheta : cp.threshold = FSTwoLevel.theta FSDefect81.childRow)
    (hmu : cp.toProfileParameters.rankError = FSTwoLevel.rankError) :
    OracleSound (MerkleFS.terminalDomain child)
      (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H)
      (Rate.diagonal childSlope checked.2.2.1) := by
  have hslope : splitChildSlope child.instance cp 2 = childSlope := by rw [splitChildSlope,htheta,hmu,hq]; rfl
  have hbase : cp.threshold+(1-cp.threshold)/(Nat.card F : ℚ) ≤ 2/Nat.card F := by
    rw [htheta,hq]; exact checked.1
  simpa only [hslope] using MerkleFS.SplitChild.oracle_sound_joint_completion child ctx p cp σ
    2 (by norm_num) (capacity_le_two child cp h1 hsmall hcut) hsmall hbase

theorem root_oracle_sound_of_parent (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hsmall : cp.listBound < Nat.card F)
    (hcut : cp.columnCutoff = 2714) (htheta : cp.threshold = FSTwoLevel.theta FSDefect81.childRow)
    (hmu : cp.toProfileParameters.rankError = FSTwoLevel.rankError)
    (parentRate : Rate)
    (hparent : OracleSound (MerkleFS.queryDomain child)
      (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1) parentRate) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨parentRate.intercept+FSDefect81.childPrice,max parentRate.slope childSlope,
        add_nonneg parentRate.intercept_nonneg FSCompletion81.checked.2.2.2.2,
        parentRate.slope_nonneg.trans (le_max_left _ _)⟩ :=
  root_oracle_sound_of_blocks child p cp ctx σ parentRate hparent
    ⟨FSDefect81.childPrice,childSlope,FSCompletion81.checked.2.2.2.2,checked.2.2.1⟩
    (child_oracle_sound child p cp ctx σ h1 hq hsmall hcut htheta hmu)

theorem root_oracle_sound_joint_of_parent (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hsmall : cp.listBound < Nat.card F)
    (hcut : cp.columnCutoff = 2714) (htheta : cp.threshold = FSTwoLevel.theta FSDefect81.childRow)
    (hmu : cp.toProfileParameters.rankError = FSTwoLevel.rankError)
    (parentRate : Rate)
    (hparent : OracleSound (MerkleFS.queryDomain child)
      (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1) parentRate) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨parentRate.intercept+childSlope,max parentRate.slope childSlope,
        add_nonneg parentRate.intercept_nonneg checked.2.2.1,
        parentRate.slope_nonneg.trans (le_max_left _ _)⟩ :=
  root_oracle_sound_of_blocks child p cp ctx σ parentRate hparent
    (Rate.diagonal childSlope checked.2.2.1)
    (child_oracle_sound_joint child p cp ctx σ h1 hq hsmall hcut htheta hmu)

/-- All certificates are selected before the adversary or Merkle tape. -/
theorem certified_child (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      FSMerkleCore81.AnalysisAt child p cp FSShiftedData.rate ∧
      ∀ (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement),
        OracleSound (MerkleFS.terminalDomain child)
          (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H)
          (Rate.diagonal childSlope checked.2.2.1) := by
  obtain ⟨p,cp,ha,hcut,htheta,hmu⟩ := FSShifted81.analysis_exists_with_child_data child h0 h1 hq
  exact ⟨p,cp,ha,fun ctx σ => child_oracle_sound_joint child p cp ctx σ h1 hq ha.small hcut htheta hmu⟩

end RecursivePolygero.Instances.FSJointChild81
