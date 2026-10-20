import polygero.Instances.FSMerkleCore81
import polygero.Instances.FSShiftedSpectrum
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSShifted81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
theorem analysis_exists_with_child_data (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance, FSMerkleCore81.AnalysisAt child p cp FSShiftedData.rate ∧
      cp.columnCutoff = 2714 ∧ cp.threshold = FSTwoLevel.theta FSDefect81.childRow ∧
      cp.toProfileParameters.rankError = FSTwoLevel.rankError := by
  have hr := (FSWholeBlock81.checked .nonuniform).1
  have hc := (FSWholeBlock81.checked .nonuniform).2.1
  obtain ⟨p,hpCut,hpTheta,hpList,hpMu⟩ := FSWholeBlock81.certificate_with_cutoff I FSDefect81.parent 2 hr h0 hq
  obtain ⟨cp,hcCut,hcTheta,hcList,hcMu⟩ := FSWholeBlock81.certificate_with_cutoff child.instance FSDefect81.childRow 2 hc h1 hq
  obtain ⟨_,_,_,hpSmall,_⟩ := hr
  obtain ⟨_,_,_,hcSmall,_⟩ := hc
  have hp : p.listBound < Nat.card F := by rw [hpList,hq]; exact hpSmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList,hq]; exact hcSmall.2
  have hpList6 : p.listBound = 6 := hpList
  have hcList6 : cp.listBound = 6 := hcList
  have hpTheta' : p.threshold = FSStoppedSpectrum.theta 81 2714 := hpTheta
  have htau : (1-cp.threshold)*cp.toProfileParameters.rankError+2/(Nat.card F : ℚ)+cp.threshold = FSDefect81.childPrice := by
    rw [hcTheta,hcMu,hq]; rfl
  have hpi : FSDefect81.childPrice-cp.threshold =
      (1-cp.threshold)*cp.toProfileParameters.rankError+2/(Nat.card F : ℚ) := by linarith
  refine ⟨p,cp,?_,hcCut,hcTheta,hcMu⟩
  refine ⟨?_,?_,hcp,?_,?_⟩
  · intro σ W
    change mean (fun a => Bcs.StoppedPotential.repeatPrice FSShiftedData.rate
      (refinedConditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ _
    rw [hcList]
    exact FSShiftedSpectrum.actual_parent_mean_le I p σ W h0.length h0.dimension h0.masks
      h0.queries hpList hp hpTheta' hpMu hq
  · intro σ W
    have h := (mean_mono (coreQueryCapacity_le child p cp σ W)).trans (queryCapacity_mean_le child p cp hp σ W)
    rw [hpMu,hpTheta',hpList6,hcList6,hq] at h
    exact h.trans (by simpa only [FSShiftedData.rate,FSShiftedData.baseline,
      FSDefectData.baseline,Nat.cast_ofNat] using FSShiftedData.checked.fresh)
  · intro stmt V
    rw [hpi]
    let T := highSystems child.instance cp V
    have hT : T.card ≤ Nat.card F := (highSystems_card_le child.instance cp hcp V).trans hcp.le
    have hm := mean_mono (fun a => responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge child.instance cp
      stmt V a (fun _ => False) (coveredRigidResponses child.instance cp stmt V a (fun _ => False) T)
      T (fun _ => coveredRigidResponses_cover child.instance cp stmt V a (fun _ => False) T))
    have hb := fixed_rigidBlockCharge_mean_le (Z := Unit) child.instance cp (fun _ => stmt) V
      (fun _ _ => False) T hT 0 (by norm_num) (by intro g; simp [indicator])
      h1.length h1.dimension h1.masks hcCut
    simp only [mean_const,add_zero] at hb
    exact hm.trans hb
  · rw [hpi]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr cp.threshold_lt_one.le)
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)))
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))


theorem analysis_exists (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      FSMerkleCore81.AnalysisAt child p cp FSShiftedData.rate := by
  obtain ⟨p,cp,ha,_⟩ := analysis_exists_with_child_data child h0 h1 hq
  exact ⟨p,cp,ha⟩


end RecursivePolygero.Instances.FSShifted81
