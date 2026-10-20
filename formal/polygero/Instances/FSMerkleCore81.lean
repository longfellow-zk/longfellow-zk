import polygero.Instances.FSCompletion81
import polygero.Recursion.FSRootAnalysis
import polygero.Recursion.FSRootTerminal
import polygero.Recursion.FSRootCommit
import polygero.Recursion.FSRootCapacity
import polygero.Recursion.FSCoreQuery
import polygero.Instances.FSCoreSpectrum

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSMerkleCore81
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

/-- The checked instance fixes only the child price of the generic analysis. -/
abbrev AnalysisAt (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (rate : ℚ) :=
  MerkleFS.CoreAnalysis.AnalysisAt child p cp rate FSDefect81.childPrice

abbrev Analysis (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) :=
  AnalysisAt child p cp FSCoreData.rate

/-- Actual geometry discharges every algebraic price premise. -/
theorem analysis_exists (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance, Analysis child p cp := by
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
  refine ⟨p,cp,?_,?_,hcp,?_,?_⟩
  · intro σ W
    change mean (fun a => Bcs.StoppedPotential.repeatPrice FSCoreData.rate
      (refinedConditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ _
    rw [hcList]
    exact FSCoreSpectrum.actual_parent_mean_le I p σ W h0.length h0.dimension h0.masks
      h0.queries hpList hp hpTheta' hpMu hq
  · intro σ W
    have h := (mean_mono (coreQueryCapacity_le child p cp σ W)).trans (queryCapacity_mean_le child p cp hp σ W)
    rw [hpMu,hpTheta',hpList6,hcList6,hq] at h
    exact h.trans (by simpa only [FSCoreData.rate,FSCoreData.baseline,
      FSDefectData.baseline,Nat.cast_ofNat] using FSCoreData.checked.fresh)
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

theorem root_oracle_sound_at (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate : ℚ) (hr : 0 ≤ rate) (hchild : FSDefect81.childPrice ≤ rate)
    (ha : AnalysisAt child p cp rate) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨rate+FSDefect81.childPrice,rate,
        add_nonneg hr FSCompletion81.checked.2.2.2.2,hr⟩ :=
  MerkleFS.CoreAnalysis.root_oracle_sound_at child p cp rate FSDefect81.childPrice hr
    FSCompletion81.checked.2.2.2.2 hchild ha ctx σ

theorem root_failure_bound_at (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate : ℚ) (hr : 0 ≤ rate) (hchild : FSDefect81.childPrice ≤ rate)
    (ha : AnalysisAt child p cp rate) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) (MerkleFS.Candidate child (D := D)) N) :
    Bcs.FiniteProbability.density (fun H => MerkleFS.failure child ctx p cp σ (tree.run H).1 H) ≤
      rate+FSDefect81.childPrice+N*rate :=
  MerkleFS.CoreAnalysis.root_failure_bound_at child p cp rate FSDefect81.childPrice hr
    FSCompletion81.checked.2.2.2.2 hchild ha ctx σ tree

theorem root_oracle_sound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : Analysis child p cp) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨FSCoreData.rate+FSDefect81.childPrice,FSCoreData.rate,
        add_nonneg FSCoreData.checked.rate_nonneg FSCompletion81.checked.2.2.2.2,
        FSCoreData.checked.rate_nonneg⟩ :=
  root_oracle_sound_at child p cp FSCoreData.rate FSCoreData.checked.rate_nonneg
    FSCoreData.checked.child ha ctx σ

theorem root_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : Analysis child p cp) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) (MerkleFS.Candidate child (D := D)) N) :
    Bcs.FiniteProbability.density (fun H => MerkleFS.failure child ctx p cp σ (tree.run H).1 H) ≤
      FSCoreData.rate+FSDefect81.childPrice+N*FSCoreData.rate :=
  root_failure_bound_at child p cp FSCoreData.rate FSCoreData.checked.rate_nonneg
    FSCoreData.checked.child ha ctx σ tree

end RecursivePolygero.Instances.FSMerkleCore81
