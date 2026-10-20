import polygero.Recursion.FSRootComposition
import polygero.Instances.FSBaselineAware81
import polygero.Recursion.FSRootTerminal
import polygero.Recursion.FSRootCommit

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSMerkle81
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

/-- Numerical certificate fields, independent of all Merkle tapes and contexts. -/
structure Analysis (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) : Prop where
  root : ∀ σ W, mean (fun a => Bcs.StoppedPotential.repeatPrice FSBaselineAware81.price
    (queryCapacity child p cp σ W a)) ≤ FSBaselineAware81.price
  fresh : ∀ σ W, mean (queryCapacity child p cp σ W) ≤ FSBaselineAware81.price
  small : cp.listBound < Nat.card F
  childMean : ∀ (stmt : child.instance.layer.Statement) (V : child.instance.layer.Oracle),
    mean (fun a => responseIncidence child.instance cp stmt V a
      (coveredRigidResponses child.instance cp stmt V a (fun _ => False)
        (highSystems child.instance cp V)) - cp.threshold +
      indicator (nonrigidException child.instance cp stmt V (highSystems child.instance cp V) a)) ≤
      FSDefect81.childPrice-cp.threshold
  child_nonneg : 0 ≤ FSDefect81.childPrice-cp.threshold

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
    change mean (fun a => Bcs.StoppedPotential.repeatPrice FSBaselineAware81.price
      (StoppedSpectrum.conditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ _
    rw [hcList]
    exact FSBaselineAwareSpectrum.actual_parent_mean_le I p σ W h0.length h0.dimension h0.masks
      h0.queries hpList hp hpTheta' hpMu hq
  · intro σ W
    have h := queryCapacity_mean_le child p cp hp σ W
    rw [hpMu,hpTheta',hpList6,hcList6,hq] at h
    exact h.trans (by simpa only [FSBaselineAware81.price,FSBaselineAwareData.baseline,
      FSDefectData.baseline,Nat.cast_ofNat] using FSBaselineAwareData.checked.fresh)
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

/-- Uniform root-context ABS transports the numerical capacity spectrum
without assuming that a child commitment is fixed before the parent coin. -/
theorem root_oracle_sound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : Analysis child p cp) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement) :
    OracleSound univ (MerkleFS.failure child ctx p cp σ)
      ⟨FSBaselineAware81.price+FSDefect81.childPrice,FSBaselineAware81.price,
        add_nonneg FSBaselineAwareData.checked.rate_nonneg FSCompletion81.checked.2.2.2.2,
        FSBaselineAwareData.checked.rate_nonneg⟩ := by
  have hp := MerkleFS.query_oracle_sound child ctx p cp σ FSBaselineAware81.price
    FSBaselineAwareData.checked.rate_nonneg ha.small (ha.root σ) (ha.fresh σ)
  have hc : OracleSound (MerkleFS.terminalDomain child)
      (fun d H => MerkleFS.failure child ctx p cp σ d H ∧ ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H)
      (Rate.diagonal FSDefect81.childPrice FSCompletion81.checked.2.2.2.2) := by
    have h := MerkleFS.child_oracle_sound child ctx cp p σ (FSDefect81.childPrice-cp.threshold)
      ha.child_nonneg ha.childMean
    simpa only [sub_add_cancel] using h
  have hm : FSDefect81.childPrice ≤ FSBaselineAware81.price := FSBaselineAwareData.checked.child
  simpa only [Rate.diagonal,max_eq_left hm] using
    MerkleFS.root_oracle_sound_of_blocks child p cp ctx σ
      (Rate.diagonal FSBaselineAware81.price FSBaselineAwareData.checked.rate_nonneg) hp
      (Rate.diagonal FSDefect81.childPrice FSCompletion81.checked.2.2.2.2) hc

theorem root_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : Analysis child p cp) (ctx : MerkleFS.Context child (D := D)) (σ : I.layer.Statement)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) (MerkleFS.Candidate child (D := D)) N) :
    Bcs.FiniteProbability.density (fun H => MerkleFS.failure child ctx p cp σ (tree.run H).1 H) ≤
      FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price := by
  have h := root_oracle_sound child p cp ha ctx σ N tree
  have hc : ∀ H, queryCost (univ : Finset (MerkleFS.Point child (D := D))) tree H ≤ (N : ℚ) := by
    clear h
    intro H
    induction tree with
    | done => simp [queryCost]
    | query q next ih => simpa only [queryCost,mem_univ,if_true,Nat.cast_add,Nat.cast_one,add_comm]
        using add_le_add_left (ih (H q)) 1
  simpa only [mul_comm] using h.cap N hc

end RecursivePolygero.Instances.FSMerkle81
