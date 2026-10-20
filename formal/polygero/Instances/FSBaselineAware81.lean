import polygero.Instances.FSBaselineAwareSpectrum
import polygero.Instances.FSIOPReference81

/-! A strict improvement of the query rate, with both IOP references made
explicit. All statements concern the same typed 81/80 verifier. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RecursivePolygero.Instances.FSBaselineAware81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock FSDefect81
open scoped Classical

def price : ℚ := FSBaselineAwareData.rate

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Both the improved affine bound and the no-grinding bound, for actual
certificates and arbitrary full-oracle adaptive provers. -/
theorem certifiedBounds {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      let probability := Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1)
      probability ≤ price+childPrice+N*price ∧ (N = 0 → probability ≤ FSIOPReference81.strongIOPError) := by
  have hr := (FSWholeBlock81.checked .nonuniform).1
  have hc := (FSWholeBlock81.checked .nonuniform).2.1
  obtain ⟨p,hpCut,hpTheta,hpList,hpMu⟩ :=
    FSWholeBlock81.certificate_with_cutoff I parent 2 hr h0 hq
  obtain ⟨cp,hcCut,hcTheta,hcList,hcMu⟩ :=
    FSWholeBlock81.certificate_with_cutoff child.instance childRow 2 hc h1 hq
  obtain ⟨_,_,_,hpSmall,_⟩ := hr
  obtain ⟨_,_,_,hcSmall,_⟩ := hc
  have hp : p.listBound < Nat.card F := by rw [hpList,hq]; exact hpSmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList,hq]; exact hcSmall.2
  have hpList6 : p.listBound = 6 := hpList
  have hcList6 : cp.listBound = 6 := hcList
  have ht : I.t = 81 := h0.queries
  have hpTheta' : p.threshold = FSStoppedSpectrum.theta 81 2714 := hpTheta
  have htau : (1-cp.threshold)*cp.toProfileParameters.rankError +
      2/(Nat.card F : ℚ) + cp.threshold = childPrice := by rw [hcTheta,hcMu,hq]; rfl
  have htau0 : 0 ≤ (1-cp.threshold)*cp.toProfileParameters.rankError +
      2/(Nat.card F : ℚ) + cp.threshold := by rw [htau]; exact FSCompletion81.checked.2.2.2.2
  refine ⟨p,cp,fun σ N tree => ?_⟩
  constructor
  · have hparent : OracleSound (queryBlockDomain child)
        (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
        (Rate.diagonal price FSBaselineAwareData.checked.rate_nonneg) := by
      apply query_joint_oracle_sound child p cp hcp σ price FSBaselineAwareData.checked.rate_nonneg
      · intro W
        change mean (fun a => Bcs.StoppedPotential.repeatPrice price
          (StoppedSpectrum.conditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ price
        rw [hcList6]
        exact FSBaselineAwareSpectrum.actual_parent_mean_le I p σ W h0.length h0.dimension
          h0.masks ht hpList6 hp hpTheta' hpMu hq
      · intro W
        have h := queryCapacity_mean_le child p cp hp σ W
        rw [hpMu,hpTheta',hpList6,hcList6,hq] at h
        exact h.trans (by simpa only [price,FSBaselineAwareData.baseline,
          FSDefectData.baseline,Nat.cast_ofNat] using FSBaselineAwareData.checked.fresh)
    have hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
        (residualFailure child p cp σ)
        (Rate.diagonal ((1-cp.threshold)*cp.toProfileParameters.rankError +
          2/(Nat.card F : ℚ) + cp.threshold) htau0) :=
      child_block_oracle_sound_fixed child cp p hcp h1.length h1.dimension h1.masks hcCut σ
    have h := joint_whole_block_affine_bound child p cp σ price
      ((1-cp.threshold)*cp.toProfileParameters.rankError+2/(Nat.card F : ℚ)+cp.threshold)
      FSBaselineAwareData.checked.rate_nonneg htau0 hparent hchild tree
    rw [htau,max_eq_left (show childPrice ≤ price from FSBaselineAwareData.checked.child)] at h
    exact h
  · intro hz
    subst N
    cases tree with
    | done d =>
      exact FSIOPReference81.fixed_failure_le_strongIOP child h0 h1 hq p cp σ d


theorem checked_strong :
    2*price+childPrice ≤ 2*(2641/1000 : ℚ)*FSIOPReference81.strongIOPError ∧
    price ≤ (2641/1000 : ℚ)*FSIOPReference81.strongIOPError ∧
    0 ≤ FSIOPReference81.strongIOPError := by
  simp only [price,FSBaselineAwareData.rate,childPrice,FSWholeBlock81.childPrice,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,twoError,profile,FSTwoLevel.theta,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,
    FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

/-- One comparison lemma handles both the working cutoff2714 IOP error
and the stronger IOP certificate for the same actual extractor. -/
theorem certifiedFailure_comparison {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (K reference : ℚ)
    (hzero : FSIOPReference81.strongIOPError ≤ K*reference)
    (hfirst : 2*price+childPrice ≤ 2*K*reference) (hslope : price ≤ K*reference) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
        K*(N+1)*reference := by
  obtain ⟨p,cp,hb⟩ := certifiedBounds child h0 h1 hq
  refine ⟨p,cp,fun σ N tree => ?_⟩
  obtain ⟨ha,hz⟩ := hb σ N tree
  by_cases hn : N = 0
  · have h := (hz hn).trans hzero
    subst N
    simpa only [Nat.cast_zero,zero_add,mul_one] using h
  · have hN : (1 : ℚ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hslope)]

theorem certifiedSoundness_comparison {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (K reference : ℚ)
    (hzero : FSIOPReference81.strongIOPError ≤ K*reference)
    (hfirst : 2*price+childPrice ≤ 2*K*reference) (hslope : price ≤ K*reference)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      K*(N+1)*reference := by
  obtain ⟨p,cp,hb⟩ := certifiedFailure_comparison child h0 h1 hq K reference hzero hfirst hslope
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H (tree.run H).1 ↔ accepts child σ H (tree.run H).1 := by
    constructor
    · exact fun h => h.1
    · intro ha
      rw [failure_empty_iff]
      refine ⟨ha, ?_⟩
      cases hh : (twoProof child p cp).run σ (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
  have heq : (fun H => accepts child σ H (tree.run H).1) =
      (fun H => failure child p cp σ (fun _ => False) H (tree.run H).1) := by
    funext H
    exact propext (he H).symm
  rw [heq]
  exact hb σ N tree

theorem certifiedSoundness_workingIOP {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      (1871/1000 : ℚ)*(N+1)*sameIOPError := by
  apply certifiedSoundness_comparison child h0 h1 hq (1871/1000) sameIOPError ?_
    FSBaselineAwareData.checked.iop_intercept FSBaselineAwareData.checked.iop_slope σ hfalse tree
  have hh := FSIOPReference81.checked.2.2.2.2.2
  have he := checked_strong.2.2
  nlinarith

theorem certifiedSoundness_strongIOP {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      (2641/1000 : ℚ)*(N+1)*FSIOPReference81.strongIOPError := by
  apply certifiedSoundness_comparison child h0 h1 hq (2641/1000) FSIOPReference81.strongIOPError ?_
    checked_strong.1 checked_strong.2.1 σ hfalse tree
  linarith [checked_strong.2.2]

end RecursivePolygero.Instances.FSBaselineAware81
