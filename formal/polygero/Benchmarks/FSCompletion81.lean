import polygero.Benchmarks.FSDefect81
import polygero.Recursion.FSJointCompletion

/-! Joint verifier completion at the unchanged 81/80 schedule. The full
same-certificate IOP comparison is below one bit, including zero queries. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace RecursivePolygero.Benchmarks.FSCompletion81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock FSDefect81
open scoped Classical

/-- Exact field arithmetic for the fresh pair and both comparison forms. -/
theorem checked :
    FSTwoLevel.rankError + 6*FSTwoLevel.theta parent +
      (1-FSTwoLevel.theta parent+6*FSTwoLevel.theta parent)/FSTwoLevel.fieldSize ≤ price ∧
    price+childPrice ≤ (2345/1000 : ℚ)*sameIOPError ∧
    2*price+childPrice ≤ 2*(1881/1000 : ℚ)*sameIOPError ∧
    price ≤ (1881/1000 : ℚ)*sameIOPError ∧ 0 ≤ childPrice := by
  simp only [price,childPrice,FSWholeBlock81.childPrice,sameIOPError,twoError,
    ProfileAnalysis.profile,FSTwoLevel.theta,parent,FSWholeBlock81.parent,
    FSBaselinePrice.row,childRow,FSWholeBlock81.childRow,FSIntegerAffine.childRow,
    FSTwoLevel.rankError,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

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
      probability ≤ price+childPrice+N*price ∧ (N = 0 → probability ≤ sameIOPError) := by
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
  have hiop := actual_iop_error child p cp hpTheta hcTheta hpMu hcMu hq
  have htau : (1-cp.threshold)*cp.toProfileParameters.rankError +
      2/(Nat.card F : ℚ) + cp.threshold = childPrice := by rw [hcTheta,hcMu,hq]; rfl
  have htau0 : 0 ≤ (1-cp.threshold)*cp.toProfileParameters.rankError +
      2/(Nat.card F : ℚ) + cp.threshold := by rw [htau]; exact checked.2.2.2.2
  refine ⟨p,cp,fun σ N tree => ?_⟩
  constructor
  · have hparent : OracleSound (queryBlockDomain child)
        (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
        (Rate.diagonal price FSDefect81.checked.1) := by
      apply query_joint_oracle_sound child p cp hcp σ price FSDefect81.checked.1
      · intro W
        change mean (fun a => Bcs.StoppedPotential.repeatPrice price
          (StoppedSpectrum.conditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ price
        rw [hcList6, ← rate_eq]
        exact FSDefectSpectrum.actual_parent_mean_le I p σ W h0.length h0.dimension
          h0.masks ht hpList6 hp hpTheta' hpMu hq
      · intro W
        have h := queryCapacity_mean_le child p cp hp σ W
        rw [hpMu,hpTheta,hpList,hcList,hq] at h
        exact h.trans checked.1
    have hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
        (residualFailure child p cp σ)
        (Rate.diagonal ((1-cp.threshold)*cp.toProfileParameters.rankError +
          2/(Nat.card F : ℚ) + cp.threshold) htau0) :=
      child_block_oracle_sound_fixed child cp p hcp h1.length h1.dimension h1.masks hcCut σ
    have h := joint_whole_block_affine_bound child p cp σ price
      ((1-cp.threshold)*cp.toProfileParameters.rankError+2/(Nat.card F : ℚ)+cp.threshold)
      FSDefect81.checked.1 htau0 hparent hchild tree
    rw [htau,max_eq_left FSDefect81.checked.2] at h
    exact h
  · intro hz
    subst N
    cases tree with
    | done d =>
      have h := fixed_failure_le_iop child p cp σ d
      rw [hiop] at h
      exact h

/-- The clean affine display now uses two verifier offsets instead of three. -/
theorem certifiedFS {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1) ≤ (N+2)*price := by
  obtain ⟨p,cp,hb⟩ := certifiedBounds child h0 h1 hq
  refine ⟨p,cp,fun σ N tree => ?_⟩
  have h := (hb σ N tree).1
  linarith [FSDefect81.checked.2]

/-- The exact complete bound is within 1.881 times `(N+1)` IOP error.
This is less than one bit for every query budget, including zero. -/
theorem certifiedFailure_iop {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
        (1881/1000 : ℚ)*(N+1)*sameIOPError := by
  obtain ⟨p,cp,hb⟩ := certifiedBounds child h0 h1 hq
  refine ⟨p,cp,fun σ N tree => ?_⟩
  obtain ⟨ha,hzero⟩ := hb σ N tree
  by_cases hz : N = 0
  · have h := hzero hz
    subst N
    have he : 0 ≤ sameIOPError := by
      exact (by positivity : (0 : ℚ) ≤ (28239/10000 : ℚ)/FSTwoLevel.fieldSize).trans
        sameIOPError_bounds.1
    norm_num only [Nat.cast_zero, zero_add, mul_one]
    linarith
  · have hn : (1 : ℚ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hs := checked.2.2.2.1
    have hi := checked.2.2.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hs)]

theorem certifiedSoundness_iop {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      (1881/1000 : ℚ)*(N+1)*sameIOPError := by
  obtain ⟨p,cp,hb⟩ := certifiedFailure_iop child h0 h1 hq
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H (tree.run H).1 ↔ accepts child σ H (tree.run H).1 := by
    rw [failure_empty_iff]
    have hn : (twoProof child p cp).run σ (tree.run H).1.1
        (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) = none := by
      cases hh : (twoProof child p cp).run σ (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
    simp only [hn,and_true]
  simpa only [he] using hb σ N tree

end RecursivePolygero.Benchmarks.FSCompletion81
