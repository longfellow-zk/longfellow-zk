import polygero.Instances.FSWholeBlock81
import polygero.Instances.FSDefectSpectrum

/-! Complete clean 126-bit two-level FS bound with unchanged 81/80
openings and the actual integer-occupancy cutoff2714/list6 certificates. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RecursivePolygero.Instances.FSDefect81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock
open scoped Classical

def parent : FSTwoLevel.Row := FSWholeBlock81.parent .nonuniform
def childRow : FSTwoLevel.Row := FSWholeBlock81.childRow
def price : ℚ := 1/(2^126 : ℚ)
def childPrice : ℚ := FSWholeBlock81.childPrice

theorem rate_eq : FSDefectData.rate = price := by
  norm_num [FSDefectData.rate, FSTwoLevel.fieldSize, price]

/-- Exact price comparison includes the terminal rank cross term. -/
theorem checked : 0 ≤ price ∧ childPrice ≤ price := by
  simp only [price,childPrice,FSWholeBlock81.childPrice,FSTwoLevel.theta,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,
    FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem childPrice_nonneg : 0 ≤ childPrice := by
  simp only [childPrice,FSWholeBlock81.childPrice,FSTwoLevel.theta,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,
    FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

/-- Interactive error of exactly the same two cutoff2714 certificates. -/
def sameIOPError : ℚ :=
  twoError (ProfileAnalysis.profile FSTwoLevel.fieldSize FSTwoLevel.rankError
    (FSTwoLevel.theta parent))
    (ProfileAnalysis.profile FSTwoLevel.fieldSize FSTwoLevel.rankError
      (FSTwoLevel.theta childRow))

/-- Field-unit comparison, independent of decimal bit displays. -/
theorem sameIOPError_bounds :
    (28239/10000 : ℚ)/FSTwoLevel.fieldSize ≤ sameIOPError ∧
    sameIOPError ≤ (2824/1000 : ℚ)/FSTwoLevel.fieldSize := by
  simp only [sameIOPError,twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
    parent,FSWholeBlock81.parent,FSBaselinePrice.row,childRow,FSWholeBlock81.childRow,
    FSIntegerAffine.childRow,FSTwoLevel.rankError,FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose]
  decide +kernel

/-- A uniform two-bit comparison to the same IOP certificates. Keeping
this affine intercept matters at N=0; the coarser three-query offset
alone would not justify the same comparison. -/
theorem checked_iop_comparison :
    2*price+childPrice ≤ 4*sameIOPError ∧ price ≤ 4*sameIOPError := by
  simp only [price,childPrice,FSWholeBlock81.childPrice,sameIOPError,twoError,
    ProfileAnalysis.profile,FSTwoLevel.theta,parent,FSWholeBlock81.parent,
    FSBaselinePrice.row,childRow,FSWholeBlock81.childRow,FSIntegerAffine.childRow,
    FSTwoLevel.rankError,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The displayed reference is the actual recursive IOP certificate,
not a different row or a sum that dropped its cross term. -/
theorem actual_iop_error {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (hpTheta : p.threshold = FSTwoLevel.theta parent)
    (hcTheta : cp.threshold = FSTwoLevel.theta childRow)
    (hpMu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hcMu : cp.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    twoError p.error cp.error = sameIOPError := by
  simp only [HahnSystemCertificate.error]
  rw [hpTheta,hcTheta,hpMu,hcMu,hq]
  rfl

/-- The actual verifier/extractor failure bound retains its exact affine
intercept. Defect-sensitive exception prices and whole-child charging
are composed over disjoint domains, for arbitrary adaptive query order. -/
theorem certifiedAffineFS {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
          2*price+childPrice + N*price := by
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
      2/(Nat.card F : ℚ) + cp.threshold = childPrice := by
    rw [hcTheta,hcMu,hq]; rfl
  have htau0 : 0 ≤ (1-cp.threshold)*cp.toProfileParameters.rankError +
      2/(Nat.card F : ℚ) + cp.threshold := by
    rw [htau]
    exact childPrice_nonneg
  refine ⟨p,cp,fun σ N tree => ?_⟩
  have hparent : OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*price,price,mul_nonneg (by norm_num) checked.1,checked.1⟩ := by
    have h := FSDefectSpectrum.query_oracle_sound child p cp hcp hcList6 σ
      h0.length h0.dimension h0.masks ht hpList6 hp hpTheta' hpMu hq
    simpa only [rate_eq] using h
  have hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
      (residualFailure child p cp σ)
      (Rate.diagonal ((1-cp.threshold)*cp.toProfileParameters.rankError +
        2/(Nat.card F : ℚ) + cp.threshold) htau0) :=
    child_block_oracle_sound_fixed child cp p hcp h1.length h1.dimension h1.masks hcCut σ
  have hbound := whole_block_affine_bound child p cp σ price
    ((1-cp.threshold)*cp.toProfileParameters.rankError + 2/(Nat.card F : ℚ) + cp.threshold)
    checked.1 htau0 hparent hchild tree
  rw [htau,max_eq_left checked.2] at hbound
  exact hbound

/-- Complete clean 126-bit certificate at the existing 81/80 schedule. -/
theorem certifiedFS {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
          (N+3)*(1/(2^126 : ℚ)) := by
  obtain ⟨p,cp,hbound⟩ := certifiedAffineFS child h0 h1 hq
  refine ⟨p,cp,fun σ N tree => ?_⟩
  have h := hbound σ N tree
  have hp := checked.2
  change _ ≤ (N+3)*price
  nlinarith

/-- False-statement acceptance has the same clean 126-bit coefficient. -/
theorem certifiedSoundness {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      (N+3)*(1/(2^126 : ℚ)) := by
  obtain ⟨p,cp,hbound⟩ := certifiedFS child h0 h1 hq
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H (tree.run H).1 ↔
        accepts child σ H (tree.run H).1 := by
    rw [failure_empty_iff]
    have hn : (twoProof child p cp).run σ (tree.run H).1.1
        (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) = none := by
      cases hh : (twoProof child p cp).run σ (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
    simp only [hn,and_true]
  simpa only [he] using hbound σ N tree

/-- The sharper affine acceptance bound, retaining the verifier intercept. -/
theorem certifiedAffineSoundness {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      2*price+childPrice+N*price := by
  obtain ⟨p,cp,hbound⟩ := certifiedAffineFS child h0 h1 hq
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H (tree.run H).1 ↔
        accepts child σ H (tree.run H).1 := by
    rw [failure_empty_iff]
    have hn : (twoProof child p cp).run σ (tree.run H).1.1
        (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) = none := by
      cases hh : (twoProof child p cp).run σ (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
    simp only [hn,and_true]
  simpa only [he] using hbound σ N tree

/-- For every ROM budget, including zero, the complete recursive FS
bound loses at most two bits relative to its same-certificate IOP error. -/
theorem certifiedSoundness_iop {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I parent)
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      4*(N+1)*sameIOPError := by
  have h := certifiedAffineSoundness child h0 h1 hq σ hfalse tree
  have hN := mul_le_mul_of_nonneg_left checked_iop_comparison.2 (Nat.cast_nonneg N)
  nlinarith [checked_iop_comparison.1]

end RecursivePolygero.Instances.FSDefect81
