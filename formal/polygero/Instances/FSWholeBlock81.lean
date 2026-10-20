import polygero.Recursion.FSWholeBlock
import polygero.Recursion.FSTerminalBlock
import polygero.Instances.FSBaselinePrice
import polygero.Instances.FSNonuniformSpectrum

/-! Complete actual two-level FS bounds at 81/80 openings. Parent prices
are proved capacity spectra. The last two roles use the whole-child-block
rigidity certificate, including all proper-system exceptions. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RecursivePolygero.Instances.FSWholeBlock81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock
open FSIntegerAffine (rowOk)
open scoped Classical

private theorem actual_field_error : FSTwoLevel.rankError + 1/(FSTwoLevel.fieldSize : ℚ) < 1 := by
  simp only [FSTwoLevel.rankError, FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose]
  decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The concrete constructor exposes its actual column cutoff, which the
payload-rigidity theorem needs in addition to threshold, list and rank. -/
theorem certificate_with_cutoff (I : Instance F) (r : FSTwoLevel.Row) (h : ℕ) (hr : rowOk r h)
    (hg : FSTwoLevel.Geometry I r) (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I,
      p.columnCutoff = r.cutoff ∧ p.threshold = FSTwoLevel.theta r ∧ p.listBound = r.list ∧
      p.toProfileParameters.rankError = FSTwoLevel.rankError := by
  obtain ⟨ht, hw, hgap, hsmall, hexcess⟩ := hr
  let profile : ProfileParameters I := {
    positive_degree := by have := hg.dimension; omega
    large_le := by simp only [hg.dimension, hg.masks, hg.length]; omega
    query_pos := by rw [hg.queries]; exact ht.1
    overlap_lt := by simp only [hg.dimension, hg.masks, hg.length]; omega }
  have hmu : profile.rankError = FSTwoLevel.rankError := by
    simp only [ProfileParameters.rankError, ProfileParameters.coreSize,
      hg.length, hg.dimension, hg.masks, hq, FSTwoLevel.rankError]
  have hover : profile.overlapSize = 639 := by
    simp [ProfileParameters.overlapSize, hg.dimension, hg.masks]
  have hlarge : profile.largeSize = 1088 := by
    simp [ProfileParameters.largeSize, ProfileParameters.coreSize, hg.dimension, hg.masks]
  have hb : CodingTheory.UniformFamilyBound I.n r.cutoff profile.overlapSize r.list := by
    rw [hg.length, hover]
    exact CodingTheory.IntegerOccupancy.uniformFamilyBound hgap
  have hcut : profile.largeSize ≤ r.cutoff := by rw [hlarge]; exact hw.1
  have hcutn : r.cutoff ≤ I.n := by rw [hg.length]; exact hw.2
  have hfloor : profile.columnFloorAt r.cutoff = FSTwoLevel.theta r := by
    simp only [ProfileParameters.columnFloorAt, hg.queries, hg.length, FSTwoLevel.theta]
  have htheta : FSTwoLevel.theta r < 1 := by
    rw [← hfloor]
    exact profile.columnFloorAt_lt_one (by omega) hcutn
  have he : DirectBinomial.HahnExcessCondition I.n I.t profile.overlapSize
      (Nat.card F) r.cutoff r.list (FSTwoLevel.theta r) := by
    rw [hg.length, hg.queries, hover, hq]
    apply Or.inr ∘ Or.inr
    refine ⟨1, le_rfl, ?_, ?_⟩
    · simpa only [Nat.min_eq_right hsmall.2.le] using hsmall.1
    · simpa only [Nat.min_eq_right hsmall.2.le] using hexcess
  let p := HahnSystemCertificate.ofUniformFamilyBound profile r.cutoff r.list
    (FSTwoLevel.theta r) hcut hcutn hb hfloor.le htheta he
      (by rw [hmu, hq]; exact actual_field_error)
  exact ⟨p, rfl, rfl, rfl, hmu⟩

inductive Schedule | unchanged | lowerCut | nonuniform

def parent : Schedule → FSTwoLevel.Row
  | .unchanged => FSBaselinePrice.row .unchanged
  | .lowerCut => FSBaselinePrice.row .lowerCut
  | .nonuniform => FSBaselinePrice.row .unchanged

def childRow : FSTwoLevel.Row := FSIntegerAffine.childRow .fixed

def price : Schedule → ℚ
  | .unchanged => FSBaselinePrice.rate .unchanged
  | .lowerCut => FSBaselinePrice.rate .lowerCut
  | .nonuniform => FSNonuniformData.rate

def childPrice : ℚ :=
  (1-FSTwoLevel.theta childRow)*FSTwoLevel.rankError +
    2/(FSTwoLevel.fieldSize : ℚ) + FSTwoLevel.theta childRow

omit [Fintype F] [DecidableEq F] in
private theorem childPrice_nonneg : 0 ≤ childPrice := by
  simp only [childPrice, FSTwoLevel.theta, childRow, FSIntegerAffine.childRow,
    FSTwoLevel.rankError, FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose]
  decide +kernel

omit [Fintype F] [DecidableEq F] in
/-- Exact price comparisons: the terminal block is cheaper than all three
proved parent prices. The strongest price is 4.8 field units. -/
theorem checked (s : Schedule) :
    FSIntegerAffine.rowOk (parent s) 2 ∧
    FSIntegerAffine.rowOk childRow 2 ∧
    0 ≤ price s ∧ childPrice ≤ price s := by
  cases s <;>
    simp only [FSIntegerAffine.rowOk, parent, childRow, FSIntegerAffine.childRow,
      FSBaselinePrice.row, price, FSBaselinePrice.rate, FSBaselinePrice.coefficient,
      FSNonuniformData.rate, childPrice, FSTwoLevel.theta,
      FSTwoLevel.rankError, FSTwoLevel.fieldSize, DiscreteThreshold.candidate,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

/-- Complete actual verifier/extractor failure theorem. Every parent and
child commitment can be adaptive; hash queries can occur in any order. -/
theorem certifiedAffineFS {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
          2*price s+childPrice + N*price s := by
  obtain ⟨hr, hc, hp0, hprice⟩ := checked s
  obtain ⟨p, hpCut, hpTheta, hpList, hpMu⟩ :=
    certificate_with_cutoff I (parent s) 2 hr h0 hq
  obtain ⟨cp, hcCut, hcTheta, hcList, hcMu⟩ :=
    certificate_with_cutoff child.instance childRow 2 hc h1 hq
  obtain ⟨_, _, _, hpSmall, _⟩ := hr
  obtain ⟨_, _, _, hcSmall, _⟩ := hc
  have hp : p.listBound < Nat.card F := by rw [hpList,hq]; exact hpSmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList,hq]; exact hcSmall.2
  have hcList6 : cp.listBound = 6 := hcList
  have ht : I.t = 81 := by
    rw [h0.queries]
    cases s <;> rfl
  have hover : p.overlapSize = 639 := by
    simp [ProfileParameters.overlapSize,h0.dimension,h0.masks]
  have hpTheta' : p.threshold = FSStoppedSpectrum.theta 81 (parent s).cutoff := by
    rw [hpTheta]
    cases s <;> rfl
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
      ⟨2*price s,price s,mul_nonneg (by norm_num) hp0,hp0⟩ := by
    cases s with
    | unchanged =>
      exact FSBaselinePrice.query_oracle_sound .unchanged child p cp hcp hcList6 σ
        h0.length ht hover hpList hp hpTheta' hpMu hq
    | lowerCut =>
      exact FSBaselinePrice.query_oracle_sound .lowerCut child p cp hcp hcList6 σ
        h0.length ht hover hpList hp hpTheta' hpMu hq
    | nonuniform =>
      exact FSNonuniformSpectrum.query_oracle_sound child p cp hcp hcList6 σ
        h0.length ht hover hpList hp hpTheta' hpMu hq
  have hchild : OracleSound (roleDomain child 2 ∪ roleDomain child 3)
      (residualFailure child p cp σ)
      (Rate.diagonal ((1-cp.threshold)*cp.toProfileParameters.rankError +
        2/(Nat.card F : ℚ) + cp.threshold) htau0) := by
    exact child_block_oracle_sound_fixed child cp p hcp h1.length h1.dimension
      h1.masks hcCut σ
  have hbound := whole_block_affine_bound child p cp σ (price s)
    ((1-cp.threshold)*cp.toProfileParameters.rankError + 2/(Nat.card F : ℚ) + cp.threshold)
    hp0 htau0 hparent hchild tree
  rw [htau, max_eq_left hprice] at hbound
  exact hbound

/-- A simpler affine bound with a three-query verifier offset. -/
theorem certifiedFS {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp σ (fun _ => False) H (tree.run H).1) ≤
          (N+3)*price s := by
  obtain ⟨p,cp,hbound⟩ := certifiedAffineFS child s h0 h1 hq
  refine ⟨p,cp,fun σ N tree => ?_⟩
  have h := hbound σ N tree
  have hp := (checked s).2.2.2
  nlinarith

/-- Actual false-statement acceptance inherits the full coefficient. -/
theorem certifiedSoundness {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child σ H (tree.run H).1) ≤
      (N+3)*price s := by
  obtain ⟨p,cp,hbound⟩ := certifiedFS child s h0 h1 hq
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

end RecursivePolygero.Instances.FSWholeBlock81
