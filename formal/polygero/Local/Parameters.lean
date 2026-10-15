import polygero.Protocol.Instance
import polygero.Algebra.Counting.Envelope
import polygero.Algebra.Counting.DiscreteThreshold
import polygero.Algebra.Counting.BinomialExcess

/-! Structural parameters and exact rational certificates for each invocation. -/
namespace RecursivePolygero
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

structure ProfileParameters (I : Instance F) where
  positive_degree : 1 ≤ I.r+I.w
  large_le : max (I.r+I.w+I.s+I.s+1) (2*(I.r+I.w)+I.s) ≤ I.n
  query_pos : 1 ≤ I.t
  overlap_lt : I.r+I.w+2*I.s-1 < I.n

namespace ProfileParameters
variable {I : Instance F}
def coreSize (_ : ProfileParameters I) : ℕ := I.r+I.w+I.s+I.s+1
def largeSize (p : ProfileParameters I) : ℕ := max p.coreSize (2*(I.r+I.w)+I.s)
def overlapSize (_ : ProfileParameters I) : ℕ := I.r+I.w+2*I.s-1
def columnFloorAt (_ : ProfileParameters I) (w : ℕ) : ℚ := ((w-1).choose I.t : ℚ)/I.n.choose I.t
def columnFloor (p : ProfileParameters I) : ℚ := ((p.largeSize-1).choose I.t : ℚ)/I.n.choose I.t
def overlapRatio (p : ProfileParameters I) : ℚ := (p.overlapSize.choose I.t : ℚ)/I.n.choose I.t
noncomputable def rankError (p : ProfileParameters I) : ℚ :=
  (I.n.choose p.coreSize : ℚ)/(Nat.card F : ℚ)^(I.s+1)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem columnFloorAt_largeSize (p : ProfileParameters I) :
    p.columnFloorAt p.largeSize = p.columnFloor := rfl

omit [Fintype F] [DecidableEq F] in
theorem columnFloorAt_nonneg (p : ProfileParameters I) (w : ℕ) : 0 ≤ p.columnFloorAt w := by
  unfold columnFloorAt
  positivity

omit [Fintype F] [DecidableEq F] in
theorem columnFloor_le_columnFloorAt (p : ProfileParameters I) {w : ℕ}
    (hw : p.largeSize ≤ w) : p.columnFloor ≤ p.columnFloorAt w := by
  unfold columnFloor columnFloorAt
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_choose I.t (Nat.sub_le_sub_right hw 1)) (by positivity)

omit [Fintype F] [DecidableEq F] in
theorem columnFloor_nonneg (p : ProfileParameters I) : 0 ≤ p.columnFloor := by
  unfold columnFloor
  positivity

private theorem choose_ratio_lt_one {a n t : ℕ} (ha : a < n)
    (ht : 1 ≤ t) (htn : t ≤ n) : (a.choose t : ℚ)/n.choose t < 1 := by
  have hm := Nat.choose_le_choose t (show a ≤ n-1 by omega)
  have hp := Nat.choose_pos (show t-1 ≤ n-1 by omega)
  have he : n.choose t = (n-1).choose (t-1)+(n-1).choose t := by
    have h := Nat.choose_succ_succ' (n-1) (t-1)
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega),Nat.sub_add_cancel ht] using h
  apply (div_lt_one (by exact_mod_cast Nat.choose_pos htn)).mpr
  exact_mod_cast (show a.choose t < n.choose t by omega)

omit [Fintype F] [DecidableEq F] in
theorem columnFloorAt_lt_one (p : ProfileParameters I) {w : ℕ}
    (hwpos : 1 ≤ w) (hw : w ≤ I.n) : p.columnFloorAt w < 1 :=
  choose_ratio_lt_one (by omega) p.query_pos I.query_le

omit [Fintype F] [DecidableEq F] in
theorem columnFloor_lt_one (p : ProfileParameters I) : p.columnFloor < 1 := by
  apply choose_ratio_lt_one _ p.query_pos I.query_le
  have := p.large_le
  have := p.positive_degree
  unfold largeSize coreSize
  omega

omit [Fintype F] [DecidableEq F] in
theorem overlapRatio_lt_one (p : ProfileParameters I) : p.overlapRatio < 1 :=
  choose_ratio_lt_one p.overlap_lt p.query_pos I.query_le

end ProfileParameters

/-- The local cutoff is derived from the column bound and an integer incidence
cutoff. It is not a recursive witness-score parameter. -/
noncomputable def ProfileParameters.countingCutoff {I : Instance F}
    (p : ProfileParameters I) (u : ℕ) : ℚ :=
  max p.columnFloor (DiscreteThreshold.candidate (Nat.card F) u p.overlapRatio)

/-- Exact integer-cutoff and local-error certificates for one invocation. -/
structure ProfileCertificate (I : Instance F) extends ProfileParameters I where
  cutoff : ℕ
  cutoff_spec : DiscreteThreshold.IsLeastIndex (Nat.card F) toProfileParameters.overlapRatio cutoff
  field_error_lt_one : toProfileParameters.rankError+1/(Nat.card F : ℚ) < 1

namespace ProfileCertificate
variable {I : Instance F}
noncomputable def threshold (p : ProfileCertificate I) : ℚ := p.countingCutoff p.cutoff
noncomputable def error (p : ProfileCertificate I) : ℚ :=
  ProfileAnalysis.profile (Nat.card F) p.rankError p.threshold

omit [Fintype F] [DecidableEq F] in
theorem floor_le (p : ProfileCertificate I) : p.columnFloor ≤ p.threshold := le_max_left _ _

omit [Fintype F] [DecidableEq F] in
theorem threshold_nonneg (p : ProfileCertificate I) : 0 ≤ p.threshold :=
  p.columnFloor_nonneg.trans p.floor_le

omit [DecidableEq F] in
private theorem field_card_ge_two : 2 ≤ Nat.card F := by
  have h := Fintype.one_lt_card (α := F)
  rw [Nat.card_eq_fintype_card]
  omega

omit [Fintype F] [DecidableEq F] in
theorem cutoff_pos (p : ProfileCertificate I) : 1 ≤ p.cutoff := p.cutoff_spec.1

omit [DecidableEq F] in
theorem cutoff_le (p : ProfileCertificate I) : p.cutoff ≤ Nat.card F :=
  (p.cutoff_spec.le_pred field_card_ge_two p.overlapRatio_lt_one.le).trans (Nat.sub_le _ _)

omit [DecidableEq F] in
theorem threshold_lt_one (p : ProfileCertificate I) : p.threshold < 1 :=
  max_lt p.columnFloor_lt_one
    (p.cutoff_spec.candidate_lt_one field_card_ge_two p.overlapRatio_lt_one)

omit [DecidableEq F] in
theorem error_lt_one (p : ProfileCertificate I) : p.error < 1 := by
  have ht := p.threshold_lt_one
  have hf := p.field_error_lt_one
  unfold error ProfileAnalysis.profile
  nlinarith

omit [DecidableEq F] in
theorem threshold_condition (p : ProfileCertificate I) :
    DiscreteThreshold.Condition (Nat.card F) p.overlapRatio p.threshold :=
  ⟨p.cutoff,p.cutoff_pos,p.cutoff_le,le_max_right _ _⟩

omit [DecidableEq F] in
theorem error_nonneg (p : ProfileCertificate I) : 0 ≤ p.error := by
  have ht := p.threshold_nonneg
  have ht1 := p.threshold_lt_one.le
  unfold error ProfileAnalysis.profile ProfileParameters.rankError
  positivity

end ProfileCertificate

/-- Certificate for one `polygero` invocation discharging the reduced-system
capacity excess via an `ActiveFamilyBound` (such as `CodingTheory.HahnDelsarte`
or `CodingTheory.InterleavedJohnson`) at column cutoff `columnCutoff ≥ largeSize`,
using either Route A (`DiscreteThreshold.Condition (min q L)`) or Route B
(direct Hahn/Delsarte pairwise-complement excess bound). -/
structure HahnSystemCertificate (I : Instance F) extends ProfileParameters I where
  columnCutoff : ℕ
  listBound : ℕ
  threshold : ℚ
  large_le_cutoff : toProfileParameters.largeSize ≤ columnCutoff
  cutoff_le_n : columnCutoff ≤ I.n
  active_bound : DirectBinomial.ActiveFamilyBound I.n columnCutoff
    toProfileParameters.overlapSize (Nat.card F) listBound
  floor_le : toProfileParameters.columnFloorAt columnCutoff ≤ threshold
  threshold_lt_one : threshold < 1
  excess_condition : DirectBinomial.HahnExcessCondition I.n I.t
    toProfileParameters.overlapSize (Nat.card F) columnCutoff listBound threshold
  field_error_lt_one : toProfileParameters.rankError + 1 / (Nat.card F : ℚ) < 1

namespace HahnSystemCertificate
variable {I : Instance F}

noncomputable def error (p : HahnSystemCertificate I) : ℚ :=
  ProfileAnalysis.profile (Nat.card F) p.rankError p.threshold

omit [Fintype F] [DecidableEq F] in
theorem columnFloor_le (p : HahnSystemCertificate I) : p.columnFloor ≤ p.threshold :=
  (p.columnFloor_le_columnFloorAt p.large_le_cutoff).trans p.floor_le

omit [Fintype F] [DecidableEq F] in
theorem threshold_nonneg (p : HahnSystemCertificate I) : 0 ≤ p.threshold :=
  p.columnFloor_nonneg.trans p.columnFloor_le

omit [Fintype F] [DecidableEq F] in
theorem overlap_lt_cutoff (p : HahnSystemCertificate I) :
    p.overlapSize < p.columnCutoff := by
  have h1 : p.overlapSize < p.largeSize := by
    unfold ProfileParameters.overlapSize ProfileParameters.largeSize ProfileParameters.coreSize
    omega
  exact h1.trans_le p.large_le_cutoff

omit [Fintype F] [DecidableEq F] in
theorem error_lt_one (p : HahnSystemCertificate I) : p.error < 1 := by
  have ht := p.threshold_lt_one
  have hf := p.field_error_lt_one
  unfold error ProfileAnalysis.profile
  nlinarith

omit [Fintype F] [DecidableEq F] in
theorem error_nonneg (p : HahnSystemCertificate I) : 0 ≤ p.error := by
  have ht := p.threshold_nonneg
  have ht1 := p.threshold_lt_one.le
  unfold error ProfileAnalysis.profile ProfileParameters.rankError
  positivity

/-- Construct a `HahnSystemCertificate` from any `UniformFamilyBound` at cutoff `w`. -/
def ofUniformFamilyBound (p : ProfileParameters I) (w L : ℕ) (θ : ℚ)
    (hw : p.largeSize ≤ w) (hwn : w ≤ I.n)
    (hbound : CodingTheory.UniformFamilyBound I.n w p.overlapSize L)
    (hfloor : p.columnFloorAt w ≤ θ) (hθ1 : θ < 1)
    (hexcess : DirectBinomial.HahnExcessCondition I.n I.t p.overlapSize (Nat.card F) w L θ)
    (hfield : p.rankError + 1 / (Nat.card F : ℚ) < 1) :
    HahnSystemCertificate I where
  toProfileParameters := p
  columnCutoff := w
  listBound := L
  threshold := θ
  large_le_cutoff := hw
  cutoff_le_n := hwn
  active_bound := Or.inl hbound
  floor_le := hfloor
  threshold_lt_one := hθ1
  excess_condition := hexcess
  field_error_lt_one := hfield

/-- Construct a `HahnSystemCertificate` directly from a checked integer
Hahn/Delsarte certificate `coeffs`. -/
def ofHahnCertificate (p : ProfileParameters I) (w : ℕ) (coeffs : List ℕ) (θ : ℚ)
    (hw : p.largeSize ≤ w) (hwn : w ≤ I.n)
    (hvalid : CodingTheory.HahnDelsarte.certificateValid I.n w p.overlapSize coeffs = true)
    (hfloor : p.columnFloorAt w ≤ θ) (hθ1 : θ < 1)
    (hexcess : DirectBinomial.HahnExcessCondition I.n I.t p.overlapSize (Nat.card F) w
      (CodingTheory.HahnDelsarte.certifiedBound I.n w coeffs) θ)
    (hfield : p.rankError + 1 / (Nat.card F : ℚ) < 1) :
    HahnSystemCertificate I :=
  ofUniformFamilyBound p w (CodingTheory.HahnDelsarte.certifiedBound I.n w coeffs) θ
    hw hwn (CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate hvalid)
    hfloor hθ1 hexcess hfield

end HahnSystemCertificate

namespace ProfileCertificate
variable {I : Instance F}

/-- Every `ProfileCertificate` embeds canonically into `HahnSystemCertificate`
with the same local error. -/
noncomputable def toHahnSystemCertificate (p : ProfileCertificate I) : HahnSystemCertificate I where
  toProfileParameters := p.toProfileParameters
  columnCutoff := p.largeSize
  listBound := Nat.card F
  threshold := p.threshold
  large_le_cutoff := le_rfl
  cutoff_le_n := p.large_le
  active_bound := Or.inr le_rfl
  floor_le := p.floor_le
  threshold_lt_one := p.threshold_lt_one
  excess_condition := Or.inr (Or.inr (by simpa [min_self, ProfileParameters.overlapRatio] using p.threshold_condition))
  field_error_lt_one := p.field_error_lt_one

omit [DecidableEq F] in
@[simp] theorem toHahnSystemCertificate_error (p : ProfileCertificate I) :
    p.toHahnSystemCertificate.error = p.error := rfl

omit [DecidableEq F] in
@[simp] theorem toHahnSystemCertificate_threshold (p : ProfileCertificate I) :
    p.toHahnSystemCertificate.threshold = p.threshold := rfl

end ProfileCertificate

end RecursivePolygero
