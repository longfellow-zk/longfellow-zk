import polygero.Recursion.FSListBound

/-! Two concrete two-level FS schedules at the geometry of the verified
rate-1/16 table. Both levels have n=8192, k=512, s=64 and field size 2^128.
These are new schedules, not rows of the original 50--70 query table.
All numerical checks use kernel reduction, not native reduction. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSTwoLevel

open FiatShamir FiatShamir.TwoLevel
open scoped Classical

def fieldSize : ℕ := 2^128
def rankError : ℚ := (Nat.choose 8192 641 : ℚ) / (fieldSize : ℚ)^65
def fieldFloor : ℚ := 2/(fieldSize : ℚ) - 1/(fieldSize : ℚ)^2

inductive Schedule | fourBit | threeBit

structure Row where
  queries : ℕ
  cutoff : ℕ
  list : ℕ
  bits : ℕ
  loss : ℕ

def data : Schedule → Row
  | .fourBit => ⟨75, 2487, 15, 123, 4⟩
  | .threeBit => ⟨81, 2660, 8, 124, 3⟩

def childData : Schedule → Row
  | .fourBit => ⟨75, 2559, 11, 123, 4⟩
  | .threeBit => ⟨80, 2713, 7, 124, 3⟩

def theta (r : Row) : ℚ := ((r.cutoff-1).choose r.queries : ℚ) /
  (Nat.choose 8192 r.queries : ℚ)

def budget (r c : Row) : ℚ :=
  2*rankError + (r.list+c.list)/(fieldSize : ℚ) + c.list*theta r + theta c

def rowOk (r : Row) : Prop :=
  (1 ≤ r.queries ∧ r.queries ≤ 8192) ∧
  (1088 ≤ r.cutoff ∧ r.cutoff ≤ 8192) ∧
  0 < CodingTheory.InterleavedJohnson.denominator 8192 7553 (8192-r.cutoff) ∧
  CodingTheory.InterleavedJohnson.listBound 8192 7553 (8192-r.cutoff) = r.list ∧
  (1 ≤ r.list ∧ r.list < fieldSize) ∧
  DiscreteThreshold.candidate r.list 1
    ((Nat.choose 639 r.queries : ℚ) / (Nat.choose 8192 r.queries : ℚ)) ≤ theta r

/-- Exact rational bounds, including the Johnson list and excess premises. -/
theorem checked (schedule : Schedule) :
    rowOk (data schedule) ∧ rowOk (childData schedule) ∧
    budget (data schedule) (childData schedule) ≤ 1/(2^(data schedule).bits : ℚ) ∧
    budget (data schedule) (childData schedule) ≤ (2^(data schedule).loss : ℚ)*fieldFloor := by
  cases schedule <;>
    simp only [rowOk, data, childData, theta, budget, rankError, fieldSize, fieldFloor,
      CodingTheory.InterleavedJohnson.denominator,
      CodingTheory.InterleavedJohnson.listBound, DiscreteThreshold.candidate,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

private theorem field_error : rankError + 1/(fieldSize : ℚ) < 1 := by
  simp only [rankError, fieldSize, Nat.choose_eq_fast_choose]
  decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem field_le_error {I : Instance F} (p : HahnSystemCertificate I) :
    1/(Nat.card F : ℚ) ≤ p.error := by
  have hm : 0 ≤ p.rankError := by unfold ProfileParameters.rankError; positivity
  have hu : 1/(Nat.card F : ℚ) ≤ 1 := by linarith [p.field_error_lt_one]
  have h0 := mul_nonneg p.threshold_nonneg (sub_nonneg.mpr hu)
  have h1 := mul_nonneg (sub_nonneg.mpr p.threshold_lt_one.le) hm
  unfold HahnSystemCertificate.error ProfileAnalysis.profile
  nlinarith

omit [Fintype F] [DecidableEq F] in
/-- The comparison uses a lower bound on the interactive error, so it
applies to any two original local certificates over this field. -/
theorem fieldFloor_le_reference {I J : Instance F}
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate J)
    (hq : Nat.card F = fieldSize) : fieldFloor ≤ twoError p.error cp.error := by
  have h0 := field_le_error p
  have h1 := field_le_error cp
  have hm : 0 ≤ p.rankError := by unfold ProfileParameters.rankError; positivity
  have hu : 1/(Nat.card F : ℚ) ≤ 1 := by linarith [p.field_error_lt_one]
  have ha := mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr cp.error_lt_one.le)
  have hb := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hu)
  rw [hq] at ha hb
  unfold fieldFloor twoError
  simp only [div_eq_mul_inv, one_mul, ← inv_pow] at ha hb ⊢
  nlinarith

/-- Geometry is asserted separately at each level; a concrete `Child`
still supplies the domain, layout and coefficient packing. -/
structure Geometry (I : Instance F) (r : Row) : Prop where
  length : I.n = 8192
  dimension : I.r + I.w = 512
  masks : I.s = 64
  queries : I.t = r.queries

omit [Fintype F] [DecidableEq F] in
theorem certificate (I : Instance F) (r : Row) (hr : rowOk r)
    (h : Geometry I r) (hq : Nat.card F = fieldSize) :
    ∃ p : HahnSystemCertificate I,
      p.threshold = theta r ∧ p.listBound = r.list ∧
      p.toProfileParameters.rankError = rankError := by
  obtain ⟨ht, hw, hden, hlist, hsmall, hexcess⟩ := hr
  let profile : ProfileParameters I := {
    positive_degree := by have := h.dimension; omega
    large_le := by simp only [h.dimension, h.masks, h.length]; omega
    query_pos := by rw [h.queries]; exact ht.1
    overlap_lt := by simp only [h.dimension, h.masks, h.length]; omega
  }
  have hmu : profile.rankError = rankError := by
    simp only [ProfileParameters.rankError, ProfileParameters.coreSize,
      h.length, h.dimension, h.masks, hq, rankError]
  have hover : profile.overlapSize = 639 := by
    simp [ProfileParameters.overlapSize, h.dimension, h.masks]
  have hlarge : profile.largeSize = 1088 := by
    simp [ProfileParameters.largeSize, ProfileParameters.coreSize, h.dimension, h.masks]
  have hb : CodingTheory.UniformFamilyBound I.n r.cutoff profile.overlapSize r.list := by
    have hh := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
      (n := 8192) (d := 7553) (E := 8192-r.cutoff)
      (by omega) (by omega) (by omega) hden
    have hsub : 8192 - (8192-r.cutoff) = r.cutoff := by omega
    simpa only [h.length, hover, hsub, hlist, show 8192-7553=639 from rfl] using hh
  have hcut : profile.largeSize ≤ r.cutoff := by rw [hlarge]; exact hw.1
  have hcutn : r.cutoff ≤ I.n := by rw [h.length]; exact hw.2
  have hfloor : profile.columnFloorAt r.cutoff = theta r := by
    simp only [ProfileParameters.columnFloorAt, h.queries, h.length, theta]
  have htheta : theta r < 1 := by
    rw [← hfloor]
    exact profile.columnFloorAt_lt_one (by omega) hcutn
  have he : DirectBinomial.HahnExcessCondition I.n I.t profile.overlapSize
      (Nat.card F) r.cutoff r.list (theta r) := by
    rw [h.length, h.queries, hover, hq]
    apply Or.inr ∘ Or.inr
    refine ⟨1, le_rfl, ?_, ?_⟩
    · simpa only [Nat.min_eq_right hsmall.2.le] using hsmall.1
    · simpa only [Nat.min_eq_right hsmall.2.le] using hexcess
  let p := HahnSystemCertificate.ofUniformFamilyBound profile r.cutoff r.list
    (theta r) hcut hcutn hb hfloor.le htheta he (by rw [hmu, hq]; exact field_error)
  exact ⟨p, rfl, rfl, hmu⟩

/-- Complete two-level ideal-ROM instantiation. No consumption inequality
or bounded-commitment premise is assumed. The field-floor comparison is
stronger than comparison with the 70-opening interactive reference. -/
theorem certifiedFS {I : Instance F} (child : Child I) (schedule : Schedule)
    (h0 : Geometry I (data schedule))
    (h1 : Geometry child.instance (childData schedule)) (hq : Nat.card F = fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (sigma : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
          (N+1)*budget (data schedule) (childData schedule) ∧
      budget (data schedule) (childData schedule) ≤ 1/(2^(data schedule).bits : ℚ) ∧
      budget (data schedule) (childData schedule) ≤ (2^(data schedule).loss : ℚ)*fieldFloor := by
  obtain ⟨hr, hc, hbits, hloss⟩ := checked schedule
  obtain ⟨p, hpTheta, hpList, hpMu⟩ := certificate I (data schedule) hr h0 hq
  obtain ⟨cp, hcTheta, hcList, hcMu⟩ := certificate child.instance (childData schedule) hc h1 hq
  obtain ⟨_, _, _, _, hsmall, _⟩ := hr
  obtain ⟨_, _, _, _, hcsmall, _⟩ := hc
  refine ⟨p, cp, fun sigma N tree => ⟨?_, hbits, hloss⟩⟩
  have hp : p.listBound < Nat.card F := by rw [hpList, hq]; exact hsmall.2
  have hc : cp.listBound < Nat.card F := by rw [hcList, hq]; exact hcsmall.2
  have hb : listBudget child p cp = budget (data schedule) (childData schedule) := by
    simp only [listBudget, ProfileAnalysis.listError, hpTheta, hpList, hpMu,
      hcTheta, hcList, hcMu, hq, budget]
    ring
  simpa only [hb] using fs_list_bound child p cp hp hc sigma tree

/-- False-statement FS soundness follows from the concrete extractor's
validity; it is not an additional local soundness assumption. -/
theorem certifiedSoundness {I : Instance F} (child : Child I) (schedule : Schedule)
    (h0 : Geometry I (data schedule))
    (h1 : Geometry child.instance (childData schedule)) (hq : Nat.card F = fieldSize)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child sigma H (tree.run H).1) ≤
      (N+1)*budget (data schedule) (childData schedule) := by
  obtain ⟨p, cp, h⟩ := certifiedFS child schedule h0 h1 hq
  have he (H : HashInput child → Answer child) :
      failure child p cp sigma (fun _ => False) H (tree.run H).1 ↔
        accepts child sigma H (tree.run H).1 := by
    rw [failure_empty_iff]
    have hn : (twoProof child p cp).run sigma (tree.run H).1.1
        (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) = none := by
      cases hh : (twoProof child p cp).run sigma (tree.run H).1.1
          (constantMessages child (tree.run H).1) (proofCoins child H (tree.run H).1) with
      | none => rfl
      | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g hh)).elim
    simp only [hn, and_true]
  simpa only [he] using (h sigma N tree).1

end RecursivePolygero.Instances.FSTwoLevel
