import polygero.Benchmarks.FSTwoLevel
import polygero.Recursion.FSLocalDomains
import polygero.Algebra.Counting.IntegerOccupancy

/-! Actual two-level FS certificates using integer column occupancies.
The protocol geometry stays n=8192,k=512,s=64,|F|=2^128. The fixed schedule
retains 81/80 openings. Other schedules explicitly trade more openings for
a smaller query coefficient. Every bound covers arbitrary-order ROM trees. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace RecursivePolygero.Benchmarks.FSIntegerAffine
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock
open scoped Classical

inductive Schedule | fixed | bits126 | near126 | bits127

def parent : Schedule → FSTwoLevel.Row
  | .fixed => ⟨81, 2714, 6, 125, 2⟩
  | .bits126 => ⟨86, 2917, 4, 126, 1⟩
  | .near126 => ⟨89, 3007, 3, 126, 1⟩
  | .bits127 => ⟨100, 3370, 2, 127, 0⟩

def childRow : Schedule → FSTwoLevel.Row
  | .fixed => ⟨80, 2714, 6, 125, 2⟩
  | .bits126 => ⟨86, 2917, 4, 126, 1⟩
  | .near126 => ⟨88, 3007, 3, 126, 1⟩
  | .bits127 => ⟨100, 3370, 2, 127, 0⟩

def occupancy : Schedule → ℕ
  | .fixed => 2
  | .bits126 => 1
  | .near126 => 1
  | .bits127 => 1

def units (s : Schedule) : ℕ := (parent s).list
def price (s : Schedule) : ℚ := units s / (FSTwoLevel.fieldSize : ℚ) + FSTwoLevel.rankError
def cleanPrice (s : Schedule) : ℚ := 1 / (2^(parent s).bits : ℚ)
def overhead : Schedule → ℕ
  | .fixed => 2
  | .bits126 => 3
  | .near126 => 2
  | .bits127 => 3

def rowOk (r : FSTwoLevel.Row) (h : ℕ) : Prop :=
  (1 ≤ r.queries ∧ r.queries ≤ 8192) ∧
  (1088 ≤ r.cutoff ∧ r.cutoff ≤ 8192) ∧
  ((r.list + 1 : ℤ) * r.list * 639 + 8192 * h * (h + 1) <
    2 * h * (r.list + 1) * r.cutoff) ∧
  (1 ≤ r.list ∧ r.list < FSTwoLevel.fieldSize) ∧
  DiscreteThreshold.candidate r.list 1
    ((Nat.choose 639 r.queries : ℚ) / (Nat.choose 8192 r.queries : ℚ)) ≤ FSTwoLevel.theta r

/-- Every inequality here is exact and kernel checked. The affine rate
retains the tiny rank term; the clean rate absorbs it using intercept slack. -/
theorem checked (s : Schedule) :
    rowOk (parent s) (occupancy s) ∧ rowOk (childRow s) (occupancy s) ∧
    FSTwoLevel.budget (parent s) (childRow s) ≤ 3 * price s ∧
    FSTwoLevel.rankError + (parent s).list / (FSTwoLevel.fieldSize : ℚ) ≤ price s ∧
    (childRow s).list * FSTwoLevel.theta (parent s) ≤ price s ∧
    FSTwoLevel.rankError + (childRow s).list / (FSTwoLevel.fieldSize : ℚ) ≤ price s ∧
    FSTwoLevel.theta (childRow s) ≤ price s ∧
    FSTwoLevel.budget (parent s) (childRow s) ≤
      overhead s * cleanPrice s - (1/64) * cleanPrice s ∧
    FSTwoLevel.rankError ≤ (1/64) * (cleanPrice s)^2 ∧
    FSTwoLevel.rankError + (parent s).list / (FSTwoLevel.fieldSize : ℚ) ≤ cleanPrice s + FSTwoLevel.rankError ∧
    (childRow s).list * FSTwoLevel.theta (parent s) ≤ cleanPrice s + FSTwoLevel.rankError ∧
    FSTwoLevel.rankError + (childRow s).list / (FSTwoLevel.fieldSize : ℚ) ≤ cleanPrice s + FSTwoLevel.rankError ∧
    FSTwoLevel.theta (childRow s) ≤ cleanPrice s + FSTwoLevel.rankError := by
  cases s <;>
    simp only [rowOk, parent, childRow, occupancy, price, units,
      cleanPrice, overhead, FSTwoLevel.theta, FSTwoLevel.budget,
      FSTwoLevel.rankError, FSTwoLevel.fieldSize, DiscreteThreshold.candidate,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Keep the finite maximum proof symbolic: no concrete binomial data
needs to be reduced while selecting one of the four oracle roles. -/
theorem role_max_le {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (rate : ℚ)
    (h0 : listError I p ≤ rate) (h1 : cp.listBound * p.threshold ≤ rate)
    (h2 : listError child.instance cp ≤ rate) (h3 : cp.threshold ≤ rate) :
    maxSlope (roleRate child p cp) ≤ rate := by
  apply Finset.sup'_le
  intro i _
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

omit [Fintype F] [DecidableEq F] in
private theorem field_error : FSTwoLevel.rankError + 1/(FSTwoLevel.fieldSize : ℚ) < 1 := by
  simp only [FSTwoLevel.rankError, FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose]
  decide +kernel

omit [Fintype F] [DecidableEq F] in
/-- The new combinatorial bound produces the same actual local-domain
certificate interface as Johnson/Hahn. No consumption premise is added. -/
theorem certificate (I : Instance F) (r : FSTwoLevel.Row) (h : ℕ) (hr : rowOk r h)
    (hg : FSTwoLevel.Geometry I r) (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I,
      p.threshold = FSTwoLevel.theta r ∧ p.listBound = r.list ∧
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
      (by rw [hmu, hq]; exact field_error)
  exact ⟨p, rfl, rfl, hmu⟩

/-- Arbitrary query order and unrestricted adaptive child commitments are
covered by the existing disjoint-role theorem, with stronger local lists. -/
theorem certifiedAffineFS {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance (childRow s))
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (sigma : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
          FSTwoLevel.budget (parent s) (childRow s) + N * price s := by
  obtain ⟨hr, hc, _, hs0, hs1, hs2, hs3, _⟩ := checked s
  obtain ⟨p, hpTheta, hpList, hpMu⟩ := certificate I (parent s) (occupancy s) hr h0 hq
  obtain ⟨cp, hcTheta, hcList, hcMu⟩ := certificate child.instance (childRow s) (occupancy s) hc h1 hq
  obtain ⟨_, _, _, hsmall, _⟩ := hr
  obtain ⟨_, _, _, hcsmall, _⟩ := hc
  refine ⟨p, cp, fun sigma N tree => ?_⟩
  have hp : p.listBound < Nat.card F := by rw [hpList, hq]; exact hsmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList, hq]; exact hcsmall.2
  have hb : listBudget child p cp = FSTwoLevel.budget (parent s) (childRow s) := by
    simp only [listBudget, listError, hpTheta, hpList, hpMu, hcTheta, hcList, hcMu,
      hq, FSTwoLevel.budget]
    ring
  have hslope : maxSlope (roleRate child p cp) ≤ price s := by
    apply role_max_le
    · simpa only [listError, hpMu, hpList, hq] using hs0
    · simpa only [hcList, hpTheta] using hs1
    · simpa only [listError, hcMu, hcList, hq] using hs2
    · exact hcTheta.trans_le hs3
  exact (fs_list_affine_bound child p cp hp hcp sigma tree).trans
    (add_le_add (le_of_eq hb) (mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N)))

/-- Absorb a negligible slope into any fixed amount of intercept slack,
using the probability cap once the proposed bound reaches one. -/
theorem absorb_rank (x intercept rate extra slack : ℚ) (N K : ℕ)
    (hcap : x ≤ 1) (hbound : x ≤ intercept + N * (rate + extra))
    (hrate : 0 ≤ rate) (hslack : 0 ≤ slack)
    (hb : intercept ≤ K * rate - slack * rate)
    (he : extra ≤ slack * rate^2) : x ≤ (N+K) * rate := by
  by_cases hn : (N : ℚ) * rate ≤ 1
  · have hne : (N : ℚ) * extra ≤ slack * rate := by
      calc
        _ ≤ (N : ℚ) * (slack * rate^2) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
        _ = ((N : ℚ) * rate) * (slack * rate) := by ring
        _ ≤ 1 * (slack * rate) := mul_le_mul_of_nonneg_right hn (mul_nonneg hslack hrate)
        _ = _ := one_mul _
    nlinarith
  · have hn' : 1 < (N : ℚ) * rate := lt_of_not_ge hn
    nlinarith

/-- Clean 125/126/126/127-bit coefficients with the stated constant
verifier overhead. This is a complete ROM theorem, not a stopped-process
sensitivity claim. In particular, the fixed row keeps 81/80 openings. -/
theorem certifiedFS {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance (childRow s))
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (sigma : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
          (N+overhead s) * cleanPrice s := by
  obtain ⟨hr, hc, _, _, _, _, _, hb, he, hs0, hs1, hs2, hs3⟩ := checked s
  obtain ⟨p, hpTheta, hpList, hpMu⟩ := certificate I (parent s) (occupancy s) hr h0 hq
  obtain ⟨cp, hcTheta, hcList, hcMu⟩ := certificate child.instance (childRow s) (occupancy s) hc h1 hq
  obtain ⟨_, _, _, hsmall, _⟩ := hr
  obtain ⟨_, _, _, hcsmall, _⟩ := hc
  refine ⟨p, cp, fun sigma N tree => ?_⟩
  have hp : p.listBound < Nat.card F := by rw [hpList, hq]; exact hsmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList, hq]; exact hcsmall.2
  have hbudget : listBudget child p cp = FSTwoLevel.budget (parent s) (childRow s) := by
    simp only [listBudget, listError, hpTheta, hpList, hpMu, hcTheta, hcList, hcMu,
      hq, FSTwoLevel.budget]
    ring
  have hslope : maxSlope (roleRate child p cp) ≤ cleanPrice s + FSTwoLevel.rankError := by
    apply role_max_le
    · simpa only [listError, hpMu, hpList, hq] using hs0
    · simpa only [hcList, hpTheta] using hs1
    · simpa only [listError, hcMu, hcList, hq] using hs2
    · exact hcTheta.trans_le hs3
  apply absorb_rank _ _ _ _ (1/64) N (overhead s)
  · unfold Bcs.FiniteProbability.density
    apply div_le_one_of_le₀
    · exact_mod_cast Finset.card_filter_le Finset.univ _
    · positivity
  · exact (fs_list_affine_bound child p cp hp hcp sigma tree).trans
      (add_le_add (le_of_eq hbudget) (mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N)))
  · unfold cleanPrice; positivity
  · norm_num
  · exact hb
  · exact he

/-- False-statement acceptance follows by validity of the actual recursive
extractor, with the same coefficient and no separate local premise. -/
theorem certifiedSoundness {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance (childRow s))
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child sigma H (tree.run H).1) ≤
      (N+overhead s) * cleanPrice s := by
  obtain ⟨p, cp, h⟩ := certifiedFS child s h0 h1 hq
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
  simpa only [he] using h sigma N tree

end RecursivePolygero.Benchmarks.FSIntegerAffine
