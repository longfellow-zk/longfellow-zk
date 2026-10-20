import polygero.Instances.FSTwoLevel
import polygero.Recursion.FSLocalDomains

/-! Complete two-level ROM bounds after retuning the openings.

These schedules use the same geometry and the same four-event coverage
as the existing verified benchmarks. The new ingredient is allocation of
adaptive queries among the disjoint roles: the intercept pays all four
roles, while every prover query pays only their maximum price.

This is a proof-cost tradeoff, not a new consumption inequality. It does
not assume a circuit restriction or a limit on adaptive child commitments.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSRetunedAffine

open FiatShamir FiatShamir.TwoLevel ProfileAnalysis
open Bcs.AffineBlock
open scoped Classical

inductive Schedule | bits126 | nearIOP | bits127

def parent : Schedule → FSTwoLevel.Row
  | .bits126 => ⟨96, 3255, 3, 126, 1⟩
  | .nearIOP => ⟨110, 3680, 2, 127, 0⟩
  | .bits127 => ⟨155, 4658, 1, 127, 0⟩

def childRow : Schedule → FSTwoLevel.Row
  | .bits126 => ⟨96, 3255, 3, 126, 1⟩
  | .nearIOP => ⟨111, 3680, 2, 127, 0⟩
  | .bits127 => ⟨156, 4658, 1, 127, 0⟩

/-- Per-query coefficient. The full theorem below keeps the verifier's
four appended lookups in the intercept instead of multiplying them by N. -/
def price : Schedule → ℚ
  | .bits126 => 1 / (2^126 : ℚ)
  | .nearIOP => 2 / (FSTwoLevel.fieldSize : ℚ) + FSTwoLevel.rankError
  | .bits127 => 1 / (2^127 : ℚ)

def overhead : Schedule → ℕ
  | .bits126 => 2
  | .nearIOP => 3
  | .bits127 => 2

def prices (s : Schedule) : Fin 4 → ℚ := ![
  FSTwoLevel.rankError + (parent s).list / (FSTwoLevel.fieldSize : ℚ),
  (childRow s).list * FSTwoLevel.theta (parent s),
  FSTwoLevel.rankError + (childRow s).list / (FSTwoLevel.fieldSize : ℚ),
  FSTwoLevel.theta (childRow s)]

/-- Both local certificates and all four actual oracle-role prices are
checked by kernel reduction. The small rank error is retained. -/
theorem checked (s : Schedule) :
    FSTwoLevel.rowOk (parent s) ∧ FSTwoLevel.rowOk (childRow s) ∧
    FSTwoLevel.budget (parent s) (childRow s) ≤ overhead s * price s ∧
    (FSTwoLevel.rankError + (parent s).list / (FSTwoLevel.fieldSize : ℚ) ≤ price s) ∧
    ((childRow s).list * FSTwoLevel.theta (parent s) ≤ price s) ∧
    (FSTwoLevel.rankError + (childRow s).list / (FSTwoLevel.fieldSize : ℚ) ≤ price s) ∧
    (FSTwoLevel.theta (childRow s) ≤ price s) := by
  cases s <;>
    simp only [parent, childRow, price, overhead, FSTwoLevel.rowOk,
      FSTwoLevel.theta, FSTwoLevel.budget, FSTwoLevel.rankError,
      FSTwoLevel.fieldSize, CodingTheory.InterleavedJohnson.denominator,
      CodingTheory.InterleavedJohnson.listBound, DiscreteThreshold.candidate,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

/-- A probability cap absorbs a tiny extra per-query coefficient into
intercept slack. This keeps an exact power-of-two bound for every N:
once `N*rate` reaches one the probability bound is automatic. -/
theorem absorb_small_rate (x intercept rate extra slack : ℚ) (N : ℕ)
    (hcap : x ≤ 1) (hbound : x ≤ intercept + N * (rate + extra))
    (hrate : 0 ≤ rate) (hslack : 0 ≤ slack)
    (hintercept : intercept ≤ 2 * rate - slack * rate)
    (hextra : extra ≤ slack * rate^2) :
    x ≤ (N+2) * rate := by
  by_cases hn : (N : ℚ) * rate ≤ 1
  · have he : (N : ℚ) * extra ≤ slack * rate := by
      calc
        _ ≤ (N : ℚ) * (slack * rate^2) :=
          mul_le_mul_of_nonneg_left hextra (Nat.cast_nonneg N)
        _ = ((N : ℚ) * rate) * (slack * rate) := by ring
        _ ≤ 1 * (slack * rate) :=
          mul_le_mul_of_nonneg_right hn (mul_nonneg hslack hrate)
        _ = slack * rate := one_mul _
    nlinarith
  · have hn' : 1 < (N : ℚ) * rate := lt_of_not_ge hn
    nlinarith

def fixedPrice (s : FSTwoLevel.Schedule) : ℚ :=
  1 / (2^((FSTwoLevel.data s).bits+1) : ℚ)

def fixedPrices (s : FSTwoLevel.Schedule) : Fin 4 → ℚ := ![
  FSTwoLevel.rankError + (FSTwoLevel.data s).list / (FSTwoLevel.fieldSize : ℚ),
  (FSTwoLevel.childData s).list * FSTwoLevel.theta (FSTwoLevel.data s),
  FSTwoLevel.rankError + (FSTwoLevel.childData s).list / (FSTwoLevel.fieldSize : ℚ),
  FSTwoLevel.theta (FSTwoLevel.childData s)]

theorem fixed_checked (s : FSTwoLevel.Schedule) :
    FSTwoLevel.budget (FSTwoLevel.data s) (FSTwoLevel.childData s) ≤
      2 * fixedPrice s - (1/64) * fixedPrice s ∧
    FSTwoLevel.rankError ≤ (1/64) * (fixedPrice s)^2 ∧
    (FSTwoLevel.rankError + (FSTwoLevel.data s).list / (FSTwoLevel.fieldSize : ℚ) ≤
      fixedPrice s + FSTwoLevel.rankError) ∧
    ((FSTwoLevel.childData s).list * FSTwoLevel.theta (FSTwoLevel.data s) ≤
      fixedPrice s + FSTwoLevel.rankError) ∧
    (FSTwoLevel.rankError + (FSTwoLevel.childData s).list / (FSTwoLevel.fieldSize : ℚ) ≤
      fixedPrice s + FSTwoLevel.rankError) ∧
    (FSTwoLevel.theta (FSTwoLevel.childData s) ≤ fixedPrice s + FSTwoLevel.rankError) := by
  cases s <;>
    simp only [fixedPrice, FSTwoLevel.data, FSTwoLevel.childData,
      FSTwoLevel.theta, FSTwoLevel.budget, FSTwoLevel.rankError,
      FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose] <;>
    decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

set_option maxHeartbeats 200000

omit [Fintype F] [DecidableEq F] in
private theorem role_max_le {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate : ℚ) (h0 : listError I p ≤ rate)
    (h1 : cp.listBound * p.threshold ≤ rate)
    (h2 : listError child.instance cp ≤ rate) (h3 : cp.threshold ≤ rate) :
    maxSlope (roleRate child p cp) ≤ rate := by
  apply Finset.sup'_le
  intro i _
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The existing 75/75 and 81/80 schedules already give, respectively,
`(N+2)2^-124` and `(N+2)2^-125`. This improves the coefficient by one bit
without changing either schedule. The tiny rank term is absorbed using
the probability cap, uniformly for every finite query budget. -/
theorem fixedCertifiedFS {I : Instance F} (child : Child I) (s : FSTwoLevel.Schedule)
    (h0 : FSTwoLevel.Geometry I (FSTwoLevel.data s))
    (h1 : FSTwoLevel.Geometry child.instance (FSTwoLevel.childData s))
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (sigma : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
          (N+2) * fixedPrice s := by
  obtain ⟨hr, hc, _, _⟩ := FSTwoLevel.checked s
  obtain ⟨hb, he, hs0, hs1, hs2, hs3⟩ := fixed_checked s
  obtain ⟨p, hpTheta, hpList, hpMu⟩ :=
    FSTwoLevel.certificate I (FSTwoLevel.data s) hr h0 hq
  obtain ⟨cp, hcTheta, hcList, hcMu⟩ :=
    FSTwoLevel.certificate child.instance (FSTwoLevel.childData s) hc h1 hq
  obtain ⟨_, _, _, _, hsmall, _⟩ := hr
  obtain ⟨_, _, _, _, hcsmall, _⟩ := hc
  refine ⟨p, cp, fun sigma N tree => ?_⟩
  have hp : p.listBound < Nat.card F := by rw [hpList, hq]; exact hsmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList, hq]; exact hcsmall.2
  have hbudget : listBudget child p cp =
      FSTwoLevel.budget (FSTwoLevel.data s) (FSTwoLevel.childData s) := by
    simp only [listBudget, listError, hpTheta, hpList, hpMu, hcTheta, hcList, hcMu,
      hq, FSTwoLevel.budget]
    generalize FSTwoLevel.rankError = mu
    ring
  have hslope : maxSlope (roleRate child p cp) ≤ fixedPrice s + FSTwoLevel.rankError := by
    apply role_max_le child p cp
    · simpa only [listError, hpMu, hpList, hq] using hs0
    · simpa only [hcList, hpTheta] using hs1
    · simpa only [listError, hcMu, hcList, hq] using hs2
    · exact hcTheta.trans_le hs3
  apply absorb_small_rate _ _ _ _ (1/64) N
  · unfold Bcs.FiniteProbability.density
    apply div_le_one_of_le₀
    · exact_mod_cast Finset.card_filter_le Finset.univ _
    · positivity
  · exact (fs_list_affine_bound child p cp hp hcp sigma tree).trans
      (add_le_add (le_of_eq hbudget)
        (mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N)))
  · unfold fixedPrice; positivity
  · norm_num
  · exact hb
  · exact he

/-- False-statement soundness at the unchanged schedules. -/
theorem fixedCertifiedSoundness {I : Instance F} (child : Child I) (s : FSTwoLevel.Schedule)
    (h0 : FSTwoLevel.Geometry I (FSTwoLevel.data s))
    (h1 : FSTwoLevel.Geometry child.instance (FSTwoLevel.childData s))
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child sigma H (tree.run H).1) ≤
      (N+2) * fixedPrice s := by
  obtain ⟨p, cp, h⟩ := fixedCertifiedFS child s h0 h1 hq
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

/-- Full adaptive two-level challenge-ROM theorem. The tree can interleave
all four roles and make arbitrarily many distinct child commitments.
The clean schedules give `(N+2)2^-126` and `(N+2)2^-127`. The middle
schedule gives `(N+3)(2/|F|+rankError)`, recovering the field-floor IOP
coefficient up to the retained rank error. This is actual verifier/extractor
failure, not a numerical sensitivity bound. -/
theorem certifiedFS {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance (childRow s))
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (sigma : I.layer.Statement) (N : ℕ)
        (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N),
      Bcs.FiniteProbability.density (fun H =>
        failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
          (N+overhead s) * price s := by
  obtain ⟨hr, hc, hb, hs0, hs1, hs2, hs3⟩ := checked s
  obtain ⟨p, hpTheta, hpList, hpMu⟩ := FSTwoLevel.certificate I (parent s) hr h0 hq
  obtain ⟨cp, hcTheta, hcList, hcMu⟩ :=
    FSTwoLevel.certificate child.instance (childRow s) hc h1 hq
  obtain ⟨_, _, _, _, hsmall, _⟩ := hr
  obtain ⟨_, _, _, _, hcsmall, _⟩ := hc
  refine ⟨p, cp, fun sigma N tree => ?_⟩
  have hp : p.listBound < Nat.card F := by rw [hpList, hq]; exact hsmall.2
  have hcp : cp.listBound < Nat.card F := by rw [hcList, hq]; exact hcsmall.2
  have hbudget : listBudget child p cp = FSTwoLevel.budget (parent s) (childRow s) := by
    simp only [listBudget, listError, hpTheta, hpList, hpMu, hcTheta, hcList, hcMu,
      hq, FSTwoLevel.budget]
    generalize FSTwoLevel.rankError = mu
    ring
  have hslope : maxSlope (roleRate child p cp) ≤ price s := by
    apply role_max_le child p cp
    · simpa only [listError, hpMu, hpList, hq] using hs0
    · simpa only [hcList, hpTheta] using hs1
    · simpa only [listError, hcMu, hcList, hq] using hs2
    · exact hcTheta.trans_le hs3
  calc
    _ ≤ listBudget child p cp + N * maxSlope (roleRate child p cp) :=
      fs_list_affine_bound child p cp hp hcp sigma tree
    _ ≤ overhead s * price s + N * price s := by
      exact add_le_add (hbudget ▸ hb)
        (mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N))
    _ = (N+overhead s) * price s := by ring

/-- Actual false-statement acceptance has the same bound, by validity of
the existing two-level extractor. No additional soundness premise is used. -/
theorem certifiedSoundness {I : Instance F} (child : Child I) (s : Schedule)
    (h0 : FSTwoLevel.Geometry I (parent s))
    (h1 : FSTwoLevel.Geometry child.instance (childRow s))
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => accepts child sigma H (tree.run H).1) ≤
      (N+overhead s) * price s := by
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

end RecursivePolygero.Instances.FSRetunedAffine
