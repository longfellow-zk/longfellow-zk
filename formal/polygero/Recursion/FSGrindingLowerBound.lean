import polygero.Recursion.FSGrindingProbability
import Bcs.GrindingBounds

/-! Finite lower bounds for the actual adaptive grinding adversary.
The short binomial prefix avoids expanding exponentially large powers.
The last theorem measures the standard recursive-FS failure event of an
ordinary proof-valued bounded oracle tree. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis Local Local.Polygero LigeroFamily Merkle.RandomOracle
open Bcs.TotalOracle.Footprint
open scoped Classical

/-- The product of two finite search lower bounds remains valid even
when the parent Bonferroni expression happens to be negative. -/
theorem grinding_product_lower (rootMass queryMass terminalMass : ℚ)
    (hr0 : 0 ≤ rootMass) (hr1 : rootMass ≤ 1)
    (hq0 : 0 ≤ queryMass) (hq1 : queryMass ≤ 1) (ht0 : 0 ≤ terminalMass)
    (R M depth : ℕ) (hdepth : depth ≤ M) :
    (R * rootMass - (R.choose 2 : ℚ) * rootMass ^ 2) *
      (1 - 1 / (∑ j ∈ range (depth + 1), (M.choose j : ℚ) * queryMass ^ j)) *
      terminalMass ≤
    (1 - (1 - rootMass) ^ R) * (1 - (1 - queryMass) ^ M) * terminalMass := by
  have hprefix : (1 : ℚ) ≤
      ∑ j ∈ range (depth + 1), (M.choose j : ℚ) * queryMass ^ j := by
    have h := single_le_sum (fun j (_ : j ∈ range (depth + 1)) =>
      mul_nonneg (Nat.cast_nonneg (M.choose j)) (pow_nonneg hq0 j))
      (show 0 ∈ range (depth + 1) by simp)
    simpa only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] using h
  have hprefixPos : (0 : ℚ) <
      ∑ j ∈ range (depth + 1), (M.choose j : ℚ) * queryMass ^ j :=
    lt_of_lt_of_le (by norm_num) hprefix
  have hchild0 : (0 : ℚ) ≤
      1 - 1 / (∑ j ∈ range (depth + 1), (M.choose j : ℚ) * queryMass ^ j) :=
    sub_nonneg.mpr ((div_le_one hprefixPos).mpr hprefix)
  have hroot0 : (0 : ℚ) ≤ 1 - (1 - rootMass) ^ R :=
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hr1) (by linarith))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (Bcs.GrindingBounds.root_search_lower rootMass hr0 hr1 R)
      (Bcs.GrindingBounds.child_search_lower queryMass hq0 hq1 M depth hdepth)
      hchild0 hroot0) ht0

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

omit [Fintype F] [DecidableEq F] in
theorem grindingAvoidance_eq (hn : 0 < child.instance.n) :
    grindingAvoidance child = (child.instance.n - child.instance.t : ℕ) / (child.instance.n : ℚ) := by
  have hn1 : child.instance.n - 1 + 1 = child.instance.n := by omega
  have hc := Nat.choose_mul_succ_eq (child.instance.n - 1) child.instance.t
  rw [hn1] at hc
  have hnq : (child.instance.n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : (child.instance.n.choose child.instance.t : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos child.instance.query_le).ne'
  unfold grindingAvoidance
  apply (div_eq_div_iff hd hnq).mpr
  exact_mod_cast hc.trans (Nat.mul_comm _ _)

theorem grindingSearch_success_lower
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (hvalues : values.Nodup)
    (roots : List I.layer.Oracle) (hroots : roots.Nodup)
    (rootMass queryMass : ℚ)
    (hr0 : 0 ≤ rootMass) (hr1 : rootMass ≤ 1)
    (hq0 : 0 ≤ queryMass) (hq1 : queryMass ≤ 1)
    (hready : ∀ W ∈ roots,
      mean (fun a => indicator (prepare W a ≠ none)) = rootMass)
    (hgood : ∀ W ∈ roots, ∀ a ready, prepare W a = some ready →
      mean (fun Q => indicator (ready.goodQueries Q)) = queryMass)
    (depth : ℕ) (hdepth : depth ≤ values.length) :
    (roots.length * rootMass - (roots.length.choose 2 : ℚ) * rootMass ^ 2) *
      (1 - 1 / (∑ j ∈ range (depth + 1),
        (values.length.choose j : ℚ) * queryMass ^ j)) * grindingAvoidance child ≤
    average (fun H : HashInput child → Answer child =>
      grindingSuccessWeight child
        ((grindingSearch child hk sigma prepare row col values roots).run H).1) := by
  rw [grindingSearch_success_probability child hk sigma prepare row col values hvalues
    roots hroots rootMass queryMass hready hgood]
  exact grinding_product_lower rootMass queryMass (grindingAvoidance child)
    hr0 hr1 hq0 hq1 (by unfold grindingAvoidance; positivity) roots.length values.length depth hdepth

/-- Convert optional search output to a standard proof-valued adversary.
The fixed fallback consumes no additional oracle query. -/
noncomputable def grindingAdversary
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (roots : List I.layer.Oracle) (fallback : Proof child) :
    Tree (HashInput child) (Answer child) (Proof child) ((2 + values.length) + roots.length) :=
  (grindingSearch child hk sigma prepare row col values roots).map (fun out => out.getD fallback)

/-- Every successful search output is an actual failure of the standard
proof-valued tree, regardless of what the fixed fallback happens to do. -/
theorem grinding_success_le_failure (p : HahnSystemCertificate I)
    (cp : HahnSystemCertificate child.instance)
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (roots : List I.layer.Oracle) (fallback : Proof child) :
    average (fun H : HashInput child → Answer child =>
      grindingSuccessWeight child
        ((grindingSearch child hk sigma prepare row col values roots).run H).1) ≤
    Bcs.FiniteProbability.density (fun H => failure child p cp sigma (fun _ => False) H
      ((grindingAdversary child hk sigma prepare row col values roots fallback).run H).1) := by
  have hm := mean_mono (fun H : HashInput child → Answer child => show
      grindingSuccessWeight child
        ((grindingSearch child hk sigma prepare row col values roots).run H).1 ≤
      indicator (failure child p cp sigma (fun _ => False) H
        ((grindingAdversary child hk sigma prepare row col values roots fallback).run H).1) from by
    cases hout : ((grindingSearch child hk sigma prepare row col values roots).run H).1 with
    | none =>
      simp only [grindingSuccessWeight]
      exact indicator_nonneg _
    | some d =>
      have hf := grindingSearch_failure child p cp hk sigma hfalse prepare row col values roots H d hout
      have ho : ((grindingAdversary child hk sigma prepare row col values roots fallback).run H).1 = d := by
        simp [grindingAdversary, Tree.run_map, hout]
      simp only [grindingSuccessWeight, ho, indicator, if_pos hf, le_refl])
  have he := mean_indicator (fun H : HashInput child → Answer child =>
    failure child p cp sigma (fun _ => False) H
      ((grindingAdversary child hk sigma prepare row col values roots fallback).run H).1)
  exact hm.trans_eq he

/-- A finite search lower bound for the actual recursive-FS failure event.
The mass hypotheses are scalar facts about the parent algebra and its
good query sets; commitment completion and adaptive freshness are proved. -/
theorem grindingAdversary_failure_lower (p : HahnSystemCertificate I)
    (cp : HahnSystemCertificate child.instance)
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (hvalues : values.Nodup)
    (roots : List I.layer.Oracle) (hroots : roots.Nodup) (fallback : Proof child)
    (rootMass queryMass : ℚ)
    (hr0 : 0 ≤ rootMass) (hr1 : rootMass ≤ 1)
    (hq0 : 0 ≤ queryMass) (hq1 : queryMass ≤ 1)
    (hready : ∀ W ∈ roots,
      mean (fun a => indicator (prepare W a ≠ none)) = rootMass)
    (hgood : ∀ W ∈ roots, ∀ a ready, prepare W a = some ready →
      mean (fun Q => indicator (ready.goodQueries Q)) = queryMass)
    (depth : ℕ) (hdepth : depth ≤ values.length) :
    (roots.length * rootMass - (roots.length.choose 2 : ℚ) * rootMass ^ 2) *
      (1 - 1 / (∑ j ∈ range (depth + 1),
        (values.length.choose j : ℚ) * queryMass ^ j)) * grindingAvoidance child ≤
    Bcs.FiniteProbability.density (fun H => failure child p cp sigma (fun _ => False) H
      ((grindingAdversary child hk sigma prepare row col values roots fallback).run H).1) :=
  (grindingSearch_success_lower child hk sigma prepare row col values hvalues roots hroots
    rootMass queryMass hr0 hr1 hq0 hq1 hready hgood depth hdepth).trans
    (grinding_success_le_failure child p cp hk sigma hfalse prepare row col values roots fallback)

end RecursivePolygero.FiatShamir.TwoLevel
