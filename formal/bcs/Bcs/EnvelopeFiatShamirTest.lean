import Bcs.FixedKeyEnvelopeFiatShamir

/-! Operational regression cases for the typed lazy-oracle compiler. -/
namespace Bcs.EnvelopeFiatShamir.Test
open Finset Bcs.TypedFiatShamir
open scoped Classical BigOperators

def bad (alpha response query : Bool) : Prop := alpha = true ∧ query = response

instance badDecidable (alpha response query : Bool) : Decidable (bad alpha response query) :=
  inferInstanceAs (Decidable (alpha = true ∧ query = response))

def bound : ResponseUniformBound bad (1 / 4) where
  envelope alpha := if alpha then 1 / 2 else 0
  dominates := by
    intro alpha response
    have hfilter : univ.filter (bad alpha response) = if alpha then {response} else ∅ := by
      ext query
      cases alpha <;> simp [bad]
    rw [Finset.filter_congr_decidable]
    rw [hfilter]
    cases alpha <;> norm_num
  mean_le := by native_decide

abbrev Program (N : ℕ) := Merkle.RandomOracle.Tree
  (Query Unit (Unit × Bool)) (Answer Bool Bool) Bool N

def failureRate {N : ℕ} (program : Program N) : ℚ :=
  let tr := Bcs.EnvelopeFiatShamir.trace program (false, false) () id
  ((univ.filter fun tape : Fin (N + 2) → Answer Bool Bool =>
    bad (definingAlphaAnswer tr tape)
      (Merkle.RandomOracle.lazyRun tape (false, false) program []).1
      (definingSubsetAnswer tr tape)).card : ℚ) /
    Fintype.card (Fin (N + 2) → Answer Bool Bool)

def noQueries : Program 0 := .done false

def repeatedAlpha : Program 2 :=
  .query (.alpha ()) (fun _ => .query (.alpha ()) (fun _ => .done false))

def alphaFirst : Program 2 :=
  .query (.alpha ()) (fun _ => .query (.subset ((), false)) (fun _ => .done false))

def subsetFirst : Program 2 :=
  .query (.subset ((), false)) (fun _ => .query (.alpha ()) (fun _ => .done false))

/-- The final response is selected after both subset answers. -/
def responseGrinding : Program 3 :=
  .query (.alpha ()) (fun _ =>
    .query (.subset ((), false)) (fun first =>
      .query (.subset ((), true)) (fun _ => .done (if first.2 then true else false))))

/-- Grind subset answers before reading the fixed-key alpha answer. -/
def subsetGrinding : Program 3 :=
  .query (.subset ((), false)) (fun first =>
    .query (.subset ((), true)) (fun _ =>
      .query (.alpha ()) (fun _ => .done (if first.2 then true else false))))

/-- Earlier subset answers decide when to query the fixed alpha key. -/
def adaptiveAlphaTiming : Program 3 :=
  .query (.subset ((), false)) (fun first =>
    if first.2 then
      .query (.subset ((), true)) (fun _ => .query (.alpha ()) (fun _ => .done true))
    else .query (.alpha ()) (fun _ => .done false))

/-- The verifier appends alpha, and may also append the selected subset key. -/
def subsetOnlyGrinding : Program 1 :=
  .query (.subset ((), false)) (fun first => .done (if first.2 then true else false))

def repeatedSubset : Program 2 :=
  .query (.subset ((), false)) (fun _ =>
    .query (.subset ((), false)) (fun _ => .done false))

theorem no_queries_exact : failureRate noQueries = 1 / 4 := by native_decide
theorem repeated_alpha_exact : failureRate repeatedAlpha = 1 / 4 := by native_decide
theorem alpha_first_exact : failureRate alphaFirst = 1 / 4 := by native_decide
theorem subset_first_exact : failureRate subsetFirst = 1 / 4 := by native_decide
theorem response_grinding_exact : failureRate responseGrinding = 3 / 8 := by native_decide
theorem subset_grinding_exact : failureRate subsetGrinding = 3 / 8 := by native_decide
theorem adaptive_alpha_timing_exact : failureRate adaptiveAlphaTiming = 3 / 8 := by native_decide
theorem subset_only_grinding_exact : failureRate subsetOnlyGrinding = 3 / 8 := by native_decide
theorem repeated_subset_exact : failureRate repeatedSubset = 1 / 4 := by native_decide

/-- Multi-response selection really exceeds the single IOP error. -/
theorem grinding_exceeds_iop : 1 / 4 < failureRate responseGrinding := by
  rw [response_grinding_exact]; norm_num

/-- Every operational fixture is covered by the same general compiler. -/
theorem all_programs_bound {N : ℕ} (program : Program N) :
    failureRate program ≤ min 1 (((N + 2) * (N + 1) : ℕ) * (1 / 4 : ℚ)) := by
  have h := extraction_ratio_le_capped program (false, false) () id bad (1 / 4) bound
  unfold failureRate
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro tape htape
  simpa only [mem_filter, mem_univ, true_and, id_eq] using htape



/-- Pre-sampling removes the query-order factor, including verifier completion. -/
theorem all_programs_fixed_key_bound {N : ℕ} (program : Program N) :
    failureRate program ≤ min 1 ((N + 1 : ℕ) * (1 / 4 : ℚ)) := by
  have h := FixedKey.extraction_ratio_le_capped program (false, false) () id bad (1 / 4) bound
  unfold failureRate
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro tape htape
  simpa only [mem_filter, mem_univ, true_and, id_eq] using htape

/-- Omitting both defining queries still leaves one IOP experiment. -/
theorem no_queries_fixed_key_tight :
    failureRate noQueries = FixedKey.errorBound 0 (1 / 4) := by
  rw [no_queries_exact]
  norm_num [FixedKey.errorBound]

end Bcs.EnvelopeFiatShamir.Test
