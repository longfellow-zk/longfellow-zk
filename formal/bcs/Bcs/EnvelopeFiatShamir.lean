import Bcs.TypedFiatShamir

/-! Response-uniform IOP errors compiled by fixed defining-query pairs.
Responses are read from the prefix of the subset query, never enumerated. -/
namespace Bcs.EnvelopeFiatShamir
open Finset Bcs.TypedFiatShamir
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {Alpha Subset Response : Type*}
variable [Fintype Alpha] [Fintype Subset] [DecidableEq Alpha] [DecidableEq Subset]
variable [Nonempty Alpha] [Nonempty Subset]

/-- A single envelope for all responses, fixed before both verifier coins. -/
structure ResponseUniformBound (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ) where
  envelope : Alpha → ℚ
  dominates : ∀ alpha response,
    ((univ.filter (bad alpha response)).card : ℚ) / Fintype.card Subset ≤ envelope alpha
  mean_le : (∑ alpha, envelope alpha) / Fintype.card Alpha ≤ epsilon

theorem ResponseUniformBound.strategy_bound
    {bad : Alpha → Response → Subset → Prop} {epsilon : ℚ}
    (bound : ResponseUniformBound bad epsilon) (respond : Alpha → Response) :
    ((univ.filter fun pair : Subset × Alpha => bad pair.2 (respond pair.2) pair.1).card : ℚ) /
      (Fintype.card Subset * Fintype.card Alpha) ≤ epsilon := by
  classical
  rw [Bcs.card_filter_prod_snd]
  push_cast
  have hs : (0 : ℚ) < Fintype.card Subset := by exact_mod_cast Fintype.card_pos
  have ha : (0 : ℚ) < Fintype.card Alpha := by exact_mod_cast Fintype.card_pos
  calc
    (∑ alpha, ((univ.filter (bad alpha (respond alpha))).card : ℚ)) /
        (Fintype.card Subset * Fintype.card Alpha)
        = (∑ alpha, ((univ.filter (bad alpha (respond alpha))).card : ℚ) /
            Fintype.card Subset) / Fintype.card Alpha := by
          simp only [div_eq_mul_inv, ← sum_mul]; ring
    _ ≤ (∑ alpha, bound.envelope alpha) / Fintype.card Alpha :=
      div_le_div_of_nonneg_right
        (sum_le_sum fun alpha _ => bound.dominates alpha (respond alpha)) ha.le
    _ ≤ epsilon := bound.mean_le

/-- Reinsert the two fresh projections into the retained tape data. -/
def pairTape {T : ℕ} (subsetSlot alphaSlot : Fin T) (_hne : subsetSlot ≠ alphaSlot)
    (data : TwoSlotData Alpha Subset T subsetSlot alphaSlot)
    (query : Subset) (alpha : Alpha) : Fin T → Answer Alpha Subset :=
  fun k => if hks : k = subsetSlot then (data.1.1, query)
    else if hka : k = alphaSlot then (alpha, data.1.2)
    else data.2 ⟨k, hks, hka⟩

theorem pairTape_of_tape {T : ℕ} (subsetSlot alphaSlot : Fin T)
    (hne : subsetSlot ≠ alphaSlot) (tape : Fin T → Answer Alpha Subset) :
    pairTape subsetSlot alphaSlot hne (twoSlotData subsetSlot alphaSlot tape)
      (subsetAnswer (tape subsetSlot)) (alphaAnswer (tape alphaSlot)) = tape := by
  funext k
  by_cases hs : k = subsetSlot
  · subst k; simp [pairTape, twoSlotData, alphaAnswer, subsetAnswer]
  · by_cases ha : k = alphaSlot
    · subst k; simp [pairTape, hs, twoSlotData, alphaAnswer, subsetAnswer]
    · simp [pairTape, hs, ha, twoSlotData]

/-- The subset projection cannot influence the response encoded in its query. -/
theorem pairTape_agree_before {T : ℕ} (subsetSlot alphaSlot : Fin T)
    (hne : subsetSlot ≠ alphaSlot)
    (data : TwoSlotData Alpha Subset T subsetSlot alphaSlot)
    (left right : Subset) (alpha : Alpha) :
    ∀ k : Fin T, k.val < subsetSlot.val →
      pairTape subsetSlot alphaSlot hne data left alpha k =
        pairTape subsetSlot alphaSlot hne data right alpha k := by
  intro k hk
  have hs : k ≠ subsetSlot := by intro h; subst k; omega
  simp only [pairTape, dif_neg hs]

/-- A fixed pair of slots pays the strategy-uniform IOP error once. -/
theorem fixed_pair_ratio_le {T : ℕ} (subsetSlot alphaSlot : Fin T)
    (hne : subsetSlot ≠ alphaSlot)
    (responseAt : (Fin T → Answer Alpha Subset) → Response)
    (hprefix : ∀ left right, (∀ k : Fin T, k.val < subsetSlot.val → left k = right k) →
      responseAt left = responseAt right)
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    ((univ.filter fun tape : Fin T → Answer Alpha Subset =>
      bad (alphaAnswer (tape alphaSlot)) (responseAt tape)
        (subsetAnswer (tape subsetSlot))).card : ℚ) /
      Fintype.card (Fin T → Answer Alpha Subset) ≤ epsilon := by
  classical
  let defaultQuery : Subset := Classical.choice (inferInstance : Nonempty Subset)
  let respond := fun data alpha =>
    responseAt (pairTape subsetSlot alphaSlot hne data defaultQuery alpha)
  let success := fun data query alpha => bad alpha (respond data alpha) query
  have heq (tape : Fin T → Answer Alpha Subset) :
      respond (twoSlotData subsetSlot alphaSlot tape) (alphaAnswer (tape alphaSlot)) =
        responseAt tape := by
    unfold respond
    apply hprefix
    have h := pairTape_agree_before subsetSlot alphaSlot hne
      (twoSlotData subsetSlot alphaSlot tape) defaultQuery
      (subsetAnswer (tape subsetSlot)) (alphaAnswer (tape alphaSlot))
    rw [pairTape_of_tape] at h
    exact h
  have h := two_projection_dependent_tape_ratio_le subsetSlot alphaSlot hne success epsilon
    (fun data => bound.strategy_bound (respond data))
  simpa only [success, heq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using h

section LazyExecution
variable {AlphaKey Output : Type*} [DecidableEq AlphaKey] [DecidableEq Response]
variable {N : ℕ}
variable (adversary : Merkle.RandomOracle.Tree
  (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
variable (dflt : Answer Alpha Subset) (alphaKey : AlphaKey) (responseOf : Output → Response)

def trace := lazyFirstOccurrenceTrace N adversary dflt (fun _ => alphaKey)
  (fun output => (alphaKey, responseOf output))

/-- Either order has a response determined strictly before its subset answer. -/
noncomputable def responseBeforeSubset (subsetSlot alphaSlot : Fin (N + 2))
    (tape : Fin (N + 2) → Answer Alpha Subset) : Response :=
  if alphaSlot < subsetSlot then
    (canonicalCaseAFloorSubsetKey adversary dflt alphaKey responseOf subsetSlot
      (Sumcheck.extract_prefix tape subsetSlot)).2
  else canonicalResponseAtSlot adversary dflt
    (alphaKey, responseOf (Merkle.RandomOracle.lazyRun
      (fun _ : Fin (N + 2) => dflt) dflt adversary []).1)
    subsetSlot tape

theorem responseBeforeSubset_congr (subsetSlot alphaSlot : Fin (N + 2))
    (left right : Fin (N + 2) → Answer Alpha Subset)
    (hprefix : ∀ k : Fin (N + 2), k.val < subsetSlot.val → left k = right k) :
    responseBeforeSubset adversary dflt alphaKey responseOf subsetSlot alphaSlot left =
      responseBeforeSubset adversary dflt alphaKey responseOf subsetSlot alphaSlot right := by
  unfold responseBeforeSubset
  split
  · congr 2
    funext k
    exact hprefix ⟨k.val, by omega⟩ k.isLt
  · exact canonicalResponseAtSlot_congr adversary dflt _ subsetSlot left right hprefix

theorem responseBeforeSubset_eq (tape : Fin (N + 2) → Answer Alpha Subset) :
    responseBeforeSubset adversary dflt alphaKey responseOf
      ((trace adversary dflt alphaKey responseOf).subsetSlot tape)
      ((trace adversary dflt alphaKey responseOf).alphaSlot tape) tape =
      responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1 := by
  let tr := trace adversary dflt alphaKey responseOf
  by_cases horder : tr.alphaSlot tape < tr.subsetSlot tape
  · have hcase : tr.caseA (fun _ => False) (fun _ => True) (fun _ => False)
        (tr.subsetSlot tape) tape := by
      exact ⟨trivial, not_false, horder, Or.inl ⟨not_false, rfl⟩⟩
    have h := canonicalCaseAFloorSubsetKey_eq adversary dflt alphaKey responseOf
      (fun _ => False) (fun _ => True) (fun _ => False) (tr.subsetSlot tape) tape hcase not_false
    simpa [responseBeforeSubset, tr, horder] using congrArg Prod.snd h
  · have hlt : tr.subsetSlot tape < tr.alphaSlot tape :=
      lt_of_le_of_ne (le_of_not_gt horder) (tr.alphaSlot_ne_subsetSlot tape).symm
    have hcase : tr.caseB (fun _ => True) (fun _ => False) (tr.subsetSlot tape) tape :=
      ⟨trivial, not_false, rfl, hlt⟩
    have h := canonicalResponseAtSlot_eq_of_caseB adversary dflt (fun _ => alphaKey)
      responseOf (alphaKey, responseOf (Merkle.RandomOracle.lazyRun
        (fun _ : Fin (N + 2) => dflt) dflt adversary []).1)
      (fun _ => True) (fun _ => False) (tr.subsetSlot tape) tape hcase
    simpa [responseBeforeSubset, tr, horder] using h

/-- Union over a fixed finite family; the indices never depend on the tape. -/
theorem finite_union_ratio_le {Index Omega : Type*}
    [Fintype Index] [Fintype Omega] [Nonempty Omega]
    (event : Omega → Prop) (piece : Index → Omega → Prop)
    (epsilon : ℚ) (hcover : ∀ omega, event omega → ∃ index, piece index omega)
    (hpiece : ∀ index, ((univ.filter (piece index)).card : ℚ) / Fintype.card Omega ≤ epsilon) :
    ((univ.filter event).card : ℚ) / Fintype.card Omega ≤ Fintype.card Index * epsilon := by
  classical
  have hcoverSet : univ.filter event ⊆ univ.biUnion (fun index => univ.filter (piece index)) := by
    intro omega h
    obtain ⟨index, hi⟩ := hcover omega (mem_filter.mp h).2
    exact mem_biUnion.mpr ⟨index, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hcard := (card_le_card hcoverSet).trans card_biUnion_le
  have hpos : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  calc
    ((univ.filter event).card : ℚ) / Fintype.card Omega ≤
        ((∑ index, (univ.filter (piece index)).card : ℕ) : ℚ) / Fintype.card Omega :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos.le
    _ = ∑ index, ((univ.filter (piece index)).card : ℚ) / Fintype.card Omega := by
      simp [div_eq_mul_inv, sum_mul]
    _ ≤ ∑ _index : Index, epsilon := sum_le_sum (fun index _ => hpiece index)
    _ = Fintype.card Index * epsilon := by simp

abbrev DistinctSlotPairs (T : ℕ) := { pair : Fin T × Fin T // pair.1 ≠ pair.2 }

theorem card_distinctSlotPairs (T : ℕ) : Fintype.card (DistinctSlotPairs T) = T * (T - 1) := by
  classical
  rw [Fintype.card_subtype, Bcs.card_filter_prod_fst]
  have hfilter (i : Fin T) : (univ.filter fun j : Fin T => i ≠ j) = univ.erase i := by
    ext j; simp [ne_comm]
  simp [hfilter]

/-- Adaptive typed FS extraction error with no response-list multiplier.
The two defining queries are installed even when the adversary omitted them. -/
theorem extraction_ratio_le
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    ((univ.filter fun tape : Fin (N + 2) → Answer Alpha Subset =>
      bad (definingAlphaAnswer tr tape)
        (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
        (definingSubsetAnswer tr tape)).card : ℚ) /
      Fintype.card (Fin (N + 2) → Answer Alpha Subset) ≤
      ((N + 2) * (N + 1) : ℕ) * epsilon := by
  classical
  dsimp only
  let piece := fun pair : DistinctSlotPairs (N + 2) => fun tape =>
    bad (alphaAnswer (tape pair.1.2))
      (responseBeforeSubset adversary dflt alphaKey responseOf pair.1.1 pair.1.2 tape)
      (subsetAnswer (tape pair.1.1))
  have h := finite_union_ratio_le _ piece epsilon (by
    intro tape htape
    let tr := trace adversary dflt alphaKey responseOf
    refine ⟨⟨(tr.subsetSlot tape, tr.alphaSlot tape),
      (tr.alphaSlot_ne_subsetSlot tape).symm⟩, ?_⟩
    simpa only [piece, responseBeforeSubset_eq, definingAlphaAnswer, definingSubsetAnswer, tr] using htape)
    (fun pair => fixed_pair_ratio_le pair.1.1 pair.1.2 pair.2
      (responseBeforeSubset adversary dflt alphaKey responseOf pair.1.1 pair.1.2)
      (responseBeforeSubset_congr adversary dflt alphaKey responseOf pair.1.1 pair.1.2)
      bad epsilon bound)
  simpa only [card_distinctSlotPairs, show N + 2 - 1 = N + 1 by omega,
    definingAlphaAnswer, definingSubsetAnswer] using h

/-- Exact probability cap, useful for arbitrary query budgets. -/
theorem extraction_ratio_le_capped
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    ((univ.filter fun tape : Fin (N + 2) → Answer Alpha Subset =>
      bad (definingAlphaAnswer tr tape)
        (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
        (definingSubsetAnswer tr tape)).card : ℚ) /
      Fintype.card (Fin (N + 2) → Answer Alpha Subset) ≤
      min 1 (((N + 2) * (N + 1) : ℕ) * epsilon) := by
  apply le_min
  · exact (div_le_one₀ (by exact_mod_cast Fintype.card_pos)).mpr
      (by exact_mod_cast card_filter_le _ _)
  · exact extraction_ratio_le adversary dflt alphaKey responseOf bad epsilon bound

end LazyExecution
end Bcs.EnvelopeFiatShamir
