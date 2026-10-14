import Bcs.LinearEnvelopeFiatShamir
import Bcs.FiniteProbability

/-! Pre-sampling the fixed defining alpha key removes the query-order loss.
The operational lazy trace and verifier completion are unchanged. -/
namespace Bcs.EnvelopeFiatShamir.FixedKey
open Finset Bcs.TypedFiatShamir Bcs.FiniteProbability
open scoped Classical BigOperators
set_option maxHeartbeats 4000000

def errorBound (queryBudget : ℕ) (epsilon : ℚ) : ℚ :=
  min 1 ((queryBudget+1 : ℕ)*epsilon)

theorem errorBound_dyadic (queryBudget coefficientBits : ℕ) :
    errorBound queryBudget ((1 : ℚ)/2^coefficientBits) =
      min 1 ((queryBudget+1 : ℚ)/2^coefficientBits) := by
  unfold errorBound
  push_cast
  congr 1
  ring

variable {Alpha Subset Response : Type*}
variable [Fintype Alpha] [Fintype Subset]
variable [Nonempty Alpha] [Nonempty Subset]

abbrev SubsetSlotData (T : ℕ) (i : Fin T) :=
  Alpha × ({k : Fin T // k ≠ i} → Answer Alpha Subset)

def subsetTape {T : ℕ} (i : Fin T) (data : SubsetSlotData (Alpha := Alpha) (Subset := Subset) T i)
    (s : Subset) : Fin T → Answer Alpha Subset :=
  fun k => if h : k = i then (data.1,s) else data.2 ⟨k,h⟩

noncomputable def splitSubsetTape {T : ℕ} (i : Fin T) :
    (Fin T → Answer Alpha Subset) ≃ SubsetSlotData (Alpha := Alpha) (Subset := Subset) T i × Subset where
  toFun tape := ((alphaAnswer (tape i),fun k => tape k.1),subsetAnswer (tape i))
  invFun x := subsetTape i x.1 x.2
  left_inv tape := by
    funext k
    by_cases hk : k = i <;> simp [subsetTape,hk,alphaAnswer,subsetAnswer]
  right_inv x := by
    rcases x with ⟨⟨a,rest⟩,s⟩
    simp only [subsetTape,alphaAnswer,subsetAnswer]
    congr 2
    funext k
    simp [k.property]

/-- The charged subset projection is fresh; the gate and response are known
before it. Alpha is fixed as an external parameter. -/
theorem gated_subset_slot_le {T : ℕ} (i : Fin T) (a : Alpha)
    (responseAt : (Fin T → Answer Alpha Subset) → Response)
    (hresponse : ∀ left right, (∀ k, k.val < i.val → left k = right k) →
      responseAt left = responseAt right)
    (gate : (Fin T → Answer Alpha Subset) → Prop)
    (hgate : ∀ left right, (∀ k, k.val < i.val → left k = right k) →
      (gate left ↔ gate right))
    (bad : Alpha → Response → Subset → Prop) (budget : ℚ)
    (bound : ∀ response, density (bad a response) ≤ budget) :
    density (fun tape => gate tape ∧ bad a (responseAt tape) (subsetAnswer (tape i))) ≤
      budget*density gate := by
  classical
  let s₀ : Subset := Classical.choice (inferInstance : Nonempty Subset)
  let base := fun data : SubsetSlotData (Alpha := Alpha) (Subset := Subset) T i => subsetTape i data s₀
  let gateData := fun data => gate (base data)
  let success := fun data s => bad a (responseAt (base data)) s
  have hprefix (tape : Fin T → Answer Alpha Subset) : ∀ k, k.val < i.val →
      base ((splitSubsetTape i) tape).1 k = tape k := by
    intro k hk
    have hki : k ≠ i := by intro he; subst k; exact (lt_irrefl _) hk
    simp [base,subsetTape,splitSubsetTape,hki]
  have hg (tape : Fin T → Answer Alpha Subset) :
      gateData ((splitSubsetTape i) tape).1 ↔ gate tape := hgate _ _ (hprefix tape)
  have hr (tape : Fin T → Answer Alpha Subset) :
      responseAt (base ((splitSubsetTape i) tape).1) = responseAt tape :=
    hresponse _ _ (hprefix tape)
  have he : density (fun tape => gate tape ∧ bad a (responseAt tape) (subsetAnswer (tape i))) =
      density (fun x : SubsetSlotData (Alpha := Alpha) (Subset := Subset) T i × Subset =>
        gateData x.1 ∧ success x.1 x.2) := by
    rw [← density_equiv (splitSubsetTape i)]
    apply density_congr
    intro tape
    change (gate tape ∧ bad a (responseAt tape) (subsetAnswer (tape i))) ↔
      (gateData ((splitSubsetTape i) tape).1 ∧
        bad a (responseAt (base ((splitSubsetTape i) tape).1)) (subsetAnswer (tape i)))
    rw [hg tape,hr tape]
  have hegate : density gate = density gateData := by
    rw [← density_product_gate (Pair := Subset) gateData,
      ← density_equiv (splitSubsetTape i)]
    exact density_congr fun tape => (hg tape).symm
  rw [he,hegate]
  exact density_product_gate_le gateData success budget (fun data => bound _)

section Execution
variable {AlphaKey Output : Type*} [DecidableEq AlphaKey] [DecidableEq Response]
variable {N : ℕ}
variable (adversary : Merkle.RandomOracle.Tree
  (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
variable (dflt : Answer Alpha Subset) (alphaKey : AlphaKey) (responseOf : Output → Response)

noncomputable def injectAlpha (a : Alpha) (tape : Fin (N+2) → Answer Alpha Subset) :
    Fin (N+2) → Answer Alpha Subset :=
  fun k => if (trace adversary dflt alphaKey responseOf).alphaSlot tape = k then
    (a,subsetAnswer (tape k)) else tape k

omit [Nonempty Alpha] [Nonempty Subset] in
theorem injectAlpha_before (a : Alpha) (tape : Fin (N+2) → Answer Alpha Subset) :
    ∀ k, k.val < ((trace adversary dflt alphaKey responseOf).alphaSlot tape).val →
      injectAlpha adversary dflt alphaKey responseOf a tape k = tape k := by
  intro k hk
  have hne : (trace adversary dflt alphaKey responseOf).alphaSlot tape ≠ k := by
    intro he; rw [he] at hk; exact (lt_irrefl _) hk
  simp [injectAlpha,hne]

omit [Nonempty Alpha] [Nonempty Subset] in
theorem injectAlpha_slot (a : Alpha) (tape : Fin (N+2) → Answer Alpha Subset) :
    (trace adversary dflt alphaKey responseOf).alphaSlot
      (injectAlpha adversary dflt alphaKey responseOf a tape) =
        (trace adversary dflt alphaKey responseOf).alphaSlot tape := by
  have h := Linear.alphaSlot_gate_congr adversary dflt alphaKey responseOf
    ((trace adversary dflt alphaKey responseOf).alphaSlot tape)
    (injectAlpha adversary dflt alphaKey responseOf a tape) tape
    (injectAlpha_before adversary dflt alphaKey responseOf a tape)
  exact h.mpr rfl

omit [Nonempty Alpha] [Nonempty Subset] in
theorem injectAlpha_alpha (a : Alpha) (tape : Fin (N+2) → Answer Alpha Subset) :
    definingAlphaAnswer (trace adversary dflt alphaKey responseOf)
      (injectAlpha adversary dflt alphaKey responseOf a tape) = a := by
  unfold definingAlphaAnswer
  rw [injectAlpha_slot]
  simp [injectAlpha,alphaAnswer]

omit [Nonempty Alpha] [Nonempty Subset] in
theorem injectAlpha_subset (a : Alpha) (tape : Fin (N+2) → Answer Alpha Subset) (k : Fin (N+2)) :
    subsetAnswer (injectAlpha adversary dflt alphaKey responseOf a tape k) = subsetAnswer (tape k) := by
  unfold injectAlpha
  split <;> rfl

omit [Nonempty Alpha] [Nonempty Subset] in
theorem injectAlpha_prefix_congr (a : Alpha) (i : Fin (N+2))
    (left right : Fin (N+2) → Answer Alpha Subset)
    (hprefix : ∀ k, k.val < i.val → left k = right k) :
    ∀ k, k.val < i.val → injectAlpha adversary dflt alphaKey responseOf a left k =
      injectAlpha adversary dflt alphaKey responseOf a right k := by
  intro k hk
  have hgate := Linear.alphaSlot_gate_congr adversary dflt alphaKey responseOf k left right
    (fun j hj => hprefix j (hj.trans hk))
  unfold injectAlpha
  rw [hprefix k hk]
  simp only [hgate]

noncomputable def swapAlpha : (Alpha × (Fin (N+2) → Answer Alpha Subset)) ≃
    Alpha × (Fin (N+2) → Answer Alpha Subset) := by
  let f := fun x : Alpha × (Fin (N+2) → Answer Alpha Subset) =>
    (definingAlphaAnswer (trace adversary dflt alphaKey responseOf) x.2,
      injectAlpha adversary dflt alphaKey responseOf x.1 x.2)
  have hf : Function.Involutive f := by
    intro x
    apply Prod.ext
    · exact injectAlpha_alpha adversary dflt alphaKey responseOf x.1 x.2
    · change injectAlpha adversary dflt alphaKey responseOf
        (definingAlphaAnswer (trace adversary dflt alphaKey responseOf) x.2)
        (injectAlpha adversary dflt alphaKey responseOf x.1 x.2) = x.2
      funext k
      simp only [injectAlpha, injectAlpha_slot]
      by_cases h : (trace adversary dflt alphaKey responseOf).alphaSlot x.2 = k
      · simp only [h, if_true, subsetAnswer, definingAlphaAnswer, alphaAnswer]
      · simp only [h, if_false]
  exact {toFun := f, invFun := f, left_inv := hf, right_inv := hf}

noncomputable def responseAt (a : Alpha) (i : Fin (N+2))
    (tape : Fin (N+2) → Answer Alpha Subset) : Response :=
  responseBeforeSubset adversary dflt alphaKey responseOf i
    ((trace adversary dflt alphaKey responseOf).alphaSlot tape)
    (injectAlpha adversary dflt alphaKey responseOf a tape)

theorem responseAt_congr (a : Alpha) (i : Fin (N+2))
    (left right : Fin (N+2) → Answer Alpha Subset)
    (hprefix : ∀ k, k.val < i.val → left k = right k) :
    responseAt adversary dflt alphaKey responseOf a i left =
      responseAt adversary dflt alphaKey responseOf a i right := by
  let tr := trace adversary dflt alphaKey responseOf
  have hinject := injectAlpha_prefix_congr adversary dflt alphaKey responseOf a i left right hprefix
  by_cases hleft : tr.alphaSlot left < i
  · have heq : tr.alphaSlot right = tr.alphaSlot left :=
      (Linear.alphaSlot_gate_congr adversary dflt alphaKey responseOf (tr.alphaSlot left)
        left right (fun k hk => hprefix k (hk.trans hleft))).mp rfl
    unfold responseAt
    rw [heq]
    exact responseBeforeSubset_congr adversary dflt alphaKey responseOf i _ _ _ hinject
  · have hright : ¬tr.alphaSlot right < i := by
      intro hr
      have heq : tr.alphaSlot left = tr.alphaSlot right :=
        (Linear.alphaSlot_gate_congr adversary dflt alphaKey responseOf (tr.alphaSlot right)
          right left (fun k hk => (hprefix k (hk.trans hr)).symm)).mp rfl
      rw [heq] at hleft
      exact hleft hr
    change ¬(trace adversary dflt alphaKey responseOf).alphaSlot left < i at hleft
    change ¬(trace adversary dflt alphaKey responseOf).alphaSlot right < i at hright
    simp only [responseAt,responseBeforeSubset,hleft,hright,if_false]
    exact canonicalResponseAtSlot_congr adversary dflt _ i _ _ hinject

theorem responseAt_eq (a : Alpha) (i : Fin (N+2))
    (tape : Fin (N+2) → Answer Alpha Subset)
    (hi : (trace adversary dflt alphaKey responseOf).subsetSlot
      (injectAlpha adversary dflt alphaKey responseOf a tape) = i) :
    responseAt adversary dflt alphaKey responseOf a i tape =
      responseOf (Merkle.RandomOracle.lazyRun
        (injectAlpha adversary dflt alphaKey responseOf a tape) dflt adversary []).1 := by
  have h := responseBeforeSubset_eq adversary dflt alphaKey responseOf
    (injectAlpha adversary dflt alphaKey responseOf a tape)
  rw [hi,injectAlpha_slot] at h
  exact h

theorem presampled_at_slot_le (a : Alpha) (i : Fin (N+2))
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    density (fun tape =>
      tr.subsetSlot (injectAlpha adversary dflt alphaKey responseOf a tape) = i ∧
      bad (definingAlphaAnswer tr (injectAlpha adversary dflt alphaKey responseOf a tape))
        (responseOf (Merkle.RandomOracle.lazyRun
          (injectAlpha adversary dflt alphaKey responseOf a tape) dflt adversary []).1)
        (definingSubsetAnswer tr (injectAlpha adversary dflt alphaKey responseOf a tape))) ≤
      bound.envelope a*density (fun tape => tr.alphaSlot tape ≠ i) := by
  classical
  dsimp only
  let tr := trace adversary dflt alphaKey responseOf
  have h := gated_subset_slot_le i a (responseAt adversary dflt alphaKey responseOf a i)
    (responseAt_congr adversary dflt alphaKey responseOf a i)
    (fun tape => tr.alphaSlot tape ≠ i)
    (fun left right hp => not_congr
      (Linear.alphaSlot_gate_congr adversary dflt alphaKey responseOf i left right hp))
    bad (bound.envelope a)
    (fun response => density_le_of_ratio_le (bad a response) (bound.envelope a)
      (bound.dominates a response))
  refine (density_mono ?_).trans h
  intro tape hp
  have hg : tr.alphaSlot tape ≠ i := by
    have hne := tr.alphaSlot_ne_subsetSlot (injectAlpha adversary dflt alphaKey responseOf a tape)
    rw [injectAlpha_slot, hp.1] at hne
    exact hne
  refine ⟨hg,?_⟩
  rw [responseAt_eq adversary dflt alphaKey responseOf a i tape hp.1]
  have hb := hp.2
  rw [injectAlpha_alpha] at hb
  unfold definingSubsetAnswer at hb
  rw [hp.1,injectAlpha_subset] at hb
  exact hb

theorem presampled_density_le (a : Alpha)
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    density (fun tape =>
      bad (definingAlphaAnswer tr (injectAlpha adversary dflt alphaKey responseOf a tape))
        (responseOf (Merkle.RandomOracle.lazyRun
          (injectAlpha adversary dflt alphaKey responseOf a tape) dflt adversary []).1)
        (definingSubsetAnswer tr (injectAlpha adversary dflt alphaKey responseOf a tape))) ≤
      (N+1 : ℕ)*bound.envelope a := by
  classical
  dsimp only
  let tr := trace adversary dflt alphaKey responseOf
  let failure := fun tape => bad (definingAlphaAnswer tr tape)
    (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1) (definingSubsetAnswer tr tape)
  let piece := fun (i : Fin (N+2)) tape =>
    tr.subsetSlot (injectAlpha adversary dflt alphaKey responseOf a tape) = i ∧
      failure (injectAlpha adversary dflt alphaKey responseOf a tape)
  have hpiece (i : Fin (N+2)) : density (piece i) ≤
      bound.envelope a*density (fun tape => tr.alphaSlot tape ≠ i) :=
    presampled_at_slot_le adversary dflt alphaKey responseOf a i bad epsilon bound
  have hg : (∑ i : Fin (N+2), density (fun tape => tr.alphaSlot tape ≠ i)) = (N+1 : ℕ) := by
    simp_rw [density_not]
    rw [sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,density_selector_sum tr.alphaSlot]
    push_cast
    ring
  calc
    _ ≤ ∑ i, density (piece i) := density_union_le _ piece
      (fun tape h => ⟨tr.subsetSlot (injectAlpha adversary dflt alphaKey responseOf a tape),rfl,h⟩)
    _ ≤ ∑ i, bound.envelope a*density (fun tape => tr.alphaSlot tape ≠ i) :=
      sum_le_sum fun i _ => hpiece i
    _ = _ := by rw [← mul_sum,hg]; ring

/-- Each completed trace has at most `N+1` non-alpha slots. Pre-sampling
allows the same conditional envelope to pay for both defining-query orders. -/
theorem extraction_density_le
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    density (fun tape => bad (definingAlphaAnswer tr tape)
      (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
      (definingSubsetAnswer tr tape)) ≤ (N+1 : ℕ)*epsilon := by
  classical
  dsimp only
  let tr := trace adversary dflt alphaKey responseOf
  let failure := fun tape : Fin (N+2) → Answer Alpha Subset => bad (definingAlphaAnswer tr tape)
    (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1) (definingSubsetAnswer tr tape)
  have he : density failure = density (fun x : Alpha × (Fin (N+2) → Answer Alpha Subset) =>
      failure (injectAlpha adversary dflt alphaKey responseOf x.1 x.2)) := by
    calc
      _ = density (fun x : Alpha × (Fin (N+2) → Answer Alpha Subset) => failure x.2) :=
        (density_product_snd failure).symm
      _ = density (fun x => failure ((swapAlpha adversary dflt alphaKey responseOf) x).2) :=
        (density_equiv (swapAlpha adversary dflt alphaKey responseOf) (fun x => failure x.2)).symm
      _ = _ := rfl
  rw [he]
  rw [density_product_average (fun a tape =>
    failure (injectAlpha adversary dflt alphaKey responseOf a tape))]
  have hq : (0 : ℚ) < Fintype.card Alpha := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (∑ a, (N+1 : ℕ)*bound.envelope a)/Fintype.card Alpha :=
      div_le_div_of_nonneg_right (sum_le_sum fun a _ =>
        presampled_density_le adversary dflt alphaKey responseOf a bad epsilon bound) hq.le
    _ = ((N+1 : ℕ) : ℚ)*((∑ a, bound.envelope a)/Fintype.card Alpha) := by rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound.mean_le (Nat.cast_nonneg _)

theorem extraction_ratio_le_capped
    (bad : Alpha → Response → Subset → Prop) (epsilon : ℚ)
    (bound : ResponseUniformBound bad epsilon) :
    let tr := trace adversary dflt alphaKey responseOf
    ((univ.filter fun tape => bad (definingAlphaAnswer tr tape)
      (responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
      (definingSubsetAnswer tr tape)).card : ℚ)/
        Fintype.card (Fin (N+2) → Answer Alpha Subset) ≤ errorBound N epsilon := by
  classical
  dsimp only
  unfold errorBound
  apply le_min
  · exact (div_le_one₀ (by exact_mod_cast Fintype.card_pos)).mpr
      (by exact_mod_cast card_filter_le _ _)
  · have h := extraction_density_le adversary dflt alphaKey responseOf bad epsilon bound
    refine le_trans ?_ h
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro tape htape
    simpa only [mem_filter,mem_univ,true_and] using htape

end Execution
end Bcs.EnvelopeFiatShamir.FixedKey
