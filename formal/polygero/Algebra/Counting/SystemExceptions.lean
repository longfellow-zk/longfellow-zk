import polygero.Algebra.FiniteProbability

/-! Finite counting for the largest exceptional query fraction. System exceptions need
only marginal bounds; no independence or bound on the number of sets is assumed. -/
namespace RecursivePolygero.SystemException
open Finset
attribute [local instance] Classical.propDecidable

theorem exists_upper_subset {I : Type*} [DecidableEq I]
    (S : Finset I) (a : I → ℚ) (q : ℕ) (hq : q ≤ S.card) :
    ∃ T ⊆ S, T.card = q ∧ ∀ i ∈ T, ∀ j ∈ S \ T, a j ≤ a i := by
  obtain ⟨U,hUS,hU⟩ := exists_subset_card_eq hq
  obtain ⟨T,hT,hmax⟩ := exists_max_image (S.powersetCard q) (fun T => ∑ i ∈ T, a i)
    ⟨U,mem_powersetCard.mpr ⟨hUS,hU⟩⟩
  obtain ⟨hTS,hcard⟩ := mem_powersetCard.mp hT
  refine ⟨T,hTS,hcard,?_⟩
  intro i hi j hj
  have hjS := (mem_sdiff.mp hj).1
  have hjT := (mem_sdiff.mp hj).2
  have hjE : j ∉ T.erase i := fun h => hjT (mem_of_mem_erase h)
  have hswap : insert j (T.erase i) ∈ S.powersetCard q := by
    apply mem_powersetCard.mpr
    refine ⟨insert_subset hjS ((erase_subset i T).trans hTS), ?_⟩
    rw [card_insert_of_notMem hjE, card_erase_of_mem hi]
    have := card_pos.mpr ⟨i,hi⟩
    omega
  have hs := hmax _ hswap
  rw [sum_insert hjE] at hs
  have he := sum_erase_add T a hi
  linarith

noncomputable def maximum {I : Type*} [Fintype I]
    (a : I → ℚ) (exceptional : I → Prop) (θ : ℚ) : ℚ :=
  (insert θ ((univ.filter exceptional).image a)).max' (by simp)

theorem maximum_le {I : Type*} [Fintype I]
    (a : I → ℚ) (exceptional : I → Prop) (θ z : ℚ)
    (hθ : θ ≤ z) (ha : ∀ i, exceptional i → a i ≤ z) : maximum a exceptional θ ≤ z := by
  apply max'_le
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hθ
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact ha i (mem_filter.mp hi).2

theorem le_maximum {I : Type*} [Fintype I]
    (a : I → ℚ) (exceptional : I → Prop) (θ : ℚ) : θ ≤ maximum a exceptional θ :=
  le_max' _ _ (mem_insert_self _ _)

theorem entry_le_maximum {I : Type*} [Fintype I]
    (a : I → ℚ) (exceptional : I → Prop) (θ : ℚ) (i : I) (hi : exceptional i) :
    a i ≤ maximum a exceptional θ :=
  le_max' _ _ (mem_insert_of_mem (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩))

/-- Capped weights are maximized on the largest entries. -/
theorem weighted_sum_le_small_sum {I : Type*} [Fintype I] [DecidableEq I]
    (a w : I → ℚ) (L C : ℚ) (q : ℕ) (hq : 0 < q)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ L)
    (hL : 0 ≤ L) (htotal : ∑ i, w i ≤ (q : ℚ)*L)
    (hsmall : ∀ T : Finset I, T.card ≤ q → ∑ i ∈ T, a i ≤ C) :
    ∑ i, w i*a i ≤ L*C := by
  by_cases hcard : Fintype.card I ≤ q
  · calc
      ∑ i, w i*a i ≤ ∑ i, L*a i := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hwL i) (ha i)
      _ = L*∑ i, a i := (mul_sum ..).symm
      _ ≤ L*C := mul_le_mul_of_nonneg_left (hsmall univ (by simpa using hcard)) hL
  · obtain ⟨T,_,hT,hupper⟩ := exists_upper_subset (univ : Finset I) a q (by simpa using Nat.le_of_lt (Nat.lt_of_not_ge hcard))
    obtain ⟨j,hj,hmin⟩ := exists_min_image T a (card_pos.mp (by omega))
    have hout (i) (hi : i ∉ T) : a i ≤ a j := hupper j hj i (by simp [hi])
    have hp (i) : w i*a i ≤ w i*a j + if i ∈ T then L*(a i-a j) else 0 := by
      by_cases hi : i ∈ T
      · rw [if_pos hi]
        have := mul_le_mul_of_nonneg_right (hwL i) (sub_nonneg.mpr (hmin i hi))
        nlinarith
      · rw [if_neg hi,add_zero]
        exact mul_le_mul_of_nonneg_left (hout i hi) (hw i)
    have h := sum_le_sum (s := univ) fun i _ => hp i
    simp only [sum_add_distrib,← sum_mul,sum_ite_mem,univ_inter,← mul_sum] at h
    have hb := mul_le_mul_of_nonneg_right htotal (ha j)
    have ht := mul_le_mul_of_nonneg_left (hsmall T hT.le) hL
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,hT] at h
    nlinarith


theorem exists_maximum_entry {I : Type*} [Fintype I]
    (a : I → ℚ) (E : I → Prop) (θ : ℚ) (h : θ < maximum a E θ) :
    ∃ i, E i ∧ maximum a E θ = a i := by
  have hm := max'_mem (insert θ ((univ.filter E).image a)) (by simp)
  rcases mem_insert.mp hm with he | he
  · exact (ne_of_gt h he).elim
  · obtain ⟨i,hi,he⟩ := mem_image.mp he
    exact ⟨i,(mem_filter.mp hi).2,he.symm⟩


theorem mean_finset_sum {I Γ : Type*} [Fintype Γ] (T : Finset I) (f : I → Γ → ℚ) :
    mean (fun γ => ∑ i ∈ T, f i γ) = ∑ i ∈ T, mean (f i) := by
  simp only [mean, sum_div]
  rw [sum_comm]

end RecursivePolygero.SystemException
