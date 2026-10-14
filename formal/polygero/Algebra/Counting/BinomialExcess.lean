import polygero.Algebra.Counting.DiscreteThreshold

/-! Binomial excess budgets for finite families of actual sets. -/
namespace RecursivePolygero.DirectBinomial
open Finset
variable {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]

omit [DecidableEq ι] in
private theorem normalized_sum_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (θ : ℚ) (hN : 0 < A.card.choose t) (hθ : θ ≤ 1)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, ((D i).card.choose t : ℚ)/A.card.choose t ≤
      1+((I.card : ℚ)-1)*θ := by
  by_cases he : I.card = 0
  · simp only [card_eq_zero.mp he,sum_empty,card_empty]
    norm_num
    linarith
  by_cases hs : I.card = 1
  · obtain ⟨i,rfl⟩ := card_eq_one.mp hs
    simp only [sum_singleton,card_singleton,Nat.cast_one,sub_self,zero_mul,add_zero]
    apply (div_le_one (by exact_mod_cast hN)).mpr
    exact_mod_cast Nat.choose_le_choose t (card_le_card (hD i (mem_singleton_self i)))
  exact DiscreteThreshold.sum_le_threshold (by omega) hIq (by positivity) hc
    (fun u => normalized_linear A I D t u ell hD ho hN (by omega))

omit [DecidableEq ι] in
/-- Any at most `q` binomial counts have total excess at most `N-U`.
The threshold condition is stated after division by the positive query count `N`. -/
theorem excess_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (U : ℚ) (hN : 0 < A.card.choose t)
    (hU : U ≤ A.card.choose t)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t)
      (U/A.card.choose t)) (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)-U) ≤ A.card.choose t-U := by
  classical
  let J := I.filter fun i => U < ((D i).card.choose t : ℚ)
  have hN' : (0 : ℚ) < A.card.choose t := by exact_mod_cast hN
  have hs := normalized_sum_le A J D t ell q (U/A.card.choose t) hN
    ((div_le_one hN').mpr hU) (fun i hi => hD i (mem_filter.mp hi).1)
    (fun i hi j hj => ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1) hc
    ((card_le_card (filter_subset _ _)).trans hIq)
  rw [← sum_div] at hs
  have hs' := (div_le_iff₀ hN').mp hs
  have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)-U)) =
      ∑ i ∈ J, (((D i).card.choose t : ℚ)-U) := by
    simp only [J,sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  rw [he,sum_sub_distrib,sum_const,nsmul_eq_mul]
  have hid : (1+((J.card : ℚ)-1)*(U/A.card.choose t))*(A.card.choose t) =
      A.card.choose t+((J.card : ℚ)-1)*U := by field_simp
  rw [hid] at hs'
  linarith

omit [DecidableEq ι] in
/-- The normalized form of the binomial excess budget. -/
theorem normalized_excess_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (θ : ℚ) (hN : 0 < A.card.choose t) (hθ : θ ≤ 1)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)/A.card.choose t-θ) ≤ 1-θ := by
  have hN' : (0 : ℚ) < A.card.choose t := by exact_mod_cast hN
  have h := excess_le A I D t ell q (θ*A.card.choose t) hN
    (by nlinarith only [hθ,hN']) hD ho
    (by simpa only [mul_div_cancel_right₀ _ hN'.ne'] using hc) hIq
  have he (i : ι) : max 0 (((D i).card.choose t : ℚ)/A.card.choose t-θ) =
      max 0 (((D i).card.choose t : ℚ)-θ*A.card.choose t)/A.card.choose t := by
    rw [← max_div_div_right hN'.le,zero_div,sub_div,mul_div_cancel_right₀ _ hN'.ne']
  simp_rw [he]
  rw [← sum_div]
  have hd := div_le_div_of_nonneg_right h hN'.le
  simpa only [sub_div,div_self hN'.ne',mul_div_cancel_right₀ _ hN'.ne'] using hd

end RecursivePolygero.DirectBinomial
