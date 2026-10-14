import polygero.Algebra.FiniteProbability

namespace RecursivePolygero.DirectBinomial
open Finset
variable {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]

def total (I : Finset ι) (D : ι → Finset Ω) (t : ℕ) : ℕ :=
  ∑ i ∈ I, (D i).card.choose t

def pairs (I : Finset ι) (D : ι → Finset Ω) (t : ℕ) : ℕ :=
  ∑ ij ∈ I.offDiag, (D ij.1 ∩ D ij.2).card.choose t

theorem discrete_integer_bound (m u : ℕ) :
    2*u*m ≤ u*(u+1)+(m*m-m) := by
  have hsq : m ≤ m*m := by nlinarith
  have hi : (0 : ℤ) ≤ ((m : ℤ)-u)*((m : ℤ)-u-1) := by
    by_cases h : m ≤ u
    · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
    · apply mul_nonneg <;> omega
  have hn : (2*u*m : ℤ) ≤ u*(u+1)+(m*m-m) := by nlinarith only [hi]
  exact_mod_cast hn

omit [DecidableEq ι] in
/-- Count incidences once by queries and once by their containing sets. -/
theorem incidence_sum {κ : Type*} [DecidableEq κ] (Q : Finset κ)
    (I : Finset ι) (P : κ → ι → Prop) [DecidableRel P] :
    (∑ x ∈ Q, (I.filter (P x)).card) = ∑ i ∈ I, (Q.filter (fun x => P x i)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

omit [DecidableEq ι] in
/-- Double counting incidences in the actual sets gives the discrete linear
bound. No auxiliary supersets or numerical allowances are involved. -/
theorem linear_bound (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t u : ℕ) (hD : ∀ i ∈ I, D i ⊆ A) :
    2*u*total I D t ≤ u*(u+1)*A.card.choose t+pairs I D t := by
  classical
  let Q := A.powersetCard t
  let covers := fun (q : Finset Ω) (i : ι) => q ⊆ D i
  have hf (B : Finset Ω) (hB : B ⊆ A) :
      (Q.filter (fun q => q ⊆ B)).card = B.card.choose t := by
    have he : Q.filter (fun q => q ⊆ B) = B.powersetCard t := by
      ext q
      simp only [Q,mem_filter,mem_powersetCard]
      exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans hB,h.2⟩,h.1⟩⟩
    rw [he,card_powersetCard]
  have htotal : (∑ q ∈ Q, (I.filter (covers q)).card) = total I D t := by
    rw [incidence_sum]
    apply sum_congr rfl
    intro i hi
    exact hf _ (hD i hi)
  have hpair : (∑ q ∈ Q, ((I.filter (covers q)).card * (I.filter (covers q)).card -
      (I.filter (covers q)).card)) = pairs I D t := by
    have he (q : Finset Ω) : (I.filter (covers q)).offDiag =
        I.offDiag.filter (fun ij => q ⊆ D ij.1 ∩ D ij.2) := by
      ext ij
      simp only [mem_offDiag,mem_filter,subset_inter_iff,covers]
      tauto
    simp_rw [← offDiag_card,he]
    rw [incidence_sum]
    apply sum_congr rfl
    intro ij hij
    obtain ⟨hi,_,_⟩ := mem_offDiag.mp hij
    exact hf _ (inter_subset_left.trans (hD _ hi))
  have hb := sum_le_sum (s := Q) (fun q _ => discrete_integer_bound
    (I.filter (covers q)).card u)
  rw [sum_add_distrib,← mul_sum,htotal,hpair] at hb
  simpa only [sum_const,nsmul_eq_mul,Q,card_powersetCard,Nat.cast_id,mul_comm] using hb

omit [DecidableEq ι] in
theorem pairs_le (I : Finset ι) (D : ι → Finset Ω)
    (t ell : ℕ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell) :
    pairs I D t ≤ I.card*(I.card-1)*ell.choose t := by
  have h := sum_le_sum (s := I.offDiag) (f := fun ij =>
    (D ij.1 ∩ D ij.2).card.choose t)
    (g := fun _ => ell.choose t) (fun ij hij => by
      obtain ⟨hi,hj,hne⟩ := mem_offDiag.mp hij
      apply Nat.choose_le_choose
      exact ho _ hi _ hj hne)
  simpa only [pairs,sum_const,nsmul_eq_mul,offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one,Nat.cast_id] using h

omit [DecidableEq ι] in
theorem linear_uniform (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t u ell : ℕ) (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell) :
    2*u*total I D t ≤ u*(u+1)*A.card.choose t+I.card*(I.card-1)*ell.choose t :=
  (linear_bound A I D t u hD).trans (Nat.add_le_add_left (pairs_le I D t ell ho) _)

omit [DecidableEq ι] in
theorem normalized_linear (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t u ell : ℕ) (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hN : 0 < A.card.choose t) (hI : 1 ≤ I.card) :
    2*(u : ℚ)*(∑ i ∈ I, ((D i).card.choose t : ℚ)/A.card.choose t) ≤
      u*(u+1)+(I.card : ℚ)*(I.card-1)*((ell.choose t : ℚ)/A.card.choose t) := by
  have h : 2*(u : ℚ)*(total I D t) ≤
      u*(u+1)*(A.card.choose t)+(I.card : ℚ)*(I.card-1)*(ell.choose t) := by
    exact_mod_cast linear_uniform A I D t u ell hD ho
  have hN' : (0 : ℚ) < A.card.choose t := by exact_mod_cast hN
  have hd := div_le_div_of_nonneg_right h hN'.le
  unfold total at hd
  push_cast at hd
  rw [← sum_div]
  convert hd using 1 <;> first | rfl | (field_simp)

end RecursivePolygero.DirectBinomial
