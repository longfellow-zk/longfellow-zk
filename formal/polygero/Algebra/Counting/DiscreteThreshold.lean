import polygero.Algebra.Counting.DirectBinomial

namespace RecursivePolygero.DiscreteThreshold

def candidate (h u : ℕ) (p : ℚ) : ℚ :=
  ((u : ℚ)-1)/(2*(h-1))+(h : ℚ)*p/(2*u)

/-- The least positive integer whose triangular product reaches the overlap
bound, expressed by two exact inequalities rather than an unbounded search. -/
def IsLeastIndex (q : ℕ) (η : ℚ) (u : ℕ) : Prop :=
  1 ≤ u ∧ (q : ℚ)*(q-1)*η ≤ u*(u+1) ∧
    (u = 1 ∨ ((u : ℚ)-1)*u < q*(q-1)*η)

instance (q : ℕ) (η : ℚ) (u : ℕ) : Decidable (IsLeastIndex q η u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem IsLeastIndex.le_of_bound {q u v : ℕ} {η : ℚ}
    (h : IsLeastIndex q η u) (hv : 1 ≤ v)
    (hb : (q : ℚ)*(q-1)*η ≤ v*(v+1)) : u ≤ v := by
  rcases h.2.2 with he | hlo
  · omega
  by_contra hn
  have h1 : (v : ℚ) ≤ u-1 := by exact_mod_cast (show (v : ℤ) ≤ u-1 by omega)
  have h2 : (v : ℚ)+1 ≤ u := by exact_mod_cast (show v+1 ≤ u by omega)
  have hm := mul_le_mul h1 h2 (by positivity : (0 : ℚ) ≤ v+1) (by linarith : (0 : ℚ) ≤ u-1)
  linarith

theorem IsLeastIndex.le_pred {q u : ℕ} {η : ℚ}
    (h : IsLeastIndex q η u) (hq : 2 ≤ q) (hη : η ≤ 1) : u ≤ q-1 := by
  apply h.le_of_bound (by omega : 1 ≤ q-1)
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hm := mul_le_mul_of_nonneg_left hη
    (mul_nonneg (by positivity) (by linarith) : (0 : ℚ) ≤ q*(q-1))
  push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
  nlinarith only [hm]

/-- Strict overlap makes the derived counting contribution strictly below one. -/
theorem IsLeastIndex.candidate_lt_one {q u : ℕ} {η : ℚ}
    (h : IsLeastIndex q η u) (hq : 2 ≤ q) (hη : η < 1) : candidate q u η < 1 := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hu : (0 : ℚ) < u := by exact_mod_cast h.1
  have hqm : (0 : ℚ) < q-1 := by linarith
  have hup : (u : ℚ) ≤ q-1 := by
    exact_mod_cast (show (u : ℤ) ≤ q-1 by have := h.le_pred hq hη.le; omega)
  have hsum : candidate q u η ≤ (u : ℚ)/(q-1) := by
    unfold candidate
    apply (le_div_iff₀ hqm).mpr
    field_simp [hu.ne',hqm.ne']
    nlinarith only [h.2.1]
  rcases lt_or_eq_of_le hup with hlt | heq
  · exact hsum.trans_lt ((div_lt_one hqm).mpr hlt)
  · unfold candidate
    rw [heq]
    have hden : (0 : ℚ) < 2*(q-1) := by positivity
    rw [← add_div,div_lt_one hden]
    nlinarith only [mul_lt_mul_of_pos_left hη (by linarith : (0 : ℚ) < q)]

theorem candidate_step (h v : ℕ) (p : ℚ) (hh : 2 ≤ h)
    (hv : 1 ≤ v) (hvh : v ≤ h+1) (hp : 0 ≤ p) :
    ∃ u, 1 ≤ u ∧ u ≤ h ∧ candidate h u p ≤ candidate (h+1) v p := by
  have hh0 : (0 : ℚ) < h := by exact_mod_cast (by omega : 0 < h)
  have hh1 : (0 : ℚ) < h-1 := by exact_mod_cast (by omega : (0 : ℤ) < h-1)
  have hv0 : (0 : ℚ) < v := by exact_mod_cast hv
  by_cases hv1 : v=1
  · refine ⟨1,by omega,by omega,?_⟩
    subst v
    simp only [candidate,Nat.cast_one,sub_self,zero_div,zero_add,Nat.cast_add]
    nlinarith
  by_cases hvlast : v=h+1
  · refine ⟨h,by omega,le_rfl,?_⟩
    subst v
    unfold candidate
    push_cast
    have hhp : (h : ℚ)+1 ≠ 0 := by linarith
    field_simp [hh0.ne',hh1.ne']
    ring_nf
    norm_num
  have hv2 : (0 : ℚ) < v-1 := by exact_mod_cast (by omega : (0 : ℤ) < v-1)
  by_cases hc : (v : ℚ)*(v-1) ≤ h*(h-1)*p
  · refine ⟨v,hv,by omega,?_⟩
    have he : candidate h v p-candidate (h+1) v p =
        ((v : ℚ)*(v-1)-h*(h-1)*p)/(2*h*(h-1)*v) := by
      unfold candidate
      push_cast
      field_simp [hh0.ne',hh1.ne']
      ring
    have hd : 0 < (2 : ℚ)*h*(h-1)*v := by positivity
    have hn := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) hd.le
    linarith
  · refine ⟨v-1,by omega,by omega,?_⟩
    have hvl : (v : ℚ) ≤ h := by exact_mod_cast (by omega : v ≤ h)
    have he : candidate h (v-1) p-candidate (h+1) v p =
        ((h : ℚ)+1-v)*(h*(h-1)*p-v*(v-1))/(2*h*(h-1)*v*(v-1)) := by
      unfold candidate
      push_cast [Nat.cast_sub hv]
      field_simp [hh0.ne',hh1.ne']
      ring
    have hn : ((h : ℚ)+1-v)*(h*(h-1)*p-v*(v-1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hd : 0 < (2 : ℚ)*h*(h-1)*v*(v-1) := by positivity
    have hdiv := div_nonpos_of_nonpos_of_nonneg hn hd.le
    linarith

theorem candidate_le_of_le (h q v : ℕ) (p : ℚ) (hh : 2 ≤ h) (hhq : h ≤ q)
    (hv : 1 ≤ v) (hvq : v ≤ q) (hp : 0 ≤ p) :
    ∃ u, 1 ≤ u ∧ u ≤ h ∧ candidate h u p ≤ candidate q v p := by
  induction q using Nat.strong_induction_on generalizing v with
  | h q ih =>
    by_cases he : h=q
    · subst q
      exact ⟨v,hv,hvq,le_rfl⟩
    · have hq : q-1+1=q := by omega
      obtain ⟨w,hw,hwh,hwc⟩ := candidate_step (q-1) v p (by omega) hv (by omega) hp
      obtain ⟨u,hu,huh,huc⟩ := ih (q-1) (by omega) w (by omega) hw hwh
      exact ⟨u,hu,huh,huc.trans (by simpa only [hq] using hwc)⟩

/-- A concrete integer certifies a sufficient counting cutoff. -/
def Condition (q : ℕ) (p θ : ℚ) : Prop :=
  ∃ u, 1 ≤ u ∧ u ≤ q ∧ candidate q u p ≤ θ

/-- Discrete interpolation converts the linear counting bounds into the sum
budget used by the expected-maximum theorem. -/
theorem sum_le_threshold {h q : ℕ} {p θ S : ℚ} (hh : 2 ≤ h) (hhq : h ≤ q)
    (hp : 0 ≤ p) (hc : Condition q p θ)
    (hl : ∀ u : ℕ, 2*(u : ℚ)*S ≤ u*(u+1)+(h : ℚ)*(h-1)*p) :
    S ≤ 1+((h : ℚ)-1)*θ := by
  obtain ⟨v,hv,hvq,hvθ⟩ := hc
  obtain ⟨u,hu,huh,huc⟩ := candidate_le_of_le h q v p hh hhq hv hvq hp
  have hu0 : (0 : ℚ) < u := by exact_mod_cast hu
  have hh1 : (0 : ℚ) < h-1 := by exact_mod_cast (by omega : (0 : ℤ) < h-1)
  have hid : 2*(u : ℚ)*(1+((h : ℚ)-1)*candidate h u p) =
      u*(u+1)+(h : ℚ)*(h-1)*p := by
    unfold candidate
    field_simp
    ring
  have hbound : S ≤ 1+((h : ℚ)-1)*candidate h u p := by
    have := hl u
    nlinarith only [hid,this,hu0]
  exact hbound.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left (huc.trans hvθ) hh1.le) _)

end RecursivePolygero.DiscreteThreshold
