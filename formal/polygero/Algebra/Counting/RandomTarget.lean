import polygero.Algebra.Counting.Envelope

/-! Random target labels, fresh exceptions, and an exact rank-exception charge. -/
namespace RecursivePolygero.SystemException
open Finset ProfileAnalysis
attribute [local instance] Classical.propDecidable

/-- Charge each excess to one attaining entry; each charge obeys that entry's frequency bound. -/
theorem mean_envelope_of_gated_frequency {I Γ : Type*} [Fintype I] [DecidableEq I]
    [Fintype Γ] [Nonempty Γ] (a : I → ℚ) (E : Γ → I → Prop) (bad : Γ → Prop)
    (θ rate : ℚ) (q : ℕ) (hq : 0 < q) (hrate : 0 ≤ rate)
    (hexcess : ∀ T : Finset I, T.card ≤ q → ∑ i ∈ T, max 0 (a i-θ) ≤ 1-θ)
    (hfreq : ∀ i, mean (fun γ => indicator (¬bad γ ∧ E γ i)) ≤ rate)
    (hslope : 1-mean (fun γ => indicator (bad γ)) ≤ (q : ℚ)*rate) :
    mean (fun γ => envelope a (E γ) (bad γ) θ) ≤
      mean (fun γ => indicator (bad γ))+
      (1-mean (fun γ => indicator (bad γ)))*θ+rate*(1-θ) := by
  have hc (γ : Γ) : ∃ c : Option I,
      (c = none → envelope a (E γ) (bad γ) θ = indicator (bad γ)+(1-indicator (bad γ))*θ) ∧
      ∀ i, c = some i → ¬bad γ ∧ E γ i ∧ envelope a (E γ) (bad γ) θ = a i ∧ θ ≤ a i := by
    by_cases hb : bad γ
    · exact ⟨none,by simp [envelope,indicator,hb]⟩
    · by_cases ht : maximum a (E γ) θ = θ
      · exact ⟨none,by simp [envelope,indicator,hb,ht]⟩
      · obtain ⟨i,hi,he⟩ := exists_maximum_entry a (E γ) θ
          (lt_of_le_of_ne (le_maximum a (E γ) θ) (Ne.symm ht))
        refine ⟨some i,by simp,?_⟩
        intro j hj
        cases Option.some.inj hj
        exact ⟨hb,hi,by simp [envelope,hb,he],he ▸ le_maximum a (E γ) θ⟩
  choose c hc using hc
  let w (i) := mean (fun γ => indicator (c γ = some i))
  have hw (i) : 0 ≤ w i := by
    simpa only [mean_const] using mean_mono (fun γ => indicator_nonneg (c γ = some i))
  have hwL (i) : w i ≤ rate :=
    (mean_mono fun γ => indicator_mono (fun h => ⟨(hc γ).2 i h |>.1,(hc γ).2 i h |>.2.1⟩)).trans (hfreq i)
  have hsum : ∑ i, w i ≤ 1-mean (fun γ => indicator (bad γ)) := by
    rw [show (∑ i, w i) = mean (fun γ => ∑ i, indicator (c γ = some i)) from
      (mean_finset_sum univ _).symm,← mean_const (I := Γ) 1,← mean_sub]
    apply mean_mono
    intro γ
    cases he : c γ with
    | none => simp [indicator]; split_ifs <;> norm_num
    | some i =>
      have hb := ((hc γ).2 i he).1
      simp [indicator,hb]
  have hp (γ) : envelope a (E γ) (bad γ) θ =
      indicator (bad γ)+(1-indicator (bad γ))*θ+
      ∑ i, indicator (c γ = some i)*max 0 (a i-θ) := by
    cases he : c γ with
    | none => simpa [he,indicator] using (hc γ).1 he
    | some i =>
      obtain ⟨hb,_,hv,hi⟩ := (hc γ).2 i he
      rw [hv]
      simp [indicator,hb,max_eq_right (sub_nonneg.mpr hi)]
  have h := weighted_sum_le_small_sum (fun i => max 0 (a i-θ)) w rate (1-θ) q hq
    (fun _ => le_max_left _ _) hw hwL hrate (hsum.trans hslope) hexcess
  simp_rw [hp]
  rw [mean_add,mean_add,mean_finset_sum]
  have hz : mean (fun γ => (1-indicator (bad γ))*θ) =
      (1-mean (fun γ => indicator (bad γ)))*θ := by
    simp_rw [mul_comm _ θ]
    rw [mean_mul_left,mean_sub,mean_const,mul_comm]
  rw [hz]
  have he (i) : mean (fun γ => indicator (c γ = some i)*max 0 (a i-θ)) =
      w i*max 0 (a i-θ) := by
    simp_rw [mul_comm _ (max 0 (a i-θ))]
    rw [mean_mul_left,mul_comm]
  simp_rw [he]
  linarith

/-- Targets may depend on earlier randomness, and fresh exceptions on both
that randomness and the fresh challenge. The rank event depends only on the latter. -/
theorem target_gated_frequency {Z Γ : Type*} [Fintype Z] [Nonempty Z]
    [Fintype Γ] [Nonempty Γ] (target : Z → Prop) (E : Z → Γ → Prop)
    (bad : Γ → Prop) (r b : ℚ) (hr : mean (fun z => indicator (target z)) ≤ r)
    (hE : ∀ z, mean (fun γ => indicator (E z γ)) ≤ b)
    (hb : b ≤ 1-mean (fun γ => indicator (bad γ))) :
    mean (fun z => mean (fun γ => indicator (¬bad γ ∧ (target z ∨ E z γ)))) ≤
      (1-mean (fun γ => indicator (bad γ)))*r+(1-r)*b := by
  have hp (z : Z) : mean (fun γ => indicator (¬bad γ ∧ (target z ∨ E z γ))) ≤
      b+(1-mean (fun γ => indicator (bad γ))-b)*indicator (target z) := by
    by_cases ht : target z
    · have he (γ : Γ) : indicator (¬bad γ ∧ (target z ∨ E z γ)) = 1-indicator (bad γ) := by
        unfold indicator
        by_cases hx : bad γ <;> simp [ht,hx]
      simp_rw [he]
      rw [mean_sub,mean_const]
      simp only [indicator,if_pos ht,mul_one]
      linarith
    · simp only [indicator,if_neg ht,mul_zero,add_zero]
      apply (mean_mono (fun γ => indicator_mono (show ¬bad γ ∧ (target z ∨ E z γ) → E z γ
        from fun h => h.2.resolve_left ht))).trans (hE z)
  have h := mean_mono hp
  rw [mean_add,mean_const,mean_mul_left] at h
  have hm := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hb)
  linarith

/-- Earlier target labels and fresh system exceptions obey the same affine
error law. The rank event is independent of the earlier randomness. -/
theorem random_target_envelope_mean {Z Γ I : Type*}
    [Fintype Z] [Nonempty Z] [Fintype Γ] [Nonempty Γ] [Fintype I] [DecidableEq I]
    (a : I → ℚ) (target : Z → I → Prop) (E : Z → Γ → I → Prop)
    (bad : Γ → Prop) (θ μ r : ℚ) (q : ℕ) (hq : 0 < q)
    (hθ : θ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hμ : μ+1/(q : ℚ) ≤ 1)
    (hbad : mean (fun γ => indicator (bad γ)) ≤ μ)
    (htarget : ∀ i, mean (fun z => indicator (target z i)) ≤ r)
    (hE : ∀ z i, mean (fun γ => indicator (E z γ i)) ≤ 1/(q : ℚ))
    (hexcess : ∀ T : Finset I, T.card ≤ q → ∑ i ∈ T, max 0 (a i-θ) ≤ 1-θ) :
    mean (fun z => mean (fun γ => envelope a
      (fun i => target z i ∨ E z γ i) (bad γ) θ)) ≤
      profile q μ θ+(1-profile q μ θ)*r := by
  let α := mean (fun γ => indicator (bad γ))
  let rate := (1-α)*r+(1-r)/(q : ℚ)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hα : α+1/(q : ℚ) ≤ 1 := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by
    have : (0 : ℚ) ≤ 1/q := by positivity
    linarith
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hf (i) : mean (fun zγ : Z × Γ => indicator
      (¬bad zγ.2 ∧ (target zγ.1 i ∨ E zγ.1 zγ.2 i))) ≤ rate := by
    rw [mean_prod]
    simpa only [rate,α,mul_one_div] using (target_gated_frequency (fun z => target z i) (fun z γ => E z γ i)
      bad r (1/(q : ℚ)) (htarget i) (fun z => hE z i) (by dsimp [α] at hα; linarith))
  have hslope : 1-α ≤ (q : ℚ)*rate := by
    have he : (q : ℚ)*rate = 1-r+(q : ℚ)*(1-α)*r := by
      dsimp [rate]
      field_simp
      ring
    rw [he]
    have hα0 : 0 ≤ α := by
      simpa only [mean_const] using (show mean (fun _ : Γ => (0 : ℚ)) ≤ α from
        mean_mono (fun γ => indicator_nonneg (bad γ)))
    have ht : 1 ≤ (q : ℚ)*(1-α) := by
      have := (div_le_iff₀ hqQ).mp (by linarith : 1/(q : ℚ) ≤ 1-α)
      nlinarith
    nlinarith
  have hmean : mean (fun zγ : Z × Γ => indicator (bad zγ.2)) = α := by
    rw [mean_prod]
    exact mean_const (I := Z) α
  have h := mean_envelope_of_gated_frequency a
    (fun zγ : Z × Γ => fun i => target zγ.1 i ∨ E zγ.1 zγ.2 i)
    (fun zγ => bad zγ.2) θ rate q hq hrate hexcess hf (by rw [hmean]; exact hslope)
  rw [mean_prod,hmean] at h
  have hm := mul_nonneg (sub_nonneg.mpr hbad)
    (mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hr1))
  dsimp [rate,α] at h
  unfold profile
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

end RecursivePolygero.SystemException
