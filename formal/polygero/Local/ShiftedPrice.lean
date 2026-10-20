import polygero.Local.StoppedSpectrum

/-! Rational concave envelope of the baseline-shifted stopping price.
The reciprocal branch keeps the baseline. The tangent parameter avoids
square roots, so all concrete certificates use rational arithmetic. -/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.ProfileAnalysis.ShiftedSpectrum
open Finset Counting Bcs.StoppedPotential
open scoped Classical
noncomputable def tangentRate (b p : ℚ) : ℚ := (b+p)^2/(b+2*p)
noncomputable def price (b p c : ℚ) : ℚ :=
  if c ≤ p then c/(b+2*p) else 1-tangentRate b p/(b+c)
variable (b p : ℚ) (hb : 0 ≤ b) (hp : 0 < p)
include hb hp

theorem tangentRate_pos : 0 < tangentRate b p := by
  unfold tangentRate
  exact div_pos (sq_pos_of_pos (by linarith)) (by linarith)

theorem price_zero : price b p 0 = 0 := by simp [price,hp.le]

theorem reciprocal_le_linear (c : ℚ) (_hc : 0 ≤ c) (hbc : 0 < b+c) :
    1-tangentRate b p/(b+c) ≤ c/(b+2*p) := by
  have hd : 0 < b+2*p := by linarith
  apply (le_div_iff₀ hd).mpr
  apply (le_of_mul_le_mul_left (a := b+c) ?_ hbc)
  have he : (b+c)*((1-tangentRate b p/(b+c))*(b+2*p)) =
      (b+c)*(b+2*p)-(b+p)^2 := by unfold tangentRate; field_simp [ne_of_gt hd,ne_of_gt hbc]
  rw [he]
  nlinarith [sq_nonneg (c-p)]

theorem seam : 1-tangentRate b p/(b+p) = p/(b+2*p) := by
  have hd : b+2*p ≠ 0 := ne_of_gt (by linarith)
  have he : b+p ≠ 0 := ne_of_gt (by linarith)
  unfold tangentRate
  field_simp [hd,he]
  ring

theorem price_nonneg (c : ℚ) (hc : 0 ≤ c) : 0 ≤ price b p c := by
  unfold price
  split_ifs with h
  · exact div_nonneg hc (by linarith)
  · have h := div_le_div_of_nonneg_left (tangentRate_pos b p hb hp).le
      (show 0 < b+p by linarith) (show b+p ≤ b+c by linarith)
    have he := seam b p hb hp
    have hh : 0 ≤ p/(b+2*p) := by positivity
    linarith

theorem price_le_one (c : ℚ) (_hc : 0 ≤ c) : price b p c ≤ 1 := by
  unfold price
  split_ifs with h
  · apply (div_le_one (by linarith : 0 < b+2*p)).mpr
    linarith
  · linarith [div_nonneg (tangentRate_pos b p hb hp).le (show 0 ≤ b+c by linarith)]

theorem price_mono (x y : ℚ) (_hx : 0 ≤ x) (hxy : x ≤ y) :
    price b p x ≤ price b p y := by
  unfold price
  split_ifs with hxc hyc hyc
  · exact div_le_div_of_nonneg_right hxy (by linarith)
  · have h₁ : x/(b+2*p) ≤ p/(b+2*p) := div_le_div_of_nonneg_right hxc (by linarith)
    have h₂ := div_le_div_of_nonneg_left (tangentRate_pos b p hb hp).le
      (show 0 < b+p by linarith) (show b+p ≤ b+y by linarith)
    have he := seam b p hb hp
    linarith
  · exact (hxc (hxy.trans hyc)).elim
  · have hh := div_le_div_of_nonneg_left (tangentRate_pos b p hb hp).le
      (show 0 < b+x by linarith) (show b+x ≤ b+y by linarith)
    linarith

theorem price_scale (x y : ℚ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x*price b p y ≤ y*price b p x := by
  unfold price
  split_ifs with hyc hxc hxc
  · ring_nf; rfl
  · exact (hxc (hxy.trans hyc)).elim
  · have hh := mul_le_mul_of_nonneg_left
      (reciprocal_le_linear b p hb hp y (hx.trans hxy) (by linarith)) hx
    exact hh.trans_eq (by ring)
  · have hbx : 0 < b+x := by linarith
    have hby : 0 < b+y := by linarith
    have hd : 0 < b+2*p := by linarith
    have hprod : (b+2*p)*(b+x)*(b+y)-(b+p)^2*(b+x+y) ≥ 0 := by
      have he : (b+2*p)*(b+x)*(b+y)-(b+p)^2*(b+x+y) =
          p*(b+p)*((x-p)+(y-p))+(b+2*p)*(x-p)*(y-p) := by ring
      rw [he]
      have hxp : 0 ≤ x-p := by linarith
      have hyp : 0 ≤ y-p := by linarith
      positivity
    have hh := mul_nonneg (sub_nonneg.mpr hxy) hprod
    have he : (y*(1-tangentRate b p/(b+x))-x*(1-tangentRate b p/(b+y))) *
        ((b+2*p)*(b+x)*(b+y)) =
        (y-x)*((b+2*p)*(b+x)*(b+y)-(b+p)^2*(b+x+y)) := by
      unfold tangentRate; field_simp [ne_of_gt hd,ne_of_gt hbx,ne_of_gt hby]; ring
    rw [← he] at hh
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity :
      0 < (b+2*p)*(b+x)*(b+y))).mp hh)

theorem price_add_le (x y : ℚ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    price b p (x+y) ≤ price b p x+price b p y := by
  by_cases hz : x+y = 0
  · have hxx : x=0 := by linarith
    have hyy : y=0 := by linarith
    simp [hxx,hyy,price_zero b p hb hp]
  have hpos : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
  have h₁ := price_scale b p hb hp x (x+y) hx (by linarith)
  have h₂ := price_scale b p hb hp y (x+y) hy (by linarith)
  apply le_of_mul_le_mul_left (a := x+y) _ hpos
  nlinarith

theorem price_sum_le {D : Type} (T : Finset D) (c : D → ℚ)
    (hc : ∀ d ∈ T, 0 ≤ c d) : price b p (∑ d ∈ T, c d) ≤ ∑ d ∈ T, price b p (c d) := by
  induction T using Finset.induction_on with
  | empty => simp [price_zero b p hb hp]
  | @insert d T hd ih =>
    simp only [sum_insert hd]
    exact (price_add_le b p hb hp (c d) _ (hc d (mem_insert_self _ _))
      (sum_nonneg fun e he => hc e (mem_insert_of_mem he))).trans
      (add_le_add le_rfl (ih fun e he => hc e (mem_insert_of_mem he)))

theorem price_indicator (c : ℚ) (E : Prop) :
    price b p (c*indicator E) = price b p c*indicator E := by
  by_cases h : E <;> simp [indicator,h,price_zero b p hb hp]

theorem baseline_le_price (rate c : ℚ) (hc : 0 ≤ c) (hr : tangentRate b p ≤ rate) :
    repeatPrice rate (b+c) ≤ price b p c := by
  by_cases hz : b+c = 0
  · simpa [repeatPrice,hz] using price_nonneg b p hb hp c hc
  have hbc : 0 < b+c := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hz)
  have hrate := div_le_div_of_nonneg_right hr hbc.le
  simp only [repeatPrice,if_neg hz]
  apply max_le (price_nonneg b p hb hp c hc)
  unfold price
  split_ifs with h
  · exact (by linarith : 1-rate/(b+c) ≤ 1-tangentRate b p/(b+c)).trans
      (reciprocal_le_linear b p hb hp c hc hbc)
  · linarith
end RecursivePolygero.ProfileAnalysis.ShiftedSpectrum
