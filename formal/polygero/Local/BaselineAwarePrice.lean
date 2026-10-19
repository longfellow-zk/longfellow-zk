import polygero.Local.DefectPacking

/-! Price the baseline and exceptional capacity jointly before taking a
subadditive spectrum. Subtracting the whole baseline is unnecessarily
expensive. All conditions below are rational polynomial inequalities. -/
namespace RecursivePolygero.ProfileAnalysis.StoppedSpectrum
open Finset Bcs.StoppedPotential Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

/-- An effective spectrum price can be strictly larger than rate-baseline.
The discriminant condition controls the linear branch; the second
condition controls the reciprocal branch. No square roots are needed. -/
theorem repeatPrice_baseline_le_effective (rate baseline effective capacity : ℚ)
    (hb : 0 ≤ baseline) (hc : 0 ≤ capacity) (he : 0 < effective)
    (hdisc : (baseline+4*effective)^2 ≤ 16*effective*rate)
    (hbranch : baseline+2*effective ≤ 2*rate) :
    repeatPrice rate (baseline+capacity) ≤ price effective capacity := by
  have hr : 0 ≤ rate := by linarith
  have hp := price_nonneg effective capacity he hc
  by_cases hz : baseline+capacity = 0
  · simpa only [repeatPrice, if_pos hz] using hp
  have hpos : 0 < baseline+capacity := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hz)
  simp only [repeatPrice, if_neg hz]
  apply max_le hp
  unfold price
  split_ifs with hsmall
  · apply (le_div_iff₀ (show 0 < 4*effective by positivity)).mpr
    have hpoly : 4*effective*(baseline+capacity-rate) ≤ capacity*(baseline+capacity) := by
      nlinarith [sq_nonneg (2*capacity+baseline-4*effective)]
    have heq : (baseline+capacity)*((1-rate/(baseline+capacity))*(4*effective)) =
        4*effective*(baseline+capacity-rate) := by field_simp
    apply le_of_mul_le_mul_left (a := baseline+capacity) ?_ hpos
    rw [heq]
    nlinarith
  · have hcp : 0 < capacity := by linarith
    have hprod : effective*(baseline+capacity) ≤ rate*capacity := by
      have hr' : effective ≤ rate := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hr') (show 0 ≤ capacity-2*effective by linarith)]
    have hdiv : effective/capacity ≤ rate/(baseline+capacity) :=
      (div_le_div_iff₀ hcp hpos).mpr hprod
    linarith

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Subadditivity of the existing effective price preserves arbitrary
overlap between exception events, including identical affine fibers. -/
theorem weightedExceptions_price_mean_le_defect_split
    (I : Instance F) (p : HahnSystemCertificate I) (hsmall : p.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (effective : ℚ) (he : 0 < effective) :
    mean (fun coin => price effective (weightedExceptions I p sigma W coin)) ≤
      lowDefectSpectrum I p W effective / Nat.card F + p.listBound/(Nat.card F : ℚ)^2 := by
  let S := highSystems I p W
  let low := fun d : systems I.domain I.primary_le W => systemDefect I W d ≤ 1
  have hraw : mean (fun coin => price effective (weightedExceptions I p sigma W coin)) ≤
      ∑ d ∈ S, price effective (systemCap I W d) * mean (fun coin =>
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
    calc
      _ ≤ mean (fun coin => ∑ d ∈ S, price effective (systemCap I W d) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
        apply mean_mono
        intro coin
        exact (price_sum_le S _ effective he (fun d _ =>
          mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _))).trans_eq
            (sum_congr rfl (fun d _ => price_indicator _ _ he _))
      _ = _ := by
        rw [SystemException.mean_finset_sum]
        exact sum_congr rfl (fun d _ => mean_mul_left _ _)
  have hlow : (∑ d ∈ S.filter low, price effective (systemCap I W d) * mean (fun coin =>
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d))) ≤
      (∑ d ∈ S.filter low, price effective (systemCap I W d))/Nat.card F := by
    calc
      _ ≤ ∑ d ∈ S.filter low, price effective (systemCap I W d)*(1/Nat.card F) :=
        sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (systemExceptions_mean I p.toProfileParameters sigma W d)
          (price_nonneg _ _ he (by unfold systemCap; positivity)))
      _ = _ := by rw [← sum_mul]; ring
  have hhigh : (∑ d ∈ S.filter (fun d => ¬low d), price effective (systemCap I W d) *
      mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d))) ≤
        p.listBound/(Nat.card F : ℚ)^2 := by
    calc
      _ ≤ ∑ _d ∈ S.filter (fun d => ¬low d), (1 : ℚ)/(Nat.card F : ℚ)^2 := by
        apply sum_le_sum
        intro d hd
        have hdef : 2 ≤ systemDefect I W d := by
          have hh := (mem_filter.mp hd).2
          dsimp [low] at hh
          omega
        calc
          _ ≤ price effective (systemCap I W d)*(1/(Nat.card F : ℚ)^2) :=
            mul_le_mul_of_nonneg_left
              (systemExceptions_mean_le_inv_sq_of_defect I p.toProfileParameters sigma W d hdef)
              (price_nonneg _ _ he (by unfold systemCap; positivity))
          _ ≤ 1*(1/(Nat.card F : ℚ)^2) := mul_le_mul_of_nonneg_right
            (price_le_one _ _ he (by unfold systemCap; positivity)) (by positivity)
          _ = _ := one_mul _
      _ = ((S.filter (fun d => ¬low d)).card : ℚ)/(Nat.card F : ℚ)^2 := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right
        (Nat.cast_le.mpr ((card_filter_le _ _).trans (highSystems_card_le I p hsmall W))) (by positivity)
  rw [← sum_filter_add_sum_filter_not S low] at hraw
  exact hraw.trans (add_le_add hlow hhigh)

theorem conditionalCapacity_repeatPrice_mean_le_effective
    (I : Instance F) (p : HahnSystemCertificate I) (hsmall : p.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (rate baseline effective : ℚ)
    (hb : 0 ≤ baseline) (he : 0 < effective)
    (hdisc : (baseline+4*effective)^2 ≤ 16*effective*rate)
    (hbranch : baseline+2*effective ≤ 2*rate) :
    mean (fun coin => repeatPrice rate (conditionalCapacity I p sigma W baseline coin)) ≤
      p.toProfileParameters.rankError + lowDefectSpectrum I p W effective/Nat.card F +
        p.listBound/(Nat.card F : ℚ)^2 := by
  have hr : 0 < rate := by linarith
  let bad := fun coin : I.layer.Coin => coin.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  have hp (coin : I.layer.Coin) : repeatPrice rate (conditionalCapacity I p sigma W baseline coin) ≤
      indicator (bad coin) + price effective (weightedExceptions I p sigma W coin) := by
    have hw : 0 ≤ weightedExceptions I p sigma W coin :=
      sum_nonneg fun d _ => mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _)
    by_cases h : bad coin
    · have hv : repeatPrice rate 1 ≤ 1 := (repeatPrice_le_price rate 1 hr (by norm_num)).trans
        (price_le_one rate 1 hr (by norm_num))
      change repeatPrice rate (if bad coin then 1 else _) ≤ _
      simp only [indicator, if_pos h]
      exact hv.trans (le_add_of_nonneg_right (price_nonneg _ _ he hw))
    · change repeatPrice rate (if bad coin then 1 else _) ≤ _
      simpa only [if_neg h, indicator, if_neg h, zero_add] using
        repeatPrice_baseline_le_effective rate baseline effective _ hb hw he hdisc hbranch
  calc
    _ ≤ _ := mean_mono hp
    _ = mean (fun coin => indicator (bad coin)) +
        mean (fun coin => price effective (weightedExceptions I p sigma W coin)) := mean_add _ _
    _ ≤ _ := by
      have h := add_le_add (rank_bad_mean I p.toProfileParameters W)
        (weightedExceptions_price_mean_le_defect_split I p hsmall sigma W effective he)
      linarith

end RecursivePolygero.ProfileAnalysis.StoppedSpectrum
