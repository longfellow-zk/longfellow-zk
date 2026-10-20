import polygero.Local.CoreEnvelope
import polygero.Local.ShiftedPrice
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.ProfileAnalysis.ShiftedSpectrum
open Finset Bcs.StoppedPotential Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
noncomputable def coreSpectrum (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (baseline pivot : ℚ) : ℚ :=
  ∑ d ∈ (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1),
    price baseline pivot (coreCapacity I W d)

theorem refinedSystemCap_price_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (d : systems I.domain I.primary_le W)
    (baseline pivot : ℚ) (hb : 0 ≤ baseline) (hp : 0 < pivot) :
    mean (fun coin => price baseline pivot (refinedSystemCap I W d coin) *
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
      price baseline pivot (coreCapacity I W d)/Nat.card F+I.n/(Nat.card F : ℚ)^2 := by
  have hc : 0 ≤ coreCapacity I W d := by unfold coreCapacity; positivity
  have hpoint (coin : I.layer.Coin) : price baseline pivot (refinedSystemCap I W d coin) *
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) ≤
      price baseline pivot (coreCapacity I W d) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) +
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧ outsidePrimary I W d coin.2) := by
    by_cases hx : coin ∈ systemExceptions p.positive_degree I.layout σ d
    · by_cases ho : outsidePrimary I W d coin.2
      · simp only [indicator,if_pos hx,if_pos (show _ ∧ _ from ⟨hx,ho⟩),mul_one]
        exact (price_le_one baseline pivot hb hp _ (refinedSystemCap_nonneg I W d coin)).trans
          (le_add_of_nonneg_left (price_nonneg baseline pivot hb hp _ hc))
      · simp only [indicator,if_pos hx,if_neg (show ¬(_ ∧ _) from fun h => ho h.2),mul_one,add_zero]
        exact price_mono baseline pivot hb hp _ _ (refinedSystemCap_nonneg I W d coin)
          (by unfold refinedSystemCap; rw [if_neg ho]; exact min_le_right _ _)
    · simp [indicator,hx]
  calc
    _ ≤ _ := mean_mono hpoint
    _ = price baseline pivot (coreCapacity I W d) * mean (fun coin : I.layer.Coin =>
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) +
        mean (fun coin : I.layer.Coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
          outsidePrimary I W d coin.2)) := by rw [mean_add,mean_mul_left]
    _ ≤ _ := by
      have h := add_le_add (mul_le_mul_of_nonneg_left
        (systemExceptions_mean I p.toProfileParameters σ W d) (price_nonneg baseline pivot hb hp _ hc))
        (exception_outside_mean_le I p.toProfileParameters σ W d)
      simpa only [mul_one_div] using h

theorem refinedWeighted_price_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (baseline pivot : ℚ) (hb : 0 ≤ baseline) (hp : 0 < pivot) :
    mean (fun coin => price baseline pivot (refinedWeightedExceptions I p σ W coin)) ≤
      coreSpectrum I p W baseline pivot/Nat.card F + p.listBound*I.n/(Nat.card F : ℚ)^2 := by
  let S := highSystems I p W
  let f := fun d : systems I.domain I.primary_le W =>
    if systemDefect I W d ≤ 1 then price baseline pivot (coreCapacity I W d) else 0
  have hraw : mean (fun coin => price baseline pivot (refinedWeightedExceptions I p σ W coin)) ≤
      ∑ d ∈ S, mean (fun coin => price baseline pivot (refinedSystemCap I W d coin) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
    calc
      _ ≤ mean (fun coin => ∑ d ∈ S, price baseline pivot (refinedSystemCap I W d coin) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
        apply mean_mono
        intro coin
        exact (price_sum_le baseline pivot hb hp S _ (fun d _ =>
          mul_nonneg (refinedSystemCap_nonneg I W d coin) (indicator_nonneg _))).trans_eq
            (sum_congr rfl (fun _ _ => price_indicator baseline pivot hb hp _ _))
      _ = _ := SystemException.mean_finset_sum _ _
  have hsingle (d : systems I.domain I.primary_le W) :
      mean (fun coin => price baseline pivot (refinedSystemCap I W d coin) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
        f d/Nat.card F+I.n/(Nat.card F : ℚ)^2 := by
    by_cases hd : systemDefect I W d ≤ 1
    · simpa only [f,if_pos hd] using refinedSystemCap_price_mean_le I p σ W d baseline pivot hb hp
    · have hm : mean (fun coin => price baseline pivot (refinedSystemCap I W d coin) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
          mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
        apply mean_mono
        intro coin
        exact (mul_le_mul_of_nonneg_right (price_le_one baseline pivot hb hp _
          (refinedSystemCap_nonneg I W d coin)) (indicator_nonneg _)).trans_eq (one_mul _)
      have hn : 1 ≤ I.n := p.positive_degree.trans (by have := I.primary_le; omega)
      have hm' := hm.trans (systemExceptions_mean_le_inv_sq_of_defect I p.toProfileParameters σ W d (by omega))
      simpa only [f,if_neg hd,zero_div,zero_add] using hm'.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) (by positivity))
  have hsum : (∑ d ∈ S, f d) = coreSpectrum I p W baseline pivot := by
    simp only [f,coreSpectrum,sum_filter,S]
  have hcard : (S.card : ℚ) ≤ p.listBound := Nat.cast_le.mpr (highSystems_card_le I p hsmall W)
  calc
    _ ≤ ∑ d ∈ S, (f d/Nat.card F+I.n/(Nat.card F : ℚ)^2) := hraw.trans (sum_le_sum fun d _ => hsingle d)
    _ = coreSpectrum I p W baseline pivot/Nat.card F + S.card*(I.n/(Nat.card F : ℚ)^2) := by
      rw [sum_add_distrib,← sum_div,hsum]
      simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ (I.n : ℚ)/(Nat.card F : ℚ)^2 by positivity)
      exact (add_le_add_right hh _).trans_eq (by ring)

theorem refinedConditional_repeatPrice_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (rate baseline pivot : ℚ) (hb : 0 ≤ baseline) (hp : 0 < pivot)
    (hr : tangentRate baseline pivot ≤ rate) :
    mean (fun coin => repeatPrice rate (refinedConditionalCapacity I p σ W baseline coin)) ≤
      p.toProfileParameters.rankError+coreSpectrum I p W baseline pivot/Nat.card F+
        p.listBound*I.n/(Nat.card F : ℚ)^2 := by
  have hrate : 0 < rate := (tangentRate_pos baseline pivot hb hp).trans_le hr
  let bad := fun coin : I.layer.Coin => coin.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  have hpoint (coin : I.layer.Coin) : repeatPrice rate (refinedConditionalCapacity I p σ W baseline coin) ≤
      indicator (bad coin)+price baseline pivot (refinedWeightedExceptions I p σ W coin) := by
    by_cases h : bad coin
    · change repeatPrice rate (if bad coin then 1 else _) ≤ _
      rw [if_pos h,show indicator (bad coin) = 1 from if_pos h]
      exact ((StoppedSpectrum.repeatPrice_le_price rate 1 hrate (by norm_num)).trans (StoppedSpectrum.price_le_one rate 1 hrate (by norm_num))).trans
        (le_add_of_nonneg_right (price_nonneg baseline pivot hb hp _ (refinedWeightedExceptions_nonneg I p σ W coin)))
    · change repeatPrice rate (if bad coin then 1 else _) ≤ _
      simpa only [if_neg h,indicator,if_neg h,zero_add] using
        baseline_le_price baseline pivot hb hp rate _
          (refinedWeightedExceptions_nonneg I p σ W coin) hr
  calc
    _ ≤ mean (fun coin => indicator (bad coin)) +
        mean (fun coin => price baseline pivot (refinedWeightedExceptions I p σ W coin)) := by
      simpa only [mean_add] using mean_mono hpoint
    _ ≤ p.toProfileParameters.rankError +
        (coreSpectrum I p W baseline pivot/Nat.card F+p.listBound*I.n/(Nat.card F : ℚ)^2) :=
      add_le_add (rank_bad_mean I p.toProfileParameters W)
        (refinedWeighted_price_mean_le I p hsmall σ W baseline pivot hb hp)
    _ = _ := by ring


end RecursivePolygero.ProfileAnalysis.ShiftedSpectrum
