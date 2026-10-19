import polygero.Local.ListSafety

/-! Capacity weighting removes the list factor from the main exceptional
mass. This is a local average, not a Boolean exception or adaptive reuse
certificate. The latter distinctions are essential for FS composition. -/
namespace RecursivePolygero.ProfileAnalysis
open Finset Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- High capacities have total at most one plus the repeated threshold.
This is stronger than bounding every capacity by one and summing the list. -/
theorem highSystems_capacity_sum_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (W : I.layer.Oracle) :
    ∑ d ∈ highSystems I p W, systemCap I W d ≤
      1 - p.threshold + p.listBound * p.threshold := by
  have hc := highSystems_card_le I p hsmall W
  have he := systemCap_excess_of_hahn I p W (highSystems I p W) (hc.trans hsmall.le)
  have hx : (∑ d ∈ highSystems I p W, max 0 (systemCap I W d - p.threshold)) =
      (∑ d ∈ highSystems I p W, systemCap I W d) -
        (highSystems I p W).card * p.threshold := by
    calc
      _ = ∑ d ∈ highSystems I p W, (systemCap I W d - p.threshold) := by
        apply sum_congr rfl
        intro d hd
        exact max_eq_right (sub_nonneg.mpr (mem_filter.mp hd).2.le)
      _ = _ := by simp [sum_sub_distrib]
  rw [hx] at he
  have hn : ((highSystems I p W).card : ℚ) ≤ p.listBound := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hn p.threshold_nonneg]

noncomputable def weightedExceptions (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) : ℚ :=
  ∑ d ∈ highSystems I p W, systemCap I W d *
    indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)

/-- The price is (1 + (L-1) theta)/|F|, rather than L/|F|.
It prices capacity-weighted mass; replacing it by the Boolean listBad
indicator would be invalid. -/
theorem weightedExceptions_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (sigma : I.layer.Statement) (W : I.layer.Oracle) :
    mean (weightedExceptions I p sigma W) ≤
      (1 - p.threshold + p.listBound * p.threshold) / Nat.card F := by
  unfold weightedExceptions
  rw [SystemException.mean_finset_sum]
  calc
    _ = ∑ d ∈ highSystems I p W, systemCap I W d *
        mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
      apply sum_congr rfl
      intro d _
      exact mean_mul_left _ _
    _ ≤ ∑ d ∈ highSystems I p W, systemCap I W d * (1 / Nat.card F) := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left (systemExceptions_mean I p.toProfileParameters sigma W d)
      unfold systemCap
      positivity
    _ = (∑ d ∈ highSystems I p W, systemCap I W d) / Nat.card F := by
      rw [← sum_mul]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (highSystems_capacity_sum_le I p hsmall W) (by positivity)

end RecursivePolygero.ProfileAnalysis
