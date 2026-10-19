import polygero.Benchmarks.FSNonuniformData
import polygero.Algebra.Counting.NonuniformOccupancy
import polygero.Recursion.FSStoppedCharges

/-! The actual fixed-81 spectrum uses the total support resource, rather
than maximizing every tail separately. The recursive six-response low
baseline is retained in the price throughout. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000

namespace RecursivePolygero.Benchmarks.FSNonuniformSpectrum
open ProfileAnalysis ProfileAnalysis.StoppedSpectrum
open FiatShamir FiatShamir.TwoLevel Bcs.AffineBlock
open Finset Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

private theorem family_spectrum_le {D : Type} (T : Finset D)
    (E : D → Finset (Fin 8192))
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (E d ∩ E e).card ≤ 639)
    (hmin : ∀ d ∈ T, 2714 ≤ (E d).card) (hcard : T.card ≤ 6) :
    ∑ d ∈ T, FSNonuniformData.f (E d).card ≤ (479/100 : ℚ) := by
  have hslope5 := FSNonuniformData.checked.2.1
  have hslope6 := FSNonuniformData.checked.2.2.1
  have hsize (d : D) : (E d).card ≤ 8192 :=
    (card_le_card (subset_univ _)).trans_eq (by simp)
  by_cases hsmall : T.card ≤ 4
  · calc
      _ ≤ ∑ _d ∈ T, (1 : ℚ) := sum_le_sum (fun d hd =>
        price_le_one _ _ FSNonuniformData.checked.1 (by unfold FSNonuniformData.capacity; positivity))
      _ = (T.card : ℚ) := by simp
      _ ≤ 4 := by exact_mod_cast hsmall
      _ ≤ 479/100 := by norm_num
  · have hcases : T.card = 5 ∨ T.card = 6 := by omega
    rcases hcases with hm | hm
    · have htotal : ∑ d ∈ T, (E d).card ≤ 14582 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 1) (by decide)
        rw [hm]
        norm_num
      have htotalQ : (∑ d ∈ T, ((E d).card : ℚ)) ≤ 14582 := by exact_mod_cast htotal
      calc
        _ ≤ ∑ d ∈ T, FSNonuniformData.line5 (E d).card :=
          sum_le_sum (fun d hd => (FSNonuniformData.affine_majorants _ (hmin d hd) (hsize d)).1)
        _ = 5*FSNonuniformData.f 2916 + FSNonuniformData.slope5*((∑ d ∈ T, ((E d).card : ℚ))-5*2916) := by
          simp only [FSNonuniformData.line5, mul_sub, sum_add_distrib, sum_sub_distrib, ← mul_sum,
            sum_const, nsmul_eq_mul, hm]
          ring
        _ ≤ 5*FSNonuniformData.f 2916 + FSNonuniformData.slope5*(14582-5*2916) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right htotalQ _) hslope5)
        _ ≤ 479/100 := FSNonuniformData.checked.2.2.2.1
    · have htotal : ∑ d ∈ T, (E d).card ≤ 17080 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 2) (by decide)
        rw [hm]
        norm_num
      have htotalQ : (∑ d ∈ T, ((E d).card : ℚ)) ≤ 17080 := by exact_mod_cast htotal
      calc
        _ ≤ ∑ d ∈ T, FSNonuniformData.line6 (E d).card :=
          sum_le_sum (fun d hd => (FSNonuniformData.affine_majorants _ (hmin d hd) (hsize d)).2)
        _ = 6*FSNonuniformData.f 2714 + FSNonuniformData.slope6*((∑ d ∈ T, ((E d).card : ℚ))-6*2714) := by
          simp only [FSNonuniformData.line6, mul_sub, sum_add_distrib, sum_sub_distrib, ← mul_sum,
            sum_const, nsmul_eq_mul, hm]
          ring
        _ ≤ 6*FSNonuniformData.f 2714 + FSNonuniformData.slope6*(17080-6*2714) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right htotalQ _) hslope6)
        _ ≤ 479/100 := FSNonuniformData.checked.2.2.2.2.1

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Actual capacity witnesses assemble the nonuniform resource bound.
All six low-response allowances are included in the shifted price. -/
theorem actual_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (ht : I.t = 81)
    (hover : p.overlapSize = 639) (hlist : p.listBound = 6)
    (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714) :
    spectrum I p W FSNonuniformData.shifted ≤ (479/100 : ℚ) := by
  let E := fun d : systems I.domain I.primary_le W =>
    Classical.choose (ReducedSystems.capacity_witness
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hs (d : systems I.domain I.primary_le W) :=
    Classical.choose_spec (ReducedSystems.capacity_witness
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  let E' := fun d => (E d).map (finCongr hn).toEmbedding
  have hcard (d) : (E' d).card = (E d).card := card_map _
  have hcap (d) : FSNonuniformData.capacity (E' d).card = systemCap I W d := by
    rw [hcard, (hs d).2]
    unfold FSNonuniformData.capacity systemCap
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _, ht,
      show I.n.choose 81 = Nat.choose 8192 81 from congrArg (fun n => n.choose 81) hn]
  have hi (d) (_hd : d ∈ highSystems I p W) (e) (_he : e ∈ highSystems I p W)
      (hne : d ≠ e) : (E' d ∩ E' e).card ≤ 639 := by
    have hh := ReducedSystems.associated_intersection
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask p.positive_degree d.1 e.1
      (E d) (E e) (hs d).1 (hs e).1 (fun h => hne (Subtype.ext h))
    change (E d ∩ E e).card ≤ p.overlapSize at hh
    rw [hover] at hh
    simpa only [E', ← map_inter, card_map] using hh
  have hmin (d) (hd : d ∈ highSystems I p W) : 2714 ≤ (E' d).card := by
    have hh := (mem_filter.mp hd).2
    rw [htheta, ← hcap] at hh
    unfold FSNonuniformData.capacity FSStoppedSpectrum.theta at hh
    have hx := DirectBinomial.size_ge_of_choose_div_gt
      (Nat.choose_pos (show 81 ≤ 8192 by decide)) le_rfl hh
    exact hx
  have hc : (highSystems I p W).card ≤ 6 := by
    rw [← hlist]
    exact highSystems_card_le I p hsmall W
  have hmain := family_spectrum_le (highSystems I p W) E' hi hmin hc
  change (∑ d ∈ highSystems I p W, price FSNonuniformData.shifted (systemCap I W d)) ≤ _
  calc
    _ = ∑ d ∈ highSystems I p W, FSNonuniformData.f (E' d).card := by
      apply sum_congr rfl
      intro d _
      rw [FSNonuniformData.f, hcap]
    _ ≤ _ := hmain

/-- The full recursive parent mean is at most 4.8/q, including rank. -/
theorem actual_spectrum_premise (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (ht : I.t = 81)
    (hover : p.overlapSize = 639) (hlist : p.listBound = 6)
    (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    p.toProfileParameters.rankError +
      spectrum I p W (FSNonuniformData.rate - 6*p.threshold) / Nat.card F ≤ FSNonuniformData.rate := by
  have he : FSNonuniformData.rate - 6*p.threshold = FSNonuniformData.shifted := by
    rw [htheta]; rfl
  rw [he, hmu, hq]
  have hs := actual_spectrum_le I p W hn ht hover hlist hsmall htheta
  have hm := FSNonuniformData.checked.2.2.2.2.2.1
  have hqpos : (0 : ℚ) < FSTwoLevel.fieldSize := by norm_num [FSTwoLevel.fieldSize]
  calc
    _ ≤ (1/100 : ℚ)/FSTwoLevel.fieldSize + (479/100 : ℚ)/FSTwoLevel.fieldSize :=
      add_le_add hm (div_le_div_of_nonneg_right hs hqpos.le)
    _ = FSNonuniformData.rate := by unfold FSNonuniformData.rate; ring

/-- Actual arbitrary-order first-two-role OracleSound certificate. -/
theorem query_oracle_sound {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (hcp : cp.listBound < Nat.card F) (hcList : cp.listBound = 6)
    (σ : I.layer.Statement)
    (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*FSNonuniformData.rate, FSNonuniformData.rate, mul_nonneg (by norm_num) FSNonuniformData.rate_nonneg,
        FSNonuniformData.rate_nonneg⟩ := by
  apply query_stopped_oracle_sound_of_spectrum child p cp hcp σ FSNonuniformData.rate
  · rw [hcList, htheta]
    exact sub_pos.mp FSNonuniformData.checked.1
  · intro W
    rw [hcList]
    exact actual_spectrum_premise I p W hn ht hover hlist hsmall htheta hmu hq

end RecursivePolygero.Benchmarks.FSNonuniformSpectrum
