import polygero.Benchmarks.FSBaselineAwareData
import polygero.Algebra.Counting.NonuniformOccupancy
import polygero.Recursion.FSJointCompletion

/-! Actual low-defect spectra with joint baseline pricing and a separate
four-system support budget. No exception independence is assumed. -/
set_option maxHeartbeats 300000
set_option maxRecDepth 50000

namespace RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum
open ProfileAnalysis ProfileAnalysis.StoppedSpectrum
open FiatShamir FiatShamir.TwoLevel Bcs.AffineBlock
open Finset Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

private theorem family_spectrum_le {D : Type} (T : Finset D)
    (E : D → Finset (Fin 8192)) (cap : D → ℕ)
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (E d ∩ E e).card ≤ 576)
    (hcap : ∀ d ∈ T, cap d ≤ (E d).card+64)
    (hmin : ∀ d ∈ T, 2714 ≤ cap d) (hcard : T.card ≤ 6) :
    ∑ d ∈ T, FSBaselineAwareData.f (cap d) ≤ FSBaselineAwareData.bound := by
  have htotal (M coretotal total : ℕ) (hm : T.card = M)
      (hcert : (M : ℤ)*(M-1)*576+8192*2 < 2*(coretotal+1))
      (heq : coretotal+M*64 = total) : ∑ d ∈ T, cap d ≤ total := by
    have hcores : ∑ d ∈ T, (E d).card ≤ coretotal := by
      apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 1) (by decide)
      rw [hm]
      convert hcert using 1 <;> norm_num
    calc
      _ ≤ ∑ d ∈ T, ((E d).card+64) := sum_le_sum hcap
      _ = (∑ d ∈ T, (E d).card)+M*64 := by simp [sum_add_distrib,hm]
      _ ≤ coretotal+M*64 := Nat.add_le_add_right hcores _
      _ = total := heq
  by_cases hsmall : T.card ≤ 3
  · calc
      _ ≤ ∑ _d ∈ T, (1 : ℚ) := sum_le_sum (fun d _ =>
        price_le_one FSBaselineAwareData.effective (FSBaselineAwareData.capacity (cap d))
          FSBaselineAwareData.checked.effective_pos
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      _ = (T.card : ℚ) := by simp
      _ ≤ 3 := by exact_mod_cast hsmall
      _ ≤ _ := FSBaselineAwareData.checked.three
  · have hcases : T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
    rcases hcases with hm | hm | hm
    · have hs := htotal 4 11648 11904 hm (by norm_num) (by norm_num)
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 11904 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSBaselineAwareData.line4 (cap d) :=
          sum_le_sum (fun d hd => FSBaselineAwareData.affine_majorant4 _ (hmin d hd))
        _ = 4*FSBaselineAwareData.f 2976 + FSBaselineAwareData.slope4*
            ((∑ d ∈ T, (cap d : ℚ))-11904) := by
          simp only [FSBaselineAwareData.line4,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 4*FSBaselineAwareData.f 2976 := by
          have h := mul_nonpos_of_nonneg_of_nonpos FSBaselineAwareData.checked.slope4_nonneg
            (sub_nonpos.mpr hsQ)
          exact add_le_of_nonpos_right h
        _ ≤ _ := FSBaselineAwareData.checked.four
    · have hs := htotal 5 13952 14272 hm (by norm_num) (by norm_num)
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 14272 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSBaselineAwareData.line (cap d) :=
          sum_le_sum (fun d hd => FSBaselineAwareData.affine_majorant _ (hmin d hd))
        _ = 5*FSBaselineAwareData.f 2714 + FSBaselineAwareData.slope*
            ((∑ d ∈ T, (cap d : ℚ))-5*2714) := by
          simp only [FSBaselineAwareData.line,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 5*FSBaselineAwareData.f 2714+FSBaselineAwareData.slope*(14272-5*2714) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hsQ _)
            FSBaselineAwareData.checked.slope_nonneg)
        _ ≤ _ := FSBaselineAwareData.checked.five
    · have hcores : ∑ d ∈ T, (E d).card ≤ 16608 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 2) (by decide)
        rw [hm]
        norm_num
      have hs : ∑ d ∈ T, cap d ≤ 16992 := by
        have hh := sum_le_sum (s := T) hcap
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hm] at hh
        omega
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 16992 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSBaselineAwareData.line (cap d) :=
          sum_le_sum (fun d hd => FSBaselineAwareData.affine_majorant _ (hmin d hd))
        _ = 6*FSBaselineAwareData.f 2714 + FSBaselineAwareData.slope*
            ((∑ d ∈ T, (cap d : ℚ))-6*2714) := by
          simp only [FSBaselineAwareData.line,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 6*FSBaselineAwareData.f 2714+FSBaselineAwareData.slope*(16992-6*2714) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hsQ _)
            FSBaselineAwareData.checked.slope_nonneg)
        _ ≤ _ := FSBaselineAwareData.checked.six

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem actual_low_defect_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (hk : I.r+I.w = 512)
    (hs : I.s = 64) (ht : I.t = 81) (hlist : p.listBound = 6)
    (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714) :
    lowDefectSpectrum I p W FSBaselineAwareData.effective ≤ FSBaselineAwareData.bound := by
  let T := (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1)
  let E := fun d : systems I.domain I.primary_le W => d.1.map (finCongr hn).toEmbedding
  let cap := fun d : systems I.domain I.primary_le W =>
    ReducedSystems.capacity (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1
  have hcap (d) (_hd : d ∈ T) : cap d ≤ (E d).card+64 := by
    have hh := capacity_add_defect_le_core_add_masks I W d
    simp only [E, card_map]
    change cap d+systemDefect I W d ≤ d.1.card+I.s at hh
    omega
  have hi (d) (hd : d ∈ T) (e) (he : e ∈ T) (hne : d ≠ e) :
      (E d ∩ E e).card ≤ 576 := by
    have hh := low_defect_core_intersection_le I (by omega) W d e hne 1 (by omega)
      (mem_filter.mp hd).2 (mem_filter.mp he).2
    have hgeom : I.r+I.w+I.s+1-1 = 576 := by omega
    rw [hgeom] at hh
    simpa only [E, ← map_inter, card_map] using hh
  have hbin (d) : FSBaselineAwareData.capacity (cap d) = systemCap I W d := by
    unfold FSBaselineAwareData.capacity FSDefectData.capacity systemCap
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _, ht,
      show I.n.choose 81 = Nat.choose 8192 81 from congrArg (fun n => n.choose 81) hn]
  have hmin (d) (hd : d ∈ T) : 2714 ≤ cap d := by
    have hh := (mem_filter.mp ((mem_filter.mp hd).1)).2
    rw [htheta, ← hbin] at hh
    unfold FSBaselineAwareData.capacity FSDefectData.capacity FSStoppedSpectrum.theta at hh
    exact DirectBinomial.size_ge_of_choose_div_gt
      (Nat.choose_pos (show 81 ≤ 8192 by decide)) le_rfl hh
  have hc : T.card ≤ 6 := by
    apply (card_filter_le _ _).trans
    rw [← hlist]
    exact highSystems_card_le I p hsmall W
  have hmain := family_spectrum_le T E cap hi hcap hmin hc
  change (∑ d ∈ T, price FSBaselineAwareData.effective (systemCap I W d)) ≤ _
  calc
    _ = ∑ d ∈ T, FSBaselineAwareData.f (cap d) := by
      apply sum_congr rfl
      intro d _
      rw [FSBaselineAwareData.f,hbin]
    _ ≤ _ := hmain

theorem actual_parent_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (hn : I.n = 8192) (hk : I.r+I.w = 512) (hs : I.s = 64) (ht : I.t = 81)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    mean (fun a => Bcs.StoppedPotential.repeatPrice FSBaselineAwareData.rate
      (conditionalCapacity I p σ W (6*p.threshold) a)) ≤ FSBaselineAwareData.rate := by
  have he : 6*p.threshold = FSBaselineAwareData.baseline := by rw [htheta]; rfl
  have hm := conditionalCapacity_repeatPrice_mean_le_effective I p hsmall σ W
    FSBaselineAwareData.rate (6*p.threshold) FSBaselineAwareData.effective
    (mul_nonneg (by norm_num) p.threshold_nonneg) FSBaselineAwareData.checked.effective_pos
    (by rw [he]; exact FSBaselineAwareData.checked.discriminant)
    (by rw [he]; exact FSBaselineAwareData.checked.branch)
  have hl := actual_low_defect_spectrum_le I p W hn hk hs ht hlist hsmall htheta
  rw [hmu,hlist,hq] at hm
  have hqpos : (0 : ℚ) ≤ FSTwoLevel.fieldSize := by positivity
  exact hm.trans ((add_le_add (add_le_add le_rfl
    (div_le_div_of_nonneg_right hl hqpos)) le_rfl).trans FSBaselineAwareData.checked.remainder)

end RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum
