import polygero.Instances.FSShiftedData
import polygero.Algebra.Counting.NonuniformOccupancy
import polygero.Recursion.FSJointCompletion
import polygero.Local.ShiftedEnvelope

/-! Actual low-defect spectra with joint baseline pricing and a separate
four-system support budget. No exception independence is assumed. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000

namespace RecursivePolygero.Instances.FSShiftedSpectrum
open ProfileAnalysis ProfileAnalysis.ShiftedSpectrum
open FiatShamir FiatShamir.TwoLevel Bcs.AffineBlock
open Finset Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

private theorem family_spectrum_le {D : Type} (T : Finset D)
    (E : D → Finset (Fin 8192)) (cap : D → ℕ)
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (E d ∩ E e).card ≤ 576)
    (hcap : ∀ d ∈ T, cap d ≤ (E d).card)
    (hmin : ∀ d ∈ T, 2650 ≤ cap d) (hcard : T.card ≤ 6) :
    ∑ d ∈ T, FSShiftedData.f (cap d) ≤ FSShiftedData.bound := by
  have htotal (M coretotal total : ℕ) (hm : T.card = M)
      (hcert : (M : ℤ)*(M-1)*576+8192*2 < 2*(coretotal+1))
      (heq : coretotal = total) : ∑ d ∈ T, cap d ≤ total := by
    have hcores : ∑ d ∈ T, (E d).card ≤ coretotal := by
      apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 1) (by decide)
      rw [hm]
      convert hcert using 1 <;> norm_num
    exact ((sum_le_sum hcap).trans hcores).trans_eq heq
  by_cases hsmall : T.card ≤ 3
  · calc
      _ ≤ ∑ _d ∈ T, (1 : ℚ) := sum_le_sum (fun d _ =>
        price_le_one FSShiftedData.baseline FSShiftedData.pivot
          FSShiftedData.checked.baseline_nonneg FSShiftedData.checked.pivot_pos (FSShiftedData.capacity (cap d))
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      _ = (T.card : ℚ) := by simp
      _ ≤ 3 := by exact_mod_cast hsmall
      _ ≤ _ := FSShiftedData.checked.three
  · have hcases : T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
    rcases hcases with hm | hm | hm
    · have hs := htotal 4 11648 11648 hm (by norm_num) (by norm_num)
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 11648 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSShiftedData.line4 (cap d) :=
          sum_le_sum (fun d hd => FSShiftedData.affine_majorant4 _ (hmin d hd))
        _ = 4*FSShiftedData.f 2912 + FSShiftedData.slope4*
            ((∑ d ∈ T, (cap d : ℚ))-11648) := by
          simp only [FSShiftedData.line4,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 4*FSShiftedData.f 2912 := by
          have h := mul_nonpos_of_nonneg_of_nonpos FSShiftedData.checked.slope4_nonneg
            (sub_nonpos.mpr hsQ)
          exact add_le_of_nonpos_right h
        _ ≤ _ := FSShiftedData.checked.four
    · have hs := htotal 5 13952 13952 hm (by norm_num) (by norm_num)
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 13952 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSShiftedData.line (cap d) :=
          sum_le_sum (fun d hd => FSShiftedData.affine_majorant _ (hmin d hd))
        _ = 5*FSShiftedData.f 2650 + FSShiftedData.slope*
            ((∑ d ∈ T, (cap d : ℚ))-5*2650) := by
          simp only [FSShiftedData.line,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 5*FSShiftedData.f 2650+FSShiftedData.slope*(13952-5*2650) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hsQ _)
            FSShiftedData.checked.slope_nonneg)
        _ ≤ _ := FSShiftedData.checked.five
    · have hcores : ∑ d ∈ T, (E d).card ≤ 16608 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 2) (by decide)
        rw [hm]
        norm_num
      have hs : ∑ d ∈ T, cap d ≤ 16608 := by
        exact (sum_le_sum hcap).trans hcores
      have hsQ : (∑ d ∈ T, (cap d : ℚ)) ≤ 16608 := by exact_mod_cast hs
      calc
        _ ≤ ∑ d ∈ T, FSShiftedData.line (cap d) :=
          sum_le_sum (fun d hd => FSShiftedData.affine_majorant _ (hmin d hd))
        _ = 6*FSShiftedData.f 2650 + FSShiftedData.slope*
            ((∑ d ∈ T, (cap d : ℚ))-6*2650) := by
          simp only [FSShiftedData.line,mul_sub,sum_add_distrib,sum_sub_distrib,
            ← mul_sum,sum_const,nsmul_eq_mul,hm]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 6*FSShiftedData.f 2650+FSShiftedData.slope*(16608-6*2650) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hsQ _)
            FSShiftedData.checked.slope_nonneg)
        _ ≤ _ := FSShiftedData.checked.six

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem actual_low_defect_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (hk : I.r+I.w = 512)
    (hs : I.s = 64) (ht : I.t = 81) (hlist : p.listBound = 6)
    (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714) :
    coreSpectrum I p W FSShiftedData.baseline FSShiftedData.pivot ≤ FSShiftedData.bound := by
  let T := (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1)
  let E := fun d : systems I.domain I.primary_le W => d.1.map (finCongr hn).toEmbedding
  let cap := fun d : systems I.domain I.primary_le W => d.1.card
  have hcap (d) (_hd : d ∈ T) : cap d ≤ (E d).card := by simp [cap,E]
  have hi (d) (hd : d ∈ T) (e) (he : e ∈ T) (hne : d ≠ e) :
      (E d ∩ E e).card ≤ 576 := by
    have hh := low_defect_core_intersection_le I (by omega) W d e hne 1 (by omega)
      (mem_filter.mp hd).2 (mem_filter.mp he).2
    have hgeom : I.r+I.w+I.s+1-1 = 576 := by omega
    rw [hgeom] at hh
    simpa only [E, ← map_inter, card_map] using hh
  have hbin (d) : FSShiftedData.capacity (cap d) = coreCapacity I W d := by
    unfold FSShiftedData.capacity FSDefectData.capacity coreCapacity
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _,ht,
      show I.n.choose 81 = Nat.choose 8192 81 from congrArg (fun n => n.choose 81) hn]
  have hmin (d) (hd : d ∈ T) : 2650 ≤ cap d := by
    have hh := (mem_filter.mp ((mem_filter.mp hd).1)).2
    rw [htheta] at hh
    unfold systemCap FSStoppedSpectrum.theta at hh
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _,ht,
      show I.n.choose 81 = Nat.choose 8192 81 from congrArg (fun n => n.choose 81) hn] at hh
    have hraw := DirectBinomial.size_ge_of_choose_div_gt
      (Nat.choose_pos (show 81 ≤ 8192 by decide)) le_rfl hh
    have hc := capacity_add_defect_le_core_add_masks I W d
    change _+systemDefect I W d ≤ cap d+I.s at hc
    omega
  have hc : T.card ≤ 6 := by
    apply (card_filter_le _ _).trans
    rw [← hlist]
    exact highSystems_card_le I p hsmall W
  have hmain := family_spectrum_le T E cap hi hcap hmin hc
  change (∑ d ∈ T, price FSShiftedData.baseline FSShiftedData.pivot (coreCapacity I W d)) ≤ _
  calc
    _ = ∑ d ∈ T, FSShiftedData.f (cap d) := by
      apply sum_congr rfl
      intro d _
      rw [FSShiftedData.f,hbin]
    _ ≤ _ := hmain

theorem actual_parent_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (hn : I.n = 8192) (hk : I.r+I.w = 512) (hs : I.s = 64) (ht : I.t = 81)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    mean (fun a => Bcs.StoppedPotential.repeatPrice FSShiftedData.rate
      (refinedConditionalCapacity I p σ W (6*p.threshold) a)) ≤ FSShiftedData.rate := by
  have he : 6*p.threshold = FSShiftedData.baseline := by rw [htheta]; rfl
  have hm := refinedConditional_repeatPrice_mean_le I p hsmall σ W
    FSShiftedData.rate (6*p.threshold) FSShiftedData.pivot
    (mul_nonneg (by norm_num) p.threshold_nonneg) FSShiftedData.checked.pivot_pos
    (by rw [he]; exact FSShiftedData.checked.tangent)
  have hl := actual_low_defect_spectrum_le I p W hn hk hs ht hlist hsmall htheta
  rw [hmu,hlist,hq,hn,he] at hm
  have hqpos : (0 : ℚ) ≤ FSTwoLevel.fieldSize := by positivity
  rw [he]
  exact hm.trans ((add_le_add (add_le_add le_rfl
    (div_le_div_of_nonneg_right hl hqpos)) le_rfl).trans FSShiftedData.checked.remainder)

end RecursivePolygero.Instances.FSShiftedSpectrum
