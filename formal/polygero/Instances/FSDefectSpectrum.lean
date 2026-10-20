import polygero.Instances.FSDefectData
import polygero.Local.DefectPacking
import polygero.Algebra.Counting.NonuniformOccupancy
import polygero.Recursion.FSStoppedCharges

/-! Defect-sensitive actual capacity spectra at 81 parent openings.
Low-defect canonical closures use their stronger 576-column overlap;
the omitted-column allowance is charged separately from core size. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 50000

namespace RecursivePolygero.Instances.FSDefectSpectrum

open ProfileAnalysis ProfileAnalysis.StoppedSpectrum
open FiatShamir FiatShamir.TwoLevel Bcs.AffineBlock
open Finset Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

private theorem family_spectrum_le {D : Type} (T : Finset D)
    (E : D → Finset (Fin 8192)) (cap : D → ℕ)
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (E d ∩ E e).card ≤ 576)
    (hcap : ∀ d ∈ T, cap d ≤ (E d).card+64)
    (hmin : ∀ d ∈ T, 2714 ≤ cap d) (hmax : ∀ d ∈ T, cap d ≤ 8192)
    (hcard : T.card ≤ 6) :
    ∑ d ∈ T, FSDefectData.f (cap d) ≤ 4-7/(FSTwoLevel.fieldSize : ℚ) := by
  have hslope := FSDefectData.checked.2.2.1
  by_cases hsmall : T.card ≤ 4
  · have hn : 0 ≤ 1-FSDefectData.shifted := by
      have h := FSDefectData.checked.2.1
      linarith
    calc
      _ ≤ ∑ _d ∈ T, (1-FSDefectData.shifted) :=
        sum_le_sum (fun d hd => FSDefectData.f_le_one_sub_shifted _ (hmax d hd))
      _ = (T.card : ℚ)*(1-FSDefectData.shifted) := by
        simp only [sum_const, nsmul_eq_mul]
      _ ≤ 4*(1-FSDefectData.shifted) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) hn
      _ ≤ _ := by have h := FSDefectData.checked.2.2.2.2.2.2.1; linarith
  · have hcases : T.card = 5 ∨ T.card = 6 := by omega
    have hbound (M total : ℕ) (hm : T.card = M)
        (htotal : ∑ d ∈ T, cap d ≤ total)
        (hline : (M : ℚ)*FSDefectData.f 2714 +
          FSDefectData.slope*((total : ℚ)-M*2714) ≤ (3999/1000 : ℚ)) :
        ∑ d ∈ T, FSDefectData.f (cap d) ≤ (3999/1000 : ℚ) := by
      have htotalQ : (∑ d ∈ T, (cap d : ℚ)) ≤ total := by exact_mod_cast htotal
      calc
        _ ≤ ∑ d ∈ T, FSDefectData.line (cap d) :=
          sum_le_sum (fun d hd => FSDefectData.affine_majorant _ (hmin d hd))
        _ = (M : ℚ)*FSDefectData.f 2714 +
            FSDefectData.slope*((∑ d ∈ T, (cap d : ℚ))-M*2714) := by
          simp only [FSDefectData.line, mul_sub, sum_add_distrib, sum_sub_distrib,
            ← mul_sum, sum_const, nsmul_eq_mul, hm]
        _ ≤ (M : ℚ)*FSDefectData.f 2714 +
            FSDefectData.slope*((total : ℚ)-M*2714) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right htotalQ _) hslope)
        _ ≤ _ := hline
    rcases hcases with hm | hm
    · have hcores : ∑ d ∈ T, (E d).card ≤ 13952 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 1) (by decide)
        rw [hm]
        norm_num
      have htotal : ∑ d ∈ T, cap d ≤ 14272 := by
        have hh := sum_le_sum (s := T) hcap
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hm] at hh
        omega
      exact (hbound 5 14272 hm htotal FSDefectData.checked.2.2.2.1).trans
        FSDefectData.checked.2.2.2.2.2.1
    · have hcores : ∑ d ∈ T, (E d).card ≤ 16608 := by
        apply CodingTheory.NonuniformOccupancy.sum_card_le T E hinter (h := 2) (by decide)
        rw [hm]
        norm_num
      have htotal : ∑ d ∈ T, cap d ≤ 16992 := by
        have hh := sum_le_sum (s := T) hcap
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hm] at hh
        omega
      exact (hbound 6 16992 hm htotal FSDefectData.checked.2.2.2.2.1).trans
        FSDefectData.checked.2.2.2.2.2.1

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The actual low-defect systems obey a strengthened whole-family
spectrum bound. Its tiny slack pays rank and high-defect consistency. -/
theorem actual_low_defect_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (hk : I.r+I.w = 512)
    (hs : I.s = 64) (ht : I.t = 81) (hlist : p.listBound = 6)
    (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714) :
    (∑ d ∈ (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1),
      price FSDefectData.shifted (systemCap I W d)) ≤
        4-7/(FSTwoLevel.fieldSize : ℚ) := by
  let T := (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1)
  let E := fun d : systems I.domain I.primary_le W => d.1.map (finCongr hn).toEmbedding
  let cap := fun d : systems I.domain I.primary_le W =>
    ReducedSystems.capacity (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1
  have hcap (d) (_hd : d ∈ T) : cap d ≤ (E d).card+64 := by
    have hh := capacity_add_defect_le_core_add_masks I W d
    simp only [E, card_map]
    change cap d + systemDefect I W d ≤ d.1.card + I.s at hh
    omega
  have hi (d) (hd : d ∈ T) (e) (he : e ∈ T) (hne : d ≠ e) :
      (E d ∩ E e).card ≤ 576 := by
    have hh := low_defect_core_intersection_le I (by omega) W d e hne 1 (by omega)
      (mem_filter.mp hd).2 (mem_filter.mp he).2
    have hgeom : I.r+I.w+I.s+1-1 = 576 := by omega
    rw [hgeom] at hh
    simpa only [E, ← map_inter, card_map] using hh
  have hbin (d) : FSDefectData.capacity (cap d) = systemCap I W d := by
    unfold FSDefectData.capacity systemCap
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _, ht,
      show I.n.choose 81 = Nat.choose 8192 81 from congrArg (fun n => n.choose 81) hn]
  have hmin (d) (hd : d ∈ T) : 2714 ≤ cap d := by
    have hh := (mem_filter.mp ((mem_filter.mp hd).1)).2
    rw [htheta, ← hbin] at hh
    unfold FSDefectData.capacity FSStoppedSpectrum.theta at hh
    exact DirectBinomial.size_ge_of_choose_div_gt
      (Nat.choose_pos (show 81 ≤ 8192 by decide)) le_rfl hh
  have hmax (d) (_hd : d ∈ T) : cap d ≤ 8192 := by
    have hh := ReducedSystems.capacity_le_n
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1
    exact hh.trans_eq hn
  have hc : T.card ≤ 6 := by
    apply (card_filter_le _ _).trans
    rw [← hlist]
    exact highSystems_card_le I p hsmall W
  have hmain := family_spectrum_le T E cap hi hcap hmin hmax hc
  calc
    _ = ∑ d ∈ T, FSDefectData.f (cap d) := by
      apply sum_congr rfl
      intro d _
      rw [FSDefectData.f, hbin]
    _ ≤ _ := hmain

/-- Rank and all high-defect exceptions fit inside the exact low-defect
slack. The six-response recursive baseline remains paid in full. -/
theorem actual_parent_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (hn : I.n = 8192) (hk : I.r+I.w = 512) (hs : I.s = 64) (ht : I.t = 81)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    mean (fun a => Bcs.StoppedPotential.repeatPrice FSDefectData.rate
      (conditionalCapacity I p σ W (6*p.threshold) a)) ≤ FSDefectData.rate := by
  have hb : 0 ≤ 6*p.threshold := mul_nonneg (by norm_num) p.threshold_nonneg
  have he : FSDefectData.rate-6*p.threshold = FSDefectData.shifted := by
    rw [htheta]; rfl
  have hbr : 6*p.threshold < FSDefectData.rate := by
    apply sub_pos.mp
    rw [he]
    exact FSDefectData.checked.1
  have hm := conditionalCapacity_repeatPrice_mean_le_defect_split I p hsmall σ W
    FSDefectData.rate (6*p.threshold) hb hbr
  have hlow := actual_low_defect_spectrum_le I p W hn hk hs ht hlist hsmall htheta
  change lowDefectSpectrum I p W FSDefectData.shifted ≤ _ at hlow
  rw [he, hmu, hlist, hq] at hm
  have hqpos : (0 : ℚ) < FSTwoLevel.fieldSize := by norm_num [FSTwoLevel.fieldSize]
  have hrank := FSDefectData.checked.2.2.2.2.2.2.2.1
  calc
    _ ≤ FSTwoLevel.rankError +
        lowDefectSpectrum I p W FSDefectData.shifted / FSTwoLevel.fieldSize +
        6/(FSTwoLevel.fieldSize : ℚ)^2 := hm
    _ ≤ 1/(FSTwoLevel.fieldSize : ℚ)^2 +
        (4-7/(FSTwoLevel.fieldSize : ℚ))/FSTwoLevel.fieldSize +
        6/(FSTwoLevel.fieldSize : ℚ)^2 :=
      add_le_add (add_le_add hrank (div_le_div_of_nonneg_right hlow hqpos.le)) le_rfl
    _ = FSDefectData.rate := by
      unfold FSDefectData.rate
      field_simp
      ring

/-- Actual arbitrary-order parent-query certificate with the clean
126-bit per-query coefficient, without changing 81/80 openings. -/
theorem query_oracle_sound {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (hcp : cp.listBound < Nat.card F) (hcList : cp.listBound = 6)
    (σ : I.layer.Statement)
    (hn : I.n = 8192) (hk : I.r+I.w = 512) (hs : I.s = 64) (ht : I.t = 81)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*FSDefectData.rate, FSDefectData.rate,
        mul_nonneg (by norm_num) FSDefectData.rate_nonneg, FSDefectData.rate_nonneg⟩ := by
  apply query_stopped_oracle_sound child p cp hcp σ FSDefectData.rate FSDefectData.rate_nonneg
  intro W
  change mean (fun a => Bcs.StoppedPotential.repeatPrice FSDefectData.rate
    (conditionalCapacity I p σ W (cp.listBound*p.threshold) a)) ≤ _
  rw [hcList]
  exact actual_parent_mean_le I p σ W hn hk hs ht hlist hsmall htheta hmu hq

end RecursivePolygero.Instances.FSDefectSpectrum
