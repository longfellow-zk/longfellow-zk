import polygero.Local.CapacityRigidity
import polygero.Local.StoppedSpectrum

/-!
# Defect-sensitive packing of actual reduced-system closures

Capacities are attained by analysis sets which may omit columns from a
canonical closure. Their omitted-column allowance decreases with the
closure's consistency defect. Low-defect closures consequently admit a
stronger packing bound than arbitrary capacity witnesses.
-/

namespace RecursivePolygero.ProfileAnalysis

open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F]

noncomputable def systemDefect (I : Instance F) (W : Oracle F I.nw I.nq I.n)
    (d : systems I.domain I.primary_le W) : ℕ :=
  fixedConsistencyCodimension (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) d.1 I.s

/-- A capacity witness loses at most `s-defect` columns on passing to its
actual canonical closure. No independently enlarged support is used. -/
theorem capacity_add_defect_le_core_add_masks
    (I : Instance F) (W : Oracle F I.nw I.nq I.n) (d : systems I.domain I.primary_le W) :
    ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 + systemDefect I W d ≤ d.1.card + I.s := by
  let C := primaryCode I.domain I.primary_le
  let W' := oracleWords W.ordinary
  obtain ⟨T, hT, hcap⟩ := ReducedSystems.capacity_witness C W' W.proximityMask d.1 d.2
  obtain ⟨_, hsize, hlow, hne, hlabel⟩ := mem_filter.mp hT
  obtain ⟨hc, hST, hdrop⟩ := PolynomialClosure.canonical_core C W' T hlow (by omega)
  have hneS := hne.mono (ConsistencyClosure.solutions_antitone _ _ hST)
  have hdef := (PolynomialClosure.closure_geometry C W' W.proximityMask _ hc hneS).2
  rw [hlabel] at hdef
  have hSD := ConsistencyClosure.subset_closure (PolynomialClosure.jointMap C W')
    W.proximityMask (PolynomialClosure.canonicalCoreSet C W' T)
  change PolynomialClosure.canonicalCoreSet C W' T ⊆
    PolynomialClosure.closure C W' W.proximityMask (PolynomialClosure.canonicalCoreSet C W' T) at hSD
  rw [hlabel] at hSD
  have hcount := card_le_card hSD
  have hsum := card_sdiff_add_card_eq_card hST
  change ReducedSystems.capacity C W' W.proximityMask d.1 +
    fixedConsistencyCodimension C W' d.1 I.s ≤ _
  rw [← hcap]
  omega

/-- Different actual affine closures of defect at most `e` intersect in
at most `k+s+e-1` columns. The extra `s` is essential: homogeneous rank
equality alone does not identify the affine proximity-mask offsets. -/
theorem low_defect_core_intersection_le
    (I : Instance F) (hk : 1 ≤ I.r + I.w) (W : Oracle F I.nw I.nq I.n)
    (a b : systems I.domain I.primary_le W) (hne : a ≠ b)
    (e : ℕ) (he : e ≤ I.s)
    (ha : systemDefect I W a ≤ e) (hb : systemDefect I W b ≤ e) :
    (a.1 ∩ b.1).card ≤ I.r + I.w + I.s + e - 1 := by
  let C := primaryCode I.domain I.primary_le
  let W' := oracleWords W.ordinary
  let A := PolynomialClosure.jointMap C W'
  have ga := geometry a
  have gb := geometry b
  have hra := PolynomialClosure.joint_rank C W' a.1 (by have := ga.core.large; omega)
  have hrb := PolynomialClosure.joint_rank C W' b.1 (by have := gb.core.large; omega)
  change ConsistencyClosure.rank A a.1 = I.r + I.w + I.s + systemDefect I W a at hra
  change ConsistencyClosure.rank A b.1 = I.r + I.w + I.s + systemDefect I W b at hrb
  by_contra hsmall
  have hI : I.r + I.w + I.s + e ≤ (a.1 ∩ b.1).card := by omega
  obtain ⟨hU, hU', hmds⟩ := PolynomialClosure.core_union_mds C W' hk a.1 b.1 ga.core gb.core (by
    change ConsistencyClosure.rank A a.1 + ConsistencyClosure.rank A b.1 ≤
      (a.1 ∩ b.1).card + (I.r + I.w + 2 * I.s)
    omega)
  change ConsistencyClosure.rank A a.1 = ConsistencyClosure.rank A (a.1 ∪ b.1) at hU
  change ConsistencyClosure.rank A b.1 = ConsistencyClosure.rank A (a.1 ∪ b.1) at hU'
  change ∀ H ⊆ a.1 ∪ b.1, ConsistencyClosure.rank A H =
    min H.card (ConsistencyClosure.rank A (a.1 ∪ b.1)) at hmds
  have hIr : ConsistencyClosure.rank A (a.1 ∩ b.1) = ConsistencyClosure.rank A a.1 := by
    rw [hmds _ (inter_subset_left.trans subset_union_left), ← hU, min_eq_right (by omega)]
  have hsol := (ConsistencyClosure.solutions_eq_of_rank_eq A W.proximityMask inter_subset_left
    ga.nonempty hIr).symm.trans
    (ConsistencyClosure.solutions_eq_of_rank_eq A W.proximityMask inter_subset_right
      gb.nonempty (hIr.trans (hU.trans hU'.symm)))
  have hclose := (ConsistencyClosure.closure_eq_iff_solutions_eq A W.proximityMask a.1 b.1).mpr hsol
  apply hne
  apply Subtype.ext
  exact ga.closed.symm.trans (hclose.trans gb.closed)

/-- A supplied uniform-family bound can be applied to low-defect cores
once each capacity exceeds the core cutoff plus the omitted-column budget. -/
theorem low_defect_capacity_systems_card_le
    (I : Instance F) (hk : 1 ≤ I.r + I.w) (W : Oracle F I.nw I.nq I.n)
    (e cutoff L : ℕ) (he : e ≤ I.s)
    (hcutoff : I.r + I.w + I.s + e - 1 < cutoff)
    (hb : CodingTheory.UniformFamilyBound I.n cutoff (I.r + I.w + I.s + e - 1) L) :
    (univ.filter (fun d : systems I.domain I.primary_le W =>
      systemDefect I W d ≤ e ∧ cutoff + I.s ≤
        ReducedSystems.capacity (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask d.1)).card ≤ L := by
  let T := univ.filter (fun d : systems I.domain I.primary_le W =>
    systemDefect I W d ≤ e ∧ cutoff + I.s ≤
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1)
  apply DirectBinomial.active_card_le_of_uniformFamilyBound T (fun d => d.1)
    cutoff (I.r + I.w + I.s + e - 1) L hcutoff _ _ hb
  · intro d hd
    have hc := capacity_add_defect_le_core_add_masks I W d
    have hlarge := (mem_filter.mp hd).2.2
    omega
  · intro a ha b hb hne
    exact low_defect_core_intersection_le I hk W a b hne e he
      (mem_filter.mp ha).2.1 (mem_filter.mp hb).2.1

/-- At the fixed geometry, at most four defect-zero-or-one systems can
have capacity at least 2916. The universal 639-overlap spectrum permits
five; the actual affine cores exclude that low-defect configuration. -/
theorem fixed_low_defect_capacity_systems_card_le_four
    (I : Instance F) (W : Oracle F I.nw I.nq I.n)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64) :
    (univ.filter (fun d : systems I.domain I.primary_le W =>
      systemDefect I W d ≤ 1 ∧ 2916 ≤
        ReducedSystems.capacity (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask d.1)).card ≤ 4 := by
  have hb : CodingTheory.UniformFamilyBound I.n 2852 (I.r + I.w + I.s + 1 - 1) 4 := by
    rw [hn, hk, hs]
    apply CodingTheory.IntegerOccupancy.uniformFamilyBound (h := 1)
    norm_num
  simpa only [hs, show 2852 + 64 = 2916 from rfl] using
    low_defect_capacity_systems_card_le I (by omega) W 1 2852 4 (by omega) (by omega) hb

private theorem sum_sets_card_le_biUnion {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset α) (E : α → Finset (Fin n)) (lam : ℕ)
    (hpair : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (E a ∩ E b).card ≤ lam) :
    (2 : ℤ) * (∑ a ∈ T, (E a).card) ≤
      2 * (T.biUnion E).card + (T.card : ℤ) * (T.card - 1) * lam := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T hnot ih =>
    have hi := ih (fun b hb c hc hne => hpair b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hne)
    have hinter : (E a ∩ T.biUnion E).card ≤ T.card * lam := by
      have he : E a ∩ T.biUnion E = T.biUnion (fun b => E a ∩ E b) := by
        ext j
        simp only [mem_inter, mem_biUnion]
        tauto
      rw [he]
      apply card_biUnion_le.trans
      exact (sum_le_sum (fun b hb => hpair a (mem_insert_self _ _) b (mem_insert_of_mem hb)
        (fun he => hnot (he ▸ hb)))).trans_eq (by simp)
    have hcard := card_union_add_card_inter (E a) (T.biUnion E)
    have hinterZ : ((E a ∩ T.biUnion E).card : ℤ) ≤ (T.card : ℤ) * lam := by exact_mod_cast hinter
    have hcardZ : ((E a ∪ T.biUnion E).card : ℤ) + (E a ∩ T.biUnion E).card =
      (E a).card + (T.biUnion E).card := by exact_mod_cast hcard
    simp only [sum_insert hnot, Nat.cast_add, card_insert_of_notMem hnot, Nat.cast_one,
      biUnion_insert] at ⊢
    nlinarith

/-- Nonuniform support budget for any fixed family of low-defect systems.
This retains total capacities, rather than bounding each by an individual
tail cutoff, so tangent-line stopped-price certificates can use it. -/
theorem low_defect_capacity_sum_le
    (I : Instance F) (hk : 1 ≤ I.r + I.w) (W : Oracle F I.nw I.nq I.n)
    (T : Finset (systems I.domain I.primary_le W))
    (e : ℕ) (he : e ≤ I.s) (hdefect : ∀ d ∈ T, systemDefect I W d ≤ e) :
    (2 : ℤ) * (∑ d ∈ T, ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1) ≤
      (T.card : ℤ) * (T.card - 1) * ((I.r + I.w + I.s + e - 1 : ℕ) : ℤ) +
        2 * I.n + 2 * T.card * I.s := by
  have hc := sum_sets_card_le_biUnion T (fun d => d.1) (I.r + I.w + I.s + e - 1)
    (fun a ha b hb hne => low_defect_core_intersection_le I hk W a b hne e he
      (hdefect a ha) (hdefect b hb))
  have hn : (T.biUnion (fun d => d.1)).card ≤ I.n := by simpa using card_le_univ (T.biUnion (fun d => d.1))
  have hs : (∑ d ∈ T, ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1) ≤ (∑ d ∈ T, d.1.card) + T.card * I.s := by
    calc
      _ ≤ ∑ d ∈ T, (d.1.card + I.s) := sum_le_sum (fun d _ => by
        have h := capacity_add_defect_le_core_add_masks I W d
        omega)
      _ = _ := by simp [sum_add_distrib]
  have hnZ : ((T.biUnion (fun d => d.1)).card : ℤ) ≤ I.n := by exact_mod_cast hn
  have hsZ : (∑ d ∈ T, (ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 : ℤ)) ≤
        (∑ d ∈ T, (d.1.card : ℤ)) + (T.card : ℤ) * I.s := by exact_mod_cast hs
  simp only [Nat.cast_sum] at hc ⊢
  nlinarith

variable [Fintype F] [DecidableEq F]

/-- Higher-defect systems pay two independent field conditions. This
counts actual affine consistency, without any independent-sampling premise. -/
theorem systemConsistency_mean_le_inv_sq_of_defect
    (I : Instance F) (W : Oracle F I.nw I.nq I.n) (d : systems I.domain I.primary_le W)
    (hdefect : 2 ≤ systemDefect I W d) :
    mean (fun B => indicator (B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1)) ≤ 1 / (Nat.card F : ℚ)^2 := by
  classical
  try dsimp only [Instance.layer] at *
  let C := primaryCode I.domain I.primary_le
  let W' := oracleWords W.ordinary
  have hd := fixedConsistencyDimension_add_codimension C W' d.1 (s := I.s)
  have hc := Affine.consistent_card_mul_field_pow_le C W' W.proximityMask d.1 1 (by
    change 2 ≤ fixedConsistencyCodimension C W' d.1 I.s at hdefect
    omega)
  change mean (fun B : Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (B ∈ Affine.consistent C W' W.proximityMask d.1)) ≤ _
  rw [mean_indicator]
  simp only [filter_mem_eq_inter, univ_inter]
  apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos)
    (pow_pos (by exact_mod_cast Nat.card_pos (α := F)) 2)).mpr
  simpa only [one_mul, Nat.cast_mul, Nat.cast_pow, Nat.card_eq_fintype_card] using
    (Nat.cast_le (α := ℚ).mpr hc)

theorem system_not_full_of_high_defect
    (I : Instance F) (W : Oracle F I.nw I.nq I.n) (d : systems I.domain I.primary_le W)
    (hdefect : 2 ≤ systemDefect I W d) :
    Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 ≠ univ := by
  intro hfull
  have h := systemConsistency_mean_le_inv_sq_of_defect I W d hdefect
  simp only [hfull, mem_univ, indicator, if_true, mean_const] at h
  have hq : (2 : ℚ) ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2 ≤ Fintype.card F from Fintype.one_lt_card)
  have hq2 : (0 : ℚ) < (Nat.card F : ℚ)^2 := by positivity
  have h' := (le_div_iff₀ hq2).mp h
  nlinarith

/-- For a proper high-defect system, the actual verifier exception is its
consistency fiber; hence the stronger `q^-2` count applies to the full coin. -/
theorem systemExceptions_mean_le_inv_sq_of_defect
    (I : Instance F) (p : ProfileParameters I)
    (σ : ConstraintSystem F I.nw I.nq I.q I.Equations) (W : Oracle F I.nw I.nq I.n) (d : systems I.domain I.primary_le W)
    (hdefect : 2 ≤ systemDefect I W d) :
    mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
      1 / (Nat.card F : ℚ)^2 := by
  classical
  try dsimp only [Instance.layer] at *
  have hn := system_not_full_of_high_defect I W d hdefect
  have he (coin : Coin F I.Equations I.nw I.nq I.s) :
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) =
        indicator (coin.2 ∈ Affine.consistent (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask d.1) := by
    rw [systemExceptions, dif_neg hn]
    congr 1
    exact propext (by simp only [mem_product, mem_univ, true_and])
  simp_rw [he]
  change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (coin.2 ∈ _)) ≤ _
  have hm := mean_snd (I := I.Equations → F) (fun B : Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1))
  exact hm.trans_le (systemConsistency_mean_le_inv_sq_of_defect I W d hdefect)

end RecursivePolygero.ProfileAnalysis

namespace RecursivePolygero.ProfileAnalysis.StoppedSpectrum

open Finset Bcs.StoppedPotential Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def lowDefectSpectrum (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (rate : ℚ) : ℚ :=
  ∑ d ∈ (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1),
    price rate (systemCap I W d)

/-- Low-defect systems pay their stopped spectrum in field units; all
higher-defect exceptions together cost at most `L/q^2`. -/
theorem weightedExceptions_repeatPrice_mean_le_defect_split
    (I : Instance F) (p : HahnSystemCertificate I) (hsmall : p.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (rate : ℚ) (hr : 0 < rate) :
    mean (fun coin => repeatPrice rate (weightedExceptions I p sigma W coin)) ≤
      lowDefectSpectrum I p W rate / Nat.card F + p.listBound / (Nat.card F : ℚ)^2 := by
  let S := highSystems I p W
  let low := fun d : systems I.domain I.primary_le W => systemDefect I W d ≤ 1
  have hraw : mean (fun coin => repeatPrice rate (weightedExceptions I p sigma W coin)) ≤
      ∑ d ∈ S, price rate (systemCap I W d) * mean (fun coin =>
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
    calc
      _ ≤ mean (fun coin => ∑ d ∈ S, price rate (systemCap I W d) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
        apply mean_mono
        intro coin
        exact repeatPrice_sum_indicator_le _ _ _ rate hr (fun d _ => by unfold systemCap; positivity)
      _ = _ := by
        rw [SystemException.mean_finset_sum]
        exact sum_congr rfl (fun d _ => mean_mul_left _ _)
  have hlow : (∑ d ∈ S.filter low, price rate (systemCap I W d) * mean (fun coin =>
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d))) ≤
      (∑ d ∈ S.filter low, price rate (systemCap I W d)) / Nat.card F := by
    calc
      _ ≤ ∑ d ∈ S.filter low, price rate (systemCap I W d) * (1 / Nat.card F) := by
        exact sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (systemExceptions_mean I p.toProfileParameters sigma W d)
          (price_nonneg _ _ hr (by unfold systemCap; positivity)))
      _ = _ := by rw [← sum_mul]; ring
  have hhigh : (∑ d ∈ S.filter (fun d => ¬low d), price rate (systemCap I W d) * mean (fun coin =>
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d))) ≤
      p.listBound / (Nat.card F : ℚ)^2 := by
    calc
      _ ≤ ∑ _d ∈ S.filter (fun d => ¬low d), (1 : ℚ) / (Nat.card F : ℚ)^2 := by
        apply sum_le_sum
        intro d hd
        have hd' : 2 ≤ systemDefect I W d := by have := (mem_filter.mp hd).2; dsimp [low] at this; omega
        calc
          _ ≤ price rate (systemCap I W d) * (1 / (Nat.card F : ℚ)^2) :=
            mul_le_mul_of_nonneg_left (systemExceptions_mean_le_inv_sq_of_defect I p.toProfileParameters
              sigma W d hd') (price_nonneg _ _ hr (by unfold systemCap; positivity))
          _ ≤ 1 * (1 / (Nat.card F : ℚ)^2) := mul_le_mul_of_nonneg_right
            (price_le_one _ _ hr (by unfold systemCap; positivity)) (by positivity)
          _ = _ := one_mul _
      _ = ((S.filter (fun d => ¬low d)).card : ℚ) / (Nat.card F : ℚ)^2 := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right
        (Nat.cast_le.mpr ((card_filter_le _ _).trans (highSystems_card_le I p hsmall W))) (by positivity)
  rw [← sum_filter_add_sum_filter_not S low] at hraw
  exact hraw.trans (add_le_add hlow hhigh)

theorem baseline_weightedExceptions_repeatPrice_mean_le_defect_split
    (I : Instance F) (p : HahnSystemCertificate I) (hsmall : p.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (rate baseline : ℚ) (hb : 0 ≤ baseline) (hbr : baseline < rate) :
    mean (fun coin => repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) ≤
      lowDefectSpectrum I p W (rate-baseline) / Nat.card F + p.listBound / (Nat.card F : ℚ)^2 := by
  calc
    _ ≤ mean (fun coin => repeatPrice (rate-baseline) (weightedExceptions I p sigma W coin)) := by
      apply mean_mono
      intro coin
      apply repeatPrice_baseline_le rate baseline _ hb hbr.le
      unfold weightedExceptions
      exact sum_nonneg (fun d _ => mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _))
    _ ≤ _ := weightedExceptions_repeatPrice_mean_le_defect_split I p hsmall sigma W _ (sub_pos.mpr hbr)

/-- Rank is paid once; the high-defect remainder is genuinely quadratic
in the field inverse. This directly supplies the existing ABS stopped
parent-query compiler's mean-price premise. -/
theorem conditionalCapacity_repeatPrice_mean_le_defect_split
    (I : Instance F) (p : HahnSystemCertificate I) (hsmall : p.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (rate baseline : ℚ) (hb : 0 ≤ baseline) (hbr : baseline < rate) :
    mean (fun coin => repeatPrice rate (conditionalCapacity I p sigma W baseline coin)) ≤
      p.toProfileParameters.rankError + lowDefectSpectrum I p W (rate-baseline) / Nat.card F +
        p.listBound / (Nat.card F : ℚ)^2 := by
  have hr : 0 < rate := hb.trans_lt hbr
  let bad := fun coin : I.layer.Coin => coin.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  calc
    _ ≤ mean (fun coin => indicator (bad coin) +
        repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) := by
      apply mean_mono
      intro coin
      change repeatPrice rate (if bad coin then 1 else
        baseline + weightedExceptions I p sigma W coin) ≤ indicator (bad coin) +
          repeatPrice rate (baseline + weightedExceptions I p sigma W coin)
      by_cases h : bad coin
      · have hone : repeatPrice rate 1 ≤ 1 :=
          (repeatPrice_le_price rate 1 hr (by norm_num)).trans
            (price_le_one rate 1 hr (by norm_num))
        simpa only [if_pos h, indicator, if_pos h] using
          hone.trans (le_add_of_nonneg_right (repeatPrice_nonneg rate
            (baseline + weightedExceptions I p sigma W coin)))
      · simp [h, indicator]
    _ = mean (fun coin => indicator (bad coin)) +
        mean (fun coin => repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) := mean_add _ _
    _ ≤ _ := by
      have h := add_le_add (rank_bad_mean I p.toProfileParameters W)
        (baseline_weightedExceptions_repeatPrice_mean_le_defect_split I p hsmall sigma W rate baseline hb hbr)
      exact h.trans_eq (by ring)

end RecursivePolygero.ProfileAnalysis.StoppedSpectrum
