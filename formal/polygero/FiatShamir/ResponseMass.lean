import polygero.Local.ResponseUniqueness
import polygero.Local.Probability
import polygero.Algebra.Counting.RestrictedExcess

/-! Response-uniform and summed high-response bounds for the concrete Polygero
verifier. These bounds include both transmitted polynomials. -/
noncomputable section
namespace RecursivePolygero.NonrecursiveFS
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting ProfileAnalysis
open PolynomialClosure Shift
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

abbrev code (I : Instance F) := primaryCode I.domain I.primary_le
abbrev words (I : Instance F) (W : I.layer.Oracle) := oracleWords W.ordinary
abbrev good (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) :=
  goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W c a

def fraction (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) : ℚ :=
  (responseCount I.layer σ W c a : ℚ) / Fintype.card I.layer.Query

def rankBad (I : Instance F) (W : I.layer.Oracle) (c : I.layer.Coin) : Prop :=
  c.2 ∈ ReducedSystems.badChallenges (code I) (words I W) W.proximityMask

def highBudget (I : Instance F) (p : HahnSystemCertificate I) : ℚ :=
  (1-p.threshold+((Nat.card F : ℚ)-1)*p.threshold)/(Nat.card F : ℚ)

omit [DecidableEq F] in
theorem highBudget_nonneg (I : Instance F) (p : HahnSystemCertificate I) : 0 ≤ highBudget I p := by
  have hq : (1 : ℚ) ≤ Nat.card F := by
    exact_mod_cast (show 1 ≤ Nat.card F from Nat.card_pos)
  unfold highBudget
  exact div_nonneg (add_nonneg (sub_nonneg.mpr p.threshold_lt_one.le)
    (mul_nonneg (sub_nonneg.mpr hq) p.threshold_nonneg)) (Nat.cast_nonneg _)

omit [Fintype F] [DecidableEq F] in
theorem error_gap (I : Instance F) (p : HahnSystemCertificate I) :
    (1-p.threshold)/(Nat.card F : ℚ) ≤ p.error-p.threshold := by
  have hmu : 0 ≤ p.rankError := by unfold ProfileParameters.rankError; positivity
  have hh := mul_nonneg (sub_nonneg.mpr p.threshold_lt_one.le) hmu
  unfold HahnSystemCertificate.error profile
  simp only [div_eq_mul_inv, one_mul]
  nlinarith

omit [Fintype F] [DecidableEq F] in
theorem threshold_le_error (I : Instance F) (p : HahnSystemCertificate I) : p.threshold ≤ p.error := by
  have := error_gap I p
  have : 0 ≤ (1-p.threshold)/(Nat.card F : ℚ) :=
    div_nonneg (sub_nonneg.mpr p.threshold_lt_one.le) (Nat.cast_nonneg _)
  linarith

theorem query_mean (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) :
    mean (fun Q => indicator (I.layer.verify σ W c a Q)) = fraction I σ W c a := by
  rw [mean_indicator]
  rfl

def failureFraction (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) : ℚ :=
  if scanRecoverAt I σ W c a = none then fraction I σ W c a else 0

/-- Extraction failure, including for a satisfiable backend statement. -/
theorem extraction_failure_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (response : I.layer.Coin → I.layer.Payload) :
    mean (fun c => failureFraction I σ W c (response c)) ≤ p.error := by
  have hlocal (c : I.layer.Coin) : failureFraction I σ W c (response c) ≤
      localEnvelope I p.toProfileParameters σ W p.threshold (fun _ => False) c := by
    by_cases hn : scanRecoverAt I σ W c (response c) = none
    · simpa only [failureFraction, fraction, if_pos hn] using
        (response_fraction_le_envelope I p.toProfileParameters σ W p.threshold
        p.columnFloor_le p.threshold_lt_one.le (fun _ => False) c (response c)
        (by simp [hn, outputHit]))
    · simpa only [failureFraction, if_neg hn] using
        (localEnvelope_bounds I p.toProfileParameters σ W p.threshold p.threshold_nonneg
          p.threshold_lt_one.le (fun _ => False) c).1
  have hmean := localEnvelope_mean_of_hahn (Z := Unit) I p (fun _ => σ) W 0
    (by norm_num) (by norm_num) (fun _ _ => False) (by intro g; simp [indicator])
  exact (mean_mono hlocal).trans (by simpa using hmean)

theorem response_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (hfalse : ∀ w, ¬ I.layer.satisfies σ w) (response : I.layer.Coin → I.layer.Payload) :
    mean (fun c => fraction I σ W c (response c)) ≤ p.error := by
  have hnone c : scanRecoverAt I σ W c (response c) = none := by
    cases he : scanRecoverAt I σ W c (response c) with
    | none => rfl
    | some g => exact (hfalse _ (scanRecoverAt_valid I σ W c (response c) g he)).elim
  have hlocal := mean_mono fun c => response_fraction_le_envelope I p.toProfileParameters
    σ W p.threshold p.columnFloor_le p.threshold_lt_one.le (fun _ => False) c (response c)
      (by simp [hnone, outputHit])
  have hmean := localEnvelope_mean_of_hahn (Z := Unit) I p (fun _ => σ) W 0
    (by norm_num) (by norm_num) (fun _ _ => False) (by intro g; simp [indicator])
  simpa only [fraction] using hlocal.trans (by simpa using hmean)

theorem fraction_le_columns (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) :
    fraction I σ W c a ≤ ((good I σ W c a).card.choose I.t : ℚ) / I.n.choose I.t := by
  have h := div_le_div_of_nonneg_right
    (show (responseCount I.layer σ W c a : ℚ) ≤ (good I σ W c a).card.choose I.t from by
      exact_mod_cast responseCount_le_columns I σ W c a) (show (0 : ℚ) ≤ Fintype.card I.layer.Query by positivity)
  simpa only [fraction, show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] using h

theorem global_of_fraction (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) (hpos : 0 < fraction I σ W c a) :
    globalCheck I.domain I.layout σ c.1 a := by
  have hn : (univ.filter (I.layer.verify σ W c a)).Nonempty := by
    apply card_pos.mp
    unfold fraction responseCount at hpos
    have := (div_pos_iff.mp hpos)
    rcases this with h | h
    · exact_mod_cast h.1
    · exact (not_lt_of_ge (Nat.cast_nonneg _) h.1).elim
  obtain ⟨Q,hQ⟩ := hn
  exact ((verify_openOracle_iff I.domain (by have := I.primary_le; omega) I.primary_le
    I.layout σ W c a Q).mp (mem_filter.mp hQ).2).1

private theorem primary_consistent (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (c : I.layer.Coin) (a : I.layer.Payload) :
    (c.2,a.primary) ∈ ConsistencyClosure.solutions (jointMap (code I) (words I W))
      W.proximityMask (good I σ W c a) := by
  intro j hj
  exact sub_eq_iff_eq_add.mpr (((mem_filter.mp hj).2).1.trans (add_comm _ _))

private theorem large_assignment (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (hb : ¬ rankBad I W c) (a : I.layer.Payload)
    (hnone : scanRecoverAt I σ W c a = none)
    (hglobal : globalCheck I.domain I.layout σ c.1 a)
    (hg : p.largeSize ≤ (good I σ W c a).card) :
    ∃ d : systems I.domain I.primary_le W,
      (c.2,a.primary) ∈ ConsistencyClosure.solutions (jointMap (code I) (words I W)) W.proximityMask d.1 ∧
      fixedConsistencyCodimension (code I) (words I W) d.1 I.s +
        ((good I σ W c a) \ d.1).card ≤ I.s ∧
      fraction I σ W c a ≤ systemCap I W d ∧ c ∈ systemExceptions p.positive_degree I.layout σ d := by
  have hc : I.r+I.w+I.s+I.s+1 ≤ (good I σ W c a).card := (le_max_left _ _).trans hg
  have hp := primary_consistent I σ W c a
  have hl := ReducedSystems.low_defect_of_not_bad (code I) (words I W) W.proximityMask
    c.2 hb (good I σ W c a) hc a.primary hp
  obtain ⟨D,hD,hpD,hbudget,hcap⟩ := ReducedSystems.assign
    (code I) (words I W) W.proximityMask (good I σ W c a) hc hl (c.2,a.primary) hp
  let d : systems I.domain I.primary_le W := ⟨D,hD⟩
  refine ⟨d,hpD,?_,?_,?_⟩
  · change fixedConsistencyCodimension (code I) (words I W) D I.s + ((good I σ W c a) \ D).card ≤ I.s
    omega
  · apply (fraction_le_columns I σ W c a).trans
    unfold systemCap
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose I.t hcap) (by positivity)
  · by_cases he : c ∈ systemExceptions p.positive_degree I.layout σ d
    · exact he
    · obtain ⟨hfull,hsome⟩ := recover_of_assigned_system I p.positive_degree σ W d c a hpD
        he hglobal (by simpa only [ProfileParameters.largeSize, ProfileParameters.coreSize,
          good, two_mul, Nat.add_assoc] using hg) (by
          change ((good I σ W c a) \ D).card ≤ I.s
          omega)
      rw [hnone] at hsome
      cases hsome

private theorem large_of_fraction (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (c : I.layer.Coin) (a : I.layer.Payload)
    (ha : p.error < fraction I σ W c a) : p.largeSize ≤ (good I σ W c a).card := by
  by_cases hlarge : p.largeSize ≤ (good I σ W c a).card
  · exact hlarge
  · have hg : (good I σ W c a).card ≤ p.largeSize-1 := by omega
    have hh := div_le_div_of_nonneg_right
      (show ((good I σ W c a).card.choose I.t : ℚ) ≤ ((p.largeSize-1).choose I.t : ℚ) from by
        exact_mod_cast Nat.choose_le_choose I.t hg) (show (0 : ℚ) ≤ I.n.choose I.t by positivity)
    exact (not_lt_of_ge ((fraction_le_columns I σ W c a).trans
      (hh.trans (p.columnFloor_le.trans (threshold_le_error I p)))) ha).elim

private theorem high_assignment (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin)
    (fails : I.layer.Payload → Prop)
    (hnone : ∀ a, fails a → scanRecoverAt I σ W c a = none)
    (hb : ¬ rankBad I W c) :
    ∃ label : ↥(univ.filter fun a : I.layer.Payload => fails a ∧ p.error < fraction I σ W c a) →
        systems I.domain I.primary_le W,
      Function.Injective label ∧ ∀ a : ↥(univ.filter fun a : I.layer.Payload => fails a ∧ p.error < fraction I σ W c a),
        fraction I σ W c a ≤ systemCap I W (label a) ∧
          c ∈ systemExceptions p.positive_degree I.layout σ (label a) := by
  let S := univ.filter fun a : I.layer.Payload => fails a ∧ p.error < fraction I σ W c a
  have hg (a : ↥S) := large_of_fraction I p σ W c a (mem_filter.mp a.2).2.2
  have hass (a : ↥S) := large_assignment I p.toProfileParameters σ W c hb a
    (hnone a (mem_filter.mp a.2).2.1)
    (global_of_fraction I σ W c a (p.error_nonneg.trans_lt (mem_filter.mp a.2).2.2)) (hg a)
  choose label hlabel using hass
  have hinj : Function.Injective label := by
    intro a b hab
    apply Subtype.ext
    have ha := hlabel a
    have hb := hlabel b
    rw [← hab] at hb
    apply response_eq_of_assigned_system I p.toProfileParameters σ W (label a) c a.1 b.1 ha.1 hb.1
    · intro payload hp
      rcases mem_insert.mp hp with he | he
      · subst payload; exact hg a
      · rw [mem_singleton.mp he]; exact hg b
    · intro payload hp
      rcases mem_insert.mp hp with he | he
      · simpa only [he] using ha.2.1
      · simpa only [mem_singleton.mp he] using hb.2.1
  exact ⟨label,hinj,fun a => (hlabel a).2.2⟩

private theorem high_mass_le_systems (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (fails : I.layer.Payload → Prop)
    (hnone : ∀ a, fails a → scanRecoverAt I σ W c a = none) (hb : ¬ rankBad I W c) :
    (∑ a : I.layer.Payload, if fails a ∧ p.error < fraction I σ W c a then fraction I σ W c a else 0) ≤
      ∑ d : systems I.domain I.primary_le W,
        indicator (c ∈ systemExceptions p.positive_degree I.layout σ d) *
          (if p.error < systemCap I W d then systemCap I W d else 0) := by
  let S := univ.filter fun a : I.layer.Payload => fails a ∧ p.error < fraction I σ W c a
  obtain ⟨label,hinj,hlabel⟩ := high_assignment I p σ W c fails hnone hb
  let weight := fun d : systems I.domain I.primary_le W =>
    indicator (c ∈ systemExceptions p.positive_degree I.layout σ d) *
      (if p.error < systemCap I W d then systemCap I W d else 0)
  have hw d : 0 ≤ weight d := by
    apply mul_nonneg (indicator_nonneg _)
    split_ifs
    · unfold systemCap; positivity
    · exact le_rfl
  have hp (a : ↥S) : fraction I σ W c a ≤ weight (label a) := by
    have ha := hlabel a
    have hc := ((mem_filter.mp a.2).2.2).trans_le ha.1
    simpa only [weight,indicator,if_pos ha.2,if_pos hc,one_mul] using ha.1
  have heq : (∑ a : I.layer.Payload, if fails a ∧ p.error < fraction I σ W c a
      then fraction I σ W c a else 0) = ∑ a : ↥S, fraction I σ W c a := by
    rw [← sum_filter]
    exact sum_subtype S (fun _ => Iff.rfl) (fraction I σ W c)
  rw [heq]
  calc
    _ ≤ ∑ a : ↥S, weight (label a) := sum_le_sum (fun a _ => hp a)
    _ = ∑ d ∈ univ.image label, weight d := (sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ d, weight d := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun d _ _ => hw d)

private theorem system_high_mass (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) :
    (∑ d : systems I.domain I.primary_le W,
      if p.error < systemCap I W d then systemCap I W d else 0) ≤
      1-p.threshold+((Nat.card F : ℚ)-1)*p.threshold := by
  have hq : (0 : ℚ) < Nat.card F := by exact_mod_cast Nat.card_pos (α := F)
  rw [← sum_filter]
  apply RestrictedExcess.high_mass_of_restricted _ (Nat.card F) (Nat.card_pos (α := F))
    p.threshold p.error p.threshold_nonneg (threshold_le_error I p)
  · have hh := (div_le_iff₀ hq).mp (error_gap I p)
    simpa only [mul_comm] using hh
  · exact systemCap_excess_of_hahn I p W

private theorem high_mass_mean_of_failure (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (fails : I.layer.Coin → I.layer.Payload → Prop)
    (hnone : ∀ c a, fails c a → scanRecoverAt I σ W c a = none) :
    mean (fun c : I.layer.Coin => if rankBad I W c then (0 : ℚ) else
      ∑ a : I.layer.Payload, if fails c a ∧ p.error < fraction I σ W c a then fraction I σ W c a else 0) ≤
      highBudget I p := by
  let high := fun d : systems I.domain I.primary_le W =>
    if p.error < systemCap I W d then systemCap I W d else 0
  have hn d : 0 ≤ high d := by
    dsimp [high]
    split_ifs
    · unfold systemCap; positivity
    · exact le_rfl
  have hp (c : I.layer.Coin) :
      (if rankBad I W c then (0 : ℚ) else ∑ a : I.layer.Payload,
        if fails c a ∧ p.error < fraction I σ W c a then fraction I σ W c a else 0) ≤
        ∑ d, indicator (c ∈ systemExceptions p.positive_degree I.layout σ d)*high d := by
    split_ifs with hb
    · exact sum_nonneg (fun d _ => mul_nonneg (indicator_nonneg _) (hn d))
    · exact high_mass_le_systems I p σ W c (fails c) (hnone c) hb
  calc
    _ ≤ mean (fun c : I.layer.Coin => ∑ d,
        indicator (c ∈ systemExceptions p.positive_degree I.layout σ d)*high d) := mean_mono hp
    _ = ∑ d, mean (fun c : I.layer.Coin =>
        indicator (c ∈ systemExceptions p.positive_degree I.layout σ d)*high d) :=
      SystemException.mean_finset_sum univ _
    _ = ∑ d, mean (fun c : I.layer.Coin =>
        indicator (c ∈ systemExceptions p.positive_degree I.layout σ d))*high d := by
      apply sum_congr rfl
      intro d _
      simpa only [mul_comm] using mean_mul_left (high d)
        (fun c : I.layer.Coin => indicator (c ∈ systemExceptions p.positive_degree I.layout σ d))
    _ ≤ ∑ d, (1/(Nat.card F : ℚ))*high d := sum_le_sum (fun d _ =>
      mul_le_mul_of_nonneg_right (systemExceptions_mean I p.toProfileParameters σ W d) (hn d))
    _ = (1/(Nat.card F : ℚ))*∑ d, high d := (mul_sum ..).symm
    _ ≤ (1/(Nat.card F : ℚ))*(1-p.threshold+((Nat.card F : ℚ)-1)*p.threshold) :=
      mul_le_mul_of_nonneg_left (system_high_mass I p W) (by positivity)
    _ = _ := by unfold highBudget; ring

/-- The total mass of high-acceptance responses whose row extraction fails.
The backend statement may be satisfiable. -/
theorem extraction_high_mass_mean (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun c : I.layer.Coin => if rankBad I W c then (0 : ℚ) else
      ∑ a : I.layer.Payload, if scanRecoverAt I σ W c a = none ∧ p.error < fraction I σ W c a
        then fraction I σ W c a else 0) ≤ highBudget I p := by
  convert! high_mass_mean_of_failure I p σ W (fun c a => scanRecoverAt I σ W c a = none)
    (fun _ _ h => h) using 1
  apply mean_congr
  intro c
  by_cases hb : rankBad I W c
  · simp only [if_pos hb]
  · simp only [if_neg hb]
    apply sum_congr rfl
    intro a _
    split_ifs <;> rfl

/-- The total mass of all high-acceptance complete responses, outside the
shared rank event. The response may depend on the first challenge. -/
theorem high_mass_mean (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (hfalse : ∀ w, ¬ I.layer.satisfies σ w) :
    mean (fun c : I.layer.Coin => if rankBad I W c then (0 : ℚ) else
      ∑ a : I.layer.Payload, if p.error < fraction I σ W c a then fraction I σ W c a else 0) ≤
      highBudget I p := by
  have hn c a (_ : True) : scanRecoverAt I σ W c a = none := by
    cases he : scanRecoverAt I σ W c a with
    | none => rfl
    | some g => exact (hfalse _ (scanRecoverAt_valid I σ W c a g he)).elim
  simpa only [true_and] using high_mass_mean_of_failure I p σ W (fun _ _ => True) hn

end RecursivePolygero.NonrecursiveFS
