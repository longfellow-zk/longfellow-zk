import polygero.Local.CoreOnlyCapacity
import polygero.Local.CapacityConsumption
import polygero.Local.BaselineAwarePrice

/-! Actual core capacities, with the omitted columns charged separately.
Full systems use different arithmetic and polynomial challenge coordinates;
proper systems pay the increased affine consistency codimension directly.
The payload union allows choices after the query; no independence of
adaptive child commitments is assumed. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode decodedLinearResidual decodedZRMaskSum)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem system_full_of_defect_zero (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (hz : systemDefect I W d = 0) :
    Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ := by
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  obtain ⟨⟨B,p⟩,hp⟩ := (geometry d).nonempty
  have hne : (Affine.consistent C rows W.proximityMask d.1).Nonempty :=
    ⟨B,mem_filter.mpr ⟨mem_univ _,
      (PolynomialClosure.exists_joint_iff C rows W.proximityMask d.1 B).mp ⟨p,hp⟩⟩⟩
  have hd := fixedConsistencyDimension_add_codimension C rows d.1 (s := I.s)
  change fixedConsistencyDimension C rows d.1 I.s + systemDefect I W d = _ at hd
  rw [hz,add_zero] at hd
  apply eq_univ_of_card
  rw [Affine.consistent_card_eq_of_nonempty C rows W.proximityMask d.1 hne,hd]
  simpa only [Nat.card_eq_fintype_card] using
    (card_challenge_eq_field_pow (F := F) (m := rowCount I.nw I.nq) (s := I.s)).symm

theorem outside_column_consistency_mean_le_inv (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (j : Fin I.n) (hj : j ∉ d.1) :
    mean (fun B => indicator (B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask (insert j d.1))) ≤ 1/(Nat.card F : ℚ) := by
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  change mean (fun B => indicator (B ∈ Affine.consistent C rows W.proximityMask
    (insert j d.1))) ≤ 1/(Nat.card F : ℚ)
  by_cases hne : (Affine.consistent C rows W.proximityMask (insert j d.1)).Nonempty
  · obtain ⟨B,hB⟩ := hne
    obtain ⟨p,hp⟩ := (PolynomialClosure.exists_joint_iff C rows W.proximityMask (insert j d.1) B).mpr
      (mem_filter.mp hB).2
    have hd := outside_column_defect_lt I W d j hj ⟨(B,p),hp⟩
    change systemDefect I W d < fixedConsistencyCodimension C rows (insert j d.1) I.s at hd
    have hdim := fixedConsistencyDimension_add_codimension C rows (insert j d.1) (s := I.s)
    have hc := Affine.consistent_card_mul_field_pow_le C rows W.proximityMask (insert j d.1) 0
      (by omega)
    rw [mean_indicator]
    simp only [filter_mem_eq_inter,univ_inter]
    apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos)
      (by exact_mod_cast Nat.card_pos (α := F))).mpr
    simpa only [one_mul,pow_one,Nat.zero_add,Nat.card_eq_fintype_card,Nat.cast_mul] using
      (Nat.cast_le (α := ℚ)).mpr hc
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp [he,indicator]

theorem outsidePrimary_mean_le_inv (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) :
    mean (fun B => indicator (outsidePrimary I W d B)) ≤ I.n/(Nat.card F : ℚ) := by
  have hi (B : Challenge F (rowCount I.nw I.nq) I.s) :
      indicator (outsidePrimary I W d B) ≤
        ∑ j : Fin I.n, indicator (j ∉ d.1 ∧ B ∈ Affine.consistent
          (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (insert j d.1)) := by
    by_cases h : outsidePrimary I W d B
    · obtain ⟨j,hj,hB⟩ := h
      have hs := single_le_sum (fun i (_ : i ∈ univ) => indicator_nonneg
        (i ∉ d.1 ∧ B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask (insert i d.1))) (mem_univ j)
      simpa only [indicator,if_pos (show outsidePrimary I W d B from ⟨j,hj,hB⟩),
        if_pos (show j ∉ d.1 ∧ B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask (insert j d.1) from ⟨hj,hB⟩)] using hs
    · simp only [indicator,if_neg h]
      exact sum_nonneg fun _ _ => indicator_nonneg _
  calc
    _ ≤ _ := mean_mono hi
    _ = ∑ j : Fin I.n, mean (fun B => indicator (j ∉ d.1 ∧ B ∈ Affine.consistent
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (insert j d.1))) :=
      SystemException.mean_finset_sum _ _
    _ ≤ ∑ _j : Fin I.n, (1 : ℚ)/Nat.card F := by
      apply sum_le_sum
      intro j _
      by_cases hj : j ∈ d.1
      · simpa only [hj,not_true_eq_false,false_and,indicator,if_false,mean_const] using
          (by positivity : (0 : ℚ) ≤ 1/Nat.card F)
      · simpa only [hj,not_false_eq_true,true_and] using
          outside_column_consistency_mean_le_inv I W d j hj
    _ = _ := by simp [div_eq_mul_inv]

/-- Even a full system pays two field conditions when an exceptional
accepting payload extends outside its canonical core. -/
theorem exception_outside_mean_le (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (d : systems I.domain I.primary_le W) :
    mean (fun coin : I.layer.Coin => indicator
      (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
        outsidePrimary I W d coin.2)) ≤ I.n/(Nat.card F : ℚ)^2 := by
  change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
      outsidePrimary I W d coin.2)) ≤ _
  by_cases hfull : Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ
  · let residual := decodedLinearResidual I.domain I.layout σ
      (extendRows (rows p.positive_degree d hfull))
    by_cases hz : residual = 0
    · have hz' : decodedLinearResidual I.domain I.layout σ
        (extendRows (rows p.positive_degree d hfull)) = 0 := hz
      simp [systemExceptions,hfull,hz',indicator]
      positivity
    · let E := affineEquationSolutions residual
        (-decodedZRMaskSum I.domain I.layout (extendRows (rows p.positive_degree d hfull)))
      have he (coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s) :
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
            outsidePrimary I W d coin.2) =
          indicator (coin.1 ∈ E) * indicator (outsidePrimary I W d coin.2) := by
        unfold systemExceptions
        rw [dif_pos hfull]
        change indicator (coin ∈ (if residual = 0 then ∅ else E ×ˢ univ) ∧ _) = _
        rw [if_neg hz]
        simp only [mem_product,mem_univ,and_true]
        unfold indicator
        split_ifs <;> simp_all
      simp_rw [he]
      change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s => _) ≤ _
      rw [mean_prod]
      simp_rw [mean_mul_left]
      have hex : mean (fun a : I.Equations → F => indicator (a ∈ E)) ≤ 1/(Nat.card F : ℚ) := by
        have hsys := systemExceptions_mean I p σ W d
        change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤ _ at hsys
        unfold systemExceptions at hsys
        rw [dif_pos hfull] at hsys
        change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
          indicator (coin ∈ (if residual = 0 then ∅ else E ×ˢ univ))) ≤ _ at hsys
        rw [if_neg hz] at hsys
        simp only [mem_product,mem_univ,and_true] at hsys
        change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s => _) ≤ _ at hsys
        simpa only [mean_prod,mean_const] using hsys
      have hout := outsidePrimary_mean_le_inv I W d
      have heq : mean (fun a : I.Equations → F => indicator (a ∈ E) *
          mean (fun B => indicator (outsidePrimary I W d B))) =
          mean (fun a : I.Equations → F => indicator (a ∈ E)) *
          mean (fun B => indicator (outsidePrimary I W d B)) := by
        rw [show (fun a : I.Equations → F => indicator (a ∈ E) *
          mean (fun B => indicator (outsidePrimary I W d B))) =
          (fun a => mean (fun B => indicator (outsidePrimary I W d B)) * indicator (a ∈ E))
          from funext (fun _ => mul_comm _ _),mean_mul_left,mul_comm]
      rw [heq]
      have hout0 : 0 ≤ mean (fun B => indicator (outsidePrimary I W d B)) := by
        exact div_nonneg (sum_nonneg fun _ _ => indicator_nonneg _) (Nat.cast_nonneg _)
      calc
        _ ≤ (1/(Nat.card F : ℚ)) * (I.n/(Nat.card F : ℚ)) :=
          mul_le_mul hex hout hout0 (by positivity)
        _ = _ := by ring
  · have hd : 1 ≤ systemDefect I W d := by
      by_contra hn
      exact hfull (system_full_of_defect_zero I W d (by omega))
    refine (mean_mono (fun _ => indicator_mono And.right)).trans ?_
    change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
      indicator (outsidePrimary I W d coin.2)) ≤ _
    rw [mean_prod]
    simp only [mean_const]
    exact outsidePrimary_mean_le I W d hd

noncomputable def refinedSystemCap (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (coin : I.layer.Coin) : ℚ :=
  min (systemCap I W d) (if outsidePrimary I W d coin.2 then 1 else coreCapacity I W d)

theorem refinedSystemCap_nonneg (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (coin : I.layer.Coin) :
    0 ≤ refinedSystemCap I W d coin := by
  apply le_min (by unfold systemCap; positivity)
  split_ifs
  · norm_num
  · unfold coreCapacity; positivity

theorem assigned_query_union_mean_le_refined (I : Instance F) (hk : 1 ≤ I.r+I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (d : systems I.domain I.primary_le W) :
    mean (fun q : I.layer.Query => indicator (∃ u : I.layer.Payload,
      ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q)) ≤
        refinedSystemCap I W d coin := by
  apply le_min (assigned_query_union_mean_le I hk σ W coin hout d)
  by_cases h : outsidePrimary I W d coin.2
  · rw [if_pos h]
    apply mean_le
    intro q
    unfold indicator
    split_ifs <;> norm_num
  · rw [if_neg h]
    exact assigned_query_union_mean_le_core I σ W coin d h

noncomputable def refinedWeightedExceptions (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) : ℚ :=
  ∑ d ∈ highSystems I p W, refinedSystemCap I W d coin *
    indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)

theorem refinedWeightedExceptions_nonneg (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) :
    0 ≤ refinedWeightedExceptions I p σ W coin :=
  sum_nonneg fun d _ => mul_nonneg (refinedSystemCap_nonneg I W d coin) (indicator_nonneg _)

theorem refinedWeightedExceptions_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) :
    refinedWeightedExceptions I p σ W coin ≤ weightedExceptions I p σ W coin := by
  apply sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (indicator_nonneg _)

theorem assignedExceptionQuery_refined_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) :
    mean (fun q => indicator (assignedExceptionQuery I p σ W coin q)) ≤
      refinedWeightedExceptions I p σ W coin := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · simp only [assignedExceptionQuery,hb,not_true_eq_false,false_and,indicator,if_false,mean_const]
    exact refinedWeightedExceptions_nonneg I p σ W coin
  let event := fun d q => ∃ u : I.layer.Payload,
    ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q
  have hi (q : I.layer.Query) : indicator (assignedExceptionQuery I p σ W coin q) ≤
      ∑ d ∈ highSystems I p W, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) *
        indicator (event d q) := by
    by_cases he : assignedExceptionQuery I p σ W coin q
    · obtain ⟨_,d,hd,hx,hu⟩ := he
      have hs := single_le_sum (fun d (_ : d ∈ highSystems I p W) =>
        mul_nonneg (indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
          (indicator_nonneg (event d q))) hd
      have hu' : event d q := hu
      simpa only [indicator,if_pos hx,if_pos hu',mul_one,
        if_pos (show assignedExceptionQuery I p σ W coin q from ⟨hb,d,hd,hx,hu⟩)] using hs
    · simpa only [indicator,if_neg he] using sum_nonneg
        (s := highSystems I p W) (fun d _ =>
          mul_nonneg (indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
            (indicator_nonneg (event d q)))
  calc
    _ ≤ _ := mean_mono hi
    _ = ∑ d ∈ highSystems I p W, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) *
        mean (fun q => indicator (event d q)) := by
      rw [SystemException.mean_finset_sum]
      exact sum_congr rfl (fun _ _ => mean_mul_left _ _)
    _ ≤ _ := by
      apply sum_le_sum
      intro d _
      rw [mul_comm (refinedSystemCap I W d coin)]
      exact mul_le_mul_of_nonneg_left
        (assigned_query_union_mean_le_refined I p.positive_degree σ W coin hb d) (indicator_nonneg _)

noncomputable def refinedConditionalCapacity (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (baseline : ℚ) (coin : I.layer.Coin) : ℚ :=
  if coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask then 1
  else baseline+refinedWeightedExceptions I p σ W coin

theorem refinedConditionalCapacity_nonneg (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (baseline : ℚ) (hb : 0 ≤ baseline)
    (coin : I.layer.Coin) : 0 ≤ refinedConditionalCapacity I p σ W baseline coin := by
  unfold refinedConditionalCapacity
  split_ifs
  · norm_num
  · exact add_nonneg hb (refinedWeightedExceptions_nonneg I p σ W coin)

theorem refinedConditionalCapacity_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (baseline : ℚ) (coin : I.layer.Coin) :
    refinedConditionalCapacity I p σ W baseline coin ≤
      StoppedSpectrum.conditionalCapacity I p σ W baseline coin := by
  unfold refinedConditionalCapacity StoppedSpectrum.conditionalCapacity
  split_ifs
  · rfl
  · exact add_le_add_right (refinedWeightedExceptions_le I p σ W coin) baseline

end RecursivePolygero.ProfileAnalysis

namespace RecursivePolygero.ProfileAnalysis.StoppedSpectrum
open Finset Bcs.StoppedPotential Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def coreSpectrum (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (effective : ℚ) : ℚ :=
  ∑ d ∈ (highSystems I p W).filter (fun d => systemDefect I W d ≤ 1),
    price effective (coreCapacity I W d)

theorem refinedSystemCap_price_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (d : systems I.domain I.primary_le W)
    (effective : ℚ) (he : 0 < effective) :
    mean (fun coin => price effective (refinedSystemCap I W d coin) *
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
      price effective (coreCapacity I W d)/Nat.card F+I.n/(Nat.card F : ℚ)^2 := by
  have hc : 0 ≤ coreCapacity I W d := by unfold coreCapacity; positivity
  have hp (coin : I.layer.Coin) : price effective (refinedSystemCap I W d coin) *
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) ≤
      price effective (coreCapacity I W d) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) +
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧ outsidePrimary I W d coin.2) := by
    by_cases hx : coin ∈ systemExceptions p.positive_degree I.layout σ d
    · by_cases ho : outsidePrimary I W d coin.2
      · simp only [indicator,if_pos hx,if_pos (show _ ∧ _ from ⟨hx,ho⟩),mul_one]
        exact (price_le_one _ _ he (refinedSystemCap_nonneg I W d coin)).trans
          (le_add_of_nonneg_left (price_nonneg _ _ he hc))
      · simp only [indicator,if_pos hx,if_neg (show ¬(_ ∧ _) from fun h => ho h.2),mul_one,add_zero]
        exact price_mono _ _ _ he (refinedSystemCap_nonneg I W d coin)
          (by unfold refinedSystemCap; rw [if_neg ho]; exact min_le_right _ _)
    · simp [indicator,hx]
  calc
    _ ≤ _ := mean_mono hp
    _ = price effective (coreCapacity I W d) * mean (fun coin : I.layer.Coin =>
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) +
        mean (fun coin : I.layer.Coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
          outsidePrimary I W d coin.2)) := by rw [mean_add,mean_mul_left]
    _ ≤ _ := by
      have h := add_le_add (mul_le_mul_of_nonneg_left
        (systemExceptions_mean I p.toProfileParameters σ W d) (price_nonneg _ _ he hc))
        (exception_outside_mean_le I p.toProfileParameters σ W d)
      simpa only [mul_one_div] using h

theorem refinedWeighted_price_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (effective : ℚ) (he : 0 < effective) :
    mean (fun coin => price effective (refinedWeightedExceptions I p σ W coin)) ≤
      coreSpectrum I p W effective/Nat.card F + p.listBound*I.n/(Nat.card F : ℚ)^2 := by
  let S := highSystems I p W
  let f := fun d : systems I.domain I.primary_le W =>
    if systemDefect I W d ≤ 1 then price effective (coreCapacity I W d) else 0
  have hraw : mean (fun coin => price effective (refinedWeightedExceptions I p σ W coin)) ≤
      ∑ d ∈ S, mean (fun coin => price effective (refinedSystemCap I W d coin) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
    calc
      _ ≤ mean (fun coin => ∑ d ∈ S, price effective (refinedSystemCap I W d coin) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
        apply mean_mono
        intro coin
        exact (price_sum_le S _ effective he (fun d _ =>
          mul_nonneg (refinedSystemCap_nonneg I W d coin) (indicator_nonneg _))).trans_eq
            (sum_congr rfl (fun _ _ => price_indicator _ _ he _))
      _ = _ := SystemException.mean_finset_sum _ _
  have hsingle (d : systems I.domain I.primary_le W) :
      mean (fun coin => price effective (refinedSystemCap I W d coin) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
        f d/Nat.card F+I.n/(Nat.card F : ℚ)^2 := by
    by_cases hd : systemDefect I W d ≤ 1
    · simpa only [f,if_pos hd] using refinedSystemCap_price_mean_le I p σ W d effective he
    · have hm : mean (fun coin => price effective (refinedSystemCap I W d coin) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
          mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
        apply mean_mono
        intro coin
        exact (mul_le_mul_of_nonneg_right (price_le_one _ _ he
          (refinedSystemCap_nonneg I W d coin)) (indicator_nonneg _)).trans_eq (one_mul _)
      have hn : 1 ≤ I.n := p.positive_degree.trans (by have := I.primary_le; omega)
      have hm' := hm.trans (systemExceptions_mean_le_inv_sq_of_defect I p.toProfileParameters σ W d (by omega))
      simpa only [f,if_neg hd,zero_div,zero_add] using hm'.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) (by positivity))
  have hsum : (∑ d ∈ S, f d) = coreSpectrum I p W effective := by
    simp only [f,coreSpectrum,sum_filter,S]
  have hcard : (S.card : ℚ) ≤ p.listBound := Nat.cast_le.mpr (highSystems_card_le I p hsmall W)
  calc
    _ ≤ ∑ d ∈ S, (f d/Nat.card F+I.n/(Nat.card F : ℚ)^2) := hraw.trans (sum_le_sum fun d _ => hsingle d)
    _ = coreSpectrum I p W effective/Nat.card F + S.card*(I.n/(Nat.card F : ℚ)^2) := by
      rw [sum_add_distrib,← sum_div,hsum]
      simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ (I.n : ℚ)/(Nat.card F : ℚ)^2 by positivity)
      exact (add_le_add_right hh _).trans_eq (by ring)

theorem refinedConditional_repeatPrice_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (rate baseline effective : ℚ) (hb : 0 ≤ baseline) (he : 0 < effective)
    (hdisc : (baseline+4*effective)^2 ≤ 16*effective*rate)
    (hbranch : baseline+2*effective ≤ 2*rate) :
    mean (fun coin => repeatPrice rate (refinedConditionalCapacity I p σ W baseline coin)) ≤
      p.toProfileParameters.rankError+coreSpectrum I p W effective/Nat.card F+
        p.listBound*I.n/(Nat.card F : ℚ)^2 := by
  have hr : 0 < rate := by linarith
  let bad := fun coin : I.layer.Coin => coin.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  have hp (coin : I.layer.Coin) : repeatPrice rate (refinedConditionalCapacity I p σ W baseline coin) ≤
      indicator (bad coin)+price effective (refinedWeightedExceptions I p σ W coin) := by
    by_cases h : bad coin
    · change repeatPrice rate (if bad coin then 1 else _) ≤ _
      rw [if_pos h,show indicator (bad coin) = 1 from if_pos h]
      exact ((repeatPrice_le_price rate 1 hr (by norm_num)).trans (price_le_one rate 1 hr (by norm_num))).trans
        (le_add_of_nonneg_right (price_nonneg _ _ he (refinedWeightedExceptions_nonneg I p σ W coin)))
    · change repeatPrice rate (if bad coin then 1 else _) ≤ _
      simpa only [if_neg h,indicator,if_neg h,zero_add] using
        repeatPrice_baseline_le_effective rate baseline effective _ hb
          (refinedWeightedExceptions_nonneg I p σ W coin) he hdisc hbranch
  calc
    _ ≤ mean (fun coin => indicator (bad coin)) +
        mean (fun coin => price effective (refinedWeightedExceptions I p σ W coin)) := by
      simpa only [mean_add] using mean_mono hp
    _ ≤ p.toProfileParameters.rankError +
        (coreSpectrum I p W effective/Nat.card F+p.listBound*I.n/(Nat.card F : ℚ)^2) :=
      add_le_add (rank_bad_mean I p.toProfileParameters W)
        (refinedWeighted_price_mean_le I p hsmall σ W effective he)
    _ = _ := by ring

end RecursivePolygero.ProfileAnalysis.StoppedSpectrum
