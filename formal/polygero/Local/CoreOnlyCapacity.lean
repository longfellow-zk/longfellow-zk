import polygero.Local.DefectPacking

/-! A canonical closure's omitted columns require extra affine rank.
For proper systems, any one agreeing outside column pays a second field
condition. This is a local refinement, not yet a new complete FS rate. -/
set_option maxHeartbeats 1000000
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem outside_column_defect_lt (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (j : Fin I.n) (hj : j ∉ d.1)
    (hne : (ConsistencyClosure.solutions
      (PolynomialClosure.jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary))
      W.proximityMask (insert j d.1)).Nonempty) :
    systemDefect I W d < fixedConsistencyCodimension (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) (insert j d.1) I.s := by
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  let A := PolynomialClosure.jointMap C rows
  have hg := geometry d
  have hs : I.r+I.w+I.s ≤ d.1.card := by have := hg.core.large; omega
  have ht : I.r+I.w+I.s ≤ (insert j d.1).card := hs.trans (card_le_card (subset_insert _ _))
  have hrd := PolynomialClosure.joint_rank C rows d.1 hs
  have hrt := PolynomialClosure.joint_rank C rows (insert j d.1) ht
  have hrm := ConsistencyClosure.rank_mono A (subset_insert j d.1)
  change ConsistencyClosure.rank A d.1 = I.r+I.w+I.s+systemDefect I W d at hrd
  change ConsistencyClosure.rank A (insert j d.1) = I.r+I.w+I.s+
    fixedConsistencyCodimension C rows (insert j d.1) I.s at hrt
  by_contra hn
  change ¬ systemDefect I W d < fixedConsistencyCodimension C rows (insert j d.1) I.s at hn
  have he : ConsistencyClosure.rank A d.1 = ConsistencyClosure.rank A (insert j d.1) := by omega
  have hc := ConsistencyClosure.subset_closure_of_rank_eq A W.proximityMask
    (subset_insert j d.1) hne he (mem_insert_self j d.1)
  change j ∈ PolynomialClosure.closure C rows W.proximityMask d.1 at hc
  rw [hg.closed] at hc
  exact hj hc

theorem outside_column_consistency_mean_le_inv_sq (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (hproper : 1 ≤ systemDefect I W d)
    (j : Fin I.n) (hj : j ∉ d.1) :
    mean (fun B => indicator (B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask (insert j d.1))) ≤ 1/(Nat.card F : ℚ)^2 := by
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  change mean (fun B => indicator (B ∈ Affine.consistent C rows W.proximityMask
    (insert j d.1))) ≤ 1/(Nat.card F : ℚ)^2
  by_cases hne : (Affine.consistent C rows W.proximityMask (insert j d.1)).Nonempty
  · obtain ⟨B,hB⟩ := hne
    obtain ⟨p,hp⟩ := (PolynomialClosure.exists_joint_iff C rows W.proximityMask (insert j d.1) B).mpr
      (mem_filter.mp hB).2
    have hd := outside_column_defect_lt I W d j hj ⟨(B,p),hp⟩
    change systemDefect I W d < fixedConsistencyCodimension C rows (insert j d.1) I.s at hd
    have hdim := fixedConsistencyDimension_add_codimension C rows (insert j d.1) (s := I.s)
    have hc := Affine.consistent_card_mul_field_pow_le C rows W.proximityMask (insert j d.1) 1 (by omega)
    rw [mean_indicator]
    simp only [filter_mem_eq_inter,univ_inter]
    apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos)
      (pow_pos (by exact_mod_cast Nat.card_pos (α := F)) 2)).mpr
    simpa only [one_mul,Nat.cast_mul,Nat.cast_pow,Nat.card_eq_fintype_card] using
      (Nat.cast_le (α := ℚ).mpr hc)
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp [he,indicator]

noncomputable def outsidePrimary (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (B : Challenge F (rowCount I.nw I.nq) I.s) : Prop :=
  ∃ j, j ∉ d.1 ∧ B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask (insert j d.1)

theorem outsidePrimary_mean_le (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (hproper : 1 ≤ systemDefect I W d) :
    mean (fun B => indicator (outsidePrimary I W d B)) ≤ I.n/(Nat.card F : ℚ)^2 := by
  have hp (B : Challenge F (rowCount I.nw I.nq) I.s) : indicator (outsidePrimary I W d B) ≤
      ∑ j : Fin I.n, indicator (j ∉ d.1 ∧ B ∈ Affine.consistent
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (insert j d.1)) := by
    by_cases h : outsidePrimary I W d B
    · obtain ⟨j,hj,hB⟩ := h
      have hs := single_le_sum (fun i (_ : i ∈ univ) => indicator_nonneg
        (i ∉ d.1 ∧ B ∈ Affine.consistent (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask (insert i d.1))) (mem_univ j)
      rw [indicator,if_pos (show outsidePrimary I W d B from ⟨j,hj,hB⟩)]
      simpa only [indicator,if_pos (show j ∉ d.1 ∧ B ∈ Affine.consistent
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (insert j d.1)
        from ⟨hj,hB⟩)] using hs
    · simp only [indicator,if_neg h]
      exact sum_nonneg fun _ _ => indicator_nonneg _
  calc
    _ ≤ _ := mean_mono hp
    _ = ∑ j : Fin I.n, mean (fun B => indicator (j ∉ d.1 ∧ B ∈ Affine.consistent
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (insert j d.1))) :=
      SystemException.mean_finset_sum _ _
    _ ≤ ∑ _j : Fin I.n, (1 : ℚ)/(Nat.card F : ℚ)^2 := by
      apply sum_le_sum
      intro j _
      by_cases hj : j ∈ d.1
      · simpa only [hj,not_true_eq_false,false_and,indicator,if_false,mean_const] using
          (by positivity : (0 : ℚ) ≤ 1/(Nat.card F : ℚ)^2)
      · simpa only [hj,not_false_eq_true,true_and] using
          outside_column_consistency_mean_le_inv_sq I W d hproper j hj
    _ = _ := by simp [div_eq_mul_inv]

/-- Uniform over all adaptive payload choices: outside the new event,
every good column of every assigned response lies in the actual core. -/
theorem assigned_good_subset_core_of_not_outside (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (d : systems I.domain I.primary_le W) (u : I.layer.Payload)
    (ha : ResponseAssignment I σ W coin u d) (hout : ¬ outsidePrimary I W d coin.2) :
    goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u ⊆ d.1 := by
  intro j hj
  by_contra hn
  apply hout
  refine ⟨j,hn,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  apply (PolynomialClosure.exists_joint_iff _ _ _ _ _).mp
  refine ⟨u.primary,?_⟩
  intro i hi
  rcases mem_insert.mp hi with hij | hi
  · subst i
    have h := (mem_filter.mp hj).2.1
    change (u.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j) =
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j + W.proximityMask j at h
    change (u.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j) -
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j = W.proximityMask j
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  · exact ha.primary i hi

noncomputable def coreCapacity (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) : ℚ :=
  (d.1.card.choose I.t : ℚ)/Fintype.card I.layer.Query

/-- Once the outside event is excluded, a single core pays for the union
of ALL assigned responses, including payloads chosen after the query. -/
theorem assigned_query_union_mean_le_core (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (d : systems I.domain I.primary_le W)
    (hout : ¬ outsidePrimary I W d coin.2) :
    mean (fun q : I.layer.Query => indicator (∃ u : I.layer.Payload,
      ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q)) ≤ coreCapacity I W d := by
  have hsub : (univ.filter fun q : I.layer.Query => ∃ u : I.layer.Payload,
      ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q) ⊆ queriesWithin d.1 := by
    intro q hq
    obtain ⟨u,ha,hv⟩ := (mem_filter.mp hq).2
    have hqcols := ((verify_openOracle_iff I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ W coin u q).mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, hqcols.trans
      (assigned_good_subset_core_of_not_outside I σ W coin d u ha hout)⟩
  rw [mean_indicator]
  unfold coreCapacity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcard : (queriesWithin (r := I.t) d.1).card = d.1.card.choose I.t := card_queriesWithin _
  have hc := (card_le_card hsub).trans_eq hcard
  have hcast := Nat.cast_le (α := ℚ).mpr hc
  convert hcast using 1
  congr 1
  congr 1
  ext q
  simp

end RecursivePolygero.ProfileAnalysis
