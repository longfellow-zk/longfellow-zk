import polygero.Local.WeightedExceptions

/-! One system pays for a UNION of adaptive responses at a single query.
The response family need not be full-system or payload-rigid. Primary
uniqueness makes its union consistent; canonical closure then bounds that
union by the original capacity. This does not sum over distinct hash queries. -/
set_option maxHeartbeats 2000000

namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private noncomputable abbrev cols (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload) :=
  goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u

/-- Proper systems are allowed. All responses assigned to one system have
one primary polynomial, so their good-column union is an actual consistent
analysis set with the same canonical closure. -/
theorem assigned_union_capacity_le (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (d : systems I.domain I.primary_le W) (S : Finset I.layer.Payload)
    (ha : ∀ u ∈ S, ResponseAssignment I σ W coin u d) :
    (S.biUnion (cols I σ W coin)).card ≤ ReducedSystems.capacity
      (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 := by
  by_cases hs : S = ∅
  · simp [hs]
  obtain ⟨u₀, hu₀⟩ := nonempty_iff_ne_empty.mpr hs
  let G := cols I σ W coin u₀
  let E := S.biUnion (cols I σ W coin)
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  have hsub : G ⊆ E := subset_biUnion_of_mem (cols I σ W coin) hu₀
  have hg := (mem_filter.mp (ha u₀ hu₀).associated).2
  change I.r + I.w + I.s + I.s + 1 ≤ G.card ∧
    fixedConsistencyCodimension C rows G I.s ≤ I.s ∧
    (ConsistencyClosure.solutions (PolynomialClosure.jointMap C rows) W.proximityMask G).Nonempty ∧
    PolynomialClosure.closure C rows W.proximityMask
      (PolynomialClosure.canonicalCoreSet C rows G) = d.1 at hg
  have heSize : I.r + I.w + I.s + I.s + 1 ≤ E.card := hg.1.trans (card_le_card hsub)
  have heSol : (coin.2, u₀.primary) ∈ ConsistencyClosure.solutions
      (PolynomialClosure.jointMap C rows) W.proximityMask E := by
    intro j hj
    obtain ⟨u, hu, hj⟩ := mem_biUnion.mp hj
    have hp := assigned_primary_unique I σ W coin u u₀ d (ha u hu) (ha u₀ hu₀)
    have hv := (mem_filter.mp hj).2.1
    change (u.primary : F[X]).eval (C.node j) = response C rows coin.2 j + W.proximityMask j at hv
    change (u₀.primary : F[X]).eval (C.node j) - response C rows coin.2 j = W.proximityMask j
    rw [hp] at hv
    exact sub_eq_iff_eq_add.mpr (hv.trans (add_comm _ _))
  have heLow := ReducedSystems.low_defect_of_not_bad C rows W.proximityMask coin.2
    hout E heSize u₀.primary heSol
  have heLabel := PolynomialClosure.canonical_closures_eq C rows W.proximityMask hk G E
    hg.2.1 heLow (by omega) (by omega) hg.2.2.1 ⟨_, heSol⟩
    (by rw [inter_eq_left.mpr hsub]; omega)
  apply Finset.le_sup (f := Finset.card)
  exact mem_filter.mpr ⟨mem_univ _, heSize, heLow, ⟨_, heSol⟩, heLabel.symm.trans hg.2.2.2⟩

/-- The payload can be chosen after the query, from any child commitment.
A system is charged once for the union, not once per possible payload. -/
theorem assigned_query_union_mean_le (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (d : systems I.domain I.primary_le W) :
    mean (fun q : I.layer.Query => indicator (∃ u : I.layer.Payload,
      ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q)) ≤ systemCap I W d := by
  let S : Finset I.layer.Payload := univ.filter (fun u => ResponseAssignment I σ W coin u d)
  let E := S.biUnion (cols I σ W coin)
  have hc := assigned_union_capacity_le I hk σ W coin hout d S (fun u hu => (mem_filter.mp hu).2)
  have hsub : (univ.filter fun q : I.layer.Query => ∃ u : I.layer.Payload,
      ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q) ⊆ queriesWithin E := by
    intro q hq
    obtain ⟨u, ha, hv⟩ := (mem_filter.mp hq).2
    have hqcols := ((verify_openOracle_iff I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ W coin u q).mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact hqcols.trans (subset_biUnion_of_mem (cols I σ W coin) (mem_filter.mpr ⟨mem_univ _, ha⟩))
  rw [mean_indicator]
  unfold systemCap
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcq : (queriesWithin (r := I.t) E).card ≤
      (ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1).choose I.t := by
    rw [card_queriesWithin]
    exact Nat.choose_le_choose I.t hc
  have hcast := Nat.cast_le (α := ℚ).mpr ((card_le_card hsub).trans hcq)
  convert hcast using 1
  congr 1
  congr 1
  ext q
  simp

/-- Exception coverage at one fresh parent-query coordinate, including
all proper-system responses and arbitrary post-query payload selection. -/
def assignedExceptionQuery (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (q : I.layer.Query) : Prop :=
  coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask ∧
  ∃ d ∈ highSystems I p W, coin ∈ systemExceptions p.positive_degree I.layout σ d ∧
    ∃ u : I.layer.Payload, ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q

/-- The weighted exception bound really covers adaptive response unions;
it is not merely a bound on an unconnected potential. -/
theorem assignedExceptionQuery_conditional_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) :
    mean (fun q => indicator (assignedExceptionQuery I p σ W coin q)) ≤
      weightedExceptions I p σ W coin := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · simp only [assignedExceptionQuery, hb, not_true_eq_false, false_and, indicator, if_false, mean_const]
    unfold weightedExceptions
    exact sum_nonneg fun d _ => mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _)
  let event := fun d q => ∃ u : I.layer.Payload,
    ResponseAssignment I σ W coin u d ∧ I.layer.verify σ W coin u q
  have hi (q : I.layer.Query) : indicator (assignedExceptionQuery I p σ W coin q) ≤
      ∑ d ∈ highSystems I p W, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) *
        indicator (event d q) := by
    by_cases he : assignedExceptionQuery I p σ W coin q
    · obtain ⟨_, d, hd, hx, hu⟩ := he
      have hs := single_le_sum (fun d (_ : d ∈ highSystems I p W) =>
        mul_nonneg (indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
          (indicator_nonneg (event d q))) hd
      have huEvent : event d q := hu
      simpa only [indicator, if_pos hx, if_pos huEvent, mul_one,
        if_pos (show assignedExceptionQuery I p σ W coin q from ⟨hb,d,hd,hx,hu⟩)] using hs
    · simpa only [indicator, if_neg he] using sum_nonneg
        (s := highSystems I p W) (fun d _ =>
          mul_nonneg (indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
          (indicator_nonneg (event d q)))
  calc
    _ ≤ _ := mean_mono hi
    _ = ∑ d ∈ highSystems I p W, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) *
        mean (fun q => indicator (event d q)) := by
      rw [SystemException.mean_finset_sum]
      apply sum_congr rfl
      intro d _
      exact mean_mul_left _ _
    _ ≤ weightedExceptions I p σ W coin := by
      unfold weightedExceptions
      apply sum_le_sum
      intro d _
      rw [mul_comm (systemCap I W d)]
      exact mul_le_mul_of_nonneg_left
        (assigned_query_union_mean_le I p.positive_degree σ W coin hb d) (indicator_nonneg _)

theorem assignedExceptionQuery_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun coin => mean (fun q => indicator (assignedExceptionQuery I p σ W coin q))) ≤
      (1 - p.threshold + p.listBound * p.threshold) / Nat.card F :=
  (mean_mono (assignedExceptionQuery_conditional_le I p σ W)).trans
    (weightedExceptions_mean_le I p hsmall σ W)

end RecursivePolygero.ProfileAnalysis
