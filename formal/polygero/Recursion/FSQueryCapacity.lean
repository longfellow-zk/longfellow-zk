import polygero.Recursion.FSCapacityConsumption
import polygero.Recursion.FSListBound
import polygero.Local.StoppedSpectrum

set_option maxHeartbeats 2000000

/-! Actual parent-query coverage with a capacity-dependent price.

The child commitment fixes at most `L_child` full-system labels before the
parent query. Low parent responses cost `L_child * theta_parent`; high
failing responses are covered by the proved assigned-response union bound.
Neither this event nor its local price assumes a query order.
-/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Counting ProfileAnalysis Local Local.Polygero
open Bcs.TotalOracle.Footprint
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- This is the old parent-query target event without first discarding
the parent's Boolean exception event. The child labels are fixed by V. -/
noncomputable def queryCapacityRisk (σ : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (a : I.layer.Coin) (q : I.layer.Query) : Prop :=
  ∃ d ∈ highSystems child.instance cp V,
    systemTarget child.instance cp.positive_degree V
      (Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q) d

noncomputable def queryCapacity (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) : ℚ :=
  StoppedSpectrum.conditionalCapacity I p σ W (cp.listBound * p.threshold) a

theorem queryCapacity_nonneg (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) : 0 ≤ queryCapacity child p cp σ W a := by
  unfold queryCapacity StoppedSpectrum.conditionalCapacity
  split_ifs
  · norm_num
  · apply add_nonneg (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg)
    unfold weightedExceptions
    exact sum_nonneg fun d _ => mul_nonneg (by unfold systemCap; positivity) (indicator_nonneg _)

private def lowSystemQuery (σ : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (a : I.layer.Coin)
    (d : systems child.instance.domain child.instance.primary_le V) (q : I.layer.Query) : Prop :=
  ∃ hfull, (responseCount I.layer σ W a (child.link.decode
      ((tupleCounts child.instance).witness (systemLabel child.instance cp.positive_degree V d hfull))) : ℚ) /
        Fintype.card I.layer.Query ≤ p.threshold ∧
    Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q
      (systemLabel child.instance cp.positive_degree V d hfull)

private theorem lowSystemQuery_mean_le (σ : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (a : I.layer.Coin)
    (d : systems child.instance.domain child.instance.primary_le V) :
    mean (fun q => indicator (lowSystemQuery child p cp σ W V a d q)) ≤ p.threshold := by
  by_cases hf : Affine.consistent
      (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
      (oracleWords V.ordinary) V.proximityMask d.1 = univ
  · let u := child.link.decode ((tupleCounts child.instance).witness
      (systemLabel child.instance cp.positive_degree V d hf))
    by_cases hl : (responseCount I.layer σ W a u : ℚ) / Fintype.card I.layer.Query ≤ p.threshold
    · calc
        _ ≤ mean (fun q => indicator (I.layer.verify σ W a u q)) := by
          apply mean_mono
          intro q
          apply indicator_mono
          rintro ⟨_, _, ht⟩
          exact ht.1
        _ = (responseCount I.layer σ W a u : ℚ) / Fintype.card I.layer.Query := mean_indicator _
        _ ≤ _ := hl
    · have hn (q : I.layer.Query) : ¬ lowSystemQuery child p cp σ W V a d q := by
        rintro ⟨_, hh, _⟩
        exact hl hh
      simpa only [indicator, if_neg (hn _), mean_const] using p.threshold_nonneg
  · have hn (q : I.layer.Query) : ¬ lowSystemQuery child p cp σ W V a d q := by
      rintro ⟨hfull, _⟩
      exact hf hfull
    simpa only [indicator, if_neg (hn _), mean_const] using p.threshold_nonneg

/-- Local query price, uniform over every child commitment and every
answer outside this query coordinate. High parent responses share the
capacity of their assigned system; low child labels retain their list cost. -/
theorem queryCapacityRisk_mean_le_of_exception_bound (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) (bound : ℚ)
    (hexc : mean (fun q => indicator (assignedExceptionQuery I p σ W a q)) ≤ bound) :
    mean (fun q => indicator (queryCapacityRisk child cp σ W V a q)) ≤
      (if a.2 ∈ ReducedSystems.badChallenges
        (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask then 1 else cp.listBound*p.threshold+bound) := by
  by_cases hb : a.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · rw [if_pos hb]
    calc
      _ ≤ mean (fun _ : I.layer.Query => (1 : ℚ)) := by
        apply mean_mono
        intro q
        unfold indicator
        split_ifs <;> norm_num
      _ = _ := mean_const _
  have hpoint (q : I.layer.Query) : indicator (queryCapacityRisk child cp σ W V a q) ≤
      indicator (assignedExceptionQuery I p σ W a q) +
        ∑ d ∈ highSystems child.instance cp V, indicator (lowSystemQuery child p cp σ W V a d q) := by
    by_cases he : queryCapacityRisk child cp σ W V a q
    · obtain ⟨d, hd, hf, ht⟩ := he
      let u := child.link.decode ((tupleCounts child.instance).witness
        (systemLabel child.instance cp.positive_degree V d hf))
      by_cases hl : (responseCount I.layer σ W a u : ℚ) / Fintype.card I.layer.Query ≤ p.threshold
      · have hlo : lowSystemQuery child p cp σ W V a d q := ⟨hf, hl, ht⟩
        have hs := single_le_sum (fun d (_ : d ∈ highSystems child.instance cp V) =>
          indicator_nonneg (lowSystemQuery child p cp σ W V a d q)) hd
        have hone : indicator (queryCapacityRisk child cp σ W V a q) = 1 := by
          simp only [indicator, if_pos (show queryCapacityRisk child cp σ W V a q from ⟨d, hd, hf, ht⟩)]
        rw [hone]
        have hs' : 1 ≤ ∑ d ∈ highSystems child.instance cp V,
            indicator (lowSystemQuery child p cp σ W V a d q) := by
          simpa only [indicator, if_pos hlo] using hs
        exact hs'.trans (le_add_of_nonneg_left (indicator_nonneg _))
      · have hhigh := lt_of_not_ge hl
        obtain ⟨e, ha, hx⟩ := high_target_response_cases I p σ W a u (fun _ => False)
          hhigh ht.2 hb
        have hehigh : e ∈ highSystems I p W := mem_filter.mpr ⟨mem_univ _,
          hhigh.trans_le (assigned_response_fraction_le I σ W a u e ha)⟩
        have hex : a ∈ systemExceptions p.positive_degree I.layout σ e := by
          rcases hx with ⟨_, hx⟩ | ⟨_, hx | hx⟩
          · exact hx
          · obtain ⟨_, hfalse⟩ := hx
            exact hfalse.elim
          · exact hx
        have hquery : assignedExceptionQuery I p σ W a q := ⟨hb, e, hehigh, hex, u, ha, ht.1⟩
        simp only [indicator, if_pos hquery,
          if_pos (show queryCapacityRisk child cp σ W V a q from ⟨d, hd, hf, ht⟩)]
        exact le_add_of_nonneg_right (sum_nonneg fun _ _ => indicator_nonneg _)
    · simp only [indicator, if_neg he]
      exact add_nonneg (indicator_nonneg _) (sum_nonneg fun _ _ => indicator_nonneg _)
  calc
    _ ≤ _ := mean_mono hpoint
    _ = mean (fun q => indicator (assignedExceptionQuery I p σ W a q)) +
        ∑ d ∈ highSystems child.instance cp V,
          mean (fun q => indicator (lowSystemQuery child p cp σ W V a d q)) := by
      rw [mean_add, SystemException.mean_finset_sum]
    _ ≤ bound + ∑ _d ∈ highSystems child.instance cp V, p.threshold :=
      add_le_add hexc
        (sum_le_sum fun d _ => lowSystemQuery_mean_le child p cp σ W V a d)
    _ ≤ bound + cp.listBound * p.threshold := by
      have hcard : ((highSystems child.instance cp V).card : ℚ) ≤ cp.listBound := by
        exact Nat.cast_le.mpr (highSystems_card_le child.instance cp hcp V)
      have hlow : (∑ _d ∈ highSystems child.instance cp V, p.threshold) ≤
          cp.listBound * p.threshold := by
        calc
          _ = (highSystems child.instance cp V).card * p.threshold := by
            simp only [sum_const, nsmul_eq_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hcard p.threshold_nonneg
      exact add_le_add le_rfl hlow
    _ = _ := by
      rw [if_neg hb]
      exact add_comm _ _

theorem queryCapacityRisk_mean_le (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) :
    mean (fun q => indicator (queryCapacityRisk child cp σ W V a q)) ≤
      queryCapacity child p cp σ W a :=
  queryCapacityRisk_mean_le_of_exception_bound child p cp hcp σ W V a
    (weightedExceptions I p σ W a) (assignedExceptionQuery_conditional_le I p σ W a)

noncomputable def queryCapacityEvent (σ : I.layer.Statement) :
    HashInput child → (HashInput child → Answer child) → Prop
  | .inr (.inl (W, V)), H => queryCapacityRisk child cp σ W V
      (H (gamma W)).1.1 (H (query W V)).1.2
  | _, _ => False

/-- The actual query hash input has the stated conditional capacity, with
the parent challenge held outside the coordinate being resampled. -/
theorem queryCapacityEvent_local (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (H : HashInput child → Answer child) :
    average (fun c => indicator
      (queryCapacityEvent child cp σ (query W V) (Function.update H (query W V) c))) ≤
        queryCapacity child p cp σ W (H (gamma W)).1.1 := by
  simp only [queryCapacityEvent, query, gamma, Function.update_self,
    Function.update_of_ne (by simp : (Sum.inl W : HashInput child) ≠ Sum.inr (Sum.inl (W,V)))]
  change mean (fun c : Answer child => indicator
    (queryCapacityRisk child cp σ W V (H (.inl W)).1.1 c.1.2)) ≤ _
  simp only [mean_prod, mean_const]
  exact queryCapacityRisk_mean_le child p cp hcp σ W V _

private theorem child_target_of_capacity_failure (σ : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) (q : I.layer.Query) (b : child.instance.layer.Coin)
    (R : child.instance.layer.Payload) (t : child.instance.layer.Query)
    (hd : child.link.direct W q)
    (hr : (twoProof child p cp).run σ W (constantMessages child (W,V,q,R)) ((a,q),(b,t)) = none) :
    outputHit (Protocol.ProfileProof.inducedFamily (child := child) σ W a (fun _ => False) q)
      (scanRecoverAt child.instance (child.link.statement σ W a q) V b R) := by
  simp only [twoProof, Protocol.HahnProfileProof.run, Protocol.HahnProfileProof.runTranscript,
    Protocol.chain, Chain.record, constantMessages, Protocol.HahnProfileProof.family] at hr
  cases he : scanRecoverAt child.instance (child.link.statement σ W a q) V b R with
  | none => trivial
  | some g =>
    have hs := scanRecoverAt_valid child.instance (child.link.statement σ W a q) V b R g he
    have hv := (child.verify_iff σ W a q _).mp ⟨hd, hs⟩
    simp only [he] at hr
    exact ⟨hv, by simp only [hr, outputHit]⟩

/-- Exhaustive failure coverage without the parent's Boolean list event.
The replacement query event is priced by `queryCapacity`, including all
proper parent-system exceptions. Child exceptions remain explicit. -/
theorem failure_capacity_cover (σ : I.layer.Statement)
    (H : HashInput child → Answer child) (d : Proof child)
    (hf : failure child p cp σ (fun _ => False) H d) :
    queryCapacityEvent child cp σ (query d.1 d.2.1) H ∨
    childEvent child cp σ (childGamma d.1 d.2.1 d.2.2.1) H ∨
    terminalEvent child cp σ (terminal d) H := by
  obtain ⟨ha, hr⟩ := (failure_empty_iff child p cp σ H d).mp hf
  obtain ⟨hq, hd, hv⟩ := (accepts_iff child σ H d).mp ha
  have ht := child_target_of_capacity_failure child p cp σ d.1 d.2.1
    (H (gamma d.1)).1.1 d.2.2.1 (H (childGamma d.1 d.2.1 d.2.2.1)).2.1
    d.2.2.2 (H (terminal d)).2.2 hd (by simpa only [proofCoins, hq] using hr)
  by_cases hl : (responseCount child.instance.layer
      (child.link.statement σ d.1 (H (gamma d.1)).1.1 d.2.2.1) d.2.1
      (H (childGamma d.1 d.2.1 d.2.2.1)).2.1 d.2.2.2 : ℚ) /
        Fintype.card child.instance.layer.Query ≤ cp.threshold
  · exact Or.inr (Or.inr ⟨hl, hv⟩)
  have hc := high_target_list_cover child.instance cp _ d.2.1 _ d.2.2.2 _
    (lt_of_not_ge hl) ht
  rcases hc with hc | hc
  · exact Or.inr (Or.inl hc)
  · left
    change queryCapacityRisk child cp σ d.1 d.2.1
      (H (gamma d.1)).1.1 (H (query d.1 d.2.1)).1.2
    rw [hq]
    exact hc

end RecursivePolygero.FiatShamir.TwoLevel
