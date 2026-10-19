import polygero.Local.ResponseRigidity
import polygero.Local.CapacityRigidity

/-!
# Response incidence with capacity rigidity

The fully consistent systems and the capacity-rigid proper systems share
one excess-incidence budget. Only proper systems which fail both rigidity
criteria are paid as response-free exception events.
-/

namespace RecursivePolygero.ProfileAnalysis

open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A fixed system is rigid either by full consistency or by the overlap
forced by its column capacity at the certificate's high-response cutoff. -/
def RigidSystem (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (d : systems I.domain I.primary_le W) : Prop :=
  Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ ∨
    ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 + 2 * (I.r + I.w) ≤
        2 * p.columnCutoff

theorem high_assigned_payload_unique_of_rigid
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (u v : I.layer.Payload) (d : systems I.domain I.primary_le W)
    (hd : RigidSystem I p W d)
    (hu : ResponseAssignment I σ W coin u d) (hv : ResponseAssignment I σ W coin v d)
    (hhu : p.threshold < (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query)
    (hhv : p.threshold < (responseCount I.layer σ W coin v : ℚ) / Fintype.card I.layer.Query) :
    u = v := by
  rcases hd with hf | hc
  · exact assigned_payload_unique I p.positive_degree σ W coin u v d hf hu hv
      ((le_max_right _ _).trans (high_response_large I p σ W coin u hhu).2)
      ((le_max_right _ _).trans (high_response_large I p σ W coin v hhv).2)
  · exact high_assigned_payload_unique_of_capacity I p σ W coin hout u v d hu hv hhu hhv hc

/-- High responses assigned to rigid systems have one payload per system.
The conclusion charges the excess, with the baseline paid once. -/
theorem rigid_response_excess_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (label : I.layer.Payload → systems I.domain I.primary_le W)
    (hmem : ∀ u ∈ S, label u ∈ T)
    (hrigid : ∀ u ∈ S, RigidSystem I p W (label u))
    (ha : ∀ u ∈ S, ResponseAssignment I σ W coin u (label u))
    (hhigh : ∀ u ∈ S, p.threshold <
      (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query) :
    (∑ u ∈ S, max 0 ((responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query - p.threshold)) ≤
      ∑ d ∈ T, max 0 (systemCap I W d - p.threshold) := by
  have hinj : Set.InjOn label S := by
    intro u hu v hv he
    exact high_assigned_payload_unique_of_rigid I p σ W coin hout u v (label u)
      (hrigid u hu) (ha u hu) (he ▸ ha v hv) (hhigh u hu) (hhigh v hv)
  calc
    _ ≤ ∑ u ∈ S, max 0 (systemCap I W (label u) - p.threshold) := by
      apply sum_le_sum
      intro u hu
      exact max_le_max_left 0 (sub_le_sub_right
        (assigned_response_fraction_le I σ W coin u _ (ha u hu)) p.threshold)
    _ = ∑ d ∈ S.image label, max 0 (systemCap I W d - p.threshold) :=
      (sum_image (f := fun d => max 0 (systemCap I W d - p.threshold)) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by intro d hd; obtain ⟨u, hu, rfl⟩ := mem_image.mp hd; exact hmem u hu)
      (fun _ _ _ => le_max_left _ _)

def RigidResponseCover (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W)) : Prop :=
  ∀ u ∈ S, p.threshold <
      (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query ∧
    ∃ d ∈ T, RigidSystem I p W d ∧ ResponseAssignment I σ W coin u d ∧
      (systemTarget I p.positive_degree W D d ∨
        coin ∈ systemExceptions p.positive_degree I.layout σ d)

/-- This actual response family includes proper systems whenever capacity
rigidity applies, and includes the exceptional responses of those systems. -/
noncomputable def coveredRigidResponses (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (T : Finset (systems I.domain I.primary_le W)) : Finset I.layer.Payload :=
  univ.filter (fun u => p.threshold <
      (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query ∧
    ∃ d ∈ T, RigidSystem I p W d ∧ ResponseAssignment I σ W coin u d ∧
      (systemTarget I p.positive_degree W D d ∨
        coin ∈ systemExceptions p.positive_degree I.layout σ d))

theorem coveredRigidResponses_cover (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (T : Finset (systems I.domain I.primary_le W)) :
    RigidResponseCover I p σ W coin D (coveredRigidResponses I p σ W coin D T) T := by
  intro u hu
  exact (mem_filter.mp hu).2

theorem rigid_response_excess_le_of_cover (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (hcover : RigidResponseCover I p σ W coin D S T) :
    (∑ u ∈ S, max 0 ((responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query - p.threshold)) ≤
      ∑ d ∈ T, max 0 (systemCap I W d - p.threshold) := by
  by_cases hS : S = ∅
  · simp only [hS, sum_empty]
    exact sum_nonneg (fun _ _ => le_max_left _ _)
  obtain ⟨u₀, hu₀⟩ := nonempty_iff_ne_empty.mpr hS
  let fallback := (hcover u₀ hu₀).2.choose
  let label (u : I.layer.Payload) := if hu : u ∈ S then (hcover u hu).2.choose else fallback
  have hs (u : I.layer.Payload) (hu : u ∈ S) :
      label u ∈ T ∧ RigidSystem I p W (label u) ∧ ResponseAssignment I σ W coin u (label u) := by
    have h := (hcover u hu).2.choose_spec
    simpa only [label, dif_pos hu] using ⟨h.1, h.2.1, h.2.2.1⟩
  exact rigid_response_excess_le I p σ W coin hout S T label
    (fun u hu => (hs u hu).1) (fun u hu => (hs u hu).2.1)
    (fun u hu => (hs u hu).2.2) (fun u hu => (hcover u hu).1)

theorem responseIncidence_le_localIncidence_of_rigid_cover
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (hcover : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask → RigidResponseCover I p σ W coin D S T) :
    responseIncidence I p σ W coin S ≤ localIncidence I p σ W T D coin := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · simp [responseIncidence, localIncidence, SystemException.incidence, indicator, hb]
  · let active := fun d => systemTarget I p.positive_degree W D d ∨
        coin ∈ systemExceptions p.positive_degree I.layout σ d
    have hc := rigid_response_excess_le_of_cover I p σ W coin hb D S
      (T.filter active) (by
        intro u hu
        obtain ⟨hh, d, hd, hr, ha, he⟩ := hcover hb u hu
        exact ⟨hh, d, mem_filter.mpr ⟨hd, he⟩, hr, ha, he⟩)
    simp only [responseIncidence, hb, if_false, localIncidence, SystemException.incidence,
      indicator, not_false_eq_true, true_and, sub_zero, one_mul, zero_add] at ⊢
    apply add_le_add le_rfl
    simp only [sum_filter, active, mul_ite, mul_one, mul_zero] at hc ⊢
    convert hc using 1 <;> congr 1

/-- Full and capacity-rigid systems use the same single baseline and rank
budget. The response family is allowed to depend on both random inputs. -/
theorem responseIncidence_mean_of_rigid_cover {Z : Type} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop)
    (S : Z → I.layer.Coin → Finset I.layer.Payload)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (rate : ℚ) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (hcover : ∀ z coin, coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask →
        RigidResponseCover I p (σ z) W coin (D z) (S z coin) T) :
    mean (fun z => mean (fun coin => responseIncidence I p (σ z) W coin (S z coin))) ≤
      p.error + (1 - p.error) * rate := by
  exact (mean_mono (fun z => mean_mono (fun coin =>
    responseIncidence_le_localIncidence_of_rigid_cover I p (σ z) W coin (D z)
      (S z coin) T (hcover z coin)))).trans
    (localIncidence_mean_of_hahn I p σ W T hT rate hr0 hr1 D hD)

/-- Removing the once-paid query baseline leaves a nonnegative block
charge: rank mass costs `1-theta`, and other coins cost response excess. -/
theorem responseIncidence_sub_threshold_nonneg
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (S : Finset I.layer.Payload) :
    0 ≤ responseIncidence I p σ W coin S - p.threshold := by
  unfold responseIncidence
  split_ifs
  · exact sub_nonneg.mpr p.threshold_lt_one.le
  · have h := sum_nonneg (s := S) (fun u _ =>
        le_max_left 0 ((responseCount I.layer σ W coin u : ℚ) /
          Fintype.card I.layer.Query - p.threshold))
    linarith

/-- The whole-block excess costs no repeated baseline. In a terminal
query, normalized successful-response charge has mean `c-theta`, so this
is the useful coefficient for fractional block charging. -/
theorem responseIncidence_excess_mean_of_rigid_cover
    {Z : Type} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop)
    (S : Z → I.layer.Coin → Finset I.layer.Payload)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (rate : ℚ) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (hcover : ∀ z coin, coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask →
        RigidResponseCover I p (σ z) W coin (D z) (S z coin) T) :
    mean (fun z => mean (fun coin => responseIncidence I p (σ z) W coin (S z coin) - p.threshold)) ≤
      (p.error - p.threshold) + (1 - p.error) * rate := by
  have h := responseIncidence_mean_of_rigid_cover I p σ W D S T hT rate hr0 hr1 hD hcover
  simp_rw [mean_sub, mean_const]
  linarith

/-- Systems not covered by either rigidity theorem are necessarily proper.
This event pays their exception once, independently of their payload count. -/
def nonrigidException (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (coin : I.layer.Coin) : Prop :=
  ∃ d ∈ T, ¬ RigidSystem I p W d ∧
    coin ∈ systemExceptions p.positive_degree I.layout σ d

theorem high_target_covered_or_nonrigid (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (D : (tupleCounts I).Index → Prop) (T : Finset (systems I.domain I.primary_le W))
    (hT : ∀ d, p.threshold < systemCap I W d → d ∈ T)
    (hh : p.threshold < (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query)
    (htarget : outputHit D (scanRecoverAt I σ W coin u))
    (hbad : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) :
    u ∈ coveredRigidResponses I p σ W coin D T ∨ nonrigidException I p σ W T coin := by
  obtain ⟨d, ha, he⟩ := high_target_response_cases I p σ W coin u D hh htarget hbad
  have hd := hT d (hh.trans_le (assigned_response_fraction_le I σ W coin u d ha))
  by_cases hr : RigidSystem I p W d
  · left
    apply mem_filter.mpr
    refine ⟨mem_univ _, hh, d, hd, hr, ha, ?_⟩
    rcases he with ⟨_, he⟩ | ⟨_, he⟩
    · exact Or.inr he
    · exact he
  · right
    refine ⟨d, hd, hr, ?_⟩
    rcases he with ⟨_, he⟩ | ⟨hf, _⟩
    · exact he
    · exact (hr (Or.inl hf)).elim

theorem nonrigidException_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) :
    mean (fun coin => indicator (nonrigidException I p σ W T coin)) ≤
      ((T.filter (fun d => ¬ RigidSystem I p W d)).card : ℚ) / Nat.card F := by
  let P := T.filter (fun d => ¬ RigidSystem I p W d)
  have hi (coin : I.layer.Coin) : indicator (nonrigidException I p σ W T coin) ≤
      ∑ d ∈ P, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) := by
    by_cases he : nonrigidException I p σ W T coin
    · obtain ⟨d, hd, hn, he'⟩ := he
      have hs := single_le_sum
        (fun d (_ : d ∈ P) => indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
        (show d ∈ P from mem_filter.mpr ⟨hd, hn⟩)
      simpa only [indicator, if_pos (show nonrigidException I p σ W T coin from ⟨d, hd, hn, he'⟩), if_pos he'] using hs
    · simpa only [indicator, if_neg he] using sum_nonneg
        (s := P) (fun d _ => indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
  calc
    _ ≤ mean (fun coin => ∑ d ∈ P, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := mean_mono hi
    _ = ∑ d ∈ P, mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) :=
      SystemException.mean_finset_sum P _
    _ ≤ ∑ _d ∈ P, (1 : ℚ) / Nat.card F :=
      sum_le_sum (fun d _ => systemExceptions_mean I p.toProfileParameters σ W d)
    _ = _ := by simp [P, div_eq_mul_inv]

theorem fixed_nonrigidException_mean_le_two (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W))
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (ha : p.columnCutoff = 2714) :
    mean (fun coin => indicator (nonrigidException I p σ W T coin)) ≤ 2 / Nat.card F := by
  apply (nonrigidException_mean_le I p σ W T).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply (card_le_card ?_).trans (fixed_nonrigid_systems_card_le_two I p W hn hk hs ha)
  intro d hd
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have h := (mem_filter.mp hd).2
  exact fun hc => h (Or.inr hc)

private theorem three_sets_card_le {n : ℕ} (A B C : Finset (Fin n)) :
    A.card + B.card + C.card ≤ n + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  have hAB := card_union_add_card_inter A B
  have hABC := card_union_add_card_inter (A ∪ B) C
  have hsplit : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [union_inter_distrib_right]
    exact card_union_le _ _
  have hn : ((A ∪ B) ∪ C).card ≤ n := by
    simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ ((A ∪ B) ∪ C))
  omega

/-- Capacity witnesses inherit the three-set packing inequality. This
nonuniform inequality also relates systems on opposite sides of the
rigidity cutoff. -/
theorem three_capacities_le (I : Instance F) (p : ProfileParameters I)
    (W : I.layer.Oracle) (a b c : systems I.domain I.primary_le W)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask a.1 +
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask b.1 +
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask c.1 ≤
      I.n + 3 * p.overlapSize := by
  let E := fun d : systems I.domain I.primary_le W =>
    Classical.choose (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hs (d : systems I.domain I.primary_le W) :=
    Classical.choose_spec (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hi (d e : systems I.domain I.primary_le W) (hne : d ≠ e) :
      (E d ∩ E e).card ≤ p.overlapSize := by
    exact ReducedSystems.associated_intersection (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask p.positive_degree d.1 e.1 (E d) (E e)
      (hs d).1 (hs e).1 (fun he => hne (Subtype.ext he))
  have h := three_sets_card_le (E a) (E b) (E c)
  have hab' := hi a b hab
  have hac' := hi a c hac
  have hbc' := hi b c hbc
  rw [(hs a).2, (hs b).2, (hs c).2] at h
  omega

/-- Two systems escaping rigidity leave no room for a third high system
at the fixed geometry. In particular, the residual count and the rigid
excess cannot simultaneously attain their separate worst cases. -/
theorem fixed_two_nonrigid_no_high_rigid
    (I : Instance F) (p : HahnSystemCertificate I) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W))
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (ha : p.columnCutoff = 2714)
    (h2 : 2 ≤ (T.filter (fun d => ¬ RigidSystem I p W d)).card) :
    ∀ d, RigidSystem I p W d → systemCap I W d ≤ p.threshold := by
  obtain ⟨a, haT, b, hbT, hab⟩ := one_lt_card.mp (show 1 <
      (T.filter (fun d => ¬ RigidSystem I p W d)).card by omega)
  have hna := (mem_filter.mp haT).2
  have hnb := (mem_filter.mp hbT).2
  intro d hd
  by_contra hlow
  have hhigh : p.threshold < systemCap I W d := lt_of_not_ge hlow
  have had : a ≠ d := fun he => hna (he ▸ hd)
  have hbd : b ≠ d := fun he => hnb (he ▸ hd)
  have hca : ¬ (ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask a.1 + 2 * (I.r + I.w) ≤ 2 * p.columnCutoff) :=
    fun hc => hna (Or.inr hc)
  have hcb : ¬ (ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask b.1 + 2 * (I.r + I.w) ≤ 2 * p.columnCutoff) :=
    fun hc => hnb (Or.inr hc)
  unfold systemCap at hhigh
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] at hhigh
  have hcd := DirectBinomial.size_ge_of_choose_div_gt (Nat.choose_pos I.query_le) p.floor_le hhigh
  have hcap := three_capacities_le I p.toProfileParameters W a b d hab had hbd
  have hover : p.toProfileParameters.overlapSize = 639 := by
    simp [ProfileParameters.overlapSize, hk, hs]
  have hcap' : ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask a.1 +
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask b.1 +
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 ≤ 8192 + 3 * 639 := by
    simpa only [hn, hover] using hcap
  omega

/-- Jointly budgeting nonrigid exceptions and rigid response excess costs
at most two field units, rather than adding their independent bounds of
two and one. The threshold baseline remains paid separately once. -/
theorem fixed_rigid_excess_add_nonrigid_count_le_two
    (I : Instance F) (p : HahnSystemCertificate I) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (ha : p.columnCutoff = 2714) :
    (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold)) +
      ((T.filter (fun d => ¬ RigidSystem I p W d)).card : ℚ) ≤ 2 := by
  let N := T.filter (fun d => ¬ RigidSystem I p W d)
  have hN : N.card ≤ 2 := by
    apply (card_le_card ?_).trans (fixed_nonrigid_systems_card_le_two I p W hn hk hs ha)
    intro d hd
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact fun hc => (mem_filter.mp hd).2 (Or.inr hc)
  by_cases h2 : 2 ≤ N.card
  · have hz : (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold)) = 0 := by
      apply sum_eq_zero
      intro d hd
      exact max_eq_left (sub_nonpos.mpr
        (fixed_two_nonrigid_no_high_rigid I p W T hn hk hs ha h2 d (mem_filter.mp hd).2))
    rw [hz, zero_add]
    exact_mod_cast hN
  · have hc : (N.card : ℚ) ≤ 1 := by exact_mod_cast (show N.card ≤ 1 by omega)
    have he := systemCap_excess_of_hahn I p W (T.filter (RigidSystem I p W))
      ((card_filter_le _ _).trans hT)
    have ht := p.threshold_nonneg
    change _ + (N.card : ℚ) ≤ 2
    linarith

/-- A joint local exception charge: rigid systems pay their query-capacity
excess, while a residual nonrigid event pays one, with no payload factor. -/
noncomputable def rigidExceptionExcess (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (coin : I.layer.Coin) : ℚ :=
  (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) *
    indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) +
      indicator (nonrigidException I p σ W T coin)

theorem rigidExceptionExcess_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) :
    mean (rigidExceptionExcess I p σ W T) ≤
      ((∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold)) +
        ((T.filter (fun d => ¬ RigidSystem I p W d)).card : ℚ)) / Nat.card F := by
  unfold rigidExceptionExcess
  rw [mean_add, SystemException.mean_finset_sum]
  simp_rw [mean_mul_left]
  calc
    _ ≤ (∑ d ∈ T.filter (RigidSystem I p W),
        max 0 (systemCap I W d - p.threshold) * (1 / Nat.card F)) +
        ((T.filter (fun d => ¬ RigidSystem I p W d)).card : ℚ) / Nat.card F := by
      apply add_le_add _ (nonrigidException_mean_le I p σ W T)
      exact sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
        (systemExceptions_mean I p.toProfileParameters σ W d) (le_max_left _ _))
    _ = _ := by rw [← sum_mul]; ring

/-- The actual joint exception charge has cost at most two field units at
81/80 geometry. This is stronger than independently paying the rigid
capacity budget and the two residual exceptions. -/
theorem fixed_rigidExceptionExcess_mean_le_two
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (ha : p.columnCutoff = 2714) :
    mean (rigidExceptionExcess I p σ W T) ≤ 2 / Nat.card F :=
  (rigidExceptionExcess_mean_le I p σ W T).trans (div_le_div_of_nonneg_right
    (fixed_rigid_excess_add_nonrigid_count_le_two I p W T hT hn hk hs ha) (by positivity))

/-- A whole-block majorant with a single rank charge, one target-excess
budget, and the joint rigid/nonrigid exception charge. -/
noncomputable def rigidBlockCharge (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (D : (tupleCounts I).Index → Prop)
    (T : Finset (systems I.domain I.primary_le W)) (coin : I.layer.Coin) : ℚ :=
  (1 - p.threshold) * indicator (coin.2 ∈ ReducedSystems.badChallenges
      (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask) +
    (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) *
      indicator (systemTarget I p.positive_degree W D d)) +
    rigidExceptionExcess I p σ W T coin

private theorem indicator_or_le (P Q : Prop) : indicator (P ∨ Q) ≤ indicator P + indicator Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [indicator, hp, hq]

theorem localIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (T : Finset (systems I.domain I.primary_le W)) :
    localIncidence I p σ W (T.filter (RigidSystem I p W)) D coin - p.threshold +
      indicator (nonrigidException I p σ W T coin) ≤ rigidBlockCharge I p σ W D T coin := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · have hn₁ : 0 ≤ ∑ d ∈ T.filter (RigidSystem I p W),
        max 0 (systemCap I W d - p.threshold) * indicator (systemTarget I p.positive_degree W D d) :=
      sum_nonneg (fun _ _ => mul_nonneg (le_max_left _ _) (indicator_nonneg _))
    have hn₂ : 0 ≤ ∑ d ∈ T.filter (RigidSystem I p W),
        max 0 (systemCap I W d - p.threshold) *
          indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) :=
      sum_nonneg (fun _ _ => mul_nonneg (le_max_left _ _) (indicator_nonneg _))
    simp only [localIncidence, SystemException.incidence, indicator, hb, not_true_eq_false,
      false_and, if_false, mul_zero, sum_const_zero, if_true, sub_self, zero_mul,
      add_zero, rigidBlockCharge, rigidExceptionExcess, mul_one] at ⊢
    dsimp [indicator] at hn₁ hn₂
    linarith
  · have hh : (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) *
        indicator (systemTarget I p.positive_degree W D d ∨
          coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
      (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) *
        indicator (systemTarget I p.positive_degree W D d)) +
      (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro d _
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (indicator_or_le (systemTarget I p.positive_degree W D d)
          (coin ∈ systemExceptions p.positive_degree I.layout σ d)) (le_max_left _ _)
    simp only [localIncidence, SystemException.incidence, indicator, hb,
      not_false_eq_true, true_and, if_false, sub_zero, one_mul, zero_add,
      rigidBlockCharge, rigidExceptionExcess, mul_zero] at ⊢
    dsimp [indicator] at hh
    simp only [add_sub_cancel_left, ← add_assoc]
    convert add_le_add hh (le_refl (if nonrigidException I p σ W T coin then (1 : ℚ) else 0)) using 1 <;>
      congr 1
    apply sum_congr rfl
    intro d _
    by_cases ht : systemTarget I p.positive_degree W D d <;>
      by_cases he : coin ∈ systemExceptions p.positive_degree I.layout σ d <;> simp [ht, he]
    · intro h
      exact (h he).elim
    · intro h
      exact (he h).elim

theorem responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (hcover : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask → RigidResponseCover I p σ W coin D S T) :
    responseIncidence I p σ W coin S - p.threshold +
      indicator (nonrigidException I p σ W T coin) ≤ rigidBlockCharge I p σ W D T coin := by
  have hh := responseIncidence_le_localIncidence_of_rigid_cover I p σ W coin D S
    (T.filter (RigidSystem I p W)) (by
      intro hb u hu
      obtain ⟨hh, d, hd, hr, ha, he⟩ := hcover hb u hu
      exact ⟨hh, d, mem_filter.mpr ⟨hd, hr⟩, hr, ha, he⟩)
  exact (add_le_add (sub_le_sub_right hh p.threshold)
    (le_refl (indicator (nonrigidException I p σ W T coin)))).trans
    (localIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge I p σ W coin D T)

/-- Target fan-out costs its total excess once. At the fixed geometry,
the child block therefore has rate `(1-theta)*(mu+rate)+2/q`; the target
rate is not multiplied by the number of high child systems. -/
theorem fixed_rigidBlockCharge_mean_le
    {Z : Type} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (rate : ℚ) (hr0 : 0 ≤ rate)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (ha : p.columnCutoff = 2714) :
    mean (fun z => mean (rigidBlockCharge I p (σ z) W (D z) T)) ≤
      (1 - p.threshold) * (p.toProfileParameters.rankError + rate) + 2 / Nat.card F := by
  have ht : 0 ≤ 1 - p.threshold := sub_nonneg.mpr p.threshold_lt_one.le
  have hrank := mul_le_mul_of_nonneg_left (rank_bad_mean I p.toProfileParameters W) ht
  have htargets (d : systems I.domain I.primary_le W) :
      mean (fun z => indicator (systemTarget I p.positive_degree W (D z) d)) ≤ rate := by
    by_cases hf : Affine.consistent (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 = univ
    · simpa only [systemTarget, exists_prop_of_true hf] using
        hD (systemLabel I p.positive_degree W d hf)
    · have he (z : Z) : ¬ systemTarget I p.positive_degree W (D z) d := fun ⟨h, _⟩ => hf h
      simpa only [indicator, if_neg (he _), mean_const] using hr0
  have htarget : mean (fun z => ∑ d ∈ T.filter (RigidSystem I p W),
      max 0 (systemCap I W d - p.threshold) * indicator (systemTarget I p.positive_degree W (D z) d)) ≤
        (1 - p.threshold) * rate := by
    rw [SystemException.mean_finset_sum]
    simp_rw [mean_mul_left]
    calc
      _ ≤ ∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold) * rate :=
        sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (htargets d) (le_max_left _ _))
      _ = (∑ d ∈ T.filter (RigidSystem I p W), max 0 (systemCap I W d - p.threshold)) * rate :=
        (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (systemCap_excess_of_hahn I p W _
        ((card_filter_le _ _).trans hT)) hr0
  have hexception : mean (fun z => mean (rigidExceptionExcess I p (σ z) W T)) ≤ 2 / Nat.card F := by
    exact (mean_mono (fun z => fixed_rigidExceptionExcess_mean_le_two I p (σ z) W T hT
      hn hk hs ha)).trans_eq (mean_const _)
  unfold rigidBlockCharge
  simp_rw [mean_add, mean_const, mean_mul_left]
  linarith

end RecursivePolygero.ProfileAnalysis
