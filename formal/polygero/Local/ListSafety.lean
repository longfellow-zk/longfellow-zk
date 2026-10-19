import polygero.Local.ResponseRigidity

/-! Fixed high-capacity lists, including proper systems, and a Boolean
exception cover. This deliberately pays list size in exchange for a
uniform bound outside the exceptional challenge event. -/

namespace RecursivePolygero.ProfileAnalysis

open Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def highSystems (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) : Finset (systems I.domain I.primary_le W) :=
  univ.filter (fun d => p.threshold < systemCap I W d)

/-- The small-family alternative in `active_bound` is insufficient in
general. A certified list bound strictly below the field size excludes it
and yields an actual global list bound. -/
theorem highSystems_card_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (W : I.layer.Oracle) :
    (highSystems I p W).card ≤ p.listBound := by
  have hb : CodingTheory.UniformFamilyBound I.n p.columnCutoff p.overlapSize p.listBound := by
    rcases p.active_bound with h | h
    · exact h
    · omega
  let E := fun d : systems I.domain I.primary_le W =>
    Classical.choose (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hs (d : systems I.domain I.primary_le W) :=
    Classical.choose_spec (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  apply DirectBinomial.active_card_le_of_uniformFamilyBound (highSystems I p W) E
    p.columnCutoff p.overlapSize p.listBound p.overlap_lt_cutoff _ _ hb
  · intro d hd
    have hh := (mem_filter.mp hd).2
    unfold systemCap at hh
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] at hh
    have hsize := DirectBinomial.size_ge_of_choose_div_gt (Nat.choose_pos I.query_le) p.floor_le hh
    exact (hs d).2 ▸ hsize
  · intro d _ e _ hne
    exact ReducedSystems.associated_intersection (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask p.positive_degree d.1 e.1 (E d) (E e)
      (hs d).1 (hs e).1 (fun h => hne (Subtype.ext h))

def listBad (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) : Prop :=
  coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask ∨
    ∃ d ∈ highSystems I p W, coin ∈ systemExceptions p.positive_degree I.layout sigma d

noncomputable def listError (I : Instance F) (p : HahnSystemCertificate I) : ℚ :=
  p.toProfileParameters.rankError + p.listBound / (Nat.card F : ℚ)

omit [Fintype F] [DecidableEq F] in
theorem listError_nonneg (I : Instance F) (p : HahnSystemCertificate I) : 0 ≤ listError I p := by
  unfold listError ProfileParameters.rankError
  positivity

theorem listBad_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (sigma : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun coin => indicator (listBad I p sigma W coin)) ≤ listError I p := by
  have hi (coin : I.layer.Coin) : indicator (listBad I p sigma W coin) ≤
      indicator (coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask) +
      ∑ d ∈ highSystems I p W, indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d) := by
    by_cases h : listBad I p sigma W coin
    · rw [indicator, if_pos h]
      rcases h with h | ⟨d, hd, he⟩
      · have hn := sum_nonneg (s := highSystems I p W) (fun d _ =>
          indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout sigma d))
        simp only [indicator, if_pos h] at hn ⊢
        linarith
      · have hs := single_le_sum (fun d (_ : d ∈ highSystems I p W) =>
          indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) hd
        rw [indicator, if_pos he] at hs
        exact hs.trans (le_add_of_nonneg_left (indicator_nonneg _))
    · rw [indicator, if_neg h]
      exact add_nonneg (indicator_nonneg _) (sum_nonneg (fun _ _ => indicator_nonneg _))
  calc
    _ ≤ _ := mean_mono hi
    _ = _ := mean_add _ _
    _ ≤ p.toProfileParameters.rankError +
        ∑ _d ∈ highSystems I p W, (1 : ℚ) / Nat.card F := by
      apply add_le_add (rank_bad_mean I p.toProfileParameters W)
      rw [SystemException.mean_finset_sum]
      exact sum_le_sum fun d _ => systemExceptions_mean I p.toProfileParameters sigma W d
    _ ≤ listError I p := by
      simp only [sum_const, nsmul_eq_mul, listError]
      have hc : ((highSystems I p W).card : ℚ) ≤ p.listBound := by
        exact_mod_cast highSystems_card_le I p hsmall W
      have hq : (0 : ℚ) ≤ Nat.card F := by positivity
      simpa only [div_eq_mul_inv, one_mul] using
        add_le_add le_rfl (div_le_div_of_nonneg_right hc hq)

/-- Outside the global exception cover the empty-target envelope is just
the threshold. This is uniform over all eventual responses. -/
theorem envelope_le_threshold_of_not_listBad
    (I : Instance F) (p : HahnSystemCertificate I) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (hn : ¬ listBad I p sigma W coin) :
    localEnvelope I p.toProfileParameters sigma W p.threshold (fun _ => False) coin ≤ p.threshold := by
  have hr := fun h => hn (Or.inl h)
  unfold localEnvelope envelope
  rw [if_neg hr]
  apply SystemException.maximum_le _ _ _ _ le_rfl
  intro d hd
  by_contra hh
  have he : coin ∈ systemExceptions p.positive_degree I.layout sigma d := by
    rcases hd with h | h
    · obtain ⟨_, hf⟩ := h
      exact hf.elim
    · exact h
  exact hn (Or.inr ⟨d, mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hh⟩, he⟩)

/-- Every high target response is either covered by the exception event
(including proper systems), or by a fixed full-system target label. -/
theorem high_target_list_cover (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (u : I.layer.Payload) (D : (tupleCounts I).Index → Prop)
    (hh : p.threshold < (responseCount I.layer sigma W coin u : ℚ) / Fintype.card I.layer.Query)
    (ht : outputHit D (scanRecoverAt I sigma W coin u)) :
    listBad I p sigma W coin ∨ ∃ d ∈ highSystems I p W,
      systemTarget I p.positive_degree W D d := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · exact Or.inl (Or.inl hb)
  obtain ⟨d, ha, he⟩ := high_target_response_cases I p sigma W coin u D hh ht hb
  have hd : d ∈ highSystems I p W := mem_filter.mpr ⟨mem_univ _,
    hh.trans_le (assigned_response_fraction_le I sigma W coin u d ha)⟩
  rcases he with ⟨_, he⟩ | ⟨_, ht | he⟩
  · exact Or.inl (Or.inr ⟨d, hd, he⟩)
  · exact Or.inr ⟨d, hd, ht⟩
  · exact Or.inl (Or.inr ⟨d, hd, he⟩)

end RecursivePolygero.ProfileAnalysis
