import polygero.Local.Parameters
import polygero.Algebra.Counting.BinomialExcess
import polygero.Local.Recovery
import polygero.Algebra.Counting.RandomTarget
import polygero.Local.OutputTarget

/-! A fixed envelope bounds every response whose extraction fails or hits a target. -/
namespace RecursivePolygero.ProfileAnalysis
open Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The query fraction allowing for the good columns omitted from a core closure. -/
noncomputable def systemCap (I : Instance F) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) : ℚ :=
  ((ReducedSystems.capacity (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask d.1).choose I.t : ℚ)/Fintype.card I.layer.Query


noncomputable def localEnvelope (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (θ : ℚ)
    (D : (tupleCounts I).Index → Prop) (coin : I.layer.Coin) : ℚ :=
  envelope (systemCap I W)
    (fun d => systemTarget I p.positive_degree W D d ∨
      coin ∈ systemExceptions p.positive_degree I.layout σ d)
    (coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) θ

theorem localEnvelope_bounds (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (θ : ℚ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (D : (tupleCounts I).Index → Prop)
    (coin : I.layer.Coin) : 0 ≤ localEnvelope I p σ W θ D coin ∧ localEnvelope I p σ W θ D coin ≤ 1 := by
  refine ⟨hθ0.trans (le_envelope _ _ _ _ hθ1),envelope_le_one _ _ _ _ hθ1 ?_⟩
  intro d
  unfold systemCap
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
  apply (div_le_one (by exact_mod_cast Nat.choose_pos I.query_le)).mpr
  exact_mod_cast Nat.choose_le_choose I.t (ReducedSystems.capacity_le_n
    (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1)

/-- The direct overlap bound applies to actual capacity-maximizing sets.
The witnesses are already in the fixed family; no coordinates are added. -/
theorem systemCap_excess (I : Instance F) (p : ProfileParameters I) (W : I.layer.Oracle)
    (θ : ℚ) (hθ : θ ≤ 1)
    (hcondition : DiscreteThreshold.Condition (Nat.card F) p.overlapRatio θ)
    (T : Finset (systems I.domain I.primary_le W)) (hTq : T.card ≤ Nat.card F) :
    ∑ d ∈ T, max 0 (systemCap I W d-θ) ≤ 1-θ := by
  let witnesses := fun d : systems I.domain I.primary_le W => ReducedSystems.capacity_witness
    (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 d.2
  let E := fun d => Classical.choose (witnesses d)
  have hspec (d : systems I.domain I.primary_le W) :
      E d ∈ ReducedSystems.associatedSets (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 ∧
      (E d).card = ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 := Classical.choose_spec (witnesses d)
  have h := DirectBinomial.normalized_excess_le (univ : Finset (Fin I.n)) T E
    I.t p.overlapSize (Nat.card F) θ (by simpa using Nat.choose_pos I.query_le) hθ
    (fun _ _ => subset_univ _)
    (fun d _ e _ hne => by
      simpa only [ProfileParameters.overlapSize] using (ReducedSystems.associated_intersection
        (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask
        p.positive_degree d.1 e.1 (E d) (E e) (hspec d).1 (hspec e).1
          (fun he => hne (Subtype.ext he))))
    (by simpa only [card_univ,Fintype.card_fin,ProfileParameters.overlapRatio] using hcondition) hTq
  have hcard := fun d => (hspec d).2
  simpa only [card_univ,Fintype.card_fin,hcard,systemCap,
    show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] using h


theorem systemExceptions_mean (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) :
    mean (fun coin : I.layer.Coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
      1/(Nat.card F : ℚ) := by
  classical
  dsimp only [Instance.layer] at *
  rw [mean_indicator]
  simp only [filter_mem_eq_inter,univ_inter]
  apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos)
    (by exact_mod_cast Nat.card_pos (α := F))).mpr
  have h := systemExceptions_card p.positive_degree I.layout σ d
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have h' := (Nat.cast_le (α := ℚ)).mpr h
  push_cast at h'
  convert! h' using 1 <;> simp only [one_mul,← Nat.card_eq_fintype_card]

theorem rank_bad_mean (I : Instance F) (p : ProfileParameters I) (W : I.layer.Oracle) :
    mean (fun coin : I.layer.Coin => indicator (coin.2 ∈ ReducedSystems.badChallenges
      (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask)) ≤ p.rankError := by
  classical
  dsimp only [Instance.layer] at *
  change mean (fun coin : (I.Equations → F) × Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (coin.2 ∈ _)) ≤ _
  have hm := mean_snd (I := I.Equations → F) (fun B : Challenge F (rowCount I.nw I.nq) I.s =>
    indicator (B ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask))
  calc
    _ = _ := hm
    _ ≤ p.rankError := by
      rw [mean_indicator]
      simp only [filter_mem_eq_inter,univ_inter]
      unfold ProfileParameters.rankError
      apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos)
        (pow_pos (by exact_mod_cast Nat.card_pos (α := F)) _)).mpr
      have h := ReducedSystems.badChallenges_card (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask
      rw [Nat.card_eq_fintype_card (α := Challenge F (rowCount I.nw I.nq) I.s)] at h
      exact_mod_cast h

/-- The oracle, systems, and witness labels are fixed before the target randomness. -/
theorem localEnvelope_mean {Z : Type*} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : ProfileParameters I)
    (σ : Z → I.layer.Statement) (W : I.layer.Oracle) (θ r : ℚ) (hθ : θ ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hμ : p.rankError+1/(Nat.card F : ℚ) ≤ 1)
    (hcondition : DiscreteThreshold.Condition (Nat.card F) p.overlapRatio θ)
    (D : Z → (tupleCounts I).Index → Prop)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ r) :
    mean (fun z => mean (localEnvelope I p (σ z) W θ (D z))) ≤
      profile (Nat.card F) p.rankError θ+(1-profile (Nat.card F) p.rankError θ)*r := by
  exact SystemException.random_target_envelope_mean (systemCap I W)
    (fun z d => systemTarget I p.positive_degree W (D z) d)
    (fun z coin d => coin ∈ systemExceptions p.positive_degree I.layout (σ z) d)
    (fun coin => coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) θ p.rankError r (Nat.card F)
    Nat.card_pos hθ hr0 hr1 hμ (rank_bad_mean I p W)
    (fun d => by
      by_cases hfull : Affine.consistent (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask d.1 = univ
      · simpa only [systemTarget,exists_prop_of_true hfull] using
          hD (systemLabel I p.positive_degree W d hfull)
      · have he (z : Z) : ¬ systemTarget I p.positive_degree W (D z) d :=
          fun ⟨h,_⟩ => hfull h
        simpa only [indicator,if_neg (he _),mean_const] using hr0)
    (fun z => systemExceptions_mean I p (σ z) W)
    (fun T hTq => systemCap_excess I p W θ hθ hcondition T hTq)

theorem responseCount_le_columns (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) (payload : I.layer.Payload) :
    responseCount I.layer σ W coin payload ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload).card.choose I.t := by
  rw [← card_queriesWithin]
  apply card_le_card
  intro Q hQ
  exact mem_filter.mpr ⟨mem_univ _,((verify_openOracle_iff I.domain (by have := I.primary_le; omega)
    I.primary_le I.layout σ W coin payload Q).mp (mem_filter.mp hQ).2).2⟩

theorem response_fraction_le_envelope (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (θ : ℚ)
    (hfloor : p.columnFloor ≤ θ) (hθ : θ ≤ 1)
    (D : (tupleCounts I).Index → Prop)
    (coin : I.layer.Coin) (payload : I.layer.Payload)
    (hout : outputHit D (scanRecoverAt I σ W coin payload)) :
    (responseCount I.layer σ W coin payload : ℚ)/Fintype.card I.layer.Query ≤
      localEnvelope I p σ W θ D coin := by
  classical
  let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload
  have hN : (0 : ℚ) < Fintype.card I.layer.Query := by exact_mod_cast Fintype.card_pos
  have hcount : (responseCount I.layer σ W coin payload : ℚ)/Fintype.card I.layer.Query ≤
      (G.card.choose I.t : ℚ)/Fintype.card I.layer.Query :=
    div_le_div_of_nonneg_right (by exact_mod_cast responseCount_le_columns I σ W coin payload) hN.le
  have hzero : 0 ≤ localEnvelope I p σ W θ D coin :=
    (localEnvelope_bounds I p σ W θ (p.columnFloor_nonneg.trans hfloor) hθ D coin).1
  by_cases hglobal : globalCheck I.domain I.layout σ coin.1 payload
  · unfold localEnvelope envelope
    split_ifs with hbad
    · exact (div_le_one hN).mpr (by exact_mod_cast card_le_univ (univ.filter (I.layer.verify σ W coin payload)))
    · by_cases hlarge : p.largeSize ≤ G.card
      · have hc : I.r+I.w+I.s+I.s+1 ≤ G.card := (le_max_left _ _).trans hlarge
        have h2k : 2*(I.r+I.w)+I.s ≤ G.card := (le_max_right _ _).trans hlarge
        obtain ⟨d,hd,he⟩ := large_response I p.positive_degree σ W coin payload hglobal hbad hc h2k
        have hel : systemTarget I p.positive_degree W D d ∨
            coin ∈ systemExceptions p.positive_degree I.layout σ d := by
          rcases he with he | hrec
          · exact Or.inr he
          · obtain ⟨hfull,hrec⟩ := hrec
            exact Or.inl ⟨hfull,by simpa only [hrec,outputHit] using hout⟩
        dsimp only [Instance.layer] at *
        apply hcount.trans
        apply le_trans _ (SystemException.entry_le_maximum _ _ _ d hel)
        apply div_le_div_of_nonneg_right _ hN.le
        exact_mod_cast Nat.choose_le_choose I.t hd
      · apply hcount.trans
        apply le_trans _ (hfloor.trans (SystemException.le_maximum _ _ _))
        unfold ProfileParameters.columnFloor
        rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose I.t (show G.card ≤ p.largeSize-1 by omega)) (by positivity)
  · have he : responseCount I.layer σ W coin payload = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      exact hglobal ((verify_openOracle_iff I.domain (by have := I.primary_le; omega)
        I.primary_le I.layout σ W coin payload Q).mp (mem_filter.mp hQ).2).1
    simpa only [he,Nat.cast_zero,zero_div] using hzero

/-- The response is fixed before the query; the envelope is independent of that response. -/
theorem family_response_mean (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (θ : ℚ)
    (hfloor : p.columnFloor ≤ θ) (hθ : θ ≤ 1)
    (D : (tupleCounts I).Index → Prop)
    (coin : I.layer.Coin) (payload : I.layer.Payload) :
    mean (fun Q : I.layer.Query => indicator (I.layer.verify σ W coin payload Q ∧
      outputHit D (scanRecoverAt I σ W coin payload))) ≤ localEnvelope I p σ W θ D coin := by
  by_cases hout : outputHit D (scanRecoverAt I σ W coin payload)
  · simpa only [hout,and_true,mean_indicator,responseCount] using
      response_fraction_le_envelope I p σ W θ hfloor hθ D coin payload hout
  · simpa only [hout,and_false,indicator,if_false,mean_const] using
      (localEnvelope_bounds I p σ W θ (p.columnFloor_nonneg.trans hfloor) hθ D coin).1

end RecursivePolygero.ProfileAnalysis
