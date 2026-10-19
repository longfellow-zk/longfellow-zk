import polygero.Local.Incidence
import polygero.Local.ResponseAssignment

/-!
# Full-system response rigidity and excess charging

The statement and challenge are fixed. Two sufficiently large responses
assigned to the same fully consistent system are equal as actual payloads.
Thus summing their excess query probabilities does not cost the size of the
payload space. Proper systems are deliberately excluded from this lemma.
-/

namespace RecursivePolygero.ProfileAnalysis

open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Primary uniqueness needs only the assigned equations and the system's
size. It does not need full consistency of the system. -/
theorem assigned_primary_unique (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (u v : I.layer.Payload)
    (d : systems I.domain I.primary_le W)
    (hu : ResponseAssignment I σ W coin u d) (hv : ResponseAssignment I σ W coin v d) :
    u.primary = v.primary := by
  apply Subtype.ext
  have hs := (geometry d).core.large
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq d.1
    (primaryCode I.domain I.primary_le).node_injective.injOn
  · exact (mem_degreeLT.mp u.primary.2).trans_le (by exact_mod_cast (show I.r + I.w + I.s ≤ d.1.card by omega))
  · exact (mem_degreeLT.mp v.primary.2).trans_le (by exact_mod_cast (show I.r + I.w + I.s ≤ d.1.card by omega))
  · intro j hj
    have h₁ := hu.primary j hj
    have h₂ := hv.primary j hj
    change (u.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j) -
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j = W.proximityMask j at h₁
    change (v.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j) -
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j = W.proximityMask j at h₂
    exact sub_left_injective (h₁.trans h₂.symm)

theorem assigned_arithmetic_canonical (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (d : systems I.domain I.primary_le W)
    (hfull : Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ)
    (hu : ResponseAssignment I σ W coin u d)
    (hlarge : 2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card) :
    u.arithmetic = (responseSemantics I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ coin.1).canonical 0 (rows hk d hfull) := by
  let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u
  have hsize : 2 * (I.r + I.w) ≤ (G ∩ d.1).card := by
    have h := card_sdiff_add_card_inter G d.1
    have hh := hu.omitted
    change (G \ d.1).card ≤ I.s at hh
    change 2 * (I.r + I.w) + I.s ≤ G.card at hlarge
    omega
  exact (identities_of_agreement (by have := I.primary_le; omega)
    I.layout σ coin u (rows hk d hfull) (G ∩ d.1) hk hsize inter_subset_left
    (fun i j hj => rows_spec hk d hfull i j (mem_inter.mp hj).2)).1

/-- Full payload equality, not merely equivalence of verifier behavior. -/
theorem assigned_payload_unique (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u v : I.layer.Payload)
    (d : systems I.domain I.primary_le W)
    (hfull : Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ)
    (hu : ResponseAssignment I σ W coin u d) (hv : ResponseAssignment I σ W coin v d)
    (hlu : 2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card)
    (hlv : 2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin v).card) :
    u = v := by
  have hp := assigned_primary_unique I σ W coin u v d hu hv
  have ha := (assigned_arithmetic_canonical I hk σ W coin u d hfull hu hlu).trans
    (assigned_arithmetic_canonical I hk σ W coin v d hfull hv hlv).symm
  cases u; cases v
  simp_all

theorem assigned_response_fraction_le (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (d : systems I.domain I.primary_le W) (hu : ResponseAssignment I σ W coin u d) :
    (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query ≤ systemCap I W d := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (responseCount_le_columns I σ W coin u).trans (Nat.choose_le_choose I.t hu.capacity)

/-- At a fixed challenge, a response family assigned into fixed full systems
has at most one response per system. Only the excess is summed; the base
must be charged once separately by the FS proof. -/
theorem full_response_excess_le (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (theta : ℚ)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (label : I.layer.Payload → systems I.domain I.primary_le W)
    (hmem : ∀ u ∈ S, label u ∈ T)
    (hfull : ∀ u ∈ S, Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask (label u).1 = univ)
    (ha : ∀ u ∈ S, ResponseAssignment I σ W coin u (label u))
    (hlarge : ∀ u ∈ S, 2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card) :
    (∑ u ∈ S, max 0 ((responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query - theta)) ≤ ∑ d ∈ T, max 0 (systemCap I W d - theta) := by
  have hinj : Set.InjOn label S := by
    intro u hu v hv he
    exact assigned_payload_unique I hk σ W coin u v (label u) (hfull u hu)
      (ha u hu) (he ▸ ha v hv) (hlarge u hu) (hlarge v hv)
  calc
    _ ≤ ∑ u ∈ S, max 0 (systemCap I W (label u) - theta) := by
      apply sum_le_sum
      intro u hu
      exact max_le_max_left 0 (sub_le_sub_right (assigned_response_fraction_le I σ W coin u _ (ha u hu)) theta)
    _ = ∑ d ∈ S.image label, max 0 (systemCap I W d - theta) :=
      (sum_image (f := fun d => max 0 (systemCap I W d - theta)) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by intro d hd; obtain ⟨u, hu, rfl⟩ := mem_image.mp hd; exact hmem u hu)
      (fun _ _ _ => le_max_left _ _)

/-- Existential coverage permits an empty system family; no artificial
default system or total assignment is required from callers. -/
theorem full_response_excess_le_of_cover (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (theta : ℚ)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (hcover : ∀ u ∈ S, ∃ d ∈ T,
      Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 = univ ∧
      ResponseAssignment I σ W coin u d ∧
      2 * (I.r + I.w) + I.s ≤
        (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card) :
    (∑ u ∈ S, max 0 ((responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query - theta)) ≤ ∑ d ∈ T, max 0 (systemCap I W d - theta) := by
  by_cases hS : S = ∅
  · simp only [hS, sum_empty]
    exact sum_nonneg (fun _ _ => le_max_left _ _)
  obtain ⟨u₀, hu₀⟩ := nonempty_iff_ne_empty.mpr hS
  let fallback := (hcover u₀ hu₀).choose
  let label (u : I.layer.Payload) := if hu : u ∈ S then (hcover u hu).choose else fallback
  have hs (u : I.layer.Payload) (hu : u ∈ S) :
      label u ∈ T ∧
      Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask (label u).1 = univ ∧
      ResponseAssignment I σ W coin u (label u) ∧
      2 * (I.r + I.w) + I.s ≤
        (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card := by
    simpa only [label, dif_pos hu] using (hcover u hu).choose_spec
  exact full_response_excess_le I hk σ W coin theta S T label
    (fun u hu => (hs u hu).1) (fun u hu => (hs u hu).2.1)
    (fun u hu => (hs u hu).2.2.1) (fun u hu => (hs u hu).2.2.2)

/-- The response sum includes only excess above the threshold. Rank and
base contributions each occur once, independently of the response count. -/
noncomputable def responseIncidence (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (S : Finset I.layer.Payload) : ℚ :=
  if coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask then 1 else
    p.threshold + ∑ u ∈ S, max 0 ((responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query - p.threshold)

def FullResponseCover (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W)) : Prop :=
  ∀ u ∈ S, ∃ d ∈ T,
    Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 = univ ∧
    ResponseAssignment I σ W coin u d ∧
    (2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card) ∧
    (systemTarget I p.positive_degree W D d ∨ coin ∈ systemExceptions p.positive_degree I.layout σ d)

/-- All responses whose full-system incidence is covered by `T`, including
systems exceptional for this statement. This is an actual finite response
set, not a response-rigidity assumption supplied by the caller. -/
noncomputable def coveredFullResponses (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop) (T : Finset (systems I.domain I.primary_le W)) : Finset I.layer.Payload :=
  univ.filter (fun u => ∃ d ∈ T,
    Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 = univ ∧
    ResponseAssignment I σ W coin u d ∧
    (2 * (I.r + I.w) + I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card) ∧
    (systemTarget I p.positive_degree W D d ∨ coin ∈ systemExceptions p.positive_degree I.layout σ d))

theorem coveredFullResponses_cover (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop) (T : Finset (systems I.domain I.primary_le W)) :
    FullResponseCover I p σ W coin D (coveredFullResponses I p σ W coin D T) T := by
  intro u hu
  exact (mem_filter.mp hu).2

theorem responseIncidence_le_localIncidence (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (D : (tupleCounts I).Index → Prop)
    (S : Finset I.layer.Payload) (T : Finset (systems I.domain I.primary_le W))
    (hcover : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask → FullResponseCover I p σ W coin D S T) :
    responseIncidence I p σ W coin S ≤ localIncidence I p σ W T D coin := by
  by_cases hb : coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  · simp [responseIncidence, localIncidence, SystemException.incidence, indicator, hb]
  · let active := fun d => systemTarget I p.positive_degree W D d ∨
        coin ∈ systemExceptions p.positive_degree I.layout σ d
    have hc := full_response_excess_le_of_cover I p.positive_degree σ W coin p.threshold S
      (T.filter active) (by
        intro u hu
        obtain ⟨d, hd, hf, ha, hl, he⟩ := hcover hb u hu
        exact ⟨d, mem_filter.mpr ⟨hd, he⟩, hf, ha, hl⟩)
    simp only [responseIncidence, hb, if_false, localIncidence, SystemException.incidence,
      indicator, not_false_eq_true, true_and, sub_zero, one_mul, zero_add] at ⊢
    apply add_le_add le_rfl
    simp only [sum_filter, active, mul_ite, mul_one, mul_zero] at hc ⊢
    convert hc using 1 <;> congr 1

/-- The response family may be selected after both target randomness and
the challenge. Its covering system family must be fixed beforehand. -/
theorem responseIncidence_mean_of_hahn {Z : Type} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : HahnSystemCertificate I)
    (σ : Z → I.layer.Statement) (W : I.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop)
    (S : Z → I.layer.Coin → Finset I.layer.Payload)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (rate : ℚ) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (hcover : ∀ z coin, coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask → FullResponseCover I p (σ z) W coin (D z) (S z coin) T) :
    mean (fun z => mean (fun coin => responseIncidence I p (σ z) W coin (S z coin))) ≤
      p.error + (1 - p.error) * rate := by
  exact (mean_mono (fun z => mean_mono (fun coin =>
    responseIncidence_le_localIncidence I p (σ z) W coin (D z) (S z coin) T (hcover z coin)))).trans
      (localIncidence_mean_of_hahn I p σ W T hT rate hr0 hr1 D hD)

/-- A genuinely high query probability forces the geometric large-set
premises, rather than assuming that every accepted response is large. -/
theorem high_response_large (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (hh : p.threshold < (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query) :
    globalCheck I.domain I.layout σ coin.1 u ∧ p.largeSize ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u).card := by
  have hpos : 0 < responseCount I.layer σ W coin u := by
    by_contra hn
    have hz : responseCount I.layer σ W coin u = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hh
    exact (not_lt_of_ge p.threshold_nonneg) hh
  obtain ⟨q, hq⟩ := card_pos.mp hpos
  have hg := ((verify_openOracle_iff I.domain (by have := I.primary_le; omega)
    I.primary_le I.layout σ W coin u q).mp (mem_filter.mp hq).2).1
  refine ⟨hg, ?_⟩
  have hcount := div_le_div_of_nonneg_right
    (Nat.cast_le (α := ℚ).mpr (responseCount_le_columns I σ W coin u))
    (show (0 : ℚ) ≤ Fintype.card I.layer.Query by positivity)
  have hhigh := hh.trans_le hcount
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] at hhigh
  exact DirectBinomial.size_ge_of_choose_div_gt (Nat.choose_pos I.query_le)
    p.columnFloor_le hhigh

/-- Concrete coverage of every high, target-hitting response outside the
rank event. Proper systems are exceptional, but are not declared rigid.
The full branch is precisely the branch covered by the incidence theorem. -/
theorem high_target_response_cases (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (D : (tupleCounts I).Index → Prop)
    (hh : p.threshold < (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query)
    (htarget : outputHit D (scanRecoverAt I σ W coin u))
    (hbad : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) :
    ∃ d : systems I.domain I.primary_le W, ResponseAssignment I σ W coin u d ∧
      ((Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 ≠ univ ∧
          coin ∈ systemExceptions p.positive_degree I.layout σ d) ∨
        (Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1 = univ ∧
          (systemTarget I p.positive_degree W D d ∨ coin ∈ systemExceptions p.positive_degree I.layout σ d))) := by
  obtain ⟨hg, hl⟩ := high_response_large I p σ W coin u hh
  obtain ⟨d, ha, he⟩ := large_response_assigned I p.positive_degree σ W coin u hg hbad
    ((le_max_left _ _).trans hl) ((le_max_right _ _).trans hl)
  refine ⟨d, ha, ?_⟩
  by_cases hf : Affine.consistent (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 = univ
  · right
    refine ⟨hf, ?_⟩
    rcases he with he | ⟨hf', hr⟩
    · exact Or.inr he
    · exact Or.inl ⟨hf', by simpa only [hr, outputHit] using htarget⟩
  · left
    refine ⟨hf, ?_⟩
    rcases he with he | ⟨hf', _⟩
    · exact he
    · exact (hf hf').elim

/-- Proper systems are charged as exception events, without asserting
uniqueness of their arithmetic responses. -/
def properException (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (coin : I.layer.Coin) : Prop :=
  ∃ d ∈ T, Affine.consistent (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask d.1 ≠ univ ∧
    coin ∈ systemExceptions p.positive_degree I.layout σ d

/-- Every high target response is covered by a full-system response
incidence or by a proper-system exception. The remaining family-coverage
premise refers to systems of high capacity, not to individual payloads. -/
theorem high_target_covered_or_proper (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload)
    (D : (tupleCounts I).Index → Prop) (T : Finset (systems I.domain I.primary_le W))
    (hT : ∀ d, p.threshold < systemCap I W d → d ∈ T)
    (hh : p.threshold < (responseCount I.layer σ W coin u : ℚ) / Fintype.card I.layer.Query)
    (htarget : outputHit D (scanRecoverAt I σ W coin u))
    (hbad : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) :
    u ∈ coveredFullResponses I p σ W coin D T ∨ properException I p σ W T coin := by
  obtain ⟨d, ha, he⟩ := high_target_response_cases I p σ W coin u D hh htarget hbad
  have hd := hT d (hh.trans_le (assigned_response_fraction_le I σ W coin u d ha))
  rcases he with ⟨hn, he⟩ | ⟨hf, he⟩
  · exact Or.inr ⟨d, hd, hn, he⟩
  · have hl := (high_response_large I p σ W coin u hh).2
    exact Or.inl (mem_filter.mpr ⟨mem_univ _, d, hd, hf, ha, (le_max_right _ _).trans hl, he⟩)

/-- An explicit response-free price for the residual proper-system branch.
The bound can be loose: it is a union over systems, with no payload factor. -/
theorem properException_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) :
    mean (fun coin => indicator (properException I p σ W T coin)) ≤
      ((T.filter (fun d => Affine.consistent (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 ≠ univ)).card : ℚ) / Nat.card F := by
  let P := T.filter (fun d => Affine.consistent (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask d.1 ≠ univ)
  have hi (coin : I.layer.Coin) : indicator (properException I p σ W T coin) ≤
      ∑ d ∈ P, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) := by
    by_cases he : properException I p σ W T coin
    · obtain ⟨d, hd, hn, he'⟩ := he
      have hs := single_le_sum
        (fun d (_ : d ∈ P) => indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
        (show d ∈ P from mem_filter.mpr ⟨hd, hn⟩)
      simpa only [indicator, if_pos (show properException I p σ W T coin from ⟨d, hd, hn, he'⟩), if_pos he'] using hs
    · simpa only [indicator, if_neg he] using sum_nonneg
        (s := P) (fun d _ => indicator_nonneg (coin ∈ systemExceptions p.positive_degree I.layout σ d))
  calc
    _ ≤ mean (fun coin => ∑ d ∈ P, indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) := mean_mono hi
    _ = ∑ d ∈ P, mean (fun coin => indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) :=
      SystemException.mean_finset_sum P _
    _ ≤ ∑ _d ∈ P, (1 : ℚ) / Nat.card F :=
      sum_le_sum (fun d _ => systemExceptions_mean I p.toProfileParameters σ W d)
    _ = _ := by simp [P, div_eq_mul_inv]

end RecursivePolygero.ProfileAnalysis
