import Lfzk.ZkPotentialBalance
import LigeroFamily.Soundness.Hypergeometric
import LigeroFamily.Protocol.Finite
import LigeroFamily.Soundness.ResponsePairCounting

/-!
# Balanced hash-answer counting for a family of complete responses

Each complete response has its own query hash input.  The mass bound below
charges all of those inputs together.  It keeps the response sum outside the
challenge/query decoder calculation, so no maximum-response or list-size
factor appears.  A protocol-specific proof supplies the query envelope and
the response-mass bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace Lfzk.ResponsePairMass

open Finset
open LigeroFamily
open scoped Classical

/-- Compatibility entry point for the generic adaptive-response pair bound. -/
theorem adaptive_response_pair_ratio_le
    {C Response : Type*} [Fintype C] [Nonempty C] [Fintype Response]
    (low high : C → Response → C → Prop) (respond : C → Response)
    (lowBudget highBudget : ℚ)
    (hlow : ∀ a response,
      (∑ b : C, if low a response b then (1 : ℚ) else 0) ≤
        Fintype.card C * lowBudget)
    (hhigh : (∑ response : Response, ∑ a : C, ∑ b : C,
      if high a response b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * highBudget) :
    (∑ a : C, ∑ b : C,
      if low a (respond a) b ∨ high a (respond a) b
      then (1 : ℚ) else 0) / (Fintype.card C : ℚ) ^ 2 ≤
        lowBudget + highBudget :=
  LigeroFamily.ResponsePairCounting.adaptive_response_pair_ratio_le
    low high respond lowBudget highBudget hlow hhigh

/-- High-agreement cost and event. Keeping these named prevents the FS
decoder proof from repeatedly expanding a protocol-specific acceptance
predicate while checking its finite-sum type. -/
def highCover (cutoff a n r : ℕ) : ℚ :=
  if cutoff < a then hypergeometricRatio a n r else 0

def highEvent {Challenge Response : Type*} {n r cutoff : ℕ}
    (good : Challenge → Response → Finset (Fin n))
    (accepts : Challenge → Response → QuerySet n r → Prop)
    (challenge : Challenge) (response : Response) (query : QuerySet n r) : Prop :=
  cutoff < (good challenge response).card ∧ accepts challenge response query

/-- A response-mass bound transfers to all raw hash-answer pairs.  The
response is held fixed while the two raw answers are counted; its distinct
query input is then charged by summing over responses. -/
theorem decoded_response_mass_ratio_le
    {C Challenge Query Response : Type*}
    [Fintype C] [Nonempty C]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Query] [DecidableEq Query] [Nonempty Query]
    [Fintype Response]
    (decodeChallenge : C → Challenge) (decodeQuery : C → Query)
    (accepts : Challenge → Response → Query → Prop)
    (envelope : Challenge → Response → ℚ)
    (henv_nonneg : ∀ challenge response, 0 ≤ envelope challenge response)
    (hquery : ∀ challenge response,
      ((univ.filter fun query : Query =>
        accepts challenge response query).card : ℚ) /
          Fintype.card Query ≤ envelope challenge response)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : C => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : C => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card Challenge ≤ Fintype.card C)
    (hkquery : kquery * Fintype.card Query ≤ Fintype.card C)
    (beta : ℚ)
    (hmass : (∑ challenge : Challenge, ∑ response : Response,
        envelope challenge response) / Fintype.card Challenge ≤ beta) :
    (∑ response : Response,
      ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) response
          (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2) ≤ beta := by
  let factor : ℚ :=
    (kchal * kquery : ℚ) * Fintype.card Challenge *
      Fintype.card Query / (Fintype.card C : ℚ) ^ 2
  have hfactor : factor ≤ 1 :=
    Lfzk.ZkPotentialBalance.decoder_pair_factor_le_one
      kchal kquery hkchal hkquery
  have hfactor_nonneg : 0 ≤ factor := by
    dsimp [factor]
    positivity
  have hmean_nonneg : 0 ≤
      (∑ challenge : Challenge, ∑ response : Response,
        envelope challenge response) / Fintype.card Challenge := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun challenge _ =>
        Finset.sum_nonneg fun response _ => henv_nonneg challenge response
    · positivity
  have hsingle (response : Response) :
      ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) response
          (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤
      factor * ((∑ challenge : Challenge,
        envelope challenge response) / Fintype.card Challenge) := by
    let event : Challenge → Query → Prop :=
      fun challenge query => accepts challenge response query
    have hraw := Lfzk.ZkPotentialBalance.decoded_pair_card_le
      decodeChallenge decodeQuery event kchal kquery hchal hqueryBalance
    have hformal :
        ((univ.filter fun p : Challenge × Query => event p.1 p.2).card : ℚ) =
        ∑ challenge : Challenge,
          ((univ.filter fun query : Query =>
            event challenge query).card : ℚ) := by
      simp only [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
    have hq (challenge : Challenge) :
        ((univ.filter fun query : Query =>
          event challenge query).card : ℚ) ≤
        Fintype.card Query * envelope challenge response := by
      have hpos : (0 : ℚ) < Fintype.card Query := by
        exact_mod_cast Fintype.card_pos
      simpa only [mul_comm, event] using
        (div_le_iff₀ hpos).mp (hquery challenge response)
    have hsum :
        ((univ.filter fun p : Challenge × Query => event p.1 p.2).card : ℚ) ≤
        Fintype.card Query *
          ∑ challenge : Challenge, envelope challenge response := by
      rw [hformal, Finset.mul_sum]
      exact Finset.sum_le_sum fun challenge _ => hq challenge
    have hraw' :
        ((univ.filter fun p : C × C =>
          event (decodeChallenge p.1) (decodeQuery p.2)).card : ℚ) ≤
        (kchal * kquery : ℚ) * Fintype.card Query *
          ∑ challenge : Challenge, envelope challenge response := by
      calc
        _ ≤ (kchal * kquery : ℚ) *
            ((univ.filter fun p : Challenge × Query =>
              event p.1 p.2).card : ℚ) := hraw
        _ ≤ (kchal * kquery : ℚ) *
            (Fintype.card Query *
              ∑ challenge : Challenge, envelope challenge response) :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have hC : (0 : ℚ) < (Fintype.card C : ℚ) ^ 2 := by
      positivity
    have hX : (0 : ℚ) < Fintype.card Challenge := by
      exact_mod_cast Fintype.card_pos
    have hdiv := div_le_div_of_nonneg_right hraw' hC.le
    dsimp only [event] at hdiv
    change ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) response (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤
      factor * ((∑ challenge : Challenge,
        envelope challenge response) / Fintype.card Challenge)
    calc
      _ ≤ ((kchal * kquery : ℚ) * Fintype.card Query *
          ∑ challenge : Challenge, envelope challenge response) /
          (Fintype.card C : ℚ) ^ 2 := hdiv
      _ = _ := by
        dsimp [factor]
        field_simp [ne_of_gt hX]
  calc
    (∑ response : Response,
      ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) response
          (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2) ≤
      ∑ response : Response,
        factor * ((∑ challenge : Challenge,
          envelope challenge response) / Fintype.card Challenge) :=
            Finset.sum_le_sum fun response _ => hsingle response
    _ = factor * ((∑ challenge : Challenge, ∑ response : Response,
          envelope challenge response) / Fintype.card Challenge) := by
            rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_comm]
    _ ≤ (∑ challenge : Challenge, ∑ response : Response,
          envelope challenge response) / Fintype.card Challenge := by
            nlinarith
    _ ≤ beta := hmass

/-- A certified high-cover mass becomes a raw hash-answer pair budget. -/
theorem high_cover_pair_ratio_le
    {C Challenge Response : Type*} [Fintype C] [Nonempty C]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Response]
    {n r cutoff : ℕ} (hrn : r ≤ n)
    (decodeChallenge : C → Challenge) (decodeQuery : C → QuerySet n r)
    (good : Challenge → Response → Finset (Fin n))
    (accepts : Challenge → Response → QuerySet n r → Prop)
    (hcover : ∀ challenge response query,
      accepts challenge response query →
        query.coordinates ⊆ good challenge response)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : C => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : C => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card Challenge ≤ Fintype.card C)
    (hkquery : kquery * Fintype.card (QuerySet n r) ≤ Fintype.card C)
    (beta : ℚ)
    (hmass : (∑ challenge : Challenge, ∑ response : Response,
      highCover cutoff (good challenge response).card n r) /
        Fintype.card Challenge ≤ beta) :
    (∑ response : Response,
      ((univ.filter fun p : C × C =>
        highEvent (cutoff := cutoff) good accepts
          (decodeChallenge p.1) response (decodeQuery p.2)).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2) ≤ beta := by
  classical
  letI : Nonempty (QuerySet n r) := QuerySet.nonempty hrn
  have hnonneg (challenge : Challenge) (response : Response) :
      0 ≤ highCover cutoff (good challenge response).card n r := by
    unfold highCover
    split_ifs
    · unfold hypergeometricRatio
      positivity
    · exact le_refl _
  have hquery (challenge : Challenge) (response : Response) :
      ((univ.filter fun query : QuerySet n r =>
        highEvent (cutoff := cutoff) good accepts
          challenge response query).card : ℚ) /
          Fintype.card (QuerySet n r) ≤
        highCover cutoff (good challenge response).card n r := by
    have hden : (0 : ℚ) < n.choose r := by
      exact_mod_cast Nat.choose_pos hrn
    by_cases hh : cutoff < (good challenge response).card
    · have hsub : (univ.filter fun query : QuerySet n r =>
          highEvent (cutoff := cutoff) good accepts
            challenge response query) ⊆
          queriesWithin (good challenge response) := by
        intro query hquery
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hcover challenge response query (Finset.mem_filter.mp hquery).2.2⟩
      have hc : (univ.filter fun query : QuerySet n r =>
          highEvent (cutoff := cutoff) good accepts
            challenge response query).card ≤
          (good challenge response).card.choose r :=
        (Finset.card_le_card hsub).trans
          (card_queriesWithin_le (good challenge response) le_rfl)
      have hcQ : ((univ.filter fun query : QuerySet n r =>
          highEvent (cutoff := cutoff) good accepts
            challenge response query).card : ℚ) ≤
          ((good challenge response).card.choose r : ℕ) := by
        exact_mod_cast hc
      simpa only [QuerySet.fintype_card, highCover, if_pos hh,
        hypergeometricRatio] using
        (div_le_div_of_nonneg_right hcQ hden.le)
    · have he : (univ.filter fun query : QuerySet n r =>
          highEvent (cutoff := cutoff) good accepts
            challenge response query) = ∅ := by
        ext query
        simp [highEvent, hh]
      rw [he]
      simp [highCover, hh]
  exact decoded_response_mass_ratio_le decodeChallenge decodeQuery
    (highEvent (cutoff := cutoff) good accepts)
    (fun challenge response =>
      highCover cutoff (good challenge response).card n r)
    hnonneg hquery kchal kquery hchal hqueryBalance hkchal hkquery beta hmass

end Lfzk.ResponsePairMass
