import LfzkV2.Current.JointMass
import TranscriptV2.SharedCharging

/-! Raw-answer budgets for the joint backend. Balanced decoders express the
ideal sampling model; the correspondence with the XOF rejection sampler is
separate. Both complete payloads belong to the child-query index. -/
noncomputable section
namespace LfzkV2.Current.JointResponse
open RecursivePolygero LigeroFamily Finset ProfileAnalysis
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)

section Budgets
variable {C : Type} [Fintype C] [Nonempty C]
variable [DecidableEq (Coin P R)]
variable (decodeCoin : C → Coin P R) (decodeQuery : C → QuerySet n t)
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card (Coin P R) ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card (QuerySet n t) ≤ Fintype.card C)
variable (σ : Statement P R) (W : Oracle P R)

omit [Nonempty C] [DecidableEq (Coin P R)] in
include kQuery hquery hkQuery in
theorem outside_raw_le (c : Coin P R) (a : Response P R) (cutoff : ℕ × ℕ) :
    (∑ b : C, indicator (Verify P R σ W c a (decodeQuery b) ∧
      (NonrecursiveFS.decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
       NonrecursiveFS.decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2))) ≤
      Fintype.card C * ((((cutoff.1+s-1).choose t : ℚ)/n.choose t) +
        (((cutoff.2+s-1).choose t : ℚ)/n.choose t)) := by
  have h (b : C) : indicator (Verify P R σ W c a (decodeQuery b) ∧
      (NonrecursiveFS.decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
       NonrecursiveFS.decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2)) ≤
      indicator (P.backend.layer.verify σ.1 W.1 c.1 a.1 (P.localQuery (decodeQuery b)) ∧
        NonrecursiveFS.decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1) +
      indicator (R.backend.layer.verify σ.2 W.2 c.2 a.2 (R.localQuery (decodeQuery b)) ∧
        NonrecursiveFS.decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2) := by
    simp only [Verify, indicator]
    split_ifs <;> simp_all
  apply (sum_le_sum (fun b _ => h b)).trans
  rw [sum_add_distrib, mul_add]
  exact add_le_add (P.outside_query_raw_le decodeQuery kQuery hquery hkQuery σ.1 W.1 c.1 a.1 cutoff.1)
    (R.outside_query_raw_le decodeQuery kQuery hquery hkQuery σ.2 W.2 c.2 a.2 cutoff.2)

omit [Nonempty C] [DecidableEq (Coin P R)] in
include kQuery hquery hkQuery in
theorem query_raw_le (c : Coin P R) (a : Response P R) :
    (∑ b : C, indicator (Verify P R σ W c a (decodeQuery b))) ≤
      Fintype.card C * fraction P R σ W c a := by
  letI : Nonempty (QuerySet n t) := QuerySet.nonempty
    (by simpa only [P.columns, P.openings] using P.backend.query_le)
  exact NonrecursiveFS.balanced_sum_le decodeQuery kQuery hquery hkQuery
    (fun Q => indicator (Verify P R σ W c a Q)) (fun _ => indicator_nonneg _)
    (fraction P R σ W c a) (fraction_nonneg P R σ W c a) (query_mean P R σ W c a).le

omit [Nonempty C] [DecidableEq (Coin P R)] in
include kQuery hquery hkQuery in
theorem low_raw_le (c : Coin P R) (a : Response P R) (ε : ℚ) (hε : 0 ≤ ε) :
    (∑ b : C, indicator (¬ rankBad P R W c ∧ ¬ ε < fraction P R σ W c a ∧
      Verify P R σ W c a (decodeQuery b) ∧ failure P R σ W c a)) ≤ Fintype.card C * ε := by
  by_cases hh : ε < fraction P R σ W c a
  · simp only [hh, not_true_eq_false, false_and, and_false, indicator, if_false, sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hε
  · apply le_trans _ ((query_raw_le P R decodeQuery kQuery hquery hkQuery σ W c a).trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by positivity)))
    exact sum_le_sum (fun b _ => indicator_mono (fun h => h.2.2.1))

omit [Nonempty C] in
include kCoin hcoin hkCoin in
theorem rank_raw_le (p : ProfileParameters P.backend) (r : ProfileParameters R.backend) :
    (∑ a : C, indicator (rankBad P R W (decodeCoin a))) ≤
      Fintype.card C * (p.rankError+r.rankError) :=
  NonrecursiveFS.balanced_sum_le decodeCoin kCoin hcoin hkCoin
    (fun c => indicator (rankBad P R W c)) (fun _ => indicator_nonneg _)
    (p.rankError+r.rankError) (by unfold ProfileParameters.rankError; positivity)
    (rank_mean P R p r W)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
private theorem high_raw_le_of_mean (ε budget : ℚ) (hbudget : 0 ≤ budget)
    (hmean : mean (highMass P R σ W ε) ≤ budget) :
    (∑ payload : Response P R, ∑ a : C, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤ (Fintype.card C : ℚ)^2*budget := by
  have haverage := NonrecursiveFS.balanced_sum_le decodeCoin kCoin hcoin hkCoin
    (highMass P R σ W ε) (highMass_nonneg P R σ W ε) budget hbudget hmean
  have hlocal (a : C) : (∑ payload : Response P R, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤
      Fintype.card C * highMass P R σ W ε (decodeCoin a) := by
    by_cases hb : rankBad P R W (decodeCoin a)
    · simp [hb, highMass, indicator]
    · simp only [highMass, hb, if_false, not_false_eq_true, true_and, mul_sum]
      apply sum_le_sum
      intro payload _
      by_cases hf : failure P R σ W (decodeCoin a) payload
      · by_cases hh : ε < fraction P R σ W (decodeCoin a) payload
        · simpa only [hf, hh, true_and, and_true, if_true] using
            query_raw_le P R decodeQuery kQuery hquery hkQuery σ W (decodeCoin a) payload
        · simp [hh, indicator]
      · simp [hf, indicator]
  calc
    _ = ∑ a : C, ∑ payload : Response P R, ∑ b : C,
        indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
          Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
          failure P R σ W (decodeCoin a) payload) := sum_comm
    _ ≤ ∑ a : C, Fintype.card C * highMass P R σ W ε (decodeCoin a) :=
      sum_le_sum (fun a _ => hlocal a)
    _ = Fintype.card C * ∑ a : C, highMass P R σ W ε (decodeCoin a) := (mul_sum ..).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left haverage (show (0 : ℚ) ≤ Fintype.card C by positivity)
      simpa only [pow_two, mul_assoc] using h

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem high_raw_le (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ payload : Response P R, ∑ a : C, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤
      (Fintype.card C : ℚ)^2 *
        (NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r) :=
  high_raw_le_of_mean P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W ε _
    (add_nonneg (NonrecursiveFS.highBudget_nonneg P.backend p)
      (NonrecursiveFS.highBudget_nonneg R.backend r))
    (extraction_high_mass_mean P R p r σ W ε hp hr)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
/-- The shared geometric mass controls the full response pair even when
one participant's carrier is much larger than the other's. -/
theorem high_raw_le_joint (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ payload : Response P R, ∑ a : C, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤
      (Fintype.card C : ℚ)^2*jointHighBudget P R p :=
  high_raw_le_of_mean P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W ε _
    (jointHighBudget_nonneg P R p) (extraction_high_mass_mean_joint P R p r σ W ε hp hr)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
/-- A genuine active-family certificate permits the geometric threshold
itself as the low/high split. There is no field-error `1/q` addition here. -/
theorem high_raw_le_active (p : HahnSystemCertificate P.backend) (r : ProfileParameters R.backend)
    (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier) :
    (∑ payload : Response P R, ∑ a : C, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤
      (Fintype.card C : ℚ)^2*activeHighBudget P R p :=
  high_raw_le_of_mean P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W ε _
    (activeHighBudget_nonneg P R p)
    (extraction_high_mass_mean_active P R p r σ W ε hθ hactive hbound)

omit [Nonempty C] [DecidableEq (Coin P R)] in
private theorem linked_high_raw_le_of_raw {Link : Type} [Fintype Link]
    (ε budget : ℚ)
    (hraw : (∑ payload : Response P R, ∑ a : C, ∑ b : C,
      indicator (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧
        failure P R σ W (decodeCoin a) payload)) ≤ (Fintype.card C : ℚ)^2*budget) :
    (∑ payload : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      if a.1 = payload.1 then
        indicator (¬ rankBad P R W (decodeCoin a.2) ∧ ε < fraction P R σ W (decodeCoin a.2) payload.2 ∧
          Verify P R σ W (decodeCoin a.2) payload.2 (decodeQuery b.2) ∧
          failure P R σ W (decodeCoin a.2) payload.2) else 0) ≤
      (Fintype.card (Link × C) : ℚ)^2*budget := by
  rw [TranscriptV2.feedback_sum (Link := Link)
    (fun (payload : Response P R) (a b : C) => indicator
      (¬ rankBad P R W (decodeCoin a) ∧ ε < fraction P R σ W (decodeCoin a) payload ∧
        Verify P R σ W (decodeCoin a) payload (decodeQuery b) ∧ failure P R σ W (decodeCoin a) payload))]
  have h := mul_le_mul_of_nonneg_left hraw
    (show (0 : ℚ) ≤ (Fintype.card Link : ℚ)^2 by positivity)
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_pow, mul_assoc] using h

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem linked_high_raw_le {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ payload : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      if a.1 = payload.1 then
        indicator (¬ rankBad P R W (decodeCoin a.2) ∧ ε < fraction P R σ W (decodeCoin a.2) payload.2 ∧
          Verify P R σ W (decodeCoin a.2) payload.2 (decodeQuery b.2) ∧
          failure P R σ W (decodeCoin a.2) payload.2) else 0) ≤
      (Fintype.card (Link × C) : ℚ)^2 *
        (NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r) :=
  linked_high_raw_le_of_raw P R decodeCoin decodeQuery σ W ε _
    (high_raw_le P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W p r ε hp hr)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
/-- Link feedback leaves the refined joint coefficient unchanged. The sum
still indexes both complete payloads and each claimed parent link. -/
theorem linked_high_raw_le_joint {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ payload : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      if a.1 = payload.1 then
        indicator (¬ rankBad P R W (decodeCoin a.2) ∧ ε < fraction P R σ W (decodeCoin a.2) payload.2 ∧
          Verify P R σ W (decodeCoin a.2) payload.2 (decodeQuery b.2) ∧
          failure P R σ W (decodeCoin a.2) payload.2) else 0) ≤
      (Fintype.card (Link × C) : ℚ)^2*jointHighBudget P R p :=
  linked_high_raw_le_of_raw P R decodeCoin decodeQuery σ W ε _
    (high_raw_le_joint P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W p r ε hp hr)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem linked_high_raw_le_active {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : ProfileParameters R.backend)
    (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier) :
    (∑ payload : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      if a.1 = payload.1 then
        indicator (¬ rankBad P R W (decodeCoin a.2) ∧ ε < fraction P R σ W (decodeCoin a.2) payload.2 ∧
          Verify P R σ W (decodeCoin a.2) payload.2 (decodeQuery b.2) ∧
          failure P R σ W (decodeCoin a.2) payload.2) else 0) ≤
      (Fintype.card (Link × C) : ℚ)^2*activeHighBudget P R p :=
  linked_high_raw_le_of_raw P R decodeCoin decodeQuery σ W ε _
    (high_raw_le_active P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery σ W p r ε hθ hactive hbound)

end Budgets
end LfzkV2.Current.JointResponse
