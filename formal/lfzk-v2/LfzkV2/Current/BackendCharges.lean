import LfzkV2.Current.JointBudgets

/-! The three charges used by the current joint backend: rank at the batching
query, low-response and outside-list failure at the opening query, and summed
high-response failure at the adjacent query pair. The child index contains
both full payloads and the claimed parent link. -/
noncomputable section
namespace LfzkV2.Current.JointResponse
open RecursivePolygero NonrecursiveFS LigeroFamily Finset ProfileAnalysis
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)

def rankCharge (W : Oracle P R) (c : Coin P R) : ℚ := indicator (rankBad P R W c)

def openingCharge (σ : Statement P R) (W : Oracle P R) (c : Coin P R)
    (a : Response P R) (cutoff : ℕ × ℕ) (ε : ℚ) (Q : QuerySet n t) : ℚ :=
  indicator (¬ rankBad P R W c ∧ ¬ ε < fraction P R σ W c a ∧
    Verify P R σ W c a Q ∧ failure P R σ W c a) +
  indicator (Verify P R σ W c a Q ∧
    (decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
     decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2))

def highCharge {Link : Type} (σ : Statement P R) (W : Oracle P R)
    (response : Link × Response P R) (ε : ℚ) (link : Link) (c : Coin P R) (Q : QuerySet n t) : ℚ :=
  if link = response.1 then indicator
    (¬ rankBad P R W c ∧ ε < fraction P R σ W c response.2 ∧
      Verify P R σ W c response.2 Q ∧ failure P R σ W c response.2) else 0

theorem rankCharge_nonneg (W : Oracle P R) (c : Coin P R) : 0 ≤ rankCharge P R W c :=
  indicator_nonneg _

theorem openingCharge_nonneg (σ : Statement P R) (W : Oracle P R) (c : Coin P R)
    (a : Response P R) (cutoff : ℕ × ℕ) (ε : ℚ) (Q : QuerySet n t) :
    0 ≤ openingCharge P R σ W c a cutoff ε Q :=
  add_nonneg (indicator_nonneg _) (indicator_nonneg _)

theorem highCharge_nonneg {Link : Type} (σ : Statement P R) (W : Oracle P R)
    (response : Link × Response P R) (ε : ℚ) (link : Link) (c : Coin P R) (Q : QuerySet n t) :
    0 ≤ highCharge P R σ W response ε link c Q := by
  unfold highCharge
  split_ifs
  · exact indicator_nonneg _
  · exact le_rfl

/-- Every accepted backend extraction/list failure is charged. Which case
holds may depend on both answers, but the local charge functions themselves
read only their explicit fixed statement and recovered oracle. -/
theorem failure_charged {Link : Type} (σ : Statement P R) (W : Oracle P R) (c : Coin P R)
    (a : Response P R) (cutoff : ℕ × ℕ) (ε : ℚ) (Q : QuerySet n t) (link : Link)
    (hv : Verify P R σ W c a Q)
    (hf : failure P R σ W c a ∨
      decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
      decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2) :
    1 ≤ rankCharge P R W c ∨
    1 ≤ openingCharge P R σ W c a cutoff ε Q ∨
    1 ≤ highCharge P R σ W (link,a) ε link c Q := by
  by_cases hr : rankBad P R W c
  · exact Or.inl (by simp [rankCharge, indicator, hr])
  rcases hf with hf | hout
  · by_cases hh : ε < fraction P R σ W c a
    · exact Or.inr (Or.inr (by simp [highCharge, indicator, hr, hh, hv, hf]))
    · apply Or.inr ∘ Or.inl
      have hz := indicator_nonneg (Verify P R σ W c a Q ∧
        (decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
         decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2))
      simpa only [openingCharge, hr, hh, hv, hf, not_false_eq_true, true_and,
        indicator, if_true] using le_add_of_nonneg_right (a := (1 : ℚ)) hz
  · apply Or.inr ∘ Or.inl
    have hz := indicator_nonneg (¬ rankBad P R W c ∧ ¬ ε < fraction P R σ W c a ∧
      Verify P R σ W c a Q ∧ failure P R σ W c a)
    simpa only [openingCharge, hv, hout, true_and, indicator, if_true] using
      le_add_of_nonneg_left (a := (1 : ℚ)) hz

section Raw
variable {C : Type} [Fintype C] [Nonempty C] [DecidableEq (Coin P R)]
variable (decodeCoin : C → Coin P R) (decodeQuery : C → QuerySet n t)
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card (Coin P R) ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card (QuerySet n t) ≤ Fintype.card C)

omit [Nonempty C] [DecidableEq (Coin P R)] in
include kQuery hquery hkQuery in
theorem openingCharge_sum (σ : Statement P R) (W : Oracle P R) (c : Coin P R)
    (a : Response P R) (cutoff : ℕ × ℕ) (ε : ℚ) (hε : 0 ≤ ε) :
    (∑ b : C, openingCharge P R σ W c a cutoff ε (decodeQuery b)) ≤
      Fintype.card C * (ε + ((cutoff.1+s-1).choose t : ℚ)/n.choose t +
        ((cutoff.2+s-1).choose t : ℚ)/n.choose t) := by
  simp only [openingCharge, sum_add_distrib]
  have h := add_le_add (low_raw_le P R decodeQuery kQuery hquery hkQuery σ W c a ε hε)
    (outside_raw_le P R decodeQuery kQuery hquery hkQuery σ W c a cutoff)
  exact h.trans_eq (by ring)

omit [Nonempty C] in
include kCoin hcoin hkCoin in
theorem rankCharge_sum (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (W : Oracle P R) :
    (∑ a : C, rankCharge P R W (decodeCoin a)) ≤ Fintype.card C * (p.rankError+r.rankError) :=
  rank_raw_le P R decodeCoin kCoin hcoin hkCoin W p r

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem highCharge_sum {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ response : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      highCharge P R σ W response ε a.1 (decodeCoin a.2) (decodeQuery b.2)) ≤
      (Fintype.card (Link × C) : ℚ)^2 *
        (NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r) :=
  linked_high_raw_le P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    σ W p r ε hp hr

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem highCharge_sum_joint {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    (∑ response : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      highCharge P R σ W response ε a.1 (decodeCoin a.2) (decodeQuery b.2)) ≤
      (Fintype.card (Link × C) : ℚ)^2*jointHighBudget P R p :=
  linked_high_raw_le_joint P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    σ W p r ε hp hr

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem highCharge_sum_active {Link : Type} [Fintype Link]
    (p : HahnSystemCertificate P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier) :
    (∑ response : Link × Response P R, ∑ a : Link × C, ∑ b : Link × C,
      highCharge P R σ W response ε a.1 (decodeCoin a.2) (decodeQuery b.2)) ≤
      (Fintype.card (Link × C) : ℚ)^2*activeHighBudget P R p :=
  linked_high_raw_le_active P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    σ W p r ε hθ hactive hbound

end Raw
end LfzkV2.Current.JointResponse
