import TranscriptV2.DigestProjection
import TranscriptV2.SharedCharging

/-! Share the query budget between ordinary protocol queries and queries
which plant speculative digest targets. The latter pay for their later
connection opportunities instead of adding a whole-search union bound. -/
namespace TranscriptV2.StrandCharging
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P D C Out : Type}
variable [Fintype P] [DecidableEq P] [Fintype D] [Nonempty D] [DecidableEq D]
variable [Fintype C] [Nonempty C]

/-- The speculative-query part of the transcript contract. It depends only
on target planting and raw digest sampling, never on a subprotocol's algebraic
failure predicate or an assumed ordinary-query average. -/
theorem targets_sum_le {fuel Q arity : ℕ}
    (tree : Tree P (D × C) Out fuel) (queries : ∀ H, (seen tree H).card ≤ Q)
    (auxiliary : P → Prop) (claims : P → Finset D)
    (claimBound : ∀ p, (claims p).card ≤ if auxiliary p then arity else 0)
    (epsilon : ℚ)
    (guessFits : (Q*arity : ℚ)/Fintype.card D ≤ epsilon) :
    (∑ H : P → D × C,
      ∑ p ∈ seen tree H, if DigestProjection.bad claims tree p H (H p) then (1 : ℚ) else 0) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H, if auxiliary p then epsilon else 0 := by
  have guesses := DigestProjection.guess_sum_le_claims claims tree queries
  have nameCost p : (Q : ℚ)/Fintype.card D * (claims p).card ≤
      if auxiliary p then epsilon else 0 := by
    have bound : ((claims p).card : ℚ) ≤ if auxiliary p then (arity : ℚ) else 0 := by
      split_ifs with aux
      · exact_mod_cast (show (claims p).card ≤ arity from by simpa only [if_pos aux] using claimBound p)
      · exact_mod_cast (show (claims p).card ≤ 0 from by simpa only [if_neg aux] using claimBound p)
    have scaled := mul_le_mul_of_nonneg_left bound
      (show (0 : ℚ) ≤ Q/Fintype.card D by positivity)
    apply scaled.trans
    split_ifs
    · simpa only [div_mul_eq_mul_div] using guessFits
    · simp only [mul_zero,le_refl]
  have targetMean : (Q : ℚ)/Fintype.card D *
      (∑ H : P → D × C, ∑ p ∈ seen tree H, ((claims p).card : ℚ)) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H, if auxiliary p then epsilon else 0 := by
    simp only [mul_sum]
    exact sum_le_sum (fun _ _ => sum_le_sum (fun p _ => nameCost p))
  exact guesses.trans targetMean

/-- Ordinary and speculative costs retain their actual role counts until
the final shared sum. New composition clients can use `targets_sum_le` and
derive the ordinary average directly from their local charge family. -/
theorem shared_targets_sum_le {fuel Q arity : ℕ}
    (tree : Tree P (D × C) Out fuel) (queries : ∀ H, (seen tree H).card ≤ Q)
    (auxiliary : P → Prop) (claims : P → Finset D)
    (claimBound : ∀ p, (claims p).card ≤ if auxiliary p then arity else 0)
    (protocol : (P → D × C) → ℚ) (epsilon : ℚ) (positive : 0 ≤ epsilon)
    (protocolMean : (∑ H, protocol H) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H, if auxiliary p then 0 else epsilon)
    (guessFits : (Q*arity : ℚ)/Fintype.card D ≤ epsilon) :
    (∑ H : P → D × C, (protocol H +
      ∑ p ∈ seen tree H, if DigestProjection.bad claims tree p H (H p) then 1 else 0)) ≤
      (Q : ℚ)*epsilon*(Fintype.card (D × C) : ℚ)^Fintype.card P := by
  have bound := add_le_add protocolMean (targets_sum_le tree queries auxiliary claims claimBound epsilon guessFits)
  have each H :
      (∑ p ∈ seen tree H, if auxiliary p then (0 : ℚ) else epsilon) +
        (∑ p ∈ seen tree H, if auxiliary p then epsilon else 0) ≤ Q*epsilon := by
    rw [← sum_add_distrib]
    have together p : (if auxiliary p then (0 : ℚ) else epsilon) +
        (if auxiliary p then epsilon else 0) = epsilon := by split_ifs <;> simp
    simp only [together,sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast queries H) positive
  rw [sum_add_distrib]
  apply bound.trans
  rw [← sum_add_distrib]
  have total := sum_le_sum (fun H (_ : H ∈ (univ : Finset (P → D × C))) => each H)
  simpa only [sum_const,card_univ,Fintype.card_fun,Nat.cast_pow,nsmul_eq_mul,mul_comm] using total

/-- Speculative strand inputs and receiving Merkle inputs occupy disjoint
query domains. Keep their actual counts until this last comparison: a strand
input pays Q/M, a Merkle input pays 2Q/M, and neither is charged both rates. -/
theorem disjoint_hash_sum_le {fuel Q : ℕ}
    (tree : Tree P (D × C) Out fuel) (queries : ∀ H, (seen tree H).card ≤ Q)
    (plants receives auxiliary : P → Prop)
    (plantAuxiliary : ∀ p, plants p → auxiliary p)
    (receiveAuxiliary : ∀ p, receives p → auxiliary p)
    (disjoint : ∀ p, plants p → ¬receives p)
    (strandClaims merkleClaims : P → Finset D)
    (strandBound : ∀ p, (strandClaims p).card ≤ if plants p then 1 else 0)
    (merkleBound : ∀ p, (merkleClaims p).card ≤ 2) :
    (∑ H : P → D × C, (DigestProjection.charge strandClaims tree H +
      DigestProjection.receivingCharge receives merkleClaims tree H)) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H,
        if auxiliary p then (2*Q : ℚ)/Fintype.card D else 0 := by
  have strand := targets_sum_le tree queries plants strandClaims strandBound
    ((Q : ℚ)/Fintype.card D) (by simp)
  have merkle := DigestProjection.receiving_sum_le receives receives (fun _ h => h)
    merkleClaims tree queries merkleBound
  have total := add_le_add strand merkle
  simp only [← sum_add_distrib] at total
  apply total.trans
  apply sum_le_sum
  intro H _
  apply sum_le_sum
  intro p _
  by_cases planted : plants p
  · have notReceiving := disjoint p planted
    simp only [if_pos planted,if_neg notReceiving,if_pos (plantAuxiliary p planted),add_zero]
    exact div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℚ) Q] : (Q : ℚ) ≤ 2*Q) (Nat.cast_nonneg _)
  · by_cases receiving : receives p
    · simp only [if_neg planted,if_pos receiving,if_pos (receiveAuxiliary p receiving),zero_add]
      exact le_of_eq (by ring)
    · simp only [if_neg planted,if_neg receiving,zero_add]
      split_ifs <;> positivity

/-- In the nonvacuous quadratic range, a speculative query's chance of
being connected by a later node fits within one ordinary query allowance.
The digest space `M` and field size `q` are separate parameters. -/
theorem digest_guess_fits {q M Q : ℕ} (positive : 0 < q)
    (space : q*q ≤ M) (budget : Q ≤ q) :
    (Q : ℚ)/M ≤ 2/(q : ℚ) := by
  have hq : (0 : ℚ) < q := by exact_mod_cast positive
  have hM : (0 : ℚ) < M := by
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.mul_pos positive positive) space
  have hQ : (Q : ℚ) ≤ q := by exact_mod_cast budget
  have hspace : (q : ℚ)*q ≤ M := by exact_mod_cast space
  apply (div_le_div_iff₀ hM hq).mpr
  have product := mul_le_mul_of_nonneg_right hQ hq.le
  nlinarith

/-- Ordinary queries and speculative queries spend the same original
budget. No separate whole-search guessing penalty is added. -/
theorem quadratic_partition_bound {q M Q ordinary speculative : ℕ}
    (positive : 0 < q) (space : q*q ≤ M) (budget : Q ≤ q)
    (partition : ordinary+speculative ≤ Q) :
    2*(ordinary : ℚ)/q + (speculative : ℚ)*Q/M ≤ 2*(Q : ℚ)/q := by
  have hq : (0 : ℚ) < q := by exact_mod_cast positive
  have hg := mul_le_mul_of_nonneg_left (digest_guess_fits positive space budget)
    (show (0 : ℚ) ≤ speculative by positivity)
  have htotal : (ordinary : ℚ)+speculative ≤ Q := by exact_mod_cast partition
  calc
    _ ≤ 2*(ordinary : ℚ)/q + (speculative : ℚ)*(2/q) := by
      simpa only [mul_div_assoc] using
        (add_le_add (le_rfl : 2*(ordinary : ℚ)/q ≤ 2*(ordinary : ℚ)/q) hg)
    _ = 2*((ordinary : ℚ)+speculative)/q := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htotal (by norm_num)) hq.le

end TranscriptV2.StrandCharging
