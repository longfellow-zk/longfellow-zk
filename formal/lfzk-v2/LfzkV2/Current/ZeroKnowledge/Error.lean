import LfzkV2.Current.ZeroKnowledge.MerklePreparation
import LfzkV2.Current.ZeroKnowledge.MerkleBound

/-! Arithmetic budget for the simulator's oracle hybrids. The algebraic
frontend and backend changes of coins are exact. Two causal commitment
preparations, retained-cache Merkle hiding, and one opening-query freshness
event contribute the terms below. This module only sums those established
component budgets; the complete-protocol theorem supplies their composition.

Earlier and later Merkle queries are counted separately. Only earlier
transcript queries can occupy the opening input before it is programmed;
the final seal is computed using the resulting oracle without programming. -/
namespace LfzkV2.Current.ZeroKnowledge.Error

def bound (nonceCard digestCard binaryCard columns openings : ℕ)
    (priorMerkle laterMerkle priorTranscript : ℕ) : ℚ :=
  2*MerklePreparation.error nonceCard digestCard columns priorMerkle +
    MerkleSimulation.openingError nonceCard digestCard columns (columns-openings) laterMerkle +
      (priorTranscript:ℚ)/(binaryCard:ℚ)^361

theorem nonnegative (nonceCard digestCard binaryCard columns openings : ℕ)
    (priorMerkle laterMerkle priorTranscript : ℕ) :
    0 ≤ bound nonceCard digestCard binaryCard columns openings priorMerkle laterMerkle priorTranscript := by
  unfold bound MerklePreparation.error MerkleSimulation.openingError
  positivity

set_option exponentiation.threshold 1024 in
theorem rate7_merkle (priorMerkle laterMerkle : ℕ) :
    2*MerklePreparation.error (2^320) (2^256) 2443 priorMerkle +
      MerkleSimulation.openingError (2^320) (2^256) 2443 (2443-84) laterMerkle =
        (47745992+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^320 +
        47716680/(2:ℚ)^256 +
          4884*(priorMerkle:ℚ)/(2:ℚ)^512 := by
  rw [MerklePreparation.rate7_error,MerkleSimulation.rate7_openingError]
  ring

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
theorem rate7 (priorMerkle laterMerkle priorTranscript : ℕ) :
    bound (2^320) (2^256) (2^128) 2443 84 priorMerkle laterMerkle priorTranscript =
      (47745992+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^320 +
          47716680/(2:ℚ)^256 +
        4884*(priorMerkle:ℚ)/(2:ℚ)^512 + (priorTranscript:ℚ)/(2:ℚ)^46208 := by
  unfold bound
  rw [rate7_merkle]
  have freshness : (priorTranscript:ℚ)/((2^128:ℕ):ℚ)^361 =
      (priorTranscript:ℚ)/(2:ℚ)^46208 := by
    rw [Nat.cast_pow,← pow_mul]
    simp only [show (128:ℕ)*361 = 46208 by decide,Nat.cast_ofNat]
  rw [freshness]

set_option exponentiation.threshold 1024 in
/-- The complete protocol's actual nonce/digest types and rate-1/7 parameters
give this explicit distinguishing-error budget. -/
theorem rate7_protocol (priorMerkle laterMerkle priorTranscript : ℕ) :
    2*MerklePreparation.error (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 priorMerkle +
      MerkleSimulation.openingError (Fintype.card MerkleNonce) (Fintype.card Digest)
        2443 (2443-84) laterMerkle + (priorTranscript:ℚ)/(2:ℚ)^46208 =
      (47745992+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^320 +
        47716680/(2:ℚ)^256 +
        4884*(priorMerkle:ℚ)/(2:ℚ)^512 + (priorTranscript:ℚ)/(2:ℚ)^46208 := by
  rw [MerkleSimulation.nonce_card,MerkleSimulation.digest_card,rate7_merkle]

/-- Bound opening-query freshness symbolically before substituting the field
cardinality. This keeps the 361-coordinate sample space out of arithmetic
normalization in the concrete query-budget proof. -/
private theorem transcriptFreshness_le (q queries : ℚ) (large : 1 ≤ q)
    (nonnegative : 0 ≤ queries) (budget : queries ≤ q) :
    queries/q^361 ≤ 1/q^2 := by
  have positive : 0 < q := lt_of_lt_of_le zero_lt_one large
  calc
    _ ≤ queries/q^3 := div_le_div_of_nonneg_left nonnegative (pow_pos positive _)
      (pow_le_pow_right₀ large (by decide : 3 ≤ 361))
    _ ≤ q/q^3 := div_le_div_of_nonneg_right budget (le_of_lt (pow_pos positive _))
    _ = _ := by
      have : q ≠ 0 := ne_of_gt positive
      field_simp

set_option exponentiation.threshold 1024 in
/-- A total budget of 2^128 Merkle queries, including those before the proof,
and at most 2^128 prior transcript queries gives error strictly below 2^-179.
The Merkle budget is shared across the earlier and later observer, not granted
independently to each. The transcript term is conservatively enlarged here
to avoid evaluating an unnecessarily large concrete power. -/
theorem rate7_at_query_budget (priorMerkle laterMerkle priorTranscript : ℕ)
    (merkleQueries : priorMerkle+laterMerkle ≤ 2^128)
    (transcriptQueries : priorTranscript ≤ 2^128) :
    bound (2^320) (2^256) (2^128) 2443 84 priorMerkle laterMerkle priorTranscript <
      1/(2:ℚ)^179 := by
  unfold bound
  rw [rate7_merkle]
  have hm : (priorMerkle:ℚ)+(laterMerkle:ℚ) ≤ (2:ℚ)^128 := by
    exact_mod_cast merkleQueries
  have ht : (priorTranscript:ℚ) ≤ (2:ℚ)^128 := by
    exact_mod_cast transcriptQueries
  have hp : (priorMerkle:ℚ) ≤ (2:ℚ)^128 :=
    (le_add_of_nonneg_right (Nat.cast_nonneg laterMerkle)).trans hm
  have weighted : 47745992+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ) ≤
      47745992+4886*(2:ℚ)^128 := by
    have := Nat.cast_nonneg (α := ℚ) laterMerkle
    linarith
  have first := div_le_div_of_nonneg_right weighted (by positivity : 0 ≤ (2:ℚ)^320)
  have third := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℚ) ≤ 4884))
    (by positivity : 0 ≤ (2:ℚ)^512)
  have fresh : (priorTranscript:ℚ)/((2^128:ℕ):ℚ)^361 ≤ 1/(2:ℚ)^256 := by
    rw [Nat.cast_pow,Nat.cast_ofNat]
    have law := transcriptFreshness_le ((2:ℚ)^128) (priorTranscript:ℚ)
      (by norm_num) (Nat.cast_nonneg _) ht
    simpa only [← pow_mul,show (128:ℕ)*2 = 256 by decide] using law

  calc
    _ ≤ (47745992+4886*(2:ℚ)^128)/(2:ℚ)^320 + 47716680/(2:ℚ)^256 +
        4884*(2:ℚ)^128/(2:ℚ)^512 + 1/(2:ℚ)^256 :=
      add_le_add (add_le_add (add_le_add first (le_refl _)) third) fresh
    _ < _ := by norm_num

end LfzkV2.Current.ZeroKnowledge.Error
