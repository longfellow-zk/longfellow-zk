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
    2*MerklePreparation.error (2^256) (2^256) 2443 priorMerkle +
      MerkleSimulation.openingError (2^256) (2^256) 2443 (2443-84) laterMerkle =
        (95462672+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^256 +
          4884*(priorMerkle:ℚ)/(2:ℚ)^512 := by
  rw [MerklePreparation.rate7_error,MerkleSimulation.rate7_openingError]
  ring

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
theorem rate7 (priorMerkle laterMerkle priorTranscript : ℕ) :
    bound (2^256) (2^256) (2^128) 2443 84 priorMerkle laterMerkle priorTranscript =
      (95462672+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^256 +
        4884*(priorMerkle:ℚ)/(2:ℚ)^512 + (priorTranscript:ℚ)/(2:ℚ)^46208 := by
  unfold bound
  rw [rate7_merkle]
  have freshness : (priorTranscript:ℚ)/((2^128:ℕ):ℚ)^361 =
      (priorTranscript:ℚ)/(2:ℚ)^46208 := by
    rw [Nat.cast_pow]
    rw [← pow_mul]
    simp only [show (128:ℕ)*361 = 46208 by decide,Nat.cast_ofNat]
  exact congrArg (fun extra =>
    (95462672+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^256 +
      4884*(priorMerkle:ℚ)/(2:ℚ)^512+extra) freshness

set_option exponentiation.threshold 1024 in
/-- The complete protocol's actual digest type and rate-1/7 parameters
give this explicit distinguishing-error budget. -/
theorem rate7_protocol (priorMerkle laterMerkle priorTranscript : ℕ) :
    2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 priorMerkle +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest)
        2443 (2443-84) laterMerkle + (priorTranscript:ℚ)/(2:ℚ)^46208 =
      (95462672+4886*(priorMerkle:ℚ)+4718*(laterMerkle:ℚ))/(2:ℚ)^256 +
        4884*(priorMerkle:ℚ)/(2:ℚ)^512 + (priorTranscript:ℚ)/(2:ℚ)^46208 := by
  rw [MerkleSimulation.digest_card,rate7_merkle]

end LfzkV2.Current.ZeroKnowledge.Error
