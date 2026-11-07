import LfzkV2.Current.ZeroKnowledge.MerkleSimulation
import LfzkV1.ZkMerkle

/-! A finite-query hiding bound for the current tuple tree.  The two fields
are one leaf message and use one shared opening set.  The public column index
is included in that message; only the nonce contributes random salt bits.

This module transports the existing generic Merkle coupling and discharges
its codec/entropy premises. It does not assume a compiled simulator's
indistinguishability or provide unrestricted access to an entire hash table. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleSimulation

open Merkle Merkle.MH Finset
open scoped Classical

def openingError (nonceCard digestCard n differed queries : ℕ) : ℚ :=
  ((4*n^2+2* differed*queries : ℕ) : ℚ)/nonceCard +
    (((2*n-1)*(2*n-2) : ℕ) : ℚ)/digestCard

theorem openingNumerator_le (S D n queries T differed : ℕ) :
    openingHidingNumerator S D n queries T differed ≤
      (4*n^2+2* differed*queries)*(S^(n-1)*D^T) +
        (2*n-1)*(2*n-2)*(S^n*D^(T-1)) := by
  have halves : 2*((2*n-1)*(2*n-2)/2) ≤ (2*n-1)*(2*n-2) := by omega
  calc
    _ = (4*n^2+2* differed*queries)*(S^(n-1)*D^T) +
        (2*((2*n-1)*(2*n-2)/2))*(S^n*D^(T-1)) := by
      unfold openingHidingNumerator
      ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ halves) _

theorem openingNumerator_ratio_le (S D n queries T differed : ℕ)
    (saltPositive : 0 < S) (digestPositive : 0 < D) (positive : 0 < n) (tapePositive : 0 < T) :
    (openingHidingNumerator S D n queries T differed : ℚ)/
        ((S:ℚ)^n*(D:ℚ)^T) ≤ openingError S D n differed queries := by
  have hs : (S:ℚ)^(n-1)*(S:ℚ) = (S:ℚ)^n := by
    rw [← pow_succ]
    congr 1
    omega
  have hd : (D:ℚ)^(T-1)*(D:ℚ) = (D:ℚ)^T := by
    rw [← pow_succ]
    congr 1
    omega
  have hS : (S:ℚ) ≠ 0 := by positivity
  have hD : (D:ℚ) ≠ 0 := by positivity
  calc
    _ ≤ (((4*n^2+2*differed*queries)*(S^(n-1)*D^T) +
          (2*n-1)*(2*n-2)*(S^n*D^(T-1)) : ℕ) : ℚ)/
        ((S:ℚ)^n*(D:ℚ)^T) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast openingNumerator_le S D n queries T differed
      · positivity
    _ = _ := by
      unfold openingError
      push_cast
      rw [← hs,← hd]
      field_simp

section Hiding
variable {Index Nonce Leaf D Enc V : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [DecidableEq V]
variable (C : Codec (Index × Nonce) Leaf D Enc) (injective : C.Inj)

include injective in
/-- For any two tuple-column arrays agreeing on the opened set, the whole
root/opening/oracle-query view is close.  The observer may query arbitrary
hash bytes, including every revealed authentication-path input. -/
theorem opening_hiding (n : ℕ) (positive : 0 < n) (I : Finset (Fin n))
    (T : ℕ) {queries : ℕ} (index : Fin n → Index)
    (first second : (Fin T → D) → Fin n → Leaf)
    (agree : ∀ tape i, i ∈ I → first tape i = second tape i)
    (observer : (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D V queries)
    (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T) :
    StatClose (openingError (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
      (openingHidingView (nonceCodec C) n I (fun tape i => (index i,first tape i)) observer)
      (openingHidingView (nonceCodec C) n I (fun tape i => (index i,second tape i)) observer) := by
  let E : Finset (Fin n) := univ \ I
  have disjoint : ∀ i ∈ E, i ∉ I := by simp only [E,mem_sdiff,mem_univ,true_and]; tauto
  have same : ∀ tape i, i ∉ E → (index i,first tape i) = (index i,second tape i) := by
    intro tape i hi
    apply Prod.ext
    · rfl
    · exact agree tape i (by simpa only [E,mem_sdiff,mem_univ,true_and,not_not] using hi)
  have nonceInj (message : (Fin T → D) → Fin n → Leaf) (tape : Fin T → D) (i : Fin n) :
      Function.Injective fun nonce : Nonce => (nonceCodec C).leafEnc (nonce,(index i,message tape i)) := by
    intro a b equal
    exact congrArg Prod.fst ((nonceCodec_inj C injective).leaf equal)
  have raw := LfzkV1.ZkMerkle.openingHiding_statClose (nonceCodec C) n positive I T
    (fun tape i => (index i,first tape i)) (fun tape i => (index i,second tape i)) E observer
    fits fitsAll (nonceCodec_inj C injective) disjoint same (nonceInj first) (nonceInj second)
  have hcard : E.card = n-I.card := by
    dsimp only [E]
    rw [card_sdiff_of_subset (subset_univ I),card_univ,Fintype.card_fin]
  have hΩ : Fintype.card (HidingSample n T Nonce D) =
      Fintype.card Nonce^n*Fintype.card D^T := by simp [HidingSample]
  apply StatClose.mono _ raw
  unfold LfzkV1.ZkMerkle.openingEps
  rw [hcard,hΩ]
  push_cast
  exact openingNumerator_ratio_le _ _ _ _ _ _ Fintype.card_pos Fintype.card_pos positive (by omega)

end Hiding

/-- Both nonce and digest are 32 bytes in the current runtime. -/
theorem digest_card : Fintype.card Digest = 2^256 := by
  simp only [Digest,Fintype.card_fun,Fintype.card_fin]
  decide

theorem rate7_openingError (queries : ℕ) :
    openingError (2^256) (2^256) 2443 (2443-84) queries =
      (47731336+4718*(queries:ℚ))/(2:ℚ)^256 := by
  unfold openingError
  push_cast
  norm_num
  ring

end LfzkV2.Current.ZeroKnowledge.MerkleSimulation
