import LfzkV2.Current.ZeroKnowledge.MerklePreparation

/-! The same preparation coupling preserves the actual honest heap labels.
Consequently a frontend may derive its public messages and affine statement
from the honest commitment root. Replacing the heap by independent common
labels costs no additional collision term. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerklePreparation

open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical
set_option maxHeartbeats 700000

variable {Salt Message Digest Enc Request Value : Type}
variable [Inhabited Digest] [DecidableEq Enc]
variable (codec : Codec Salt Message Digest Enc) (n : ℕ)

def actualLabels (nonce : Fin n → Salt) (messages : Fin n → Message) (H : Enc → Digest) :
    Fin (2*n-1) → Digest := fun i =>
  ((commitPass codec n nonce messages (2*n-1) (fun _ => default)).run H).1 (2*n-1-i.val)

theorem prepared_labels (positive : 0 < n) (nonce : Fin n → Salt) (messages : Fin n → Message)
    (tape : Fin (2*n-1) → Digest) (background : Enc → Digest)
    (injective : commitInputsInjective codec n nonce messages (commitOracle codec n nonce messages tape)) :
    actualLabels codec n nonce messages (MerkleCache.prepared codec n nonce messages tape background) = tape := by
  funext i
  unfold actualLabels
  rw [MerkleCache.commit_run]
  have result := commitPass_run codec n nonce messages (commitOracle codec n nonce messages tape)
    (2*n-1) (fun _ => default)
    (fun vertex beyond => (commitLabels_of_ge (S := codec.withOracle (commitOracle codec n nonce messages tape))
      n nonce messages vertex (by omega)).symm) (2*n-1-i.val) (by have := i.isLt; omega)
  rw [result,commitLabels_eq_tape codec n positive nonce messages tape injective
    (2*n-1-i.val) (by have := i.isLt; omega) (by omega) (by have := i.isLt; omega)]
  congr 1
  apply Fin.ext
  change 2*n-1-(2*n-1-i.val) = i.val
  have := i.isLt
  omega

variable {fuel : ℕ} (before : Tree Enc Digest Request fuel)
variable (cells : Request → Fin n → Message)

def honestLabels (nonce : Fin n → Salt) (H : Enc → Digest) : Fin (2*n-1) → Digest :=
  actualLabels codec n nonce (cells (before.run H).1) H

variable [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
variable [Fintype Digest] [DecidableEq Digest] [DecidableEq Value]

def labelledRefreshed (background : Enc → Digest)
    (observe : (Fin n → Salt) → Request → (Enc → Digest) → (Fin (2*n-1) → Digest) → Value)
    (coin : HidingSample n (2*n-1) Salt Digest) : Value :=
  let H := refreshFor codec n before cells coin.1 (background,coin.2)
  observe coin.1 (before.run H.1).1 H.1 (honestLabels codec n before cells coin.1 H.1)

def labelledPrepared (background : Enc → Digest)
    (observe : (Fin n → Salt) → Request → (Enc → Digest) → (Fin (2*n-1) → Digest) → Value)
    (coin : HidingSample n (2*n-1) Salt Digest) : Value :=
  observe coin.1 (before.run background).1 (MerkleCache.prepared codec n coin.1 (cells (before.run background).1) coin.2 background) coin.2

omit [Nonempty Salt] in
theorem labelled_disagreement_card (positive : 0 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest)
    (observe : (Fin n → Salt) → Request → (Enc → Digest) → (Fin (2*n-1) → Digest) → Value) :
    (univ.filter fun coin : HidingSample n (2*n-1) Salt Digest =>
      labelledRefreshed codec n before cells background observe coin ≠
        labelledPrepared codec n before cells background observe coin).card ≤
      numerator (Fintype.card Salt) (Fintype.card Digest) n (prior before background).card := by
  apply le_trans (card_le_card ?_)
    (bad_card codec n positive codecInjective (cells (before.run background).1) (prior before background))
  intro coin member
  by_contra outside
  have good := prepared_off_bad codec n before cells positive background coin outside
  let H := refreshFor codec n before cells coin.1 (background,coin.2)
  have request : (before.run H.1).1 = (before.run background).1 := by
    have old := MerkleRefresh.prior_refresh (MerkleCommitRefresh.initial before)
      (MerkleCommitRefresh.input codec n (fun _ => coin.1) cells) (MerkleCommitRefresh.update n)
      (2*n-1) (le_refl _) (background,coin.2)
    simpa only [H,refreshFor,MerkleCommitRefresh.initial,Tree.run_map] using
      congrArg (fun run => run.1.1) old
  have labels : honestLabels codec n before cells coin.1 H.1 = coin.2 := by
    unfold honestLabels
    rw [request]
    change actualLabels codec n coin.1 (cells (before.run background).1)
      (refreshFor codec n before cells coin.1 (background,coin.2)).1 = _
    rw [show (refreshFor codec n before cells coin.1 (background,coin.2)).1 =
      MerkleCache.prepared codec n coin.1 (cells (before.run background).1) coin.2 background from good.2]
    exact prepared_labels codec n positive coin.1 _ coin.2 background good.1
  apply (mem_filter.mp member).2
  change observe coin.1 (before.run H.1).1 H.1 (honestLabels codec n before cells coin.1 H.1) = _
  rw [labels,request]
  exact congrArg (fun oracle => observe coin.1 (before.run background).1 oracle coin.2) good.2

theorem labelled_fixed_statClose (atLeastTwo : 1 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest)
    (observe : (Fin n → Salt) → Request → (Enc → Digest) → (Fin (2*n-1) → Digest) → Value) :
    StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (labelledRefreshed codec n before cells background observe)
      (labelledPrepared codec n before cells background observe) := by
  have counted : CountingClose _ _ _ := labelled_disagreement_card codec n before cells
    (by omega) codecInjective background observe
  have normalized := LfzkV1.ZkMerkle.statClose_of_countingClose counted
  apply StatClose.mono _ normalized
  have size : Fintype.card (HidingSample n (2*n-1) Salt Digest) =
      Fintype.card Salt^n*Fintype.card Digest^(2*n-1) := by simp [HidingSample]
  rw [size]
  push_cast
  exact (numerator_ratio_le _ _ _ _ Fintype.card_pos Fintype.card_pos atLeastTwo).trans
    (error_mono _ _ _ (prior_card before background))

theorem labelled_preparation_statClose [Fintype Enc]
    (atLeastTwo : 1 < n) (codecInjective : codec.Inj)
    (observe : (Fin n → Salt) → Request → (Enc → Digest) → (Fin (2*n-1) → Digest) → Value) :
    StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        observe coin.2.1 (before.run coin.1).1 coin.1 (honestLabels codec n before cells coin.2.1 coin.1))
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        labelledPrepared codec n before cells coin.1 observe coin.2) := by
  have nonnegative : 0 ≤ error (Fintype.card Salt) (Fintype.card Digest) n fuel := by
    unfold error
    positivity
  have mixture : StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        labelledRefreshed codec n before cells coin.1 observe coin.2)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        labelledPrepared codec n before cells coin.1 observe coin.2) :=
    statClose_mix nonnegative
      (fun background => labelledRefreshed codec n before cells background observe)
      (fun background => labelledPrepared codec n before cells background observe)
      (fun background => labelled_fixed_statClose codec n before cells atLeastTwo codecInjective background observe)
  apply statClose_reindex (refreshEquiv codec n before cells).symm (Equiv.refl _) _ (fun _ => rfl) mixture
  intro coin
  exact (congrArg
    (fun result : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
      observe result.2.1 (before.run result.1).1 result.1 (honestLabels codec n before cells result.2.1 result.1))
    ((refreshEquiv codec n before cells).apply_symm_apply coin)).symm

end LfzkV2.Current.ZeroKnowledge.MerklePreparation
