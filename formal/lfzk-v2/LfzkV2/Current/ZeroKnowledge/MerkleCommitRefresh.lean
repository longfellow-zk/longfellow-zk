import LfzkV2.Current.ZeroKnowledge.MerkleRefresh
import Merkle.CheckPass

/-! The causal refresh sequence is the actual Merkle commitment pass.
The earlier oracle computation may choose the public request adaptively.
Private nonces and cells are fixed functions of that request, chosen before
the commitment's answers.  No future label is an input to a leaf message.

Step i processes heap vertex 2n−1−i.  A leaf uses its nonce and cells; a
parent uses only the child labels already stored by earlier steps.  The
theorem retains the complete earlier and commitment query/answer traces. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh

open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Enc Request : Type}
variable [DecidableEq Enc] [Inhabited Digest]
variable (codec : Codec Salt Message Digest Enc) (n : ℕ)
variable (nonce : Request → Fin n → Salt) (cells : Request → Fin n → Message)

abbrev State (Request Digest : Type) := Request × (ℕ → Digest)

def input (count : ℕ) (state : State Request Digest) : Enc :=
  let vertex := 2*n-1-count
  if leaf : n ≤ vertex ∧ vertex < 2*n then
    codec.leafEnc (nonce state.1 ⟨vertex-n,by omega⟩,cells state.1 ⟨vertex-n,by omega⟩)
  else codec.nodeEnc (state.2 (2*vertex),state.2 (2*vertex+1))

def update (count : ℕ) (state : State Request Digest) (answer : Digest) : State Request Digest :=
  (state.1,Function.update state.2 (2*n-1-count) answer)

def initial {fuel : ℕ} (before : Tree Enc Digest Request fuel) :
    Tree Enc Digest (State Request Digest) fuel :=
  before.map fun request => (request,fun _ => default)

def actual {fuel : ℕ} (before : Tree Enc Digest Request fuel) :
    Tree Enc Digest (State Request Digest) ((2*n-1)+fuel) :=
  before.bind fun request =>
    (commitPass codec n (nonce request) (cells request) (2*n-1) (fun _ => default)).map
      fun values => (request,values)

/-- Finish the unprocessed suffix, retaining the complete earlier trace. -/
def finish (remaining : ℕ) (H : Enc → Digest)
    (earlier : State Request Digest × List (Enc × Digest)) :
    State Request Digest × List (Enc × Digest) :=
  let rest := (commitPass codec n (nonce earlier.1.1) (cells earlier.1.1) remaining earlier.1.2).run H
  ((earlier.1.1,rest.1),earlier.2++rest.2)

theorem finish_zero (H : Enc → Digest) (earlier : State Request Digest × List (Enc × Digest)) :
    finish codec n nonce cells 0 H earlier = earlier := by
  simp only [finish,commitPass,Tree.run_done,List.append_nil]

theorem finish_step (count : ℕ) (inside : count < 2*n-1) (H : Enc → Digest)
    (state : State Request Digest) (trace : List (Enc × Digest)) :
    finish codec n nonce cells (2*n-1-(count+1)) H
      (update n count state (H (input codec n nonce cells count state)),
        trace++[(input codec n nonce cells count state,H (input codec n nonce cells count state))]) =
      finish codec n nonce cells (2*n-1-count) H (state,trace) := by
  let remaining := 2*n-1-(count+1)
  have vertex : 2*n-1-count = remaining+1 := by dsimp [remaining]; omega
  have bound : remaining+1 < 2*n := by dsimp [remaining]; omega
  by_cases leaf : n ≤ remaining+1 ∧ remaining+1 < 2*n
  · have query : input codec n nonce cells count state =
        codec.leafEnc (nonce state.1 ⟨remaining+1-n,by omega⟩,
          cells state.1 ⟨remaining+1-n,by omega⟩) := by
      simp only [input,vertex,dif_pos leaf]
    rw [query]
    unfold finish update
    rw [vertex]
    rw [commitPass_step_leaf codec n (nonce state.1) (cells state.1) remaining state.2 leaf,
      Tree.run_query]
    simp only [List.append_assoc,List.singleton_append]
    rfl
  · have node : 0 < remaining+1 ∧ remaining+1 < n := by omega
    have query : input codec n nonce cells count state =
        codec.nodeEnc (state.2 (2*(remaining+1)),state.2 (2*(remaining+1)+1)) := by
      simp only [input,vertex,dif_neg leaf]
    rw [query]
    unfold finish update
    rw [vertex]
    rw [commitPass_step_node codec n (nonce state.1) (cells state.1) remaining state.2 leaf node,
      Tree.run_query]
    simp only [List.append_assoc,List.singleton_append]
    rfl

variable {fuel : ℕ} (before : Tree Enc Digest Request fuel)

omit [DecidableEq Enc] in
theorem history_request (count : ℕ) (H : Enc → Digest) :
    ((MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) count).run H).1.1 =
      (before.run H).1 := by
  induction count with
  | zero => simp only [MerkleRefresh.history,initial,Tree.run_map]
  | succ count ih =>
      rw [MerkleRefresh.history_next]
      exact ih

theorem history_finish (count : ℕ) (inside : count ≤ 2*n-1) (H : Enc → Digest) :
    finish codec n nonce cells (2*n-1-count) H
      ((MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) count).run H) =
      finish codec n nonce cells (2*n-1) H ((initial before).run H) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [MerkleRefresh.history_next]
      rw [finish_step codec n nonce cells count (by omega)]
      exact ih (by omega)

/-- Exact correspondence with the current honest commitment, including
repeated queries and every answer in the prior observer's trace. -/
theorem history_actual (H : Enc → Digest) :
    (MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) (2*n-1)).run H =
      (actual codec n nonce cells before).run H := by
  have result := history_finish codec n nonce cells before (2*n-1) (le_refl _) H
  rw [Nat.sub_self,finish_zero] at result
  simpa only [finish,
    initial,actual,Tree.run_bind,Tree.run_map] using result

/-- The root produced by the refresh schedule is the honest root for the
adaptively selected request. This is a deterministic equality for every oracle. -/
theorem history_root (positive : 0 < n) (H : Enc → Digest) :
    ((MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) (2*n-1)).run H).1.2 1 =
      root (codec.withOracle H) n (nonce (before.run H).1) (cells (before.run H).1) := by
  rw [history_actual codec n nonce cells before]
  simp only [actual,Tree.run_bind,Tree.run_map]
  apply commitPass_run
  · intro vertex beyond
    exact (commitLabels_of_ge (S := codec.withOracle H) n _ _ vertex (by omega)).symm
  · omega

end LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh
