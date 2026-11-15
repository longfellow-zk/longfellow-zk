import LfzkV2.Current.ZeroKnowledge.MerkleRefresh
import Merkle.CheckPass

/-! The causal refresh sequence is the actual Merkle commitment pass.
The earlier oracle computation may choose the public request adaptively.
Private nonces and cells are fixed functions of that request, chosen before
the commitment's answers.  No future label is an input to a leaf message.

Step i processes heap vertex 2n−1−i.  A leaf uses its nonce and cells; a
parent uses only the child labels already stored by earlier steps. -/
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

end LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh
