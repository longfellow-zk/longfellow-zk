import LfzkV2.Current.ZeroKnowledge.MerkleBound

/-! A commitment programs its own fresh inputs, leaving a pre-existing
oracle table intact everywhere else.  Unlike an empty-cache lazy execution,
this representation retains every earlier oracle answer.  The freshness
splice supplies disjointness from the prior trace; hiding then compares two
such prepared tables over the same unchanged background oracle.

The background may be any total function. It is not exposed to the observer,
which accesses it only through its bounded query tree. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCache
open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

section Prepared
variable {Salt Message Digest Enc Observed : Type}
variable [Inhabited Digest] [DecidableEq Enc]
variable (C : Codec Salt Message Digest Enc) (n : ℕ)
variable (nonce : Fin n → Salt) (message : Fin n → Message)
variable {T : ℕ} (labels : Fin T → Digest) (background : Enc → Digest)

/-- Replace only the commitment's inputs. Every other answer, including
every retained prior cache entry, stays the background oracle's answer. -/
def prepared : Enc → Digest := fun query =>
  if query ∈ commitSeen C n nonce message labels then
    commitOracle C n nonce message labels query else background query

theorem prepared_outside (query : Enc)
    (outside : query ∉ commitSeen C n nonce message labels) :
    prepared C n nonce message labels background query = background query := by
  rw [prepared,if_neg outside]

end Prepared

end LfzkV2.Current.ZeroKnowledge.MerkleCache
