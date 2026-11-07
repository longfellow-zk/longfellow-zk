import LfzkV2.Current.ZeroKnowledge.MerkleCacheBackend

/-! Retained-cache tests include repeat queries: programming fresh honest
commitment inputs must preserve both the old values and the old full trace. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleCache
open Merkle Merkle.MH Merkle.RandomOracle ZeroKnowledge

example {Salt Message D Enc : Type} [Inhabited D] [DecidableEq Enc]
    (C : Codec Salt Message D Enc) (n T : ℕ) (nonce : Fin n → Salt)
    (messages : Fin n → Message) (labels : Fin T → D) (background : Enc → D)
    (query : Enc) (fresh : query ∉ commitSeen C n nonce messages labels) :
    (Tree.query query (fun _ => Tree.query query (fun answer => Tree.done (fuel := 0) answer))).run
        (MerkleCache.prepared C n nonce messages labels background) =
      (background query,[(query,background query),(query,background query)]) := by
  simp only [Tree.run_query,Tree.run_done,
    MerkleCache.prepared_outside C n nonce messages labels background query fresh]

#print axioms MerkleCache.caught_card_le
#print axioms MerkleCache.prior_preserved
#print axioms MerkleCache.commit_run
#print axioms MerkleCache.openingView_eq
#print axioms MerkleCache.opening_hiding
#print axioms MerkleBackend.joint_cache_hiding

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleCache
