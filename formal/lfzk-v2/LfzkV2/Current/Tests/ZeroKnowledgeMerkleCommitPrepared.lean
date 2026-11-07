import LfzkV2.Current.ZeroKnowledge.MerkleCommitPrepared

/-! The independent-label analysis retains prior answers even on its bad
repeated-input branches. Freshness and the prepared table are derived only
after excluding the concrete collision and nonce/node guessing events. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitPrepared

open Merkle Merkle.MH ZeroKnowledge.MerkleCommitRefresh

def codec : Codec Unit Unit Bool Bool where
  leafEnc := fun _ => false
  nodeEnc := fun _ => true

def nonce (_ : Unit) (_ : Fin 1) : Unit := ()
def cells (_ : Unit) (_ : Fin 1) : Unit := ()

example (tape : Fin 1 → Bool) :
    (false,true) ∈
      (ZeroKnowledge.MerkleRefresh.sampledRun (input codec 1 nonce cells) (update 1)
        (((),fun _ => false),[(false,true)]) tape 1 (by decide)).2 :=
  (sampledRun_trace_mem 1 codec nonce cells () tape _ 1 (by decide) _).mpr (Or.inl (by simp))

example (tape : Fin 1 → Bool) :
    (false,tape 0) ∈
      (ZeroKnowledge.MerkleRefresh.sampledRun (input codec 1 nonce cells) (update 1)
        (((),fun _ => false),[(false,true)]) tape 1 (by decide)).2 :=
  (sampledRun_trace_mem 1 codec nonce cells () tape _ 1 (by decide) _).mpr
    (Or.inr ⟨0,by decide,rfl⟩)

#print axioms sampledRun_trace_mem
#print axioms refresh_fresh
#print axioms refresh_eq_prepared
#print axioms priorAvoids_of_no_hit
#print axioms refresh_eq_prepared_of_no_bad

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitPrepared
