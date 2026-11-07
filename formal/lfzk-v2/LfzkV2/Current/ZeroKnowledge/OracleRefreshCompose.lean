import LfzkV2.Current.ZeroKnowledge.MerklePrequery
import Merkle.TreeCompose

/-! A prior observer can choose the public request adaptively. Appending a
causal honest prefix leaves exactly its external earlier calls to be counted
by the primary-mask hit bound. Local freshness is proved for the concrete
honest program in `HonestTranscriptRefresh`; this module only composes the
two query programs and preserves their full traces. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose
open Merkle.RandomOracle
open scoped Classical
variable {Query Answer Request Pending : Type} {beforeFuel prefixFuel : ℕ}
variable (before : Tree Query Answer Request beforeFuel)
variable (next : Request → Tree Query Answer Pending prefixFuel)
variable (input : Request → Pending → Query)

def append : Tree Query Answer (Request × Pending) (prefixFuel+beforeFuel) :=
  before.bind fun request => (next request).map fun pending => (request,pending)

def target (out : Request × Pending) : Query := input out.1 out.2

theorem append_run (H : Query → Answer) :
    (append before next).run H =
      let old := before.run H
      let fresh := (next old.1).run H
      ((old.1,fresh.1),old.2++fresh.2) := by
  rw [append,Tree.run_bind,Tree.run_map]

/-- The external prefix is retained literally, including repeats and answers.
Only that prefix can have guessed the later honest program's target. -/
theorem fresh_iff_prior (H : Query → Answer)
    (localFresh : MerklePrequery.fresh (next (before.run H).1) (input (before.run H).1) H) :
    MerklePrequery.fresh (append before next) (target input) H ↔
      ∀ qa ∈ (before.run H).2,
        qa.1 ≠ input (before.run H).1 ((next (before.run H).1).run H).1 := by
  simp only [MerklePrequery.fresh,MerklePrequery.location,append_run,target,List.mem_append]
  constructor
  · intro fresh qa member
    exact fresh qa (Or.inl member)
  · intro old qa member
    rcases member with member | member
    · exact old qa member
    · exact localFresh qa member

theorem append_update (H : Query → Answer) (answer : Answer)
    (localFresh : MerklePrequery.fresh (next (before.run H).1) (input (before.run H).1) H)
    (prior : ∀ qa ∈ (before.run H).2,
      qa.1 ≠ input (before.run H).1 ((next (before.run H).1).run H).1) :
    (append before next).run
      (Function.update H (target input ((append before next).run H).1) answer) =
    (append before next).run H :=
  MerklePrequery.prior_update (append before next) (target input) H answer
    ((fresh_iff_prior before next input H localFresh).mpr prior)

end LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose
