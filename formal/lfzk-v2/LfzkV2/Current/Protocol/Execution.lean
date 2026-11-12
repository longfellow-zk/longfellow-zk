import LfzkV2.Current.Messages
import LfzkV2.Current.PrefixCodec
import TranscriptV2.Queries

/-! Shared execution data. Original adversarial queries and verifier replay
remain separate; only the original query log supplies commitment evidence. -/
noncomputable section
namespace LfzkV2.Current.Protocol.Execution
open Merkle.RandomOracle TranscriptV2
open scoped Classical

@[ext] structure View (Output Result Context : Type) where
  original : Output × List (Bytes × Digest)
  verifier : Result × List (Bytes × Digest)
  cuts : Context → List (Bytes × Digest)

structure Program (Output : Type) (fuel : ℕ) where
  tree : Tree Bytes Digest Output fuel

/-- A bound on every total original byte oracle, with repetitions counted
once. No acceptance, extraction or failure-cover premise belongs here. -/
structure Adversary (Output : Type) (fuel queries : ℕ) extends Program Output fuel where
  queryBound : ∀ H, (seen tree H).card ≤ queries

namespace Program
variable {Output Result : Type} {fuel : ℕ}

def map (program : Program Output fuel) (decode : Output → Result) : Program Result fuel :=
  ⟨program.tree.map decode⟩

def bounded (program : Program Output fuel) : Adversary Output fuel fuel where
  tree := program.tree
  queryBound := seen_card_le program.tree

end Program

namespace Adversary
variable {Output Result : Type} {fuel queries : ℕ}

/-- Pure complete-proof parsing changes the submitted output and preserves
the adversary's exact original query trace and budget. -/
def map (adversary : Adversary Output fuel queries) (decode : Output → Result) :
    Adversary Result fuel queries where
  tree := adversary.tree.map decode
  queryBound H := by
    simpa only [seen, Bcs.TotalOracle.queried, Tree.run_map] using adversary.queryBound H

end Adversary
end LfzkV2.Current.Protocol.Execution
