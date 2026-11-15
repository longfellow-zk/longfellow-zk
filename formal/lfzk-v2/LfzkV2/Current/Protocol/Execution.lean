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

/-- The external privacy observation contains the submitted proof and both
observer traces. It excludes the prover's private execution and random tape. -/
abbrev PublicView (Context Output Observed : Type) :=
  (Context × List (Bytes × Digest)) × (Option Output × Observed) × List (Bytes × Digest)

namespace PublicView
variable {Context Output Observed : Type} (view : PublicView Context Output Observed)
abbrev result : Observed := view.2.1.2
end PublicView

structure Program (Output : Type) (fuel : ℕ) where
  tree : Tree Bytes Digest Output fuel

/-- A bound on every total original byte oracle, with repetitions counted
once. No acceptance, extraction or failure-cover premise belongs here. -/
structure Adversary (Output : Type) (fuel queries : ℕ) extends Program Output fuel where
  queryBound : ∀ H, (seen tree H).card ≤ queries

namespace Program
variable {Output Result : Type} {fuel : ℕ}

def bounded (program : Program Output fuel) : Adversary Output fuel fuel where
  tree := program.tree
  queryBound := seen_card_le program.tree

end Program

end LfzkV2.Current.Protocol.Execution
