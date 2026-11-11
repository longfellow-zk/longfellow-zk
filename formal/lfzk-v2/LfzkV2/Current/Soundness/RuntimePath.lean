import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.ReplayPrefix
import Survival.PrefixCache
import TranscriptV2.Composition

/-! The actual replay family supplies all strict ancestors on its recovered
query path. These are exact preimages, including messages and digest links. -/
noncomputable section
namespace Survival.RuntimePath
open LfzkV2.Current Merkle.RandomOracle TranscriptV2
open scoped Classical

variable {g : Geometry} {F : Fields} {Advice Auth Key Block C Request Aux Out : Type}
variable (encodings : Request → Replay.Encoding g F Advice Auth Key Block C) (initial : Digest)
local notation "Point" => Replay.Point g F Advice Auth Key Block
local notation "Output" => RuntimeAdaptive.Output (g := g) (fields := F) (Advice := Advice)
  (Auth := Auth) (Request := Request)
local notation "M" => RuntimeAdaptive.chain encodings initial

theorem family_priorPoints (output : Output) (H : Point → Digest × C)
    (index : ℕ) (within : index ≤ g.roles.length) (j : Fin ((M).point output H index).rank) :
    ((M).point output H index).priorPoints j = (M).point output H j.val := by
  have all (earlier : ℕ) (bounded : earlier < ((M).point output H index).rank) :
      ((M).point output H index).priorPoints ⟨earlier,bounded⟩ = (M).point output H earlier := by
    have rank := (M).point_rank output H within
    change Input.rank _ = index at rank
    have atRank : ((M).point output H index).atRank earlier = some ((M).point output H earlier) := by
      rw [RuntimeAdaptive.point_eq, RuntimeAdaptive.point_eq]
      exact (encodings output.request).point_atRank initial output.proof H index earlier within (by omega)
    simp only [Input.atRank, dif_pos bounded] at atRank
    exact Option.some.inj atRank
  exact all j.val j.isLt

theorem ancestors_before {A : Type} [Fintype A] [queryDecidable : DecidableEq (Point ⊕ Aux)] {fuel : ℕ}
    (tree : Tree (Point ⊕ Aux) (Digest × A) Out fuel) (G : Point ⊕ Aux → Digest × A)
    (output : Output) (H : Point → Digest × C)
    (path : Composition.PathQueries (rounds := g.roles.length) tree G
      (fun index => .inl ((M).point output H index)))
    (index : ℕ) (within : index ≤ g.roles.length) (j : Fin ((M).point output H index).rank) :
    (Sum.inl (((M).point output H index).priorPoints j) : Point ⊕ Aux) ∈
      before tree G (.inl ((M).point output H index)) := by
  rw [family_priorPoints encodings initial output H index within j]
  apply PrefixCache.earlier_path_before tree G (fun i => .inl ((M).point output H i))
    path.queried path.ordered ?_ index within j.val ?_
  · intro i hi same
    have equal := congrArg Input.rank (Sum.inl.inj same)
    have leftRank := (M).point_rank output H hi.le
    have rightRank := (M).point_rank output H (Nat.succ_le_of_lt hi)
    change Input.rank _ = i at leftRank
    change Input.rank _ = i+1 at rightRank
    have impossible : i = i+1 := leftRank.symm.trans (equal.trans rightRank)
    omega
  · have rank := (M).point_rank output H within
    change Input.rank _ = index at rank
    have := j.isLt
    omega

end Survival.RuntimePath
