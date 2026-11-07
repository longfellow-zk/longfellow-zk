import LfzkV2.Current.ZeroKnowledge.OracleProgramming
import LfzkV2.Current.BackendPath

/-! An honest opening preimage is assembled from the earlier batching
prefix, its answer, and the response computed from those already available
values.  This gives the own-answer independence needed by the fresh-coordinate
swap.  The simulator's Q-dependent response must first be transported by the
backend/common-label coupling; it must not be substituted into this refresh
argument as if it were independent of the sampled opening answer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleOpening
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Context Block C Response : Type}
variable (e : Replay.Encoding g fields Advice Authentication Context Block C)
variable (initial : Digest) (pending : Replay.Output g fields Advice Authentication)
local notation "Point" => Replay.Point g fields Advice Authentication Context Block
local notation "Parent" => BackendQueries.Parent g.roles Context Block Digest g.batchingIndex

def parent (H : Point → Digest × C) : Parent :=
  BackendPath.parent e initial pending H g.batchingIndex

/-- The response generator has only the strict prefix and the batching
answer. It cannot read the opening answer, any future link or the final seal. -/
def point (encode : Response → Block)
    (respond : Parent → (Fin g.batchingIndex.val → C) → (Digest × C) → Response)
    (H : Point → Digest × C) : Point :=
  let p := parent e initial pending H
  p.child g.batchingIndex_next encode
    ((H p.point).1,respond p (p.point.priorAnswers H) (H p.point))

@[simp] theorem point_rank (encode : Response → Block)
    (respond : Parent → (Fin g.batchingIndex.val → C) → (Digest × C) → Response)
    (H : Point → Digest × C) :
    (point e initial pending encode respond H).rank = g.openingIndex.val := rfl

private theorem earlier_replay (encode : Response → Block)
    (respond : Parent → (Fin g.batchingIndex.val → C) → (Digest × C) → Response)
    (H H' : Point → Digest × C)
    (off : Bcs.TotalOracle.AgreeOff (point e initial pending encode respond H) H H') :
    (e.chain initial).point pending H g.batchingIndex.val =
      (e.chain initial).point pending H' g.batchingIndex.val := by
  apply congrArg (e.chain initial).input
  apply (e.chain initial).replay_congr_prefix
  intro index before
  apply off
  intro equal
  have hr := (e.chain initial).point_rank pending H
    (show index ≤ g.roles.length by have := g.batchingIndex.isLt; omega)
  have ht := point_rank e initial pending encode respond H
  change Input.rank _ = index at hr
  rw [equal] at hr
  have next := g.openingIndex_val
  omega

/-- The actual prior prefix is unchanged by replacing the answer at this
opening input. This is derived from the increasing query counters. -/
theorem parent_off (encode : Response → Block)
    (respond : Parent → (Fin g.batchingIndex.val → C) → (Digest × C) → Response)
    (H H' : Point → Digest × C)
    (off : Bcs.TotalOracle.AgreeOff (point e initial pending encode respond H) H H') :
    parent e initial pending H = parent e initial pending H' := by
  apply BackendQueries.Parent.point_injective (Body := Body g fields Advice Authentication)
  rw [parent,BackendPath.parent_point,parent,BackendPath.parent_point]
  exact earlier_replay e initial pending encode respond H H' off

theorem point_off (encode : Response → Block)
    (respond : Parent → (Fin g.batchingIndex.val → C) → (Digest × C) → Response)
    (H H' : Point → Digest × C)
    (off : Bcs.TotalOracle.AgreeOff (point e initial pending encode respond H) H H') :
    point e initial pending encode respond H = point e initial pending encode respond H' := by
  have hp := parent_off e initial pending encode respond H H' off
  let p := parent e initial pending H
  have hbatch : H p.point = H' p.point := by
    apply off
    intro equal
    have hr := congrArg Input.rank equal
    change g.batchingIndex.val = g.openingIndex.val at hr
    have next := g.openingIndex_val
    omega
  have hprior : p.point.priorAnswers H = p.point.priorAnswers H' := by
    funext i
    apply congrArg Prod.snd
    apply off
    intro equal
    have hr := p.point.priorPoints_rank i
    rw [equal] at hr
    have ht := point_rank e initial pending encode respond H
    have hi := i.isLt
    change i.val < g.batchingIndex.val at hi
    have next := g.openingIndex_val
    omega
  unfold point
  rw [← hp]
  change p.child _ _ ((H p.point).1,respond p (p.point.priorAnswers H) (H p.point)) =
    p.child _ _ ((H' p.point).1,respond p (p.point.priorAnswers H') (H' p.point))
  rw [hbatch,hprior]

end LfzkV2.Current.ZeroKnowledge.OracleOpening
