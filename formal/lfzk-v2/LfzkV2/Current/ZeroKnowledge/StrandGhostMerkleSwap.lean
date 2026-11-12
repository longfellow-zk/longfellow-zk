import LfzkV2.Current.ZeroKnowledge.MerklePrequery

/-! Move fresh, indexed leaf answers to independent leaf-digest coins.

The leaf addresses may depend on the complete earlier oracle computation.
The swap checks its actual trace; on a previous leaf query it does nothing.
It is a total involution, not an assertion that all inputs are fresh. The
prior result and every earlier raw query/answer are preserved exactly. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap
open Merkle.RandomOracle LigeroFamily
open scoped Classical

variable {Index Raw Digest Context : Type}

/-- Replace only the enumerated leaf coordinates. The embedding is supplied
by the indexed leaf encoding; all other hash inputs retain their answers. -/
def replace (points : Index ↪ Raw) (H : Raw → Digest) (values : Index → Digest) : Raw → Digest :=
  fun raw => match Function.partialInv points raw with
    | none => H raw
    | some index => values index

theorem replace_at (points : Index ↪ Raw) (H : Raw → Digest) (values : Index → Digest)
    (index : Index) : replace points H values (points index) = values index := by
  simp only [replace,Function.partialInv_left points.injective]

theorem replace_off (points : Index ↪ Raw) (H : Raw → Digest) (values : Index → Digest)
    (raw : Raw) (outside : ∀ index, raw ≠ points index) : replace points H values raw = H raw := by
  unfold replace
  cases found : Function.partialInv points raw with
  | none => rfl
  | some index =>
      have same := (points.injective.isPartialInv index raw).mp found
      exact False.elim (outside index same.symm)

/-- The same finite programming preserves agreement at every address
where the original two tables agree. No freshness premise is needed. -/
theorem replace_congr (points : Index ↪ Raw) (first second : Raw → Digest) (values : Index → Digest)
    (raw : Raw) (same : first raw = second raw) :
    replace points first values raw = replace points second values raw := by
  unfold replace
  cases Function.partialInv points raw with
  | none => exact same
  | some _ => rfl

theorem replace_restore (points : Index ↪ Raw) (H : Raw → Digest) (values : Index → Digest) :
    replace points (replace points H values) (fun index => H (points index)) = H := by
  funext raw
  unfold replace
  cases found : Function.partialInv points raw with
  | none => rfl
  | some index =>
      have same := (points.injective.isPartialInv index raw).mp found
      exact congrArg H same

variable {preQueries : ℕ}
variable (before : Tree Raw Digest Context preQueries) (addresses : Context → Index ↪ Raw)

def fresh (H : Raw → Digest) : Prop :=
  ∀ entry ∈ (before.run H).2, ∀ index, entry.1 ≠ addresses (before.run H).1 index

theorem before_replace (H : Raw → Digest) (values : Index → Digest) (unused : fresh before addresses H) :
    before.run (replace (addresses (before.run H).1) H values) = before.run H := by
  apply Tree.run_congr_on_trace
  intro entry member
  rw [replace_off _ _ _ _ (unused entry member)]
  exact (Tree.trace_sound before H entry member).symm

theorem fresh_replace (H : Raw → Digest) (values : Index → Digest) (unused : fresh before addresses H) :
    fresh before addresses (replace (addresses (before.run H).1) H values) := by
  unfold fresh
  rw [before_replace before addresses H values unused]
  exact unused

/-- Refuse to overwrite a previously queried coordinate. This guard makes
the sampling coupling a permutation on every oracle, including bad branches. -/
def swap (coins : (Raw → Digest) × (Index → Digest)) : (Raw → Digest) × (Index → Digest) :=
  if fresh before addresses coins.1 then
    (replace (addresses (before.run coins.1).1) coins.1 coins.2,
      fun index => coins.1 (addresses (before.run coins.1).1 index))
  else coins

theorem swap_involutive : Function.Involutive (swap before addresses) := by
  rintro ⟨H,values⟩
  by_cases unused : fresh before addresses H
  · have next := fresh_replace before addresses H values unused
    have prior := before_replace before addresses H values unused
    simp only [swap,unused,next,↓reduceIte,prior]
    apply Prod.ext
    · exact replace_restore _ H values
    · funext index
      exact replace_at _ H values index
  · simp only [swap,unused,↓reduceIte]

def equiv : ((Raw → Digest) × (Index → Digest)) ≃ ((Raw → Digest) × (Index → Digest)) where
  toFun := swap before addresses
  invFun := swap before addresses
  left_inv := swap_involutive before addresses
  right_inv := swap_involutive before addresses

/-- Equality includes the complete earlier trace, not only its returned
request. In particular the request is allowed to depend on those answers. -/
theorem before_swap (coins : (Raw → Digest) × (Index → Digest)) :
    before.run (swap before addresses coins).1 = before.run coins.1 := by
  unfold swap
  split_ifs with unused
  · exact before_replace before addresses coins.1 coins.2 unused
  · rfl

theorem swap_leaf (coins : (Raw → Digest) × (Index → Digest))
    (unused : fresh before addresses coins.1) (index : Index) :
    (swap before addresses coins).1 (addresses (before.run coins.1).1 index) = coins.2 index := by
  simp only [swap,unused,↓reduceIte]
  exact replace_at _ _ _ index

/-- This is only a uniform-oracle change of variables. Hiding follows
separately by bounding actual leaf queries of the later observer. -/
theorem sameDistribution [Fintype Raw] [Fintype Index] [Fintype Digest]
    {Observed : Type} [DecidableEq Observed]
    (observe : ((Raw → Digest) × (Index → Digest)) → Observed) :
    SameDistribution (fun coins => observe (swap before addresses coins)) observe := by
  apply sameDistribution_of_equiv (equiv before addresses)
  intro coins
  rfl

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap
