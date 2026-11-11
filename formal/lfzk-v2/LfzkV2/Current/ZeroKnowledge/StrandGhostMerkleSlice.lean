import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleProbability
import LfzkV2.Current.ZeroKnowledge.StrandLeafOracle

/-! The leaf-answer permutation acts on a finite oracle slice. The rest of
the byte oracle is fixed pointwise, including transcript and internal-node
answers. This avoids imposing a finite type on all possible byte strings.
The prior computation still runs against the complete byte oracle and keeps
its actual trace; no query or answer is erased by conditioning on the slice. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap.Slice
open Merkle.RandomOracle
open scoped Classical

variable {Leaf Index Raw Digest Context : Type} {fuel : ℕ}
variable (encode : Leaf ↪ Raw) (outside : Raw → Digest)

private theorem reconstruct (H : Raw → Digest)
    (off : ∀ raw, (∀ leaf, raw ≠ encode leaf) → H raw = outside raw) :
    oracle encode outside (fun leaf => H (encode leaf)) = H := by
  funext raw
  unfold oracle replace
  cases found : Function.partialInv encode raw with
  | none =>
      apply Eq.symm
      apply off raw
      intro leaf same
      have decoded := Function.partialInv_left encode.injective leaf
      rw [← same,found] at decoded
      cases decoded
  | some leaf =>
      exact congrArg H ((encode.injective.isPartialInv leaf raw).mp found)

variable (before : Tree Raw Digest Context fuel) (points : Context → Index ↪ Leaf)

def swap (coins : (Leaf → Digest) × (Index → Digest)) :
    (Leaf → Digest) × (Index → Digest) :=
  let moved := Swap.swap before (fun context => (points context).trans encode)
    (oracle encode outside coins.1,coins.2)
  (fun leaf => moved.1 (encode leaf),moved.2)

/-- The finite-table swap is exactly the original raw-oracle swap. Its
support is contained in the leaf slice, even on prior-query conflicts. -/
theorem lift_swap (coins : (Leaf → Digest) × (Index → Digest)) :
    (oracle encode outside (swap encode outside before points coins).1,
      (swap encode outside before points coins).2) =
    Swap.swap before (fun context => (points context).trans encode)
      (oracle encode outside coins.1,coins.2) := by
  apply Prod.ext
  · apply reconstruct
    intro raw off
    unfold Swap.swap
    split_ifs
    · dsimp only
      rw [replace_off ((points (before.run (oracle encode outside coins.1)).1).trans encode)
        (oracle encode outside coins.1) coins.2 raw (fun index => off _)]
      exact replace_off encode outside coins.1 raw off
    · exact replace_off encode outside coins.1 raw off
  · rfl

theorem swap_involutive : Function.Involutive (swap encode outside before points) := by
  intro coins
  have lifted := lift_swap encode outside before points (swap encode outside before points coins)
  rw [lift_swap encode outside before points coins,Swap.swap_involutive] at lifted
  apply Prod.ext
  · exact oracle_injective encode outside (congrArg Prod.fst lifted)
  · exact congrArg (fun pair : (Raw → Digest) × (Index → Digest) => pair.2) lifted

def equiv : ((Leaf → Digest) × (Index → Digest)) ≃ ((Leaf → Digest) × (Index → Digest)) where
  toFun := swap encode outside before points
  invFun := swap encode outside before points
  left_inv := swap_involutive encode outside before points
  right_inv := swap_involutive encode outside before points

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap.Slice

namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
open Merkle Merkle.Indexed LigeroFamily
open scoped Classical

variable {Salt Message Digest Raw Context Result : Type} {n preFuel postFuel : ℕ}
local instance : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)
variable (before : RandomOracle.Tree Raw Digest Context preFuel)
variable (columns : Context → Fin n → Message)
variable (prepare : Context → (Observer.Other codec dec → Digest) → Digest →
  Schedule.Prepared n Salt Message Digest Raw Result postFuel)
variable [Inhabited Digest]
variable (abort : Context → RandomOracle.Tree Raw Digest Result postFuel)
variable (separated : ∀ index children salt message,
  codec.nodeEnc index children ≠ codec.leafEnc (salt,message))

private def leafPoints (nonces : Fin n → Salt) (context : Context) :
    Fin n ↪ ((Fin n × Salt) × Message) where
  toFun index := ((index,nonces index),columns context index)
  inj' _ _ same := congrArg (fun value => value.1.1) same

include separated in
/-- Hiding for an arbitrary fixed non-leaf oracle. Only the finite leaf
table, nonce vector, and auxiliary ghost labels are sampled. All queries
still have their original raw addresses, and the full prior/later view is
retained. Averaging over the independent non-leaf oracle is a later step. -/
theorem statistical_hiding_slice [Fintype Salt] [Nonempty Salt]
    [Fintype Message] [Fintype Digest] (outside : Raw → Digest) :
    StatClose ((preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ))
      (fun coin : Coins n Salt ((Fin n × Salt) × Message) Digest =>
        Schedule.honest codec dec before columns prepare
          (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.1)
      (fun coin : Coins n Salt ((Fin n × Salt) × Message) Digest =>
        Schedule.simulate codec dec before columns prepare abort
          (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.2.2
          (fun index => coin.1 index.val)) := by
  let change := Equiv.prodCongrRight fun nonces : Fin n → Salt =>
    Swap.Slice.equiv (leafEmbedding codec dec) outside before (leafPoints columns nonces)
  let real := fun coin : Coins n Salt ((Fin n × Salt) × Message) Digest =>
    Schedule.honest codec dec before columns prepare
      (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.1
  let ideal := fun coin : Coins n Salt ((Fin n × Salt) × Message) Digest =>
    Schedule.simulate codec dec before columns prepare abort
      (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.2.2
      (fun index => coin.1 index.val)
  have nonnegative : (0 : ℚ) ≤ (preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have mixed := statClose_mix nonnegative
    (fun outer : (((Fin n × Salt) × Message) → Digest) × (Fin n → Digest) =>
      fun nonces : Fin n → Salt => Schedule.honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns
          (Swap.Slice.oracle (leafEmbedding codec dec) outside outer.1) nonces outer.2) nonces)
    (fun outer : (((Fin n × Salt) × Message) → Digest) × (Fin n → Digest) =>
      fun nonces : Fin n → Salt => Schedule.simulate codec dec before columns prepare abort
        (Swap.Slice.oracle (leafEmbedding codec dec) outside outer.1) outer.2
        (fun index => nonces index.val))
    (fun outer => fixed_oracle_close codec dec before columns prepare abort separated _ outer.2)
  let order := Equiv.prodComm (Fin n → Salt)
    ((((Fin n × Salt) × Message) → Digest) × (Fin n → Digest))
  have shifted : StatClose ((preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ))
      (fun coin => real (change coin)) ideal := by
    apply statClose_reindex order order _ (fun _ => rfl) mixed
    intro coin
    change Schedule.honest codec dec before columns prepare
        (Swap.Slice.oracle (leafEmbedding codec dec) outside
          (Swap.Slice.swap (leafEmbedding codec dec) outside before (leafPoints columns coin.1) coin.2).1) coin.1 =
      Schedule.honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns
          (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.1 coin.2.2) coin.1
    rw [show Swap.Slice.oracle (leafEmbedding codec dec) outside
        (Swap.Slice.swap (leafEmbedding codec dec) outside before (leafPoints columns coin.1) coin.2).1 =
        History.coupledOracle codec dec before columns
          (Swap.Slice.oracle (leafEmbedding codec dec) outside coin.2.1) coin.1 coin.2.2 from
      congrArg Prod.fst (Swap.Slice.lift_swap (leafEmbedding codec dec) outside before
        (leafPoints columns coin.1) coin.2)]
  apply statClose_reindex change.symm
    (Equiv.refl (Coins n Salt ((Fin n × Salt) × Message) Digest)) _ (fun _ => rfl) shifted
  intro coin
  rw [Equiv.apply_symm_apply]

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
