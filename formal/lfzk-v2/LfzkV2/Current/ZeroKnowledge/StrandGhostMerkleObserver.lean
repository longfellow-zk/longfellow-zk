import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleTree
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleNonce

/-! The ghost observer sees ordinary oracle answers except at opened leaves.
This boundary exposes all later raw queries, including adaptive repeats.
Only an actual query at a hidden leaf can distinguish the two oracle tables;
no digest distinctness or collision-free execution is assumed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Observer
open Merkle Merkle.Indexed Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Raw Result : Type} {n fuel : ℕ}
local instance : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)

variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)

/-- Transcript and internal-tree inputs occupy the non-leaf slice. A program
on this query type cannot secretly inspect a hidden leaf answer. -/
def Other := {raw : Raw // dec.leafDec raw = none}

def candidate (raw : Raw) : Option (Fin n × Salt) :=
  (dec.leafDec raw).map Prod.fst

theorem candidate_leaf (index : Fin n) (nonce : Salt) (message : Message) :
    candidate codec dec (codec.leafEnc ((index,nonce),message)) = some (index,nonce) := by
  simp only [candidate,dec.leaf_roundTrip,Option.map_some]

theorem installAll_other (H : Raw → Digest) (nonces : Fin n → Salt)
    (columns : Fin n → Message) (leaves : Fin n → Digest) (raw : Other codec dec) :
    Tree.installAll codec dec H nonces columns leaves raw.val = H raw.val := by
  apply Swap.replace_off
  intro index equal
  have decoded := congrArg dec.leafDec equal
  change dec.leafDec raw.val = dec.leafDec (codec.leafEnc _) at decoded
  rw [raw.property,dec.leaf_roundTrip] at decoded
  contradiction

theorem installOpened_other (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : I → Salt) (columns : I → Message) (leaves : Fin n → Digest)
    (raw : Other codec dec) :
    Tree.installOpened codec dec H I nonces columns leaves raw.val = H raw.val := by
  apply Swap.replace_off
  intro index equal
  have decoded := congrArg dec.leafDec equal
  change dec.leafDec raw.val = dec.leafDec (codec.leafEnc _) at decoded
  rw [raw.property,dec.leaf_roundTrip] at decoded
  contradiction

/-- Away from actual hidden leaf preimages, the full honest installation
and the public opened-only installation agree exactly. -/
theorem install_agree (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : Fin n → Salt) (columns : Fin n → Message) (leaves : Fin n → Digest)
    (raw : Raw) (miss : ∀ index, index ∉ I →
      raw ≠ codec.leafEnc ((index,nonces index),columns index)) :
    Tree.installAll codec dec H nonces columns leaves raw =
      Tree.installOpened codec dec H I (fun index => nonces index.val)
        (fun index => columns index.val) leaves raw := by
  by_cases present : ∃ index, raw = codec.leafEnc ((index,nonces index),columns index)
  · obtain ⟨index,rfl⟩ := present
    have member : index ∈ I := by
      by_contra outside
      exact miss index outside rfl
    rw [Tree.installAll_leaf]
    exact (Tree.installOpened_leaf codec dec H I (fun index => nonces index.val)
      (fun index => columns index.val) leaves ⟨index,member⟩).symm
  · have outside : ∀ index, raw ≠ codec.leafEnc ((index,nonces index),columns index) := by
      simpa only [not_exists] using present
    rw [Tree.installAll,Swap.replace_off _ _ _ _ outside,
      Tree.installOpened,Swap.replace_off _ _ _ _ (fun index => outside index.val)]

/-- The complete later view includes the full raw query/answer trace.
The observer may choose every later query from earlier returned answers. -/
def observe (H : Raw → Digest) (I : Finset (Fin n))
    (leaves : Fin n → Digest) (columns : I → Message)
    (after : (I → Salt) → RandomOracle.Tree Raw Digest Result fuel)
    (revealed : I → Salt) : Result × List (Raw × Digest) :=
  (after revealed).run (Tree.installOpened codec dec H I revealed columns leaves)

theorem trace_length {fuel : ℕ} (body : RandomOracle.Tree Raw Digest Result fuel)
    (H : Raw → Digest) : (body.run H).2.length ≤ fuel := by
  induction body with
  | done out => simp only [RandomOracle.Tree.run_done,List.length_nil]; omega
  | query raw next ih =>
      simpa only [RandomOracle.Tree.run_query,List.length_cons] using
        Nat.add_le_add_right (ih (H raw)) 1

theorem observe_length (H : Raw → Digest) (I : Finset (Fin n))
    (leaves : Fin n → Digest) (columns : I → Message)
    (after : (I → Salt) → RandomOracle.Tree Raw Digest Result fuel)
    (revealed : I → Salt) :
    (observe codec dec H I leaves columns after revealed).2.length ≤ fuel :=
  trace_length _ _

/-- This is a deterministic equality off a concrete nonce-hit event, not
an assumed observer bound. The probability is supplied separately by the
indexed off-coordinate counting theorem. -/
theorem observer_eq_of_no_hit (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : Fin n → Salt) (columns : Fin n → Message) (leaves : Fin n → Digest)
    (after : (I → Salt) → RandomOracle.Tree Raw Digest Result fuel)
    (prior : List Raw)
    (miss : ¬ StrandGhostMerkle.Nonce.Hit (candidate codec dec) I prior
      (fun revealed => (observe codec dec H I leaves (fun index => columns index.val)
        after revealed).2.map Prod.fst) nonces) :
    (after (fun index => nonces index.val)).run
        (Tree.installAll codec dec H nonces columns leaves) =
      observe codec dec H I leaves (fun index => columns index.val) after
        (fun index => nonces index.val) := by
  apply RandomOracle.Tree.run_congr_on_trace
  intro entry member
  rw [install_agree codec dec H I nonces columns leaves entry.1 ?_]
  · exact (RandomOracle.Tree.trace_sound _ _ entry member).symm
  · intro index hidden equal
    apply miss
    apply StrandGhostMerkle.Nonce.hit_of_later (candidate codec dec) I prior _ nonces index hidden entry.1
    · exact List.mem_map.mpr ⟨entry,member,rfl⟩
    · rw [equal,candidate_leaf]

theorem filterRatio_changeDecider {X : Type} [Fintype X]
    {event : X → Prop} {first : DecidablePred event} [second : DecidablePred event]
    {denominator bound : ℚ}
    (law : ((@Finset.filter X event first Finset.univ).card : ℚ) / denominator ≤ bound) :
    ((Finset.univ.filter event).card : ℚ) / denominator ≤ bound := by
  cases Subsingleton.elim first second
  exact law

/-- Fixed-oracle, fixed-ghost-tree hiding against the actual adaptive later
observer. No averaging over hash answers or conditioning on misses occurs.
This bound can subsequently be averaged over those independent coins. -/
theorem observer_disagreement_ratio_le [Fintype Salt] [Nonempty Salt]
    (H : Raw → Digest) (I : Finset (Fin n))
    (columns : Fin n → Message) (leaves : Fin n → Digest)
    (after : (I → Salt) → RandomOracle.Tree Raw Digest Result fuel) (prior : List Raw) :
    ((Finset.univ.filter fun nonces : Fin n → Salt =>
      (after (fun index => nonces index.val)).run
          (Tree.installAll codec dec H nonces columns leaves) ≠
        observe codec dec H I leaves (fun index => columns index.val) after
          (fun index => nonces index.val)).card : ℚ) /
        (Fintype.card Salt : ℚ) ^ n ≤
      (prior.length + fuel : ℕ) / (Fintype.card Salt : ℚ) := by
  let later := fun revealed =>
    (observe codec dec H I leaves (fun index => columns index.val) after revealed).2.map Prod.fst
  have bounded : ∀ revealed, (later revealed).length ≤ fuel := by
    intro revealed
    simpa only [later,List.length_map] using
      (observe_length codec dec H I leaves (fun index => columns index.val) after revealed)
  have law := StrandGhostMerkle.Nonce.event_ratio_le (candidate codec dec) I prior later
    (fun nonces => (after (fun index => nonces index.val)).run
        (Tree.installAll codec dec H nonces columns leaves) ≠
      observe codec dec H I leaves (fun index => columns index.val) after
        (fun index => nonces index.val))
    (fun nonces miss => not_not.mpr
      (observer_eq_of_no_hit codec dec H I nonces columns leaves after prior miss))
    fuel bounded
  exact filterRatio_changeDecider (by simpa only [Fintype.card_fin] using law)

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Observer
