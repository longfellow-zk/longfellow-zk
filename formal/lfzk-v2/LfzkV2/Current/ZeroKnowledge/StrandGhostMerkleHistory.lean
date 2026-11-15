import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleObserver

/-! Moving the actual honest commitment across the leaf-answer swap.
The public request/columns can depend on the complete earlier oracle run.
Every prior query and answer is retained, rather than replacing the earlier
observer by a fixed request or assuming an empty oracle history. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.History
open Merkle Merkle.Indexed Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Raw Context Result : Type} {n preFuel postFuel : ℕ}

variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)
variable (before : RandomOracle.Tree Raw Digest Context preFuel)
variable (columns : Context → Fin n → Message)

/-- The swap is on leaf coordinates selected using the actual prior request.
Independent nonce coins are supplied after that prior stage. -/
def coupledOracle (H : Raw → Digest) (nonces : Fin n → Salt) (leaves : Fin n → Digest) :
    Raw → Digest :=
  (Swap.swap before (fun context => Tree.addresses codec dec nonces (columns context))
    (H,leaves)).1

theorem prior_preserved (H : Raw → Digest) (nonces : Fin n → Salt) (leaves : Fin n → Digest) :
    before.run (coupledOracle codec dec before columns H nonces leaves) = before.run H :=
  Swap.before_swap _ _ _

theorem fresh_of_no_hit (H : Raw → Digest) (nonces : Fin n → Salt)
    (I : Finset (Fin n)) (later : (I → Salt) → List Raw)
    (miss : ¬ Nonce.Hit (Observer.candidate codec dec) I
      ((before.run H).2.map Prod.fst) later nonces) :
    Swap.fresh before (fun context => Tree.addresses codec dec nonces (columns context)) H := by
  intro entry member index equal
  apply miss
  apply Nonce.hit_of_prior (Observer.candidate codec dec) I _ later nonces index entry.1
  · exact List.mem_map.mpr ⟨entry,member,rfl⟩
  · change entry.1 = codec.leafEnc ((index,nonces index),columns (before.run H).1 index) at equal
    rw [equal,Observer.candidate_leaf]

theorem coupledOracle_eq_installAll (H : Raw → Digest)
    (nonces : Fin n → Salt) (leaves : Fin n → Digest)
    (I : Finset (Fin n)) (later : (I → Salt) → List Raw)
    (miss : ¬ Nonce.Hit (Observer.candidate codec dec) I
      ((before.run H).2.map Prod.fst) later nonces) :
    coupledOracle codec dec before columns H nonces leaves =
      Tree.installAll codec dec H nonces (columns (before.run H).1) leaves := by
  unfold coupledOracle Swap.swap
  rw [if_pos (fresh_of_no_hit codec dec before columns H nonces I later miss)]
  rfl

variable [Inhabited Digest]
variable (separated : ∀ index children salt message,
  codec.nodeEnc index children ≠ codec.leafEnc (salt,message))

/-- The output consists of the complete earlier view, actual Merkle root,
authentication data, and the complete later raw-query view. The later tree
may be selected from all disclosed nonces; no nonce is supplied for a hidden
column. At the protocol instantiation the public prefix selects `I` before
any nonce is disclosed. -/
def honestView (H : Raw → Digest) (nonces : Fin n → Salt) (I : Finset (Fin n))
    (after : (I → Salt) → RandomOracle.Tree Raw Digest Result postFuel) :=
  let context := (before.run H).1
  (before.run H,
    (commitLabels (codec.withOracle H) n (fun index => (index,nonces index)) (columns context) 1,
      openCore (codec.withOracle H) n I (fun index => (index,nonces index)) (columns context),
      (after (fun index => nonces index.val)).run H))

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.History
