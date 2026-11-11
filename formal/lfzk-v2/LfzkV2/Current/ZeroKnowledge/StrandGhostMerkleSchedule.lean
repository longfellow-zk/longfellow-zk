import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleHistory

/-! The public stage selects openings using a root and non-leaf oracle.
Completion then receives only the disclosed columns and authentication.
This is the dependency boundary needed for a response-selected opening:
its index set may depend on every frontend/backend response and ordinary
SHA answer, but not on any still-hidden leaf nonce. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Schedule
open Merkle Merkle.Indexed Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Raw Context Result : Type} {n preFuel postFuel : ℕ}
variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)

structure Prepared (n : ℕ) (Salt Message Digest Raw Result : Type) (postFuel : ℕ) where
  opened : Finset (Fin n)
  finish : (opened → Message) → Opening n opened (Fin n × Salt) Digest →
    RandomOracle.Tree Raw Digest Result postFuel

variable (before : RandomOracle.Tree Raw Digest Context preFuel)
variable (columns : Context → Fin n → Message)
variable (prepare : Context → (Observer.Other codec dec → Digest) → Digest →
  Prepared n Salt Message Digest Raw Result postFuel)
variable [Inhabited Digest]

/-- The completion tree may include an arbitrary post-proof observer. Its
result can retain the canonical complete proof, including the final seal. -/
def honest (H : Raw → Digest) (nonces : Fin n → Salt) :=
  let earlier := before.run H
  let root := commitLabels (codec.withOracle H) n (fun index => (index,nonces index)) (columns earlier.1) 1
  let stage := prepare earlier.1 (fun other => H other.val) root
  let opening := openCore (codec.withOracle H) n stage.opened
    (fun index => (index,nonces index)) (columns earlier.1)
  (earlier,(stage.finish (fun index => columns earlier.1 index.val) opening).run H)

def prepared (H : Raw → Digest) (leaves : Fin n → Digest) :=
  prepare (before.run H).1 (fun other => H other.val) (Tree.labels codec H leaves 1)

/-- All hidden nonce coordinates have disappeared from this computation's
interface. Only the disclosure at the already chosen index set is supplied. -/
def after (H : Raw → Digest) (leaves : Fin n → Digest)
    (revealed : (prepared codec dec before prepare H leaves).opened → Salt) :=
  let stage := prepared codec dec before prepare H leaves
  stage.finish (fun index => columns (before.run H).1 index.val)
    (Tree.opening codec H leaves stage.opened revealed)

def ghost (H : Raw → Digest) (leaves : Fin n → Digest) (nonces : Fin n → Salt) :=
  let I := (prepared codec dec before prepare H leaves).opened
  (before.run H,Observer.observe codec dec H I leaves
    (fun index => columns (before.run H).1 index.val)
    (after codec dec before columns prepare H leaves) (fun index => nonces index.val))

def trace (H : Raw → Digest) (leaves : Fin n → Digest)
    (revealed : (prepared codec dec before prepare H leaves).opened → Salt) : List Raw :=
  let I := (prepared codec dec before prepare H leaves).opened
  (Observer.observe codec dec H I leaves (fun index => columns (before.run H).1 index.val)
    (after codec dec before columns prepare H leaves) revealed).2.map Prod.fst

/-- Only actual disclosed preimages are checked against the prior trace.
On a conflict the public simulator must retain the previously answered table. -/
def openedFresh (H : Raw → Digest) (leaves : Fin n → Digest)
    (revealed : (prepared codec dec before prepare H leaves).opened → Salt) : Prop :=
  ∀ entry ∈ (before.run H).2,
    ∀ index : (prepared codec dec before prepare H leaves).opened,
      entry.1 ≠ codec.leafEnc ((index.val,revealed index),columns (before.run H).1 index.val)

/-- This public simulation boundary receives no hidden nonce or column.
Rejected programming retains the original oracle and propagates failure to
the original post-proof observer. Ordinary completion uses the same non-leaf
oracle; it never installs transcript answers or resets a PRF reader. -/
def complete (stage : Prepared n Salt Message Digest Raw Result postFuel)
    (prior : List (Raw × Digest)) (disclosed : stage.opened → Message)
    (abort : RandomOracle.Tree Raw Digest Result postFuel)
    (H : Raw → Digest) (leaves : Fin n → Digest) (revealed : stage.opened → Salt) :=
  if ∀ entry ∈ prior, ∀ index : stage.opened,
      entry.1 ≠ codec.leafEnc ((index.val,revealed index),disclosed index) then
    Observer.observe codec dec H stage.opened leaves disclosed
      (fun nonces => stage.finish disclosed (Tree.opening codec H leaves stage.opened nonces)) revealed
  else abort.run H

def simulate (abort : Context → RandomOracle.Tree Raw Digest Result postFuel)
    (H : Raw → Digest) (leaves : Fin n → Digest)
    (revealed : (prepared codec dec before prepare H leaves).opened → Salt) :=
  let stage := prepared codec dec before prepare H leaves
  (before.run H,complete codec dec stage (before.run H).2
    (fun index => columns (before.run H).1 index.val) (abort (before.run H).1) H leaves revealed)

theorem simulate_eq_ghost_of_no_hit
    (abort : Context → RandomOracle.Tree Raw Digest Result postFuel)
    (H : Raw → Digest) (nonces : Fin n → Salt) (leaves : Fin n → Digest)
    (miss : ¬ Nonce.Hit (Observer.candidate codec dec)
      (prepared codec dec before prepare H leaves).opened ((before.run H).2.map Prod.fst)
      (trace codec dec before columns prepare H leaves) nonces) :
    simulate codec dec before columns prepare abort H leaves (fun index => nonces index.val) =
      ghost codec dec before columns prepare H leaves nonces := by
  have unused : openedFresh codec dec before columns prepare H leaves (fun index => nonces index.val) := by
    intro entry member index same
    apply miss
    apply Nonce.hit_of_prior (Observer.candidate codec dec) _ _ _ nonces index.val entry.1
    · exact List.mem_map.mpr ⟨entry,member,rfl⟩
    · rw [same,Observer.candidate_leaf]
  dsimp only [simulate,complete]
  unfold openedFresh at unused
  rw [if_pos unused]
  rfl

variable (separated : ∀ index children salt message,
  codec.nodeEnc index children ≠ codec.leafEnc (salt,message))

include separated in
theorem honest_coupled_eq_ghost (H : Raw → Digest) (nonces : Fin n → Salt)
    (leaves : Fin n → Digest)
    (miss : ¬ Nonce.Hit (Observer.candidate codec dec)
      (prepared codec dec before prepare H leaves).opened ((before.run H).2.map Prod.fst)
      (trace codec dec before columns prepare H leaves) nonces) :
    honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns H nonces leaves) nonces =
      ghost codec dec before columns prepare H leaves nonces := by
  have installed := History.coupledOracle_eq_installAll codec dec before columns H nonces leaves _ _ miss
  have other :
      (fun raw : Observer.Other codec dec =>
        Tree.installAll codec dec H nonces (columns (before.run H).1) leaves raw.val) =
      (fun raw : Observer.Other codec dec => H raw.val) := by
    funext raw
    exact Observer.installAll_other codec dec H nonces (columns (before.run H).1) leaves raw
  unfold honest
  rw [History.prior_preserved]
  dsimp only
  rw [installed,Tree.installAll_commit codec dec separated,other,
    Tree.installAll_opening codec dec separated]
  exact congrArg (fun later => (before.run H,later))
    (Observer.observer_eq_of_no_hit codec dec H
      (prepared codec dec before prepare H leaves).opened nonces (columns (before.run H).1) leaves
      (after codec dec before columns prepare H leaves) _ miss)

include separated in
theorem honest_coupled_eq_simulate
    (abort : Context → RandomOracle.Tree Raw Digest Result postFuel)
    (H : Raw → Digest) (nonces : Fin n → Salt) (leaves : Fin n → Digest)
    (miss : ¬ Nonce.Hit (Observer.candidate codec dec)
      (prepared codec dec before prepare H leaves).opened ((before.run H).2.map Prod.fst)
      (trace codec dec before columns prepare H leaves) nonces) :
    honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns H nonces leaves) nonces =
      simulate codec dec before columns prepare abort H leaves (fun index => nonces index.val) := by
  rw [simulate_eq_ghost_of_no_hit codec dec before columns prepare abort H nonces leaves miss]
  exact honest_coupled_eq_ghost codec dec before columns prepare separated H nonces leaves miss

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Schedule
