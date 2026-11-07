import LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability
import LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose

/-! An adaptive external prefix followed by a causal honest computation.
Internal round ranks rule out self-hits. Only external earlier queries are
charged, and later oracle access is included in the arbitrary observer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior
open Merkle.RandomOracle LigeroFamily
open scoped Classical
set_option maxHeartbeats 800000
variable {Mask Query Answer Request Pending View : Type} {priorFuel nextFuel : ℕ}
variable [Fintype Mask] [Fintype Query] [Fintype Answer] [DecidableEq View]
variable (before : Tree Query Answer Request priorFuel)
variable (next : Mask → Request → Tree Query Answer Pending nextFuel)
variable (input : Mask → Request → Pending → Query)
variable (active : Mask → Request → Pending → Prop)

def keys (H : Query → Answer) : Finset Query := ((before.run H).2.map Prod.fst).toFinset

omit [Fintype Mask] [Fintype Query] [Fintype Answer] [DecidableEq View] in
theorem keys_card (H : Query → Answer) : (keys before H).card ≤ priorFuel := by
  have length : (before.run H).2.length ≤ priorFuel := by
    induction before with
    | done out => exact Nat.zero_le _
    | query query continuation ih =>
      simpa only [Tree.run_query,List.length_cons] using Nat.succ_le_succ (ih (H query))
  exact (List.toFinset_card_le _).trans (by simpa only [List.length_map] using length)

def program (mask : Mask) := OracleRefreshCompose.append before (next mask)

def target (mask : Mask) (out : Request × Pending) := input mask out.1 out.2

def enabled (mask : Mask) (out : Request × Pending) := active mask out.1 out.2

omit [Fintype Mask] [Fintype Query] [Fintype Answer] [DecidableEq View] in
theorem bad_prior (mask : Mask) (H : Query → Answer)
    (localFresh : MerklePrequery.fresh (next mask (before.run H).1) (input mask (before.run H).1) H)
    (bad : ¬MerklePrequery.fresh (program before next mask) (target input mask) H) :
    input mask (before.run H).1 ((next mask (before.run H).1).run H).1 ∈ keys before H := by
  have earlier := (OracleRefreshCompose.fresh_iff_prior before (next mask) (input mask) H localFresh).not.mp bad
  push Not at earlier
  obtain ⟨qa,member,same⟩ := earlier
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨qa,member,same⟩)

variable (observe : Mask → ((Request × Pending) × List (Query × Answer)) → Option Answer → (Query → Answer) → View)

def hitEvent (H : Query → Answer) (mask : Mask) : Prop :=
  active mask (before.run H).1 ((next mask (before.run H).1).run H).1 ∧
    input mask (before.run H).1 ((next mask (before.run H).1).run H).1 ∈ keys before H

/-- Local freshness is a deterministic causal-program fact. The remaining
probability counts only hits on the external prefix, at a fixed base table. -/
theorem statClose_of_probability {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (localFresh : ∀ mask H, MerklePrequery.fresh (next mask (before.run H).1) (input mask (before.run H).1) H)
    (hit : ∀ H : Query → Answer,
      probOf id (hitEvent before next input active H) ≤ epsilon) :
    StatClose epsilon
      (OracleRefreshProbability.programmed (program before next) (target input) (enabled active) observe)
      (OracleRefreshProbability.honest (program before next) (target input) (enabled active) observe) := by
  apply OracleRefreshProbability.statClose_of_probability (program before next) (target input) (enabled active) observe nonnegative
  intro full
  have contained : ∀ mask,
      OracleRefreshProbability.hitEvent (program before next) (target input) (enabled active) full mask →
        hitEvent before next input active full mask := by
    intro mask member
    obtain ⟨enabled,bad⟩ := member
    refine ⟨?_,bad_prior before next input mask full (localFresh mask full) bad⟩
    simpa only [program,OracleRefreshCompose.append_run,OracleRefreshPrior.enabled] using enabled
  exact (OracleRefreshProbability.probability_mono _ _ contained).trans (hit full)

/-- Concrete counting bounds enter through one generic probability bridge;
subsequent causal composition uses event inclusion alone. -/
theorem statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (localFresh : ∀ mask H, MerklePrequery.fresh (next mask (before.run H).1) (input mask (before.run H).1) H)
    (hit : ∀ H : Query → Answer,
      ((Finset.univ.filter fun mask =>
        active mask (before.run H).1 ((next mask (before.run H).1).run H).1 ∧
        input mask (before.run H).1 ((next mask (before.run H).1).run H).1 ∈ keys before H).card : ℚ) /
          Fintype.card Mask ≤ epsilon) :
    StatClose epsilon
      (OracleRefreshProbability.programmed (program before next) (target input) (enabled active) observe)
      (OracleRefreshProbability.honest (program before next) (target input) (enabled active) observe) := by
  apply statClose_of_probability before next input active observe nonnegative localFresh
  intro H
  simpa only [probOf,id_eq,hitEvent] using hit H

end LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior
