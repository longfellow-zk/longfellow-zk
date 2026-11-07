import LfzkV2.Current.ZeroKnowledge.OracleRefreshActive
import LfzkV1.ZkMerkle

/-! Averaging an abort-aware whole-answer refresh over private masks.
The bad event is counted at each fixed base oracle, before programming.
The observer receives the resulting oracle and may make arbitrary later
queries. No independence conditional on the programmed table is used. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability
open Merkle.RandomOracle LigeroFamily
open scoped Classical
variable {Mask Query Answer Result View : Type} {fuel : ℕ}
variable [Fintype Mask] [Fintype Query] [Fintype Answer] [DecidableEq View]
variable (before : Mask → Tree Query Answer Result fuel)
variable (input : Mask → Result → Query) (active : Mask → Result → Prop)
variable (observe : Mask → (Result × List (Query × Answer)) → Option Answer → (Query → Answer) → View)

/-- Event inclusion can be used without exposing the finite enumeration or
its chosen decision procedure to the caller. This uses the existing
uniform finite probability model. -/
theorem probability_mono {Coin : Type} [Fintype Coin]
    (first second : Coin → Prop) (included : ∀ coin, first coin → second coin) :
    probOf id first ≤ probOf id second := by
  unfold probOf
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg (Fintype.card Coin))
  exact_mod_cast Finset.card_le_card (show
    Finset.univ.filter (fun coin => first (id coin)) ⊆
      Finset.univ.filter (fun coin => second (id coin)) from by
    intro coin member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,included coin (Finset.mem_filter.mp member).2⟩)

def honest (coin : Mask × ((Query → Answer) × Answer)) : View :=
  OracleRefreshActive.honest (before coin.1) (input coin.1) (active coin.1) (observe coin.1) coin.2

def programmed (coin : Mask × ((Query → Answer) × Answer)) : View :=
  OracleRefreshActive.programmed (before coin.1) (input coin.1) (active coin.1) (observe coin.1) coin.2

def guarded (coin : Mask × ((Query → Answer) × Answer)) : View :=
  OracleRefreshActive.guarded (before coin.1) (input coin.1) (active coin.1) (observe coin.1) coin.2

def exchange : (Mask × ((Query → Answer) × Answer)) ≃ (Mask × ((Query → Answer) × Answer)) :=
  Equiv.prodCongrRight fun mask => OracleRefreshActive.swapEquiv (before mask) (input mask) (active mask)

omit [Fintype Mask] [Fintype Query] [Fintype Answer] [DecidableEq View] in
theorem guarded_exchange (coin : Mask × ((Query → Answer) × Answer)) :
    guarded before input active observe coin = honest before input active observe (exchange before input active coin) :=
  OracleRefreshActive.guarded_after_swap (before coin.1) (input coin.1) (active coin.1) (observe coin.1) coin.2

/-- This event is evaluated at the fixed base oracle, before the independent
opening answer is inserted. It therefore does not condition on a programmed
oracle whose selected coordinate may depend on the private mask. -/
def hitEvent (H : Query → Answer) (mask : Mask) : Prop :=
  active mask ((before mask).run H).1 ∧
    ¬MerklePrequery.fresh (before mask) (input mask) H

/-- A bound on the actual event probability suffices for the entire
observer view, including later queries to the returned oracle. -/
theorem statClose_of_probability {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (hit : ∀ H : Query → Answer,
      probOf id (hitEvent before input active H) ≤ epsilon) :
    StatClose epsilon (programmed before input active observe) (honest before input active observe) := by
  let f := fun (oracle : (Query → Answer) × Answer) (mask : Mask) =>
    OracleRefreshActive.programmed (before mask) (input mask) (active mask) (observe mask) oracle
  let g := fun (oracle : (Query → Answer) × Answer) (mask : Mask) =>
    OracleRefreshActive.guarded (before mask) (input mask) (active mask) (observe mask) oracle
  have each : ∀ oracle, StatClose epsilon (f oracle) (g oracle) := by
    intro oracle
    let bad := Finset.univ.filter fun mask => active mask ((before mask).run oracle.1).1 ∧
      ¬MerklePrequery.fresh (before mask) (input mask) oracle.1
    have counted : CountingClose bad.card (f oracle) (g oracle) := by
      apply le_trans (Finset.card_le_card ?_) (le_refl bad.card)
      intro mask member
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ mask,
        OracleRefreshActive.disagreement_active_hit (before mask) (input mask) (active mask)
          (observe mask) oracle (Finset.mem_filter.mp member).2⟩
    have probability : ((bad.card : ℚ) / Fintype.card Mask) ≤ epsilon := by
      simpa only [probOf,id_eq,hitEvent] using hit oracle.1
    exact StatClose.mono probability (LfzkV1.ZkMerkle.statClose_of_countingClose counted)
  have mixed := statClose_mix nonnegative f g each
  intro P
  have rearranged := mixed P
  rw [← probOf_equiv (Equiv.prodComm Mask ((Query → Answer) × Answer))
      (fun coin : ((Query → Answer) × Answer) × Mask => f coin.1 coin.2) P,
    ← probOf_equiv (Equiv.prodComm Mask ((Query → Answer) × Answer))
      (fun coin : ((Query → Answer) × Answer) × Mask => g coin.1 coin.2) P] at rearranged
  change |probOf (programmed before input active observe) P - probOf (guarded before input active observe) P| ≤ epsilon at rearranged
  have same : probOf (guarded before input active observe) P = probOf (honest before input active observe) P := by
    rw [show guarded before input active observe = (fun coin => honest before input active observe (exchange before input active coin)) from
      funext (guarded_exchange before input active observe)]
    exact probOf_equiv (exchange before input active) (honest before input active observe) P
  rwa [same] at rearranged

/-- The finite counting interface is retained for concrete mask bounds.
The conversion to probability is confined to this generic boundary. -/
theorem statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (hit : ∀ H : Query → Answer,
      ((Finset.univ.filter fun mask => active mask ((before mask).run H).1 ∧
        ¬MerklePrequery.fresh (before mask) (input mask) H).card : ℚ) /
          Fintype.card Mask ≤ epsilon) :
    StatClose epsilon (programmed before input active observe) (honest before input active observe) := by
  apply statClose_of_probability before input active observe nonnegative
  intro H
  simpa only [probOf,id_eq,hitEvent] using hit H

end LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability
