import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSchedule
import LfzkV2.Current.ZeroKnowledge.StrandLeafOracle
import Bcs.StatisticalDistance

/-! Statistical hiding of a real indexed commitment versus the leaf-only
public-view experiment. All earlier/later raw observer queries count once.
The coupling changes only leaf answers; internal hashes, transcript nodes,
PRF streams and the final seal remain ordinary evaluations of the oracle.
The public frontend/backend coin changes are composed separately. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
open Merkle Merkle.Indexed Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Raw Context Result : Type} {n preFuel postFuel : ℕ}
local instance : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)

private theorem close_of_disagreement {X View : Type} [Fintype X] [DecidableEq View]
    (first second : X → View) (epsilon : ℚ)
    (bounded : ((Finset.univ.filter fun x => first x ≠ second x).card : ℚ) /
      Fintype.card X ≤ epsilon) : StatClose epsilon first second := by
  have coupling : ZkClose (Finset.univ.filter fun x => first x ≠ second x).card first second := by
    refine ⟨Equiv.refl X,?_⟩
    simp only [SumcheckV1.event_card,Equiv.refl_apply]
    apply Finset.card_le_card
    intro x member
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at member ⊢
    exact Ne.symm member
  exact (zkClose_statClose coupling).mono bounded

variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)
variable (before : RandomOracle.Tree Raw Digest Context preFuel)
variable (columns : Context → Fin n → Message)
variable (prepare : Context → (Observer.Other codec dec → Digest) → Digest →
  Schedule.Prepared n Salt Message Digest Raw Result postFuel)
variable [Inhabited Digest]
variable (abort : Context → RandomOracle.Tree Raw Digest Result postFuel)
variable (separated : ∀ index children salt message,
  codec.nodeEnc index children ≠ codec.leafEnc (salt,message))

include separated in
theorem fixed_oracle_close [Fintype Salt] [Nonempty Salt]
    (H : Raw → Digest) (leaves : Fin n → Digest) :
    StatClose ((preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ))
      (fun nonces : Fin n → Salt => Schedule.honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns H nonces leaves) nonces)
      (fun nonces : Fin n → Salt => Schedule.simulate codec dec before columns prepare abort H leaves
        (fun index => nonces index.val)) := by
  let I := (Schedule.prepared codec dec before prepare H leaves).opened
  let later := Schedule.trace codec dec before columns prepare H leaves
  have bounded : ∀ revealed, (later revealed).length ≤ postFuel := by
    intro revealed
    simpa only [later,Schedule.trace,List.length_map] using
      Observer.observe_length codec dec H I leaves
        (fun index => columns (before.run H).1 index.val)
        (Schedule.after codec dec before columns prepare H leaves) revealed
  have law := Nonce.event_ratio_le (Observer.candidate codec dec) I
    ((before.run H).2.map Prod.fst) later
    (fun nonces : Fin n → Salt => Schedule.honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns H nonces leaves) nonces ≠
      Schedule.simulate codec dec before columns prepare abort H leaves (fun index => nonces index.val))
    (fun nonces miss => not_not.mpr
      (Schedule.honest_coupled_eq_simulate codec dec before columns prepare separated abort H nonces leaves miss))
    postFuel bounded
  have priorBound := Observer.trace_length before H
  have small : (((before.run H).2.map Prod.fst).length + postFuel : ℕ) /
      (Fintype.card Salt : ℚ) ≤ (preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    simp only [List.length_map]
    exact_mod_cast Nat.add_le_add_right priorBound postFuel
  apply close_of_disagreement
  calc
    _ ≤ (((before.run H).2.map Prod.fst).length + postFuel : ℕ) /
        (Fintype.card Salt : ℚ) :=
      Observer.filterRatio_changeDecider (by
        simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using law)
    _ ≤ _ := small

/-- Nonces are not changed by the oracle permutation. The request-dependent
leaf coordinates may use every earlier oracle answer and all fixed private
prover coins; none is selected using the fresh leaf answer being swapped. -/
def coinEquiv : Coins n Salt Raw Digest ≃ Coins n Salt Raw Digest :=
  Equiv.prodCongrRight fun nonces : Fin n → Salt =>
    Swap.equiv before (fun context => Tree.addresses codec dec nonces (columns context))

/-- The real side ignores the independent ghost-leaf coins. They are
auxiliary sampling coins used by the proof, never a serialized message. -/
def real (coin : Coins n Salt Raw Digest) :=
  Schedule.honest codec dec before columns prepare coin.2.1 coin.1

def ideal (coin : Coins n Salt Raw Digest) :=
  Schedule.simulate codec dec before columns prepare abort coin.2.1 coin.2.2
    (fun index => coin.1 index.val)

include separated in
/-- This finite-oracle theorem already includes an adaptive prior request,
a response-selected opening set, and the actual later observer trace. It
requires only the literal leaf/node role separation, not collision-free hash
outputs. The concrete byte-oracle endpoint is its finite marginal transport. -/
theorem statistical_hiding [Fintype Salt] [Nonempty Salt] [Fintype Raw] [Fintype Digest] :
    StatClose ((preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ))
      (real codec dec before columns prepare) (ideal codec dec before columns prepare abort) := by
  have nonnegative : (0 : ℚ) ≤ (preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have mixed := statClose_mix nonnegative
    (fun outer : (Raw → Digest) × (Fin n → Digest) => fun nonces : Fin n → Salt =>
      Schedule.honest codec dec before columns prepare
        (History.coupledOracle codec dec before columns outer.1 nonces outer.2) nonces)
    (fun outer : (Raw → Digest) × (Fin n → Digest) =>
      fun nonces : Fin n → Salt => Schedule.simulate codec dec before columns prepare abort outer.1 outer.2
        (fun index => nonces index.val))
    (fun outer => fixed_oracle_close codec dec before columns prepare abort separated outer.1 outer.2)
  let order := Equiv.prodComm (Fin n → Salt) ((Raw → Digest) × (Fin n → Digest))
  have shifted : StatClose ((preFuel + postFuel : ℕ) / (Fintype.card Salt : ℚ))
      (fun coin => real codec dec before columns prepare (coinEquiv codec dec before columns coin))
      (ideal codec dec before columns prepare abort) :=
    statClose_reindex order order (fun _ => rfl) (fun _ => rfl) mixed
  apply statClose_reindex (coinEquiv codec dec before columns).symm
    (Equiv.refl (Coins n Salt Raw Digest)) _ (fun _ => rfl) shifted
  intro coin
  rw [Equiv.apply_symm_apply]

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
