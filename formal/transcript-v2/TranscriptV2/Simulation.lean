import TranscriptV2.SharedFailure
import Bcs.FiniteProbability
import Merkle.TreeCompose
import Mathlib.Tactic.Linarith

/-! Simulation composes at boundaries carrying the remaining state, not only
the last public message. In particular fingerprint responses may constrain
later pads. A change of coins preserves their joint boundary state.

The transcript programming contract additionally retains the returned oracle,
the observer state and earlier answers. It has its own explicit bad event;
soundness query accounting does not imply programmability. Concrete strand
programming must construct this coupling and bound its actual conflicts.
-/
noncomputable section
namespace TranscriptV2.Simulation
open Finset Bcs.FiniteProbability
open scoped Classical

private theorem density_or_le {R : Type} [Fintype R] (first second : R → Prop) :
    density (fun r => first r ∨ second r) ≤ density first + density second := by
  have bound := density_union_le (fun r => first r ∨ second r)
    (fun flag : Bool => if flag then first else second) (by
      intro r active
      rcases active with active | active
      · exact ⟨true,active⟩
      · exact ⟨false,active⟩)
  simpa only [Fintype.sum_bool,Bool.true_eq,if_true,Bool.false_eq_true,if_false] using bound

/-- The output includes everything used by subsequent stages. Equality of
message marginals alone cannot construct this interface. The coin equivalence
may depend on the witness; the public simulator supplied to a final theorem
must be a single function without a witness argument. -/
structure BoundaryCoupling {R S State : Type} (real : R → State) (simulated : S → State) where
  coins : R ≃ S
  bad : R → Prop
  agrees : ∀ r, ¬bad r → real r = simulated (coins r)

namespace BoundaryCoupling
variable {R S U State View : Type} {real : R → State} {simulated : S → State}

def ofEquiv (coins : R ≃ S) (same : ∀ r, real r = simulated (coins r)) :
    BoundaryCoupling real simulated where
  coins := coins
  bad _ := False
  agrees r _ := same r

/-- Later computation may use the state actually preserved here. If that
state omits the oracle, this lemma does not license further oracle queries;
their full run must first be included in the coupled observer view. -/
def map (coupling : BoundaryCoupling real simulated) (observe : State → View) :
    BoundaryCoupling (fun r => observe (real r)) (fun s => observe (simulated s)) where
  coins := coupling.coins
  bad := coupling.bad
  agrees r good := congrArg observe (coupling.agrees r good)

def trans {last : U → State} (first : BoundaryCoupling real simulated)
    (second : BoundaryCoupling simulated last) : BoundaryCoupling real last where
  coins := first.coins.trans second.coins
  bad r := first.bad r ∨ second.bad (first.coins r)
  agrees r good := (first.agrees r (fun h => good (Or.inl h))).trans
    (second.agrees _ (fun h => good (Or.inr h)))

theorem trans_bad_le [Fintype R] [Fintype S]
    {last : U → State} (first : BoundaryCoupling real simulated) (second : BoundaryCoupling simulated last) :
    density (first.trans second).bad ≤ density first.bad + density second.bad := by
  exact (density_or_le first.bad (fun r => second.bad (first.coins r))).trans_eq
    (congrArg (fun x => density first.bad+x) (density_equiv first.coins second.bad))

private theorem event_le [Fintype R] [Nonempty R]
    (first second bad : R → Prop) (same : ∀ r, ¬bad r → (first r ↔ second r)) :
    density first ≤ density second + density bad := by
  apply SharedFailure.failure_ratio_le first bad (fun r => if second r then 1 else 0)
  · intro r; split_ifs <;> norm_num
  · intro r active good
    simp only [if_pos ((same r good).mp active),le_refl]
  · simp only [sum_boole,density]
    have nonzero : (Fintype.card R : ℚ) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ nonzero]
  · exact le_rfl

/-- A coupling of the full boundary bounds every test on every continuation.
No restriction is placed on the observer's computation in this finite model. -/
theorem advantage_le [Fintype R] [Nonempty R] [Fintype S]
    (coupling : BoundaryCoupling real simulated) (observe : State → View) (event : View → Prop) :
    |density (fun r => event (observe (real r))) -
      density (fun s => event (observe (simulated s)))| ≤ density coupling.bad := by
  rw [← density_equiv coupling.coins (fun s => event (observe (simulated s)))]
  have same r (good : ¬coupling.bad r) :
      event (observe (real r)) ↔ event (observe (simulated (coupling.coins r))) := by
    rw [coupling.agrees r good]
  have forward := event_le _ _ coupling.bad same
  have backward := event_le _ _ coupling.bad (fun r good => (same r good).symm)
  apply abs_le.mpr
  constructor <;> linarith

section Sequential
variable {R' S' Next : Type}
variable (first : BoundaryCoupling real simulated)
variable (realNext : State → R' → Next) (simulatedNext : State → S' → Next)
variable (next : ∀ state, BoundaryCoupling (realNext state) (simulatedNext state))

/-- The second coin change is chosen in the fiber of the preserved first
state. Indexing its inverse by the simulated first state makes the global
map a genuine bijection even on the first component's bad branches. -/
def bind : BoundaryCoupling
    (fun r : R × R' => realNext (real r.1) r.2)
    (fun s : S × S' => simulatedNext (simulated s.1) s.2) where
  coins := (Equiv.prodCongr first.coins (Equiv.refl R')).trans
    (Equiv.prodCongrRight fun s => (next (simulated s)).coins)
  bad r := first.bad r.1 ∨ (next (simulated (first.coins r.1))).bad r.2
  agrees r good := by
    change realNext (real r.1) r.2 =
      simulatedNext (simulated (first.coins r.1)) ((next (simulated (first.coins r.1))).coins r.2)
    rw [first.agrees r.1 (fun h => good (Or.inl h))]
    exact (next _).agrees r.2 (fun h => good (Or.inr h))

theorem bind_bad_le [Fintype R] [Nonempty R] [Fintype R'] [Nonempty R']
    (firstError nextError : ℚ) (firstBound : density first.bad ≤ firstError)
    (nextBound : ∀ state, density (next state).bad ≤ nextError) :
    density (first.bind realNext simulatedNext next).bad ≤ firstError+nextError := by
  apply (density_or_le (fun r : R × R' => first.bad r.1)
    (fun r => (next (simulated (first.coins r.1))).bad r.2)).trans
  apply add_le_add
  · simpa only [density_product_gate] using firstBound
  · rw [density_product_average (fun (r : R) (later : R') =>
      (next (simulated (first.coins r))).bad later)]
    have total := sum_le_sum (fun r (_ : r ∈ (univ : Finset R)) =>
      nextBound (simulated (first.coins r)))
    have positive : (0 : ℚ) < Fintype.card R := by positivity
    apply (div_le_iff₀ positive).mpr
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_comm] using total

end Sequential
end BoundaryCoupling

/-- A programming boundary retains the actual proof, oracle and observation
prefix. The context includes the public request and any retained observer
state. Later observer queries are computations of this complete state. -/
structure OracleBoundary (Query Answer Proof Context : Type) where
  proof : Proof
  oracle : Query → Answer
  prior : List (Query × Answer)
  context : Context

/-- The observer receives queried coordinates, never the complete oracle as
public advice. Its later queries use the actual returned oracle. -/
structure ObserverView (Query Answer Proof Context Output : Type) where
  proof : Proof
  context : Context
  prior : List (Query × Answer)
  output : Output
  later : List (Query × Answer)

namespace OracleBoundary
variable {Query Answer Proof Context : Type}

def observe {Output : Type} {fuel : ℕ}
    (after : Context → Proof → Merkle.RandomOracle.Tree Query Answer Output fuel)
    (state : OracleBoundary Query Answer Proof Context) : ObserverView Query Answer Proof Context Output :=
  let later := (after state.context state.proof).run state.oracle
  ⟨state.proof,state.context,state.prior,later.1,later.2⟩

/-- Prior answers and proof-implied hashes must both remain valid. The final
seal predicate is the concrete verifier check on the complete canonical body,
not a caller-selected replacement message. -/
def Valid (implied : Proof → List (Query × Answer))
    (finalSeal : Proof → (Query → Answer) → Prop) (state : OracleBoundary Query Answer Proof Context) : Prop :=
  (∀ qa ∈ state.prior, state.oracle qa.1 = qa.2) ∧
    (∀ qa ∈ implied state.proof, state.oracle qa.1 = qa.2) ∧ finalSeal state.proof state.oracle

end OracleBoundary

/-- Soundness realizations do not supply this contract. Programming needs
its own coupling of proof, returned oracle and complete retained view, with
conflicts at the actually programmed inputs included in its bad event. -/
structure ProgrammingRealization {R S Query Answer Proof Context Output : Type} {fuel : ℕ}
    (real : R → OracleBoundary Query Answer Proof Context)
    (simulated : S → OracleBoundary Query Answer Proof Context)
    (after : Context → Proof → Merkle.RandomOracle.Tree Query Answer Output fuel)
    (implied : Proof → List (Query × Answer)) (finalSeal : Proof → (Query → Answer) → Prop) where
  coupling : BoundaryCoupling (fun r => (real r).observe after) (fun s => (simulated s).observe after)
  valid : ∀ r, ¬coupling.bad r → OracleBoundary.Valid implied finalSeal (simulated (coupling.coins r))

/-- An existing coupling of complete oracle states is sufficient, but is
stronger than required. Bounded-observer proofs may couple only executed views
and separately prove consistency on prior and proof-implied coordinates. -/
def ProgrammingRealization.ofBoundary {R S Query Answer Proof Context Output : Type} {fuel : ℕ}
    {real : R → OracleBoundary Query Answer Proof Context}
    {simulated : S → OracleBoundary Query Answer Proof Context}
    (coupling : BoundaryCoupling real simulated)
    (after : Context → Proof → Merkle.RandomOracle.Tree Query Answer Output fuel)
    (implied : Proof → List (Query × Answer)) (finalSeal : Proof → (Query → Answer) → Prop)
    (valid : ∀ r, OracleBoundary.Valid implied finalSeal (real r)) :
    ProgrammingRealization real simulated after implied finalSeal where
  coupling := coupling.map (OracleBoundary.observe after)
  valid r good := by
    change OracleBoundary.Valid implied finalSeal (simulated (coupling.coins r))
    rw [← coupling.agrees r good]
    exact valid r

/-- Every bounded observer test is controlled by the programming conflict
event. Its query bounds enter the concrete proof of this event's probability,
not an assumption that the observer sees an independent replacement oracle. -/
theorem ProgrammingRealization.advantage_le
    {R S Query Answer Proof Context Output : Type} [Fintype R] [Nonempty R] [Fintype S] {fuel : ℕ}
    {real : R → OracleBoundary Query Answer Proof Context}
    {simulated : S → OracleBoundary Query Answer Proof Context}
    {after : Context → Proof → Merkle.RandomOracle.Tree Query Answer Output fuel}
    {implied : Proof → List (Query × Answer)} {finalSeal : Proof → (Query → Answer) → Prop}
    (realization : ProgrammingRealization real simulated after implied finalSeal)
    (event : ObserverView Query Answer Proof Context Output → Prop) :
    |density (fun r => event ((real r).observe after)) -
      density (fun s => event ((simulated s).observe after))| ≤ density realization.coupling.bad :=
  realization.coupling.advantage_le id event

end TranscriptV2.Simulation
