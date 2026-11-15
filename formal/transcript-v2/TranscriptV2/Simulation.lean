import TranscriptV2.SharedFailure
import Bcs.FiniteProbability
import Merkle.TreeCompose
import Mathlib.Tactic.Linarith

/-! A simulation boundary carries the remaining state, not only the last
public message. In particular fingerprint responses may constrain later
pads. A change of coins preserves the boundary state.

The transcript programming contract additionally retains the returned oracle,
the observer state and earlier answers. It has its own explicit bad event;
soundness query accounting does not imply programmability. Concrete strand
programming must construct this coupling and bound its actual conflicts.
-/
noncomputable section
namespace TranscriptV2.Simulation
open Finset Bcs.FiniteProbability
open scoped Classical

/-- The output includes everything used by subsequent stages. Equality of
message marginals alone cannot construct this interface. The coin equivalence
may depend on the witness; the public simulator supplied to a final theorem
must be a single function without a witness argument. -/
structure BoundaryCoupling {R S State : Type} (real : R → State) (simulated : S → State) where
  coins : R ≃ S
  bad : R → Prop
  agrees : ∀ r, ¬bad r → real r = simulated (coins r)

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

end TranscriptV2.Simulation
