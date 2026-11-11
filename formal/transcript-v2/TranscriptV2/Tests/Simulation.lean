import TranscriptV2.Simulation

namespace TranscriptV2.Tests.Simulation
open TranscriptV2.Simulation Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

private def xorEquiv (bit : Bool) : Bool ≃ Bool where
  toFun := Bool.xor bit
  invFun := Bool.xor bit
  left_inv coin := by cases bit <;> cases coin <;> rfl
  right_inv coin := by cases bit <;> cases coin <;> rfl

private def first : BoundaryCoupling (Bool.xor true) id :=
  .ofEquiv (xorEquiv true) (fun _ => rfl)

private def next (state : Bool) : BoundaryCoupling (Bool.xor state) id :=
  .ofEquiv (xorEquiv state) (fun _ => rfl)

private def joint := first.bind Bool.xor (fun _ => id) next

-- The later coin change depends on the preserved first state. Treating the
-- two stages as independent message distributions would lose this relation.
example : joint.coins (false,false) = (true,true) := rfl
example : joint.coins (true,false) = (false,false) := rfl

example (event : Bool → Prop) :
    |density (fun r : Bool × Bool => event (Bool.xor (Bool.xor true r.1) r.2)) -
      density (fun s : Bool × Bool => event s.2)| ≤ 0 := by
  simpa [joint,BoundaryCoupling.bind,first,next,BoundaryCoupling.ofEquiv,density] using
    joint.advantage_le id event

private def real (_ : Unit) : OracleBoundary Bool Bool Bool Unit :=
  ⟨false,id,[(false,false)],()⟩

private def simulated (_ : Unit) : OracleBoundary Bool Bool Bool Unit :=
  ⟨false,fun _ => false,[(false,false)],()⟩

private def after (_ : Unit) (_ : Bool) : Tree Bool Bool Bool 1 :=
  .query false fun answer => .done answer

private def implied (proof : Bool) := [(false,proof)]
private def finalSeal (proof : Bool) (H : Bool → Bool) := H false = proof

private def programmed : ProgrammingRealization real simulated after implied finalSeal where
  coupling := BoundaryCoupling.ofEquiv (Equiv.refl Unit) (fun _ => rfl)
  valid _ _ := by simp [OracleBoundary.Valid,simulated,implied,finalSeal]

-- Full observed answers and proof equations agree even though an unqueried
-- coordinate differs. The interface must not expose the entire oracle table.
example : (real ()).oracle true ≠ (simulated ()).oracle true := by decide

example (event : ObserverView Bool Bool Bool Unit Bool → Prop) :
    |density (fun r => event ((real r).observe after)) -
      density (fun s => event ((simulated s).observe after))| ≤ 0 := by
  simpa [programmed,BoundaryCoupling.ofEquiv,density] using programmed.advantage_le event

/--
info: 'TranscriptV2.Simulation.BoundaryCoupling.advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms BoundaryCoupling.advantage_le

/--
info: 'TranscriptV2.Simulation.BoundaryCoupling.bind_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms BoundaryCoupling.bind_bad_le

end TranscriptV2.Tests.Simulation
