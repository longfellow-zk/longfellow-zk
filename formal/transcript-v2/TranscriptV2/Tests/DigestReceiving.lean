import TranscriptV2.DigestProjection

namespace TranscriptV2.Tests.DigestReceiving
open Finset Merkle.RandomOracle Bcs.TotalOracle
open scoped Classical

-- The first query plants a target. Its challenge decides whether a second,
-- auxiliary query is made. The auxiliary count must remain inside the mean.
private def adaptive : Tree Bool (Bool × Bool) Unit 2 :=
  .query false fun answer => if answer.2 then
    .query true fun _ => .done () else (Tree.done () : Tree Bool (Bool × Bool) Unit 0).weaken

private def targets (point : Bool) : Finset Bool := if point then ∅ else {false}

example :
    (∑ H : Bool → Bool × Bool,
      DigestProjection.receivingCharge (fun p => p = true) targets adaptive H) ≤
      ∑ H : Bool → Bool × Bool, ∑ p ∈ seen adaptive H, if p = true then (1 : ℚ) else 0 := by
  have bound := DigestProjection.receiving_sum_le (Q := 2) (arity := 1)
    (fun p : Bool => p = true) (fun p => p = true) (fun _ h => h) targets adaptive
    (fun H => (card_le_card (subset_univ (seen adaptive H))).trans (by decide))
    (fun p => by cases p <;> simp [targets])
  simpa using bound

-- A target hit at an ordinary address receives no Merkle charge, even
-- if its digest happens to hit a target.
example (H : Bool → Bool × Bool) (noAuxiliary : (H false).2 = false) :
    DigestProjection.receivingCharge (fun p => p = true) targets adaptive H = 0 := by
  simp [DigestProjection.receivingCharge,adaptive,seen,queried,noAuxiliary,Tree.run_weaken]

-- Self-reference is included: the receiving input already names its
-- target before seeing its own answer.
example : DigestProjection.receivingCharge (fun _ : Bool => True) (fun _ => {false})
    (.query false fun _ => .done () : Tree Bool (Bool × Bool) Unit 1)
    (fun _ => (false,false)) = 1 := by
  simp [DigestProjection.receivingCharge,DigestProjection.bad,DigestCharging.targets,seen,queried,before]

/--
info: 'TranscriptV2.DigestProjection.receiving_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms DigestProjection.receiving_sum_le

end TranscriptV2.Tests.DigestReceiving
