import TranscriptV2.DigestCollision

namespace TranscriptV2.Tests.DigestCollision
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

private def repeated : Tree (Fin 2) Bool Unit 3 :=
  .query 0 fun _ => .query 0 fun _ => .query 1 fun _ => .done ()

-- Repeating a query does not increase the two-distinct-query birthday bound.
example : ((univ.filter (DigestCollision.Collision id repeated)).card : ℚ) /
    (Fintype.card Bool : ℚ)^Fintype.card (Fin 2) ≤ 1/2 := by
  have bound := DigestCollision.ratio_le (S := 2) repeated (by
    intro H
    simp [seen,queried,repeated])
  simpa using bound

private def grouped : Tree (Fin 2) (Bool × Bool) Unit 2 :=
  .query 0 fun _ => .query 1 fun _ => .done ()

-- Equal digests count as a collision even when the exposed challenges differ.
example : DigestCollision.Collision Prod.fst grouped (fun p => (false,p = 0)) := by
  refine ⟨0,?_,1,?_,by decide,rfl⟩ <;> simp [seen,queried,grouped]

private def interleaved : Tree (Fin 4) Bool Unit 4 :=
  .query 2 fun branch =>
    .query (if branch then 0 else 1) fun _ =>
      .query 3 fun _ => .query (if branch then 1 else 0) fun _ => .done ()

-- Outside answers can select the order of the counted calls. They remain
-- part of the same oracle, but do not enlarge the selected domain's budget.
example (eligible : Fin 4 → Prop) (size : (univ.filter eligible).card ≤ 2) :
    ((univ.filter (DigestCollision.CollisionWithin eligible id interleaved)).card : ℚ) /
    (Fintype.card Bool : ℚ)^Fintype.card (Fin 4) ≤ 1/2 := by
  have bound := DigestCollision.within_ratio_le (S := 2) eligible interleaved (by
    intro H
    exact (card_le_card (filter_subset_filter eligible (subset_univ (seen interleaved H)))).trans size)
  simpa using bound

-- An input outside the selected domain cannot form its second collision
-- endpoint, even when every answer happens to be identical.
example : ¬DigestCollision.CollisionWithin (fun p => p = 0) id repeated (fun _ => false) := by
  classical
  simp only [DigestCollision.CollisionWithin,mem_filter]
  rintro ⟨p,⟨_,hp⟩,q,⟨_,hq⟩,distinct,_⟩
  exact distinct (hp.trans hq.symm)

/--
info: 'TranscriptV2.DigestCollision.first_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms DigestCollision.first_ratio_le

/--
info: 'TranscriptV2.DigestCollision.within_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms DigestCollision.within_ratio_le

end TranscriptV2.Tests.DigestCollision
