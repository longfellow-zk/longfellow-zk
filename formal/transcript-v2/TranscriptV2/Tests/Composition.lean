import TranscriptV2.CompositionTransport

namespace TranscriptV2.Tests.Composition
open TranscriptV2.Composition Merkle.RandomOracle Bcs.TotalOracle Finset
open scoped Classical

-- A charge on one role must not spend the allowance at an auxiliary role.
private def localProof : LocalCharges Bool Bool Unit Empty Unit where
  parent p := nomatch p
  child p _ := nomatch p
  distinct p := nomatch p
  single point _ answer := if point = false ∧ answer.1 = true then 1 else 0
  pair p := nomatch p
  single_nonneg _ _ _ := by split_ifs <;> norm_num
  pair_nonneg p := nomatch p
  single_off _ _ _ _ _ := rfl
  pair_off p := nomatch p
  singleBudget point := if point then 0 else 1/2
  pairBudget p := nomatch p
  single_mean point _ := by
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_unique]
    cases point <;> norm_num
  pair_mean p := nomatch p

private def twoRoles : Tree Bool (Bool × Unit) Unit 2 :=
  .query false fun _ => .query true fun _ => .done ()

-- The original execution already reached the named context, so later
-- verifier work cannot enlarge its extraction cut.
example (H : Bool → Bool × Unit) :
    beforeLabel id true (twoRoles.bind fun _ => (.query false fun _ => .done () : Tree Bool (Bool × Unit) Unit 1)) H =
      beforeLabel id true twoRoles H := by
  apply beforeLabel_bind_of_queried
  exact ⟨true,by simp [twoRoles,seen,queried],rfl⟩

example : (∑ H : Bool → Bool × Unit, localProof.charge twoRoles H) ≤ 2 := by
  have bound := localProof.charge_mean twoRoles (fun p => if p then 0 else 1/2)
    (by intro p; simp [LocalCharges.budget,localProof])
  norm_num [twoRoles,seen,queried,Fintype.card_fun] at bound ⊢
  exact bound

end TranscriptV2.Tests.Composition

#guard_msgs (drop info) in #check TranscriptV2.DigestProjection.charge_congr

/--
info: 'TranscriptV2.DigestProjection.charge_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.DigestProjection.charge_congr

#guard_msgs (drop info) in #check TranscriptV2.DigestProjection.charge_mapQueries

/--
info: 'TranscriptV2.DigestProjection.charge_mapQueries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.DigestProjection.charge_mapQueries
