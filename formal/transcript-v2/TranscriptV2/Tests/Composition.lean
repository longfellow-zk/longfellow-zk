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

-- The old construction supplies a realization, including zero-round proofs.
private def noRounds : Chain Bool Bool Unit Bool 0 where
  parent _ := none
  claimed _ := false
  State := Unit
  rank _ := 0
  initial _ := ()
  input _ := false
  advance _ i := Fin.elim0 i
  initial_rank _ := rfl
  advance_rank _ i := Fin.elim0 i
  advance_parent _ i := Fin.elim0 i
  advance_link _ i := Fin.elim0 i
  finalSeal := id

private def complete : Tree Bool (Bool × Unit) Bool 1 := .query false fun a => .done a.1
private def observe (out : Bool) (H : Bool → Bool × Unit) := (out,(H false).1)

private def realization := SoundnessRealization.ofChain noRounds complete observe
  (fun view => view.1 = view.2) (fun _ _ valid => valid.symm)

example (H : Bool → Bool × Unit) : realization.speculation H = 0 := rfl

example (event : Bool × Bool → Prop) :
    Bcs.FiniteProbability.density (fun H => event (observe (complete.run H).1 H)) =
      Bcs.FiniteProbability.density (fun H => event (observe (complete.run H).1 H)) :=
  realization.observation_law event

-- Renaming retains the complete observation; unused target coordinates
-- cannot alter either the verifier decision or the extracted cut.
example (event : Bool × Bool → Prop) :
    Bcs.FiniteProbability.density (fun H => event (observe (complete.run H).1 H)) =
      Bcs.FiniteProbability.density (fun H : Bool ⊕ Unit → Bool × Unit =>
        event (observe ((mapQueries Sum.inl complete).run H).1 (H ∘ Sum.inl))) :=
  (realization.rename Sum.inl Sum.inl_injective).observation_law event

example (H : Bool ⊕ Unit → Bool × Unit) :
    (realization.rename Sum.inl Sum.inl_injective).speculation H = 0 := rfl

private def speculative : Tree Bool (Bool × Unit) Unit 1 := .query true fun _ => .done ()

private def paid : SoundnessRealization (rounds := 0) speculative
    (fun _ : Bool → Bool × Unit => ()) (fun _ _ => ()) (fun _ => True) (fun _ _ _ => false) where
  observation_law _ := rfl
  exception _ := False
  speculation _ := 1
  speculation_nonneg _ := by norm_num
  accepted_path _ _ _ := Or.inr le_rfl

-- A charged speculative execution need not admit an algebraic failure
-- cover. Requiring one there would silently assume raw/typed correspondence
-- in exactly the exceptional case which the transcript proof already pays for.
example : Bcs.FiniteProbability.density (fun _ : Bool → Bool × Unit => True) ≤ 1 := by
  have bound := paid.failure_ratio_le localProof (fun _ => True) (fun _ => True) (fun p => p = true) 1 0
    (by norm_num)
    (Q := 1) (by intro H; simp [speculative,seen,queried])
    (by intro p; cases p <;> norm_num [LocalCharges.budget,localProof])
    (by simp [paid,speculative,seen,queried])
    (by simp [paid,Bcs.FiniteProbability.density])
    (by intro _ _ _ _ _ small; norm_num [paid] at small)
  simpa only [and_self,Nat.cast_one,one_mul,add_zero] using bound

/--
info: 'TranscriptV2.Composition.SoundnessRealization.failure_ratio_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms SoundnessRealization.failure_ratio_le

/--
info: 'TranscriptV2.Composition.SoundnessRealization.rename' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms SoundnessRealization.rename

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
