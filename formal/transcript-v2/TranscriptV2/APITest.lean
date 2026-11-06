import TranscriptV2

/-! A finite one-round transcript exercises the representation laws as well as
the two exceptional cases. Its final input binds the body and actual link. -/
namespace TranscriptV2.APITest
open Bcs.TotalOracle Merkle.RandomOracle

abbrev Point := Option (Fin 2 × Bool)
abbrev Output := Bool × Fin 2
abbrev Answer := Fin 2 × Bool

def model : Chain Point (Fin 2) Bool Output 1 where
  parent := fun p => match p with | none => none | some _ => some none
  claimed := fun p => match p with | none => 0 | some p => p.1
  State := Point
  rank := fun p => match p with | none => 0 | some _ => 1
  initial := fun _ => none
  input := id
  advance := fun out _ _ a => some (a.1, out.1)
  initial_rank := by intro _; rfl
  advance_rank := by
    intro out i s a _
    change 1 = i.val+1
    omega
  advance_parent := by
    intro out i s a hs
    cases s with
    | none => rfl
    | some p => change 1 = i.val at hs; omega
  advance_link := by intro _ _ _ _ _; rfl
  finalSeal := Prod.snd

theorem final_input (out : Output) (H : Point → Answer) :
    model.finalSealPoint out H = some ((H none).1, out.1) := rfl

example (H : Point → Answer) (seal₁ seal₂ : Fin 2) :
    model.finalSealPoint (false, seal₁) H ≠ model.finalSealPoint (true, seal₂) H := by
  simp [final_input]

def noQueries : Tree Point Answer Output 0 := .done (false, 0)
def constantOracle : Point → Answer := fun _ => (0, false)

-- A lucky final seal can pass with no queries, so the lower bound must keep
-- its explicit guessing exception.
example : (constantOracle (model.finalSealPoint (noQueries.run constantOracle).1 constantOracle)).1 =
    model.finalSeal (noQueries.run constantOracle).1 := rfl

example : FinalSealGuess model noQueries constantOracle := by
  refine ⟨some (0, false), rfl, ?_, rfl⟩
  simp [seen, queried, noQueries]

def backwards : Tree Point Answer Output 2 :=
  .query (some (0, false)) fun _ => .query none fun _ => .done (false, 0)

-- Asking the final point before its parent succeeds here only because the
-- guessed link equals the later root answer.
example : LinkGuess model.toLinks backwards constantOracle := by
  refine ⟨none, some (0, false), ?_, rfl⟩
  simp [earlyChildren, before, backwards, model]

def ordered : Tree Point Answer Output 2 :=
  .query none fun a => .query (some (a.1, false)) fun b => .done (false, b.1)

-- The hypotheses of the lower bound are inhabited by an ordinary ordered
-- execution, for every oracle, rather than only by a lucky constant oracle.
example (H : Point → Answer) : ¬ LinkGuess model.toLinks ordered H := by
  rintro ⟨p,c,hc,_⟩
  have hp := (Finset.mem_filter.mp hc).2
  cases c with
  | none => simp [model] at hp
  | some c =>
      have heq : p = none := (Option.some.inj hp).symm
      subst p
      simp [earlyChildren, before, ordered] at hc

example (H : Point → Answer) : ¬ FinalSealGuess model ordered H := by
  rintro ⟨p,hp,hm,_⟩
  apply hm
  rw [← hp]
  simp [final_input, seen, queried, ordered, Tree.run]

example (H : Point → Answer) :
    (H (model.finalSealPoint (ordered.run H).1 H)).1 = model.finalSeal (ordered.run H).1 := rfl

example {fuel : ℕ} (tree : Tree Point Answer Output fuel) (H : Point → Answer)
    (hl : ¬ LinkGuess model.toLinks tree H) (hs : ¬ FinalSealGuess model tree H)
    (hv : (H (model.finalSealPoint (tree.run H).1 H)).1 = model.finalSeal (tree.run H).1) :
    2 ≤ (seen tree H).card := model.required_fresh_queries tree H hl hs hv

#guard_msgs (drop info) in #check Chain.parent_queried_before
#guard_msgs (drop info) in #check Chain.required_fresh_queries
#guard_msgs (drop info) in #check short_search_ratio_le
#guard_msgs (drop info) in #check Reduction.failure_ratio_le

/--
info: 'TranscriptV2.link_guess_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms link_guess_ratio_le
/--
info: 'TranscriptV2.final_seal_guess_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms final_seal_guess_ratio_le
/--
info: 'TranscriptV2.Chain.required_fresh_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Chain.required_fresh_queries
/--
info: 'TranscriptV2.short_search_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms short_search_ratio_le
/--
info: 'TranscriptV2.Reduction.failure_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Reduction.failure_ratio_le

end TranscriptV2.APITest
