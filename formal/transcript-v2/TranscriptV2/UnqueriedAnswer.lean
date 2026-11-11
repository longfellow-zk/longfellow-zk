import TranscriptV2.Queries
import Bcs.FiniteProbability

/-! Guessing one selected, unqueried oracle answer. Both the address and
its target may use other oracle coordinates. Their joint independence from
the selected answer is the entire local proof obligation. -/
namespace TranscriptV2.UnqueriedAnswer
open Finset Bcs.TotalOracle Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

variable {P D Out : Type} [DecidableEq P]

def Hit {fuel : ℕ} (select : Out → (P → D) → P × D)
    (program : Tree P D Out fuel) (H : P → D) : Prop :=
  let selected := select (program.run H).1 H
  selected.1 ∉ seen program H ∧ H selected.1 = selected.2

/-- A partial selector can decline to name a coordinate. This lets a finite
oracle window count only represented inputs, without assigning artificial
guesses to rejected executions or to addresses outside that window. -/
def PartialHit {fuel : ℕ} (select : Out → (P → D) → Option (P × D))
    (program : Tree P D Out fuel) (H : P → D) : Prop :=
  ∃ point target, select (program.run H).1 H = some (point,target) ∧
    point ∉ seen program H ∧ H point = target

theorem partial_ratio_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (select : Out → (P → D) → Option (P × D))
    (independent : ∀ out H H' point target, select out H = some (point,target) →
      AgreeOff point H H' → select out H' = some (point,target))
    (program : Tree P D Out fuel) :
    ((univ.filter (PartialHit select program)).card : ℚ) /
      (Fintype.card D : ℚ)^Fintype.card P ≤ 1 / (Fintype.card D : ℚ) := by
  let event := fun point H answer =>
    select (program.run H).1 H = some (point,answer) ∧ point ∉ seen program H
  have stable : ∀ point H H', AgreeOff point H H' → ∀ answer,
      event point H answer → event point H' answer := by
    intro point H H' agree answer ⟨address,missing⟩
    have run := run_eq_of_not_mem program point agree (by
      simpa only [seen,List.mem_toFinset] using missing)
    have same := independent (program.run H).1 H H' point answer address agree
    refine ⟨?_,?_⟩
    · rw [run]; exact same
    · simpa only [seen,queried,run] using missing
  let weight := fun point H =>
    if (select (program.run H).1 H).map Prod.fst = some point ∧ point ∉ seen program H then 1 else 0
  have localBound : ∀ point H, (univ.filter (event point H)).card ≤ weight point H := by
    intro point H
    by_cases selected : (select (program.run H).1 H).map Prod.fst = some point ∧ point ∉ seen program H
    · obtain ⟨pair,found,equal⟩ := Option.map_eq_some_iff.mp selected.1
      obtain ⟨raw,target⟩ := pair
      change raw = point at equal
      subst raw
      have same : univ.filter (event point H) = {target} := by
        ext answer
        simp [event,found,selected.2,eq_comm]
      rw [same,card_singleton]
      exact le_of_eq (by simp only [weight,if_pos selected])
    · have empty : univ.filter (event point H) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro answer member
        obtain ⟨found,missing⟩ := (mem_filter.mp member).2
        exact selected ⟨by rw [found]; rfl,missing⟩
      rw [empty,card_empty]
      exact Nat.zero_le _
  have total : ∀ H, ∑ point, weight point H ≤ 1 := by
    intro H
    calc
      (∑ point, weight point H) ≤
          ∑ point, if (select (program.run H).1 H).map Prod.fst = some point then 1 else 0 := by
        apply sum_le_sum
        intro point _
        dsimp [weight]
        split_ifs <;> simp_all
      _ ≤ 1 := by cases select (program.run H).1 H <;> simp
  simpa only [Nat.cast_one] using ratio_exists_coord_le
    (PartialHit select program) event
    (fun H ⟨point,target,found,missing,value⟩ => ⟨point,by rw [value]; exact ⟨found,missing⟩⟩) stable weight
    (fun point H => by simpa only [event] using localBound point H) 1 total

theorem partial_density_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (select : Out → (P → D) → Option (P × D))
    (independent : ∀ out H H' point target, select out H = some (point,target) →
      AgreeOff point H H' → select out H' = some (point,target))
    (program : Tree P D Out fuel) :
    density (PartialHit select program) ≤ 1 / (Fintype.card D : ℚ) := by
  simpa only [density,Fintype.card_fun,Nat.cast_pow] using partial_ratio_le select independent program

theorem ratio_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (select : Out → (P → D) → P × D)
    (independent : ∀ out H H', AgreeOff (select out H).1 H H' → select out H = select out H')
    (program : Tree P D Out fuel) :
    ((univ.filter (Hit select program)).card : ℚ) /
      (Fintype.card D : ℚ)^Fintype.card P ≤ 1 / (Fintype.card D : ℚ) := by
  have bound := partial_ratio_le (fun out H => some (select out H)) (by
    intro out H H' point target found agree
    have same := Option.some.inj found
    rw [← independent out H H' (by simpa only [same] using agree)]
    exact found) program
  have same : PartialHit (fun out H => some (select out H)) program = Hit select program := by
    funext H
    apply propext
    constructor
    · rintro ⟨point,target,found,missing,value⟩
      have pair := Option.some.inj found
      simpa only [Hit,pair] using And.intro missing value
    · intro hit
      exact ⟨_,_,rfl,hit⟩
  rwa [same] at bound

theorem density_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (select : Out → (P → D) → P × D)
    (independent : ∀ out H H', AgreeOff (select out H).1 H H' → select out H = select out H')
    (program : Tree P D Out fuel) : density (Hit select program) ≤ 1 / (Fintype.card D : ℚ) := by
  simpa only [density,Fintype.card_fun,Nat.cast_pow] using ratio_le select independent program

end TranscriptV2.UnqueriedAnswer
