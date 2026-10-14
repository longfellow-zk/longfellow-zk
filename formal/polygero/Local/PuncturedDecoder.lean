import polygero.Algebra.FiniteProbability

/-! A decoder contract for an arbitrary code on supplied coordinate subsets.
The allowed restrictions and radii must have unique bounded-distance recovery. -/
namespace RecursivePolygero
open Finset
variable {Alphabet Message : Type*} {n : ℕ}

open scoped Classical in
noncomputable def puncturedErrors (encode : Message → Fin n → Alphabet)
    (word : Fin n → Alphabet) (S : Finset (Fin n)) (message : Message) : Finset (Fin n) :=
  S.filter fun j => word j ≠ encode message j

/-- Any implementation returning only nearby messages and recovering every
nearby message on the allowed punctured codes satisfies this contract. -/
structure PuncturedDecoder (encode : Message → Fin n → Alphabet)
    (allowed : Finset (Fin n) → ℕ → Prop) where
  decode : (Fin n → Alphabet) → Finset (Fin n) → ℕ → Option Message
  valid : ∀ word S radius message, decode word S radius = some message →
    (puncturedErrors encode word S message).card ≤ radius
  complete : ∀ word S radius, allowed S radius → ∀ message,
    (puncturedErrors encode word S message).card ≤ radius → decode word S radius = some message

namespace PuncturedDecoder
variable {encode : Message → Fin n → Alphabet} {allowed : Finset (Fin n) → ℕ → Prop}

theorem decode_eq_some_iff (decoder : PuncturedDecoder encode allowed)
    (word : Fin n → Alphabet) (S : Finset (Fin n)) (radius : ℕ)
    (hallowed : allowed S radius) (message : Message) :
    decoder.decode word S radius = some message ↔
      (puncturedErrors encode word S message).card ≤ radius :=
  ⟨decoder.valid word S radius message, decoder.complete word S radius hallowed message⟩

theorem decode_eq_none_iff (decoder : PuncturedDecoder encode allowed)
    (word : Fin n → Alphabet) (S : Finset (Fin n)) (radius : ℕ)
    (hallowed : allowed S radius) :
    decoder.decode word S radius = none ↔
      ¬ ∃ message, (puncturedErrors encode word S message).card ≤ radius := by
  constructor
  · rintro hnone ⟨message,hnear⟩
    have := decoder.complete word S radius hallowed message hnear
    simp only [hnone, reduceCtorEq] at this
  · intro hnone
    cases h : decoder.decode word S radius with
    | none => rfl
    | some message => exact (hnone ⟨message,decoder.valid word S radius message h⟩).elim

/-- A specification decoder exists whenever the allowed balls are disjoint.
Efficient implementations may replace this specification without changing its outputs. -/
noncomputable def of_unique (encode : Message → Fin n → Alphabet)
    (allowed : Finset (Fin n) → ℕ → Prop)
    (hunique : ∀ word S radius, allowed S radius → ∀ f g,
      (puncturedErrors encode word S f).card ≤ radius →
      (puncturedErrors encode word S g).card ≤ radius → f = g) :
    PuncturedDecoder encode allowed := by
  classical
  let decode := fun word S radius =>
    if h : ∃ message, (puncturedErrors encode word S message).card ≤ radius
    then some h.choose else none
  refine ⟨decode, ?_, ?_⟩
  · intro word S radius message h
    dsimp [decode] at h
    split_ifs at h with he
    cases Option.some.inj h
    exact he.choose_spec
  · intro word S radius hallowed message hnear
    have he : ∃ m, (puncturedErrors encode word S m).card ≤ radius := ⟨message,hnear⟩
    dsimp [decode]
    rw [dif_pos he]
    exact congrArg some (hunique word S radius hallowed _ message he.choose_spec hnear)

end PuncturedDecoder
end RecursivePolygero
