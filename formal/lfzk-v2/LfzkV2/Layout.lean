import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Committed witness layout

`runtime/v2/proto/src/sumcheck.rs` allocates two pads per round, then the
two final-claim pads and their product. Layers follow the private-input prefix.
The indices below are natural numbers; correspondence to machine arithmetic
additionally requires that the total committed length fit in `usize`.
-/

namespace LfzkV2

def padCount (rounds : ℕ) : ℕ := 2 * rounds + 3

def geometrySize : List ℕ → ℕ
  | [] => 0
  | rounds :: rest => padCount rounds + geometrySize rest

/-- A position in the concatenated layer blocks, including the product slots. -/
inductive GeometrySlot : List ℕ → Type where
  | here {rounds : ℕ} {rest : List ℕ} (index : Fin (padCount rounds)) :
      GeometrySlot (rounds :: rest)
  | there {rounds : ℕ} {rest : List ℕ} (slot : GeometrySlot rest) :
      GeometrySlot (rounds :: rest)

namespace GeometrySlot

def index : {geometry : List ℕ} → GeometrySlot geometry → ℕ
  | _, .here i => i.val
  | rounds :: _, .there slot => padCount rounds + index slot

theorem index_lt {geometry : List ℕ} (slot : GeometrySlot geometry) :
    slot.index < geometrySize geometry := by
  induction slot with
  | here i => exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  | there slot ih => exact Nat.add_lt_add_left ih _

theorem index_injective {geometry : List ℕ} :
    Function.Injective (@index geometry) := by
  intro a
  induction a with
  | here i =>
      intro b h
      cases b with
      | here j => exact congrArg here (Fin.ext h)
      | there slot =>
          have hi := i.isLt
          simp only [index] at h
          omega
  | there slot ih =>
      intro b h
      cases b with
      | here j =>
          have hj := j.isLt
          simp only [index] at h
          omega
      | there other =>
          exact congrArg there (ih (Nat.add_left_cancel h))

def round {rounds : ℕ} {rest : List ℕ} (r : Fin rounds) (s : Fin 2) :
    GeometrySlot (rounds :: rest) :=
  .here ⟨2 * r.val + s.val, by have := r.isLt; have := s.isLt; unfold padCount; omega⟩

def claim {rounds : ℕ} {rest : List ℕ} (s : Fin 3) : GeometrySlot (rounds :: rest) :=
  .here ⟨2 * rounds + s.val, by have := s.isLt; unfold padCount; omega⟩

@[simp] theorem index_round {rounds : ℕ} {rest : List ℕ} (r : Fin rounds) (s : Fin 2) :
    (round (rest := rest) r s).index = 2 * r.val + s.val := rfl

@[simp] theorem index_claim {rounds : ℕ} {rest : List ℕ} (s : Fin 3) :
    (claim (rounds := rounds) (rest := rest) s).index = 2 * rounds + s.val := rfl

/-- Round pads cannot overlap either final-claim pad or its product. -/
theorem round_ne_claim {rounds : ℕ} {rest : List ℕ} (r : Fin rounds) (s : Fin 2)
    (c : Fin 3) : round (rest := rest) r s ≠ claim c := by
  intro h
  have hi := congrArg index h
  simp only [index_round, index_claim] at hi
  have := r.isLt
  have := s.isLt
  omega

theorem round_injective {rounds : ℕ} {rest : List ℕ} (r r' : Fin rounds) (s s' : Fin 2)
    (h : round (rest := rest) r s = round r' s') : r = r' ∧ s = s' := by
  have hi := congrArg index h
  simp only [index_round] at hi
  have := s.isLt
  have := s'.isLt
  constructor <;> apply Fin.ext <;> omega

end GeometrySlot

inductive CommittedSlot (nPrivate : ℕ) (geometry : List ℕ) where
  | input (index : Fin nPrivate)
  | pad (slot : GeometrySlot geometry)

namespace CommittedSlot

def index {nPrivate : ℕ} {geometry : List ℕ} : CommittedSlot nPrivate geometry → ℕ
  | .input i => i.val
  | .pad slot => nPrivate + slot.index

theorem index_lt {nPrivate : ℕ} {geometry : List ℕ} (slot : CommittedSlot nPrivate geometry) :
    slot.index < nPrivate + geometrySize geometry := by
  cases slot with
  | input i => exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  | pad slot => exact Nat.add_lt_add_left slot.index_lt _

/-- Private inputs, round pads, final pads, and product slots occupy distinct coordinates. -/
theorem index_injective {nPrivate : ℕ} {geometry : List ℕ} :
    Function.Injective (@index nPrivate geometry) := by
  intro a b h
  cases a with
  | input i =>
      cases b with
      | input j => exact congrArg input (Fin.ext h)
      | pad slot =>
          have := i.isLt
          simp only [index] at h
          omega
  | pad slot =>
      cases b with
      | input j =>
          have := j.isLt
          simp only [index] at h
          omega
      | pad other => exact congrArg pad (GeometrySlot.index_injective (Nat.add_left_cancel h))

/-- If the whole vector fits, every allocated coordinate is below the machine-size limit. -/
theorem index_lt_limit {nPrivate limit : ℕ} {geometry : List ℕ}
    (slot : CommittedSlot nPrivate geometry) (hsize : nPrivate + geometrySize geometry ≤ limit) :
    slot.index < limit := lt_of_lt_of_le slot.index_lt hsize

end CommittedSlot

end LfzkV2
