import Bcs.Counting
import Mathlib.Data.List.Basic

/-! First-occurrence slots for two domain-separated defining queries. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Bcs

/-- The trace facts established after the verifier appends its two defining
queries.  `alphaQuery` is `H₁(x,root)` and `subsetQuery` is
`H₂(x,root,response)`.  Appending missing verifier queries is precisely what
proves `alpha_mem` and `subset_mem`; `trace_length` carries the resulting
`Q+2` bound.

The two inputs are required to be distinct (normally by domain-separation
tags), so their first occurrences have a strict order. -/
structure FirstOccurrenceTrace (Ω Query : Type*) (querySlots : ℕ)
    [BEq Query] [LawfulBEq Query] where
  trace : Ω → List Query
  alphaQuery : Ω → Query
  subsetQuery : Ω → Query
  alpha_mem : ∀ ω, alphaQuery ω ∈ trace ω
  subset_mem : ∀ ω, subsetQuery ω ∈ trace ω
  separated : ∀ ω, alphaQuery ω ≠ subsetQuery ω
  trace_length : ∀ ω, (trace ω).length ≤ querySlots

namespace FirstOccurrenceTrace

variable {Ω Query : Type*} [Fintype Ω] [BEq Query] [LawfulBEq Query]
variable {querySlots : ℕ}

/-- Pull a first-occurrence trace back along a deterministic map of sample
spaces.  This is used to add independent Merkle randomness without changing
the two Fiat--Shamir defining queries or their order. -/
def comap {Ω' : Type*}
    (F : FirstOccurrenceTrace Ω Query querySlots) (f : Ω' → Ω) :
    FirstOccurrenceTrace Ω' Query querySlots where
  trace ω := F.trace (f ω)
  alphaQuery ω := F.alphaQuery (f ω)
  subsetQuery ω := F.subsetQuery (f ω)
  alpha_mem ω := F.alpha_mem (f ω)
  subset_mem ω := F.subset_mem (f ω)
  separated ω := F.separated (f ω)
  trace_length ω := F.trace_length (f ω)

/-- First defining alpha query precedes the defining subset query. -/
def caseA (F : FirstOccurrenceTrace Ω Query querySlots)
    (listed win bindBreak : Ω → Prop) (i : Fin querySlots) (ω : Ω) : Prop :=
  win ω ∧ ¬bindBreak ω ∧
    (F.trace ω).idxOf (F.alphaQuery ω) <
      (F.trace ω).idxOf (F.subsetQuery ω) ∧
    ((¬listed ω ∧ (F.trace ω).idxOf (F.subsetQuery ω) = i.val) ∨
      (listed ω ∧ (F.trace ω).idxOf (F.alphaQuery ω) = i.val))

/-- Case B, also charged to the first H2 slot: H2 occurred before H1.  This
is the slot whose fresh subset answer the predictable-selection lemma uses.
-/
def caseB (F : FirstOccurrenceTrace Ω Query querySlots)
    (win bindBreak : Ω → Prop) (i : Fin querySlots) (ω : Ω) : Prop :=
  win ω ∧ ¬bindBreak ω ∧
    (F.trace ω).idxOf (F.subsetQuery ω) = i.val ∧
    (F.trace ω).idxOf (F.subsetQuery ω) <
      (F.trace ω).idxOf (F.alphaQuery ω)

omit [Fintype Ω] in
/-- The defining queries' first occurrences are different. -/
theorem idxOf_ne (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    (F.trace ω).idxOf (F.alphaQuery ω) ≠
      (F.trace ω).idxOf (F.subsetQuery ω) := by
  intro heq
  exact F.separated ω ((List.idxOf_inj (F.alpha_mem ω)).mp heq)

omit [Fintype Ω] in
/-- The first H2 occurrence is a real slot of the augmented trace. -/
theorem subset_idx_lt (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    (F.trace ω).idxOf (F.subsetQuery ω) < querySlots :=
  lt_of_lt_of_le (List.idxOf_lt_length_of_mem (F.subset_mem ω)) (F.trace_length ω)

omit [Fintype Ω] in
/-- The first `H₁` occurrence is a real slot of the augmented trace. -/
theorem alpha_idx_lt (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    (F.trace ω).idxOf (F.alphaQuery ω) < querySlots :=
  lt_of_lt_of_le (List.idxOf_lt_length_of_mem (F.alpha_mem ω)) (F.trace_length ω)

/-- The actual first-occurrence slot of the defining batching query. -/
def alphaSlot (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    Fin querySlots :=
  ⟨(F.trace ω).idxOf (F.alphaQuery ω), F.alpha_idx_lt ω⟩

/-- The actual first-occurrence slot of the defining subset query. -/
def subsetSlot (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    Fin querySlots :=
  ⟨(F.trace ω).idxOf (F.subsetQuery ω), F.subset_idx_lt ω⟩

omit [Fintype Ω] in
theorem alphaSlot_ne_subsetSlot
    (F : FirstOccurrenceTrace Ω Query querySlots) (ω : Ω) :
    F.alphaSlot ω ≠ F.subsetSlot ω := by
  intro heq
  exact F.idxOf_ne ω (Fin.ext_iff.mp heq)

omit [Fintype Ω] in
theorem subsetSlot_eq_of_caseB
    (F : FirstOccurrenceTrace Ω Query querySlots)
    (win bindBreak : Ω → Prop) (i : Fin querySlots) (ω : Ω)
    (hcase : F.caseB win bindBreak i ω) :
    F.subsetSlot ω = i := by
  exact Fin.ext hcase.2.2.1

omit [Fintype Ω] in
theorem alphaSlot_eq_of_caseA_listed
    (F : FirstOccurrenceTrace Ω Query querySlots)
    (listed win bindBreak : Ω → Prop) (i : Fin querySlots) (ω : Ω)
    (hcase : F.caseA listed win bindBreak i ω) (hlisted : listed ω) :
    F.alphaSlot ω = i := by
  rcases hcase.2.2.2 with hfloor | hexcess
  · exact absurd hlisted hfloor.1
  · exact Fin.ext hexcess.2

omit [Fintype Ω] in
theorem subsetSlot_eq_of_caseA_floor
    (F : FirstOccurrenceTrace Ω Query querySlots)
    (listed win bindBreak : Ω → Prop) (i : Fin querySlots) (ω : Ω)
    (hcase : F.caseA listed win bindBreak i ω) (hunlisted : ¬listed ω) :
    F.subsetSlot ω = i := by
  rcases hcase.2.2.2 with hfloor | hexcess
  · exact Fin.ext hfloor.2
  · exact absurd hexcess.1 hunlisted

end FirstOccurrenceTrace
end Bcs
