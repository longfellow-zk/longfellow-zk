import ReedSolomon.Domain
import Mathlib.Algebra.Polynomial.Roots

/-! Minimal punctured-domain adapter for the imported reconstruction proof.
Word representation is shared with the existing coding-theory development. -/
namespace Codes
abbrev Word (F : Type*) (n : ℕ) := CodingTheory.Word F n
variable {F : Type*} {n k : ℕ}
variable [Field F] [DecidableEq F]

structure RSCode (F : Type*) [Field F] (n k : ℕ) where
  node : Fin n → F
  node_injective : Function.Injective node
  dimension_le_length : k ≤ n

namespace RSCode

variable (C : RSCode F n k)

/-- Restrict a word to a finite set of coordinates, reindexed by a canonical
`Fin` type. -/
noncomputable def restrictWord (_C : RSCode F n k)
    (S : Finset (Fin n)) (x : Word F n) :
    Word F S.card :=
  fun j ↦ x ((Finset.equivFin S).symm j).1

/-- Puncture an RS evaluation code to a finite set of coordinates. -/
noncomputable def puncture (S : Finset (Fin n)) (hk : k ≤ S.card) :
    RSCode F S.card k where
  node j := C.node ((Finset.equivFin S).symm j).1
  node_injective := C.node_injective.comp
    (Subtype.val_injective.comp (Finset.equivFin S).symm.injective)
  dimension_le_length := hk

omit [DecidableEq F] in
@[simp] theorem puncture_node (S : Finset (Fin n)) (hk : k ≤ S.card)
    (j : Fin S.card) :
    (C.puncture S hk).node j = C.node ((Finset.equivFin S).symm j).1 := rfl

end RSCode
end Codes
