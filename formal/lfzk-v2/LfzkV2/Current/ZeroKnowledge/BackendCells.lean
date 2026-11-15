import LfzkV2.Current.ZeroKnowledge.Backend
import LfzkV2.Current.ConcreteSetup

/-! Selected frontend cells enter the ordinary 265-wide logical tableau
in their physical array order. The last row's unused cells are zero; the
84 random prefix coordinates belong to backend masking and are not part
of this logical array. Both fingerprint masks are retained.

Prime shared inputs have no prime address. The existing Prime.index map
orders remaining inputs, pads, the hiding scalar, then fingerprint masks. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendCells

open LigeroFamily
open scoped Classical

variable {F : Type} [Field F]

def tableau {cells : ℕ} (flat : Fin (cells+2) → F) :
    Backend.Cells F (ConcreteSetup.rows cells) 265 := fun row column =>
  if inside : 265*row.val+column.val < cells+2 then flat ⟨265*row.val+column.val,inside⟩ else 0

theorem primary_read {cells : ℕ} (flat : Fin (cells+2) → F) (i : Fin (cells+2)) :
    tableau flat (CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cells) i).1
      (CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cells) i).2 = flat i := by
  have index : 265*(i.val/265)+i.val%265 = i.val := by
    have decomposition := Nat.mod_add_div i.val 265
    omega
  unfold tableau
  change (if inside : 265*(i.val/265)+i.val%265 < cells+2 then
    flat ⟨265*(i.val/265)+i.val%265,inside⟩ else 0) = flat i
  simp only [index,dif_pos i.isLt]

def primeRead {remaining pads : ℕ}
    (flat : Fin (CellLayout.Prime.cells remaining pads+2) → F) :
    CellLayout.Prime.Slot remaining pads → F := flat ∘ CellLayout.Prime.index remaining pads

end LfzkV2.Current.ZeroKnowledge.BackendCells
