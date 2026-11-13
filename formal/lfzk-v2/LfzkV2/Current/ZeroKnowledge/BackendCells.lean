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

theorem tail_zero {cells : ℕ} (flat : Fin (cells+2) → F)
    (row : Fin (ConcreteSetup.rows cells)) (column : Fin 265)
    (outside : cells+2 ≤ 265*row.val+column.val) : tableau flat row column = 0 :=
  dif_neg (by omega)

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

theorem logical_read {cells : ℕ} (flat : Fin (cells+2) → F) :
    LfzkV2.Backend.read (Backend.logical (tableau flat)) ∘
      LfzkV2.Backend.linearAddress
        (CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cells)) = flat := by
  funext i
  exact primary_read flat i

def primeRead {remaining pads : ℕ}
    (flat : Fin (CellLayout.Prime.cells remaining pads+2) → F) :
    CellLayout.Prime.Slot remaining pads → F := flat ∘ CellLayout.Prime.index remaining pads

theorem prime_read {remaining pads : ℕ}
    (flat : Fin (CellLayout.Prime.cells remaining pads+2) → F) (slot : CellLayout.Prime.Slot remaining pads) :
    tableau flat
      (CellLayout.primary (by decide : 0<265)
        (ConcreteSetup.rows_capacity (CellLayout.Prime.cells remaining pads))
        (CellLayout.Prime.index remaining pads slot)).1
      (CellLayout.primary (by decide : 0<265)
        (ConcreteSetup.rows_capacity (CellLayout.Prime.cells remaining pads))
        (CellLayout.Prime.index remaining pads slot)).2 = primeRead flat slot :=
  primary_read flat _

theorem prime_logical_read {remaining pads : ℕ}
    (flat : Fin (CellLayout.Prime.cells remaining pads+2) → F) :
    LfzkV2.Backend.read (Backend.logical (tableau flat)) ∘
      LfzkV2.Backend.linearAddress
        ((CellLayout.Prime.index remaining pads).toEmbedding.trans
          (CellLayout.primary (by decide : 0<265)
            (ConcreteSetup.rows_capacity (CellLayout.Prime.cells remaining pads)))) = primeRead flat := by
  funext slot
  exact prime_read flat slot

/-- Store typed prime cells in the actual flat runtime order. -/
def primeFlat {remaining pads : ℕ} (read : CellLayout.Prime.Slot remaining pads → F) :
    Fin (CellLayout.Prime.cells remaining pads+2) → F :=
  read ∘ (CellLayout.Prime.index remaining pads).symm

omit [Field F] in
theorem primeRead_flat {remaining pads : ℕ} (read : CellLayout.Prime.Slot remaining pads → F) :
    primeRead (primeFlat read) = read := by
  funext slot
  simp only [primeRead,primeFlat,Function.comp_apply,Equiv.symm_apply_apply]

end LfzkV2.Current.ZeroKnowledge.BackendCells
