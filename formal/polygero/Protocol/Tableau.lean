import LigeroFamily.Protocol.DirectProduct

/-! The physical ordinary tableau has only the core rows and the two checked
arithmetic masks. There is no base proximity blind or multiplicative mask.
Arithmetic masks have no singleton repetition index. Legacy honest openings
are projected into this physical representation. -/
namespace RecursivePolygero.Local.Polygero
open LigeroFamily

structure Tableau (F : Type) (nw nq n : ℕ) where
  core : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin n → F
  checkedMask : LinearConstraintMask → Fin n → F

structure Column (F : Type) (nw nq : ℕ) where
  core : (block : CoreBlock) → Fin (block.rowCount nw nq) → F
  checkedMask : LinearConstraintMask → F

namespace Tableau
variable {F : Type} {nw nq n : ℕ}
def ofLegacy (o : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) : Tableau F nw nq n :=
  ⟨o.core,o.checkedMask 0⟩
@[simp] theorem ofLegacy_core (o : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) :
    (ofLegacy o).core = o.core := rfl
@[simp] theorem ofLegacy_checkedMask (o : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) :
    (ofLegacy o).checkedMask = o.checkedMask 0 := rfl

def column (o : Tableau F nw nq n) (j : Fin n) : Column F nw nq :=
  ⟨fun b i => o.core b i j,fun a => o.checkedMask a j⟩
end Tableau
namespace Column
variable {F : Type} {nw nq : ℕ}
def ofLegacy (c : SchemeColumn F LinearConstraintMask NoMask nw nq 1) : Column F nw nq :=
  ⟨c.core,c.checkedMask 0⟩
end Column

def openTableau {F : Type} {nw nq n t : ℕ} (o : Tableau F nw nq n) (Q : QuerySet n t) :=
  fun j : ↥Q.coordinates => o.column j.1
end RecursivePolygero.Local.Polygero
