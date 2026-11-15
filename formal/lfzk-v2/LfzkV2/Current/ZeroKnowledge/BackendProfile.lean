import LfzkV2.Current.ZeroKnowledge.BackendJoint
import LfzkV2.Current.ConcreteSetup
import LfzkV2.Current.OpeningBody

/-! Concrete rate-1/7 specialization and the runtime's transmitted arrays.
The row map is the existing `u,m,witness,fstar` map. H and Z are evaluated
on their actual oracle-prefix nodes; they are not serialized as monomial
coefficients. An arbitrary supplied ordering of Q handles the runtime's
without-replacement query order without changing the underlying simulator. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend
open Polynomial Application RecursivePolygero LigeroFamily RecursivePolygero.Local
open scoped Classical

variable {F : Type} [Field F]

def profileGeometry (nodes : Fin 2792 ↪ F) : PolygeroZk.Geometry F 84 265 0 2443 where
  domain := (ConcreteSetup.backend nodes 0).backend.domain
  k_le_n := by decide
  productSlots := ⟨Fin.elim0,by intro a; exact Fin.elim0 a⟩
  short_positive := by decide
  product_degree := by decide

abbrev ProfileTape (nodes : Fin 2792 ↪ F) (cells : ℕ) :=
  Tape (profileGeometry nodes) (ConcreteSetup.rows cells) 12

def physicalRows {Q : QuerySet 2443 84} {rows : ℕ}
    (order : Fin 84 ≃ ↥Q.coordinates) (view : View (F := F) 265 rows 12 Q) :
    Fin (rows+3) → Fin 84 → F := fun row query =>
  (OpeningBody.leafEquiv F rows).symm (view.1.1 (order query),view.1.2 (order query)) row

def responseSamples (nodes : Fin 2792 ↪ F) {Q : QuerySet 2443 84} {rows : ℕ}
    (view : View (F := F) 265 rows 12 Q) : (Fin 361 → F) × (Fin 698 → F) :=
  (fun i => (view.2.primary : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩),
    fun i => (view.2.arithmetic : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩))

end LfzkV2.Current.ZeroKnowledge.Backend

namespace LfzkV2.Current.ZeroKnowledge.Backend
variable {B N : Type} [Field B] [Field N]
abbrev JointMasks (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
    (binaryCells primeCells : ℕ) :=
  ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells
end LfzkV2.Current.ZeroKnowledge.Backend
