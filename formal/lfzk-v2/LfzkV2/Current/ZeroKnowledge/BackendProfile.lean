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

def profileSimulate [Fintype F] [DecidableEq F] (nodes : Fin 2792 ↪ F) (cells count : ℕ)
    (Q : QuerySet 2443 84)
    (statement : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Statement)
    (coin : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Coin)
    (tape : ProfileTape nodes cells) : View (F := F) 265 (ConcreteSetup.rows cells) 12 Q :=
  simulate (profileGeometry nodes) Q 0 statement coin tape

/-- This is the exact current `Instance.layer` verification predicate,
specialized to the implementation's public dimensions and affine row count. -/
theorem profileSimulate_verifies [Fintype F] [DecidableEq F]
    (nodes : Fin 2792 ↪ F) (cells count : ℕ) (Q : QuerySet 2443 84)
    (statement : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Statement)
    (coin : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Coin)
    (tape : ProfileTape nodes cells) :
    ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.verify statement
      (PolygeroZk.oracle (profileGeometry nodes) 0 tape) coin
      (profileSimulate nodes cells count Q statement coin tape).2 Q := by
  exact simulate_verifies (profileGeometry nodes) (by change 84+265+12 ≤ 2443; decide)
    Q 0 statement coin tape

def physicalRows {Q : QuerySet 2443 84} {rows : ℕ}
    (order : Fin 84 ≃ ↥Q.coordinates) (view : View (F := F) 265 rows 12 Q) :
    Fin (rows+3) → Fin 84 → F := fun row query =>
  (OpeningBody.leafEquiv F rows).symm (view.1.1 (order query),view.1.2 (order query)) row

def responseSamples (nodes : Fin 2792 ↪ F) {Q : QuerySet 2443 84} {rows : ℕ}
    (view : View (F := F) 265 rows 12 Q) : (Fin 361 → F) × (Fin 698 → F) :=
  (fun i => (view.2.primary : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩),
    fun i => (view.2.arithmetic : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩))

def wireView (nodes : Fin 2792 ↪ F) {Q : QuerySet 2443 84} {rows : ℕ}
    (order : Fin 84 ≃ ↥Q.coordinates) (view : View (F := F) 265 rows 12 Q) :
    ((Fin 361 → F) × (Fin 698 → F)) × (Fin (rows+3) → Fin 84 → F) :=
  (responseSamples nodes view,physicalRows order view)

/-- Exact privacy includes the actual serialized H/Z samples and physical
opened-row ordering, under any further canonical byte encoding. -/
theorem profile_wire_sameDistribution [Fintype F] [DecidableEq F]
    {Observed : Type} [DecidableEq Observed]
    (nodes : Fin 2792 ↪ F) (cells count : ℕ) (Q : QuerySet 2443 84)
    (order : Fin 84 ≃ ↥Q.coordinates) (values : Cells F (ConcreteSetup.rows cells) 265)
    (statement : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Statement)
    (hsat : statement.Satisfies (logical values))
    (coin : ((ConcreteSetup.backend nodes cells).indexed count).backend.layer.Coin)
    (observe : (((Fin 361 → F) × (Fin 698 → F)) ×
      (Fin (ConcreteSetup.rows cells+3) → Fin 84 → F)) → Observed) :
    SameDistribution
      (fun tape => observe (wireView nodes order (real (profileGeometry nodes) Q values statement coin tape)))
      (fun tape => observe (wireView nodes order (profileSimulate nodes cells count Q statement coin tape))) :=
  sameDistribution (profileGeometry nodes) Q 0 values statement hsat coin (observe ∘ wireView nodes order)

section Joint
variable {B N : Type} [Field B] [Fintype B] [DecidableEq B]
  [Field N] [Fintype N] [DecidableEq N]

/-- The physical wire arrays of both fields have their correct joint
distribution, including their shared, ordered opening set. -/
theorem jointProfile_wire_sameDistribution {Observed : Type} [DecidableEq Observed]
    (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
    (binaryCells primeCells binaryCount primeCount : ℕ) (Q : QuerySet 2443 84)
    (order : Fin 84 ≃ ↥Q.coordinates)
    (binaryValues : Cells B (ConcreteSetup.rows binaryCells) 265)
    (primeValues : Cells N (ConcreteSetup.rows primeCells) 265)
    (binaryStatement : ((ConcreteSetup.backend binaryNodes binaryCells).indexed binaryCount).backend.layer.Statement)
    (primeStatement : ((ConcreteSetup.backend primeNodes primeCells).indexed primeCount).backend.layer.Statement)
    (hsat : binaryStatement.Satisfies (logical binaryValues) ∧ primeStatement.Satisfies (logical primeValues))
    (binaryCoin : ((ConcreteSetup.backend binaryNodes binaryCells).indexed binaryCount).backend.layer.Coin)
    (primeCoin : ((ConcreteSetup.backend primeNodes primeCells).indexed primeCount).backend.layer.Coin)
    (observe : ((((Fin 361 → B) × (Fin 698 → B)) ×
      (Fin (ConcreteSetup.rows binaryCells+3) → Fin 84 → B)) ×
      (((Fin 361 → N) × (Fin 698 → N)) ×
      (Fin (ConcreteSetup.rows primeCells+3) → Fin 84 → N))) → Observed) :
    SameDistribution
      (fun tape : ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells =>
        observe (wireView binaryNodes order (real (profileGeometry binaryNodes) Q binaryValues binaryStatement binaryCoin tape.1),
          wireView primeNodes order (real (profileGeometry primeNodes) Q primeValues primeStatement primeCoin tape.2)))
      (fun tape : ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells =>
        observe (wireView binaryNodes order
            (profileSimulate binaryNodes binaryCells binaryCount Q binaryStatement binaryCoin tape.1),
          wireView primeNodes order
            (profileSimulate primeNodes primeCells primeCount Q primeStatement primeCoin tape.2))) :=
  joint_sameDistribution (profileGeometry binaryNodes) (profileGeometry primeNodes) Q 0
    (binaryValues,primeValues) (binaryStatement,primeStatement) hsat (binaryCoin,primeCoin)
    (fun view => observe (wireView binaryNodes order view.1,wireView primeNodes order view.2))

end Joint

end LfzkV2.Current.ZeroKnowledge.Backend

namespace LfzkV2.Current.ZeroKnowledge.Backend
variable {B N : Type} [Field B] [Field N]
abbrev JointMasks (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
    (binaryCells primeCells : ℕ) :=
  ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells
end LfzkV2.Current.ZeroKnowledge.Backend
