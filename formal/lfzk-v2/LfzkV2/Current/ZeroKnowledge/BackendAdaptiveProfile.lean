import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveJoint
import LfzkV2.Current.ZeroKnowledge.BackendProfile

/-! The current backend's actual transmitted response arrays and ordered
84-column reader. This is a specialization of the existing fixed-opening
algebra through the public response-fiber translation, not a new backend.
The selector may be the actual numbered SHA/PRF reader at a fixed public
frontend and ghost root. Both fields' complete H/Z arrays precede it. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend.Adaptive.Profile
open Polynomial Application LigeroFamily RecursivePolygero.Local
open scoped Classical

abbrev ResponseSamples (F : Type) := (Fin 361 → F) × (Fin 698 → F)

def responseSamples {F : Type} [Field F] (nodes : Fin 2792 ↪ F)
    (response : LigeroPayload F 349 12) : ResponseSamples F :=
  (fun i => (response.primary : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩),
    fun i => (response.arithmetic : F[X]).eval (nodes ⟨349+i.val,by have := i.isLt; omega⟩))

theorem responseSamples_eq {F : Type} [Field F] (nodes : Fin 2792 ↪ F)
    {Q : QuerySet 2443 84} {rows : ℕ} (view : Backend.View (F := F) 265 rows 12 Q) :
    responseSamples nodes view.2 = Backend.responseSamples nodes view := rfl

def referenceIndices : Fin 84 ↪ Fin 2443 where
  toFun i := ⟨i.val,by have := i.isLt; omega⟩
  inj' _ _ equal := Fin.ext (congrArg (fun i : Fin 2443 => i.val) equal)

def reference : QuerySet 2443 84 := OrderedOpening.query referenceIndices

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
variable (binaryCells primeCells : ℕ)

abbrev Response := ResponseSamples B × ResponseSamples N
abbrev Output := Response (B := B) (N := N) ×
  Option ((Fin 84 ↪ Fin 2443) ×
    ((Fin (ConcreteSetup.rows binaryCells+3) → Fin 84 → B) ×
      (Fin (ConcreteSetup.rows primeCells+3) → Fin 84 → N)))

def responses (response : Adaptive.Responses (B := B) (N := N) (r := 84) (w := 265) (s := 12)) :
    Response (B := B) (N := N) :=
  (responseSamples binaryNodes response.1,responseSamples primeNodes response.2)

/-- The selector result retains the sampled order. Rows have their actual
u,m,witness,fstar order, using the existing physical-row equivalence. -/
def wire (output : JointOutput (B := B) (N := N) (w := 265)
    (bw := ConcreteSetup.rows binaryCells) (nw := ConcreteSetup.rows primeCells) (s := 12)
    (OrderedOpening.query (n := 2443) (t := 84))) :
    Output (B := B) (N := N) binaryCells primeCells :=
  (responses binaryNodes primeNodes output.1,output.2.map fun selected =>
    (selected.1,
      Backend.physicalRows (OrderedOpening.order selected.1) (selected.2.1,output.1.1),
      Backend.physicalRows (OrderedOpening.order selected.1) (selected.2.2,output.1.2)))

variable {BE NE : Type} [Fintype BE] [Fintype NE]
variable (statements :
  ConstraintSystem B (ConcreteSetup.rows binaryCells) 0 265 BE ×
    ConstraintSystem N (ConcreteSetup.rows primeCells) 0 265 NE)
variable (coins :
  Polygero.Coin B BE (ConcreteSetup.rows binaryCells) 0 12 ×
    Polygero.Coin N NE (ConcreteSetup.rows primeCells) 0 12)
variable (select : Response (B := B) (N := N) → Option (Fin 84 ↪ Fin 2443))

/-- Public simulation has no logical-cell vector or satisfying witness
argument. Its randomness is exactly the actual pair of backend mask tapes. -/
def simulate (tape : ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells) :
    Output (B := B) (N := N) binaryCells primeCells :=
  wire binaryNodes primeNodes binaryCells primeCells
    (Adaptive.simulate (profileGeometry binaryNodes) (profileGeometry primeNodes) reference 0
      statements coins OrderedOpening.query (select ∘ responses binaryNodes primeNodes) tape)

variable (cells : Cells B (ConcreteSetup.rows binaryCells) 265 ×
  Cells N (ConcreteSetup.rows primeCells) 265)

def honest (tape : ProfileTape binaryNodes binaryCells × ProfileTape primeNodes primeCells) :
    Output (B := B) (N := N) binaryCells primeCells :=
  wire binaryNodes primeNodes binaryCells primeCells
    (Adaptive.honest (profileGeometry binaryNodes) (profileGeometry primeNodes)
      statements coins OrderedOpening.query (select ∘ responses binaryNodes primeNodes) cells tape)

/-- The current H/Z arrays and complete ordered physical openings have the
honest joint distribution. The actual reader can reject; both sides retain
that same decision, without an independently sampled opening answer. -/
theorem sameDistribution {Observed : Type} [DecidableEq Observed]
    (satisfied : statements.1.Satisfies (logical cells.1) ∧ statements.2.Satisfies (logical cells.2))
    (observe : Output (B := B) (N := N) binaryCells primeCells → Observed) :
    SameDistribution
      (fun tape => observe (honest binaryNodes primeNodes binaryCells primeCells statements coins select cells tape))
      (fun tape => observe (simulate binaryNodes primeNodes binaryCells primeCells statements coins select tape)) :=
  Adaptive.sameDistribution (profileGeometry binaryNodes) (profileGeometry primeNodes) reference 0
    statements coins OrderedOpening.query (select ∘ responses binaryNodes primeNodes) cells satisfied
    (observe ∘ wire binaryNodes primeNodes binaryCells primeCells)

end LfzkV2.Current.ZeroKnowledge.Backend.Adaptive.Profile
