import LfzkV2.Current.ZeroKnowledge.CommonLabels
import LfzkV2.Current.ZeroKnowledge.BackendJoint

/-! Instantiate the common-label Merkle argument with the current affine
backend simulator.  The committed columns below contain every ordinary row,
both checked mask rows and the proximity mask.  The public part contains both
complete H/Z responses in addition to the frontend prefix.

At a fixed Merkle label tape the frontend prefix, logical cells, affine
statement and batching coin can depend on those labels.  They cannot depend
on the backend mask tape: that is the separation established by the frontend
masking argument.  No independence of the honest commitment root and backend
masks is assumed.  The actual backend change of variables supplies the two
pointwise equalities required by the Merkle argument.

This remains the commit-first experiment.  An observer's earlier hash queries
must be transported separately before applying this result. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleBackend

open Merkle Merkle.MH LigeroFamily RecursivePolygero.Local
open scoped Classical

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]

abbrev Leaf := RecursivePolygero.MerkleCompiler.Leaf B bw 0 ×
  RecursivePolygero.MerkleCompiler.Leaf N nw 0

abbrev MaskTape := Backend.Tape binary bw s × Backend.Tape prime nw s

abbrev Responses := LigeroPayload B (r+w) s × LigeroPayload N (r+w) s

/-- All committed rows at one column, including the independent proximity
mask.  This is the same ordinary-column/proximity pair consumed by Polygero. -/
def column {F : Type} {rows : ℕ} (oracle : Polygero.Oracle F rows 0 n) (i : Fin n) :
    RecursivePolygero.MerkleCompiler.Leaf F rows 0 :=
  ({ core := fun block row => oracle.ordinary.core block row i
     checkedMask := fun kind => oracle.ordinary.checkedMask kind i },oracle.proximityMask i)

def realColumns (cells : Backend.Cells B bw w × Backend.Cells N nw w)
    (coin : MaskTape binary prime (bw := bw) (nw := nw) (s := s)) (i : Fin n) :
    Leaf (B := B) (N := N) (bw := bw) (nw := nw) :=
  (column (PolygeroZk.oracle binary (Backend.messages cells.1) coin.1) i,
    column (PolygeroZk.oracle prime (Backend.messages cells.2) coin.2) i)

def simColumns (coin : MaskTape binary prime (bw := bw) (nw := nw) (s := s)) (i : Fin n) :
    Leaf (B := B) (N := N) (bw := bw) (nw := nw) :=
  (column (PolygeroZk.oracle binary 0 coin.1) i,
    column (PolygeroZk.oracle prime 0 coin.2) i)

def realResponses (Q : QuerySet n r)
    (cells : Backend.Cells B bw w × Backend.Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : MaskTape binary prime (bw := bw) (nw := nw) (s := s)) :
    Responses (B := B) (N := N) (r := r) (w := w) (s := s) :=
  ((Backend.jointReal binary prime Q cells statements coins tape).1.2,
    (Backend.jointReal binary prime Q cells statements coins tape).2.2)

def simResponses (Q : QuerySet n r) (pivot : Fin w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : MaskTape binary prime (bw := bw) (nw := nw) (s := s)) :
    Responses (B := B) (N := N) (r := r) (w := w) (s := s) :=
  ((Backend.jointSimulate binary prime Q pivot statements coins tape).1.2,
    (Backend.jointSimulate binary prime Q pivot statements coins tape).2.2)

/-- The masking bijection preserves the actual complete tuple leaf at each
shared opening, rather than only a dot product or participant marginal. -/
theorem columns_coupling (Q : QuerySet n r) (pivot : Fin w)
    (cells : Backend.Cells B bw w × Backend.Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (satisfied : statements.1.Satisfies (Backend.logical cells.1) ∧
      statements.2.Satisfies (Backend.logical cells.2))
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : MaskTape binary prime (bw := bw) (nw := nw) (s := s))
    (i : Fin n) (hi : i ∈ Q.coordinates) :
    realColumns binary prime cells tape i =
      simColumns binary prime
        (Backend.jointCoupling binary prime Q pivot cells statements satisfied coins tape) i := by
  have equal := Backend.jointCoupling_view binary prime Q pivot cells statements satisfied coins tape
  have opened := congrArg (fun view =>
    ((view.1.1.1 ⟨i,hi⟩,view.1.1.2 ⟨i,hi⟩),
      (view.2.1.1 ⟨i,hi⟩,view.2.1.2 ⟨i,hi⟩))) equal
  exact opened.symm

theorem responses_coupling (Q : QuerySet n r) (pivot : Fin w)
    (cells : Backend.Cells B bw w × Backend.Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (satisfied : statements.1.Satisfies (Backend.logical cells.1) ∧
      statements.2.Satisfies (Backend.logical cells.2))
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : MaskTape binary prime (bw := bw) (nw := nw) (s := s)) :
    realResponses binary prime Q cells statements coins tape =
      simResponses binary prime Q pivot statements coins
        (Backend.jointCoupling binary prime Q pivot cells statements satisfied coins tape) := by
  exact (congrArg (fun view => (view.1.2,view.2.2))
    (Backend.jointCoupling_view binary prime Q pivot cells statements satisfied coins tape)).symm

section Hiding
variable {Index Nonce D Enc Front Observed : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [DecidableEq Observed]
variable (C : Codec (Index × Nonce) (Leaf (B := B) (N := N) (bw := bw) (nw := nw)) D Enc)
variable (T queries : ℕ) (Q : QuerySet n r) (pivot : Fin w) (index : Fin n → Index)
variable (front : (Fin T → D) → Front)
variable (cells : (Fin T → D) → Backend.Cells B bw w × Backend.Cells N nw w)
variable (statements : (Fin T → D) → ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
variable (coins : (Fin T → D) → Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)

/-- Full backend/Merkle privacy at common lazy labels.  The statement may
be chosen from the frontend transcript and the common commitment root; only
ordinary affine satisfaction is required of the real logical cells.  The
simulated columns and responses have no logical-cell argument. -/
theorem joint_hiding
    (injective : C.Inj) (positive : 0 < n) (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T)
    (satisfied : ∀ labels,
      (statements labels).1.Satisfies (Backend.logical (cells labels).1) ∧
      (statements labels).2.Satisfies (Backend.logical (cells labels).2))
    (observer : (Front × Responses (B := B) (N := N) (r := r) (w := w) (s := s)) →
      ({i : Fin n // i ∈ Q.coordinates} → Leaf (B := B) (N := N) (bw := bw) (nw := nw)) →
      (Fin T → D) → OpeningView n Q.coordinates Nonce D →
      RandomOracle.Tree Enc D Observed queries) :
    StatClose (MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-Q.coordinates.card) queries)
      (CommonLabels.compiled C n T queries Q.coordinates index
        (fun labels tape => realColumns binary prime (cells labels) tape)
        (fun labels tape => (front labels,
          realResponses binary prime Q (cells labels) (statements labels) (coins labels) tape)) observer)
      (CommonLabels.compiled C n T queries Q.coordinates index
        (fun _ tape => simColumns binary prime tape)
        (fun labels tape => (front labels,
          simResponses binary prime Q pivot (statements labels) (coins labels) tape)) observer) := by
  apply CommonLabels.compiled_hiding C n T queries Q.coordinates index injective positive fits fitsAll
    _ _ _ _ (fun labels => Backend.jointCoupling binary prime Q pivot (cells labels)
      (statements labels) (satisfied labels) (coins labels))
  · intro labels tape i hi
    exact columns_coupling binary prime Q pivot (cells labels) (statements labels)
      (satisfied labels) (coins labels) tape i hi
  · intro labels tape
    exact congrArg (fun response => (front labels,response))
      (responses_coupling binary prime Q pivot (cells labels) (statements labels)
        (satisfied labels) (coins labels) tape)

end Hiding
end LfzkV2.Current.ZeroKnowledge.MerkleBackend
