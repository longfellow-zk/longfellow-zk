import LfzkV2.Linear.Backend
import LfzkV2.Current.Selection

/-! The two fingerprint equations at the actual affine-statement boundary.
The projection reads the original cells and the two dedicated mask cells
from the recovered ordinary tableau. Internal backend rows are not selected
as frontend witness cells. -/
noncomputable section
namespace LfzkV2.Current.FingerprintRows
open SumcheckV2 WitnessSelection RecursivePolygero
open scoped Classical

variable {F Slot Index : Type} [Field F] [Fintype Index]

def project (data : Index → Slot) (mask : Fin 2 → Slot) (read : Slot → F) : Candidate F Index :=
  (read ∘ data, (read (mask 0), read (mask 1)))

/-- A complete frontend layout distinguishes its selected cells from the two
dedicated fingerprint masks. Backend padding lies outside this slot type. -/
def realize (layout : (Index ⊕ Fin 2) ≃ Slot) (candidate : Candidate F Index) : Slot → F :=
  fun slot => match layout.symm slot with
    | .inl i => candidate.1 i
    | .inr j => if j = 0 then candidate.2.1 else candidate.2.2

omit [Field F] [Fintype Index] in
theorem realize_project (layout : (Index ⊕ Fin 2) ≃ Slot) (read : Slot → F) :
    realize layout (project (fun i => layout (.inl i)) (fun j => layout (.inr j)) read) = read := by
  funext slot
  obtain ⟨cell,rfl⟩ := layout.surjective slot
  cases cell with
  | inl i => simp [realize, project]
  | inr j => fin_cases j <;> simp [realize, project]

omit [Fintype Index] in
/-- Every frontend row can be evaluated on the selected projection. This is
why selecting only private inputs, while omitting pads or terminal cells,
would not suffice for the later fixed-witness sumcheck argument. -/
theorem rows_realized (layout : (Index ⊕ Fin 2) ≃ Slot)
    (rows : List (LinearRow Slot F)) (read : Slot → F) :
    RowsHold rows (realize layout
      (project (fun i => layout (.inl i)) (fun j => layout (.inr j)) read)) ↔ RowsHold rows read := by
  rw [realize_project]

def row (data : Index → Slot) (mask : Slot) (coefficients : Index → F) (target : F) :
    LinearRow Slot F where
  constant := -target
  terms := [(mask,1)] ++ (Finset.univ.toList.map fun i => (data i, coefficients i))

def rows (data : Index → Slot) (mask : Fin 2 → Slot) (coins : Coins F Index) (target : F × F) :
    List (LinearRow Slot F) :=
  [row data (mask 0) coins.1 target.1, row data (mask 1) coins.2 target.2]

theorem row_eval (data : Index → Slot) (mask : Slot) (coefficients : Index → F) (target : F)
    (read : Slot → F) :
    (row data mask coefficients target).eval read = WitnessSelection.dot coefficients (read ∘ data) + read mask - target := by
  simp [row, PadExpression.eval, WitnessSelection.dot, Function.comp_def]
  ring

theorem rows_iff (data : Index → Slot) (mask : Fin 2 → Slot) (coins : Coins F Index) (target : F × F)
    (read : Slot → F) :
    RowsHold (rows data mask coins target) read ↔
      fingerprint coins (project data mask read) = target := by
  rw [← affine_rows_iff]
  simp [RowsHold, rows, row_eval, project]

variable [Fintype F] [DecidableEq F]

noncomputable def view (I : Instance F) (primary : Slot → Fin I.nw × Fin I.q)
    (data : Index → Slot) (mask : Fin 2 → Slot) (g : (Counting.tupleCounts I).Index) : Candidate F Index :=
  project data mask (Backend.read ((Counting.tupleCounts I).witness g) ∘ Backend.linearAddress primary)

def statement (I : Instance F) (front : List (LinearRow Slot F))
    (primary : Slot → Fin I.nw × Fin I.q) (data : Index → Slot) (mask : Fin 2 → Slot)
    (coins : Coins F Index) (target : F × F)
    (eqns : I.Equations ≃ Fin (front ++ rows data mask coins target).length) : I.layer.Statement :=
  Backend.statement (fun e => Backend.remap
    ((front ++ rows data mask coins target).get (eqns e)) (Backend.linearAddress primary))

/-- Decoding the complete statement supplies both the frontend rows and the
fingerprint match. The affine equations are obtained from the real backend
decoder, rather than assumed as a separate authentication premise. -/
theorem decoded_view (I : Instance F) (front : List (LinearRow Slot F))
    (primary : Slot → Fin I.nw × Fin I.q) (data : Index → Slot) (mask : Fin 2 → Slot)
    (coins : Coins F Index) (target : F × F)
    (eqns : I.Equations ≃ Fin (front ++ rows data mask coins target).length)
    (W : I.layer.Oracle) (c : I.layer.Coin) (a : I.layer.Payload)
    (g : (Counting.tupleCounts I).Index)
    (hdecode : scanRecoverAt I (statement I front primary data mask coins target eqns) W c a = some g) :
    RowsHold front
      (Backend.read ((Counting.tupleCounts I).witness g) ∘ Backend.linearAddress primary) ∧
      fingerprint coins (view I primary data mask g) = target := by
  have h := Linear.Backend.decoded_rows I (front ++ rows data mask coins target) primary eqns W c a g hdecode
  refine ⟨?_, (rows_iff data mask coins target _).mp ?_⟩
  · intro r hr
    exact h r (List.mem_append_left _ hr)
  · intro r hr
    exact h r (List.mem_append_right _ hr)

end LfzkV2.Current.FingerprintRows
