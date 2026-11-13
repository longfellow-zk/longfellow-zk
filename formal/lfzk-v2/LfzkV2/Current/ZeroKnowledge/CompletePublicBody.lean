import LfzkV2.Current.OpeningBody
import Merkle.Hiding

/-! Encode a complete body from the public backend view alone: its two
response arrays, ordered opened tuple columns, opened nonces and frontier.
No unopened column, private mask or Merkle oracle is an input. This is the
observer-side encoder used in the backend privacy hybrid. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompletePublicBody
open Merkle Merkle.MH RecursivePolygero LigeroFamily
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type} {k s n t : ℕ}
def fillRows (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (rows : ∀ side, Fin (g.dataRows side+3) → Fin g.openings → fields side)
    (nonce : Fin g.openings → MerkleNonce) (frontier : List Digest)
    (context : Digest) (capacity : frontier.length ≤ OpeningBody.frontierCapacity g) :
    Body g fields Advice (OpeningBody.Authentication g) :=
  { body with
    binaryBackend := ⟨responses.1,rows .binary⟩
    primeBackend := ⟨responses.2,rows .prime⟩
    authentication := {
      context := context
      nonce := nonce
      frontierLength := ⟨frontier.length,Nat.lt_succ_of_le capacity⟩
      frontier := fun i => frontier[i.val]'i.isLt } }

variable (P R : Joint.Participant k s n t)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
variable (hopenings : g.openings = t)

def fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (raw : OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest)
    (context : Digest) (capacity : raw.frontier.length ≤ OpeningBody.frontierCapacity g) :
    Body g fields Advice (OpeningBody.Authentication g) :=
  fillRows body responses (fun side => match side with
    | .binary => fun row query =>
      (OpeningBody.participantEquiv .binary P binary hB).symm
        ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings query))).1) row
    | .prime => fun row query =>
      (OpeningBody.participantEquiv .prime R prime hN).symm
        ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings query))).2) row)
    (fun query => raw.nonce (Fin.cast hopenings query)) raw.frontier context capacity

def ordered {Column : Type} (indices : Fin t ↪ Fin n)
    (columns : ↥(OrderedOpening.query indices).coordinates → Column)
    (opening : Opening n (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    OrderedOpening.Raw t MerkleNonce Column Digest where
  values i := columns (OrderedOpening.order indices i)
  nonce i := opening.nonce (OrderedOpening.order indices i)
  frontier := List.ofFn fun i : Fin (Heap.frontierList n (OrderedOpening.query indices).coordinates).length =>
    opening.frontierValue ⟨(Heap.frontierList n (OrderedOpening.query indices).coordinates)[i.val]'i.isLt,
      Heap.mem_frontierList.mp (List.getElem_mem i.isLt)⟩

theorem ordered_frontier_bound {Column : Type} (indices : Fin t ↪ Fin n)
    (columns : ↥(OrderedOpening.query indices).coordinates → Column)
    (opening : Opening n (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    (ordered indices columns opening).frontier.length ≤ t*(Heap.heapDepth n+1) := by
  have bound := Heap.frontier_card_le n (OrderedOpening.query indices).coordinates
  simpa only [ordered,List.length_ofFn,Heap.frontierList_length,QuerySet.card_coordinates] using bound

end LfzkV2.Current.ZeroKnowledge.CompletePublicBody
