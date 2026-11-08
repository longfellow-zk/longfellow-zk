import LfzkV2.Current.ZeroKnowledge.CompleteBody
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
variable (P R : Joint.Participant k s n t)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
variable (hopenings : g.openings = t)

def fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (raw : OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest)
    (context : Digest) (capacity : raw.frontier.length ≤ OpeningBody.frontierCapacity g) :
    Body g fields Advice (OpeningBody.Authentication g) :=
  { body with
    binaryBackend := ⟨responses.1,fun row query =>
      (CompleteBody.participantEquiv .binary P binary hB).symm
        ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings query))).1) row⟩
    primeBackend := ⟨responses.2,fun row query =>
      (CompleteBody.participantEquiv .prime R prime hN).symm
        ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings query))).2) row⟩
    authentication := {
      context := context
      nonce := fun query => raw.nonce (Fin.cast hopenings query)
      frontierLength := ⟨raw.frontier.length,by omega⟩
      frontier := fun i => raw.frontier[i.val] } }

theorem fill_honest {Enc : Type}
    (scheme : Scheme (Fin n × MerkleNonce) (Joint.Pair.family P R).Leaf Digest Enc)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → MerkleNonce)
    (columns : Fin n → (Joint.Pair.family P R).Leaf)
    (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (context : Digest)
    (capacity : (CompleteBody.frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g) :
    fill P R binary prime hB hN hopenings body responses
        (CompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns) context capacity =
      CompleteBody.fill P R binary prime hB hN hopenings scheme indices nonces columns
        body responses context capacity := rfl

def raw (indices : Fin t ↪ Fin n)
    (columns : ↥(OrderedOpening.query indices).coordinates → (Joint.Pair.family P R).Leaf)
    (opening : OpeningView n (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest where
  values i := columns (OrderedOpening.order indices i)
  nonce i := opening.proof.nonce (OrderedOpening.order indices i)
  frontier := List.ofFn fun i : Fin (Heap.frontierList n (OrderedOpening.query indices).coordinates).length =>
    opening.proof.frontierValue ⟨(Heap.frontierList n (OrderedOpening.query indices).coordinates)[i.val]'i.isLt,
      Heap.mem_frontierList.mp (List.getElem_mem i.isLt)⟩

theorem raw_frontier_bound (indices : Fin t ↪ Fin n)
    (columns : ↥(OrderedOpening.query indices).coordinates → (Joint.Pair.family P R).Leaf)
    (opening : OpeningView n (OrderedOpening.query indices).coordinates MerkleNonce Digest) :
    (raw P R indices columns opening).frontier.length ≤ t*(Heap.heapDepth n+1) := by
  have bound := Heap.frontier_card_le n (OrderedOpening.query indices).coordinates
  simpa only [raw,List.length_ofFn,Heap.frontierList_length,QuerySet.card_coordinates] using bound

theorem raw_honest {Enc : Type}
    (scheme : Scheme (Fin n × MerkleNonce) (Joint.Pair.family P R).Leaf Digest Enc)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → MerkleNonce)
    (columns : Fin n → (Joint.Pair.family P R).Leaf) :
    raw P R indices (fun i => columns i.val)
        ⟨root scheme n (fun i => (i,nonces i)) columns,
          { nonce := fun i => nonces i.val
            frontierValue := fun vertex => commitLabels scheme n (fun i => (i,nonces i)) columns vertex.val }⟩ =
      CompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns := by
  have frontier :
      List.ofFn (fun i : Fin (Heap.frontierList n (OrderedOpening.query indices).coordinates).length =>
        commitLabels scheme n (fun j => (j,nonces j)) columns
          ((Heap.frontierList n (OrderedOpening.query indices).coordinates)[i.val]'i.isLt)) =
      (Heap.frontierList n (OrderedOpening.query indices).coordinates).map
        (commitLabels scheme n (fun j => (j,nonces j)) columns) := by
    exact List.ofFn_getElem_eq_map _ _
  unfold raw CompleteOpening.raw
  simp only [OrderedOpening.order_val]
  rw [frontier]

/-- Combining the public opening encoder with the honest opening gives
the identical complete body, including its exact unpadded frontier. -/
theorem fill_raw_honest {Enc : Type}
    (scheme : Scheme (Fin n × MerkleNonce) (Joint.Pair.family P R).Leaf Digest Enc)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → MerkleNonce)
    (columns : Fin n → (Joint.Pair.family P R).Leaf)
    (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (context : Digest)
    (capacity : (raw P R indices (fun i => columns i.val)
        ⟨root scheme n (fun i => (i,nonces i)) columns,
          { nonce := fun i => nonces i.val
            frontierValue := fun vertex => commitLabels scheme n (fun i => (i,nonces i)) columns vertex.val }⟩).frontier.length ≤
      OpeningBody.frontierCapacity g) :
    fill P R binary prime hB hN hopenings body responses
        (raw P R indices (fun i => columns i.val)
          ⟨root scheme n (fun i => (i,nonces i)) columns,
            { nonce := fun i => nonces i.val
              frontierValue := fun vertex => commitLabels scheme n (fun i => (i,nonces i)) columns vertex.val }⟩)
        context capacity =
      CompleteBody.fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context
        (by simpa only [CompleteBody.frontier,raw_honest] using capacity) := by
  simpa only [raw_honest] using
    (fill_honest P R binary prime hB hN hopenings scheme indices nonces columns body responses context
      (by simpa only [CompleteBody.frontier,raw_honest] using capacity))

end LfzkV2.Current.ZeroKnowledge.CompletePublicBody
