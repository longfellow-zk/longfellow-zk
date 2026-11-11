import LfzkV2.Current.Opening
import LfzkV2.Current.ZeroKnowledge.IndexedCompleteness

/-! Honest authentication in the actual sampled-order wire layout. The
query positions come from the opening oracle; only nonce and frontier values
are serialized. Reconstructing them checks the original commitment root. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.IndexedCompleteOpening

open Merkle Merkle.Indexed Merkle.RandomOracle LigeroFamily
open Merkle.MH (OpeningClaim)
open scoped Classical

variable {Salt Nonce Leaf D Enc : Type} [Inhabited D] [Inhabited Leaf]
variable {n t : ℕ}

def raw (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OrderedOpening.Raw t Nonce Leaf D where
  values i := columns (indices i)
  nonce i := nonces (indices i)
  frontier := (Heap.frontierList n (OrderedOpening.query indices).coordinates).map
    (commitLabels scheme n (fun i => bind i (nonces i)) columns)

omit [Inhabited Leaf] in
theorem raw_frontier_bound (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    (raw scheme bind indices nonces columns).frontier.length ≤ t*(Heap.heapDepth n+1) := by
  have bound := Heap.frontier_card_le n (OrderedOpening.query indices).coordinates
  simpa only [raw,List.length_map,Heap.frontierList_length,QuerySet.card_coordinates] using bound

def claim (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OpeningClaim n Salt Leaf D where
  I := (OrderedOpening.query indices).coordinates
  a i := if i ∈ (OrderedOpening.query indices).coordinates then columns i else default
  pf := openCore scheme n (OrderedOpening.query indices).coordinates (fun i => bind i (nonces i)) columns

theorem claim_value (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf)
    (i : Fin n) (inside : i ∈ (OrderedOpening.query indices).coordinates) :
    (claim scheme bind indices nonces columns).a i = columns i := if_pos inside

theorem decode_raw (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OrderedOpening.decode bind indices (raw scheme bind indices nonces columns) =
      some (claim scheme bind indices nonces columns) := by
  have length : (raw scheme bind indices nonces columns).frontier.length =
      (Heap.frontierList n (OrderedOpening.query indices).coordinates).length := List.length_map ..
  unfold OrderedOpening.decode
  rw [dif_pos length]
  congr 1
  apply congrArg₂ (OpeningClaim.mk (OrderedOpening.query indices).coordinates)
  · funext i
    by_cases inside : i ∈ (OrderedOpening.query indices).coordinates
    · simp only [raw,dif_pos inside,if_pos inside]
      congr 1
      exact congrArg Subtype.val ((OrderedOpening.order indices).apply_symm_apply ⟨i,inside⟩)
    · simp only [dif_neg inside,if_neg inside]
  · apply congrArg₂ Merkle.MH.Opening.mk
    · funext i
      change bind i.val (nonces (indices ((OrderedOpening.order indices).symm i))) = bind i.val (nonces i.val)
      exact congrArg (fun j => bind i.val (nonces j))
        (congrArg Subtype.val ((OrderedOpening.order indices).apply_symm_apply i))
    · funext vertex
      change ((Heap.frontierList n (OrderedOpening.query indices).coordinates).map
          (commitLabels scheme n (fun i => bind i (nonces i)) columns))[(Heap.frontierList n
            (OrderedOpening.query indices).coordinates).idxOf vertex.val]'(by
              rw [List.length_map]
              exact List.idxOf_lt_length_of_mem (Heap.mem_frontierList.mpr vertex.property)) = _
      rw [List.getElem_map,List.getElem_idxOf]


end LfzkV2.Current.ZeroKnowledge.IndexedCompleteOpening
