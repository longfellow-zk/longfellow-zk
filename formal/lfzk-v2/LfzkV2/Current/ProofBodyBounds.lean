import LfzkV2.Current.CanonicalPrefix

/-! Static sizes of the proof body's components. Every body has the same
scalar counts; only the actual Merkle frontier length varies. The public
bound `bodyBound` covers every body (`TaggedFormat.body_length_le`), so the
final bytes operation fits without a per-proof capacity certificate or
padding. -/
namespace LfzkV2.Current.ProofBodyBounds
open Finset

open PrefixCodec (vector_length)

private theorem dependent_length (count : ℕ) (A : Fin count → Type)
    (codecs : ∀ i, PrefixCodec (A i)) (width : Fin count → ℕ)
    (hlen : ∀ i value, ((codecs i).encode value).length = width i)
    (value : ∀ i, A i) :
    ((PrefixCodec.dependentVector count A codecs).encode value).length = ∑ i, width i := by
  induction count with
  | zero => simp only [PrefixCodec.dependentVector,PrefixCodec.equiv,PrefixCodec.unit,
      List.length_nil,Finset.univ_eq_empty,Finset.sum_empty]
  | succ count ih =>
      change ((codecs 0).encode (value 0) ++
        (PrefixCodec.dependentVector count (fun i => A i.succ) (fun i => codecs i.succ)).encode
          (fun i => value i.succ)).length = ∑ i, width i
      rw [List.length_append,hlen,ih (fun i => A i.succ) (fun i => codecs i.succ)
        (fun i => width i.succ) (fun i => hlen i.succ)]
      exact (Fin.sum_univ_succ width).symm

def frontendCells (shape : Frontend) : ℕ := ∑ i : Fin shape.stages.length, (2*(shape.stages.get i).rounds+3)

theorem layer_length {F : Type} (field : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (field.encode value).length = width) (rounds : ℕ)
    (value : LayerPayload F rounds) :
    ((ProofBodyCodec.layer field rounds).encode value).length = (2*rounds+3)*width := by
  change ((PrefixCodec.vector (field.pair field) rounds).encode value.coefficients ++
    (field.encode value.cross ++ (field.encode value.claims.1 ++ field.encode value.claims.2))).length = _
  rw [List.length_append,vector_length (field.pair field) (2*width) (by
    intro pair
    change (field.encode pair.1 ++ field.encode pair.2).length = _
    rw [List.length_append,hlen,hlen]
    omega)]
  simp only [List.length_append,hlen]
  ring

theorem frontend_length {F : Type} (field : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (field.encode value).length = width) (shape : Frontend)
    (value : FrontendPayload F shape) :
    ((ProofBodyCodec.frontend field shape).encode value).length = frontendCells shape*width := by
  rw [ProofBodyCodec.frontend,dependent_length _ _ _
    (fun i => (2*(shape.stages.get i).rounds+3)*width)
    (fun i => layer_length field width hlen (shape.stages.get i).rounds)]
  unfold frontendCells
  exact (Finset.sum_mul Finset.univ (fun i : Fin shape.stages.length => 2*(shape.stages.get i).rounds+3) width).symm

private theorem cast_length {A B : Type} (h : A = B) (codec : PrefixCodec A) (width : ℕ)
    (hlen : ∀ value, (codec.encode value).length = width) (value : B) :
    ((cast (congrArg PrefixCodec h) codec).encode value).length = width := by
  cases h
  exact hlen value

theorem packing_length {F : Type} (field : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (field.encode value).length = width) (degree : ℕ)
    (value : PackingPayload F degree) :
    ((ProofBodyCodec.packing field degree).encode value).length =
      if degree = 1 then 0 else (degree+1)*width := by
  by_cases h : degree = 1
  · subst degree
    change 0 = 0
    rfl
  · simp only [ProofBodyCodec.packing,h,↓reduceDIte,↓reduceIte]
    exact cast_length (by simp only [PackingPayload,h,↓reduceIte])
      ((PrefixCodec.vector field degree).pair field) ((degree+1)*width) (by
        intro pair
        change ((PrefixCodec.vector field degree).encode pair.1 ++ field.encode pair.2).length = _
        rw [List.length_append,vector_length field width hlen,hlen]
        ring) value

theorem response_length {F : Type} (field : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (field.encode value).length = width) (g : Geometry) (value : Response g F) :
    ((ProofBodyCodec.response field g).encode value).length = (3*g.rowDimension+g.maskingDegree)*width := by
  change ((PrefixCodec.vector field (g.rowDimension+g.maskingDegree)).encode value.h ++
    (PrefixCodec.vector field (2*g.rowDimension)).encode value.z).length = _
  rw [List.length_append,vector_length field width hlen,vector_length field width hlen]
  ring

theorem digest_length (value : Digest) : (ProofBodyCodec.digest.encode value).length = 32 :=
  by simpa only [ProofBodyCodec.digest,Nat.mul_one] using vector_length PrefixCodec.byte 1
      (fun value => by simp only [PrefixCodec.byte_encode,List.length_singleton]) 32 value

theorem nonce_length (value : MerkleNonce) :
    (ProofBodyCodec.nonce.encode value).length = merkleNonceBytes :=
  by simpa only [ProofBodyCodec.nonce,Nat.mul_one] using vector_length PrefixCodec.byte 1
      (fun value => by simp only [PrefixCodec.byte_encode,List.length_singleton]) merkleNonceBytes value

/-- Maximum over the public frontier capacity, with all fixed scalar and
advice sizes included. No part of this bound is serialized. The constant 172
is the magic (4), the root (32), both fingerprint responses (2*16+2*32), mu
(32) and the frontier's u64 count (8). -/
def bodyBound {fields : Fields} {Advice : Type} (repr : ProofBodyCodec.Representations fields Advice)
    (g : Geometry) : ℕ :=
  172+repr.adviceWidth + frontendCells g.binary*16 +
    (if g.packingDegree = 1 then 0 else (g.packingDegree+1)*16) +
    frontendCells g.prime*32 +
    (3*g.rowDimension+g.maskingDegree+(g.dataRows .binary+3)*g.openings)*16 +
    (3*g.rowDimension+g.maskingDegree+(g.dataRows .prime+3)*g.openings)*32 +
    merkleNonceBytes*g.openings+32*OpeningBody.frontierCapacity g

end LfzkV2.Current.ProofBodyBounds
