import LfzkV2.Current.ByteCodecs
import LfzkV2.Current.OpeningBody

/-! Canonical MDA6/JPG2 body encoding, in the runtime's physical order.
The complete body includes terminal authentication. Its final seal is a
separate 32-byte value and is not encoded by this module. -/
namespace LfzkV2.Current.ProofBodyCodec
open TranscriptV2.Framing (FieldCodec)
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice F : Type}

/-- Raw scalar and fixed-size canonical advice representations. Scalar
bytes carry no transcript-operation tags inside the proof body. -/
structure Representations (fields : Fields) (Advice : Type) where
  binary : FieldCodec (fields .binary)
  prime : FieldCodec (fields .prime)
  binaryWidth : binary.width = 16
  primeWidth : prime.width = 32
  advice : PrefixCodec Advice
  adviceWidth : ℕ
  adviceLength : ∀ value, (advice.encode value).length = adviceWidth

private def layerData (rounds : ℕ) :
    ((Fin rounds → F × F) × (F × (F × F))) ≃ LayerPayload F rounds where
  toFun value := ⟨value.1,value.2.1,value.2.2⟩
  invFun value := (value.coefficients,value.cross,value.claims)
  left_inv _ := rfl
  right_inv value := by cases value; rfl

/-- Each layer writes its two round coefficients, then its cross
coefficient, then its two terminal claims. -/
def layer (field : PrefixCodec F) (rounds : ℕ) : PrefixCodec (LayerPayload F rounds) :=
  ((PrefixCodec.vector (field.pair field) rounds).pair (field.pair (field.pair field))).equiv
    (layerData rounds)

/-- Public layer geometry supplies every count; no layer lengths are
serialized. Quad fragments add no payloads of their own. -/
def frontend (field : PrefixCodec F) (shape : Frontend) : PrefixCodec (FrontendPayload F shape) :=
  PrefixCodec.dependentVector shape.stages.length
    (fun i => LayerPayload F (shape.stages.get i).rounds)
    (fun i => layer field (shape.stages.get i).rounds)

/-- Degree-one packing contributes no bytes. Higher degrees write U in
coordinate order followed by the single A response. -/
def packing (field : PrefixCodec F) (degree : ℕ) : PrefixCodec (PackingPayload F degree) :=
  if h : degree = 1 then by simpa only [PackingPayload,if_pos h] using PrefixCodec.unit
  else by simpa only [PackingPayload,if_neg h] using (PrefixCodec.vector field degree).pair field

private def responseData (g : Geometry) :
    ((Fin (g.rowDimension+g.maskingDegree) → F) × (Fin (2*g.rowDimension) → F)) ≃ Response g F where
  toFun value := ⟨value.1,value.2⟩
  invFun value := (value.h,value.z)
  left_inv _ := rfl
  right_inv value := by cases value; rfl

/-- Complete H precedes complete Z. These are wire evaluation vectors, not
padded tables or per-fragment responses. -/
def response (field : PrefixCodec F) (g : Geometry) : PrefixCodec (Response g F) :=
  ((PrefixCodec.vector field (g.rowDimension+g.maskingDegree)).pair
    (PrefixCodec.vector field (2*g.rowDimension))).equiv (responseData g)

private def fieldData (g : Geometry) (fields : Fields) (side : Side) :
    (Response g (fields side) × (Fin (g.dataRows side+3) → Fin g.openings → fields side)) ≃
      FieldBody g fields side where
  toFun value := ⟨value.1,value.2⟩
  invFun value := (value.response,value.rows)
  left_inv _ := rfl
  right_inv value := by cases value; rfl

/-- Opened values are row-major, with the sampled column order retained
inside every row. Both the writer and reader use the public row count. -/
def fieldBody (side : Side) (field : PrefixCodec (fields side)) (g : Geometry) :
    PrefixCodec (FieldBody g fields side) :=
  ((response field g).pair (PrefixCodec.vector (PrefixCodec.vector field g.openings)
    (g.dataRows side+3))).equiv (fieldData g fields side)

def digest : PrefixCodec Digest := PrefixCodec.vector PrefixCodec.byte 32

def nonce : PrefixCodec MerkleNonce := PrefixCodec.vector PrefixCodec.byte merkleNonceBytes

abbrev Frontier (g : Geometry) :=
  (length : Fin (OpeningBody.frontierCapacity g+1)) × (Fin length.val → Digest)

private theorem frontierCountFits (g : Geometry) : OpeningBody.frontierCapacity g+1 ≤ 256^4 :=
  (Nat.add_le_add_right (Nat.min_le_left _ _) 1).trans (by decide)

/-- The count is one canonical u32 word followed by exactly that many
32-byte frontier nodes. No padded tail is stored in the logical value. -/
def frontier (g : Geometry) : PrefixCodec (Frontier g) :=
  PrefixCodec.counted 4 (OpeningBody.frontierCapacity g+1) (frontierCountFits g)
    (fun length => Fin length.val → Digest) (fun length => PrefixCodec.vector digest length.val)

private abbrev PrefixData (g : Geometry) (fields : Fields) (Advice : Type) :=
  Digest × Fingerprints fields × fields .prime × Advice × FrontendPayload (fields .binary) g.binary ×
    PackingPayload (fields .binary) g.packingDegree × FrontendPayload (fields .prime) g.prime

private abbrev JointData (g : Geometry) (fields : Fields) :=
  Digest × FieldBody g fields .binary × FieldBody g fields .prime × (Fin g.openings → MerkleNonce) × Frontier g

private def bodyData (g : Geometry) (fields : Fields) (Advice : Type) :
    (PrefixData g fields Advice × JointData g fields) ≃
      Body g fields Advice (OpeningBody.Authentication g) where
  toFun value :=
    let (commitment,fingerprints,mu,advice,binary,packing,prime) := value.1
    let (context,binaryBackend,primeBackend,nonce,path) := value.2
    { commitment := commitment, fingerprints := fingerprints, mu := mu, advice := advice
      binary := binary, prime := prime, packing := packing
      binaryBackend := binaryBackend, primeBackend := primeBackend
      authentication := { context := context, nonce := nonce, frontierLength := path.1, frontier := path.2 } }
  invFun value :=
    ((value.commitment,value.fingerprints,value.mu,value.advice,value.binary,value.packing,value.prime),
      value.authentication.context,value.binaryBackend,value.primeBackend,value.authentication.nonce,
      ⟨value.authentication.frontierLength,value.authentication.frontier⟩)
  left_inv value := by
    rcases value with ⟨⟨root,fingerprints,mu,advice,binary,packing,prime⟩,context,binaryBackend,primeBackend,nonce,⟨length,path⟩⟩
    rfl
  right_inv value := by cases value; rfl

/-- Proof-body marker bytes, distinct from numbered-strand domain tags. -/
def mda6 : Bytes := [77,68,65,54]
def jpg2 : Bytes := [74,80,71,50]

private def initial (repr : Representations fields Advice) (g : Geometry) :
    PrefixCodec (PrefixData g fields Advice) :=
  let b := PrefixCodec.field repr.binary
  let p := PrefixCodec.field repr.prime
  digest.pair (((b.pair b).pair (p.pair p)).pair (p.pair (repr.advice.pair
    ((frontend b g.binary).pair ((packing b g.packingDegree).pair (frontend p g.prime))))))

private def joint (repr : Representations fields Advice) (g : Geometry) :
    PrefixCodec (JointData g fields) :=
  (digest.pair ((fieldBody .binary (PrefixCodec.field repr.binary) g).pair
    ((fieldBody .prime (PrefixCodec.field repr.prime) g).pair
      ((PrefixCodec.vector nonce g.openings).pair (frontier g))))).prefixed jpg2

/-- Root, fingerprint responses, mu, advice, binary frontend and packing,
prime frontend, JPG2/context, binary and prime field bodies, then the one
shared nonce vector and counted frontier. No statement identifier or final
seal is inserted between these existing body fields. -/
def codec (repr : Representations fields Advice) (g : Geometry) :
    PrefixCodec (Body g fields Advice (OpeningBody.Authentication g)) :=
  (((initial repr g).pair (joint repr g)).equiv (bodyData g fields Advice)).prefixed mda6

/-- The visible byte formula fixes the same field and authentication
order as the MDA6/JPG2 writer. The component codecs prove canonical parsing;
no whole-body injectivity or layout certificate is assumed. -/
theorem codec_encode (repr : Representations fields Advice) (g : Geometry)
    (value : Body g fields Advice (OpeningBody.Authentication g)) :
    (codec repr g).encode value =
      mda6 ++ digest.encode value.commitment ++
      repr.binary.encode value.fingerprints.1.1 ++ repr.binary.encode value.fingerprints.1.2 ++
      repr.prime.encode value.fingerprints.2.1 ++ repr.prime.encode value.fingerprints.2.2 ++
      repr.prime.encode value.mu ++ repr.advice.encode value.advice ++
      (frontend (PrefixCodec.field repr.binary) g.binary).encode value.binary ++
      (packing (PrefixCodec.field repr.binary) g.packingDegree).encode value.packing ++
      (frontend (PrefixCodec.field repr.prime) g.prime).encode value.prime ++
      jpg2 ++ digest.encode value.authentication.context ++
      (fieldBody .binary (PrefixCodec.field repr.binary) g).encode value.binaryBackend ++
      (fieldBody .prime (PrefixCodec.field repr.prime) g).encode value.primeBackend ++
      (PrefixCodec.vector nonce g.openings).encode value.authentication.nonce ++
      (frontier g).encode ⟨value.authentication.frontierLength,value.authentication.frontier⟩ := by
  simp only [codec,initial,joint,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,
    PrefixCodec.marker,bodyData,PrefixCodec.field,Equiv.coe_fn_symm_mk,List.append_assoc]

/-- The runtime rejects a joint context different from its public geometry.
The restriction is on decoded data and preserves canonical body bytes. -/
noncomputable def checked (repr : Representations fields Advice) (g : Geometry) (context : Digest) :
    PrefixCodec {body : Body g fields Advice (OpeningBody.Authentication g) //
      body.authentication.context = context} :=
  (codec repr g).restrict (fun body => body.authentication.context = context)

end LfzkV2.Current.ProofBodyCodec
