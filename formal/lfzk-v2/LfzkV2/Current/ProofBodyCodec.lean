import LfzkV2.Current.ByteCodecs
import LfzkV2.Current.BodyScalars
import LfzkV2.Current.OpeningBody

/-! The component codecs of the proof body: sumcheck layers and frontends,
packing, Polygero responses, digests and nonces, each with its public
counts and no length word. `TaggedFormat.body` assembles them in the
runtime's physical order. -/
namespace LfzkV2.Current.ProofBodyCodec
open TranscriptV2.Framing (FieldCodec)
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice F : Type}

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

def digest : PrefixCodec Digest := PrefixCodec.vector PrefixCodec.byte 32

def nonce : PrefixCodec MerkleNonce := PrefixCodec.vector PrefixCodec.byte merkleNonceBytes

/-- Proof-body marker bytes, distinct from numbered-strand domain tags. -/
def mda7 : Bytes := [77,68,65,55]

end LfzkV2.Current.ProofBodyCodec
