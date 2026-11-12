import LfzkV2.Current.WireBlockRequest
import LfzkV2.Current.QueryRuntime

/-! The actual opening block contains only the complete binary H/Z and
prime H/Z slices. Its bytes and parsed cache are constructed from that same
response pair, independently of requests, other body fields or metadata. -/
noncomputable section
namespace LfzkV2.Current.WireOpening
open WireBlocks
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Auth : Type}
variable (shape : WireBlocks.Shape g fields)

abbrev Responses (g : Geometry) (fields : Fields) :=
  Response g (fields .binary) × Response g (fields .prime)

theorem startAt_opening : WireBlocks.startAt g g.openingIndex = .none := by
  have hlength := g.roles_length
  have hlast := g.openingIndex_last
  have hp : g.openingIndex.val ≠ g.primeStart := by
    dsimp only [Geometry.primeStart]
    omega
  have hb : g.openingIndex.val ≠ g.binaryStart := by
    dsimp only [Geometry.binaryStart]
    omega
  simp only [WireBlocks.startAt,if_neg hp,if_neg hb]

private def noneValue (start : WireBlocks.Start) (h : start = .none) :
    WireBlocks.StartData (Advice := Advice) shape start := by
  cases h
  exact ()

private def responseValue (role : Role) (h : role = .opening) (responses : Responses g fields) :
    WireBlocks.RoleData shape role := by
  cases h
  exact responses

/-- The public opening index supplies both dependent index equalities.
No full proof body or arbitrary metadata is an input to this constructor. -/
def openingData (responses : Responses g fields) :
    WireBlocks.Data (Advice := Advice) shape g.openingIndex :=
  (noneValue shape _ startAt_opening,responseValue shape _ g.get_openingIndex responses)

private theorem noneValue_cache (start : WireBlocks.Start) (h : start = .none) :
    WireBlocks.startCache (Advice := Advice) shape start (noneValue shape start h) = {} := by
  cases h
  rfl

private theorem responseValue_cache (role : Role) (h : role = .opening) (responses : Responses g fields) :
    WireBlocks.roleCache (Advice := Advice) shape role (responseValue shape role h responses) =
      { responses := some responses } := by
  cases h
  rfl

theorem openingData_cache (responses : Responses g fields) :
    WireBlocks.cache (Advice := Advice) shape g.openingIndex (openingData shape responses) =
      { responses := some responses } := by
  unfold WireBlocks.cache openingData
  rw [noneValue_cache,responseValue_cache]

variable (repr : ProofBodyCodec.Representations fields Advice)

private theorem noneValue_encode (start : WireBlocks.Start) (h : start = .none) :
    (WireBlocks.startCodec repr shape start).encode (noneValue shape start h) = [] := by
  cases h
  rfl

private theorem responseValue_encode (role : Role) (h : role = .opening) (responses : Responses g fields) :
    (WireBlocks.roleCodec repr shape role).encode (responseValue shape role h responses) =
      ((WireBlocks.response repr .binary).pair (WireBlocks.response repr .prime)).encode responses := by
  cases h
  rfl

/-- Four existing slice operations, in the participant traversal order.
The values are the transmitted evaluations, before backend interpolation. -/
theorem openingData_encode (responses : Responses g fields) :
    (WireBlocks.codec repr shape g.openingIndex).encode (openingData shape responses) =
      (WireBlocks.slice repr.binary (g.rowDimension+g.maskingDegree)).encode responses.1.h ++
      (WireBlocks.slice repr.binary (2*g.rowDimension)).encode responses.1.z ++
      (WireBlocks.slice repr.prime (g.rowDimension+g.maskingDegree)).encode responses.2.h ++
      (WireBlocks.slice repr.prime (2*g.rowDimension)).encode responses.2.z := by
  change (WireBlocks.startCodec repr shape _).encode (noneValue shape _ _) ++
    (WireBlocks.roleCodec repr shape _).encode (responseValue shape _ _ responses) = _
  rw [noneValue_encode,responseValue_encode,List.nil_append]
  simp only [WireBlocks.response,WireBlocks.fieldCodec,PrefixCodec.equiv,PrefixCodec.pair,Equiv.coe_fn_symm_mk,List.append_assoc]

private theorem startFromBody_none (body : Body g fields Advice Auth)
    (start : WireBlocks.Start) (h : start = .none) (metadata : WireBlocks.StartMetadata shape start) :
    WireBlocks.startFromBody shape body start metadata = noneValue shape start h := by
  cases h
  rfl

private theorem roleFromBody_opening (body : Body g fields Advice Auth)
    (role : Role) (h : role = .opening) (valid : WireBlocks.ValidRole g role)
    (metadata : WireBlocks.RoleMetadata shape role) :
    WireBlocks.roleFromBody shape body role valid metadata = responseValue shape role h
      (body.binaryBackend.response,body.primeBackend.response) := by
  cases h
  rfl

/-- Requests and metadata cannot affect the opening bytes: all four arrays
are filled from the same complete body responses by the packet constructor. -/
theorem fromRequest_opening (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime) (body : Body g fields Advice Auth)
    (metadata : WireBlocks.Metadata shape g.openingIndex) :
    WireBlocks.fromRequest shape binaryInputs primeInputs g.openingIndex body metadata =
      openingData shape (body.binaryBackend.response,body.primeBackend.response) := by
  apply Prod.ext
  · exact startFromBody_none shape body _ startAt_opening _
  · exact roleFromBody_opening shape body _ g.get_openingIndex _ _

section Bounded
variable (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

/-- This capacity bounds whole blocks and can exceed u64. The opening's
individual slice counts retain the public operation bounds in `Shape`. -/
def openingBase (responses : Responses g fields) :
    BoundedBytes (QueryRuntime.Runtime.capacity repr shape setup publicCount) :=
  ⟨(WireBlocks.codec repr shape g.openingIndex).encode (openingData shape responses),
    (WireBlocks.encode_length_le shape repr g.openingIndex _).trans (le_max_right _ _)⟩

def openingWire (responses : Responses g fields) :
    QueryRuntime.Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
      (ProtocolWrites.Fresh g fields Advice) :=
  (openingBase shape repr setup publicCount responses,{ responses := some responses })

@[simp] theorem openingBase_bytes (responses : Responses g fields) :
    (openingBase shape repr setup publicCount responses).bytes =
      (WireBlocks.codec repr shape g.openingIndex).encode (openingData shape responses) := rfl

theorem ordinary_opening (responses : Responses g fields) :
    (QueryRuntime.Runtime.ordinary repr shape setup publicCount g.openingIndex).block (openingData shape responses) =
      openingWire shape repr setup publicCount responses := by
  apply Prod.ext
  · apply BoundedBytes.ext
    rfl
  · exact openingData_cache shape responses

theorem ordinary_fromRequest_opening (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime) (body : Body g fields Advice Auth)
    (metadata : WireBlocks.Metadata shape g.openingIndex) :
    (QueryRuntime.Runtime.ordinary repr shape setup publicCount g.openingIndex).block
        (WireBlocks.fromRequest shape binaryInputs primeInputs g.openingIndex body metadata) =
      openingWire shape repr setup publicCount (body.binaryBackend.response,body.primeBackend.response) := by
  rw [fromRequest_opening]
  exact ordinary_opening shape repr setup publicCount _

end Bounded
end LfzkV2.Current.WireOpening
