import LfzkV2.Current.WireBlockBody

/-! The late public request supplies the prime-start public scalars. A
metadata function cannot substitute different values: the constructor writes
the request vector itself, and the complete bytes reader recovers it. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open CanonicalPrefix
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Auth : Type}
variable (shape : Shape g fields)

def setPublic (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime) :
    (start : Start) → StartMetadata shape start → StartMetadata shape start
  | .none, metadata => metadata
  | .prime, metadata => ((metadata.1.1,primeInputs),metadata.2)
  | .binary, metadata => (((metadata.1.1.1,binaryInputs),(metadata.1.2.1,binaryInputs)),metadata.2)

def requestMetadata (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (metadata : Metadata shape i) : Metadata shape i :=
  (setPublic shape binaryInputs primeInputs (startAt g i) metadata.1,metadata.2)

/-- All prover-message fields still come from the complete body. The two
public vectors are assigned directly from the verifier's request. -/
def fromRequest (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    Data (Advice := Advice) shape i :=
  fromBody shape i body (requestMetadata shape binaryInputs primeInputs i metadata)

theorem fromRequest_cache (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    cache shape i (fromRequest shape binaryInputs primeInputs i body metadata) = ProtocolWrites.fresh body i :=
  fromBody_cache shape i body _

variable (repr : ProofBodyCodec.Representations fields Advice)

private theorem readPrimePublic_start (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (body : Body g fields Advice Auth) (start : Start) (h : start = .prime)
    (metadata : StartMetadata shape start) (role : Role) (payload : RoleData shape role) :
    readPrimePublic repr shape role
      (((startCodec repr shape start).pair (roleCodec repr shape role)).encode
        (startFromBody shape body start (setPublic shape binaryInputs primeInputs start metadata),payload)) = some primeInputs := by
  cases h
  exact readPrimePublic_encode repr shape role
    (body.fingerprints,((metadata.1.1,primeInputs),metadata.2)) payload

/-- The requested public vector is recovered from the actual encoded
prime-start block, not from a future public value attached to the key. -/
theorem readPrimePublic_fromRequest (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (hi : i.val = g.primeStart)
    (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    readPrimePublic repr shape (g.roles.get i)
      ((codec repr shape i).encode (fromRequest shape binaryInputs primeInputs i body metadata)) = some primeInputs := by
  exact readPrimePublic_start shape repr binaryInputs primeInputs body (startAt g i) (by simp [startAt,hi])
    metadata.1 (g.roles.get i) (roleFromBody shape body _ (role_valid g i) metadata.2)

def binaryCodec (role : Role) :
    PrefixCodec (BinaryStart fields Advice shape.binaryPublic × RoleData shape role) :=
  (binaryStart repr shape).pair (roleCodec repr shape role)

/-- Read the hash statement's public inputs, checking the entire block
including the masked words, both statements, the schedule and the first
role payload. -/
def readBinaryPublic (role : Role) (bytes : Bytes) :
    Option (Fin shape.binaryPublic → fields .binary) :=
  (readWhole (binaryCodec shape repr role) bytes).map fun value => value.1.2.1.1.2

theorem readBinaryPublic_encode (role : Role) (startData : BinaryStart fields Advice shape.binaryPublic)
    (payload : RoleData shape role) :
    readBinaryPublic shape repr role ((binaryCodec shape repr role).encode (startData,payload)) =
      some startData.2.1.1.2 := by
  simp only [readBinaryPublic,readWhole_encode,Option.map_some]

private theorem readBinaryPublic_start (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (body : Body g fields Advice Auth) (start : Start) (h : start = .binary)
    (metadata : StartMetadata shape start) (role : Role) (payload : RoleData shape role) :
    readBinaryPublic shape repr role
      (((startCodec repr shape start).pair (roleCodec repr shape role)).encode
        (startFromBody shape body start (setPublic shape binaryInputs primeInputs start metadata),payload)) =
      some binaryInputs := by
  cases h
  exact readBinaryPublic_encode shape repr role
    (body.advice,(((metadata.1.1.1,binaryInputs),(metadata.1.2.1,binaryInputs)),metadata.2)) payload

theorem readBinaryPublic_fromRequest (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (hi : i.val = g.binaryStart)
    (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    readBinaryPublic shape repr (g.roles.get i)
      ((codec repr shape i).encode (fromRequest shape binaryInputs primeInputs i body metadata)) =
      some binaryInputs := by
  have hne : g.binaryStart ≠ g.primeStart := by
    dsimp only [Geometry.binaryStart,Geometry.primeStart]
    omega
  exact readBinaryPublic_start shape repr binaryInputs primeInputs body (startAt g i)
    (by simp [startAt,hi,hne]) metadata.1 (g.roles.get i)
    (roleFromBody shape body _ (role_valid g i) metadata.2)

theorem parseCache_fromRequest (binaryInputs : Fin shape.binaryPublic → fields .binary)
    (primeInputs : Fin shape.primePublic → fields .prime)
    (i : Fin g.roles.length) (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    parseCache repr shape i ((codec repr shape i).encode (fromRequest shape binaryInputs primeInputs i body metadata)) =
      some (ProtocolWrites.fresh body i) := by
  rw [parseCache_encode,fromRequest_cache]

end LfzkV2.Current.WireBlocks
