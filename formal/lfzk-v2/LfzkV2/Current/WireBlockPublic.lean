import LfzkV2.Current.WireBlocks

/-! Public-input readback from the actual prime-start bytes. The reader
checks the complete block, including the trailing role message. Public
values are neither placed in the earlier context key nor supplied through a
later equality certificate. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open CanonicalPrefix
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice) (shape : Shape g fields)

def primeCodec (role : Role) :
    PrefixCodec (PrimeStart fields shape.primePublic × RoleData shape role) :=
  (primeStart repr shape).pair (roleCodec repr shape role)

def readPrimePublic (role : Role) (bytes : Bytes) : Option (Fin shape.primePublic → fields .prime) :=
  (readWhole (primeCodec repr shape role) bytes).map (fun value => value.1.2.1.2)

theorem readPrimePublic_encode (role : Role) (startData : PrimeStart fields shape.primePublic)
    (payload : RoleData shape role) :
    readPrimePublic repr shape role ((primeCodec repr shape role).encode (startData,payload)) =
      some startData.2.1.2 := by
  simp only [readPrimePublic,readWhole_encode,Option.map_some]

private theorem startAt_prime (i : Fin g.roles.length) (hi : i.val = g.primeStart) :
    startAt g i = .prime := by simp [startAt,hi]

private def primeValue (start : Start) (h : start = .prime)
    (value : PrimeStart fields shape.primePublic) : StartData (Advice := Advice) shape start := by
  cases h
  exact value

private theorem primeValue_encode (start : Start) (h : start = .prime)
    (value : PrimeStart fields shape.primePublic) :
    (startCodec repr shape start).encode (primeValue shape start h value) =
      (primeStart repr shape).encode value := by
  cases h
  rfl

private theorem primeValue_cache (start : Start) (h : start = .prime)
    (value : PrimeStart fields shape.primePublic) :
    startCache (Advice := Advice) shape start (primeValue shape start h value) =
      { fingerprints := some value.1 } := by
  cases h
  rfl

def primePacket (i : Fin g.roles.length) (hi : i.val = g.primeStart)
    (startData : PrimeStart fields shape.primePublic) (payload : RoleData shape (g.roles.get i)) :
    Data (Advice := Advice) shape i :=
  (primeValue shape (startAt g i) (startAt_prime i hi) startData,payload)

theorem primePacket_encode (i : Fin g.roles.length) (hi : i.val = g.primeStart)
    (startData : PrimeStart fields shape.primePublic) (payload : RoleData shape (g.roles.get i)) :
    (codec repr shape i).encode (primePacket shape i hi startData payload) =
      (primeCodec repr shape (g.roles.get i)).encode (startData,payload) := by
  change (startCodec repr shape (startAt g i)).encode (primeValue shape _ _ startData) ++ (roleCodec repr shape (g.roles.get i)).encode payload = _
  rw [primeValue_encode]
  rfl

/-- The actual packet constructor and actual bytes reader agree for every
public input vector. No caller-supplied public-input correspondence is used. -/
theorem readPrimePublic_primePacket (i : Fin g.roles.length) (hi : i.val = g.primeStart)
    (startData : PrimeStart fields shape.primePublic) (payload : RoleData shape (g.roles.get i)) :
    readPrimePublic repr shape (g.roles.get i)
      ((codec repr shape i).encode (primePacket shape i hi startData payload)) = some startData.2.1.2 := by
  rw [primePacket_encode]
  exact readPrimePublic_encode repr shape _ startData payload

theorem primePacket_fingerprints (i : Fin g.roles.length) (hi : i.val = g.primeStart)
    (startData : PrimeStart fields shape.primePublic) (payload : RoleData shape (g.roles.get i)) :
    (cache (Advice := Advice) shape i (primePacket (Advice := Advice) shape i hi startData payload)).fingerprints = some startData.1 := by
  change (startCache (Advice := Advice) shape (startAt g i) (primeValue shape _ _ startData)).fingerprints = _
  rw [primeValue_cache]

end LfzkV2.Current.WireBlocks
