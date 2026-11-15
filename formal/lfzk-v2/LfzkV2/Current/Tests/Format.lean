import LfzkV2.Current.LegacyFormat

/-! `LegacyFormat` is the deployed encoding: its history codec, logical
points and request replay are the earlier legacy definitions by `rfl`, so
the format bundle changes no byte. The history codec law is derived once,
for every format, from the per-node codec laws. -/
namespace LfzkV2.Current.Tests.Format
open CanonicalPrefix QueryRuntime

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
local notation "L" => LegacyFormat repr shape setup publicCount

-- The strand history of a parsed legacy value is the deployed serializer.
example (value : QueryRuntime.Runtime.Value repr shape setup publicCount) :
    StrandRuntime.history NodeWire.current (ProofBodyCodec.codec repr g).whole
        (QueryRuntime.Runtime.toPoint repr shape setup publicCount value) =
      (L).schema.encode value :=
  (L).toPoint_history value

-- Parsing the history recovers the packet values, without the earlier
-- chained-transcript bytes or a u64 round bound.
example (value : QueryRuntime.Runtime.Value repr shape setup publicCount) :
    (L).schema.decode
      (StrandRuntime.history NodeWire.current (ProofBodyCodec.codec repr g).whole
        (QueryRuntime.Runtime.toPoint repr shape setup publicCount value)) = some value :=
  (L).history_codec value

example : Function.Injective (QueryRuntime.Runtime.toPoint repr shape setup publicCount) :=
  (L).toPoint_injective

-- The request replay is the canonical request encoding.
example {C : Type} (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
    (request : CanonicalRequest.Request shape publicCount) :
    (L).encoding binaryRequest metadata request =
      CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request := rfl

/--
info: 'LfzkV2.Current.Format.history_codec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Format.history_codec

/--
info: 'LfzkV2.Current.Format.withBackendOpening_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Format.withBackendOpening_eq

/--
info: 'LfzkV2.Current.LegacyFormat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LegacyFormat

end LfzkV2.Current.Tests.Format
