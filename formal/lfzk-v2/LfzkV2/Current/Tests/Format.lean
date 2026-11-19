import LfzkV2.Current.TaggedFormat

/-! The history codec law is derived once, for every format, from the
per-node codec laws; here it is instantiated at the deployed `TaggedFormat`. -/
namespace LfzkV2.Current.Tests.Format

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : TaggedFormat.Setup) (publicCount : ℕ)
variable [Fintype (fields .prime)] [Inhabited Advice]
local notation "T" => TaggedFormat.format repr shape setup publicCount

-- The strand history of a parsed value is the format's serializer.
example (value : (T).Value) :
    StrandRuntime.history (T).wire (T).body ((T).toPoint value) = (T).schema.encode value :=
  (T).toPoint_history value

-- Parsing the history recovers the packet values.
example (value : (T).Value) :
    (T).schema.decode (StrandRuntime.history (T).wire (T).body ((T).toPoint value)) = some value :=
  (T).history_codec value

example : Function.Injective (T).toPoint := (T).toPoint_injective

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
info: 'LfzkV2.Current.TaggedFormat.format' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TaggedFormat.format

end LfzkV2.Current.Tests.Format
