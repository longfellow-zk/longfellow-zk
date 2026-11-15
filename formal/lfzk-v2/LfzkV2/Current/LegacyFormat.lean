import LfzkV2.Current.Format
import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ProofBodyBounds
import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.LegacyNode

/-! The deployed transcript format, `LegacyFormat`: the first-fingerprint
prefix (`FingerprintPrefix`), the role-local wire blocks (`WireBlocks`), the
MDA7/JPG2 body (`ProofBodyCodec`) and the deployed node wire
(`NodeWire.current`). Every field is the existing definition, so the
format changes no byte; the lemmas at the end state that definitionally.

-/


noncomputable section
namespace LfzkV2.Current
open CanonicalPrefix QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

private theorem later_get (i : Fin g.roles.length) (h : i.val-1 <
      (List.ofFn (QueryRuntime.Runtime.ordinary repr shape setup publicCount)).tail.length) (hi : i.val ≠ 0) :
    (List.ofFn (QueryRuntime.Runtime.ordinary repr shape setup publicCount)).tail.get ⟨i.val-1,h⟩ =
      QueryRuntime.Runtime.ordinary repr shape setup publicCount i := by
  simp only [List.get_eq_getElem,List.getElem_tail,List.getElem_ofFn]
  congr 1
  ext
  simp only
  omega

private theorem packet_block_cast {Fresh : Type} {capacity : ℕ} {first second : Packet Fresh capacity}
    (h : first = second) (value : first.Data) : second.block (h ▸ value) = first.block value := by
  cases h
  rfl

/-- The deployed format. -/
@[reducible] def LegacyFormat : Format g fields Advice publicCount where
  wire := NodeWire.current
  Key := FingerprintPrefix.Key publicCount
  keyFintype := inferInstance
  capacity := QueryRuntime.Runtime.capacity repr shape setup publicCount
  first := FingerprintPrefix.codec setup publicCount
  first_bounded value := (FingerprintPrefix.encode_length_le setup publicCount value).trans (le_max_left _ _)
  later := (List.ofFn (QueryRuntime.Runtime.ordinary repr shape setup publicCount)).tail
  roles_eq := QueryRuntime.Runtime.roles_eq repr shape setup publicCount
  body := (ProofBodyCodec.codec repr g).whole
  scalars := repr
  binaryPublic := shape.binaryPublic
  primePublic := shape.primePublic
  context := FingerprintPrefix.context
  root := FingerprintPrefix.Key.root
  root_context _ _ := rfl
  hashPublic := CanonicalRequest.hashPublic publicCount
  hashPublic_context _ _ := rfl
  jointContext := setup.jointContext
  openingBase := WireOpening.openingBase shape repr setup publicCount
  primeIndex := CanonicalRequest.primeBoundary g
  primeIndex_le := le_rfl
  decodePrimePublic := CanonicalRequest.decodePrimePublic repr shape setup publicCount
  Metadata := WireBlocks.Metadata shape
  block binaryRequest metadata request body :=
    CanonicalRequest.block repr shape setup publicCount binaryRequest metadata request ⟨body,fun _ => 0⟩
  block_zero binaryRequest metadata request body i past hi :=
    CanonicalRequest.block_zero repr shape setup publicCount binaryRequest metadata request ⟨body,fun _ => 0⟩ i hi past
  block_fresh binaryRequest metadata request body i past :=
    CanonicalRequest.block_fresh repr shape setup publicCount binaryRequest metadata request ⟨body,fun _ => 0⟩ i past
  block_opening binaryRequest metadata request body past :=
    CanonicalRequest.block_opening repr shape setup publicCount binaryRequest metadata request ⟨body,fun _ => 0⟩ past
  block_prime binaryRequest metadata request body i past hi := by
    subst hi
    exact CanonicalRequest.readPrimePublic_block repr shape setup publicCount binaryRequest metadata request
      ⟨body,fun _ => 0⟩ _ rfl past
  block_independent binaryRequest metadata independent request body i first second :=
    CanonicalRequest.block_challengeIndependent repr shape setup publicCount binaryRequest metadata independent
      request ⟨body,fun _ => 0⟩ i first second

  block_later binaryRequest metadata request body i past hi :=
    ⟨(later_get repr shape setup publicCount i _ hi).symm ▸
        CanonicalRequest.ordinaryData shape publicCount binaryRequest metadata request body i past,
      (CanonicalRequest.block_pos repr shape setup publicCount binaryRequest metadata request ⟨body,fun _ => 0⟩
        i hi past).trans (packet_block_cast _ _).symm⟩
  bodyBound := ProofBodyBounds.bodyBound repr g
  body_bound := ProofBodyBounds.encode_length_le repr g
  node binaryRequest metadata request root i writes past :=
    if h : Nonempty Advice then
      LegacyNode.canonicalBase shape (Classical.choice h) repr setup publicCount binaryRequest metadata
        request root i writes past
    else ⟨[],by simp⟩
  block_node binaryRequest metadata request body i past := by
    have nonempty : Nonempty Advice := ⟨body.advice⟩
    rw [dif_pos nonempty]
    exact (LegacyNode.canonicalBase_body shape _ repr setup publicCount binaryRequest metadata request
      ⟨body,fun _ => 0⟩ i past).symm

/-! The deployed format is the existing encoding, definitionally. -/
namespace LegacyFormat
local notation "L" => LegacyFormat repr shape setup publicCount

theorem wire_eq : (L).wire = NodeWire.current := rfl
theorem body_eq : (L).body = (ProofBodyCodec.codec repr g).whole := rfl
theorem scalars_eq : (L).scalars = repr := rfl
theorem first_eq : (L).first = FingerprintPrefix.codec setup publicCount := rfl
theorem Key_eq : (L).Key = FingerprintPrefix.Key publicCount := rfl
theorem Base_eq : (L).Base = CanonicalRequest.Base repr shape setup publicCount := rfl
theorem Point_eq : (L).Point = QueryRuntime.Runtime.Point repr shape setup publicCount := rfl
theorem Request_eq : (L).Request = CanonicalRequest.Request shape publicCount := rfl
theorem Value_eq : (L).Value = QueryRuntime.Runtime.Value repr shape setup publicCount := rfl
theorem packets_eq : (L).packets = QueryRuntime.Runtime.packets repr shape setup publicCount := rfl
theorem blocks_eq : (L).blocks = QueryRuntime.Runtime.blocks repr shape setup publicCount := rfl
theorem toPoint_eq : (L).toPoint = QueryRuntime.Runtime.toPoint repr shape setup publicCount := rfl
theorem key_eq : (L).key = QueryRuntime.Runtime.key repr shape setup publicCount := rfl
theorem schema_eq : (L).schema = StrandQueryCodec.schema NodeWire.current (ProofBodyCodec.codec repr g).whole
    (QueryRuntime.Runtime.blocks repr shape setup publicCount) := rfl
theorem Canonical_eq : (L).Canonical = QueryRuntime.Runtime.Canonical repr shape setup publicCount := rfl
theorem openingWire_eq : (L).openingWire = WireOpening.openingWire shape repr setup publicCount := rfl
theorem hashPublic_eq : (L).hashPublic = CanonicalRequest.hashPublic publicCount := rfl
theorem decodePrimePublic_eq :
    (L).decodePrimePublic = CanonicalRequest.decodePrimePublic repr shape setup publicCount := rfl

theorem RequestMetadata_eq {C : Type} :
    (L).RequestMetadata C = CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount := rfl

theorem encoding_eq {C : Type} (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
    (request : CanonicalRequest.Request shape publicCount) :
    (L).encoding binaryRequest metadata request =
      CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request := rfl

end LegacyFormat
end LfzkV2.Current

namespace LfzkV2.Current.CanonicalRuntime
variable {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}

/-- Runtime outputs for requests of the deployed format, named by its
public shape alone; equal to `FormatOutput binary (LegacyFormat ..)`. -/
abbrev Output (binary : ApplicationSetup.BinaryPublic B shared maskBits adviceBits)
    (shape : WireBlocks.Shape g fields) :=
  RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice)
    (Request := CanonicalRequest.Request shape binary.nPublic)

end LfzkV2.Current.CanonicalRuntime
