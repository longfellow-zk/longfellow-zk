import LfzkV2.Current.Format
import LfzkV2.Current.CanonicalRequest

/-! The deployed transcript format, `LegacyFormat`: the first-fingerprint
prefix (`FingerprintPrefix`), the role-local wire blocks (`WireBlocks`), the
MDA7/JPG2 body (`ProofBodyCodec`) and the deployed node wire
(`NodeWire.current`). Every field is the existing definition, so the
format changes no byte; the lemmas at the end state that definitionally.

`StrandRuntime.Runtime` keeps the earlier names of the history codec at
this format, for the modules not yet stated over a `Format`. -/

noncomputable section
namespace LfzkV2.Current.StrandRuntime
open CanonicalPrefix QueryRuntime
open scoped Classical

namespace Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type} (wire : NodeWire)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

local notation "Value" => QueryRuntime.Runtime.Value repr shape setup publicCount
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "blocks" => QueryRuntime.Runtime.blocks repr shape setup publicCount
local notation "toPoint" => QueryRuntime.Runtime.toPoint repr shape setup publicCount

/-- This is instantiated with the existing first-fingerprint packet and
every role-local runtime packet, including the complete canonical proof body. -/
def schema : TranscriptV2.Strand.History.Codec Value := StrandQueryCodec.schema wire bodyCodec blocks

/-- The actual runtime serializer is the same encoding recognized by the
online decoder. No assumption about arbitrary cache serialization is needed. -/
theorem toPoint_history (value : Value) :
    StrandRuntime.history wire bodyCodec (toPoint value) = (schema wire repr shape setup publicCount).encode value := by
  unfold QueryRuntime.Runtime.toPoint
  rw [history_reindex,history_embed]
  rfl

theorem parent_key (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    QueryRuntime.Runtime.key repr shape setup publicCount value =
      QueryRuntime.Runtime.key repr shape setup publicCount earlier :=
  StrandQueryCodec.parent_first bodyCodec _ _ value earlier previous

/-- The parent relation consumed by the existing algebraic failure cover is
exactly the one obtained by dropping the last strand node. -/
theorem toPoint_parent (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    (toPoint value).parent = some (toPoint earlier) := by
  dsimp only [QueryRuntime.Runtime.Value,QueryRuntime.Runtime.blocks] at value earlier previous
  unfold QueryRuntime.Runtime.toPoint
  rw [reindex_parent,embed_parent,previous,Option.map_some,Option.map_some,
    parent_key repr shape setup publicCount value earlier previous]

theorem history_parent (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    ∃ digest message, (schema wire repr shape setup publicCount).encode value =
      .child ((schema wire repr shape setup publicCount).encode earlier) digest message :=
  StrandQueryCodec.history_parent wire bodyCodec blocks value earlier previous

/-- Parsed packet values and canonical runtime points are the same finite
objects. The verifier's redundant caches add no independent coordinates. -/
def valuesEquiv (fits : g.roles.length < 2^64) :
    Value ≃ {point : Point // QueryRuntime.Runtime.Canonical repr shape setup publicCount point} :=
  Equiv.ofInjective toPoint (QueryRuntime.Runtime.toPoint_injective repr shape setup publicCount fits)

theorem valuesEquiv_apply (fits : g.roles.length < 2^64) (value : Value) :
    ((valuesEquiv repr shape setup publicCount fits) value).val = toPoint value := rfl

theorem valuesEquiv_symm (fits : g.roles.length < 2^64)
    (point : {point : Point // QueryRuntime.Runtime.Canonical repr shape setup publicCount point}) :
    toPoint ((valuesEquiv repr shape setup publicCount fits).symm point) = point.val := by
  have same := congrArg Subtype.val ((valuesEquiv repr shape setup publicCount fits).apply_symm_apply point)
  rw [valuesEquiv_apply] at same
  exact same

variable {P : Type}

/-- Give each canonical verifier input its one ordinary name in the
renamed search. All speculative and malformed names remain in the complement. -/
def pointCodec (fits : g.roles.length < 2^64) (locate : Value → P) :
    ByteOracleTransport.Codec Point (StrandSearch.Name P Value)
      (QueryRuntime.Runtime.Canonical repr shape setup publicCount) where
  encode point :=
    let value := (valuesEquiv repr shape setup publicCount fits).symm point
    .inl (locate value,some value)
  decode
    | .inl (point,some value) =>
        if point = locate value then some ((valuesEquiv repr shape setup publicCount fits) value) else none
    | _ => none
  decode_encode point := by simp only [Equiv.apply_symm_apply,if_true]
  encode_decode raw point found := by
    cases raw with
    | inr _ => cases found
    | inl raw =>
        rcases raw with ⟨raw,value⟩
        cases value with
        | none => cases found
        | some value =>
            change (if raw = locate value then some ((valuesEquiv repr shape setup publicCount fits) value)
              else none) = some point at found
            by_cases equal : raw = locate value
            · rw [if_pos equal] at found
              cases Option.some.inj found
              simp only [Equiv.symm_apply_apply,equal]
            · rw [if_neg equal] at found
              contradiction

/-- Merkle preimages start with ASCII `p`, whereas every canonical
strand node starts with type word one. Even a forged logical annotation
cannot make these raw bytes spend an ordinary protocol-query allowance. -/
theorem pointCodec_merkle_auxiliary (fits : g.roles.length < 2^64) (locate : Value → P)
    (bytes : P → Bytes)
    (located : ∀ value, bytes (locate value) = ((schema wire repr shape setup publicCount).encode value).input.encode)
    (raw : P) (value : Option Value) (merkle : (bytes raw).head? = some 112) :
    (pointCodec repr shape setup publicCount fits locate).decode (.inl (raw,value)) = none := by
  cases value with
  | none => rfl
  | some value =>
      have different : raw ≠ locate value := by
        intro same
        rw [same,located value] at merkle
        have first : (((schema wire repr shape setup publicCount).encode value).input.encode).head? = some 1 := by
          cases (schema wire repr shape setup publicCount).encode value <;> rfl
        rw [first] at merkle
        exact (by decide : (1 : TranscriptV2.Framing.Byte) ≠ 112) (Option.some.inj merkle)
      simp only [pointCodec,if_neg different]

/-- Every ordinary name actually emitted by online decoding is in this
canonical image. The raw-byte equality follows from parsing, not a promise
about how a caller constructed its cache. -/
theorem pointCodec_ordinary (fits : g.roles.length < 2^64) (locate : Value → P)
    (bytes : P → Bytes) (injective : Function.Injective bytes)
    (located : ∀ value, bytes (locate value) = ((schema wire repr shape setup publicCount).encode value).input.encode)
    (past : List TranscriptV2.Strand.Entry) (raw : P) (value : Value)
    (parsed : StrandSearch.decode (schema wire repr shape setup publicCount) bytes past raw = some value) :
    ((pointCodec repr shape setup publicCount fits locate).decode (.inl (raw,some value))).map Subtype.val =
      some (toPoint value) := by
  have same : raw = locate value := injective
    ((StrandSearch.decode_erases (schema wire repr shape setup publicCount) bytes past raw value parsed).symm.trans
      (located value).symm)
  simp only [pointCodec,if_pos same,Option.map_some,valuesEquiv]
  rfl

end Runtime
end LfzkV2.Current.StrandRuntime

noncomputable section
namespace LfzkV2.Current
open CanonicalPrefix QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

/-- The deployed format. -/
def LegacyFormat : Format g fields Advice publicCount where
  wire := NodeWire.current
  Key := FingerprintPrefix.Key publicCount
  keyFintype := inferInstance
  capacity := QueryRuntime.Runtime.capacity repr shape setup publicCount
  first := FingerprintPrefix.codec setup publicCount
  first_bounded value := (FingerprintPrefix.encode_length_le setup publicCount value).trans (le_max_left _ _)
  later := (List.ofFn (QueryRuntime.Runtime.ordinary repr shape setup publicCount)).tail
  roles_eq := QueryRuntime.Runtime.roles_eq repr shape setup publicCount
  body := ProofBodyCodec.codec repr g
  binaryPublic := shape.binaryPublic
  primePublic := shape.primePublic
  context := FingerprintPrefix.context
  root := FingerprintPrefix.Key.root
  root_context _ _ := rfl
  hashPublic := CanonicalRequest.hashPublic publicCount
  hashPublic_context _ _ := rfl
  jointContext := setup.jointContext
  openingBase := WireOpening.openingBase shape repr setup publicCount
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
    obtain rfl : i = CanonicalRequest.primeBoundary g := Fin.ext hi
    exact CanonicalRequest.readPrimePublic_block repr shape setup publicCount binaryRequest metadata request
      ⟨body,fun _ => 0⟩ _ rfl past
  block_independent binaryRequest metadata independent request body i first second :=
    CanonicalRequest.block_challengeIndependent repr shape setup publicCount binaryRequest metadata independent
      request ⟨body,fun _ => 0⟩ i first second

/-! The deployed format is the existing encoding, definitionally. -/
namespace LegacyFormat
local notation "L" => LegacyFormat repr shape setup publicCount

theorem wire_eq : (L).wire = NodeWire.current := rfl
theorem body_eq : (L).body = ProofBodyCodec.codec repr g := rfl
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
theorem schema_eq : (L).schema = StrandRuntime.Runtime.schema NodeWire.current repr shape setup publicCount := rfl
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
