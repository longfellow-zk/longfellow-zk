import LfzkV2.Current.TaggedFormat
import LfzkV2.Current.MdocAdvice

/-! The deployed tagged codecs are instances of the node grammar (`Grammar`):
every message `TaggedFormat` writes, typed with `TaggedCodec`, has the bytes of
the `Grammar` encoding of one message of the deployed registry
(`rust/src/runtime/v2/proto/tags.rs`), so `Grammar`'s parser and injectivity
apply to the deployed bytes.

- `table` and `registry` are the deployed field and tag registries. An
  element is its canonical serialization of the field's width (16 bytes for
  GF(2^128), 32 for P-256), as the registry parser reads it; the typed field
  codecs embed into it injectively.
- `Writes` is a typed value written as a fixed number of grammar messages
  that determine it. Each value codec of `TaggedCodec` and each message codec
  of `TaggedFormat` has its `Writes` (`*_encodes`).
- The node theorems: a later node is the grammar messages of its packet and
  `ROUND` (`later_node`), the seal node is the `Seal` message and `SEAL`
  (`seal_node`), and node 0 is the setup's statement prefix, then grammar
  messages and `ROUND` (`first_node`).
- `toPoint_injective`: the deployed canonical points are injective, derived
  from the grammar's injectivity rather than from the packet parsers.

The masked quotients are the one message whose codec a format takes as a
parameter (`Representations.adviceWrites`); `AdviceGrammar` states that it is
the `P256AdapterQuotients` schema, and `mdocAdvice` proves it for the deployed
mdoc advice. -/
noncomputable section
namespace LfzkV2.Current.TaggedGrammar
open TranscriptV2.Framing (Byte FieldCodec encodeLE)
open CanonicalPrefix TaggedCodec

/-! ## The deployed registry -/

/-- The element width of each registered field. -/
def width : Side → ℕ
  | .binary => 16
  | .prime => 32

/-- An element as the registry parser reads it: its field's width of bytes. -/
abbrev Raw (side : Side) := {bytes : Bytes // bytes.length = width side}

def rawCodec (side : Side) : FieldCodec (Raw side) where
  width := width side
  positive := by cases side <;> decide
  buffer := by cases side <;> decide
  encode := Subtype.val
  decode bytes := if h : bytes.length = width side then some ⟨bytes,h⟩ else none
  length value := value.property
  inverse value := dif_pos value.property
  canonical bytes value h := by
    split at h
    · cases Option.some.inj h
      rfl
    · contradiction

def fieldWord (side : Side) : Grammar.Word := ⟨TaggedFormat.fieldId side,by cases side <;> decide⟩

def ofFieldWord (word : Grammar.Word) : Option Side :=
  if word.val = TaggedFormat.fieldId .binary then some .binary
  else if word.val = TaggedFormat.fieldId .prime then some .prime else none

/-- The registered fields: `FieldID::Gf2_128` (4) and `FieldID::P256` (1). -/
abbrev table : Grammar.FieldTable where
  Id := Side
  code := fieldWord
  ofCode := ofFieldWord
  ofCode_code side := by cases side <;> rfl
  code_ofCode word side h := by
    unfold ofFieldWord at h
    split at h
    next hb => cases h; exact Fin.ext hb.symm
    next =>
      split at h
      next hp => cases h; exact Fin.ext hp.symm
      next => contradiction
  Element := Raw
  codec := rawCodec

/-- The tags of `rust/src/runtime/v2/proto/tags.rs`. -/
inductive Tag where
  | mdocStatement | zkStatement | circuit | commitmentLayout | jointGeometry | publicInputs
  | adapterLayout | commitment | fingerprintResponse | sumcheckRound | sumcheckCross
  | sumcheckClaims | splitOpening | adapterQuotients | packingU | packingA | polygeroResponse
  | seal
  deriving DecidableEq, Repr

def Tag.value : Tag → ℕ
  | .mdocStatement => 16
  | .zkStatement => 17
  | .circuit => 18
  | .commitmentLayout => 19
  | .jointGeometry => 20
  | .publicInputs => TaggedFormat.publicInputsTag
  | .adapterLayout => 22
  | .commitment => TaggedFormat.commitmentTag
  | .fingerprintResponse => TaggedFormat.fingerprintTag
  | .sumcheckRound => TaggedFormat.roundTag
  | .sumcheckCross => TaggedFormat.crossTag
  | .sumcheckClaims => TaggedFormat.claimsTag
  | .splitOpening => TaggedFormat.splitTag
  | .adapterQuotients => TaggedFormat.quotientsTag
  | .packingU => TaggedFormat.packingUTag
  | .packingA => TaggedFormat.packingATag
  | .polygeroResponse => TaggedFormat.responseTag
  | .seal => TaggedFormat.sealTag

def Tag.code (tag : Tag) : Grammar.Word := ⟨tag.value,by cases tag <;> decide⟩

def Tag.all : List Tag :=
  [.mdocStatement,.zkStatement,.circuit,.commitmentLayout,.jointGeometry,.publicInputs,
    .adapterLayout,.commitment,.fingerprintResponse,.sumcheckRound,.sumcheckCross,.sumcheckClaims,
    .splitOpening,.adapterQuotients,.packingU,.packingA,.polygeroResponse,.seal]

def Tag.ofCode (word : Grammar.Word) : Option Tag := Tag.all.find? fun tag => tag.code = word

/-- Each tag's value kinds (`Tag::schema`). -/
def Tag.schema : Tag → List Grammar.Kind
  | .mdocStatement => [.bytes,.bytes,.bytes,.nats]
  | .zkStatement => [.bytes,.bytes]
  | .circuit => [.bytes]
  | .commitmentLayout => [.nats,.bytes,.nats,.nats,.nats]
  | .jointGeometry => [.nats]
  | .publicInputs => [.elements]
  | .adapterLayout => [.bytes,.nats,.nats]
  | .commitment => [.bytes]
  | .fingerprintResponse => [.elements]
  | .sumcheckRound => [.elements]
  | .sumcheckCross => [.elements]
  | .sumcheckClaims => [.elements]
  | .splitOpening => [.elements]
  | .adapterQuotients => [.bits,.bits]
  | .packingU => [.elements]
  | .packingA => [.elements]
  | .polygeroResponse => [.elements,.elements]
  | .seal => [.bytes]

abbrev registry : Grammar.Registry where
  Tag := Tag
  code := Tag.code
  ofCode := Tag.ofCode
  ofCode_code tag := by cases tag <;> decide
  code_ofCode word tag h := by
    unfold Tag.ofCode at h
    simpa using List.find?_some h
  reserved tag := by cases tag <;> decide
  schema := Tag.schema

abbrev Message := Grammar.Message table registry

/-- The grammar bytes of a message list. -/
def messagesBytes (messages : List Message) : Bytes :=
  messages.flatMap (Grammar.message table registry).encode

/-! ## Values -/

def bytesOf (value : BoundedBytes maxLength) : Grammar.Value table .bytes :=
  ⟨value.bytes,by have := value.bound; unfold maxLength at this; omega⟩

theorem bytesOf_injective : Function.Injective bytesOf := by
  intro first second same
  exact BoundedBytes.ext (congrArg Subtype.val same)

theorem bytesValue_grammar (value : BoundedBytes maxLength) :
    bytesValue.encode value = (Grammar.value table .bytes).encode (bytesOf value) := by
  rw [bytesValue_encode,Grammar.bytes_encode]
  rfl

def digestOf (digest : Digest) : Grammar.Value table .bytes :=
  ⟨List.ofFn digest,by rw [List.length_ofFn]; decide⟩

theorem digestOf_injective : Function.Injective digestOf := by
  intro first second same
  exact List.ofFn_injective (congrArg Subtype.val same)

theorem digestValue_grammar (digest : Digest) :
    digestValue.encode digest = (Grammar.value table .bytes).encode (digestOf digest) := by
  rw [Grammar.bytes_encode]
  change word 0 ++ word 32 ++ (PrefixCodec.vector PrefixCodec.byte 32).encode digest = _
  rw [PrefixCodec.bytes_encode]
  simp only [digestOf,Grammar.u64_encode,List.length_ofFn]
  rfl

/-- A fixed-width element codec read as raw elements of one field. -/
def raw {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) (value : F) : Raw side :=
  ⟨codec.encode value,fixed value⟩

theorem raw_injective {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) :
    Function.Injective (raw side codec fixed) := by
  intro first second same
  exact codec.encode_injective (congrArg Subtype.val same)

def elementsOf {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) (count : ℕ) (fits : count < 2^64)
    (values : Fin count → F) : Grammar.Value table .elements :=
  ⟨side,⟨List.ofFn fun j => raw side codec fixed (values j),by rw [List.length_ofFn]; exact fits⟩⟩

theorem elementsOf_injective {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) (count : ℕ) (fits : count < 2^64) :
    Function.Injective (elementsOf side codec fixed count fits) := by
  intro first second same
  have lists := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj same).2)
  have functions := List.ofFn_injective lists
  funext j
  exact raw_injective side codec fixed (congrFun functions j)

private theorem flatMap_raw {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) (values : List F) :
    (values.map (raw side codec fixed)).flatMap Subtype.val = values.flatMap codec.encode := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.map_cons,List.flatMap_cons,ih]; rfl

theorem elementsOf_grammar {F : Type} (side : Side) (codec : PrefixCodec F)
    (fixed : ∀ value, (codec.encode value).length = width side) (count : ℕ) (fits : count < 2^64)
    (values : Fin count → F) :
    (TaggedCodec.elementsOf (TaggedFormat.fieldId side) codec count).encode values =
      (Grammar.value table .elements).encode (elementsOf side codec fixed count fits values) := by
  rw [TaggedCodec.elementsOf_encode,Grammar.elements_encode]
  have hlist : (List.ofFn fun j => raw side codec fixed (values j)) = (List.ofFn values).map (raw side codec fixed) :=
    by rw [List.map_ofFn]; rfl
  simp only [elementsOf,Grammar.u64_encode,List.length_ofFn]
  rw [hlist]
  change _ = _ ++ ((List.ofFn values).map (raw side codec fixed)).flatMap Subtype.val
  rw [flatMap_raw]
  rfl

/-! ## Messages that determine their values -/

/-- A typed value written as a fixed number of grammar messages, which
determine it. -/
structure Writes (A : Type) where
  count : ℕ
  messages : A → List Message
  length : ∀ value, (messages value).length = count
  injective : Function.Injective messages

namespace Writes
variable {A B : Type}

/-- A codec's bytes are the grammar bytes of these messages. -/
def Encodes (writes : Writes A) (codec : PrefixCodec A) : Prop :=
  ∀ value, codec.encode value = messagesBytes (writes.messages value)

def none : Writes Unit where
  count := 0
  messages _ := []
  length _ := rfl
  injective _ _ _ := rfl

theorem none_encodes : none.Encodes PrefixCodec.unit := fun _ => rfl

/-- One message with a fixed tag. -/
def single (tag : Tag) (values : A → Grammar.Values table tag.schema)
    (injective : Function.Injective values) : Writes A where
  count := 1
  messages value := [⟨tag,values value⟩]
  length _ := rfl
  injective _ _ same :=
    injective (eq_of_heq (Sigma.mk.inj (List.cons_eq_cons.mp same).1).2)

theorem single_encodes (tag : Tag) (values : A → Grammar.Values table tag.schema)
    (injective : Function.Injective values) (codec : PrefixCodec A)
    (encodes : ∀ value, codec.encode value = (Grammar.values table tag.schema).encode (values value)) :
    (single tag values injective).Encodes (tagged tag.value codec) := by
  intro value
  change word tag.value ++ codec.encode value = (Grammar.message table registry).encode ⟨tag,values value⟩ ++ []
  rw [List.append_nil,Grammar.message_encode,encodes]
  rfl

def pair (first : Writes A) (second : Writes B) : Writes (A × B) where
  count := first.count+second.count
  messages value := first.messages value.1 ++ second.messages value.2
  length value := by rw [List.length_append,first.length,second.length]
  injective one other same := by
    obtain ⟨h1,h2⟩ := List.append_inj same (by rw [first.length,first.length])
    exact Prod.ext (first.injective h1) (second.injective h2)

theorem pair_encodes (first : Writes A) (second : Writes B) (firstCodec : PrefixCodec A)
    (secondCodec : PrefixCodec B) (hfirst : first.Encodes firstCodec) (hsecond : second.Encodes secondCodec) :
    (first.pair second).Encodes (firstCodec.pair secondCodec) := by
  intro value
  change firstCodec.encode value.1 ++ secondCodec.encode value.2 = _
  rw [hfirst,hsecond]
  simp only [messagesBytes,pair,List.flatMap_append]

theorem cast_encodes (h : A = B) (writes : Writes A) (codec : PrefixCodec A) (encodes : writes.Encodes codec) :
    (cast (congrArg Writes h) writes).Encodes (cast (congrArg PrefixCodec h) codec) := by
  subst h
  exact encodes

end Writes

/-! ## The typed messages of `TaggedFormat` -/

section Packets
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)

theorem fieldCodec_fixed (side : Side) (value : fields side) :
    ((PrefixCodec.field (TaggedFormat.fieldCodec repr side)).encode value).length = width side := by
  cases side
  · exact (repr.binary.length value).trans repr.binaryWidth
  · exact (repr.prime.length value).trans repr.primeWidth

/-- `Elements(F, count)` of one side's field. -/
def fieldElements (side : Side) (count : ℕ) (fits : count < 2^64) (values : Fin count → fields side) :
    Grammar.Values table [.elements] :=
  (elementsOf side (PrefixCodec.field (TaggedFormat.fieldCodec repr side)) (fieldCodec_fixed repr side)
    count fits values,())

theorem fieldElements_injective (side : Side) (count : ℕ) (fits : count < 2^64) :
    Function.Injective (fieldElements repr side count fits) := by
  intro first second same
  exact elementsOf_injective _ _ _ count fits (congrArg Prod.fst same)

theorem elements_grammar (side : Side) (count : ℕ) (fits : count < 2^64) (values : Fin count → fields side) :
    (elements (TaggedFormat.fieldId side) (TaggedFormat.fieldCodec repr side) count).encode values =
      (Grammar.values table [.elements]).encode (fieldElements repr side count fits values) := by
  change _ = _ ++ []
  rw [List.append_nil]
  exact elementsOf_grammar _ _ _ count fits values

/-- `Elements(F, 1)` of one element. -/
def one (side : Side) (value : fields side) : Grammar.Values table [.elements] :=
  fieldElements repr side 1 (by decide) fun _ => value

theorem one_injective (side : Side) : Function.Injective (one repr side) := by
  intro first second same
  exact congrFun (fieldElements_injective repr side 1 (by decide) same) 0

/-- `Elements(F, 2)` of a pair. -/
def two (side : Side) (value : fields side × fields side) : Grammar.Values table [.elements] :=
  fieldElements repr side 2 (by decide) ![value.1,value.2]

theorem two_injective (side : Side) : Function.Injective (two repr side) := by
  intro first second same
  have equal := fieldElements_injective repr side 2 (by decide) same
  exact Prod.ext (congrFun equal 0) (congrFun equal 1)

theorem element_grammar (side : Side) (value : fields side) :
    (element (TaggedFormat.fieldId side) (TaggedFormat.fieldCodec repr side)).encode value =
      (Grammar.values table [.elements]).encode (one repr side value) :=
  elements_grammar repr side 1 (by decide) _

theorem elementPair_grammar (side : Side) (value : fields side × fields side) :
    (elementPair (TaggedFormat.fieldId side) (TaggedFormat.fieldCodec repr side)).encode value =
      (Grammar.values table [.elements]).encode (two repr side value) :=
  elements_grammar repr side 2 (by decide) _

/-- The masked quotients follow the `P256AdapterQuotients` schema: the
format's advice writes are the grammar bytes of two `Bits` values. -/
structure AdviceGrammar where
  values : Advice → Grammar.Values table (Tag.schema .adapterQuotients)
  encodes : ∀ advice, repr.adviceWrites.encode advice =
    (Grammar.values table (Tag.schema .adapterQuotients)).encode (values advice)

variable {repr}

theorem AdviceGrammar.injective (advice : AdviceGrammar repr) : Function.Injective advice.values := by
  intro first second same
  apply repr.adviceWrites.encode_injective
  rw [advice.encodes,advice.encodes,same]

variable (repr)

/-- Both fields' masked fingerprints, or the masked quotients, at a
frontend's first boundary. -/
def startWrites (advice : AdviceGrammar repr) :
    (start : WireBlocks.Start) → Writes (TaggedFormat.StartData fields Advice start)
  | .none => Writes.none
  | .prime => (Writes.single .fingerprintResponse (two repr .binary) (two_injective repr .binary)).pair
      (Writes.single .fingerprintResponse (two repr .prime) (two_injective repr .prime))
  | .binary => Writes.single .adapterQuotients advice.values advice.injective

theorem startWrites_encodes (advice : AdviceGrammar repr) (start : WireBlocks.Start) :
    (startWrites repr advice start).Encodes (TaggedFormat.startCodec repr start) := by
  cases start with
  | none => exact Writes.none_encodes
  | prime =>
      exact Writes.pair_encodes _ _ _ _
        (Writes.single_encodes _ _ (two_injective repr .binary) _ (elementPair_grammar repr .binary))
        (Writes.single_encodes _ _ (two_injective repr .prime) _ (elementPair_grammar repr .prime))
  | binary => exact Writes.single_encodes _ _ advice.injective _ advice.encodes

variable (shape : WireBlocks.Shape g fields)

theorem shape_fits (count : ℕ)
    (h : count ∈ [shape.primeInputs,shape.sharedBits+1,shape.packingInputs,g.packingDegree,
      g.rowDimension+g.maskingDegree,2*g.rowDimension]) : count < 2^64 :=
  shape.sliceFits count h

/-- `PolygeroResponse`: `Elements(F, k+s)` H, then `Elements(F, 2k)` Z. -/
def responseValues (side : Side) (response : Response g (fields side)) :
    Grammar.Values table (Tag.schema .polygeroResponse) :=
  ((fieldElements repr side _ (shape_fits shape _ (by simp)) response.h).1,
    ((fieldElements repr side _ (shape_fits shape _ (by simp)) response.z).1,()))

theorem responseValues_injective (side : Side) : Function.Injective (responseValues repr shape side) := by
  intro first second same
  have hh := elementsOf_injective _ _ _ _ (shape_fits shape _ (by simp)) (congrArg Prod.fst same)
  have hz := elementsOf_injective _ _ _ _ (shape_fits shape _ (by simp)) (congrArg (fun value => value.2.1) same)
  cases first
  cases second
  cases hh
  cases hz
  rfl

def responseWrites (side : Side) : Writes (Response g (fields side)) :=
  Writes.single .polygeroResponse (responseValues repr shape side) (responseValues_injective repr shape side)

theorem responseWrites_encodes (side : Side) :
    (responseWrites repr shape side).Encodes (TaggedFormat.response repr side) := by
  refine Writes.single_encodes _ _ (responseValues_injective repr shape side) _ ?_
  intro response
  change (elements _ _ _).encode response.h ++ (elements _ _ _).encode response.z = _
  rw [elements_grammar repr side _ (shape_fits shape _ (by simp)),
    elements_grammar repr side _ (shape_fits shape _ (by simp))]
  change (Grammar.value table .elements).encode (fieldElements repr side _ (shape_fits shape _ (by simp)) response.h).1 ++ [] ++
      ((Grammar.value table .elements).encode (fieldElements repr side _ (shape_fits shape _ (by simp)) response.z).1 ++ []) =
    (Grammar.value table .elements).encode (fieldElements repr side _ (shape_fits shape _ (by simp)) response.h).1 ++
      ((Grammar.value table .elements).encode (fieldElements repr side _ (shape_fits shape _ (by simp)) response.z).1 ++ [])
  simp only [List.append_nil]

/-- `PackingA`, absent at packing degree one. -/
def packingAWrites : Writes (WireBlocks.PackingA g fields) :=
  if h : g.packingDegree = 1 then
    cast (congrArg Writes (by simp only [WireBlocks.PackingA,h,↓reduceIte])) Writes.none
  else
    cast (congrArg Writes (by simp only [WireBlocks.PackingA,h,↓reduceIte]))
      (Writes.single .packingA (one repr .binary) (one_injective repr .binary))

theorem packingAWrites_encodes : (packingAWrites (g := g) repr).Encodes (TaggedFormat.packingA repr) := by
  by_cases h : g.packingDegree = 1
  · simp only [packingAWrites,TaggedFormat.packingA,h,↓reduceDIte]
    exact Writes.cast_encodes (by simp only [WireBlocks.PackingA,h,↓reduceIte]) _ _ Writes.none_encodes
  · simp only [packingAWrites,TaggedFormat.packingA,h,↓reduceDIte]
    apply Writes.cast_encodes (by simp only [WireBlocks.PackingA,h,↓reduceIte])
    exact Writes.single_encodes _ _ (one_injective repr .binary) _ (element_grammar repr .binary)

/-- The prover message of each role. -/
def roleWrites : (role : Role) → Writes (TaggedFormat.RoleData g fields role)
  | .fingerprint => Writes.none
  | .inputAssertions .. => Writes.none
  | .assertions .. => Writes.none
  | .sumcheck side .. => Writes.single .sumcheckRound (two repr side) (two_injective repr side)
  | .terminal side .. => Writes.single .sumcheckCross (one repr side) (one_injective repr side)
  | .combine side .. => Writes.single .sumcheckClaims (two repr side) (two_injective repr side)
  | .rowBatching => Writes.none
  | .conversion => Writes.single .splitOpening (one repr .prime) (one_injective repr .prime)
  | .packing => Writes.single .packingU (fieldElements repr .binary _ (shape_fits shape _ (by simp)))
      (fieldElements_injective repr .binary _ _)
  | .batching => packingAWrites repr
  | .opening => (responseWrites repr shape .binary).pair (responseWrites repr shape .prime)

theorem roleWrites_encodes (role : Role) :
    (roleWrites repr shape role).Encodes (TaggedFormat.roleCodec repr role) := by
  cases role with
  | fingerprint => exact Writes.none_encodes
  | inputAssertions => exact Writes.none_encodes
  | assertions => exact Writes.none_encodes
  | sumcheck side => exact Writes.single_encodes _ _ (two_injective repr side) _ (elementPair_grammar repr side)
  | terminal side => exact Writes.single_encodes _ _ (one_injective repr side) _ (element_grammar repr side)
  | combine side => exact Writes.single_encodes _ _ (two_injective repr side) _ (elementPair_grammar repr side)
  | rowBatching => exact Writes.none_encodes
  | conversion => exact Writes.single_encodes _ _ (one_injective repr .prime) _ (element_grammar repr .prime)
  | packing =>
      exact Writes.single_encodes .packingU _ (fieldElements_injective repr .binary _ _) _
        (elements_grammar repr .binary _ _)
  | batching => exact packingAWrites_encodes repr
  | opening =>
      exact Writes.pair_encodes _ _ _ _ (responseWrites_encodes repr shape .binary)
        (responseWrites_encodes repr shape .prime)

/-- The prover messages of boundary `i`. -/
def codecWrites (advice : AdviceGrammar repr) (i : Fin g.roles.length) :
    Writes (TaggedFormat.Data (fields := fields) (Advice := Advice) i) :=
  (startWrites repr advice (WireBlocks.startAt g i)).pair (roleWrites repr shape (g.roles.get i))

theorem codecWrites_encodes (advice : AdviceGrammar repr) (i : Fin g.roles.length) :
    (codecWrites repr shape advice i).Encodes (TaggedFormat.codec repr i) :=
  Writes.pair_encodes _ _ _ _ (startWrites_encodes repr advice _) (roleWrites_encodes repr shape _)

end Packets

/-! ## Nodes -/

/-- A node's payload: its messages and its terminator. -/
theorem encodeMessages_eq (messages : List Message) (terminal : Grammar.End) :
    Grammar.encodeMessages table registry messages terminal =
      messagesBytes messages ++ word terminal.code.val := rfl

/-- A node with a message is a `Grammar` node. -/
theorem encodeMessages_node (messages : List Message) (nonempty : messages ≠ []) (terminal : Grammar.End) :
    Grammar.encodeMessages table registry messages terminal =
      (Grammar.node table registry).encode ⟨messages,nonempty,terminal⟩ := rfl

section Later
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice) (shape : WireBlocks.Shape g fields)

/-- Every later node: the grammar messages of the boundary's packet, then
`ROUND`. -/
theorem later_node (advice : AdviceGrammar repr) (i : Fin g.roles.length)
    (value : TaggedFormat.Data (fields := fields) (Advice := Advice) i) (domain : Domain) :
    (TaggedFormat.codec repr i).encode value ++ TaggedFormat.wire.terminator domain =
      Grammar.encodeMessages table registry ((codecWrites repr shape advice i).messages value) .round := by
  rw [codecWrites_encodes repr shape advice i value]
  rfl

end Later

/-- The `Seal` message: one `Bytes` value, the whole body. -/
def sealMessage (body : BoundedBytes maxLength) : Message := ⟨.seal,(bytesOf body,())⟩

/-- The seal node: the `Seal` message, then `SEAL`. -/
theorem seal_node (body : BoundedBytes maxLength) :
    TaggedFormat.wire.sealFrame body.bytes = Grammar.encodeMessages table registry [sealMessage body] .seal := by
  rw [encodeMessages_eq,TaggedFormat.wire_sealFrame]
  change _ = word TaggedFormat.sealTag ++ ((Grammar.value table .bytes).encode (bytesOf body) ++ []) ++ [] ++ word 1
  rw [← bytesValue_grammar,bytesValue_encode]
  simp only [List.append_nil,List.append_assoc]
  rfl

section First
variable {Prime : Type} (prime : FieldCodec Prime)

theorem prime_fixed (primeWidth : prime.width = 32) (value : Prime) : ((PrefixCodec.field prime).encode value).length = width .prime :=
  (prime.length value).trans primeWidth

variable (primeWidth : prime.width = 32) (publicCount primeCount : ℕ) (publicFits : publicCount < 2^64)
  (primeFits : primeCount < 2^64)
include primeWidth publicFits primeFits

/-- The messages of node 0 after the setup's statement prefix: both
`PublicInputs` messages and the `Commitment`. -/
def keyMessages (key : TaggedFormat.Key publicCount primeCount Prime) : List Message :=
  [⟨.publicInputs,(elementsOf .binary TaggedFormat.bit TaggedFormat.bit_length publicCount publicFits
      key.publicBits,())⟩,
    ⟨.publicInputs,(elementsOf .prime (PrefixCodec.field prime) (prime_fixed prime primeWidth) primeCount
      primeFits key.primeInputs,())⟩,
    ⟨.commitment,(digestOf key.root,())⟩]

/-- The key's public values and root are determined by these messages. -/
theorem keyMessages_injective (first second : TaggedFormat.Key publicCount primeCount Prime)
    (same : keyMessages prime primeWidth publicCount primeCount publicFits primeFits first =
      keyMessages prime primeWidth publicCount primeCount publicFits primeFits second) :
    first.publicBits = second.publicBits ∧ first.primeInputs = second.primeInputs ∧ first.root = second.root := by
  simp only [keyMessages,List.cons.injEq,Sigma.mk.injEq,heq_eq_eq,and_true,true_and] at same
  exact ⟨elementsOf_injective _ _ _ _ publicFits (congrArg Prod.fst same.1),
    elementsOf_injective _ _ _ _ primeFits (congrArg Prod.fst same.2.1),digestOf_injective (congrArg Prod.fst same.2.2)⟩

/-- Node 0 before its terminator: the setup's statement prefix with the
session, then the grammar messages of the public inputs and the root. -/
theorem first_grammar (setup : TaggedFormat.Setup) (key : TaggedFormat.Key publicCount primeCount Prime) :
    (TaggedFormat.first setup prime publicCount primeCount).encode key =
      setup.head ++ bytesValue.encode key.session ++ setup.constants ++
        messagesBytes (keyMessages prime primeWidth publicCount primeCount publicFits primeFits key) := by
  rw [TaggedFormat.first_encode,TaggedCodec.elements,
    elementsOf_grammar .binary TaggedFormat.bit TaggedFormat.bit_length publicCount publicFits,
    elementsOf_grammar .prime _ (prime_fixed prime primeWidth) primeCount primeFits,digestValue_grammar]
  show _ = setup.head ++ bytesValue.encode key.session ++ setup.constants ++
    ((word TaggedFormat.publicInputsTag ++ ((Grammar.value table .elements).encode
        (elementsOf .binary TaggedFormat.bit TaggedFormat.bit_length publicCount publicFits key.publicBits) ++ [])) ++
      ((word TaggedFormat.publicInputsTag ++ ((Grammar.value table .elements).encode
          (elementsOf .prime (PrefixCodec.field prime) (prime_fixed prime primeWidth) primeCount primeFits
            key.primeInputs) ++ [])) ++
        ((word TaggedFormat.commitmentTag ++ ((Grammar.value table .bytes).encode (digestOf key.root) ++ [])) ++ [])))
  simp only [List.append_nil,List.append_assoc]

/-- Node 0. -/
theorem first_node (setup : TaggedFormat.Setup) (key : TaggedFormat.Key publicCount primeCount Prime)
    (domain : Domain) :
    (TaggedFormat.first setup prime publicCount primeCount).encode key ++ TaggedFormat.wire.terminator domain =
      setup.head ++ bytesValue.encode key.session ++ setup.constants ++
        Grammar.encodeMessages table registry
          (keyMessages prime primeWidth publicCount primeCount publicFits primeFits key) .round := by
  rw [first_grammar prime primeWidth publicCount primeCount publicFits primeFits,encodeMessages_eq,
    List.append_assoc]
  rfl

end First

/-! ## The mdoc quotients -/

theorem toBits_length (width value : ℕ) : (Grammar.toBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [Grammar.toBits,List.length_cons,ih]

theorem ofBits_toBits (width value : ℕ) : Grammar.ofBits (Grammar.toBits width value) = value % 2^width := by
  induction width generalizing value with
  | zero => simp only [Grammar.toBits,Grammar.ofBits,pow_zero,Nat.mod_one]
  | succ width ih =>
      simp only [Grammar.toBits,Grammar.ofBits,ih,pow_succ',Nat.mod_mul]
      have : (decide (value % 2 = 1)).toNat = value % 2 := by
        rcases Nat.mod_two_eq_zero_or_one value with h | h <;> simp [h]
      rw [this]

theorem take_toBits (low high value : ℕ) :
    (Grammar.toBits (low+high) value).take low = Grammar.toBits low value := by
  induction low generalizing value with
  | zero => rfl
  | succ low ih =>
      rw [show low+1+high = (low+high)+1 by omega]
      simp only [Grammar.toBits,List.take_succ_cons,ih]

theorem drop_toBits (low high value : ℕ) :
    (Grammar.toBits (low+high) value).drop low = Grammar.toBits high (value/2^low) := by
  induction low generalizing value with
  | zero => simp only [Nat.zero_add,List.drop_zero,pow_zero,Nat.div_one]
  | succ low ih =>
      rw [show low+1+high = (low+high)+1 by omega]
      simp only [Grammar.toBits,List.drop_succ_cons,ih,Nat.div_div_eq_div_mul,pow_succ']

/-- A ten-bit word's `Bits(10)` payload is its two little-endian bytes. -/
theorem pack_word (word : MdocAdvice.Word) :
    Grammar.pack (Grammar.byteCount 10) (Grammar.toBits 10 word.val) = encodeLE 2 word.val := by
  have hw := word.isLt
  have hcount : Grammar.byteCount 10 = 2 := rfl
  have hlow := take_toBits 8 2 word.val
  have hhigh := drop_toBits 8 2 word.val
  have hshort : (Grammar.toBits 2 (word.val/2^8)).take 8 = Grammar.toBits 2 (word.val/2^8) :=
    List.take_of_length_le (by rw [toBits_length]; omega)
  rw [hcount]
  simp only [Grammar.pack,Grammar.chunk,encodeLE,hlow,hhigh,hshort,ofBits_toBits]
  refine List.cons_eq_cons.mpr ⟨Fin.ext ?_,List.cons_eq_cons.mpr ⟨Fin.ext ?_,rfl⟩⟩
  · norm_num
  · simp only
    omega

def bitsOf (word : MdocAdvice.Word) : Grammar.Value table .bits :=
  ⟨Grammar.toBits 10 word.val,by rw [toBits_length]; decide⟩

theorem bitsOf_encode (word : MdocAdvice.Word) :
    (Grammar.value table .bits).encode (bitsOf word) = encodeLE 8 3 ++ encodeLE 8 10 ++ encodeLE 2 word.val := by
  rw [Grammar.bits_encode]
  simp only [bitsOf,Grammar.u64_encode,toBits_length]
  rw [pack_word]
  rfl

/-- The deployed mdoc advice writes are the `P256AdapterQuotients` schema:
two `Bits(10)` values. -/
def mdocAdvice {fields : Fields} (binary : FieldCodec (fields .binary)) (prime : FieldCodec (fields .prime))
    (binaryWidth : binary.width = 16) (primeWidth : prime.width = 32) :
    AdviceGrammar (MdocAdvice.representations binary prime binaryWidth primeWidth) where
  values advice := (bitsOf (advice 0),(bitsOf (advice 1),()))
  encodes advice := by
    change MdocAdvice.writes.encode advice =
      (Grammar.value table .bits).encode (bitsOf (advice 0)) ++
        ((Grammar.value table .bits).encode (bitsOf (advice 1)) ++ [])
    rw [MdocAdvice.writes_encode,bitsOf_encode,bitsOf_encode,List.append_nil]

/-! ## Deployed points

The injectivity of the deployed canonical points, from the grammar: a node's
payload determines its messages and terminator
(`Grammar.encodeMessages_injective`, which is `Grammar.nodes_injective` for
one node with a message), and the messages determine the packet value
(`Writes.injective`). The generic `Format.toPoint_injective` proves the same
by parsing with the packet codecs. -/

section Points
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice) (shape : WireBlocks.Shape g fields)

include shape in
/-- A later node's payload determines its packet value. -/
theorem later_injective (advice : AdviceGrammar repr) (i : Fin g.roles.length) (domain : Domain) :
    Function.Injective fun value : TaggedFormat.Data (fields := fields) (Advice := Advice) i =>
      (TaggedFormat.codec repr i).encode value ++ TaggedFormat.wire.terminator domain := by
  intro first second same
  have bytes : (TaggedFormat.codec repr i).encode first ++ TaggedFormat.wire.terminator domain =
      (TaggedFormat.codec repr i).encode second ++ TaggedFormat.wire.terminator domain := same
  rw [later_node repr shape advice,later_node repr shape advice] at bytes
  exact (codecWrites repr shape advice i).injective (Grammar.encodeMessages_injective table registry bytes).1

/-- Node 0's payload determines the key: the session through its `Bytes`
value after the setup's statement head, the rest through the grammar
messages after the setup constants. -/
theorem first_injective {Prime : Type} (setup : TaggedFormat.Setup) (prime : FieldCodec Prime)
    (primeWidth : prime.width = 32) (publicCount primeCount : ℕ) (publicFits : publicCount < 2^64)
    (primeFits : primeCount < 2^64) (domain : Domain) :
    Function.Injective fun key : TaggedFormat.Key publicCount primeCount Prime =>
      (TaggedFormat.first setup prime publicCount primeCount).encode key ++ TaggedFormat.wire.terminator domain := by
  intro first second same
  have bytes : (TaggedFormat.first setup prime publicCount primeCount).encode first ++
        TaggedFormat.wire.terminator domain =
      (TaggedFormat.first setup prime publicCount primeCount).encode second ++
        TaggedFormat.wire.terminator domain := same
  rw [first_node prime primeWidth publicCount primeCount publicFits primeFits,
    first_node prime primeWidth publicCount primeCount publicFits primeFits] at bytes
  simp only [List.append_assoc] at bytes
  have decoded := congrArg bytesValue.decode (List.append_cancel_left bytes)
  rw [bytesValue.inverse,bytesValue.inverse] at decoded
  obtain ⟨session,rest⟩ := Prod.mk.inj (Option.some.inj decoded)
  obtain ⟨bits,primes,root⟩ := keyMessages_injective prime primeWidth publicCount primeCount publicFits
    primeFits first second (Grammar.encodeMessages_injective table registry (List.append_cancel_left rest)).1
  cases first
  cases second
  cases session
  cases bits
  cases primes
  cases root
  rfl

/-- The seal node's payload determines the body. -/
theorem sealed_injective {Body : Type} (body : WholeCodec Body) :
    Function.Injective (TaggedFormat.wire.sealed body).encode := by
  intro first second same
  have bytes := (seal_node ⟨body.encode first.val,first.property⟩).symm.trans
    (((TaggedFormat.wire.sealed_encode body first).symm.trans same).trans
      ((TaggedFormat.wire.sealed_encode body second).trans (seal_node ⟨body.encode second.val,second.property⟩)))
  have message := List.head_eq_of_cons_eq (Grammar.encodeMessages_injective table registry bytes).1
  have payload := bytesOf_injective (congrArg Prod.fst (eq_of_heq (Sigma.mk.inj message).2))
  exact Subtype.ext (body.encode_injective (congrArg BoundedBytes.bytes payload))

variable (setup : TaggedFormat.Setup) (publicCount : ℕ)

/-- The deployed canonical points are injective, from the node grammar. -/
theorem toPoint_injective [Fintype (fields .prime)] [Inhabited Advice] (advice : AdviceGrammar repr)
    (publicFits : publicCount < 2^64) (primeFits : shape.primePublic < 2^64) :
    Function.Injective (TaggedFormat.format repr shape setup publicCount).toPoint := by
  intro first second same
  have histories := congrArg (StrandRuntime.history (TaggedFormat.format repr shape setup publicCount).wire
    (TaggedFormat.format repr shape setup publicCount).body) same
  rw [Format.toPoint_history,Format.toPoint_history] at histories
  have spines := congrArg TranscriptV2.Strand.History.spine histories
  simp only [Format.schema,StrandQueryCodec.schema,StrandQueryCodec.toHistory,
    TranscriptV2.Strand.History.spine_ofSpine,Prod.eta] at spines
  refine StrandQueryCodec.encode_injective _ _ _ ?_ (sealed_injective _) spines
  intro block mem
  simp only [Format.blocks,Format.packets,List.map_cons,List.mem_cons,List.mem_map] at mem
  rcases mem with rfl | ⟨packet,mem,rfl⟩
  · exact first_injective setup repr.prime repr.primeWidth publicCount shape.primePublic publicFits primeFits _
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_tail mem)
    exact later_injective repr shape advice i _

end Points

end LfzkV2.Current.TaggedGrammar
