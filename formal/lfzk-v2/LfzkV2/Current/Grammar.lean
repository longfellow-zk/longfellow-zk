import LfzkV2.Current.ByteCodecs

/-! The node grammar of `rust/src/runtime/v2/transcript/DESIGN.md` (transcript
I5, I6), as prefix codecs. Every integer is a u64 little-endian word. A value
is a kind word, its count and its payload; a message is a tag of at least 16
followed by the values its schema fixes; a node is one or more messages and a
terminator, 0 (ROUND) or 1 (SEAL). Parsing needs only the registries, and a
concatenation of nodes is an injective encoding of its node sequence.

The deployed format, `TaggedFormat`, writes its nodes with the typed codecs
of `TaggedCodec`. `TaggedGrammar` proves that their bytes are this grammar
over the deployed registry, and `Tests.TaggedFormat` and `Tests.TaggedGrammar`
check the Rust vectors. -/
namespace LfzkV2.Current.Grammar
open TranscriptV2.Framing (Byte encodeLE take take_length_append take_sound)

/-- Every integer of the grammar: a count, a kind, a tag, a field ID or a
Nats entry. -/
abbrev Word := Fin (2^64)

def u64 : PrefixCodec Word := PrefixCodec.unsigned 8 (2^64) (by decide)

theorem u64_encode (word : Word) : u64.encode word = encodeLE 8 word.val := rfl

@[simp] theorem u64_length (word : Word) : (u64.encode word).length = 8 :=
  TranscriptV2.Framing.encodeLE_length 8 word.val

section Codecs
variable {A : Type} {B : A → Type}

/-- A first component that selects the codec of the second. A tag selects
its schema this way, and a field ID its element width. -/
def dependent (first : PrefixCodec A) (second : ∀ a, PrefixCodec (B a)) :
    PrefixCodec ((a : A) × B a) where
  encode value := first.encode value.1 ++ (second value.1).encode value.2
  decode bytes := do
    let (a,rest) ← first.decode bytes
    let (b,suffix) ← (second a).decode rest
    some (⟨a,b⟩,suffix)
  inverse value suffix := by
    simp only [List.append_assoc,first.inverse,Option.bind_eq_bind,Option.bind_some,
      (second value.1).inverse]
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨a,rest⟩,ha,⟨b,last⟩,hb,heq⟩ := h
    cases Option.some.inj heq
    change (second a).decode rest = some (b,last) at hb
    change bytes = (first.encode a ++ (second a).encode b) ++ last
    rw [first.canonical _ _ _ ha,(second a).canonical _ _ _ hb,List.append_assoc]

variable (codec : PrefixCodec A)

/-- Read exactly `count` consecutive values. -/
def readMany : ℕ → Bytes → Option (List A × Bytes)
  | 0, bytes => some ([],bytes)
  | count+1, bytes => do
      let (value,rest) ← codec.decode bytes
      let (values,suffix) ← readMany count rest
      some (value::values,suffix)

theorem readMany_encode (values : List A) (suffix : Bytes) :
    readMany codec values.length (values.flatMap codec.encode ++ suffix) = some (values,suffix) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readMany,codec.inverse,
        Option.bind_eq_bind,Option.bind_some,ih]

theorem readMany_sound (count : ℕ) (bytes : Bytes) (values : List A) (suffix : Bytes)
    (h : readMany codec count bytes = some (values,suffix)) :
    values.length = count ∧ bytes = values.flatMap codec.encode ++ suffix := by
  induction count generalizing bytes values with
  | zero =>
      simp only [readMany,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨rfl,rfl⟩
  | succ count ih =>
      simp only [readMany,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨⟨value,rest⟩,hv,⟨tail,last⟩,ht,heq⟩ := h
      cases Option.some.inj heq
      change readMany codec count rest = some (tail,last) at ht
      obtain ⟨hlength,hrest⟩ := ih rest tail ht
      refine ⟨by simp only [List.length_cons,hlength],?_⟩
      rw [codec.canonical _ _ _ hv,hrest,List.flatMap_cons,List.append_assoc]

/-- A u64 count followed by exactly that many values. -/
def many : PrefixCodec {values : List A // values.length < 2^64} where
  encode values := u64.encode ⟨values.val.length,values.property⟩ ++ values.val.flatMap codec.encode
  decode bytes := do
    let (count,rest) ← u64.decode bytes
    let (values,suffix) ← readMany codec count.val rest
    if h : values.length < 2^64 then some (⟨values,h⟩,suffix) else none
  inverse values suffix := by
    simp only [List.append_assoc,u64.inverse,Option.bind_eq_bind,Option.bind_some]
    rw [readMany_encode]
    simp only [Option.bind_some,dif_pos values.property]
  canonical bytes values suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨count,rest⟩,hc,⟨decoded,last⟩,hd,h⟩ := h
    change readMany codec count.val rest = some (decoded,last) at hd
    split at h
    next hb =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      obtain ⟨hlength,hrest⟩ := readMany_sound codec _ _ _ _ hd
      have hcount : count = ⟨decoded.length,hb⟩ := Fin.ext hlength.symm
      rw [u64.canonical _ _ _ hc,hrest,hcount,List.append_assoc]
    next => contradiction

end Codecs

section Bits

/-- Bits of a little-endian word, least significant first. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | width+1, value => decide (value % 2 = 1) :: toBits width (value/2)

def ofBits : List Bool → ℕ
  | [] => 0
  | bit::bits => bit.toNat + 2*ofBits bits

theorem ofBits_lt (bits : List Bool) : ofBits bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
      have : bit.toNat ≤ 1 := Bool.toNat_le bit
      simp only [ofBits,List.length_cons,pow_succ]
      omega

theorem toBits_zero (width : ℕ) : toBits width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [toBits,Nat.zero_mod,Nat.zero_div,ih,List.replicate_succ]; rfl

theorem toBits_ofBits (bits : List Bool) (width : ℕ) (fits : bits.length ≤ width) :
    toBits width (ofBits bits) = bits ++ List.replicate (width-bits.length) false := by
  induction bits generalizing width with
  | nil => simp only [ofBits,toBits_zero,List.nil_append,List.length_nil,Nat.sub_zero]
  | cons bit bits ih =>
      obtain ⟨width,rfl⟩ : ∃ w, width = w+1 := ⟨width-1,by simp only [List.length_cons] at fits; omega⟩
      simp only [List.length_cons] at fits
      have hmod : (bit.toNat + 2*ofBits bits) % 2 = bit.toNat := by
        cases bit <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
      have hdiv : (bit.toNat + 2*ofBits bits) / 2 = ofBits bits := by
        cases bit <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
      simp only [ofBits,toBits,hmod,hdiv,ih width (by omega),List.length_cons,List.cons_append,
        Nat.add_sub_add_right]
      cases bit <;> rfl

/-- One payload byte holds the next eight bits, least significant first. -/
def chunk (bits : List Bool) : Byte := ⟨ofBits (bits.take 8) % 256,Nat.mod_lt _ (by decide)⟩

theorem chunk_val (bits : List Bool) : (chunk bits).val = ofBits (bits.take 8) := by
  apply Nat.mod_eq_of_lt
  calc ofBits (bits.take 8) < 2^(bits.take 8).length := ofBits_lt _
    _ ≤ 2^8 := Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)

/-- `count` payload bytes; trailing bits of the last byte are zero. -/
def pack : ℕ → List Bool → Bytes
  | 0, _ => []
  | count+1, bits => chunk bits :: pack count (bits.drop 8)

def byteCount (count : ℕ) : ℕ := (count+7)/8

def unpack (count : ℕ) (payload : Bytes) : List Bool :=
  (payload.flatMap fun byte => toBits 8 byte.val).take count

@[simp] theorem pack_length (count : ℕ) (bits : List Bool) : (pack count bits).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [pack,List.length_cons,ih]

theorem pack_bits (count : ℕ) (bits : List Bool) (fits : bits.length ≤ 8*count) :
    (pack count bits).flatMap (fun byte => toBits 8 byte.val) =
      bits ++ List.replicate (8*count-bits.length) false := by
  induction count generalizing bits with
  | zero =>
      have : bits = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst bits
      rfl
  | succ count ih =>
      simp only [pack,List.flatMap_cons,chunk_val]
      rw [toBits_ofBits _ 8 (by simp only [List.length_take]; omega),
        ih _ (by simp only [List.length_drop]; omega)]
      by_cases long : 8 ≤ bits.length
      · have htake : (bits.take 8).length = 8 := by simp only [List.length_take]; omega
        rw [htake,Nat.sub_self,List.replicate_zero,List.append_nil,← List.append_assoc,
          List.take_append_drop,List.length_drop]
        congr 2
        omega
      · have hdrop : bits.drop 8 = [] := List.drop_eq_nil_of_le (by omega)
        have htake : bits.take 8 = bits := List.take_of_length_le (by omega)
        rw [hdrop,htake,List.nil_append,List.length_nil,Nat.sub_zero,List.append_assoc,
          ← List.replicate_add]
        congr 2
        omega

theorem unpack_pack (bits : List Bool) :
    unpack bits.length (pack (byteCount bits.length) bits) = bits := by
  unfold unpack
  rw [pack_bits _ _ (by unfold byteCount; omega)]
  exact List.take_left' rfl

/-- A u64 bit count and the packed bytes. The decoder rejects nonzero
padding, so every accepted byte string is the encoding of its value. -/
def bits : PrefixCodec {values : List Bool // values.length < 2^64} where
  encode values := u64.encode ⟨values.val.length,values.property⟩ ++
    pack (byteCount values.val.length) values.val
  decode bytes := do
    let (count,rest) ← u64.decode bytes
    let (payload,suffix) ← take (byteCount count.val) rest
    let values := unpack count.val payload
    if h : values.length < 2^64 ∧ values.length = count.val ∧
        pack (byteCount count.val) values = payload then
      some (⟨values,h.1⟩,suffix)
    else none
  inverse values suffix := by
    have ht := take_length_append (pack (byteCount values.val.length) values.val) suffix
    rw [pack_length] at ht
    simp only [List.append_assoc,u64.inverse,Option.bind_eq_bind,Option.bind_some,ht,
      unpack_pack,values.property,and_self,dif_pos]
  canonical bytes values suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨count,rest⟩,hc,⟨payload,last⟩,hp,h⟩ := h
    change take (byteCount count.val) rest = some (payload,last) at hp
    split at h
    next hv =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      change (unpack count.val payload).length < 2^64 ∧ (unpack count.val payload).length = count.val ∧
        pack (byteCount count.val) (unpack count.val payload) = payload at hv
      have hcount : count = ⟨(unpack count.val payload).length,hv.1⟩ := Fin.ext hv.2.1.symm
      rw [u64.canonical _ _ _ hc,(take_sound _ _ _ _ hp).2]
      calc u64.encode count ++ (payload ++ last)
          = u64.encode ⟨(unpack count.val payload).length,hv.1⟩ ++
              (pack (byteCount (unpack count.val payload).length) (unpack count.val payload) ++ last) := by
            rw [← hcount,hv.2.1,hv.2.2]
        _ = _ := (List.append_assoc _ _ _).symm
    next => contradiction

end Bits

/-- Element fields: a u64 field ID on the wire and a fixed element width
for each field. -/
structure FieldTable where
  Id : Type
  code : Id → Word
  ofCode : Word → Option Id
  ofCode_code : ∀ field, ofCode (code field) = some field
  code_ofCode : ∀ word field, ofCode word = some field → code field = word
  Element : Id → Type
  codec : ∀ field, TranscriptV2.Framing.FieldCodec (Element field)

namespace FieldTable
variable (fields : FieldTable)

def id : PrefixCodec fields.Id where
  encode field := u64.encode (fields.code field)
  decode bytes := do
    let (word,suffix) ← u64.decode bytes
    let field ← fields.ofCode word
    some (field,suffix)
  inverse field suffix := by
    simp only [u64.inverse,Option.bind_eq_bind,Option.bind_some,fields.ofCode_code]
  canonical bytes field suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨word,rest⟩,hw,decoded,hd,heq⟩ := h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [u64.canonical _ _ _ hw,fields.code_ofCode _ _ hd]

end FieldTable

/-- The four value kinds; there is no scalar kind. -/
inductive Kind where
  | bytes | nats | elements | bits
  deriving DecidableEq, Repr

def Kind.code : Kind → Word
  | .bytes => 0 | .nats => 1 | .elements => 2 | .bits => 3

abbrev Counted (A : Type) := {values : List A // values.length < 2^64}

variable (fields : FieldTable)

abbrev Value : Kind → Type
  | .bytes => Counted Byte
  | .nats => Counted Word
  | .elements => (field : fields.Id) × Counted (fields.Element field)
  | .bits => Counted Bool

/-- The payload of one value after its kind word. -/
def payload : (kind : Kind) → PrefixCodec (Value fields kind)
  | .bytes => many PrefixCodec.byte
  | .nats => many u64
  | .elements => dependent fields.id fun field => many (PrefixCodec.field (fields.codec field))
  | .bits => bits

/-- `kind count payload`, with the kind word checked against the schema. -/
def value (kind : Kind) : PrefixCodec (Value fields kind) :=
  (payload fields kind).prefixed (u64.encode kind.code)

/-- The values of one schema, in order. -/
abbrev Values : List Kind → Type
  | [] => Unit
  | kind::rest => Value fields kind × Values rest

def values : (schema : List Kind) → PrefixCodec (Values fields schema)
  | [] => PrefixCodec.unit
  | kind::rest => (value fields kind).pair (values rest)

/-! The bytes of each kind, as written in the design grammar. -/

theorem bytes_encode (payload : Counted Byte) :
    (value fields .bytes).encode payload =
      u64.encode 0 ++ u64.encode ⟨payload.val.length,payload.property⟩ ++ payload.val := by
  change u64.encode 0 ++ (u64.encode _ ++ payload.val.flatMap PrefixCodec.byte.encode) = _
  rw [show PrefixCodec.byte.encode = (fun byte => [byte]) by funext byte; exact PrefixCodec.byte_encode byte,
    List.flatMap_singleton',List.append_assoc]
  rfl

theorem nats_encode (words : Counted Word) :
    (value fields .nats).encode words =
      u64.encode 1 ++ u64.encode ⟨words.val.length,words.property⟩ ++ words.val.flatMap u64.encode := by
  change u64.encode 1 ++ (_ ++ _) = _
  rw [List.append_assoc]
  rfl

theorem elements_encode (field : fields.Id) (elements : Counted (fields.Element field)) :
    (value fields .elements).encode ⟨field,elements⟩ =
      u64.encode 2 ++ u64.encode (fields.code field) ++ u64.encode ⟨elements.val.length,elements.property⟩ ++
        elements.val.flatMap (fields.codec field).encode := by
  change u64.encode 2 ++ (u64.encode (fields.code field) ++ (_ ++ _)) = _
  simp only [List.append_assoc]
  rfl

theorem bits_encode (bits : Counted Bool) :
    (value fields .bits).encode bits =
      u64.encode 3 ++ u64.encode ⟨bits.val.length,bits.property⟩ ++
        pack (byteCount bits.val.length) bits.val := by
  change u64.encode 3 ++ (_ ++ _) = _
  rw [List.append_assoc]
  rfl

/-- The message registry: tags of at least 16 (0..15 are terminators), each
with one fixed list of value kinds (transcript I6). -/
structure Registry where
  Tag : Type
  code : Tag → Word
  ofCode : Word → Option Tag
  ofCode_code : ∀ tag, ofCode (code tag) = some tag
  code_ofCode : ∀ word tag, ofCode word = some tag → code tag = word
  reserved : ∀ tag, 16 ≤ (code tag).val
  schema : Tag → List Kind

namespace Registry
variable (registry : Registry)

def tag : PrefixCodec registry.Tag where
  encode tag := u64.encode (registry.code tag)
  decode bytes := do
    let (word,suffix) ← u64.decode bytes
    let tag ← registry.ofCode word
    some (tag,suffix)
  inverse tag suffix := by
    simp only [u64.inverse,Option.bind_eq_bind,Option.bind_some,registry.ofCode_code]
  canonical bytes tag suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨word,rest⟩,hw,decoded,hd,heq⟩ := h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [u64.canonical _ _ _ hw,registry.code_ofCode _ _ hd]

end Registry

variable (registry : Registry)

/-- A tag followed by the values of its schema. -/
abbrev Message := (tag : registry.Tag) × Values fields (registry.schema tag)

def message : PrefixCodec (Message fields registry) :=
  dependent registry.tag fun tag => values fields (registry.schema tag)

theorem message_encode (value : Message fields registry) :
    (message fields registry).encode value =
      u64.encode (registry.code value.1) ++ (values fields (registry.schema value.1)).encode value.2 := rfl

/-- The terminator ending a node. -/
inductive End where
  | round | seal
  deriving DecidableEq, Repr

def End.code : End → Word
  | .round => 0 | .seal => 1

def End.ofCode (word : Word) : Option End :=
  if word.val = 0 then some .round else if word.val = 1 then some .seal else none

def terminator : PrefixCodec End where
  encode terminal := u64.encode terminal.code
  decode bytes := do
    let (word,suffix) ← u64.decode bytes
    let terminal ← End.ofCode word
    some (terminal,suffix)
  inverse terminal suffix := by
    cases terminal <;> simp only [u64.inverse,Option.bind_eq_bind,Option.bind_some] <;> rfl
  canonical bytes terminal suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨word,rest⟩,hw,decoded,hd,heq⟩ := h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [u64.canonical _ _ _ hw]
    unfold End.ofCode at hd
    split at hd
    next h0 =>
      cases hd
      obtain rfl : word = 0 := Fin.ext h0
      rfl
    next =>
      split at hd
      next h1 =>
        cases hd
        obtain rfl : word = 1 := Fin.ext h1
        rfl
      next => contradiction

/-- A word below 16 ends the node; a message never starts with one. -/
theorem terminator_message (value : Message fields registry) (suffix : Bytes) :
    terminator.decode ((message fields registry).encode value ++ suffix) = none := by
  change terminator.decode ((u64.encode (registry.code value.1) ++ _) ++ suffix) = none
  have reserved := registry.reserved value.1
  simp only [terminator,List.append_assoc,u64.inverse,Option.bind_eq_bind,Option.bind_some,End.ofCode]
  rw [if_neg (by omega),if_neg (by omega)]
  rfl

theorem message_length (value : Message fields registry) :
    8 ≤ ((message fields registry).encode value).length := by
  change 8 ≤ (u64.encode (registry.code value.1) ++ _).length
  simp only [List.length_append,u64_length]
  omega

/-- One strand node payload (transcript I7): at least one message, then
its terminator. -/
structure Node where
  messages : List (Message fields registry)
  nonempty : messages ≠ []
  terminal : End

/-- Read messages until a terminator. The fuel only bounds the recursion;
every message consumes at least eight bytes. -/
def readMessages : ℕ → Bytes → Option (List (Message fields registry) × End × Bytes)
  | 0, _ => none
  | fuel+1, bytes =>
      match terminator.decode bytes with
      | some (terminal,suffix) => some ([],terminal,suffix)
      | none => do
          let (first,rest) ← (message fields registry).decode bytes
          let (later,terminal,suffix) ← readMessages fuel rest
          some (first::later,terminal,suffix)

def encodeMessages (messages : List (Message fields registry)) (terminal : End) : Bytes :=
  messages.flatMap (message fields registry).encode ++ terminator.encode terminal

theorem readMessages_encode (messages : List (Message fields registry)) (terminal : End)
    (suffix : Bytes) (fuel : ℕ) (enough : messages.length < fuel) :
    readMessages fields registry fuel (encodeMessages fields registry messages terminal ++ suffix) =
      some (messages,terminal,suffix) := by
  induction messages generalizing fuel with
  | nil =>
      obtain ⟨fuel,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by simp only [List.length_nil] at enough; omega⟩
      simp only [encodeMessages,List.flatMap_nil,List.nil_append,readMessages,terminator.inverse]
  | cons first later ih =>
      obtain ⟨fuel,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by simp only [List.length_cons] at enough; omega⟩
      simp only [encodeMessages,List.flatMap_cons,List.append_assoc,readMessages]
      rw [terminator_message,(message fields registry).inverse]
      simp only [Option.bind_eq_bind,Option.bind_some]
      have := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp only [encodeMessages,List.append_assoc] at this
      rw [this]
      rfl

theorem readMessages_sound (fuel : ℕ) (bytes : Bytes) (messages : List (Message fields registry))
    (terminal : End) (suffix : Bytes)
    (h : readMessages fields registry fuel bytes = some (messages,terminal,suffix)) :
    bytes = encodeMessages fields registry messages terminal ++ suffix := by
  induction fuel generalizing bytes messages with
  | zero => cases h
  | succ fuel ih =>
      simp only [readMessages] at h
      split at h
      next terminal' rest ht =>
        cases Option.some.inj h
        simpa only [encodeMessages,List.flatMap_nil,List.nil_append] using
          terminator.canonical _ _ _ ht
      next =>
        simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
        obtain ⟨⟨first,rest⟩,hf,⟨later,terminal',last⟩,hl,heq⟩ := h
        change readMessages fields registry fuel rest = some (later,terminal',last) at hl
        cases Option.some.inj heq
        rw [(message fields registry).canonical _ _ _ hf,ih _ _ hl]
        simp only [encodeMessages,List.flatMap_cons,List.append_assoc]

/-- `node := message+ end`. -/
def node : PrefixCodec (Node fields registry) where
  encode node := encodeMessages fields registry node.messages node.terminal
  decode bytes := do
    let (messages,terminal,suffix) ← readMessages fields registry (bytes.length+1) bytes
    if h : messages ≠ [] then some (⟨messages,h,terminal⟩,suffix) else none
  inverse node suffix := by
    rw [readMessages_encode]
    · simp only [Option.bind_eq_bind,Option.bind_some,dif_pos node.nonempty]
    · have hlength : node.messages.length*8 ≤ (node.messages.flatMap (message fields registry).encode).length := by
        rw [List.length_flatMap]
        clear suffix
        induction node.messages with
        | nil => simp
        | cons first later ih =>
            simp only [List.length_cons,List.map_cons,List.sum_cons]
            have := message_length fields registry first
            omega
      simp only [encodeMessages,List.length_append]
      omega
  canonical bytes node suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨messages,terminal,last⟩,hm,h⟩ := h
    split at h
    next hn =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      exact readMessages_sound fields registry _ _ _ _ _ hm
    next => contradiction

theorem node_encode (value : Node fields registry) :
    (node fields registry).encode value =
      value.messages.flatMap (message fields registry).encode ++ u64.encode value.terminal.code := rfl

theorem node_nonempty (value : Node fields registry) : (node fields registry).encode value ≠ [] := by
  intro h
  have := congrArg List.length h
  change (encodeMessages fields registry value.messages value.terminal).length = 0 at this
  simp only [encodeMessages,List.length_append,terminator,u64_length] at this
  omega

/-- A prefix codec with nonempty encodings is injective on concatenations. -/
theorem flatMap_injective {A : Type} (codec : PrefixCodec A) (nonempty : ∀ value, codec.encode value ≠ []) :
    Function.Injective fun values : List A => values.flatMap codec.encode := by
  intro first second h
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons value _ =>
          exact absurd (List.append_eq_nil_iff.mp h.symm).1 (nonempty value)
  | cons value rest ih =>
      cases second with
      | nil => exact absurd (List.append_eq_nil_iff.mp h).1 (nonempty value)
      | cons other later =>
          simp only [List.flatMap_cons] at h
          have hd := congrArg codec.decode h
          rw [codec.inverse,codec.inverse] at hd
          obtain ⟨rfl,hrest⟩ := Prod.mk.inj (Option.some.inj hd)
          rw [ih hrest]

/-- The transcript payloads of a strand chain, concatenated, determine the
whole sequence of messages and boundaries. -/
theorem nodes_injective :
    Function.Injective fun nodes : List (Node fields registry) => nodes.flatMap (node fields registry).encode :=
  flatMap_injective _ (node_nonempty fields registry)

end LfzkV2.Current.Grammar
