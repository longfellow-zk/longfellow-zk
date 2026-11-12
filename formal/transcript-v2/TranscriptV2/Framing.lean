import Mathlib.Tactic.NormNum

/-! Canonical framing of the existing Rust v2 writer. Bytes are unsigned
values below 256. A fixed public schema determines the field and its width;
field identity is not an additional serialized scalar tag. The inverse laws
below apply to valid schema values, whose byte/slice lengths fit in u64. -/
namespace TranscriptV2.Framing

abbrev Byte := Fin 256
abbrev Bytes := List Byte

def encodeLE : ℕ → ℕ → Bytes
  | 0, _ => []
  | width+1, value => ⟨value % 256,Nat.mod_lt _ (by decide)⟩ :: encodeLE width (value/256)

def readLE : ℕ → Bytes → Option (ℕ × Bytes)
  | 0, bytes => some (0,bytes)
  | _+1, [] => none
  | width+1, byte::bytes => do
      let (value,rest) ← readLE width bytes
      some (byte.val+256*value,rest)

@[simp] theorem encodeLE_length (width value : ℕ) : (encodeLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [encodeLE,List.length_cons,ih]

/-- A u64 length is precisely eight little-endian bytes. The bound excludes
the truncation performed by a cast of an oversized host length. -/
theorem readLE_encode_append (width value : ℕ) (suffix : Bytes) (h : value < 256^width) :
    readLE width (encodeLE width value ++ suffix) = some (value,suffix) := by
  induction width generalizing value with
  | zero =>
      have hv : value = 0 := by simpa only [pow_zero,Nat.lt_one_iff] using h
      subst value
      rfl
  | succ width ih =>
      have hdiv : value/256 < 256^width := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa only [pow_succ,Nat.mul_comm] using h
      simp only [encodeLE,List.cons_append,readLE,ih _ hdiv,Option.bind_eq_bind,Option.bind_some]
      rw [Nat.mod_add_div]

/-- The parser consumes no byte following the requested fixed-width block. -/
def take : ℕ → Bytes → Option (Bytes × Bytes)
  | 0, bytes => some ([],bytes)
  | _+1, [] => none
  | width+1, byte::bytes => do
      let (head,rest) ← take width bytes
      some (byte::head,rest)

@[simp] theorem take_length_append (payload suffix : Bytes) :
    take payload.length (payload ++ suffix) = some (payload,suffix) := by
  induction payload with
  | nil => rfl
  | cons byte bytes ih => simp only [List.length_cons,List.cons_append,take,ih,Option.bind_eq_bind,Option.bind_some]

/-- These are the fixed public representation laws used by the Rust field
writer. The 128-byte limit is its serialization buffer size. -/
structure FieldCodec (F : Type) where
  width : ℕ
  positive : 0 < width
  buffer : width ≤ 128
  encode : F → Bytes
  decode : Bytes → Option F
  length : ∀ value, (encode value).length = width
  inverse : ∀ value, decode (encode value) = some value
  canonical : ∀ payload value, decode payload = some value → encode value = payload

namespace FieldCodec
variable {F : Type} (codec : FieldCodec F)

theorem encode_injective : Function.Injective codec.encode := by
  intro first second h
  have hd := congrArg codec.decode h
  simpa only [codec.inverse,Option.some.injEq] using hd

def read (bytes : Bytes) : Option (F × Bytes) := do
  let (payload,rest) ← take codec.width bytes
  let value ← codec.decode payload
  some (value,rest)

theorem read_encode_append (value : F) (suffix : Bytes) :
    codec.read (codec.encode value ++ suffix) = some (value,suffix) := by
  unfold read
  rw [← codec.length value,take_length_append]
  simp only [Option.bind_eq_bind,Option.bind_some,codec.inverse]

def encodeSlice : List F → Bytes
  | [] => []
  | value::values => codec.encode value ++ encodeSlice values

def readSlice : ℕ → Bytes → Option (List F × Bytes)
  | 0, bytes => some ([],bytes)
  | count+1, bytes => do
      let (value,rest) ← codec.read bytes
      let (values,last) ← readSlice count rest
      some (value::values,last)

theorem readSlice_encode_append (values : List F) (suffix : Bytes) :
    codec.readSlice values.length (codec.encodeSlice values ++ suffix) = some (values,suffix) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [encodeSlice,List.length_cons,List.append_assoc,readSlice,
        codec.read_encode_append,Option.bind_eq_bind,Option.bind_some,ih]

@[simp] theorem encodeSlice_length (values : List F) :
    (codec.encodeSlice values).length = values.length*codec.width := by
  induction values with
  | nil => simp only [encodeSlice,List.length_nil,Nat.zero_mul]
  | cons value values ih =>
      simp only [encodeSlice,List.length_append,codec.length,ih,List.length_cons,Nat.succ_mul]
      omega

end FieldCodec

/-- A public operation schema fixes the scalar/slice field. A byte frame,
scalar frame and slice frame carry exactly Rust's tags 0, 1 and 2. -/
inductive Kind (Index : Type) where
  | bytes
  | scalar (field : Index)
  | slice (field : Index)

variable {Index : Type} (Field : Index → Type) (codecs : ∀ i, FieldCodec (Field i))

abbrev Value : Kind Index → Type
  | .bytes => Bytes
  | .scalar field => Field field
  | .slice field => List (Field field)

def Valid : (kind : Kind Index) → Value Field kind → Prop
  | .bytes, payload => payload.length < 2^64
  | .scalar _, _ => True
  | .slice _, values => values.length < 2^64

def encode : (kind : Kind Index) → Value Field kind → Bytes
  | .bytes, payload => 0 :: (encodeLE 8 payload.length ++ payload)
  | .scalar field, value => 1 :: (codecs field).encode value
  | .slice field, values => 2 :: (encodeLE 8 values.length ++ (codecs field).encodeSlice values)

def decode : (kind : Kind Index) → Bytes → Option (Value Field kind × Bytes)
  | .bytes, 0::bytes => do
      let (length,rest) ← readLE 8 bytes
      take length rest
  | .scalar field, 1::bytes => (codecs field).read bytes
  | .slice field, 2::bytes => do
      let (length,rest) ← readLE 8 bytes
      (codecs field).readSlice length rest
  | _, _ => none

/-- Canonical framed payloads decode in front of any continuation. No end
marker or external delimiter is needed between ordinary writer calls. -/
theorem decode_encode_append (kind : Kind Index) (value : Value Field kind) (suffix : Bytes)
    (h : Valid Field kind value) :
    decode Field codecs kind (encode Field codecs kind value ++ suffix) = some (value,suffix) := by
  cases kind with
  | bytes =>
      change value.length < 2^64 at h
      have hlength : value.length < 256^8 := by simpa only [show 256^8 = 2^64 by norm_num] using h
      simp only [encode,List.cons_append,List.append_assoc,decode,
        readLE_encode_append 8 value.length _ hlength,Option.bind_eq_bind,Option.bind_some,take_length_append]
  | scalar field => exact (codecs field).read_encode_append value suffix
  | slice field =>
      change value.length < 2^64 at h
      have hlength : value.length < 256^8 := by simpa only [show 256^8 = 2^64 by norm_num] using h
      simp only [encode,List.cons_append,List.append_assoc,decode,
        readLE_encode_append 8 value.length _ hlength,Option.bind_eq_bind,Option.bind_some,
        (codecs field).readSlice_encode_append]

/-- Exact sizes of the three existing Rust frames, including their tags and
length words. Variable payload sizes remain explicit. -/
def byteLength : (kind : Kind Index) → Value Field kind → ℕ
  | .bytes, payload => 9+payload.length
  | .scalar field, _ => 1+(codecs field).width
  | .slice field, values => 9+values.length*(codecs field).width

theorem encode_length (kind : Kind Index) (value : Value Field kind) :
    (encode Field codecs kind value).length = byteLength Field codecs kind value := by
  cases kind <;> simp only [encode,byteLength,List.length_cons,List.length_append,
    encodeLE_length,FieldCodec.length,FieldCodec.encodeSlice_length] <;> omega

/-- A heterogeneous list of public writer operations. -/
def Values : List (Kind Index) → Type
  | [] => Unit
  | kind::rest => Value Field kind × Values rest

def ValidValues : (schema : List (Kind Index)) → Values Field schema → Prop
  | [], _ => True
  | kind::rest, values => Valid Field kind values.1 ∧ ValidValues rest values.2

def encodeValues : (schema : List (Kind Index)) → Values Field schema → Bytes
  | [], _ => []
  | kind::rest, values => encode Field codecs kind values.1 ++ encodeValues rest values.2

def decodeValues : (schema : List (Kind Index)) → Bytes → Option (Values Field schema × Bytes)
  | [], bytes => some ((),bytes)
  | kind::rest, bytes => do
      let (value,remaining) ← decode Field codecs kind bytes
      let (values,suffix) ← decodeValues rest remaining
      some ((value,values),suffix)

/-- The complete fixed schema can be read in front of any subsequent byte
stream. This gives both concatenation boundaries and ordinary prefix reads. -/
theorem decodeValues_encode_append (schema : List (Kind Index)) (values : Values Field schema)
    (suffix : Bytes) (h : ValidValues Field schema values) :
    decodeValues Field codecs schema (encodeValues Field codecs schema values ++ suffix) =
      some (values,suffix) := by
  induction schema with
  | nil => cases values; rfl
  | cons kind rest ih =>
      rcases values with ⟨value,values⟩
      simp only [ValidValues] at h
      simp only [encodeValues,List.append_assoc,decodeValues,Option.bind_eq_bind]
      rw [decode_encode_append Field codecs kind value _ h.1]
      simp only [Option.bind_some]
      rw [ih values h.2]
      rfl

/-- Fixed-schema encoding is injective on the valid values that the writer
can emit. No injectivity claim is made across unrelated field schemas. -/
theorem encodeValues_eq (schema : List (Kind Index)) (first second : Values Field schema)
    (hf : ValidValues Field schema first) (hs : ValidValues Field schema second)
    (h : encodeValues Field codecs schema first = encodeValues Field codecs schema second) :
    first = second := by
  have hfirst := decodeValues_encode_append Field codecs schema first [] hf
  have hsecond := decodeValues_encode_append Field codecs schema second [] hs
  rw [h] at hfirst
  exact congrArg Prod.fst (Option.some.inj (hfirst.symm.trans hsecond))

def appendValues : (first second : List (Kind Index)) → Values Field first → Values Field second →
    Values Field (first ++ second)
  | [], _, _, right => right
  | _::rest, second, left, right => (left.1,appendValues rest second left.2 right)

theorem encodeValues_append (first second : List (Kind Index))
    (left : Values Field first) (right : Values Field second) :
    encodeValues Field codecs (first ++ second) (appendValues Field first second left right) =
      encodeValues Field codecs first left ++ encodeValues Field codecs second right := by
  induction first with
  | nil => rfl
  | cons kind rest ih =>
      rcases left with ⟨value,values⟩
      simp only [List.cons_append,appendValues,encodeValues,ih,List.append_assoc]

theorem validValues_append (first second : List (Kind Index))
    (left : Values Field first) (right : Values Field second)
    (hl : ValidValues Field first left) (hr : ValidValues Field second right) :
    ValidValues Field (first ++ second) (appendValues Field first second left right) := by
  induction first with
  | nil => exact hr
  | cons kind rest ih => exact ⟨hl.1,ih left.2 hl.2⟩

def valuesByteLength : (schema : List (Kind Index)) → Values Field schema → ℕ
  | [], _ => 0
  | kind::rest, values => byteLength Field codecs kind values.1 + valuesByteLength rest values.2

theorem encodeValues_length (schema : List (Kind Index)) (values : Values Field schema) :
    (encodeValues Field codecs schema values).length = valuesByteLength Field codecs schema values := by
  induction schema with
  | nil => rfl
  | cons kind rest ih =>
      simp only [encodeValues,List.length_append,encode_length,valuesByteLength,ih]

end TranscriptV2.Framing
