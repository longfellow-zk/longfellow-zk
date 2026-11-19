import LfzkV2.Current.ProofBodyCodec
import LfzkV2.Current.BodyEncoding

/-! Canonical codecs for typed request and proof packets. Only data already
bound at the boundary occur here. Physical digest-linked nodes and PRF inputs
are defined in TranscriptV2.Strand*; the exact raw-oracle connection is proved
by the current soundness transport. -/
namespace LfzkV2.Current.CanonicalPrefix
open TranscriptV2.Framing (Byte encodeLE)
open scoped Classical

/-- The runtime writes one tag, one unsigned u64 byte count, and the payload. -/
def frame (payload : Bytes) : Bytes := [0] ++ encodeLE 8 payload.length ++ payload

@[simp] theorem frame_length (payload : Bytes) : (frame payload).length = 9+payload.length := by
  simp only [frame,List.length_append,List.length_singleton,TranscriptV2.Framing.encodeLE_length]

def maxLength : ℕ := 2^64-1

private abbrev NoFields (_ : Empty) := PEmpty
private def noCodecs (index : Empty) : TranscriptV2.Framing.FieldCodec (NoFields index) := nomatch index

private def bytesData :
    {value : TranscriptV2.Framing.Values NoFields [.bytes] //
      TranscriptV2.Framing.ValidValues NoFields [.bytes] value} ≃ BoundedBytes maxLength where
  toFun value := ⟨value.val.1,by
    have h := value.property.1
    change value.val.1.length < 2^64 at h
    dsimp [maxLength]
    omega⟩
  invFun value := ⟨(value.bytes,()),by
    refine ⟨?_,trivial⟩
    have h := value.bound
    change value.bytes.length < 2^64
    dsimp [maxLength] at h
    omega⟩
  left_inv value := by rcases value with ⟨⟨bytes,⟨⟩⟩,h⟩; rfl
  right_inv value := by cases value; rfl

/-- The u64 validity bound makes the existing byte operation canonical. -/
def bytes : PrefixCodec (BoundedBytes maxLength) :=
  (PrefixCodec.schema NoFields noCodecs [.bytes]).equiv bytesData

/-- UTF-8 is used only for literal ASCII domain strings. -/
def utf8 (text : String) : Bytes := text.toUTF8.data.toList.map fun value =>
  ⟨value.toNat,UInt8.toNat_lt _⟩

section Payload
variable {A : Type}

/-- A whole payload must consume its complete byte slice. Prefix parsing
alone would identify an encoding with the same encoding plus ignored bytes. -/
def readWhole (codec : PrefixCodec A) (input : Bytes) : Option A := do
  let (value,rest) ← codec.decode input
  if rest = [] then some value else none

theorem readWhole_encode (codec : PrefixCodec A) (value : A) :
    readWhole codec (codec.encode value) = some value := by
  have hi := codec.inverse value []
  simp only [List.append_nil] at hi
  simp [readWhole,hi]

theorem readWhole_canonical (codec : PrefixCodec A) (input : Bytes) (value : A)
    (h : readWhole codec input = some value) : input = codec.encode value := by
  simp only [readWhole,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨decoded,rest⟩,hd,h⟩ := h
  split at h
  · rename_i hr
    cases Option.some.inj h
    change rest = [] at hr
    simpa only [hr,List.append_nil] using codec.canonical input decoded rest hd
  · contradiction


/-- A codec for a whole input, with no suffix: the encoding of a value
that is the last field of its frame, such as a proof body before its seal
block. -/
structure _root_.LfzkV2.Current.WholeCodec (A : Type) where
  encode : A → Bytes
  decode : Bytes → Option A
  inverse : ∀ value, decode (encode value) = some value
  canonical : ∀ input value, decode input = some value → input = encode value

/-- A prefix codec read on a whole input. -/
def _root_.LfzkV2.Current.PrefixCodec.whole (codec : PrefixCodec A) : WholeCodec A where
  encode := codec.encode
  decode := readWhole codec
  inverse := readWhole_encode codec
  canonical := readWhole_canonical codec

instance : Coe (PrefixCodec A) (WholeCodec A) := ⟨PrefixCodec.whole⟩

@[simp] theorem _root_.LfzkV2.Current.PrefixCodec.whole_encode (codec : PrefixCodec A) :
    codec.whole.encode = codec.encode := rfl

theorem _root_.LfzkV2.Current.WholeCodec.encode_injective (codec : WholeCodec A) :
    Function.Injective codec.encode := by
  intro first second same
  have decoded := congrArg codec.decode same
  rw [codec.inverse,codec.inverse] at decoded
  exact Option.some.inj decoded

end Payload

end LfzkV2.Current.CanonicalPrefix
