import LfzkV2.Current.ProofBodyReplay

/-! Exact byte framing shared by every current query. Only bytes already
bound at the boundary occur here. Round indices and domains are actual wire
values; feedback contains the actual 32-byte answer prefix. -/
namespace LfzkV2.Current.CanonicalPrefix
open TranscriptV2.Framing (Byte encodeLE)
open scoped Classical

/-- The runtime writes one tag, one unsigned u64 byte count, and the payload. -/
def frame (payload : Bytes) : Bytes := [0] ++ encodeLE 8 payload.length ++ payload

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

theorem bytes_encode (value : BoundedBytes maxLength) : bytes.encode value = frame value.bytes := by
  simp only [bytes,PrefixCodec.equiv,bytesData,Equiv.coe_fn_symm_mk,PrefixCodec.schema,
    TranscriptV2.Framing.encodeValues,TranscriptV2.Framing.encode,frame,List.append_nil,
    List.cons_append,List.nil_append]

/-- UTF-8 is used only for the literal ASCII domain strings below. -/
def utf8 (text : String) : Bytes := text.toUTF8.data.toList.map fun value =>
  ⟨value.toNat,UInt8.toNat_lt _⟩

def sessionDomain : Bytes := utf8 "longfellow/transcript/v2"
def roundDomain : Bytes := utf8 "longfellow/transcript/v2/round"
def feedbackDomain : Bytes := utf8 "longfellow/transcript/v2/boundary-output"
def finalDomain : Bytes := utf8 "longfellow/transcript/v2/final"

def label (domain : Domain) : Byte := ⟨domain.tag.val,domain.tag.isLt.trans (by decide)⟩

def roundFooter (domain : Domain) (counter : Fin (2^64)) : Bytes :=
  frame roundDomain ++ frame [label domain] ++ frame (encodeLE 8 counter.val)

def finalFooter (counter : Fin (2^64)) : Bytes :=
  frame finalDomain ++ frame (encodeLE 8 counter.val)

/-- Digest framing is write_bytes, not a scalar-field operation. -/
def framedDigest : PrefixCodec Digest :=
  ProofBodyCodec.digest.prefixed ([0] ++ encodeLE 8 32)

theorem framedDigest_encode (value : Digest) : framedDigest.encode value = frame (List.ofFn value) := by
  simp only [framedDigest,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,
    PrefixCodec.marker,Equiv.coe_fn_symm_mk,ProofBodyCodec.digest,PrefixCodec.bytes_encode,
    frame,List.length_ofFn,List.append_assoc]

def feedback : PrefixCodec Digest := framedDigest.prefixed (frame feedbackDomain)

theorem feedback_encode (value : Digest) : feedback.encode value =
    frame feedbackDomain ++ frame (List.ofFn value) := by
  simp only [feedback,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,
    PrefixCodec.marker,Equiv.coe_fn_symm_mk,framedDigest_encode]

theorem feedback_nonempty (value : Digest) : feedback.encode value ≠ [] := by
  rw [feedback_encode]
  intro h
  cases h

/-- Session initialization precedes all bind-only and round operations. -/
def session : PrefixCodec (BoundedBytes maxLength) := bytes.prefixed (frame sessionDomain)


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

/-- Frame the actual canonical payload bytes. The u64 bound is explicit;
the parser rejects any unused bytes inside the framed payload. -/
def framed (codec : PrefixCodec A) :
    PrefixCodec {value // (codec.encode value).length ≤ maxLength} where
  encode value := bytes.encode ⟨codec.encode value.val,value.property⟩
  decode input := do
    let (payload,suffix) ← bytes.decode input
    match h : readWhole codec payload.bytes with
    | none => none
    | some value => some (⟨value,by
        rw [← readWhole_canonical codec payload.bytes value h]
        exact payload.bound⟩,suffix)
  inverse value suffix := by
    simp only [bytes.inverse,Option.bind_eq_bind,Option.bind_some]
    split
    · rename_i hn
      have hi := readWhole_encode codec value.val
      rw [hn] at hi
      contradiction
    · rename_i decoded hd
      have he : decoded = value.val := Option.some.inj (hd.symm.trans (readWhole_encode codec value.val))
      subst decoded
      rfl
  canonical input value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨payload,rest⟩,hp,h⟩ := h
    split at h
    · contradiction
    · rename_i decoded hd
      cases Option.some.inj h
      have he := readWhole_canonical codec payload.bytes decoded hd
      have hb : (codec.encode decoded).length ≤ maxLength := by rw [← he]; exact payload.bound
      have hs : payload = (⟨codec.encode decoded,hb⟩ : BoundedBytes maxLength) := BoundedBytes.ext he
      calc
        input = bytes.encode payload ++ rest := bytes.canonical input payload rest hp
        _ = bytes.encode ⟨codec.encode decoded,hb⟩ ++ rest := by rw [hs]
        _ = _ := rfl

theorem framed_encode (codec : PrefixCodec A)
    (value : {value // (codec.encode value).length ≤ maxLength}) :
    (framed codec).encode value = frame (codec.encode value.val) := bytes_encode _

end Payload

end LfzkV2.Current.CanonicalPrefix
