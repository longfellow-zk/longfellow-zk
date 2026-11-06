import TranscriptV2.FramingSound

/-! Fixed public schemas have a finite byte bound even when payload counts
vary. This supports bounded raw blocks without introducing serialized padding. -/
namespace TranscriptV2.Framing

def maxFrameBytes : ℕ := 9+128*(2^64-1)

variable {Index : Type} (Field : Index → Type) (codecs : ∀ i, FieldCodec (Field i))

theorem byteLength_le (kind : Kind Index) (value : Value Field kind)
    (h : Valid Field kind value) : byteLength Field codecs kind value ≤ maxFrameBytes := by
  cases kind with
  | bytes =>
      change value.length < 2^64 at h
      change 9+value.length ≤ 9+128*(2^64-1)
      omega
  | scalar field =>
      have hwidth := (codecs field).buffer
      change 1+(codecs field).width ≤ 9+128*(2^64-1)
      omega
  | slice field =>
      change value.length < 2^64 at h
      have hcount : value.length ≤ 2^64-1 := by omega
      have hp := Nat.mul_le_mul hcount (codecs field).buffer
      change 9+value.length*(codecs field).width ≤ 9+128*(2^64-1)
      omega

theorem encodeValues_length_le (schema : List (Kind Index)) (values : Values Field schema)
    (h : ValidValues Field schema values) :
    (encodeValues Field codecs schema values).length ≤ schema.length*maxFrameBytes := by
  rw [encodeValues_length]
  induction schema with
  | nil => simp only [valuesByteLength,List.length_nil,Nat.zero_mul,le_refl]
  | cons kind rest ih =>
      have hhead := byteLength_le Field codecs kind values.1 h.1
      have htail := ih values.2 h.2
      simp only [valuesByteLength,List.length_cons,Nat.succ_mul]
      omega

end TranscriptV2.Framing
