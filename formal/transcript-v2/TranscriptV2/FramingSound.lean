import TranscriptV2.Framing

/-! Successful frame parsing recovers the exact consumed bytes. Together
with the prefix inverse, this gives canonical parsing on a fixed public
schema, including variable byte strings and counted field slices. -/
namespace TranscriptV2.Framing

/-- Every complete little-endian word is canonical and within its width. -/
theorem readLE_sound (width : ℕ) (bytes : Bytes) (value : ℕ) (suffix : Bytes)
    (h : readLE width bytes = some (value,suffix)) :
    value < 256^width ∧ bytes = encodeLE width value ++ suffix := by
  induction width generalizing bytes value with
  | zero =>
      simp only [readLE,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨by decide,rfl⟩
  | succ width ih =>
      cases bytes with
      | nil => simp only [readLE,reduceCtorEq] at h
      | cons byte bytes =>
          cases hr : readLE width bytes with
          | none => simp only [readLE,hr,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at h
          | some pair =>
              rcases pair with ⟨decoded,remaining⟩
              simp only [readLE,hr,Option.bind_eq_bind,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              obtain ⟨hbound,hbytes⟩ := ih bytes decoded hr
              constructor
              · simp only [pow_succ]
                have := byte.isLt
                omega
              · have hmod : (byte.val+256*decoded)%256 = byte.val := by have := byte.isLt; omega
                have hdiv : (byte.val+256*decoded)/256 = decoded := by have := byte.isLt; omega
                have hbyte : (⟨(byte.val+256*decoded)%256,Nat.mod_lt _ (by decide)⟩ : Byte) = byte :=
                  Fin.ext hmod
                simp only [encodeLE,hdiv,List.cons_append,hbyte]
                exact congrArg (List.cons byte) hbytes

theorem take_sound (width : ℕ) (bytes payload suffix : Bytes)
    (h : take width bytes = some (payload,suffix)) :
    payload.length = width ∧ bytes = payload ++ suffix := by
  induction width generalizing bytes payload with
  | zero =>
      simp only [take,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  | succ width ih =>
      cases bytes with
      | nil => simp only [take,reduceCtorEq] at h
      | cons byte bytes =>
          cases hr : take width bytes with
          | none => simp only [take,hr,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at h
          | some pair =>
              rcases pair with ⟨head,remaining⟩
              simp only [take,hr,Option.bind_eq_bind,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              obtain ⟨hwidth,hbytes⟩ := ih bytes head hr
              exact ⟨congrArg (·+1) hwidth,congrArg (List.cons byte) hbytes⟩

namespace FieldCodec
variable {F : Type} (codec : FieldCodec F)

theorem read_sound (bytes : Bytes) (value : F) (suffix : Bytes)
    (h : codec.read bytes = some (value,suffix)) :
    bytes = codec.encode value ++ suffix := by
  simp only [read,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨payload,remaining⟩,hpayload,actual,hactual,hresult⟩ := h
  cases Option.some.inj hresult
  have hs := (take_sound codec.width bytes payload remaining hpayload).2
  rw [← codec.canonical payload value hactual] at hs
  exact hs

theorem readSlice_sound (count : ℕ) (bytes : Bytes) (values : List F) (suffix : Bytes)
    (h : codec.readSlice count bytes = some (values,suffix)) :
    values.length = count ∧ bytes = codec.encodeSlice values ++ suffix := by
  induction count generalizing bytes values with
  | zero =>
      simp only [readSlice,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  | succ count ih =>
      simp only [readSlice,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨⟨head,remaining⟩,hhead,⟨tail,last⟩,htail,hresult⟩ := h
      cases Option.some.inj hresult
      obtain ⟨hcount,hbytes⟩ := ih remaining tail htail
      constructor
      · exact congrArg (·+1) hcount
      · rw [codec.read_sound bytes head remaining hhead,hbytes]
        simp only [encodeSlice,List.append_assoc]

end FieldCodec

variable {Index : Type} (Field : Index → Type) (codecs : ∀ i, FieldCodec (Field i))

/-- A successful frame parser recognizes the canonical encoded prefix,
and the actual decoded byte/slice count fits the u64 length word. -/
theorem decode_sound (kind : Kind Index) (bytes : Bytes) (value : Value Field kind) (suffix : Bytes)
    (h : decode Field codecs kind bytes = some (value,suffix)) :
    Valid Field kind value ∧ bytes = encode Field codecs kind value ++ suffix := by
  cases kind with
  | bytes =>
      cases bytes with
      | nil => simp only [decode,reduceCtorEq] at h
      | cons tag bytes =>
          by_cases htag : tag = 0
          · subst tag
            simp only [decode,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
            obtain ⟨⟨length,remaining⟩,hlength,htake⟩ := h
            obtain ⟨hbound,hbytes⟩ := readLE_sound 8 bytes length remaining hlength
            obtain ⟨hwidth,hpayload⟩ := take_sound length remaining value suffix htake
            constructor
            · change value.length < 2^64
              rw [hwidth]
              simpa only [show 256^8 = 2^64 by norm_num] using hbound
            · rw [hbytes,hpayload]
              simp only [encode,List.cons_append,List.append_assoc,hwidth]
          · simp [decode,htag] at h
  | scalar field =>
      cases bytes with
      | nil => simp only [decode,reduceCtorEq] at h
      | cons tag bytes =>
          by_cases htag : tag = 1
          · subst tag
            have hs := (codecs field).read_sound bytes value suffix h
            exact ⟨trivial,congrArg (List.cons 1) hs⟩
          · simp [decode,htag] at h
  | slice field =>
      cases bytes with
      | nil => simp only [decode,reduceCtorEq] at h
      | cons tag bytes =>
          by_cases htag : tag = 2
          · subst tag
            simp only [decode,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
            obtain ⟨⟨length,remaining⟩,hlength,hslice⟩ := h
            obtain ⟨hbound,hbytes⟩ := readLE_sound 8 bytes length remaining hlength
            obtain ⟨hcount,hpayload⟩ := (codecs field).readSlice_sound length remaining value suffix hslice
            constructor
            · change value.length < 2^64
              rw [hcount]
              simpa only [show 256^8 = 2^64 by norm_num] using hbound
            · rw [hbytes,hpayload]
              simp only [encode,List.cons_append,List.append_assoc,hcount]
          · simp [decode,htag] at h

/-- Fixed-schema recognition includes the complete consumed prefix and the
validity of every count. Unknown field identities are never inferred from bytes. -/
theorem decodeValues_sound (schema : List (Kind Index)) (bytes : Bytes)
    (values : Values Field schema) (suffix : Bytes)
    (h : decodeValues Field codecs schema bytes = some (values,suffix)) :
    ValidValues Field schema values ∧ bytes = encodeValues Field codecs schema values ++ suffix := by
  induction schema generalizing bytes with
  | nil =>
      cases values
      simp only [decodeValues,Option.some.injEq,Prod.mk.injEq,true_and] at h
      exact ⟨trivial,h⟩
  | cons kind rest ih =>
      simp only [decodeValues,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨⟨head,remaining⟩,hhead,⟨tail,last⟩,htail,hresult⟩ := h
      cases Option.some.inj hresult
      obtain ⟨hvalidHead,hbytes⟩ := decode_sound Field codecs kind bytes head remaining hhead
      obtain ⟨hvalidTail,hremaining⟩ := ih remaining tail htail
      refine ⟨⟨hvalidHead,hvalidTail⟩,?_⟩
      rw [hbytes,hremaining]
      simp only [encodeValues,List.append_assoc]

end TranscriptV2.Framing
