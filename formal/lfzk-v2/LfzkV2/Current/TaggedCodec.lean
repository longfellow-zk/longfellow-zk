import LfzkV2.Current.CanonicalPrefix
import LfzkV2.Current.Grammar

/-! Typed codecs for the tagged transcript grammar of
`rust/src/runtime/v2/transcript/DESIGN.md` (transcript I5, I6): a message is
a u64 tag and its fixed list of values, each value a kind word, a count and
a payload, every integer a u64 little-endian word. A message whose schema
fixes every count is a prefix codec on its typed values; its bytes are the
`Grammar` encoding of the same values. Whole-input codecs carry a last
field of unwritten length, such as the Merkle frontier of a proof body. -/
noncomputable section
namespace LfzkV2.Current.TaggedCodec
open TranscriptV2.Framing (Byte FieldCodec encodeLE)
open CanonicalPrefix

variable {A B F : Type}

/-- One u64 little-endian word. -/
def word (n : ℕ) : Bytes := encodeLE 8 n

/-- A tag word before a message's values. -/
def tagged (tag : ℕ) (codec : PrefixCodec A) : PrefixCodec A := codec.prefixed (word tag)

/-- `Elements`: kind 2, the field ID, the count, then each element's
canonical serialization. The schema fixes the count. -/
def elementsOf (field : ℕ) (codec : PrefixCodec F) (count : ℕ) : PrefixCodec (Fin count → F) :=
  (PrefixCodec.vector codec count).prefixed (word 2 ++ word field ++ word count)

def elements (field : ℕ) (codec : FieldCodec F) (count : ℕ) : PrefixCodec (Fin count → F) :=
  elementsOf field (PrefixCodec.field codec) count

private def pairData : (Fin 2 → F) ≃ F × F where
  toFun value := (value 0,value 1)
  invFun value := ![value.1,value.2]
  left_inv value := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

private def singleData : (Fin 1 → F) ≃ F where
  toFun value := value 0
  invFun value := fun _ => value
  left_inv value := by funext i; fin_cases i; rfl
  right_inv _ := rfl

/-- `Elements(F, 2)` as a pair. -/
def elementPair (field : ℕ) (codec : FieldCodec F) : PrefixCodec (F × F) :=
  (elements field codec 2).equiv pairData

/-- `Elements(F, 1)` as one element. -/
def element (field : ℕ) (codec : FieldCodec F) : PrefixCodec F :=
  (elements field codec 1).equiv singleData

theorem elementsOf_encode (field : ℕ) (codec : PrefixCodec F) (count : ℕ) (values : Fin count → F) :
    (elementsOf field codec count).encode values =
      word 2 ++ word field ++ word count ++ (List.ofFn values).flatMap codec.encode := by
  change word 2 ++ word field ++ word count ++ (PrefixCodec.vector codec count).encode values = _
  rw [PrefixCodec.vector_encode]

theorem elements_encode (field : ℕ) (codec : FieldCodec F) (count : ℕ) (values : Fin count → F) :
    (elements field codec count).encode values =
      word 2 ++ word field ++ word count ++ (List.ofFn values).flatMap codec.encode :=
  elementsOf_encode field (PrefixCodec.field codec) count values

theorem word_length (n : ℕ) : (word n).length = 8 := TranscriptV2.Framing.encodeLE_length _ _

theorem tagged_length (tag : ℕ) (codec : PrefixCodec A) (value : A) :
    ((tagged tag codec).encode value).length = 8+(codec.encode value).length := by
  change (word tag ++ codec.encode value).length = _
  rw [List.length_append,word_length]

theorem elementsOf_length (field : ℕ) (codec : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (codec.encode value).length = width) (count : ℕ) (value : Fin count → F) :
    ((elementsOf field codec count).encode value).length = 24+count*width := by
  change (word 2 ++ word field ++ word count ++ (PrefixCodec.vector codec count).encode value).length = _
  simp only [List.length_append,word_length,PrefixCodec.vector_length codec width hlen]

theorem elements_length (field : ℕ) (codec : FieldCodec F) (count : ℕ) (value : Fin count → F) :
    ((elements field codec count).encode value).length = 24+count*codec.width :=
  elementsOf_length field _ codec.width codec.length count value

theorem elementPair_length (field : ℕ) (codec : FieldCodec F) (value : F × F) :
    ((elementPair field codec).encode value).length = 24+2*codec.width :=
  elements_length field codec 2 _

theorem element_length (field : ℕ) (codec : FieldCodec F) (value : F) :
    ((element field codec).encode value).length = 24+codec.width := by
  rw [show 24+codec.width = 24+1*codec.width by ring]
  exact elements_length field codec 1 _

/-- `Bytes(32)`: a digest. -/
def digestValue : PrefixCodec Digest :=
  (PrefixCodec.vector PrefixCodec.byte 32).prefixed (word 0 ++ word 32)

private def countedBytes : {values : List Byte // values.length < 2^64} ≃ BoundedBytes maxLength where
  toFun value := ⟨value.val,by have := value.property; dsimp [maxLength]; omega⟩
  invFun value := ⟨value.bytes,by have := value.bound; dsimp [maxLength] at this; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Bytes`: kind 0, the byte count, the bytes. -/
def bytesValue : PrefixCodec (BoundedBytes maxLength) :=
  ((Grammar.many PrefixCodec.byte).prefixed (word 0)).equiv countedBytes

theorem digestValue_length (digest : Digest) : (digestValue.encode digest).length = 48 := by
  change (word 0 ++ word 32 ++ (PrefixCodec.vector PrefixCodec.byte 32).encode digest).length = _
  rw [PrefixCodec.bytes_encode]
  simp only [List.length_append,word_length,List.length_ofFn]

theorem bytesValue_encode (value : BoundedBytes maxLength) :
    bytesValue.encode value = word 0 ++ word value.bytes.length ++ value.bytes := by
  change word 0 ++ (encodeLE 8 value.bytes.length ++ value.bytes.flatMap PrefixCodec.byte.encode) = _
  rw [show PrefixCodec.byte.encode = (fun byte => [byte]) by funext byte; exact PrefixCodec.byte_encode byte,
    List.flatMap_singleton',List.append_assoc]
  rfl

/-! ## Whole-input codecs -/

namespace Whole

/-- A prefix field followed by a whole-input field. -/
def andThen (first : PrefixCodec A) (rest : WholeCodec B) : WholeCodec (A × B) where
  encode value := first.encode value.1 ++ rest.encode value.2
  decode input := match first.decode input with
    | some (a,suffix) => (rest.decode suffix).map fun b => (a,b)
    | none => none
  inverse value := by
    simp only [first.inverse,rest.inverse,Option.map_some]
  canonical input value found := by
    split at found
    · rename_i a suffix parsed
      obtain ⟨b,decoded,same⟩ := Option.map_eq_some_iff.mp found
      cases same
      rw [first.canonical _ _ _ parsed,rest.canonical _ _ decoded]
    · contradiction

def equiv (codec : WholeCodec A) (e : A ≃ B) : WholeCodec B where
  encode value := codec.encode (e.symm value)
  decode input := (codec.decode input).map e
  inverse value := by simp only [codec.inverse,Option.map_some,Equiv.apply_symm_apply]
  canonical input value found := by
    obtain ⟨a,decoded,same⟩ := Option.map_eq_some_iff.mp found
    cases same
    simpa only [Equiv.symm_apply_apply] using codec.canonical _ _ decoded

/-- A fixed marker before a whole-input field. -/
def prefixed (codec : WholeCodec A) (expected : Bytes) : WholeCodec A :=
  equiv (andThen (PrefixCodec.marker expected) codec) {
    toFun := Prod.snd
    invFun value := ((),value)
    left_inv value := by rcases value with ⟨⟨⟩,value⟩; rfl
    right_inv _ := rfl }

theorem andThen_encode (first : PrefixCodec A) (rest : WholeCodec B) (value : A × B) :
    (andThen first rest).encode value = first.encode value.1 ++ rest.encode value.2 := rfl

theorem equiv_encode (codec : WholeCodec A) (e : A ≃ B) (value : B) :
    (equiv codec e).encode value = codec.encode (e.symm value) := rfl

theorem prefixed_encode (codec : WholeCodec A) (expected : Bytes) (value : A) :
    (prefixed codec expected).encode value = expected ++ codec.encode value := rfl

/-- Digests filling the rest of the input, with no count: at most `bound`
of them. The input length fixes their number. -/
abbrev Digests (bound : ℕ) := (length : Fin (bound+1)) × (Fin length.val → Digest)

private abbrev digestVector (count : ℕ) : PrefixCodec (Fin count → Digest) :=
  PrefixCodec.vector (PrefixCodec.vector PrefixCodec.byte 32) count

def digestsEncode (bound : ℕ) (value : Digests bound) : Bytes := (digestVector value.1.val).encode value.2

def digestsDecode (bound : ℕ) (input : Bytes) : Option (Digests bound) :=
  if h : input.length / 32 < bound+1 then
    (readWhole (digestVector (input.length/32)) input).map fun digests => ⟨⟨input.length/32,h⟩,digests⟩
  else none

private theorem digestVector_length (count : ℕ) (digests : Fin count → Digest) :
    ((digestVector count).encode digests).length = count*32 :=
  PrefixCodec.vector_length _ 32 (fun digest => by
    rw [PrefixCodec.vector_length _ 1 (fun byte => by rw [PrefixCodec.byte_encode]; rfl)]) count digests

private theorem digests_inverse_at (bound : ℕ) (input : Bytes) (count : ℕ) (bounded : count < bound+1)
    (digests : Fin count → Digest) (encoded : (digestVector count).encode digests = input) :
    digestsDecode bound input = some ⟨⟨count,bounded⟩,digests⟩ := by
  have quotient : input.length / 32 = count := by
    rw [← encoded,digestVector_length]; omega
  subst quotient
  unfold digestsDecode
  rw [dif_pos bounded]
  have parsed := readWhole_encode (digestVector (input.length/32)) digests
  rw [encoded] at parsed
  rw [parsed]
  rfl

theorem digests_length (bound : ℕ) (value : Digests bound) :
    (digestsEncode bound value).length = 32*value.1.val := by
  rw [digestsEncode,digestVector_length,Nat.mul_comm]

def digests (bound : ℕ) : WholeCodec (Digests bound) where
  encode := digestsEncode bound
  decode := digestsDecode bound
  inverse value := digests_inverse_at bound _ value.1.val value.1.isLt value.2 rfl
  canonical input value found := by
    unfold digestsDecode at found
    split at found
    · rename_i fits
      obtain ⟨digests,parsed,same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact readWhole_canonical _ _ _ parsed
    · contradiction

end Whole

/-- A proof: the body, then its 32-byte seal block. -/
def withSeal {Proof : Type} (body : WholeCodec A) (e : A × Digest ≃ Proof) : WholeCodec Proof where
  encode proof := body.encode (e.symm proof).1 ++ List.ofFn (e.symm proof).2
  decode input :=
    if 32 ≤ input.length then do
      let value ← body.decode (input.take (input.length-32))
      let sealed ← readWhole (PrefixCodec.vector PrefixCodec.byte 32) (input.drop (input.length-32))
      some (e (value,sealed))
    else none
  inverse proof := by
    have hseal : (List.ofFn (e.symm proof).2).length = 32 := List.length_ofFn
    have fits : 32 ≤ (body.encode (e.symm proof).1 ++ List.ofFn (e.symm proof).2).length := by
      rw [List.length_append,hseal]; omega
    have cut : (body.encode (e.symm proof).1 ++ List.ofFn (e.symm proof).2).length - 32 =
        (body.encode (e.symm proof).1).length := by rw [List.length_append,hseal]; omega
    simp only [if_pos fits,cut,List.take_left,List.drop_left,body.inverse,Option.bind_eq_bind,Option.bind_some]
    have parsed := readWhole_encode (PrefixCodec.vector PrefixCodec.byte 32) (e.symm proof).2
    rw [PrefixCodec.bytes_encode] at parsed
    rw [parsed]
    simp only [Option.bind_some,Prod.mk.eta,Equiv.apply_symm_apply]
  canonical input proof found := by
    split at found
    · rename_i fits
      simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at found
      obtain ⟨value,hv,sealed,hs,same⟩ := found
      cases Option.some.inj same
      simp only [Equiv.symm_apply_apply]
      have hb := body.canonical _ _ hv
      have hsl := readWhole_canonical _ _ _ hs
      rw [PrefixCodec.bytes_encode] at hsl
      rw [← hb,← hsl,List.take_append_drop]
    · contradiction

end LfzkV2.Current.TaggedCodec
